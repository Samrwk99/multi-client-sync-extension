/**
 * Multi-Client Sync — SillyTavern UI extension
 *
 * The extension is intentionally dependency-soft:
 *
 *   plugin present + compatible -> synchronization enabled
 *   plugin missing             -> show "Server plugin required", do nothing
 *   plugin incompatible        -> show "Plugin incompatible", do nothing
 *
 * Ordinary SillyTavern continues functioning in all of those cases.
 *
 * Uses:
 * - SillyTavern.getContext()
 * - ST public event API
 * - ST public save path
 * - ST public generation interceptor
 * - SSE for authoritative live transport
 * - BroadcastChannel as an optimization only
 * - IndexedDB for durable pending local operations
 *
 * The server is authoritative for:
 * - user
 * - scope
 * - revision
 * - event sequence
 * - generation ownership
 * - generation lease
 *
 * The browser remains authoritative only for its own unacknowledged local
 * changes until the server accepts/rebases them.
 */

const EXTENSION_ID =
    'multi-client-sync';

const PLUGIN_BASE =
    '/api/plugins/multi-client-sync';

const PROTOCOL_VERSION =
    4;

const DB_NAME =
    'multi-client-sync-v4';

const DB_VERSION =
    2;

const MESSAGE_NAMESPACE =
    'multi_client_sync';

const MAX_LOCAL_QUEUE =
    200;

const MAX_PENDING_BYTES =
    64 * 1024 * 1024;

const HEARTBEAT_MS =
    10_000;

const STREAM_FLUSH_MS =
    160;

const RESYNC_DELAY_MS =
    120;

const PLUGIN_RETRY_MS =
    30_000;

const MAX_RECONNECT_MS =
    30_000;

const DEFAULT_SETTINGS =
    Object.freeze({
        enabled:
            true,

        debug:
            false,
    });


/* -------------------------------------------------------------------------- */
/* Runtime                                                                    */
/* -------------------------------------------------------------------------- */

let ctx = null;

let startPromise =
    null;

let started =
    false;

let stopping =
    false;

let pluginAvailable =
    false;

let principalKey =
    null;

let subscriptionToken =
    null;

let currentScope =
    null;

let currentState =
    null;

let scopeEpoch =
    0;

let reconnectTimer =
    null;

let pluginRetryTimer =
    null;

let heartbeatTimer =
    null;

let resyncTimer =
    null;

let streamTimer =
    null;

let finalizationTimer =
    null;

let eventSource =
    null;

let broadcastChannel =
    null;

let reconnectAttempt =
    0;

let applyingRemoteDepth =
    0;

let queueDrainPromise =
    null;

let resyncPromise =
    null;

let saveChain =
    Promise.resolve();

let streamFlushPromise =
    null;

let latestStreamSnapshot =
    null;

let latestStreamReason =
    null;

let localGenerationId =
    null;

let localGenerationLost =
    false;

let localStopRequested =
    false;

let generationTerminalizing =
    new Set();

let lastEventId =
    null;

let lastEpoch =
    null;

let lastSeq =
    0;

let lastRevision =
    0;

let localSequence =
    0;

let browserListeners =
    [];

let stListeners =
    [];

let uiRoot =
    null;


/* -------------------------------------------------------------------------- */
/* Basic utilities                                                            */
/* -------------------------------------------------------------------------- */

function log(
    ...args
) {
    if (
        getSettings().debug
    ) {
        console.debug(
            '[MultiClientSync]',
            ...args,
        );
    }
}

function warn(
    ...args
) {
    console.warn(
        '[MultiClientSync]',
        ...args,
    );
}

function clone(
    value,
) {
    if (
        value === undefined
    ) {
        return undefined;
    }

    if (
        typeof structuredClone ===
        'function'
    ) {
        try {
            return structuredClone(
                value,
            );
        } catch {
            // fallback
        }
    }

    return JSON.parse(
        JSON.stringify(
            value,
        ),
    );
}

function stableStringify(
    value,
) {
    if (
        value === null ||
        typeof value !==
            'object'
    ) {
        return JSON.stringify(
            value,
        );
    }

    if (
        Array.isArray(value)
    ) {
        return `[${value.map(
            stableStringify,
        ).join(',')}]`;
    }

    return `{${Object.keys(value)
        .sort()
        .map(
            key =>
                `${JSON.stringify(
                    key,
                )}:${stableStringify(
                    value[key],
                )}`,
        )
        .join(',')}}`;
}

async function sha256(
    value,
) {
    const stringValue =
        typeof value ===
            'string'
            ? value
            : stableStringify(
                value,
            );

    const bytes =
        new TextEncoder().encode(
            stringValue,
        );

    const digest =
        await crypto.subtle.digest(
            'SHA-256',
            bytes,
        );

    return Array
        .from(
            new Uint8Array(
                digest,
            ),
        )
        .map(
            byte =>
                byte
                    .toString(16)
                    .padStart(
                        2,
                        '0',
                    ),
        )
        .join('');
}

function uuid() {
    if (
        crypto.randomUUID
    ) {
        return crypto.randomUUID();
    }

    return (
        `${Date.now()
            .toString(36)}-` +
        `${Math.random()
            .toString(36)
            .slice(2)}-` +
        `${Math.random()
            .toString(36)
            .slice(2)}`
    );
}


/* -------------------------------------------------------------------------- */
/* Client/device identity                                                     */
/* -------------------------------------------------------------------------- */

function loadIdentity() {
    let storedDeviceId =
        localStorage.getItem(
            `${EXTENSION_ID}:deviceId`,
        );

    if (!storedDeviceId) {
        storedDeviceId =
            uuid();

        try {
            localStorage.setItem(
                `${EXTENSION_ID}:deviceId`,
                storedDeviceId,
            );
        } catch {
            // storage unavailable
        }
    }

    let storedClientId =
        sessionStorage.getItem(
            `${EXTENSION_ID}:clientId`,
        );

    if (!storedClientId) {
        storedClientId =
            uuid();

        try {
            sessionStorage.setItem(
                `${EXTENSION_ID}:clientId`,
                storedClientId,
            );
        } catch {
            // storage unavailable
        }
    }

    return {
        deviceId:
            storedDeviceId,

        clientId:
            storedClientId,
    };
}

const identity =
    loadIdentity();

const deviceId =
    identity.deviceId;

const clientId =
    identity.clientId;


/* -------------------------------------------------------------------------- */
/* Settings                                                                   */
/* -------------------------------------------------------------------------- */

function getSettings() {
    const settings =
        ctx?.extensionSettings || {};

    if (
        !settings[
            EXTENSION_ID
        ]
    ) {
        settings[
            EXTENSION_ID
        ] =
            structuredClone(
                DEFAULT_SETTINGS,
            );
    }

    for (
        const [
            key,
            value,
        ] of Object.entries(
            DEFAULT_SETTINGS,
        )
    ) {
        if (
            !Object.hasOwn(
                settings[
                    EXTENSION_ID
                ],
                key,
            )
        ) {
            settings[
                EXTENSION_ID
            ][key] =
                value;
        }
    }

    return settings[
        EXTENSION_ID
    ];
}


/* -------------------------------------------------------------------------- */
/* Scope                                                                     */
/* -------------------------------------------------------------------------- */

function getCurrentScope() {
    if (!ctx) {
        return null;
    }

    const chatId =
        ctx.chatId ??
        ctx.getCurrentChatId?.();

    if (
        chatId ==
            null ||
        chatId ===
            ''
    ) {
        return null;
    }

    const groupId =
        ctx.groupId !=
            null &&
        String(
            ctx.groupId,
        ) !==
            ''
            ? String(
                ctx.groupId,
            )
            : null;

    let characterId =
        null;

    if (
        groupId ===
            null &&
        ctx.characterId !=
            null
    ) {
        const character =
            ctx.characters?.[
                ctx.characterId
            ];

        if (
            character?.avatar
        ) {
            characterId =
                String(
                    character.avatar,
                );
        }
    }

    if (
        groupId ===
            null &&
        !characterId
    ) {
        return null;
    }

    const metadata =
        ctx.chatMetadata || {};

    const branchId =
        metadata.main_chat
            ? (
                metadata.integrity
                    ? String(
                        metadata.integrity,
                    )
                    : null
            )
            : null;

    const parentChatId =
        metadata.main_chat
            ? String(
                metadata.main_chat,
            )
            : null;

    return {
        scopeType:
            groupId !==
                null
                ? 'group'
                : 'character',

        characterId:
            groupId !==
                null
                ? null
                : characterId,

        groupId,

        chatId:
            String(
                chatId,
            ),

        branchId,

        parentChatId,
    };
}

function sameScope(
    a,
    b,
) {
    return (
        Boolean(a) &&
        Boolean(b) &&
        stableStringify(
            a,
        ) ===
            stableStringify(
                b,
            )
    );
}

function currentEpoch() {
    return scopeEpoch;
}


/* -------------------------------------------------------------------------- */
/* Snapshot handling                                                          */
/* -------------------------------------------------------------------------- */

function ensureMessageIds(
    chat,
) {
    if (
        !Array.isArray(chat)
    ) {
        return false;
    }

    let changed =
        false;

    /*
     * chat[0] is the ST chat header. Message IDs start at 1.
     */
    for (
        let index = 1;
        index <
            chat.length;
        index++
    ) {
        const message =
            chat[index];

        if (
            !message ||
            typeof message !==
                'object'
        ) {
            continue;
        }

        if (
            !message.extra ||
            typeof message.extra !==
                'object' ||
            Array.isArray(
                message.extra,
            )
        ) {
            message.extra = {};
            changed = true;
        }

        if (
            !message.extra[
                MESSAGE_NAMESPACE
            ] ||
            typeof message.extra[
                MESSAGE_NAMESPACE
            ] !==
                'object' ||
            Array.isArray(
                message.extra[
                    MESSAGE_NAMESPACE
                ],
            )
        ) {
            message.extra[
                MESSAGE_NAMESPACE
            ] = {};

            changed = true;
        }

        if (
            !message.extra[
                MESSAGE_NAMESPACE
            ].messageId
        ) {
            message.extra[
                MESSAGE_NAMESPACE
            ].messageId =
                uuid();

            changed = true;
        }
    }

    return changed;
}

function normalizeSnapshot(
    raw,
) {
    if (
        !raw ||
        typeof raw !==
            'object' ||
        !Array.isArray(
            raw.chat,
        )
    ) {
        return null;
    }

    const snapshot = {
        chat:
            clone(
                raw.chat,
            ),

        chatMetadata:
            clone(
                raw.chatMetadata ||
                raw.chat?.[0]
                    ?.chat_metadata ||
                {},
            ),
    };

    ensureMessageIds(
        snapshot.chat,
    );

    if (
        snapshot.chat[0]
    ) {
        snapshot.chat[0]
            .chat_metadata =
            clone(
                snapshot.chatMetadata,
            );
    }

    return snapshot;
}

function makeLocalSnapshot() {
    if (
        !ctx ||
        !currentScope
    ) {
        return null;
    }

    const snapshot =
        normalizeSnapshot({
            chat:
                ctx.chat,

            chatMetadata:
                ctx.chatMetadata,
        });

    return snapshot;
}

async function hashLocalSnapshot() {
    const snapshot =
        makeLocalSnapshot();

    return snapshot
        ? sha256(
            snapshot,
        )
        : null;
}


/* -------------------------------------------------------------------------- */
/* ST UI application                                                          */
/* -------------------------------------------------------------------------- */

async function applySnapshotLocally(
    snapshot,
    {
        persist = true,
        reason = 'apply',
    } = {},
) {
    const normalized =
        normalizeSnapshot(
            snapshot,
        );

    if (
        !normalized ||
        !currentScope
    ) {
        return false;
    }

    const scopeAtStart =
        clone(currentScope);

    applyingRemoteDepth += 1;

    try {
        if (
            !sameScope(
                scopeAtStart,
                currentScope,
            )
        ) {
            return false;
        }

        if (
            Array.isArray(
                ctx.chat,
            )
        ) {
            ctx.chat.splice(
                0,
                ctx.chat.length,
                ...normalized.chat.map(
                    clone,
                ),
            );
        }

        if (
            normalized.chat[0]
        ) {
            normalized.chat[0]
                .chat_metadata =
                clone(
                    normalized.chatMetadata,
                );
        }

        /*
         * Current ST exposes updateChatMetadata as the public metadata mutation
         * path.
         */
        if (
            typeof ctx.updateChatMetadata ===
            'function'
        ) {
            ctx.updateChatMetadata(
                clone(
                    normalized.chatMetadata,
                ),
                true,
            );
        }

        /*
         * Current ST exposes printMessages publicly through getContext().
         */
        if (
            typeof ctx.printMessages ===
            'function'
        ) {
            await ctx.printMessages();
        }

        if (
            persist
        ) {
            const saved =
                await saveCurrentChat(
                    `remote:${reason}`,
                );

            if (
                !saved
            ) {
                setStatus(
                    'Save pending',
                    'Remote state is applied in memory but ST did not confirm the save',
                );
            }
        }

        return true;
    } catch (error) {
        warn(
            'Remote snapshot application failed',
            error,
        );

        setStatus(
            'Sync error',
            'Could not apply authoritative state',
        );

        return false;
    } finally {
        applyingRemoteDepth -= 1;
    }
}

async function applyPatchLocally(
    patch,
    {
        persist = true,
        reason = 'patch',
    } = {},
) {
    if (
        !patch ||
        !currentScope
    ) {
        return false;
    }

    if (
        patch.kind ===
        'full'
    ) {
        return applySnapshotLocally(
            patch.snapshot,
            {
                persist,
                reason,
            },
        );
    }

    applyingRemoteDepth += 1;

    try {
        if (
            patch.kind ===
            'append'
        ) {
            const messages =
                Array.isArray(
                    patch.messages,
                )
                    ? patch.messages
                        .map(
                            clone,
                        )
                    : [];

            ctx.chat.splice(
                Number(
                    patch.startIndex,
                ),
                0,
                ...messages,
            );
        }

        if (
            patch.kind ===
            'patch'
        ) {
            for (
                const change of
                    patch.changes ||
                    []
            ) {
                const index =
                    Number(
                        change.index,
                    );

                if (
                    Number.isInteger(
                        index,
                    ) &&
                    index >= 1 &&
                    index <
                        ctx.chat.length
                ) {
                    ctx.chat[index] =
                        clone(
                            change.message,
                        );
                }
            }
        }

        if (
            patch.chatMetadata
        ) {
            if (
                typeof ctx.updateChatMetadata ===
                'function'
            ) {
                ctx.updateChatMetadata(
                    clone(
                        patch.chatMetadata,
                    ),
                    true,
                );
            }

            if (
                ctx.chat[0]
            ) {
                ctx.chat[0]
                    .chat_metadata =
                    clone(
                        patch.chatMetadata,
                    );
            }
        }

        if (
            typeof ctx.printMessages ===
            'function'
        ) {
            await ctx.printMessages();
        }

        if (
            persist
        ) {
            await saveCurrentChat(
                `remote:${reason}`,
            );
        }

        return true;
    } catch (error) {
        warn(
            'Remote patch application failed',
            error,
        );

        return false;
    } finally {
        applyingRemoteDepth -= 1;
    }
}


/* -------------------------------------------------------------------------- */
/* ST persistence                                                             */
/* -------------------------------------------------------------------------- */

async function saveCurrentChat(
    reason = 'save',
) {
    const scopeAtStart =
        currentScope
            ? clone(
                currentScope,
            )
            : null;

    if (
        !scopeAtStart ||
        typeof ctx.saveChat !==
            'function'
    ) {
        return false;
    }

    saveChain =
        saveChain.then(
            async () => {
                if (
                    !sameScope(
                        scopeAtStart,
                        currentScope,
                    )
                ) {
                    return false;
                }

                try {
                    await ctx.saveChat();

                    log(
                        'ST save completed',
                        reason,
                    );

                    return true;
                } catch (error) {
                    warn(
                        'ST save failed',
                        reason,
                        error,
                    );

                    return false;
                }
            },
        );

    return saveChain;
}


/* -------------------------------------------------------------------------- */
/* HTTP                                                                       */
/* -------------------------------------------------------------------------- */

function requestHeaders(
    extra = {},
) {
    return {
        Accept:
            'application/json',

        ...(
            ctx?.getRequestHeaders?.() ||
            {}
        ),

        ...extra,
    };
}

async function api(
    path,
    {
        method = 'GET',
        body = undefined,
    } = {},
) {
    const options = {
        method,

        credentials:
            'same-origin',

        cache:
            'no-store',

        headers:
            requestHeaders(
                body !== undefined
                    ? {
                        'Content-Type':
                            'application/json',
                    }
                    : {},
            ),
    };

    if (
        body !== undefined
    ) {
        options.body =
            JSON.stringify(
                body,
            );
    }

    const response =
        await fetch(
            `${PLUGIN_BASE}${path}`,
            options,
        );

    let parsed =
        null;

    try {
        parsed =
            await response.json();
    } catch {
        // non-json
    }

    if (
        !response.ok
    ) {
        const error =
            new Error(
                parsed?.message ||
                    `HTTP ${response.status}`,
            );

        error.status =
            response.status;

        error.code =
            parsed?.code ||
            `http_${response.status}`;

        error.state =
            parsed?.state;

        error.expectedHash =
            parsed?.expectedHash;

        error.actualHash =
            parsed?.actualHash;

        throw error;
    }

    return parsed || {};
}


/* -------------------------------------------------------------------------- */
/* IndexedDB                                                                  */
/* -------------------------------------------------------------------------- */

let databasePromise =
    null;

function openDatabase() {
    if (
        databasePromise
    ) {
        return databasePromise;
    }

    databasePromise =
        new Promise(
            (
                resolve,
                reject,
            ) => {
                const request =
                    indexedDB.open(
                        DB_NAME,
                        DB_VERSION,
                    );

                request.onerror =
                    () =>
                        reject(
                            request.error,
                        );

                request.onupgradeneeded =
                    () => {
                        const db =
                            request.result;

                        if (
                            !db.objectStoreNames.contains(
                                'ops',
                            )
                        ) {
                            db.createObjectStore(
                                'ops',
                                {
                                    keyPath:
                                        'opId',
                                },
                            );
                        }

                        if (
                            !db.objectStoreNames.contains(
                                'meta',
                            )
                        ) {
                            db.createObjectStore(
                                'meta',
                            );
                        }
                    };

                request.onsuccess =
                    () =>
                        resolve(
                            request.result,
                        );
            },
        );

    return databasePromise;
}

async function dbPutOperation(
    operation,
) {
    const db =
        await openDatabase();

    await new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    'ops',
                    'readwrite',
                );

            tx.objectStore(
                'ops',
            ).put(
                clone(
                    operation,
                ),
            );

            tx.oncomplete =
                resolve;

            tx.onerror =
                () =>
                    reject(
                        tx.error,
                    );
        },
    );
}

async function dbDeleteOperation(
    opId,
) {
    const db =
        await openDatabase();

    await new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    'ops',
                    'readwrite',
                );

            tx.objectStore(
                'ops',
            ).delete(
                opId,
            );

            tx.oncomplete =
                resolve;

            tx.onerror =
                () =>
                    reject(
                        tx.error,
                    );
        },
    );
}

async function dbGetOperations(
    scope,
) {
    if (
        !principalKey
    ) {
        return [];
    }

    const db =
        await openDatabase();

    return new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    'ops',
                    'readonly',
                );

            const request =
                tx.objectStore(
                    'ops',
                ).getAll();

            request.onerror =
                () =>
                    reject(
                        request.error,
                    );

            request.onsuccess =
                () => {
                    const values =
                        request.result
                            .filter(
                                operation =>
                                    operation
                                        .principalKey ===
                                        principalKey &&
                                    sameScope(
                                        operation.scope,
                                        scope,
                                    ),
                            )
                            .sort(
                                (
                                    a,
                                    b,
                                ) =>
                                    a.localSeq -
                                    b.localSeq,
                            );

                    resolve(
                        values,
                    );
                };
        },
    );
}

async function dbPutMeta(
    key,
    value,
) {
    if (
        !principalKey
    ) {
        return;
    }

    const db =
        await openDatabase();

    await new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    'meta',
                    'readwrite',
                );

            tx.objectStore(
                'meta',
            ).put(
                clone(
                    value,
                ),
                `${principalKey}:${key}`,
            );

            tx.oncomplete =
                resolve;

            tx.onerror =
                () =>
                    reject(
                        tx.error,
                    );
        },
    );
}

async function dbGetMeta(
    key,
) {
    if (
        !principalKey
    ) {
        return null;
    }

    const db =
        await openDatabase();

    return new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    'meta',
                    'readonly',
                );

            const request =
                tx.objectStore(
                    'meta',
                ).get(
                    `${principalKey}:${key}`,
                );

            request.onerror =
                () =>
                    reject(
                        request.error,
                    );

            request.onsuccess =
                () =>
                    resolve(
                        request.result ||
                            null,
                    );
        },
    );
}

async function dbClearAll() {
    const db =
        await openDatabase();

    await new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    [
                        'ops',
                        'meta',
                    ],
                    'readwrite',
                );

            tx.objectStore(
                'ops',
            ).clear();

            tx.objectStore(
                'meta',
            ).clear();

            tx.oncomplete =
                resolve;

            tx.onerror =
                () =>
                    reject(
                        tx.error,
                    );
        },
    );
}


/* -------------------------------------------------------------------------- */
/* UI                                                                         */
/* -------------------------------------------------------------------------- */

function ensureUi() {
    if (
        uiRoot ||
        !document.body
    ) {
        return;
    }

    uiRoot =
        document.createElement(
            'div',
        );

    uiRoot.id =
        'multi-client-sync-status';

    uiRoot.innerHTML = `
        <div data-mcs-title></div>
        <div data-mcs-detail></div>
        <div data-mcs-actions></div>
    `;

    Object.assign(
        uiRoot.style,
        {
            position:
                'fixed',

            right:
                '12px',

            bottom:
                '12px',

            zIndex:
                '99999',

            minWidth:
                '230px',

            maxWidth:
                '360px',

            padding:
                '9px 11px',

            borderRadius:
                '8px',

            background:
                'rgba(20,20,20,.94)',

            color:
                '#fff',

            fontSize:
                '12px',

            lineHeight:
                '1.4',

            boxShadow:
                '0 3px 18px rgba(0,0,0,.35)',
        },
    );

    document.body.appendChild(
        uiRoot,
    );
}

function setStatus(
    title,
    detail = '',
    actions = [],
) {
    ensureUi();

    if (!uiRoot) {
        return;
    }

    const titleNode =
        uiRoot.querySelector(
            '[data-mcs-title]',
        );

    const detailNode =
        uiRoot.querySelector(
            '[data-mcs-detail]',
        );

    const actionsNode =
        uiRoot.querySelector(
            '[data-mcs-actions]',
        );

    titleNode.textContent =
        title;

    detailNode.textContent =
        detail;

    actionsNode.replaceChildren();

    for (
        const action of
            actions
    ) {
        const button =
            document.createElement(
                'button',
            );

        button.type =
            'button';

        button.textContent =
            action.label;

        button.style.margin =
            '5px 4px 0 0';

        button.addEventListener(
            'click',
            action.run,
        );

        actionsNode.appendChild(
            button,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Server cursor                                                              */
/* -------------------------------------------------------------------------- */

async function persistCursor() {
    if (
        !currentScope
    ) {
        return;
    }

    await dbPutMeta(
        stableStringify(
            currentScope,
        ),
        {
            lastEventId,
            lastEpoch,
            lastSeq,
            lastRevision,
        },
    );
}

function applyStateCursor(
    state,
) {
    if (!state) {
        return;
    }

    if (
        state.epoch
    ) {
        lastEpoch =
            String(
                state.epoch,
            );
    }

    if (
        Number.isSafeInteger(
            Number(
                state.seq,
            ),
        )
    ) {
        lastSeq =
            Number(
                state.seq,
            );
    }

    if (
        Number.isSafeInteger(
            Number(
                state.revision,
            ),
        )
    ) {
        lastRevision =
            Number(
                state.revision,
            );
    }

    if (
        state.lastEventId
    ) {
        lastEventId =
            String(
                state.lastEventId,
            );
    } else if (
        lastEpoch &&
        lastSeq >
            0
    ) {
        lastEventId =
            `${lastEpoch}:${lastSeq}`;
    }
}


/* -------------------------------------------------------------------------- */
/* Generation helpers                                                         */
/* -------------------------------------------------------------------------- */

function isLocalGenerationOwner() {
    const generation =
        currentState?.generation;

    return Boolean(
        generation &&
        generation.ownerClientId ===
            clientId &&
        generation.ownerDeviceId ===
            deviceId &&
        localGenerationId ===
            generation.id &&
        !localGenerationLost,
    );
}

function activeGeneration() {
    return (
        currentState?.generation ||
        null
    );
}


/* -------------------------------------------------------------------------- */
/* Generation claim                                                           */
/* -------------------------------------------------------------------------- */

async function claimGeneration(
    generationType,
    targetMessageId = null,
) {
    if (
        currentState?.generation
    ) {
        return isLocalGenerationOwner();
    }

    const expectedScope =
        currentEpoch();

    const generationId =
        uuid();

    localGenerationId =
        generationId;

    localGenerationLost =
        false;

    localStopRequested =
        false;

    try {
        const result =
            await api(
                '/event',
                {
                    method:
                        'POST',

                    body: {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        clientId,

                        deviceId,

                        scope:
                            currentScope,

                        opId:
                            uuid(),

                        type:
                            'generation_claim',

                        generationId,

                        generationType:
                            String(
                                generationType ||
                                    'unknown',
                            ),

                        targetMessageId,

                        baseRevision:
                            lastRevision,
                    },
                },
            );

        if (
            expectedScope !==
            currentEpoch()
        ) {
            localGenerationLost =
                true;

            return false;
        }

        if (
            result.state
        ) {
            applyStateCursor(
                result.state,
            );

            currentState =
                currentState ||
                {};

            currentState.generation =
                result.state
                    .generation
                    ? clone(
                        result.state
                            .generation,
                    )
                    : null;
        }

        if (
            result.state
                ?.generation
                ?.id !==
            generationId
        ) {
            localGenerationLost =
                true;

            return false;
        }

        setStatus(
            'Generation owner',
            'This client owns the generation lease',
        );

        await persistCursor();

        return true;
    } catch (error) {
        localGenerationLost =
            true;

        if (
            error.code ===
            'generation_owned'
        ) {
            try {
                ctx.stopGeneration?.();
            } catch {
                // ignored
            }

            setStatus(
                'Generation busy',
                'Another client owns generation',
            );
        } else if (
            error.code ===
            'stale_revision'
        ) {
            await resyncCurrentScope(
                'generation claim conflict',
            );

            try {
                ctx.stopGeneration?.();
            } catch {
                // ignored
            }
        } else {
            warn(
                'Generation claim failed',
                error,
            );
        }

        return false;
    }
}


/* -------------------------------------------------------------------------- */
/* Pre-generation interceptor                                                  */
/* -------------------------------------------------------------------------- */

/**
 * Current ST resolves generate_interceptor by looking up the configured
 * function name on globalThis.
 *
 * Therefore this is deliberately attached to globalThis.
 *
 * IMPORTANT:
 * The manifest still needs:
 *
 * "generate_interceptor": "multiClientSyncGenerateInterceptor"
 *
 * to activate this pre-generation gate.
 */
async function multiClientSyncGenerateInterceptor(
    chat,
    contextSize,
    abort,
    type,
) {
    if (
        !getSettings().enabled
    ) {
        return;
    }

    const available =
        await ensureConnected();

    /*
     * Missing plugin must never break ordinary Tavern generation.
     */
    if (!available) {
        return;
    }

    const generation =
        activeGeneration();

    if (
        generation &&
        !isLocalGenerationOwner()
    ) {
        abort(
            true,
        );

        return;
    }

    const targetMessageId =
        getLastMessageSyncId();

    const claimed =
        await claimGeneration(
            type,
            targetMessageId,
        );

    if (
        !claimed
    ) {
        abort(
            true,
        );
    }
}

globalThis.multiClientSyncGenerateInterceptor =
    multiClientSyncGenerateInterceptor;


/* -------------------------------------------------------------------------- */
/* Stable message identity                                                    */
/* -------------------------------------------------------------------------- */

function getLastMessageSyncId() {
    const snapshot =
        makeLocalSnapshot();

    if (
        !snapshot ||
        snapshot.chat.length <
            2
    ) {
        return null;
    }

    for (
        let index =
            snapshot.chat.length -
            1;
        index >= 1;
        index--
    ) {
        const id =
            snapshot.chat[index]
                ?.extra
                ?.[MESSAGE_NAMESPACE]
                ?.messageId;

        if (id) {
            return id;
        }
    }

    return null;
}


/* -------------------------------------------------------------------------- */
/* Three-way merge                                                            */
/* -------------------------------------------------------------------------- */

function messageId(
    message,
) {
    return (
        message
            ?.extra
            ?.[MESSAGE_NAMESPACE]
            ?.messageId ||
        null
    );
}

function messageMap(
    chat,
) {
    const result =
        new Map();

    for (
        let index = 1;
        index < chat.length;
        index++
    ) {
        const id =
            messageId(
                chat[index],
            );

        if (
            id
        ) {
            result.set(
                id,
                {
                    message:
                        chat[index],

                    index,
                },
            );
        }
    }

    return result;
}

function mergeSnapshots(
    base,
    local,
    remote,
) {
    const conflicts =
        [];

    const baseChat =
        base?.chat || [];

    const localChat =
        local?.chat || [];

    const remoteChat =
        remote?.chat || [];

    const baseMap =
        messageMap(
            baseChat,
        );

    const localMap =
        messageMap(
            localChat,
        );

    const remoteMap =
        messageMap(
            remoteChat,
        );

    /*
     * A precise merge is impossible if one side does not have stable IDs.
     * Use authoritative remote state instead of guessing.
     */
    for (
        const chat of [
            baseChat,
            localChat,
            remoteChat,
        ]
    ) {
        for (
            let i = 1;
            i < chat.length;
            i++
        ) {
            if (
                !messageId(
                    chat[i],
                )
            ) {
                conflicts.push({
                    type:
                        'legacy_message_identity',

                    policy:
                        'remote_wins',
                });

                return {
                    snapshot:
                        clone(
                            remote,
                        ),

                    conflicts,
                };
            }
        }
    }

    const ids =
        new Set([
            ...baseMap.keys(),
            ...localMap.keys(),
            ...remoteMap.keys(),
        ]);

    const mergedById =
        new Map();

    for (
        const id of ids
    ) {
        const b =
            baseMap.get(id)
                ?.message;

        const l =
            localMap.get(id)
                ?.message;

        const r =
            remoteMap.get(id)
                ?.message;

        const bExists =
            Boolean(b);

        const lExists =
            Boolean(l);

        const rExists =
            Boolean(r);

        if (
            !bExists
        ) {
            if (
                lExists &&
                rExists
            ) {
                if (
                    sameValue(
                        l,
                        r,
                    )
                ) {
                    mergedById.set(
                        id,
                        clone(l),
                    );
                } else {
                    /*
                     * Deterministic conflict policy.
                     */
                    mergedById.set(
                        id,
                        clone(r),
                    );

                    conflicts.push({
                        type:
                            'concurrent_insert',

                        messageId:
                            id,

                        policy:
                            'remote_wins',
                    });
                }
            } else if (
                lExists
            ) {
                mergedById.set(
                    id,
                    clone(l),
                );
            } else if (
                rExists
            ) {
                mergedById.set(
                    id,
                    clone(r),
                );
            }

            continue;
        }

        const localChanged =
            lExists &&
            !sameValue(
                l,
                b,
            );

        const remoteChanged =
            rExists &&
            !sameValue(
                r,
                b,
            );

        if (
            !lExists &&
            !rExists
        ) {
            continue;
        }

        if (
            !lExists
        ) {
            if (
                remoteChanged
            ) {
                conflicts.push({
                    type:
                        'delete_vs_change',

                    messageId:
                        id,

                    policy:
                        'remote_wins',
                });

                mergedById.set(
                    id,
                    clone(r),
                );
            }

            continue;
        }

        if (
            !rExists
        ) {
            if (
                localChanged
            ) {
                conflicts.push({
                    type:
                        'change_vs_delete',

                    messageId:
                        id,

                    policy:
                        'remote_wins',
                });
            }

            continue;
        }

        if (
            localChanged &&
            !remoteChanged
        ) {
            mergedById.set(
                id,
                clone(l),
            );

            continue;
        }

        if (
            !localChanged &&
            remoteChanged
        ) {
            mergedById.set(
                id,
                clone(r),
            );

            continue;
        }

        if (
            localChanged &&
            remoteChanged
        ) {
            if (
                sameValue(
                    l,
                    r,
                )
            ) {
                mergedById.set(
                    id,
                    clone(l),
                );
            } else {
                mergedById.set(
                    id,
                    clone(r),
                );

                conflicts.push({
                    type:
                        'concurrent_edit',

                    messageId:
                        id,

                    policy:
                        'remote_wins',
                });
            }

            continue;
        }

        mergedById.set(
            id,
            clone(b),
        );
    }

    /*
     * Preserve remote ordering for shared messages.
     */
    const resultMessages =
        [];

    const emitted =
        new Set();

    for (
        let index = 1;
        index <
            remoteChat.length;
        index++
    ) {
        const id =
            messageId(
                remoteChat[index],
            );

        if (
            id &&
            mergedById.has(
                id,
            )
        ) {
            resultMessages.push(
                clone(
                    mergedById.get(
                        id,
                    ),
                ),
            );

            emitted.add(
                id,
            );
        }
    }

    /*
     * Insert local-only messages deterministically after their nearest surviving
     * predecessor.
     */
    for (
        let index = 1;
        index <
            localChat.length;
        index++
    ) {
        const id =
            messageId(
                localChat[index],
            );

        if (
            !id ||
            emitted.has(id) ||
            !mergedById.has(id)
        ) {
            continue;
        }

        let insertAt =
            resultMessages.length;

        for (
            let previous =
                index - 1;
            previous >= 1;
            previous--
        ) {
            const previousId =
                messageId(
                    localChat[previous],
                );

            const anchor =
                resultMessages.findIndex(
                    message =>
                        messageId(
                            message,
                        ) ===
                        previousId,
                );

            if (
                anchor >= 0
            ) {
                insertAt =
                    anchor + 1;

                break;
            }
        }

        resultMessages.splice(
            insertAt,
            0,
            clone(
                mergedById.get(
                    id,
                ),
            ),
        );

        emitted.add(
            id,
        );

        conflicts.push({
            type:
                'concurrent_insert_position',

            messageId:
                id,

            policy:
                'deterministic_anchor',
        });
    }

    /*
     * Metadata merge.
     */
    const mergedMetadata =
        clone(
            remote?.chatMetadata ||
                {},
        );

    const baseMetadata =
        base?.chatMetadata ||
            {};

    const localMetadata =
        local?.chatMetadata ||
            {};

    const metadataKeys =
        new Set([
            ...Object.keys(
                baseMetadata,
            ),
            ...Object.keys(
                localMetadata,
            ),
            ...Object.keys(
                remote?.chatMetadata ||
                    {},
            ),
        ]);

    for (
        const key of
            metadataKeys
    ) {
        const b =
            baseMetadata[key];

        const l =
            localMetadata[key];

        const r =
            remote?.chatMetadata?.[
                key
            ];

        const localChanged =
            !sameValue(
                l,
                b,
            );

        const remoteChanged =
            !sameValue(
                r,
                b,
            );

        if (
            localChanged &&
            !remoteChanged
        ) {
            mergedMetadata[key] =
                clone(l);
        } else if (
            localChanged &&
            remoteChanged &&
            !sameValue(
                l,
                r,
            )
        ) {
            conflicts.push({
                type:
                    'metadata_conflict',

                key,

                policy:
                    'remote_wins',
            });
        }
    }

    return {
        snapshot: {
            chat: [
                clone(
                    remoteChat[0] ||
                        {
                            chat_metadata:
                                {},
                        },
                ),
                ...resultMessages,
            ],

            chatMetadata:
                mergedMetadata,
        },

        conflicts,
    };
}


/* -------------------------------------------------------------------------- */
/* Pending queue                                                              */
/* -------------------------------------------------------------------------- */

const COALESCIBLE_TYPES =
    new Set([
        'message_sent',
        'message_received',
        'message_edited',
        'message_updated',
        'message_swiped',
        'message_reasoning_edited',
        'message_reasoning_deleted',
        'stream_reasoning_done',
        'tool_calls_performed',
    ]);

function pendingBytes(
    operations,
) {
    return operations.reduce(
        (
            total,
            operation,
        ) =>
            total +
            JSON.stringify(
                operation,
            ).length,
        0,
    );
}

async function enqueueLocalMutation(
    type,
    payload = {},
) {
    if (
        applyingRemoteDepth >
            0 ||
        !pluginAvailable ||
        !currentScope ||
        !currentState ||
        !getSettings().enabled
    ) {
        return;
    }

    /*
     * A remote generation owner controls ordinary chat state until its terminal
     * event. The non-owner must not manufacture conflicting writes.
     */
    if (
        currentState.generation &&
        !isLocalGenerationOwner()
    ) {
        return;
    }

    const saved =
        await saveCurrentChat(
            type,
        );

    if (
        !saved
    ) {
        setStatus(
            'Save pending',
            'SillyTavern did not confirm the current local save',
        );

        return;
    }

    const migrated =
        ensureMessageIds(
            ctx.chat,
        );

    if (
        migrated
    ) {
        const idsSaved =
            await saveCurrentChat(
                'stable-message-id-migration',
            );

        if (
            !idsSaved
        ) {
            return;
        }
    }

    const snapshot =
        makeLocalSnapshot();

    if (!snapshot) {
        return;
    }

    let operations =
        await dbGetOperations(
            currentScope,
        );

    const serialized =
        JSON.stringify(
            snapshot,
        );

    if (
        serialized.length >
            MAX_PENDING_BYTES
    ) {
        setStatus(
            'Chat too large',
            'Local synchronization snapshot exceeds the client queue limit',
        );

        return;
    }

    if (
        COALESCIBLE_TYPES.has(
            type,
        ) &&
        operations.length
    ) {
        const last =
            operations[
                operations.length - 1
            ];

        if (
            last.coalescible
        ) {
            await dbDeleteOperation(
                last.opId,
            );

            operations =
                operations.slice(
                    0,
                    -1,
                );
        }
    }

    if (
        operations.length >=
        MAX_LOCAL_QUEUE
    ) {
        setStatus(
            'Sync queue full',
            'Local changes are not being silently discarded',
        );

        return;
    }

    localSequence +=
        1;

    const operation = {
        principalKey,

        opId:
            uuid(),

        localSeq:
            localSequence,

        scope:
            clone(
                currentScope,
            ),

        type,

        payload:
            clone(
                payload,
            ),

        snapshot:
            clone(
                snapshot,
            ),

        baseSnapshot:
            clone(
                currentState.serverSnapshot ||
                    snapshot,
            ),

        baseRevision:
            lastRevision,

        coalescible:
            COALESCIBLE_TYPES.has(
                type,
            ),
    };

    operations.push(
        operation,
    );

    if (
        pendingBytes(
            operations,
        ) >
        MAX_PENDING_BYTES
    ) {
        setStatus(
            'Sync queue full',
            'Durable local queue limit reached',
        );

        return;
    }

    await dbPutOperation(
        operation,
    );

    broadcastLocalChange(
        type,
    );

    await drainPendingQueue();
}

async function rebasePendingQueue(
    remoteSnapshot,
    remoteRevision,
) {
    const operations =
        await dbGetOperations(
            currentScope,
        );

    if (
        !operations.length
    ) {
        return null;
    }

    let baseSnapshot =
        clone(
            remoteSnapshot,
        );

    let baseRevision =
        Number(
            remoteRevision,
        ) || 0;

    for (
        const operation of
            operations
    ) {
        const merged =
            mergeSnapshots(
                operation.baseSnapshot ||
                    baseSnapshot,
                operation.snapshot,
                baseSnapshot,
            );

        operation.baseSnapshot =
            clone(
                baseSnapshot,
            );

        operation.baseRevision =
            baseRevision;

        operation.snapshot =
            clone(
                merged.snapshot,
            );

        baseSnapshot =
            clone(
                merged.snapshot,
            );

        /*
         * The queue is submitted sequentially. Once this operation is accepted,
         * the next one will be based on the next revision.
         */
        baseRevision +=
            1;

        await dbPutOperation(
            operation,
        );
    }

    return baseSnapshot;
}

async function sendPendingOperation(
    operation,
) {
    if (
        !currentScope ||
        !pluginAvailable ||
        !sameScope(
            currentScope,
            operation.scope,
        )
    ) {
        return false;
    }

    try {
        const result =
            await api(
                '/event',
                {
                    method:
                        'POST',

                    body: {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        clientId,

                        deviceId,

                        scope:
                            operation.scope,

                        opId:
                            operation.opId,

                        type:
                            operation.type,

                        payload:
                            operation.payload,

                        snapshot:
                            operation.snapshot,

                        baseSnapshot:
                            operation.baseSnapshot,

                        baseRevision:
                            operation.baseRevision,
                    },
                },
            );

        if (
            result.state
        ) {
            applyStateCursor(
                result.state,
            );

            currentState.serverSnapshot =
                result.state.snapshot
                    ? normalizeSnapshot(
                        result.state
                            .snapshot,
                    )
                    : currentState.serverSnapshot;

            currentState.generation =
                result.state.generation
                    ? clone(
                        result.state
                            .generation,
                    )
                    : null;
        }

        await dbDeleteOperation(
            operation.opId,
        );

        await persistCursor();

        return true;
    } catch (error) {
        if (
            error.code ===
                'st_not_persisted'
        ) {
            await saveCurrentChat(
                'pending-save-retry',
            );

            operation.snapshot =
                makeLocalSnapshot();

            operation.opId =
                uuid();

            await dbPutOperation(
                operation,
            );

            return false;
        }

        if (
            error.code ===
            'stale_revision'
        ) {
            if (
                error.state
                    ?.snapshot
            ) {
                const remoteSnapshot =
                    normalizeSnapshot(
                        error.state
                            .snapshot,
                    );

                const merged =
                    mergeSnapshots(
                        operation.baseSnapshot ||
                            currentState.serverSnapshot ||
                            remoteSnapshot,

                        operation.snapshot,

                        remoteSnapshot,
                    );

                applyStateCursor(
                    error.state,
                );

                currentState.serverSnapshot =
                    remoteSnapshot;

                operation.baseSnapshot =
                    clone(
                        remoteSnapshot,
                    );

                operation.baseRevision =
                    lastRevision;

                operation.snapshot =
                    clone(
                        merged.snapshot,
                    );

                operation.opId =
                    uuid();

                await applySnapshotLocally(
                    merged.snapshot,
                    {
                        persist:
                            true,

                        reason:
                            'stale-revision-rebase',
                    },
                );

                await dbPutOperation(
                    operation,
                );

                return sendPendingOperation(
                    operation,
                );
            }

            await resyncCurrentScope(
                'stale revision',
            );

            return false;
        }

        if (
            error.code ===
            'generation_lock'
        ) {
            return false;
        }

        if (
            [
                'not_member',
                'membership_expired',
                'scope_not_found',
            ].includes(
                error.code,
            )
        ) {
            await reconnectScope(
                'membership recovery',
            );

            return false;
        }

        warn(
            'Pending operation failed',
            error,
        );

        return false;
    }
}

async function drainPendingQueue() {
    if (
        queueDrainPromise
    ) {
        return queueDrainPromise;
    }

    queueDrainPromise =
        (async () => {
            try {
                const operations =
                    await dbGetOperations(
                        currentScope,
                    );

                for (
                    const operation of
                        operations
                ) {
                    const expectedEpoch =
                        currentEpoch();

                    const accepted =
                        await sendPendingOperation(
                            operation,
                        );

                    if (
                        expectedEpoch !==
                        currentEpoch()
                    ) {
                        return;
                    }

                    if (
                        !accepted
                    ) {
                        break;
                    }
                }

                const remaining =
                    await dbGetOperations(
                        currentScope,
                    );

                if (
                    !remaining.length
                ) {
                    currentState.pendingCount =
                        0;
                } else {
                    currentState.pendingCount =
                        remaining.length;
                }
            } finally {
                queueDrainPromise =
                    null;
            }
        })();

    return queueDrainPromise;
}


/* -------------------------------------------------------------------------- */
/* Resync                                                                     */
/* -------------------------------------------------------------------------- */

async function resyncCurrentScope(
    reason = 'manual',
) {
    if (
        !currentScope ||
        !pluginAvailable
    ) {
        return false;
    }

    if (
        resyncPromise
    ) {
        return resyncPromise;
    }

    const expectedEpoch =
        currentEpoch();

    resyncPromise =
        (async () => {
            const previousEventSource =
                eventSource;

            closeSse();

            try {
                setStatus(
                    'Resyncing',
                    reason,
                );

                const result =
                    await api(
                        '/state',
                        {
                            method:
                                'POST',

                            body: {
                                protocolVersion:
                                    PROTOCOL_VERSION,

                                clientId,

                                deviceId,

                                scope:
                                    currentScope,
                            },
                        },
                    );

                if (
                    expectedEpoch !==
                    currentEpoch()
                ) {
                    return false;
                }

                const serverState =
                    result.state;

                applyStateCursor(
                    serverState,
                );

                currentState =
                    currentState ||
                    {};

                currentState.generation =
                    serverState.generation
                        ? clone(
                            serverState.generation,
                        )
                        : null;

                const serverSnapshot =
                    serverState.snapshot
                        ? normalizeSnapshot(
                            serverState.snapshot,
                        )
                        : null;

                currentState.serverSnapshot =
                    serverSnapshot;

                const pending =
                    await dbGetOperations(
                        currentScope,
                    );

                currentState.pendingCount =
                    pending.length;

                if (
                    pending.length
                ) {
                    /*
                     * Preserve the local pending intent, rebase it against the
                     * authoritative server state, then save the resulting local
                     * state through ST.
                     */
                    const rebased =
                        await rebasePendingQueue(
                            serverSnapshot,
                            lastRevision,
                        );

                    if (
                        rebased
                    ) {
                        await applySnapshotLocally(
                            rebased,
                            {
                                persist:
                                    true,

                                reason:
                                    'pending-rebase',
                            },
                        );
                    }

                    await drainPendingQueue();
                } else if (
                    serverSnapshot
                ) {
                    /*
                     * With no pending operation, determine whether the local
                     * browser state is simply stale or requires an explicit
                     * out-of-band conflict choice.
                     */
                    const localSnapshot =
                        makeLocalSnapshot();

                    const localHash =
                        localSnapshot
                            ? await sha256(
                                localSnapshot,
                            )
                            : null;

                    const priorCursor =
                        await dbGetMeta(
                            stableStringify(
                                currentScope,
                            ),
                        );

                    const serverWon =
                        Boolean(
                            priorCursor?.epoch &&
                            priorCursor.epoch ===
                                serverState.epoch &&
                            Number(
                                priorCursor.revision,
                            ) <
                                Number(
                                    serverState.revision,
                                ),
                        );

                    if (
                        localHash !==
                        serverState.snapshotHash
                    ) {
                        if (
                            serverWon
                        ) {
                            await applySnapshotLocally(
                                serverSnapshot,
                                {
                                    persist:
                                        true,

                                    reason:
                                        'server-newer',
                                },
                            );
                        } else {
                            showDivergenceChoice(
                                localSnapshot,
                                serverSnapshot,
                            );
                        }
                    }
                }

                await persistCursor();

                /*
                 * Reconnect with an explicit fresh cursor now that state and
                 * revision are known.
                 */
                connectSse();

                setStatus(
                    'Live',
                    `revision ${lastRevision}`,
                );

                return true;
            } catch (error) {
                warn(
                    'Resync failed',
                    error,
                );

                if (
                    previousEventSource
                ) {
                    // intentionally not reused; a fresh connection is safer
                }

                scheduleReconnect(
                    error.code ||
                        'resync-failed',
                );

                return false;
            } finally {
                resyncPromise =
                    null;
            }
        })();

    return resyncPromise;
}

function scheduleResync(
    reason,
) {
    if (
        resyncTimer
    ) {
        clearTimeout(
            resyncTimer,
        );
    }

    resyncTimer =
        setTimeout(
            () => {
                resyncTimer =
                    null;

                void resyncCurrentScope(
                    reason,
                );
            },
            RESYNC_DELAY_MS,
        );
}


/* -------------------------------------------------------------------------- */
/* Divergence choice                                                          */
/* -------------------------------------------------------------------------- */

function showDivergenceChoice(
    localSnapshot,
    serverSnapshot,
) {
    setStatus(
        'Sync conflict',
        'The browser and server contain different state',
        [
            {
                label:
                    'Use server',

                run:
                    async () => {
                        await applySnapshotLocally(
                            serverSnapshot,
                            {
                                persist:
                                    true,

                                reason:
                                    'user-chose-server',
                            },
                        );
                    },
            },
            {
                label:
                    'Use current chat',

                run:
                    async () => {
                        await reconcileLocalToServer(
                            localSnapshot,
                        );
                    },
            },
        ],
    );
}

async function reconcileLocalToServer(
    snapshot,
) {
    try {
        const result =
            await api(
                '/event',
                {
                    method:
                        'POST',

                    body: {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        clientId,

                        deviceId,

                        scope:
                            currentScope,

                        opId:
                            uuid(),

                        type:
                            'reconcile_local',

                        baseRevision:
                            lastRevision,

                        snapshot,
                    },
                },
            );

        if (
            result.state
        ) {
            applyStateCursor(
                result.state,
            );

            currentState.serverSnapshot =
                result.state.snapshot
                    ? normalizeSnapshot(
                        result.state
                            .snapshot,
                    )
                    : currentState
                        .serverSnapshot;
        }

        setStatus(
            'Reconciled',
            'Current SillyTavern chat is now authoritative',
        );
    } catch (error) {
        warn(
            'Local reconciliation failed',
            error,
        );

        await resyncCurrentScope(
            'local reconciliation failed',
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Plugin dependency                                                           */
/* -------------------------------------------------------------------------- */

async function checkPlugin() {
    try {
        const result =
            await api(
                '/health',
                {
                    method:
                        'GET',
                },
            );

        if (
            Number(
                result.protocolVersion,
            ) !==
            PROTOCOL_VERSION
        ) {
            throw Object.assign(
                new Error(
                    'Protocol mismatch',
                ),
                {
                    code:
                        'protocol_mismatch',
                },
            );
        }

        principalKey =
            result.userKey ||
            null;

        pluginAvailable =
            true;

        return result;
    } catch (error) {
        pluginAvailable =
            false;

        principalKey =
            null;

        closeSse();

        clearHeartbeat();

        setStatus(
            error.code ===
                'protocol_mismatch'
                ? 'Plugin incompatible'
                : 'Server plugin required',

            error.code ===
                'protocol_mismatch'
                ? `Expected protocol ${PROTOCOL_VERSION}`
                : 'Multi-Client Sync server plugin is required',
        );

        schedulePluginRetry();

        return null;
    }
}

function schedulePluginRetry() {
    if (
        pluginRetryTimer ||
        stopping ||
        !getSettings().enabled
    ) {
        return;
    }

    pluginRetryTimer =
        setTimeout(
            async () => {
                pluginRetryTimer =
                    null;

                if (
                    await checkPlugin()
                ) {
                    const scope =
                        getCurrentScope();

                    if (
                        scope
                    ) {
                        await switchScope(
                            scope,
                        );
                    }
                }
            },
            PLUGIN_RETRY_MS,
        );
}

async function ensureConnected() {
    if (
        stopping ||
        !getSettings().enabled
    ) {
        return false;
    }

    if (
        pluginAvailable &&
        currentScope &&
        currentState
    ) {
        return true;
    }

    const plugin =
        await checkPlugin();

    if (
        !plugin
    ) {
        return false;
    }

    const scope =
        getCurrentScope();

    if (
        !scope
    ) {
        return false;
    }

    if (
        !sameScope(
            currentScope,
            scope,
        ) ||
        !currentState
    ) {
        await switchScope(
            scope,
        );
    }

    return Boolean(
        pluginAvailable &&
        currentScope &&
        currentState,
    );
}


/* -------------------------------------------------------------------------- */
/* Heartbeat                                                                  */
/* -------------------------------------------------------------------------- */

function clearHeartbeat() {
    if (
        heartbeatTimer
    ) {
        clearInterval(
            heartbeatTimer,
        );

        heartbeatTimer =
            null;
    }
}

function startHeartbeat() {
    clearHeartbeat();

    heartbeatTimer =
        setInterval(
            async () => {
                if (
                    !currentScope ||
                    !pluginAvailable ||
                    stopping
                ) {
                    return;
                }

                try {
                    const result =
                        await api(
                            '/heartbeat',
                            {
                                method:
                                    'POST',

                                body: {
                                    protocolVersion:
                                        PROTOCOL_VERSION,

                                    clientId,

                                    deviceId,

                                    scope:
                                        currentScope,

                                    generationId:
                                        isLocalGenerationOwner()
                                            ? currentState
                                                .generation
                                                .id
                                            : null,
                                },
                            },
                        );

                    if (
                        result.subscriptionToken
                    ) {
                        subscriptionToken =
                            result.subscriptionToken;
                    }

                    if (
                        result.state
                    ) {
                        applyStateCursor(
                            result.state,
                        );

                        currentState.generation =
                            result.state
                                .generation
                                ? clone(
                                    result.state
                                        .generation,
                                )
                                : null;

                        /*
                         * If the server says the generation disappeared while
                         * this client still thinks ST is generating, fence it.
                         */
                        if (
                            localGenerationId &&
                            !currentState.generation
                        ) {
                            localGenerationLost =
                                true;

                            try {
                                ctx.stopGeneration?.();
                            } catch {
                                // ignored
                            }
                        }
                    }

                    await persistCursor();
                } catch (error) {
                    if (
                        [
                            'not_member',
                            'membership_expired',
                            'scope_not_found',
                        ].includes(
                            error.code,
                        )
                    ) {
                        await reconnectScope(
                            'heartbeat recovery',
                        );
                    }
                }
            },
            HEARTBEAT_MS,
        );
}


/* -------------------------------------------------------------------------- */
/* SSE                                                                         */
/* -------------------------------------------------------------------------- */

function closeSse() {
    if (
        eventSource
    ) {
        try {
            eventSource.close();
        } catch {
            // ignored
        }
    }

    eventSource =
        null;
}

function connectSse() {
    if (
        stopping ||
        !pluginAvailable ||
        !currentScope ||
        !subscriptionToken
    ) {
        return;
    }

    closeSse();

    let url =
        `${location.origin}${PLUGIN_BASE}/events`
        + `?token=${encodeURIComponent(
            subscriptionToken,
        )}`;

    if (
        lastEventId
    ) {
        url +=
            `&since=${encodeURIComponent(
                lastEventId,
            )}`;
    }

    try {
        eventSource =
            new EventSource(
                url,
                {
                    withCredentials:
                        true,
                },
            );
    } catch (error) {
        warn(
            'Could not create EventSource',
            error,
        );

        scheduleReconnect(
            'SSE creation failed',
        );

        return;
    }

    eventSource.addEventListener(
        'hello',
        event => {
            try {
                const data =
                    JSON.parse(
                        event.data,
                    );

                if (
                    data.protocolVersion !==
                    PROTOCOL_VERSION
                ) {
                    pluginAvailable =
                        false;

                    closeSse();

                    setStatus(
                        'Plugin incompatible',
                        `Server protocol ${data.protocolVersion}`,
                    );

                    schedulePluginRetry();

                    return;
                }

                if (
                    lastEpoch &&
                    data.epoch &&
                    lastEpoch !==
                        data.epoch
                ) {
                    /*
                     * Server restart.
                     */
                    lastEventId =
                        null;

                    lastSeq =
                        0;

                    lastRevision =
                        0;
                }

                /*
                 * If we have an explicit cursor from persistence, preserve it
                 * so historical replay can happen. Otherwise establish the
                 * current cursor from hello.
                 */
                if (
                    !lastEventId
                ) {
                    lastEpoch =
                        data.epoch;

                    lastSeq =
                        Number(
                            data.seq,
                        ) || 0;

                    lastRevision =
                        Number(
                            data.revision,
                        ) || 0;

                    lastEventId =
                        data.lastEventId ||
                        (
                            lastEpoch &&
                            lastSeq
                                ? `${lastEpoch}:${lastSeq}`
                                : null
                        );
                } else {
                    lastEpoch =
                        data.epoch;
                }

                if (
                    currentState
                ) {
                    currentState.generation =
                        data.generation
                            ? clone(
                                data.generation,
                            )
                            : currentState
                                .generation;
                }

                void persistCursor();

                setStatus(
                    'Live',
                    `revision ${lastRevision}`,
                );

                reconnectAttempt =
                    0;
            } catch (error) {
                warn(
                    'Invalid SSE hello',
                    error,
                );
            }
        },
    );

    eventSource.addEventListener(
        'replay',
        event => {
            void handleReplayEvent(
                event,
            );
        },
    );

    eventSource.addEventListener(
        'replay_complete',
        () => {
            void resyncCurrentScope(
                'replay complete',
            );
        },
    );

    eventSource.addEventListener(
        'resync_required',
        event => {
            let reason =
                'server requested resync';

            try {
                const data =
                    JSON.parse(
                        event.data,
                    );

                reason =
                    data.reason ||
                    reason;
            } catch {
                // ignored
            }

            lastEventId =
                null;

            void resyncCurrentScope(
                reason,
            );
        },
    );

    eventSource.addEventListener(
        'sync',
        event => {
            void handleLiveEvent(
                event,
            );
        },
    );

    eventSource.addEventListener(
        'shutdown',
        () => {
            closeSse();

            setStatus(
                'Server restarting',
                'Synchronization will reconnect automatically',
            );

            scheduleReconnect(
                'server shutdown',
            );
        },
    );

    eventSource.onerror =
        () => {
            scheduleResync(
                'SSE error',
            );
        };
}

async function handleReplayEvent(
    event,
) {
    try {
        const data =
            JSON.parse(
                event.data,
            );

        if (
            lastEpoch &&
            data.epoch !==
                lastEpoch
        ) {
            await resyncCurrentScope(
                'replay epoch mismatch',
            );

            return;
        }

        const seq =
            Number(
                data.seq,
            );

        if (
            !Number.isSafeInteger(
                seq,
            )
        ) {
            await resyncCurrentScope(
                'invalid replay sequence',
            );

            return;
        }

        if (
            lastSeq > 0 &&
            seq >
                lastSeq + 1
        ) {
            await resyncCurrentScope(
                'replay sequence gap',
            );

            return;
        }

        if (
            seq <=
            lastSeq
        ) {
            return;
        }

        lastSeq =
            seq;

        lastRevision =
            Number(
                data.revision,
            );

        lastEpoch =
            data.epoch;

        lastEventId =
            data.id ||
            `${lastEpoch}:${lastSeq}`;

        await persistCursor();
    } catch (error) {
        warn(
            'Replay event processing failed',
            error,
        );

        await resyncCurrentScope(
            'replay parse failure',
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Live event handling                                                        */
/* -------------------------------------------------------------------------- */

async function handleLiveEvent(
    event,
) {
    const expectedEpoch =
        currentEpoch();

    try {
        const data =
            JSON.parse(
                event.data,
            );

        if (
            expectedEpoch !==
                currentEpoch()
        ) {
            return;
        }

        if (
            data.epoch !==
            lastEpoch &&
            lastEpoch
        ) {
            await resyncCurrentScope(
                'live epoch mismatch',
            );

            return;
        }

        const seq =
            Number(
                data.seq,
            );

        const revision =
            Number(
                data.revision ||
                data.state?.revision,
            );

        const baseRevision =
            Number(
                data.baseRevision,
            );

        if (
            !Number.isSafeInteger(
                seq,
            ) ||
            !Number.isSafeInteger(
                revision,
            )
        ) {
            await resyncCurrentScope(
                'invalid live event sequence',
            );

            return;
        }

        /*
         * Ignore duplicates.
         */
        if (
            seq <=
            lastSeq
        ) {
            return;
        }

        /*
         * Require exact contiguous ordering.
         */
        if (
            lastSeq > 0 &&
            seq !==
                lastSeq + 1
        ) {
            await resyncCurrentScope(
                'live sequence gap',
            );

            return;
        }

        /*
         * Every accepted mutation advances revision by one.
         */
        if (
            lastRevision > 0 &&
            (
                baseRevision !==
                lastRevision ||
                revision !==
                lastRevision + 1
            )
        ) {
            await resyncCurrentScope(
                'live revision conflict',
            );

            return;
        }

        const sourceClientId =
            data.sourceClientId;

        const isLocalSource =
            sourceClientId ===
            clientId;

        const isStream =
            data.type ===
            'generation_stream';

        if (
            data.state
        ) {
            applyStateCursor(
                data.state,
            );
        }

        if (
            isLocalSource
        ) {
            /*
             * We already have our own local state. The accepted server event
             * becomes the new authoritative server base.
             */
            const localSnapshot =
                makeLocalSnapshot();

            if (
                localSnapshot
            ) {
                currentState.serverSnapshot =
                    clone(
                        localSnapshot,
                    );
            }

            if (
                data.state
            ) {
                currentState.generation =
                    data.state
                        .generation
                        ? clone(
                            data.state
                                .generation,
                        )
                        : null;
            }
        } else {
            const pending =
                await dbGetOperations(
                    currentScope,
                );

            if (
                pending.length
            ) {
                /*
                 * Remote authority moved forward while this client has local
                 * pending work. Preserve local intent, rebase it, then retry.
                 */
                if (
                    data.patch?.kind ===
                        'full'
                ) {
                    const remoteSnapshot =
                        normalizeSnapshot(
                            data.patch
                                .snapshot,
                        );

                    currentState.serverSnapshot =
                        remoteSnapshot;

                    const rebased =
                        await rebasePendingQueue(
                            remoteSnapshot,
                            revision,
                        );

                    if (
                        rebased
                    ) {
                        await applySnapshotLocally(
                            rebased,
                            {
                                persist:
                                    true,

                                reason:
                                    'remote-with-pending',
                            },
                        );
                    }

                    void drainPendingQueue();
                } else {
                    await resyncCurrentScope(
                        'remote event with pending operations',
                    );

                    return;
                }
            } else if (
                data.patch
            ) {
                const patch =
                    data.patch;

                if (
                    patch.kind ===
                    'full'
                ) {
                    currentState.serverSnapshot =
                        normalizeSnapshot(
                            patch.snapshot,
                        );

                    await applySnapshotLocally(
                        patch.snapshot,
                        {
                            persist:
                                !isStream,

                            reason:
                                data.type,
                        },
                    );
                } else {
                    currentState.serverSnapshot =
                        applyPatchToSnapshot(
                            currentState.serverSnapshot,
                            patch,
                        );

                    await applyPatchLocally(
                        patch,
                        {
                            persist:
                                !isStream,

                            reason:
                                data.type,
                        },
                    );
                }
            }
        }

        /*
         * Generation control is handled separately.
         */
        await handleGenerationEvent(
            data,
        );

        lastSeq =
            seq;

        lastRevision =
            revision;

        lastEpoch =
            data.epoch ||
            lastEpoch;

        lastEventId =
            data.id ||
            `${lastEpoch}:${lastSeq}`;

        await persistCursor();

        if (
            data.state
                ?.generation
        ) {
            currentState.generation =
                clone(
                    data.state
                        .generation,
                );
        } else if (
            [
                'generation_terminal',
                'generation_abandoned',
            ].includes(
                data.type,
            )
        ) {
            currentState.generation =
                null;
        }

        if (
            !data.state
                ?.generation &&
            !isLocalGenerationOwner()
        ) {
            setStatus(
                'Synced',
                `revision ${lastRevision}`,
            );
        }
    } catch (error) {
        warn(
            'Live synchronization event failed',
            error,
        );

        await resyncCurrentScope(
            'live event failure',
        );
    }
}

function applyPatchToSnapshot(
    current,
    patch,
) {
    if (
        !current
    ) {
        return null;
    }

    const snapshot =
        clone(current);

    if (
        patch.kind ===
        'append'
    ) {
        snapshot.chat.splice(
            Number(
                patch.startIndex,
            ),
            0,
            ...(
                patch.messages ||
                []
            ).map(
                clone,
            ),
        );
    }

    if (
        patch.kind ===
        'patch'
    ) {
        for (
            const change of
                patch.changes ||
                []
        ) {
            const index =
                Number(
                    change.index,
                );

            if (
                Number.isInteger(
                    index,
                ) &&
                index >= 1
            ) {
                snapshot.chat[index] =
                    clone(
                        change.message,
                    );
            }
        }
    }

    if (
        patch.chatMetadata
    ) {
        snapshot.chatMetadata =
            clone(
                patch.chatMetadata,
            );

        if (
            snapshot.chat[0]
        ) {
            snapshot.chat[0]
                .chat_metadata =
                clone(
                    patch.chatMetadata,
                );
        }
    }

    return snapshot;
}


/* -------------------------------------------------------------------------- */
/* Generation SSE handling                                                    */
/* -------------------------------------------------------------------------- */

async function handleGenerationEvent(
    data,
) {
    if (
        data.type ===
        'generation_claimed'
    ) {
        const generation =
            data.generation ||
            data.state?.generation ||
            null;

        currentState.generation =
            generation
                ? clone(
                    generation,
                )
                : null;

        if (
            generation &&
            generation.ownerClientId !==
                clientId &&
            localGenerationId
        ) {
            localGenerationLost =
                true;

            try {
                ctx.stopGeneration?.();
            } catch {
                // ignored
            }
        }

        return;
    }

    if (
        data.type ===
        'generation_started'
    ) {
        if (
            data.generation
        ) {
            currentState.generation =
                clone(
                    data.generation,
                );
        }

        if (
            data.generation
                ?.ownerClientId !==
                clientId &&
            localGenerationId
        ) {
            localGenerationLost =
                true;

            try {
                ctx.stopGeneration?.();
            } catch {
                // ignored
            }
        }

        return;
    }

    if (
        data.type ===
        'generation_stop_requested'
    ) {
        const generation =
            data.generation ||
            data.state?.generation ||
            currentState.generation;

        if (
            generation &&
            generation.ownerClientId ===
                clientId &&
            generation.id ===
                localGenerationId
        ) {
            localStopRequested =
                true;

            setStatus(
                'Stop requested',
                'Stopping local generation',
            );

            try {
                ctx.stopGeneration?.();
            } catch (error) {
                warn(
                    'Remote stop could not be executed',
                    error,
                );
            }
        }

        currentState.generation =
            generation
                ? clone(
                    generation,
                )
                : null;

        return;
    }

    if (
        data.type ===
            'generation_abandoned' ||
        data.type ===
            'generation_terminal'
    ) {
        const generation =
            data.generation ||
            null;

        if (
            generation?.ownerClientId ===
                clientId &&
            generation.id ===
                localGenerationId
        ) {
            localGenerationLost =
                true;

            if (
                !localStopRequested
            ) {
                try {
                    ctx.stopGeneration?.();
                } catch {
                    // ignored
                }
            }
        }

        currentState.generation =
            data.type ===
                'generation_terminal' ||
                data.type ===
                    'generation_abandoned'
                ? null
                : generation;

        if (
            generation?.id
        ) {
            generationTerminalizing.delete(
                generation.id,
            );
        }

        return;
    }
}


/* -------------------------------------------------------------------------- */
/* Generation stream pipeline                                                 */
/* -------------------------------------------------------------------------- */

function queueStreamUpdate(
    reason = 'token',
) {
    if (
        !isLocalGenerationOwner()
    ) {
        return;
    }

    latestStreamSnapshot =
        makeLocalSnapshot();

    latestStreamReason =
        reason;

    if (
        streamTimer
    ) {
        return;
    }

    streamTimer =
        setTimeout(
            () => {
                streamTimer =
                    null;

                void flushStreamUpdate();
            },
            STREAM_FLUSH_MS,
        );
}

async function flushStreamUpdate() {
    if (
        streamFlushPromise ||
        !isLocalGenerationOwner() ||
        !latestStreamSnapshot
    ) {
        return;
    }

    const snapshot =
        latestStreamSnapshot;

    const reason =
        latestStreamReason;

    latestStreamSnapshot =
        null;

    latestStreamReason =
        null;

    const generation =
        currentState.generation;

    const streamSeq =
        Number(
            generation.streamSeq ||
                0,
        ) + 1;

    const expectedEpoch =
        currentEpoch();

    streamFlushPromise =
        (async () => {
            try {
                const result =
                    await api(
                        '/event',
                        {
                            method:
                                'POST',

                            body: {
                                protocolVersion:
                                    PROTOCOL_VERSION,

                                clientId,

                                deviceId,

                                scope:
                                    currentScope,

                                opId:
                                    uuid(),

                                type:
                                    'generation_stream',

                                generationId:
                                    generation.id,

                                streamSeq,

                                baseRevision:
                                    lastRevision,

                                payload: {
                                    reason,
                                },

                                snapshot,
                            },
                        },
                    );

                if (
                    expectedEpoch !==
                    currentEpoch()
                ) {
                    return;
                }

                if (
                    result.state
                ) {
                    applyStateCursor(
                        result.state,
                    );

                    currentState.generation =
                        result.state
                            .generation
                            ? clone(
                                result.state
                                    .generation,
                            )
                            : null;
                }

                if (
                    result.state
                        ?.generation
                        ?.ownerClientId !==
                    clientId
                ) {
                    localGenerationLost =
                        true;

                    try {
                        ctx.stopGeneration?.();
                    } catch {
                        // ignored
                    }
                }

                await persistCursor();
            } catch (error) {
                if (
                    [
                        'generation_stale',
                        'generation_not_owner',
                        'generation_expired',
                    ].includes(
                        error.code,
                    )
                ) {
                    localGenerationLost =
                        true;

                    try {
                        ctx.stopGeneration?.();
                    } catch {
                        // ignored
                    }
                } else if (
                    error.code ===
                        'stale_revision' ||
                    error.code ===
                        'stream_sequence_gap'
                ) {
                    await resyncCurrentScope(
                        `generation stream ${error.code}`,
                    );
                } else {
                    warn(
                        'Generation stream failed',
                        error,
                    );
                }
            } finally {
                streamFlushPromise =
                    null;

                if (
                    latestStreamSnapshot &&
                    isLocalGenerationOwner()
                ) {
                    void flushStreamUpdate();
                }
            }
        })();

    return streamFlushPromise;
}


/* -------------------------------------------------------------------------- */
/* Generation terminal                                                        */
/* -------------------------------------------------------------------------- */

async function finishGeneration(
    status,
) {
    const generation =
        currentState?.generation;

    if (
        !generation ||
        !isLocalGenerationOwner()
    ) {
        return;
    }

    if (
        generationTerminalizing.has(
            generation.id,
        )
    ) {
        return;
    }

    generationTerminalizing.add(
        generation.id,
    );

    try {
        await flushStreamUpdate();

        while (
            streamFlushPromise
        ) {
            await new Promise(
                resolve =>
                    setTimeout(
                        resolve,
                        25,
                    ),
            );
        }

        await saveCurrentChat(
            'generation-terminal',
        );

        const snapshot =
            makeLocalSnapshot();

        if (!snapshot) {
            return;
        }

        const generationId =
            generation.id;

        try {
            const result =
                await api(
                    '/event',
                    {
                        method:
                            'POST',

                        body: {
                            protocolVersion:
                                PROTOCOL_VERSION,

                            clientId,

                            deviceId,

                            scope:
                                currentScope,

                            opId:
                                uuid(),

                            type:
                                'generation_terminal',

                            generationId,

                            status,

                            baseRevision:
                                lastRevision,

                            snapshot,
                        },
                    },
                );

            if (
                result.state
            ) {
                applyStateCursor(
                    result.state,
                );

                currentState.generation =
                    result.state
                        .generation
                        ? clone(
                            result.state
                                .generation,
                        )
                        : null;
            }

            await persistCursor();

            localGenerationId =
                null;

            localGenerationLost =
                false;

            localStopRequested =
                false;

            setStatus(
                'Synced',
                `${status}; revision ${lastRevision}`,
            );
        } catch (error) {
            if (
                error.code ===
                'st_not_persisted'
            ) {
                /*
                 * One deliberate retry after another ST save.
                 */
                await saveCurrentChat(
                    'generation-terminal-retry',
                );

                const retrySnapshot =
                    makeLocalSnapshot();

                const retry =
                    await api(
                        '/event',
                        {
                            method:
                                'POST',

                            body: {
                                protocolVersion:
                                    PROTOCOL_VERSION,

                                clientId,

                                deviceId,

                                scope:
                                    currentScope,

                                opId:
                                    uuid(),

                                type:
                                    'generation_terminal',

                                generationId,

                                status,

                                baseRevision:
                                    lastRevision,

                                snapshot:
                                    retrySnapshot,
                            },
                        },
                    );

                if (
                    retry.state
                ) {
                    applyStateCursor(
                        retry.state,
                    );

                    currentState.generation =
                        retry.state
                            .generation
                            ? clone(
                                retry.state
                                    .generation,
                            )
                            : null;
                }

                await persistCursor();

                localGenerationId =
                    null;

                localGenerationLost =
                    false;

                localStopRequested =
                    false;

                return;
            }

            if (
                error.code ===
                'stale_revision'
            ) {
                await resyncCurrentScope(
                    'generation terminal stale revision',
                );
            } else {
                warn(
                    'Generation terminal failed',
                    error,
                );
            }
        }
    } finally {
        generationTerminalizing.delete(
            generation.id,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Chat mutation event handlers                                               */
/* -------------------------------------------------------------------------- */

function scheduleMutation(
    type,
    payload = {},
) {
    if (
        applyingRemoteDepth >
            0 ||
        !pluginAvailable ||
        !getSettings().enabled ||
        !currentScope
    ) {
        return;
    }

    if (
        currentState?.generation &&
        !isLocalGenerationOwner()
    ) {
        return;
    }

    if (
        isLocalGenerationOwner()
    ) {
        queueStreamUpdate(
            type,
        );

        return;
    }

    if (
        resyncTimer
    ) {
        clearTimeout(
            resyncTimer,
        );
    }

    resyncTimer =
        setTimeout(
            () => {
                resyncTimer =
                    null;

                void enqueueLocalMutation(
                    type,
                    payload,
                );
            },
            RESYNC_DELAY_MS,
        );
}


/* -------------------------------------------------------------------------- */
/* ST listeners                                                               */
/* -------------------------------------------------------------------------- */

function bindStEvent(
    eventName,
    handler,
) {
    if (
        !eventName ||
        !ctx?.eventSource
    ) {
        return;
    }

    ctx.eventSource.on(
        eventName,
        handler,
    );

    stListeners.push([
        eventName,
        handler,
    ]);
}

function unbindStEvents() {
    if (
        !ctx?.eventSource
    ) {
        return;
    }

    for (
        const [
            eventName,
            handler,
        ] of stListeners
    ) {
        try {
            ctx.eventSource.removeListener(
                eventName,
                handler,
            );
        } catch {
            // ignored
        }
    }

    stListeners = [];
}

function bindStEvents() {
    const e =
        ctx?.eventTypes;

    if (!e) {
        return;
    }

    bindStEvent(
        e.MESSAGE_SENT,
        () =>
            scheduleMutation(
                'message_sent',
            ),
    );

    bindStEvent(
        e.MESSAGE_RECEIVED,
        () =>
            scheduleMutation(
                'message_received',
            ),
    );

    bindStEvent(
        e.MESSAGE_EDITED,
        (...args) =>
            scheduleMutation(
                'message_edited',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_DELETED,
        (...args) =>
            scheduleMutation(
                'message_deleted',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_UPDATED,
        (...args) =>
            scheduleMutation(
                'message_updated',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_SWIPED,
        (...args) =>
            scheduleMutation(
                'message_swiped',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_SWIPE_DELETED,
        (...args) =>
            scheduleMutation(
                'message_swipe_deleted',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_FILE_EMBEDDED,
        (...args) =>
            scheduleMutation(
                'message_file_embedded',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.FILE_ATTACHMENT_DELETED,
        (...args) =>
            scheduleMutation(
                'file_attachment_deleted',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MEDIA_ATTACHMENT_DELETED,
        (...args) =>
            scheduleMutation(
                'media_attachment_deleted',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_REASONING_EDITED,
        (...args) =>
            scheduleMutation(
                'message_reasoning_edited',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.MESSAGE_REASONING_DELETED,
        (...args) =>
            scheduleMutation(
                'message_reasoning_deleted',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.STREAM_REASONING_DONE,
        (...args) =>
            scheduleMutation(
                'stream_reasoning_done',
                {
                    args,
                },
            ),
    );

    bindStEvent(
        e.TOOL_CALLS_PERFORMED,
        (...args) =>
            scheduleMutation(
                'tool_calls_performed',
                {
                    args,
                },
            ),
    );

    /*
     * MORE_MESSAGES_LOADED is not a mutation.
     */
    bindStEvent(
        e.MORE_MESSAGES_LOADED,
        () =>
            scheduleResync(
                'more messages loaded',
            ),
    );

    bindStEvent(
        e.CHAT_LOADED,
        () =>
            void handleChatLifecycle(
                'chat_loaded',
            ),
    );

    bindStEvent(
        e.CHAT_CHANGED,
        () =>
            void handleChatLifecycle(
                'chat_changed',
            ),
    );

    bindStEvent(
        e.CHAT_CREATED,
        () =>
            void handleChatLifecycle(
                'chat_created',
            ),
    );

    bindStEvent(
        e.CHAT_DELETED,
        () =>
            void handleChatLifecycle(
                'chat_deleted',
            ),
    );

    bindStEvent(
        e.CHAT_RENAMED,
        () =>
            void handleChatLifecycle(
                'chat_renamed',
            ),
    );

    bindStEvent(
        e.GROUP_CHAT_CREATED,
        () =>
            void handleChatLifecycle(
                'group_chat_created',
            ),
    );

    bindStEvent(
        e.GROUP_CHAT_DELETED,
        () =>
            void handleChatLifecycle(
                'group_chat_deleted',
            ),
    );

    bindStEvent(
        e.GROUP_UPDATED,
        () =>
            void handleChatLifecycle(
                'group_updated',
            ),
    );


    /*
     * Fallback generation path.
     *
     * The stronger path is generate_interceptor above.
     */
    bindStEvent(
        e.GENERATION_STARTED,
        async type => {
            if (
                applyingRemoteDepth >
                    0 ||
                !getSettings().enabled
            ) {
                return;
            }

            const available =
                await ensureConnected();

            if (!available) {
                return;
            }

            const generation =
                activeGeneration();

            if (
                generation &&
                !isLocalGenerationOwner()
            ) {
                localGenerationLost =
                    true;

                try {
                    ctx.stopGeneration?.();
                } catch {
                    // ignored
                }

                return;
            }

            if (
                isLocalGenerationOwner()
            ) {
                if (
                    generation.state !==
                    'streaming'
                ) {
                    try {
                        const result =
                            await api(
                                '/event',
                                {
                                    method:
                                        'POST',

                                    body: {
                                        protocolVersion:
                                            PROTOCOL_VERSION,

                                        clientId,

                                        deviceId,

                                        scope:
                                            currentScope,

                                        opId:
                                            uuid(),

                                        type:
                                            'generation_started',

                                        baseRevision:
                                            lastRevision,

                                        generationId:
                                            generation.id,
                                    },
                                },
                            );

                        if (
                            result.state
                        ) {
                            applyStateCursor(
                                result.state,
                            );

                            currentState.generation =
                                result.state
                                    .generation
                                    ? clone(
                                        result.state
                                            .generation,
                                    )
                                    : null;
                        }
                    } catch (error) {
                        warn(
                            'Fallback generation start failed',
                            error,
                        );

                        localGenerationLost =
                            true;

                        try {
                            ctx.stopGeneration?.();
                        } catch {
                            // ignored
                        }
                    }
                }

                return;
            }

            const claimed =
                await claimGeneration(
                    type,
                    getLastMessageSyncId(),
                );

            if (!claimed) {
                try {
                    ctx.stopGeneration?.();
                } catch {
                    // ignored
                }

                return;
            }

            try {
                const result =
                    await api(
                        '/event',
                        {
                            method:
                                'POST',

                            body: {
                                protocolVersion:
                                    PROTOCOL_VERSION,

                                clientId,

                                deviceId,

                                scope:
                                    currentScope,

                                opId:
                                    uuid(),

                                type:
                                    'generation_started',

                                baseRevision:
                                    lastRevision,

                                generationId:
                                    currentState
                                        .generation
                                        .id,
                            },
                        },
                    );

                if (
                    result.state
                ) {
                    applyStateCursor(
                        result.state,
                    );
                }
            } catch (error) {
                warn(
                    'Generation start failed',
                    error,
                );

                localGenerationLost =
                    true;

                try {
                    ctx.stopGeneration?.();
                } catch {
                    // ignored
                }
            }
        },
    );

    bindStEvent(
        e.STREAM_TOKEN_RECEIVED,
        () =>
            queueStreamUpdate(
                'token',
            ),
    );

    bindStEvent(
        e.GENERATION_STOPPED,
        async () => {
            if (
                isLocalGenerationOwner()
            ) {
                localStopRequested =
                    true;

                await finishGeneration(
                    'stopped',
                );
            }
        },
    );

    bindStEvent(
        e.GENERATION_ENDED,
        async () => {
            if (
                !isLocalGenerationOwner()
            ) {
                return;
            }

            if (
                finalizationTimer
            ) {
                clearTimeout(
                    finalizationTimer,
                );
            }

            finalizationTimer =
                setTimeout(
                    () => {
                        finalizationTimer =
                            null;

                        void finishGeneration(
                            localStopRequested
                                ? 'stopped'
                                : 'completed',
                        );
                    },
                    250,
                );
        },
    );
}


/* -------------------------------------------------------------------------- */
/* Chat lifecycle                                                              */
/* -------------------------------------------------------------------------- */

async function handleChatLifecycle(
    reason,
) {
    if (
        applyingRemoteDepth >
            0 ||
        stopping ||
        !getSettings().enabled
    ) {
        return;
    }

    const nextScope =
        getCurrentScope();

    if (
        !nextScope
    ) {
        await switchScope(
            null,
        );

        return;
    }

    if (
        !sameScope(
            currentScope,
            nextScope,
        )
    ) {
        await switchScope(
            nextScope,
        );

        return;
    }

    if (
        pluginAvailable
    ) {
        scheduleResync(
            reason,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Scope switching                                                             */
/* -------------------------------------------------------------------------- */

async function switchScope(
    nextScope,
) {
    const previousScope =
        currentScope;

    scopeEpoch +=
        1;

    const expectedEpoch =
        scopeEpoch;

    clearHeartbeat();
    closeSse();

    if (
        reconnectTimer
    ) {
        clearTimeout(
            reconnectTimer,
        );

        reconnectTimer =
            null;
    }

    if (
        resyncTimer
    ) {
        clearTimeout(
            resyncTimer,
        );

        resyncTimer =
            null;
    }

    if (
        streamTimer
    ) {
        clearTimeout(
            streamTimer,
        );

        streamTimer =
            null;
    }

    if (
        finalizationTimer
    ) {
        clearTimeout(
            finalizationTimer,
        );

        finalizationTimer =
            null;
    }

    latestStreamSnapshot =
        null;

    latestStreamReason =
        null;

    currentScope =
        nextScope
            ? clone(
                nextScope,
            )
            : null;

    currentState =
        null;

    subscriptionToken =
        null;

    localGenerationId =
        null;

    localGenerationLost =
        false;

    localStopRequested =
        false;

    lastEventId =
        null;

    lastEpoch =
        null;

    lastSeq =
        0;

    lastRevision =
        0;

    if (
        previousScope &&
        pluginAvailable
    ) {
        try {
            await api(
                '/leave',
                {
                    method:
                        'POST',

                    body: {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        clientId,

                        deviceId,

                        scope:
                            previousScope,
                    },
                },
            );
        } catch {
            /*
             * Leave is best-effort. Server membership expiry is the crash-safe
             * fallback.
             */
        }
    }

    if (
        expectedEpoch !==
        scopeEpoch ||
        !currentScope ||
        stopping ||
        !getSettings().enabled
    ) {
        return;
    }

    const available =
        await checkPlugin();

    if (
        !available
    ) {
        return;
    }

    try {
        await joinCurrentScope(
            currentScope,
        );
    } catch (error) {
        warn(
            'Scope join failed',
            error,
        );

        setStatus(
            'Sync unavailable',
            error.message ||
                error.code ||
                'join failed',
        );

        scheduleReconnect(
            'join failed',
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Join                                                                      */
/* -------------------------------------------------------------------------- */

async function joinCurrentScope(
    scope,
) {
    const expectedEpoch =
        currentEpoch();

    const previousCursor =
        await dbGetMeta(
            stableStringify(
                scope,
            ),
        );

    const result =
        await api(
            '/join',
            {
                method:
                    'POST',

                body: {
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId,

                    deviceId,

                    scope,
                },
            },
        );

    if (
        expectedEpoch !==
            currentEpoch() ||
        !sameScope(
            currentScope,
            scope,
        )
    ) {
        return;
    }

    principalKey =
        result.principalKey;

    subscriptionToken =
        result.subscriptionToken;

    currentState = {
        serverSnapshot:
            result.state
                ?.snapshot
                ? normalizeSnapshot(
                    result.state
                        .snapshot,
                )
                : null,

        generation:
            result.state
                ?.generation
                ? clone(
                    result.state
                        .generation,
                )
                : null,

        pendingCount:
            0,

        serverEpoch:
            result.state?.epoch ||
            null,
    };

    applyStateCursor(
        result.state,
    );

    /*
     * Preserve older replay cursor if it belongs to the same server epoch.
     */
    if (
        previousCursor?.lastEpoch &&
        previousCursor.lastEpoch ===
            result.state?.epoch &&
        Number.isSafeInteger(
            Number(
                previousCursor.lastSeq,
            ),
        ) &&
        Number(
            previousCursor.lastSeq,
        ) <
            Number(
                result.state.seq,
            )
    ) {
        lastEpoch =
            previousCursor.lastEpoch;

        lastSeq =
            Number(
                previousCursor.lastSeq,
            );

        lastRevision =
            Number(
                previousCursor.lastRevision,
            ) || 0;

        lastEventId =
            previousCursor.lastEventId ||
            null;
    }


    const pending =
        await dbGetOperations(
            scope,
        );

    currentState.pendingCount =
        pending.length;

    /*
     * Make sure the local browser state uses stable IDs before comparing hashes.
     */
    const migrated =
        ensureMessageIds(
            ctx.chat,
        );

    if (
        migrated
    ) {
        await saveCurrentChat(
            'stable-message-id-migration',
        );
    }

    const localSnapshot =
        makeLocalSnapshot();

    const localHash =
        localSnapshot
            ? await sha256(
                localSnapshot,
            )
            : null;

    const serverSnapshot =
        currentState.serverSnapshot;


    /*
     * No server state yet.
     *
     * If ST already has a real file, the server's JOIN has normally populated
     * the state. So this branch mainly covers a newly created unsaved chat.
     */
    if (
        !serverSnapshot &&
        localSnapshot &&
        !pending.length
    ) {
        const bootstrap =
            {
                principalKey,

                opId:
                    uuid(),

                localSeq:
                    ++localSequence,

                scope:
                    clone(scope),

                type:
                    'bootstrap',

                payload: {},

                snapshot:
                    clone(
                        localSnapshot,
                    ),

                baseSnapshot:
                    clone(
                        localSnapshot,
                    ),

                baseRevision:
                    0,

                coalescible:
                    false,
            };

        await dbPutOperation(
            bootstrap,
        );

        await drainPendingQueue();
    } else if (
        serverSnapshot &&
        !pending.length
    ) {
        /*
         * With no local pending operations, decide whether server state should
         * win automatically or whether the local browser contains an out-of-
         * band change requiring an explicit user choice.
         */
        if (
            localHash !==
            result.state.snapshotHash
        ) {
            const serverWasNewer =
                Boolean(
                    previousCursor?.lastEpoch &&
                    previousCursor
                        .lastEpoch ===
                        result.state
                            .epoch &&
                    Number(
                        previousCursor
                            .lastRevision,
                    ) <
                        Number(
                            result.state
                                .revision,
                        ),
                );

            if (
                serverWasNewer
            ) {
                await applySnapshotLocally(
                    serverSnapshot,
                    {
                        persist:
                            true,

                        reason:
                            'server-newer-on-join',
                    },
                );
            } else {
                showDivergenceChoice(
                    localSnapshot,
                    serverSnapshot,
                );
            }
        }
    } else if (
        serverSnapshot &&
        pending.length
    ) {
        /*
         * Keep the local pending intent, but rebase it against current server
         * authority before transmitting it.
         */
        const rebased =
            await rebasePendingQueue(
                serverSnapshot,
                lastRevision,
            );

        if (
            rebased
        ) {
            await applySnapshotLocally(
                rebased,
                {
                    persist:
                        true,

                    reason:
                        'join-pending-rebase',
                },
            );
        }

        await drainPendingQueue();
    }

    /*
     * If server reported a genuine persisted-file divergence, keep it visible
     * rather than silently declaring victory.
     */
    if (
        result.divergence
            ?.detected &&
        !pending.length
    ) {
        setStatus(
            'Sync conflict',
            'Server mirror and current ST chat differ',
            [
                {
                    label:
                        'Use server',

                    run:
                        () =>
                            applySnapshotLocally(
                                serverSnapshot,
                                {
                                    persist:
                                        true,

                                    reason:
                                        'server-divergence-choice',
                                },
                            ),
                },
                {
                    label:
                        'Use current',

                    run:
                        () =>
                            reconcileLocalToServer(
                                makeLocalSnapshot(),
                            ),
                },
            ],
        );
    }

    connectSse();

    startHeartbeat();

    await persistCursor();

    setStatus(
        'Live',
        `revision ${lastRevision}`,
    );
}


/* -------------------------------------------------------------------------- */
/* Reconnect                                                                  */
/* -------------------------------------------------------------------------- */

function scheduleReconnect(
    reason = 'disconnect',
) {
    if (
        stopping ||
        reconnectTimer ||
        !currentScope
    ) {
        return;
    }

    const delay =
        Math.min(
            MAX_RECONNECT_MS,

            500 *
                (
                    2 **
                    Math.min(
                        reconnectAttempt,
                        6,
                    )
                ) +

                Math.floor(
                    Math.random() *
                        400,
                ),
        );

    reconnectAttempt +=
        1;

    setStatus(
        'Reconnecting',
        `${reason}; ${Math.ceil(
            delay / 1000,
        )}s`,
    );

    reconnectTimer =
        setTimeout(
            async () => {
                reconnectTimer =
                    null;

                await reconnectScope(
                    reason,
                );
            },
            delay,
        );
}

async function reconnectScope(
    reason = 'reconnect',
) {
    if (
        !currentScope ||
        stopping
    ) {
        return false;
    }

    const available =
        await checkPlugin();

    if (
        !available
    ) {
        return false;
    }

    try {
        await switchScope(
            currentScope,
        );

        return true;
    } catch (error) {
        warn(
            'Reconnect failed',
            reason,
            error,
        );

        scheduleReconnect(
            reason,
        );

        return false;
    }
}


/* -------------------------------------------------------------------------- */
/* BroadcastChannel                                                           */
/* -------------------------------------------------------------------------- */

function startBroadcastChannel() {
    if (
        broadcastChannel
    ) {
        return;
    }

    try {
        broadcastChannel =
            new BroadcastChannel(
                `${EXTENSION_ID}:v4`,
            );

        broadcastChannel.addEventListener(
            'message',
            event => {
                void handleBroadcastMessage(
                    event.data,
                );
            },
        );
    } catch (error) {
        log(
            'BroadcastChannel unavailable',
            error,
        );

        broadcastChannel =
            null;
    }
}

function broadcastLocalChange(
    type,
) {
    try {
        broadcastChannel?.postMessage(
            {
                protocolVersion:
                    PROTOCOL_VERSION,

                sourceClientId:
                    clientId,

                sourceDeviceId:
                    deviceId,

                scope:
                    currentScope,

                type,

                kind:
                    'local_change',
            },
        );
    } catch {
        // ignored
    }
}

async function handleBroadcastMessage(
    message,
) {
    if (
        !message ||
        message.protocolVersion !==
            PROTOCOL_VERSION
    ) {
        return;
    }

    if (
        message.sourceClientId ===
        clientId
    ) {
        return;
    }

    if (
        !sameScope(
            message.scope,
            currentScope,
        )
    ) {
        return;
    }

    /*
     * BroadcastChannel is intentionally never applied as authority.
     * It simply asks the current browser tab to reconcile from the server.
     */
    if (
        message.kind ===
        'local_change'
    ) {
        scheduleResync(
            `same-browser peer: ${
                message.type ||
                'change'
            }`,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Browser lifecycle                                                          */
/* -------------------------------------------------------------------------- */

function bindBrowserEvents() {
    const online =
        () => {
            void reconnectScope(
                'browser online',
            );
        };

    const pageShow =
        () => {
            scheduleResync(
                'pageshow',
            );
        };

    const visibility =
        () => {
            if (
                document.visibilityState ===
                'visible'
            ) {
                scheduleResync(
                    'visibility resume',
                );
            }
        };

    window.addEventListener(
        'online',
        online,
    );

    window.addEventListener(
        'pageshow',
        pageShow,
    );

    document.addEventListener(
        'visibilitychange',
        visibility,
    );

    browserListeners.push(
        [
            'window',
            'online',
            online,
        ],
        [
            'window',
            'pageshow',
            pageShow,
        ],
        [
            'document',
            'visibilitychange',
            visibility,
        ],
    );
}

function unbindBrowserEvents() {
    for (
        const [
            target,
            event,
            handler,
        ] of browserListeners
    ) {
        try {
            if (
                target ===
                'window'
            ) {
                window.removeEventListener(
                    event,
                    handler,
                );
            } else {
                document.removeEventListener(
                    event,
                    handler,
                );
            }
        } catch {
            // ignored
        }
    }

    browserListeners =
        [];
}


/* -------------------------------------------------------------------------- */
/* Start / stop                                                               */
/* -------------------------------------------------------------------------- */

async function startInternal() {
    if (
        started &&
        !stopping
    ) {
        return;
    }

    stopping =
        false;

    ctx =
        SillyTavern.getContext();

    if (!ctx) {
        return;
    }

    getSettings();

    ensureUi();

    setStatus(
        'Starting',
        'Checking synchronization server',
    );

    bindStEvents();
    bindBrowserEvents();
    startBroadcastChannel();

    started =
        true;

    await checkPlugin();

    if (
        !pluginAvailable
    ) {
        return;
    }

    const scope =
        getCurrentScope();

    if (
        scope
    ) {
        await switchScope(
            scope,
        );
    } else {
        setStatus(
            'Ready',
            'Open a chat to start synchronization',
        );
    }
}

async function stopInternal() {
    stopping =
        true;

    scopeEpoch +=
        1;

    clearHeartbeat();

    closeSse();

    if (
        reconnectTimer
    ) {
        clearTimeout(
            reconnectTimer,
        );

        reconnectTimer =
            null;
    }

    if (
        pluginRetryTimer
    ) {
        clearTimeout(
            pluginRetryTimer,
        );

        pluginRetryTimer =
            null;
    }

    if (
        resyncTimer
    ) {
        clearTimeout(
            resyncTimer,
        );

        resyncTimer =
            null;
    }

    if (
        streamTimer
    ) {
        clearTimeout(
            streamTimer,
        );

        streamTimer =
            null;
    }

    if (
        finalizationTimer
    ) {
        clearTimeout(
            finalizationTimer,
        );

        finalizationTimer =
            null;
    }

    try {
        if (
            currentScope &&
            pluginAvailable
        ) {
            await api(
                '/leave',
                {
                    method:
                        'POST',

                    body: {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        clientId,

                        deviceId,

                        scope:
                            currentScope,
                    },
                },
            );
        }
    } catch {
        // best effort
    }

    unbindStEvents();
    unbindBrowserEvents();

    try {
        broadcastChannel?.close();
    } catch {
        // ignored
    }

    broadcastChannel =
        null;

    currentScope =
        null;

    currentState =
        null;

    subscriptionToken =
        null;

    pluginAvailable =
        false;

    principalKey =
        null;

    localGenerationId =
        null;

    localGenerationLost =
        false;

    localStopRequested =
        false;

    started =
        false;
}


/* -------------------------------------------------------------------------- */
/* Extension lifecycle hooks                                                  */
/* -------------------------------------------------------------------------- */

export async function init() {
    if (
        startPromise
    ) {
        return startPromise;
    }

    startPromise =
        startInternal()
            .finally(
                () => {
                    if (
                        !started
                    ) {
                        startPromise =
                            null;
                    }
                },
            );

    return startPromise;
}

export async function onInstall() {
    ctx =
        SillyTavern.getContext();

    if (!ctx) {
        return;
    }

    if (
        !ctx.extensionSettings[
            EXTENSION_ID
        ]
    ) {
        ctx.extensionSettings[
            EXTENSION_ID
        ] =
            structuredClone(
                DEFAULT_SETTINGS,
            );

        ctx.saveSettingsDebounced?.();
    }
}

export async function onUpdate() {
    /*
     * IndexedDB versioning is intentionally non-destructive.
     * Existing queued operations survive extension upgrades.
     */
    return init();
}

export async function onEnable() {
    const settings =
        getSettings();

    settings.enabled =
        true;

    ctx?.saveSettingsDebounced?.();

    return init();
}

export async function onDisable() {
    const settings =
        getSettings();

    settings.enabled =
        false;

    ctx?.saveSettingsDebounced?.();

    await stopInternal();

    setStatus(
        'Disabled',
        'Multi-client synchronization is disabled',
    );
}

export async function onDelete() {
    await stopInternal();
}

export async function onClean() {
    try {
        await dbClearAll();
    } catch {
        // ignored
    }
}


/* -------------------------------------------------------------------------- */
/* Minimal startup bootstrap                                                  */
/* -------------------------------------------------------------------------- */

/*
 * ST's current extension lifecycle invokes exported hooks from the manifest.
 * Keep an idempotent fallback for existing manifests that only load index.js.
 */
void (async () => {
    try {
        const eventTypes =
            SillyTavern
                .getContext?.()
                ?.eventTypes;

        if (
            eventTypes?.APP_READY
        ) {
            const eventSource =
                SillyTavern
                    .getContext()
                    .eventSource;

            eventSource.once(
                eventTypes.APP_READY,
                () => {
                    void init();
                },
            );
        } else {
            void init();
        }
    } catch {
        try {
            void init();
        } catch {
            // ignored
        }
    }
})();