const EXTENSION_ID = 'multi-client-sync';

const PLUGIN_BASE =
    '/api/plugins/multi-client-sync';

const PROTOCOL = 6;
const SCHEMA = 6;

const DB_NAME =
    'multi-client-sync';

const DB_VERSION = 6;

const DEVICE_STORAGE_KEY =
    `${EXTENSION_ID}:device-id`;

const CLIENT_STORAGE_KEY =
    `${EXTENSION_ID}:client-id`;

const MAX_QUEUE = 1_000;

const SNAPSHOT_CAPTURE_DELAY = 100;

const REMOTE_APPLY_TIMEOUT =
    15_000;

const defaultSettings = Object.freeze({
    enabled: true,
    autoConnect: true,

    syncMessages: true,
    syncMetadata: true,
    syncSwipes: true,

    syncGroupSettings: true,
    syncBranches: true,

    coordinateGeneration: true,
    remoteStop: true,

    notifications: true,
    debug: false,
});

let ctx = null;
let settings = null;

let started = false;
let startPromise = null;

let serverAvailable = false;
let serverCompatible = false;
let serverUserId = null;

let currentScope = null;
let currentState = null;

let scopeEpoch = 0;

let sse = null;
let sseReconnectTimer = null;
let reconnectAttempt = 0;
let sseEventChain =
    Promise.resolve();

let heartbeatTimer = null;
let generationHeartbeatTimer = null;

let localGeneration = null;
let localGenerationLost = false;

let finishingGeneration = false;

let applyingRemoteDepth = 0;
let hostMessageIdsDirty = false;

let captureTimer = null;
let captureScheduled = false;

let streamTimer = null;
let streamFlushPromise =
    Promise.resolve();

let pendingStreamMessage = null;

let uiRoot = null;

let listenerBindings = [];
let browserBindings = [];

let broadcastChannel = null;

let dbPromise = null;

let lastError = '';

function getContext() {
    return SillyTavern.getContext();
}

function log(...args) {
    if (settings?.debug) {
        console.debug(
            `[${EXTENSION_ID}]`,
            ...args,
        );
    }
}

function warn(...args) {
    console.warn(
        `[${EXTENSION_ID}]`,
        ...args,
    );
}

function toast(
    type,
    message,
) {
    if (!settings?.notifications) {
        return;
    }

    try {
        toastr[type]?.(
            message,
            'Multi-Client Sync',
        );
    } catch {}
}

function clone(value) {
    if (value === undefined) {
        return undefined;
    }

    return structuredClone(value);
}

function now() {
    return Date.now();
}

function randomId(
    prefix = '',
) {
    if (
        globalThis.crypto
        ?.randomUUID
    ) {
        return (
            prefix
            + globalThis.crypto
                .randomUUID()
                .replaceAll(
                    '-',
                    '',
                )
        );
    }

    return (
        prefix
        + Date.now().toString(36)
        + Math.random()
            .toString(36)
            .slice(2)
        + Math.random()
            .toString(36)
            .slice(2)
    );
}

async function sha256(
    value,
) {
    const bytes =
        new TextEncoder().encode(
            String(value),
        );

    if (
        globalThis.crypto
            ?.subtle
    ) {
        const hash =
            await globalThis.crypto
                .subtle
                .digest(
                    'SHA-256',
                    bytes,
                );

        return [
            ...new Uint8Array(hash),
        ]
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

    /*
     * Modern ST browsers normally expose WebCrypto.
     * Without it, do not pretend this fallback is SHA-256.
     */
    return null;
}

function sameScope(
    a,
    b,
) {
    return (
        !!a
        && !!b
        && JSON.stringify(a)
            === JSON.stringify(b)
    );
}

function scopeKey(
    scope,
) {
    if (!scope) {
        return '';
    }

    return [
        scope.kind,
        scope.kind === 'character'
            ? scope.character
            : scope.groupId,
        scope.chatId,
        scope.branchId
            || 'main',
    ].join('|');
}

function sameScopePrincipal(
    a,
    b,
) {
    return (
        !!a
        && !!b
        && scopeKey(a)
            === scopeKey(b)
    );
}

function isObject(value) {
    return value !== null
        && typeof value === 'object'
        && !Array.isArray(value);
}

const forbiddenKeys =
    new Set([
        '__proto__',
        'prototype',
        'constructor',
    ]);

function validateDataTree(
    value,
    depth = 0,
    seen = new WeakSet(),
) {
    if (depth > 40) {
        return false;
    }

    if (
        value === null
        || typeof value === 'string'
        || typeof value === 'boolean'
    ) {
        return true;
    }

    if (
        typeof value === 'number'
    ) {
        return Number.isFinite(
            value,
        );
    }

    if (
        typeof value !== 'object'
    ) {
        return false;
    }

    if (seen.has(value)) {
        return false;
    }

    seen.add(value);

    if (Array.isArray(value)) {
        return value.every(
            child =>
                validateDataTree(
                    child,
                    depth + 1,
                    seen,
                ),
        );
    }

    for (
        const [
            key,
            child,
        ]
        of Object.entries(value)
    ) {
        if (
            forbiddenKeys.has(key)
        ) {
            return false;
        }

        if (
            !validateDataTree(
                child,
                depth + 1,
                seen,
            )
        ) {
            return false;
        }
    }

    return true;
}

function stableMessageId(
    message,
) {
    const id =
        message
            ?.extra
            ?.multi_client_sync
            ?.messageId;

    return (
        typeof id === 'string'
        && id.length > 0
    )
        ? id
        : null;
}

function ensureMessageIds(
    snapshot,
) {
    const out =
        clone(
            Array.isArray(snapshot)
                ? snapshot
                : [],
        );

    const used =
        new Set();

    for (
        const message
        of out
    ) {
        if (!isObject(message)) {
            continue;
        }

        if (!isObject(message.extra)) {
            message.extra = {};
        }

        if (
            !isObject(
                message
                    .extra
                    .multi_client_sync,
            )
        ) {
            message.extra
                .multi_client_sync = {};
        }

        let id =
            stableMessageId(
                message,
            );

        if (
            !id
            || id.length > 128
            || /[\\/\u0000-\u001f]/
                .test(id)
            || used.has(id)
        ) {
            id =
                randomId('m_');

            message
                .extra
                .multi_client_sync
                .messageId = id;
        }

        used.add(id);
    }

    return out;
}

function normalizeSnapshot(
    snapshot,
) {
    const out =
        ensureMessageIds(
            snapshot,
        );

    if (
        !validateDataTree(out)
    ) {
        throw new Error(
            'Chat contains unsupported data.',
        );
    }

    return out;
}

function ensureHostMessageIds() {
    if (
        !Array.isArray(
            ctx?.chat,
        )
    ) {
        return false;
    }

    const used =
        new Set();

    let changed =
        false;

    for (
        const message
        of ctx.chat
    ) {
        if (!isObject(message)) {
            continue;
        }

        if (!isObject(message.extra)) {
            message.extra = {};
            changed = true;
        }

        if (
            !isObject(
                message
                    .extra
                    .multi_client_sync,
            )
        ) {
            message
                .extra
                .multi_client_sync = {};
            changed = true;
        }

        let id =
            stableMessageId(
                message,
            );

        if (
            !id
            || id.length > 128
            || /[\\/\u0000-\u001f]/
                .test(id)
            || used.has(id)
        ) {
            id =
                randomId('m_');

            changed = true;
        }

        if (
            message
                .extra
                .multi_client_sync
                .messageId
            !== id
        ) {
            changed = true;
        }

        message
            .extra
            .multi_client_sync
            .messageId = id;

        used.add(id);
    }

    if (changed) {
        hostMessageIdsDirty = true;
    }

    return changed;
}

function localSnapshot() {
    ensureHostMessageIds();

    return normalizeSnapshot(
        ctx.chat || [],
    );
}

function localMetadata() {
    return isObject(
        ctx?.chatMetadata,
    )
        ? clone(
            ctx.chatMetadata,
        )
        : {};
}

async function snapshotDigest(
    snapshot,
) {
    const data =
        JSON.stringify(
            snapshot,
        );

    return sha256(data);
}

function settingsRef() {
    ctx = getContext();

    if (
        !isObject(
            ctx.extensionSettings[
                EXTENSION_ID
            ],
        )
    ) {
        ctx.extensionSettings[
            EXTENSION_ID
        ] = clone(
            defaultSettings,
        );
    }

    const target =
        ctx.extensionSettings[
            EXTENSION_ID
        ];

    for (
        const [
            key,
            value,
        ]
        of Object.entries(
            defaultSettings,
        )
    ) {
        if (!(key in target)) {
            target[key] =
                clone(value);
        }
    }

    settings =
        target;

    return target;
}

function principalKey() {
    if (!serverUserId) {
        return 'unknown-user';
    }

    return String(
        serverUserId,
    );
}

function deviceIdentifier() {
    try {
        const existing =
            localStorage.getItem(
                DEVICE_STORAGE_KEY,
            );

        if (existing) {
            return existing;
        }

        const value =
            randomId('d_');

        localStorage.setItem(
            DEVICE_STORAGE_KEY,
            value,
        );

        return value;
    } catch {
        return randomId('d_');
    }
}

function clientIdentifier() {
    try {
        const existing =
            sessionStorage.getItem(
                CLIENT_STORAGE_KEY,
            );

        if (existing) {
            return existing;
        }

        const value =
            randomId('c_');

        sessionStorage.setItem(
            CLIENT_STORAGE_KEY,
            value,
        );

        return value;
    } catch {
        return randomId('c_');
    }
}

const deviceId =
    deviceIdentifier();

const clientId =
    clientIdentifier();

function getCurrentScope() {
    ctx =
        getContext();

    if (
        ctx.groupId !== undefined
        && ctx.groupId !== null
        && String(ctx.groupId)
    ) {
        const group =
            ctx.groups?.find(
                item =>
                    String(item.id)
                    === String(
                        ctx.groupId,
                    ),
            );

        const chatId =
            ctx.getCurrentChatId?.()
            || ctx.chatId
            || group?.chat_id;

        if (!chatId) {
            return null;
        }

        return {
            kind: 'group',
            groupId:
                String(
                    ctx.groupId,
                ),
            chatId:
                String(
                    chatId,
                ),

            /*
             * For the main group chat there may still be an integrity
             * value, but branchId is intentionally used only for a
             * branch/checkpoint chat where main_chat is present.
             */
            branchId:
                ctx.chatMetadata
                    ?.main_chat
                    && ctx.chatMetadata
                        ?.integrity
                    ? String(
                        ctx.chatMetadata
                            .integrity,
                    )
                    : '',

            parentChatId:
                ctx.chatMetadata
                    ?.main_chat
                    ? String(
                        ctx.chatMetadata
                            .main_chat,
                    )
                    : '',
        };
    }

    if (
        ctx.characterId === undefined
        || ctx.characterId === null
        || String(ctx.characterId)
            === ''
    ) {
        return null;
    }

    const character =
        ctx.characters?.[
            ctx.characterId
        ];

    const avatar =
        character?.avatar;

    const chatId =
        ctx.getCurrentChatId?.()
        || ctx.chatId
        || character?.chat;

    if (
        !avatar
        || !chatId
    ) {
        return null;
    }

    return {
        kind: 'character',
        character:
            String(avatar),
        chatId:
            String(chatId),

        branchId:
            ctx.chatMetadata
                ?.main_chat
                && ctx.chatMetadata
                    ?.integrity
                ? String(
                    ctx.chatMetadata
                        .integrity,
                )
                : '',

        parentChatId:
            ctx.chatMetadata
                ?.main_chat
                ? String(
                    ctx.chatMetadata
                        .main_chat,
                )
                : '',
    };
}

function scopeIsCurrent(
    expectedEpoch,
    expectedScope,
) {
    return (
        expectedEpoch === scopeEpoch
        && currentScope
        && (
            !expectedScope
            || sameScope(
                expectedScope,
                currentScope,
            )
        )
    );
}

async function api(
    route,
    options = {},
) {
    ctx =
        getContext();

    const headers = {
        Accept:
            'application/json',
        ...(ctx.getRequestHeaders?.()
            || {}),
        ...(options.headers || {}),
    };

    if (
        options.body !== undefined
    ) {
        headers['Content-Type'] =
            'application/json';
    }

    const response =
        await fetch(
            `${PLUGIN_BASE}${route}`,
            {
                credentials:
                    'same-origin',
                cache:
                    'no-store',
                ...options,
                headers,
            },
        );

    const text =
        await response.text();

    let data = null;

    if (text) {
        try {
            data =
                JSON.parse(text);
        } catch {
            data = {
                ok: false,
                error: {
                    code:
                        'invalid_json',
                    message:
                        text.slice(
                            0,
                            500,
                        ),
                },
            };
        }
    }

    if (!response.ok) {
        const error =
            new Error(
                data
                    ?.error
                    ?.message
                || `HTTP ${response.status}`,
            );

        error.status =
            response.status;

        error.code =
            data
                ?.error
                ?.code
            || `http_${response.status}`;

        error.data =
            data;

        throw error;
    }

    return data;
}

function eventBody(
    type,
    extra = {},
    scope = currentScope,
) {
    return {
        protocol:
            PROTOCOL,

        schema:
            SCHEMA,

        type,

        clientId,
        deviceId,

        scope:
            clone(scope),

        ...extra,
    };
}

function setStatus(
    state,
    text,
) {
    if (!uiRoot) {
        return;
    }

    const dot =
        uiRoot.querySelector(
            '.mcs-status',
        );

    const label =
        uiRoot.querySelector(
            '.mcs-state-text',
        );

    dot?.classList.remove(
        'mcs-connected',
        'mcs-disconnected',
        'mcs-disabled',
        'mcs-owner',
        'mcs-streaming',
        'mcs-warning',
    );

    let css;

    switch (state) {
        case 'owner':
            css =
                'mcs-owner';
            break;

        case 'streaming':
            css =
                'mcs-streaming';
            break;

        case 'warning':
            css =
                'mcs-warning';
            break;

        case 'disabled':
            css =
                'mcs-disabled';
            break;

        case 'connected':
            css =
                'mcs-connected';
            break;

        default:
            css =
                'mcs-disconnected';
            break;
    }

    dot?.classList.add(
        css,
    );

    if (label) {
        label.textContent =
            text || state;
    }
}

function updateInfo() {
    if (!uiRoot) {
        return;
    }

    const info =
        uiRoot.querySelector(
            '[data-mcs-info]',
        );

    if (!info) {
        return;
    }

    const scope =
        currentScope
            ? (
                `${currentScope.kind}:`
                + `${currentScope.chatId}`
            )
            : 'none';

    const generation =
        currentState
            ?.generation
            ? (
                `generation `
                + currentState
                    .generation
                    .phase
            )
            : 'idle';

    const revision =
        Number(
            currentState
                ?.revision
            || 0,
        );

    info.textContent =
        `Scope: ${scope} · `
        + `revision ${revision} · `
        + `${generation}`
        + (
            lastError
                ? ` · ${lastError}`
                : ''
        );
}

function updateUi() {
    if (
        !settings?.enabled
    ) {
        setStatus(
            'disabled',
            'disabled',
        );

        updateInfo();

        return;
    }

    if (!serverAvailable) {
        setStatus(
            'warning',
            'server plugin required',
        );

        updateInfo();

        return;
    }

    if (!serverCompatible) {
        setStatus(
            'warning',
            'plugin incompatible',
        );

        updateInfo();

        return;
    }

    if (
        localGeneration
        && currentState
            ?.generation
            ?.id
            === localGeneration.id
    ) {
        setStatus(
            currentState
                .generation
                .phase
                === 'streaming'
                ? 'streaming'
                : 'owner',
            currentState
                .generation
                .phase,
        );

        updateInfo();

        return;
    }

    setStatus(
        'connected',
        'synchronized',
    );

    updateInfo();
}

function renderUi() {
    if (
        uiRoot
        && uiRoot.isConnected
    ) {
        return;
    }

    const host =
        document.querySelector(
            '#extensions_settings2',
        )
        || document.querySelector(
            '#extensions_settings',
        );

    if (!host) {
        return;
    }

    const root =
        document.createElement(
            'div',
        );

    root.className =
        'mcs-settings';

    root.innerHTML = `
        <h3>Multi-Client Sync</h3>

        <div class="mcs-status-row">
            <span class="mcs-status"
                  title="Multi-client sync status"></span>
            <span class="mcs-state-text">starting</span>
        </div>

        <div class="mcs-info"
             data-mcs-info></div>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="enabled">
            Enable synchronization
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="autoConnect">
            Connect automatically
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="syncMessages">
            Sync messages
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="syncMetadata">
            Sync chat metadata
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="syncSwipes">
            Sync swipes/reasoning/tools
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="syncGroupSettings">
            Sync group settings
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="syncBranches">
            Sync branches/checkpoints
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="coordinateGeneration">
            Coordinate generation
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="remoteStop">
            Allow remote generation stop
        </label>

        <label class="checkbox_label">
            <input type="checkbox"
                   data-mcs="notifications">
            Notifications
        </label>

        <div class="mcs-actions">
            <button type="button"
                    class="menu_button"
                    data-mcs-action="reconnect">
                Reconnect
            </button>

            <button type="button"
                    class="menu_button"
                    data-mcs-action="resync">
                Resync
            </button>

            <button type="button"
                    class="menu_button"
                    data-mcs-action="branch">
                Create branch
            </button>

            <button type="button"
                    class="menu_button"
                    data-mcs-action="checkpoint">
                Create checkpoint
            </button>
        </div>
    `;

    host.append(
        root,
    );

    uiRoot = root;

    for (
        const input
        of root.querySelectorAll(
            'input[data-mcs]',
        )
    ) {
        const key =
            input.getAttribute(
                'data-mcs',
            );

        input.checked =
            !!settings?.[key];

        input.addEventListener(
            'change',
            async () => {
                settings[key] =
                    input.checked;

                await ctx
                    .saveSettingsDebounced
                    ?.();

                if (
                    key === 'enabled'
                ) {
                    if (
                        input.checked
                    ) {
                        await onEnable();
                    } else {
                        await onDisable();
                    }

                    return;
                }

                if (
                    key === 'autoConnect'
                    && input.checked
                ) {
                    await reconnectCurrentScope();
                }

                updateUi();
            },
        );
    }

    root.querySelector(
        '[data-mcs-action="reconnect"]',
    )?.addEventListener(
        'click',
        () =>
            void reconnectCurrentScope(),
    );

    root.querySelector(
        '[data-mcs-action="resync"]',
    )?.addEventListener(
        'click',
        () =>
            void resyncCurrentScope(),
    );

    root.querySelector(
        '[data-mcs-action="branch"]',
    )?.addEventListener(
        'click',
        () =>
            void createNativeBranch(),
    );

    root.querySelector(
        '[data-mcs-action="checkpoint"]',
    )?.addEventListener(
        'click',
        () =>
            void createNativeCheckpoint(),
    );

    updateUi();
}

async function checkHealth() {
    try {
        const result =
            await api(
                '/health',
            );

        serverAvailable =
            !!result.ok;

        serverCompatible =
            serverAvailable
            && Number(
                result.protocol,
            )
                === PROTOCOL
            && Number(
                result.schema,
            )
                === SCHEMA;

        if (
            result.userId
        ) {
            serverUserId =
                String(
                    result.userId,
                );
        }

        if (
            !serverCompatible
        ) {
            lastError =
                'Server plugin version is incompatible.';
        } else {
            lastError = '';
        }

        return serverCompatible;
    } catch (error) {
        serverAvailable =
            false;

        serverCompatible =
            false;

        lastError =
            error.message;

        return false;
    }
}

/* -------------------------------------------------------------------------- */
/* IndexedDB                                                                   */
/* -------------------------------------------------------------------------- */

function openDb() {
    if (dbPromise) {
        return dbPromise;
    }

    dbPromise =
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

                request.onupgradeneeded =
                    () => {
                        const db =
                            request.result;

                        const transaction =
                            request
                                .transaction;

                        const ops =
                            db.objectStoreNames
                                .contains(
                                    'ops',
                                )
                                ? transaction
                                    .objectStore(
                                        'ops',
                                    )
                                : db.createObjectStore(
                                    'ops',
                                    {
                                        keyPath:
                                            'key',
                                    },
                                );

                        if (
                            !ops.indexNames
                                .contains(
                                    'principalScope',
                                )
                        ) {
                            ops.createIndex(
                                'principalScope',
                                'principalScope',
                                {
                                    unique:
                                        false,
                                },
                            );
                        }

                        if (
                            !ops.indexNames
                                .contains(
                                    'createdAt',
                                )
                        ) {
                            ops.createIndex(
                                'createdAt',
                                'createdAt',
                                {
                                    unique:
                                        false,
                                },
                            );
                        }

                        if (
                            ops.indexNames
                                .contains(
                                    'scope',
                                )
                        ) {
                            // Existing compatibility index.
                        } else {
                            ops.createIndex(
                                'scope',
                                'scope',
                                {
                                    unique:
                                        false,
                                },
                            );
                        }

                        const meta =
                            db.objectStoreNames
                                .contains(
                                    'meta',
                                )
                                ? transaction
                                    .objectStore(
                                        'meta',
                                    )
                                : db.createObjectStore(
                                    'meta',
                                    {
                                        keyPath:
                                            'key',
                                    },
                                );

                        if (
                            !meta.indexNames
                                .contains(
                                    'principal',
                                )
                        ) {
                            meta.createIndex(
                                'principal',
                                'principal',
                                {
                                    unique:
                                        false,
                                },
                            );
                        }
                    };

                request.onsuccess =
                    () =>
                        resolve(
                            request.result,
                        );

                request.onerror =
                    () =>
                        reject(
                            request.error,
                        );
            },
        );

    return dbPromise;
}

async function idb(
    storeName,
    mode,
    callback,
) {
    const db =
        await openDb();

    return new Promise(
        (
            resolve,
            reject,
        ) => {
            const tx =
                db.transaction(
                    storeName,
                    mode,
                );

            const store =
                tx.objectStore(
                    storeName,
                );

            let result;

            try {
                result =
                    callback(
                        store,
                        tx,
                    );
            } catch (error) {
                reject(error);
                return;
            }

            tx.oncomplete =
                () => resolve(
                    result,
                );

            tx.onerror =
                () => reject(
                    tx.error,
                );

            tx.onabort =
                () => reject(
                    tx.error
                    || new Error(
                        'IndexedDB transaction aborted.',
                    ),
                );
        },
    );
}

function metadataKey(
    scope,
) {
    return (
        `${principalKey()}|`
        + scopeKey(scope)
    );
}

function operationKey(
    operation,
) {
    return (
        `${principalKey()}|`
        + scopeKey(
            operation.scope,
        )
        + '|'
        + operation.opId
    );
}

function principalScopeKey(
    scope,
) {
    return (
        `${principalKey()}|`
        + scopeKey(scope)
    );
}

async function readMeta(
    scope,
) {
    const key =
        metadataKey(scope);

    return idb(
        'meta',
        'readonly',
        store =>
            new Promise(
                resolve => {
                    const request =
                        store.get(key);

                    request.onsuccess =
                        () =>
                            resolve(
                                request.result
                                || {
                                    key,
                                    principal:
                                        principalKey(),
                                    scope:
                                        scopeKey(
                                            scope,
                                        ),
                                    lastEventId:
                                        0,
                                    epoch:
                                        '',
                                    revision:
                                        0,
                                    localSequence:
                                        0,
                                    baseSnapshot:
                                        [],
                                    baseMetadata:
                                        {},
                                },
                            );

                    request.onerror =
                        () =>
                            resolve(
                                {
                                    key,
                                    principal:
                                        principalKey(),
                                    scope:
                                        scopeKey(
                                            scope,
                                        ),
                                    lastEventId:
                                        0,
                                    epoch:
                                        '',
                                    revision:
                                        0,
                                    localSequence:
                                        0,
                                    baseSnapshot:
                                        [],
                                    baseMetadata:
                                        {},
                                },
                            );
                },
            ),
    );
}

async function writeMeta(
    scope,
    patch,
) {
    const current =
        await readMeta(
            scope,
        );

    return idb(
        'meta',
        'readwrite',
        store =>
            store.put({
                ...current,
                ...clone(patch),
                key:
                    metadataKey(
                        scope,
                    ),
                principal:
                    principalKey(),
                scope:
                    scopeKey(scope),
                updatedAt:
                    now(),
            }),
    );
}

async function nextLocalSequence(
    scope,
) {
    const key =
        metadataKey(scope);

    return idb(
        'meta',
        'readwrite',
        store =>
            new Promise(
                (
                    resolve,
                    reject,
                ) => {
                    const request =
                        store.get(key);

                    request.onerror =
                        () =>
                            reject(
                                request.error,
                            );

                    request.onsuccess =
                        () => {
                            const existing =
                                request.result
                                || {
                                    key,
                                    principal:
                                        principalKey(),
                                    scope:
                                        scopeKey(
                                            scope,
                                        ),
                                    lastEventId:
                                        0,
                                    epoch:
                                        '',
                                    revision:
                                        0,
                                    localSequence:
                                        0,
                                    baseSnapshot:
                                        [],
                                    baseMetadata:
                                        {},
                                };

                            const next =
                                Number(
                                    existing
                                        .localSequence
                                    || 0,
                                ) + 1;

                            const write =
                                store.put({
                                    ...existing,
                                    key,
                                    principal:
                                        principalKey(),
                                    scope:
                                        scopeKey(
                                            scope,
                                        ),
                                    localSequence:
                                        next,
                                    updatedAt:
                                        now(),
                                });

                            write.onerror =
                                () =>
                                    reject(
                                        write.error,
                                    );

                            write.onsuccess =
                                () =>
                                    resolve(
                                        next,
                                    );
                        };
                },
            ),
    );
}

async function listQueuedOps(
    scope,
) {
    const principalScope =
        principalScopeKey(
            scope,
        );

    return idb(
        'ops',
        'readonly',
        store =>
            new Promise(
                resolve => {
                    const result = [];

                    const index =
                        store.index(
                            'principalScope',
                        );

                    const request =
                        index.openCursor(
                            IDBKeyRange.only(
                                principalScope,
                            ),
                        );

                    request.onsuccess =
                        () => {
                            const cursor =
                                request.result;

                            if (!cursor) {
                                result.sort(
                                    (
                                        a,
                                        b,
                                    ) =>
                                        (
                                            Number(
                                                a.localSequence,
                                            )
                                            - Number(
                                                b.localSequence,
                                            )
                                        )
                                        || (
                                            Number(
                                                a.createdAt,
                                            )
                                            - Number(
                                                b.createdAt,
                                            )
                                        ),
                                );

                                resolve(
                                    result,
                                );

                                return;
                            }

                            result.push(
                                cursor.value,
                            );

                            cursor.continue();
                        };

                    request.onerror =
                        () => resolve(
                            result,
                        );
                },
            ),
    );
}

async function putOperation(
    operation,
) {
    return idb(
        'ops',
        'readwrite',
        store =>
            store.put({
                ...clone(operation),

                key:
                    operationKey(
                        operation,
                    ),

                principalScope:
                    principalScopeKey(
                        operation.scope,
                    ),

                scope:
                    scopeKey(
                        operation.scope,
                    ),
            }),
    );
}

async function deleteOperation(
    operation,
) {
    return idb(
        'ops',
        'readwrite',
        store =>
            store.delete(
                operation.key
                || operationKey(
                    operation,
                ),
            ),
    );
}

async function clearOwnData() {
    const db =
        await openDb();

    const principal =
        principalKey();

    for (
        const storeName
        of [
            'ops',
            'meta',
        ]
    ) {
        await idb(
            storeName,
            'readwrite',
            store =>
                new Promise(
                    (
                        resolve,
                        reject,
                    ) => {
                        const index =
                            storeName
                                === 'ops'
                                ? store.index(
                                    'principalScope',
                                )
                                : store.index(
                                    'principal',
                                );

                        const range =
                            storeName
                                === 'ops'
                                ? IDBKeyRange.bound(
                                    `${principal}|`,
                                    `${principal}|\uffff`,
                                )
                                : IDBKeyRange.only(
                                    principal,
                                );

                        const request =
                            index.openCursor(
                                range,
                            );

                        request.onsuccess =
                            () => {
                                const cursor =
                                    request.result;

                                if (!cursor) {
                                    resolve();
                                    return;
                                }

                                cursor.delete();
                                cursor.continue();
                            };

                        request.onerror =
                            () =>
                                reject(
                                    request.error,
                                );
                    },
                ),
        );
    }

    db.close();

    dbPromise =
        null;
}

/* -------------------------------------------------------------------------- */
/* Merge                                                                       */
/* -------------------------------------------------------------------------- */

function messageEqual(
    a,
    b,
) {
    return JSON.stringify(a)
        === JSON.stringify(b);
}

function mergeSnapshots(
    base,
    local,
    remote,
) {
    const B =
        normalizeSnapshot(
            base || [],
        );

    const L =
        normalizeSnapshot(
            local || [],
        );

    const R =
        normalizeSnapshot(
            remote || [],
        );

    if (
        messageEqual(
            L,
            B,
        )
    ) {
        return R;
    }

    if (
        messageEqual(
            R,
            B,
        )
    ) {
        return L;
    }

    const mapById =
        list =>
            new Map(
                list.map(
                    message => [
                        stableMessageId(
                            message,
                        ),
                        message,
                    ],
                ),
            );

    const bm =
        mapById(B);

    const lm =
        mapById(L);

    const rm =
        mapById(R);

    const allIds =
        new Set([
            ...bm.keys(),
            ...lm.keys(),
            ...rm.keys(),
        ]);

    const chosen =
        new Map();

    /*
     * Conflict rule:
     *
     *   1. Identical => keep it.
     *   2. One side unchanged from base => take the changed side.
     *   3. If either side deleted a message that existed in base,
     *      deletion wins. This prevents resurrection.
     *   4. Otherwise remote wins same-message content conflict.
     */
    for (
        const id
        of allIds
    ) {
        const b =
            bm.get(id);

        const l =
            lm.get(id);

        const r =
            rm.get(id);

        if (
            l
            && r
            && messageEqual(
                l,
                r,
            )
        ) {
            chosen.set(
                id,
                clone(l),
            );

            continue;
        }

        const localDeleted =
            !l
            && !!b;

        const remoteDeleted =
            !r
            && !!b;

        if (
            localDeleted
            || remoteDeleted
        ) {
            continue;
        }

        if (
            l
            && b
            && messageEqual(
                l,
                b,
            )
        ) {
            if (r) {
                chosen.set(
                    id,
                    clone(r),
                );
            }

            continue;
        }

        if (
            r
            && b
            && messageEqual(
                r,
                b,
            )
        ) {
            if (l) {
                chosen.set(
                    id,
                    clone(l),
                );
            }

            continue;
        }

        if (r) {
            chosen.set(
                id,
                clone(r),
            );
        } else if (l) {
            chosen.set(
                id,
                clone(l),
            );
        }
    }

    const active =
        new Set(
            chosen.keys(),
        );

    const edges =
        new Map();

    const indegree =
        new Map();

    for (
        const id
        of active
    ) {
        edges.set(
            id,
            new Set(),
        );

        indegree.set(
            id,
            0,
        );
    }

    function addConstraints(
        list,
    ) {
        let previous = null;

        for (
            const message
            of list
        ) {
            const id =
                stableMessageId(
                    message,
                );

            if (
                !id
                || !active.has(id)
            ) {
                continue;
            }

            if (
                previous
                && previous !== id
                && !edges
                    .get(
                        previous,
                    )
                    .has(id)
            ) {
                edges
                    .get(
                        previous,
                    )
                    .add(id);

                indegree.set(
                    id,
                    indegree.get(id)
                        + 1,
                );
            }

            previous = id;
        }
    }

    addConstraints(B);
    addConstraints(L);
    addConstraints(R);

    /*
     * Deterministic final ordering:
     * topological order first, then lexicographic message ID.
     */
    const result = [];

    const remaining =
        new Set(active);

    while (
        remaining.size
    ) {
        const ready =
            [...remaining]
                .filter(
                    id =>
                        indegree.get(id)
                            === 0,
                )
                .sort();

        const nextId =
            ready[0]
            || [...remaining]
                .sort()[0];

        result.push(
            clone(
                chosen.get(
                    nextId,
                ),
            ),
        );

        remaining.delete(
            nextId,
        );

        for (
            const child
            of edges.get(
                nextId,
            ) || []
        ) {
            indegree.set(
                child,
                Math.max(
                    0,
                    indegree.get(
                        child,
                    ) - 1,
                ),
            );
        }
    }

    return normalizeSnapshot(
        result,
    );
}

/* -------------------------------------------------------------------------- */
/* Local application                                                           */
/* -------------------------------------------------------------------------- */

async function applySnapshotLocally(
    snapshot,
    metadata,
    expectedEpoch,
    reason,
    expectedScope,
) {
    if (
        !scopeIsCurrent(
            expectedEpoch,
            expectedScope,
        )
    ) {
        return false;
    }

    const next =
        normalizeSnapshot(
            snapshot,
        );

    const nextMetadata =
        isObject(metadata)
            ? clone(metadata)
            : {};

    applyingRemoteDepth++;

    try {
        if (
            !scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            return false;
        }

        ctx =
            getContext();

        ctx.chat.splice(
            0,
            ctx.chat.length,
            ...next,
        );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            return false;
        }

        ctx.updateChatMetadata?.(
            nextMetadata,
            true,
        );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            return false;
        }

        await ctx.printMessages?.();

        if (
            !scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            return false;
        }

        await ctx.saveChat?.();

        if (
            !scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            return false;
        }

        hostMessageIdsDirty =
            false;

        log(
            'remote snapshot applied',
            reason,
        );

        return true;
    } finally {
        applyingRemoteDepth =
            Math.max(
                0,
                applyingRemoteDepth - 1,
            );
    }
}

async function applyGroupSettings(
    groupSettings,
    expectedEpoch,
) {
    if (
        !settings.syncGroupSettings
        || !currentScope
        || currentScope.kind
            !== 'group'
        || !isObject(
            groupSettings,
        )
        || !scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        return false;
    }

    const group =
        ctx.groups?.find(
            item =>
                String(item.id)
                === String(
                    currentScope.groupId,
                ),
        );

    if (!group) {
        return false;
    }

    applyingRemoteDepth++;

    try {
        const allowedKeys = [
            'name',
            'members',
            'disabled_members',
            'chat_id',
            'chats',
            'generation_mode',
            'generation_mode_join_prefix',
            'generation_mode_join_suffix',
            'activation_strategy',
            'auto_mode_delay',
            'allow_self_responses',
            'avatar_url',
            'hideMutedSprites',
            'fav',
        ];

        for (
            const key
            of allowedKeys
        ) {
            if (
                Object.prototype
                    .hasOwnProperty
                    .call(
                        groupSettings,
                        key,
                    )
            ) {
                group[key] =
                    clone(
                        groupSettings[key],
                    );
            }
        }

        const groupModule =
            await import(
                '/scripts/group-chats.js'
            );

        if (
            typeof groupModule.editGroup
                === 'function'
        ) {
            await groupModule.editGroup(
                String(
                    currentScope.groupId,
                ),
                true,
                false,
            );
        }

        return scopeIsCurrent(
            expectedEpoch,
        );
    } catch (error) {
        warn(
            'group settings apply failed',
            error,
        );

        return false;
    } finally {
        applyingRemoteDepth =
            Math.max(
                0,
                applyingRemoteDepth - 1,
            );
    }
}

/* -------------------------------------------------------------------------- */
/* Queue                                                                       */
/* -------------------------------------------------------------------------- */

async function coalesceSnapshotOperation(
    operation,
) {
    const queued =
        await listQueuedOps(
            operation.scope,
        );

    const previous =
        queued.at(-1);

    if (
        !previous
        || previous.type
            !== 'snapshot'
        || operation.type
            !== 'snapshot'
        || previous.inFlight
    ) {
        return false;
    }

    previous.snapshot =
        clone(
            operation.snapshot,
        );

    previous.chatMetadata =
        operation.chatMetadata
            !== undefined
            ? clone(
                operation.chatMetadata,
            )
            : previous.chatMetadata;

    previous.reason =
        operation.reason;

    previous.localSequence =
        operation.localSequence;

    previous.updatedAt =
        now();

    await putOperation(
        previous,
    );

    return true;
}

async function enqueueMutation(
    reason,
    expectedEpoch = scopeEpoch,
) {
    if (
        applyingRemoteDepth > 0
        || !currentScope
        || !settings.enabled
        || !serverCompatible
        || !scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        return;
    }

    const scopeAtStart =
        clone(
            currentScope,
        );

    const baseState =
        currentState;

    const messagesEnabled =
        settings.syncMessages;

    const metadataEnabled =
        settings.syncMetadata;

    if (
        !messagesEnabled
        && !metadataEnabled
    ) {
        return;
    }

    const snapshot =
        messagesEnabled
            ? localSnapshot()
            : clone(
                baseState
                    ?.snapshot
                || [],
            );

    if (
        messagesEnabled
        && hostMessageIdsDirty
    ) {
        try {
            await ctx.saveChat?.();
            hostMessageIdsDirty =
                false;
        } catch (error) {
            warn(
                'Could not persist message IDs',
                error,
            );

            return;
        }
    }

    if (
        !scopeIsCurrent(
            expectedEpoch,
            scopeAtStart,
        )
    ) {
        return;
    }

    const metadata =
        metadataEnabled
            ? localMetadata()
            : undefined;

    const baseSnapshot =
        clone(
            baseState?.snapshot
            || [],
        );

    const baseMetadata =
        clone(
            baseState
                ?.chatMetadata
            || {},
        );

    if (
        JSON.stringify(
            snapshot,
        )
            === JSON.stringify(
                baseSnapshot,
            )
        && (
            !metadataEnabled
            || JSON.stringify(
                metadata,
            )
                === JSON.stringify(
                    baseMetadata,
                )
        )
    ) {
        return;
    }

    const localSequence =
        await nextLocalSequence(
            scopeAtStart,
        );

    const operation = {
        opId:
            randomId('op_'),

        type:
            metadataEnabled
            && !messagesEnabled
                ? 'metadata'
                : 'snapshot',

        reason,

        createdAt:
            now(),

        updatedAt:
            now(),

        localSequence,

        scope:
            scopeAtStart,

        baseRevision:
            Number(
                baseState
                    ?.revision
                || 0,
            ),

        baseSnapshot,

        baseMetadata,

        snapshot,

        ...(metadataEnabled
            ? {
                chatMetadata:
                    metadata,
            }
            : {}),
    };

    const queued =
        await listQueuedOps(
            scopeAtStart,
        );

    if (
        queued.length
        >= MAX_QUEUE
    ) {
        await deleteOperation(
            queued[0],
        );

        toast(
            'warning',
            'The synchronization queue was full; the oldest pending operation was dropped.',
        );
    }

    if (
        await coalesceSnapshotOperation(
            operation,
        )
    ) {
        void flushQueue(
            expectedEpoch,
        );

        return;
    }

    await putOperation(
        operation,
    );

    void flushQueue(
        expectedEpoch,
    );
}

async function rebaseOperation(
    operation,
    serverState,
) {
    const localDesired =
        mergeSnapshots(
            operation.baseSnapshot
                || [],
            operation.snapshot
                || [],
            serverState.snapshot
                || [],
        );

    const hasMetadata =
        Object.prototype
            .hasOwnProperty
            .call(
                operation,
                'chatMetadata',
            );

    let mergedMetadata =
        serverState
            .chatMetadata
        || {};

    if (hasMetadata) {
        const base =
            operation.baseMetadata
            || {};

        const local =
            operation.chatMetadata
            || {};

        const remote =
            serverState.chatMetadata
            || {};

        if (
            JSON.stringify(local)
            === JSON.stringify(base)
        ) {
            mergedMetadata =
                clone(remote);
        } else if (
            JSON.stringify(remote)
            === JSON.stringify(base)
        ) {
            mergedMetadata =
                clone(local);
        } else {
            mergedMetadata = {
                ...clone(remote),
                ...clone(local),
            };
        }
    }

    operation.baseRevision =
        Number(
            serverState.revision,
        );

    operation.baseSnapshot =
        clone(
            serverState.snapshot
            || [],
        );

    operation.baseMetadata =
        clone(
            serverState
                .chatMetadata
            || {},
        );

    operation.snapshot =
        localDesired;

    if (hasMetadata) {
        operation.chatMetadata =
            mergedMetadata;
    }

    operation.updatedAt =
        now();

    return operation;
}

async function applyRebasedOperationLocally(
    operation,
    expectedEpoch,
) {
    if (
        !scopeIsCurrent(
            expectedEpoch,
            operation.scope,
        )
    ) {
        return;
    }

    await applySnapshotLocally(
        operation.snapshot,
        operation.chatMetadata
            ?? currentState
                ?.chatMetadata
            ?? {},
        expectedEpoch,
        'queue-rebase',
        operation.scope,
    );
}

async function refreshServerState(
    expectedEpoch,
) {
    const scopeAtStart =
        clone(
            currentScope,
        );

    if (
        !scopeAtStart
        || !scopeIsCurrent(
            expectedEpoch,
            scopeAtStart,
        )
    ) {
        return null;
    }

    try {
        const data =
            await api(
                '/state',
                {
                    method:
                        'POST',
                    body:
                        JSON.stringify({
                            scope:
                                scopeAtStart,
                            clientId,
                            deviceId,
                        }),
                },
            );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                scopeAtStart,
            )
        ) {
            return null;
        }

        await setServerState(
            data.state,
            data.cursor,
        );

        return data.state;
    } catch (error) {
        lastError =
            error.message;

        updateInfo();

        return null;
    }
}

async function flushQueue(
    expectedEpoch = scopeEpoch,
) {
    if (
        !scopeIsCurrent(
            expectedEpoch,
        )
        || flushingQueueFlag
    ) {
        return;
    }

    flushingQueueFlag =
        true;

    try {
        while (
            scopeIsCurrent(
                expectedEpoch,
            )
        ) {
            const queue =
                await listQueuedOps(
                    currentScope,
                );

            if (!queue.length) {
                break;
            }

            const operation =
                queue[0];

            if (
                !sameScope(
                    operation.scope,
                    currentScope,
                )
            ) {
                await deleteOperation(
                    operation,
                );

                continue;
            }

            operation.inFlight =
                true;

            await putOperation(
                operation,
            );

            try {
                const payload = {
                    opId:
                        operation.opId,

                    baseRevision:
                        operation.baseRevision,
                };

                if (
                    operation.type
                    === 'snapshot'
                ) {
                    payload.snapshot =
                        clone(
                            operation.snapshot,
                        );

                    payload.chatMetadata =
                        clone(
                            operation.chatMetadata
                            ?? operation
                                .baseMetadata
                            ?? {},
                        );

                    const digest =
                        await snapshotDigest(
                            localSnapshot(),
                        );

                    if (digest) {
                        payload
                            .hostSnapshotDigest =
                            digest;
                    }
                } else if (
                    operation.type
                    === 'metadata'
                ) {
                    payload.chatMetadata =
                        clone(
                            operation.chatMetadata
                            || {},
                        );
                }

                const result =
                    await api(
                        '/event',
                        {
                            method:
                                'POST',
                            body:
                                JSON.stringify(
                                    eventBody(
                                        operation.type,
                                        payload,
                                    ),
                                ),
                        },
                    );

                if (
                    !scopeIsCurrent(
                        expectedEpoch,
                    )
                ) {
                    operation.inFlight =
                        false;

                    await putOperation(
                        operation,
                    );

                    return;
                }

                await setServerState(
                    result.state,
                    {
                        epoch:
                            result.epoch,
                        revision:
                            result.revision,
                        lastEventId:
                            result.eventId,
                    },
                );

                await deleteOperation(
                    operation,
                );

                broadcastScopeEvent(
                    'accepted',
                );
            } catch (error) {
                operation.inFlight =
                    false;

                await putOperation(
                    operation,
                );

                if (
                    error.code
                        === 'revision_conflict'
                    || error.code
                        === 'stale_host'
                ) {
                    const state =
                        await refreshServerState(
                            expectedEpoch,
                        );

                    if (!state) {
                        break;
                    }

                    await rebaseOperation(
                        operation,
                        state,
                    );

                    await applyRebasedOperationLocally(
                        operation,
                        expectedEpoch,
                    );

                    await putOperation(
                        operation,
                    );

                    continue;
                }

                if (
                    error.code
                        === 'not_member'
                    || error.code
                        === 'unauthenticated'
                ) {
                    await reconnectCurrentScope();
                    break;
                }

                if (
                    error.code
                        === 'branch_host_missing'
                ) {
                    break;
                }

                warn(
                    'queue flush failed',
                    error,
                );

                break;
            }
        }
    } finally {
        flushingQueueFlag =
            false;

        updateUi();
        updateInfo();
    }
}

let flushingQueueFlag =
    false;

/* -------------------------------------------------------------------------- */
/* Server state                                                                */
/* -------------------------------------------------------------------------- */

async function setServerState(
    state,
    cursor = {},
) {
    if (
        !state
        || !currentScope
    ) {
        return;
    }

    const token =
        currentState
            ?.subscriptionToken;

    currentState =
        clone(
            state,
        );

    if (token) {
        currentState
            .subscriptionToken =
            token;
    }

    await writeMeta(
        currentScope,
        {
            lastEventId:
                Number(
                    cursor.lastEventId
                    ?? cursor.eventId
                    ?? 0,
                ),

            epoch:
                state.epoch,

            revision:
                Number(
                    state.revision
                    || 0,
                ),

            baseSnapshot:
                clone(
                    state.snapshot
                    || [],
                ),

            baseMetadata:
                clone(
                    state.chatMetadata
                    || {},
                ),
        },
    );

    updateUi();
    updateInfo();
}

/* -------------------------------------------------------------------------- */
/* Remote event application                                                    */
/* -------------------------------------------------------------------------- */

async function localDiffersFromBase() {
    if (!currentState) {
        return false;
    }

    const local =
        settings.syncMessages
            ? localSnapshot()
            : null;

    const localMeta =
        settings.syncMetadata
            ? localMetadata()
            : null;

    const remoteBase =
        currentState.snapshot
        || [];

    const remoteMeta =
        currentState.chatMetadata
        || {};

    return (
        (
            settings.syncMessages
            && JSON.stringify(
                local,
            )
                !== JSON.stringify(
                    remoteBase,
                )
        )
        || (
            settings.syncMetadata
            && JSON.stringify(
                localMeta,
            )
                !== JSON.stringify(
                    remoteMeta,
                )
        )
    );
}

async function protectRemoteApply(
    expectedEpoch,
    incomingState,
) {
    if (
        !scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        return false;
    }

    if (
        applyingRemoteDepth > 0
    ) {
        return true;
    }

    const queue =
        await listQueuedOps(
            currentScope,
        );

    if (queue.length) {
        await resyncCurrentScope({
            preferLocal:
                true,
            incomingState,
        });

        return false;
    }

    if (
        await localDiffersFromBase()
    ) {
        await resyncCurrentScope({
            preferLocal:
                true,
            incomingState,
        });

        return false;
    }

    return true;
}

async function handleRemoteEvent(
    event,
    state,
    expectedEpoch,
) {
    if (
        !event
        || !scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        return;
    }

    if (
        event.source
            ?.clientId
            === clientId
        && event.source
            ?.deviceId
            === deviceId
    ) {
        return;
    }

    if (
        event.type
            === 'metadata'
    ) {
        if (
            !settings.syncMetadata
        ) {
            return;
        }

        if (
            !(await protectRemoteApply(
                expectedEpoch,
                state,
            ))
        ) {
            return;
        }

        const messages =
            settings.syncMessages
                ? clone(
                    currentState
                        ?.snapshot
                    || localSnapshot(),
                )
                : localSnapshot();

        await applySnapshotLocally(
            messages,
            state
                ?.chatMetadata
            || event.chatMetadata
            || {},
            expectedEpoch,
            'remote-metadata',
        );

        return;
    }

    if (
        event.type
            === 'snapshot'
        || event.type
            === 'reconcile_local'
        || event.type
            === 'bootstrap'
    ) {
        if (
            !settings.syncMessages
        ) {
            return;
        }

        if (
            !(await protectRemoteApply(
                expectedEpoch,
                state,
            ))
        ) {
            return;
        }

        await applySnapshotLocally(
            state
                ?.snapshot
            || [],
            settings.syncMetadata
                ? (
                    state
                        ?.chatMetadata
                    || {}
                )
                : localMetadata(),
            expectedEpoch,
            `remote-${event.type}`,
        );

        return;
    }

    if (
        event.type
            === 'generation_claim'
        || event.type
            === 'generation_started'
        || event.type
            === 'generation_heartbeat'
    ) {
        currentState = {
            ...(currentState || {}),
            generation:
                clone(
                    event.generation
                    || state
                        ?.generation
                    || null,
                ),
        };

        updateUi();
        updateInfo();

        return;
    }

    if (
        event.type
            === 'generation_stream'
    ) {
        if (
            !settings.syncMessages
        ) {
            return;
        }

        await applyRemoteGenerationStream(
            event,
            expectedEpoch,
        );

        return;
    }

    if (
        event.type
            === 'generation_stop_request'
    ) {
        if (
            settings.remoteStop
            && currentState
                ?.generation
                ?.id
                === event
                    .generationId
        ) {
            try {
                ctx.stopGeneration?.();
            } catch (error) {
                warn(
                    'remote stop failed',
                    error,
                );
            }
        }

        return;
    }

    if (
        event.type
            === 'generation_terminal'
    ) {
        if (
            settings.syncMessages
            && state?.snapshot
        ) {
            const ok =
                await protectRemoteApply(
                    expectedEpoch,
                    state,
                );

            if (ok) {
                await applySnapshotLocally(
                    state.snapshot,
                    settings.syncMetadata
                        ? (
                            state
                                .chatMetadata
                            || {}
                        )
                        : localMetadata(),
                    expectedEpoch,
                    'remote-generation-terminal',
                );
            }
        }

        currentState = {
            ...(currentState || {}),
            generation:
                null,
        };

        updateUi();
        updateInfo();

        return;
    }

    if (
        event.type
            === 'generation_recover'
    ) {
        currentState = {
            ...(currentState || {}),
            generation:
                null,
        };

        updateUi();
        updateInfo();

        return;
    }

    if (
        event.type
            === 'group_settings'
    ) {
        await applyGroupSettings(
            event.groupSettings,
            expectedEpoch,
        );

        return;
    }

    if (
        event.type
            === 'branch_announce'
    ) {
        /*
         * Announce only. We deliberately do not silently navigate the user
         * to another chat. The actual child chat is native ST state.
         */
        return;
    }
}

async function applyRemoteGenerationStream(
    event,
    expectedEpoch,
) {
    if (
        !scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        return;
    }

    const generation =
        currentState?.generation;

    if (
        !generation
        || generation.id
            !== event.generationId
    ) {
        return;
    }

    const sequence =
        Number(
            event.streamSeq,
        );

    if (
        sequence
        <= Number(
            generation.streamSeq
            || 0,
        )
    ) {
        return;
    }

    if (
        sequence
        !== Number(
            generation.streamSeq
            || 0,
        ) + 1
    ) {
        await resyncCurrentScope();
        return;
    }

    if (event.message) {
        const snapshot =
            localSnapshot();

        const messageId =
            event.messageId
            || stableMessageId(
                event.message,
            );

        const index =
            snapshot.findIndex(
                message =>
                    stableMessageId(
                        message,
                    )
                    === messageId,
            );

        if (index >= 0) {
            snapshot[index] =
                clone(
                    event.message,
                );
        } else {
            snapshot.push(
                clone(
                    event.message,
                ),
            );
        }

        await applySnapshotLocally(
            snapshot,
            localMetadata(),
            expectedEpoch,
            'remote-generation-stream',
        );
    }

    if (
        scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        currentState.generation
            .streamSeq =
            sequence;
    }
}

/* -------------------------------------------------------------------------- */
/* SSE                                                                         */
/* -------------------------------------------------------------------------- */

function closeSse() {
    if (sseReconnectTimer) {
        clearTimeout(
            sseReconnectTimer,
        );
    }

    sseReconnectTimer =
        null;

    if (sse) {
        try {
            sse.close();
        } catch {}
    }

    sse = null;
}

function scheduleReconnect(
    expectedEpoch,
) {
    if (
        sseReconnectTimer
        || !scopeIsCurrent(
            expectedEpoch,
        )
        || !serverCompatible
        || !settings.enabled
    ) {
        return;
    }

    const delay =
        Math.min(
            30_000,
            750 * (
                2 ** Math.min(
                    reconnectAttempt,
                    6,
                )
            ),
        );

    reconnectAttempt++;

    sseReconnectTimer =
        setTimeout(
            () => {
                sseReconnectTimer =
                    null;

                if (
                    !scopeIsCurrent(
                        expectedEpoch,
                    )
                ) {
                    return;
                }

                void reconnectCurrentScope();
            },
            delay,
        );
}

async function connectSse() {
    if (
        !currentScope
        || !serverCompatible
        || !settings.enabled
    ) {
        return;
    }

    closeSse();

    const expectedEpoch =
        scopeEpoch;

    const expectedScope =
        clone(
            currentScope,
        );

    const token =
        currentState
            ?.subscriptionToken;

    if (
        !token
        || !scopeIsCurrent(
            expectedEpoch,
            expectedScope,
        )
    ) {
        return;
    }

    const meta =
        await readMeta(
            expectedScope,
        );

    const url =
        new URL(
            `${PLUGIN_BASE}/events`,
            location.origin,
        );

    url.searchParams.set(
        'token',
        token,
    );

    if (
        meta.lastEventId
    ) {
        url.searchParams.set(
            'lastEventId',
            String(
                meta.lastEventId,
            ),
        );
    }

    const stream =
        new EventSource(
            url,
            {
                withCredentials:
                    true,
            },
        );

    sse =
        stream;

    sseEventChain =
        Promise.resolve();

    stream.onopen = () => {
        reconnectAttempt = 0;

        lastError = '';

        updateUi();
        updateInfo();
    };

    const parseAndQueue =
        (
            event,
            type,
        ) => {
            sseEventChain =
                sseEventChain
                    .then(
                        async () => {
                            let data;

                            try {
                                data =
                                    JSON.parse(
                                        event.data,
                                    );
                            } catch {
                                return;
                            }

                            if (
                                !scopeIsCurrent(
                                    expectedEpoch,
                                    expectedScope,
                                )
                                || sse
                                    !== stream
                            ) {
                                return;
                            }

                            await handleSseData(
                                type,
                                data,
                                event.lastEventId,
                                expectedEpoch,
                                expectedScope,
                            );
                        },
                    )
                    .catch(
                        error =>
                            warn(
                                'SSE handling failed',
                                error,
                            ),
                    );
        };

    for (
        const eventName
        of [
            'hello',
            'replay',
            'replay_complete',
            'resync_required',
            'sync',
            'shutdown',
        ]
    ) {
        stream.addEventListener(
            eventName,
            event =>
                parseAndQueue(
                    event,
                    eventName,
                ),
        );
    }

    stream.onerror = () => {
        try {
            stream.close();
        } catch {}

        if (sse === stream) {
            sse = null;
        }

        scheduleReconnect(
            expectedEpoch,
        );

        updateUi();
    };
}

async function handleSseData(
    type,
    data,
    lastEventId,
    expectedEpoch,
    expectedScope,
) {
    if (
        !scopeIsCurrent(
            expectedEpoch,
            expectedScope,
        )
    ) {
        return;
    }

    if (
        type === 'hello'
    ) {
        if (
            currentState?.epoch
            && data.epoch
            && currentState.epoch
                !== data.epoch
        ) {
            await writeMeta(
                expectedScope,
                {
                    lastEventId:
                        0,
                },
            );

            await resyncCurrentScope();
            return;
        }

        currentState = {
            ...(currentState || {}),
            epoch:
                data.epoch,
            revision:
                Math.max(
                    Number(
                        currentState
                            ?.revision
                        || 0,
                    ),
                    Number(
                        data.revision
                        || 0,
                    ),
                ),
            generation:
                clone(
                    data.generation
                    || null,
                ),
        };

        updateUi();

        return;
    }

    if (
        type === 'replay'
    ) {
        if (
            data.epoch
            && currentState?.epoch
            && data.epoch
                !== currentState.epoch
        ) {
            return;
        }

        if (data.event) {
            await handleRemoteEvent(
                data.event,
                currentState,
                expectedEpoch,
            );
        }

        await writeMeta(
            expectedScope,
            {
                lastEventId:
                    Number(
                        lastEventId
                        || data
                            .event
                            ?.id
                        || 0,
                    ),
            },
        );

        return;
    }

    if (
        type === 'replay_complete'
    ) {
        await writeMeta(
            expectedScope,
            {
                lastEventId:
                    Number(
                        data.eventId
                        || lastEventId
                        || 0,
                    ),
                epoch:
                    data.epoch,
                revision:
                    Number(
                        data.revision
                        || currentState
                            ?.revision
                        || 0,
                    ),
            },
        );

        await resyncCurrentScope();

        return;
    }

    if (
        type === 'resync_required'
    ) {
        await writeMeta(
            expectedScope,
            {
                lastEventId:
                    0,
            },
        );

        await resyncCurrentScope();

        return;
    }

    if (
        type === 'sync'
    ) {
        if (
            data.epoch
            && currentState?.epoch
            && data.epoch
                !== currentState.epoch
        ) {
            await resyncCurrentScope();

            return;
        }

        await handleRemoteEvent(
            data.event,
            data.state,
            expectedEpoch,
        );

        if (
            scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            if (
                data.state
            ) {
                await setServerState(
                    data.state,
                    {
                        epoch:
                            data.epoch
                            || data.state
                                .epoch,
                        revision:
                            data.state
                                .revision,
                        lastEventId:
                            lastEventId
                            || data
                                .event
                                ?.id
                            || 0,
                    },
                );
            }
        }

        broadcastScopeEvent(
            'remote',
        );

        return;
    }

    if (
        type === 'shutdown'
    ) {
        closeSse();
    }
}

/* -------------------------------------------------------------------------- */
/* Joining / reconnect                                                         */
/* -------------------------------------------------------------------------- */

async function joinScope(
    scope,
    expectedEpoch,
) {
    if (
        !scope
        || !serverCompatible
        || !settings.enabled
        || !scopeIsCurrent(
            expectedEpoch,
            scope,
        )
    ) {
        return false;
    }

    const previousMeta =
        await readMeta(
            scope,
        );

    try {
        const result =
            await api(
                '/join',
                {
                    method:
                        'POST',
                    body:
                        JSON.stringify({
                            scope:
                                scope,
                            clientId,
                            deviceId,
                        }),
                },
            );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                scope,
            )
        ) {
            return false;
        }

        serverUserId =
            String(
                result.userId
                || serverUserId
                || '',
            );

        currentState =
            clone(
                result.state,
            );

        currentState
            .subscriptionToken =
            result.subscriptionToken;

        const sameEpoch =
            previousMeta.epoch
                === result.state.epoch;

        await writeMeta(
            scope,
            {
                lastEventId:
                    sameEpoch
                        ? Number(
                            previousMeta
                                .lastEventId
                            || 0,
                        )
                        : 0,

                epoch:
                    result.state
                        .epoch,

                revision:
                    result.state
                        .revision,

                baseSnapshot:
                    clone(
                        result.state
                            .snapshot
                        || [],
                    ),

                baseMetadata:
                    clone(
                        result.state
                            .chatMetadata
                        || {},
                    ),
            },
        );

        ensureHostMessageIds();

        if (
            hostMessageIdsDirty
            && settings.syncMessages
        ) {
            try {
                await ctx.saveChat?.();
                hostMessageIdsDirty =
                    false;
            } catch (error) {
                warn(
                    'message ID save failed',
                    error,
                );
            }
        }

        /*
         * Never blindly overwrite local changes on join.
         * Merge local state with server state.
         */
        if (
            result.state
            && currentScope
        ) {
            const local =
                settings.syncMessages
                    ? localSnapshot()
                    : [];

            const remote =
                result.state.snapshot
                || [];

            const differs =
                settings.syncMessages
                && JSON.stringify(
                    local,
                )
                    !== JSON.stringify(
                        remote,
                    );

            if (differs) {
                const queue =
                    await listQueuedOps(
                        scope,
                    );

                const merged =
                    mergeSnapshots(
                        queue.length
                            ? (
                                queue
                                    .at(0)
                                    .baseSnapshot
                                || []
                            )
                            : (
                                currentState
                                    .snapshot
                                || []
                            ),
                        local,
                        remote,
                    );

                await applySnapshotLocally(
                    merged,
                    settings.syncMetadata
                        ? {
                            ...(
                                result.state
                                    .chatMetadata
                                || {}
                            ),
                            ...localMetadata(),
                        }
                        : localMetadata(),
                    expectedEpoch,
                    'join-merge',
                    scope,
                );

                if (!queue.length) {
                    await enqueueMutation(
                        'join-merge',
                        expectedEpoch,
                    );
                }
            }

            if (
                settings.syncMessages
                && result.state.snapshot
                    ?.length
                && !differs
            ) {
                await applySnapshotLocally(
                    result.state.snapshot,
                    settings.syncMetadata
                        ? (
                            result.state
                                .chatMetadata
                            || {}
                        )
                        : localMetadata(),
                    expectedEpoch,
                    'join',
                    scope,
                );
            }
        }

        reconnectAttempt = 0;

        await connectSse();

        startHeartbeat();

        void flushQueue(
            expectedEpoch,
        );

        updateUi();
        updateInfo();

        return true;
    } catch (error) {
        serverAvailable =
            error.code
            !== 'unauthenticated'
            && error.status
                !== 404;

        serverCompatible =
            error.status
                !== 404;

        lastError =
            error.message;

        updateUi();
        updateInfo();

        return false;
    }
}

async function leaveScope(
    scope,
) {
    if (
        !scope
        || !serverCompatible
    ) {
        return;
    }

    try {
        await api(
            '/leave',
            {
                method:
                    'POST',
                body:
                    JSON.stringify({
                        scope,
                        clientId,
                        deviceId,
                    }),
            },
        );
    } catch {}
}

async function switchScope(
    nextScope,
) {
    const previousScope =
        clone(
            currentScope,
        );

    const expectedEpoch =
        ++scopeEpoch;

    closeSse();
    stopHeartbeat();
    stopGenerationHeartbeat();

    if (previousScope) {
        void leaveScope(
            previousScope,
        );
    }

    currentScope =
        nextScope
            ? clone(
                nextScope,
            )
            : null;

    currentState =
        null;

    localGeneration =
        null;

    localGenerationLost =
        false;

    if (!currentScope) {
        updateUi();
        updateInfo();

        return;
    }

    if (
        !settings.enabled
        || !settings.autoConnect
        || !serverCompatible
    ) {
        updateUi();
        updateInfo();

        return;
    }

    await joinScope(
        currentScope,
        expectedEpoch,
    );
}

async function reconnectCurrentScope() {
    await checkHealth();

    const target =
        getCurrentScope();

    if (!target) {
        closeSse();
        stopHeartbeat();

        currentScope =
            null;

        currentState =
            null;

        updateUi();
        updateInfo();

        return false;
    }

    if (
        sameScope(
            target,
            currentScope,
        )
    ) {
        const expectedEpoch =
            ++scopeEpoch;

        closeSse();
        stopHeartbeat();

        await joinScope(
            clone(target),
            expectedEpoch,
        );

        return true;
    }

    await switchScope(
        target,
    );

    return true;
}

/* -------------------------------------------------------------------------- */
/* Heartbeat                                                                   */
/* -------------------------------------------------------------------------- */

function startHeartbeat() {
    stopHeartbeat();

    heartbeatTimer =
        setInterval(
            () =>
                void sendHeartbeat(),
            10_000,
        );
}

function stopHeartbeat() {
    if (heartbeatTimer) {
        clearInterval(
            heartbeatTimer,
        );
    }

    heartbeatTimer =
        null;
}

async function sendHeartbeat() {
    if (
        !currentScope
        || !serverCompatible
        || !settings.enabled
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
                    body:
                        JSON.stringify({
                            scope:
                                currentScope,
                            clientId,
                            deviceId,
                        }),
                },
            );

        if (
            currentState
        ) {
            currentState.generation =
                clone(
                    result.generation
                    || null,
                );

            currentState.revision =
                Math.max(
                    Number(
                        currentState
                            .revision
                        || 0,
                    ),
                    Number(
                        result.revision
                        || 0,
                    ),
                );
        }

        updateUi();
    } catch {
        scheduleReconnect(
            scopeEpoch,
        );
    }
}

/* -------------------------------------------------------------------------- */
/* Generation                                                                  */
/* -------------------------------------------------------------------------- */

function startGenerationHeartbeat() {
    stopGenerationHeartbeat();

    generationHeartbeatTimer =
        setInterval(
            () =>
                void renewGeneration(),
            5_000,
        );
}

function stopGenerationHeartbeat() {
    if (
        generationHeartbeatTimer
    ) {
        clearInterval(
            generationHeartbeatTimer,
        );
    }

    generationHeartbeatTimer =
        null;
}

async function renewGeneration() {
    if (
        !localGeneration
        || localGenerationLost
        || !currentScope
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
                    body:
                        JSON.stringify({
                            scope:
                                currentScope,
                            clientId,
                            deviceId,
                            generationId:
                                localGeneration
                                    .id,
                        }),
                },
            );

        currentState = {
            ...(currentState || {}),
            generation:
                clone(
                    result.generation,
                ),
        };
    } catch (error) {
        if (
            [
                'generation_mismatch',
                'no_generation',
                'not_generation_owner',
            ].includes(
                error.code,
            )
        ) {
            localGenerationLost =
                true;
        }
    }
}

async function claimGeneration(
    generationType = 'normal',
) {
    if (
        !settings.coordinateGeneration
        || !currentScope
        || !serverCompatible
    ) {
        return true;
    }

    if (
        currentState?.generation
    ) {
        toast(
            'warning',
            'Another synchronized client owns generation in this chat.',
        );

        return false;
    }

    const generationId =
        randomId('g_');

    try {
        const result =
            await api(
                '/event',
                {
                    method:
                        'POST',
                    body:
                        JSON.stringify(
                            eventBody(
                                'generation_claim',
                                {
                                    opId:
                                        randomId(
                                            'op_',
                                        ),
                                    generationId,
                                    generationType,
                                },
                            ),
                        ),
                },
            );

        localGeneration = {
            id:
                generationId,
            type:
                generationType,
        };

        localGenerationLost =
            false;

        currentState = {
            ...(currentState || {}),
            generation:
                clone(
                    result.generation,
                ),
        };

        startGenerationHeartbeat();

        updateUi();

        return true;
    } catch (error) {
        if (
            error.code
                === 'generation_busy'
        ) {
            toast(
                'warning',
                'Another synchronized client is generating in this chat.',
            );
        } else {
            warn(
                'generation claim failed',
                error,
            );
        }

        return false;
    }
}

async function acknowledgeGenerationStarted(
    type,
    messageId,
) {
    if (
        !localGeneration
        || localGenerationLost
        || !currentScope
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
                    body:
                        JSON.stringify(
                            eventBody(
                                'generation_started',
                                {
                                    opId:
                                        randomId(
                                            'op_',
                                        ),
                                    generationId:
                                        localGeneration
                                            .id,
                                    generationType:
                                        type,
                                    messageId:
                                        messageId
                                            || null,
                                },
                            ),
                        ),
                },
            );

        currentState = {
            ...(currentState || {}),
            generation:
                clone(
                    result.generation,
                ),
        };

        return true;
    } catch (error) {
        localGenerationLost =
            true;

        warn(
            'generation start acknowledgement failed',
            error,
        );

        try {
            ctx.stopGeneration?.();
        } catch {}

        return false;
    }
}

async function finishGeneration(
    status = 'completed',
) {
    if (
        finishingGeneration
    ) {
        return;
    }

    finishingGeneration =
        true;

    try {
        stopGenerationHeartbeat();

        if (
            !localGeneration
            || localGenerationLost
            || !currentScope
            || !serverCompatible
        ) {
            return;
        }

        const generationId =
            localGeneration.id;

        await streamFlushPromise;

        const expectedEpoch =
            scopeEpoch;

        const snapshot =
            localSnapshot();

        const metadata =
            localMetadata();

        if (
            hostMessageIdsDirty
        ) {
            await ctx.saveChat?.();
            hostMessageIdsDirty =
                false;
        }

        const opId =
            randomId('op_');

        let accepted =
            false;

        for (
            let attempt = 0;
            attempt < 3;
            attempt++
        ) {
            try {
                const digest =
                    await snapshotDigest(
                        snapshot,
                    );

                const result =
                    await api(
                        '/event',
                        {
                            method:
                                'POST',
                            body:
                                JSON.stringify(
                                    eventBody(
                                        'generation_terminal',
                                        {
                                            opId,
                                            generationId,
                                            status,
                                            snapshot,
                                            chatMetadata:
                                                metadata,
                                            ...(digest
                                                ? {
                                                    hostSnapshotDigest:
                                                        digest,
                                                }
                                                : {}),
                                        },
                                    ),
                                ),
                        },
                    );

                accepted = true;

                if (
                    scopeIsCurrent(
                        expectedEpoch,
                    )
                ) {
                    await setServerState(
                        result.state,
                        {
                            epoch:
                                result.epoch,
                            revision:
                                result.revision,
                            lastEventId:
                                result.eventId,
                        },
                    );
                }

                return;
            } catch (error) {
                if (
                    [
                        'generation_mismatch',
                        'no_generation',
                        'not_generation_owner',
                    ].includes(
                        error.code,
                    )
                ) {
                    localGenerationLost =
                        true;

                    return;
                }

                if (
                    attempt < 2
                    && (
                        !error.status
                        || error.status
                            >= 500
                    )
                ) {
                    await sleep(
                        150 * (
                            attempt + 1
                        ),
                    );

                    continue;
                }

                warn(
                    'generation terminal failed',
                    error,
                );

                return;
            }
        }
    } finally {
        if (
            acceptedGenerationTerminalPlaceholder
            || localGenerationLost
        ) {
            localGeneration =
                null;

            localGenerationLost =
                false;
        }

        /*
         * `acceptedGenerationTerminalPlaceholder` is assigned by the
         * outer completion helper below so the final cleanup remains
         * intentionally conservative.
         */
        acceptedGenerationTerminalPlaceholder =
            false;

        finishingGeneration =
            false;

        updateUi();
        updateInfo();
    }
}

let acceptedGenerationTerminalPlaceholder =
    false;

async function sendGenerationStream(
    message,
) {
    if (
        !localGeneration
        || localGenerationLost
        || !currentScope
        || !settings.coordinateGeneration
    ) {
        return;
    }

    const generationId =
        localGeneration.id;

    const nextSequence =
        Number(
            currentState
                ?.generation
                ?.streamSeq
            || 0,
        ) + 1;

    const digest =
        await snapshotDigest(
            localSnapshot(),
        );

    try {
        const result =
            await api(
                '/event',
                {
                    method:
                        'POST',
                    body:
                        JSON.stringify(
                            eventBody(
                                'generation_stream',
                                {
                                    opId:
                                        randomId(
                                            'op_',
                                        ),
                                    generationId,
                                    streamSeq:
                                        nextSequence,
                                    messageId:
                                        stableMessageId(
                                            message,
                                        ),
                                    message:
                                        clone(
                                            message,
                                        ),
                                    ...(digest
                                        ? {
                                            hostSnapshotDigest:
                                                digest,
                                        }
                                        : {}),
                                },
                            ),
                        ),
                },
            );

        if (
            localGeneration
                ?.id
                === generationId
        ) {
            currentState = {
                ...(currentState || {}),
                generation:
                    clone(
                        result.generation,
                    ),
            };
        }
    } catch (error) {
        if (
            [
                'stream_sequence_gap',
                'generation_mismatch',
                'not_generation_owner',
            ].includes(
                error.code,
            )
        ) {
            localGenerationLost =
                true;
        } else {
            warn(
                'generation stream failed',
                error,
            );
        }
    }
}

function streamCandidate() {
    if (
        !localGeneration
        || localGenerationLost
    ) {
        return null;
    }

    const generatingId =
        currentState
            ?.generation
            ?.messageId;

    if (generatingId) {
        const found =
            ctx.chat.find(
                message =>
                    stableMessageId(
                        message,
                    )
                    === generatingId,
            );

        if (found) {
            return clone(
                found,
            );
        }
    }

    const last =
        ctx.chat?.at?.(-1);

    return last
        ? clone(last)
        : null;
}

function scheduleStreamCapture() {
    if (
        !localGeneration
        || localGenerationLost
        || applyingRemoteDepth
    ) {
        return;
    }

    pendingStreamMessage =
        streamCandidate();

    if (streamTimer) {
        return;
    }

    streamTimer =
        setTimeout(
            () => {
                streamTimer =
                    null;

                const message =
                    pendingStreamMessage;

                pendingStreamMessage =
                    null;

                if (!message) {
                    return;
                }

                streamFlushPromise =
                    streamFlushPromise
                        .then(
                            () =>
                                sendGenerationStream(
                                    message,
                                ),
                        );
            },
            80,
        );
}

/* -------------------------------------------------------------------------- */
/* Branches / checkpoints                                                      */
/* -------------------------------------------------------------------------- */

async function fetchNativeChatHeader(
    scope,
    childChatId,
) {
    try {
        if (
            scope.kind
                === 'character'
        ) {
            const response =
                await fetch(
                    '/api/chats/get',
                    {
                        method:
                            'POST',
                        credentials:
                            'same-origin',
                        headers:
                            ctx.getRequestHeaders?.()
                            || {},
                        body:
                            JSON.stringify({
                                avatar_url:
                                    scope.character,
                                file_name:
                                    childChatId,
                            }),
                    },
                );

            if (!response.ok) {
                return null;
            }

            const data =
                await response.json();

            return {
                metadata:
                    isObject(
                        data?.[0]
                            ?.chat_metadata,
                    )
                        ? clone(
                            data[0]
                                .chat_metadata,
                        )
                        : {},
            };
        }

        const response =
            await fetch(
                '/api/chats/group/get',
                {
                    method:
                        'POST',
                    credentials:
                        'same-origin',
                    headers:
                        ctx.getRequestHeaders?.()
                        || {},
                    body:
                        JSON.stringify({
                            id:
                                childChatId,
                        }),
                },
            );

        if (!response.ok) {
            return null;
        }

        const data =
            await response.json();

        return {
            metadata:
                isObject(
                    data?.[0]
                        ?.chat_metadata,
                )
                    ? clone(
                        data[0]
                            .chat_metadata,
                    )
                    : {},
        };
    } catch {
        return null;
    }
}

async function announceNativeChild(
    parentScope,
    childChatId,
    branchKind,
    expectedEpoch,
) {
    const header =
        await fetchNativeChatHeader(
            parentScope,
            childChatId,
        );

    if (
        !header
        || !header.metadata
            ?.integrity
        || !header.metadata
            ?.main_chat
    ) {
        toast(
            'warning',
            'SillyTavern created the child chat, but its native branch metadata could not be read yet.',
        );

        return false;
    }

    const childScope = {
        ...clone(
            parentScope,
        ),

        chatId:
            String(
                childChatId,
            ),

        branchId:
            String(
                header.metadata
                    .integrity,
            ),

        parentChatId:
            String(
                header.metadata
                    .main_chat,
            ),
    };

    try {
        await api(
            '/event',
            {
                method:
                    'POST',
                body:
                    JSON.stringify(
                        eventBody(
                            'branch_announce',
                            {
                                opId:
                                    randomId(
                                        'op_',
                                    ),

                                baseRevision:
                                    Number(
                                        currentState
                                            ?.revision
                                        || 0,
                                    ),

                                branchKind,

                                childScope,
                            },
                            parentScope,
                        ),
                    ),
            },
        );

        return true;
    } catch (error) {
        warn(
            'branch announcement failed',
            error,
        );

        if (
            error.code
                === 'revision_conflict'
        ) {
            await resyncCurrentScope();

            return false;
        }

        return false;
    }
}

async function createNativeBranch() {
    if (
        !settings.syncBranches
        || !currentScope
        || !serverCompatible
    ) {
        return;
    }

    const parentScope =
        clone(
            currentScope,
        );

    const expectedEpoch =
        scopeEpoch;

    const index =
        Math.max(
            0,
            ctx.chat.length - 1,
        );

    try {
        const bookmarks =
            await import(
                '/scripts/bookmarks.js'
            );

        /*
         * This is the current native ST API.
         * It creates the branch without automatically navigating.
         */
        const childChatId =
            await bookmarks.createBranch(
                index,
                {},
            );

        if (!childChatId) {
            return;
        }

        if (
            !scopeIsCurrent(
                expectedEpoch,
                parentScope,
            )
        ) {
            return;
        }

        /*
         * createBranch modifies the parent message's branch list.
         * Persist that native parent change first.
         */
        try {
            await ctx.saveChat?.();
        } catch {}

        await enqueueMutation(
            'native-branch-created',
            expectedEpoch,
        );

        await flushQueue(
            expectedEpoch,
        );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                parentScope,
            )
        ) {
            return;
        }

        await announceNativeChild(
            parentScope,
            String(childChatId),
            'branch',
            expectedEpoch,
        );

        toast(
            'success',
            `Branch created: ${childChatId}`,
        );
    } catch (error) {
        warn(
            'native branch creation failed',
            error,
        );

        toast(
            'error',
            `Branch creation failed: ${error.message}`,
        );
    }
}

async function createNativeCheckpoint() {
    if (
        !settings.syncBranches
        || !currentScope
        || !serverCompatible
    ) {
        return;
    }

    const parentScope =
        clone(
            currentScope,
        );

    const expectedEpoch =
        scopeEpoch;

    const index =
        Math.max(
            0,
            ctx.chat.length - 1,
        );

    try {
        const bookmarks =
            await import(
                '/scripts/bookmarks.js'
            );

        /*
         * Current native ST checkpoint API.
         * It does not navigate away from the current chat.
         */
        const childChatId =
            await bookmarks.createNewBookmark(
                index,
            );

        if (!childChatId) {
            return;
        }

        if (
            !scopeIsCurrent(
                expectedEpoch,
                parentScope,
            )
        ) {
            return;
        }

        await enqueueMutation(
            'native-checkpoint-created',
            expectedEpoch,
        );

        await flushQueue(
            expectedEpoch,
        );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                parentScope,
            )
        ) {
            return;
        }

        await announceNativeChild(
            parentScope,
            String(childChatId),
            'checkpoint',
            expectedEpoch,
        );

        toast(
            'success',
            `Checkpoint created: ${childChatId}`,
        );
    } catch (error) {
        warn(
            'native checkpoint creation failed',
            error,
        );

        toast(
            'error',
            `Checkpoint creation failed: ${error.message}`,
        );
    }
}

/* -------------------------------------------------------------------------- */
/* Group settings                                                              */
/* -------------------------------------------------------------------------- */

function currentGroupSettings() {
    if (
        !currentScope
        || currentScope.kind
            !== 'group'
    ) {
        return null;
    }

    const group =
        ctx.groups?.find(
            item =>
                String(item.id)
                === String(
                    currentScope.groupId,
                ),
        );

    if (!group) {
        return null;
    }

    const allowedKeys = [
        'name',
        'members',
        'disabled_members',
        'chat_id',
        'chats',
        'generation_mode',
        'generation_mode_join_prefix',
        'generation_mode_join_suffix',
        'activation_strategy',
        'auto_mode_delay',
        'allow_self_responses',
        'avatar_url',
        'hideMutedSprites',
        'fav',
    ];

    const settingsSnapshot =
        {};

    for (
        const key
        of allowedKeys
    ) {
        if (
            group[key] !== undefined
        ) {
            settingsSnapshot[key] =
                clone(
                    group[key],
                );
        }
    }

    return settingsSnapshot;
}

async function publishGroupSettings(
    expectedEpoch = scopeEpoch,
) {
    if (
        !settings.syncGroupSettings
        || !currentScope
        || currentScope.kind
            !== 'group'
        || !serverCompatible
        || !scopeIsCurrent(
            expectedEpoch,
        )
    ) {
        return;
    }

    const snapshot =
        currentGroupSettings();

    if (!snapshot) {
        return;
    }

    try {
        const result =
            await api(
                '/event',
                {
                    method:
                        'POST',
                    body:
                        JSON.stringify(
                            eventBody(
                                'group_settings',
                                {
                                    opId:
                                        randomId(
                                            'op_',
                                        ),
                                    baseRevision:
                                        Number(
                                            currentState
                                                ?.revision
                                            || 0,
                                        ),
                                    groupSettings:
                                        snapshot,
                                },
                            ),
                        ),
                },
            );

        if (
            scopeIsCurrent(
                expectedEpoch,
            )
        ) {
            await setServerState(
                result.state,
                {
                    epoch:
                        result.epoch,
                    revision:
                        result.revision,
                    lastEventId:
                        result.eventId,
                },
            );
        }
    } catch (error) {
        if (
            error.code
                === 'revision_conflict'
        ) {
            await resyncCurrentScope();
            return;
        }

        warn(
            'group setting publish failed',
            error,
        );
    }
}

/* -------------------------------------------------------------------------- */
/* Capture                                                                     */
/* -------------------------------------------------------------------------- */

function scheduleLocalCapture(
    reason,
) {
    if (
        applyingRemoteDepth
        || !currentScope
        || !serverCompatible
        || !settings.enabled
        || captureScheduled
    ) {
        return;
    }

    captureScheduled =
        true;

    clearTimeout(
        captureTimer,
    );

    captureTimer =
        setTimeout(
            () => {
                captureScheduled =
                    false;

                void enqueueMutation(
                    reason,
                    scopeEpoch,
                );
            },
            SNAPSHOT_CAPTURE_DELAY,
        );
}

async function handleChatChanged() {
    if (
        applyingRemoteDepth
    ) {
        return;
    }

    const nextScope =
        getCurrentScope();

    if (
        sameScope(
            nextScope,
            currentScope,
        )
    ) {
        scheduleLocalCapture(
            'chat-changed',
        );

        return;
    }

    await switchScope(
        nextScope,
    );
}

/* -------------------------------------------------------------------------- */
/* BroadcastChannel                                                            */
/* -------------------------------------------------------------------------- */

function initBroadcastChannel() {
    if (
        typeof BroadcastChannel
            === 'undefined'
    ) {
        return;
    }

    if (broadcastChannel) {
        return;
    }

    try {
        broadcastChannel =
            new BroadcastChannel(
                EXTENSION_ID,
            );

        broadcastChannel.onmessage =
            event => {
                const data =
                    event.data;

                if (
                    !data
                    || data.type
                        !== 'scope-event'
                ) {
                    return;
                }

                if (
                    data.scopeKey
                        !== scopeKey(
                            currentScope,
                        )
                ) {
                    return;
                }

                /*
                 * BroadcastChannel is only an optimization.
                 * SSE remains the authoritative source.
                 */
                void resyncCurrentScope();
            };
    } catch {
        broadcastChannel =
            null;
    }
}

function broadcastScopeEvent(
    type,
) {
    try {
        broadcastChannel
            ?.postMessage({
                type:
                    'scope-event',
                scopeKey:
                    scopeKey(
                        currentScope,
                    ),
                eventType:
                    type,
            });
    } catch {}
}

/* -------------------------------------------------------------------------- */
/* Browser / ST events                                                         */
/* -------------------------------------------------------------------------- */

function bindBrowserEvent(
    name,
    fn,
    options,
) {
    window.addEventListener(
        name,
        fn,
        options,
    );

    browserBindings.push({
        name,
        fn,
        options,
    });
}

function unbindBrowserEvents() {
    for (
        const binding
        of browserBindings
    ) {
        window.removeEventListener(
            binding.name,
            binding.fn,
            binding.options,
        );
    }

    browserBindings =
        [];
}

function bindStEvent(
    name,
    handler,
) {
    if (
        !name
        || !ctx?.eventSource
    ) {
        return;
    }

    const wrapped =
        (...args) =>
            void handler(
                ...args,
            );

    ctx.eventSource.on(
        name,
        wrapped,
    );

    listenerBindings.push({
        name,
        wrapped,
    });
}

function unbindStEvents() {
    for (
        const binding
        of listenerBindings
    ) {
        try {
            ctx.eventSource
                ?.removeListener(
                    binding.name,
                    binding.wrapped,
                );
        } catch {}
    }

    listenerBindings =
        [];
}

function bindStEvents() {
    unbindStEvents();

    ctx =
        getContext();

    const events =
        ctx.eventTypes
        || ctx.event_types
        || {};

    const capture = [
        'MESSAGE_SENT',
        'MESSAGE_RECEIVED',
        'MESSAGE_EDITED',
        'MESSAGE_DELETED',
        'MESSAGE_UPDATED',
        'MESSAGE_SWIPED',
        'MESSAGE_SWIPE_DELETED',
        'MESSAGE_REASONING_EDITED',
        'MESSAGE_REASONING_DELETED',
        'MESSAGE_FILE_EMBEDDED',
        'FILE_ATTACHMENT_DELETED',
        'MEDIA_ATTACHMENT_DELETED',
        'TOOL_CALLS_PERFORMED',
    ];

    for (
        const key
        of capture
    ) {
        const event =
            events[key];

        if (!event) {
            continue;
        }

        bindStEvent(
            event,
            () => {
                if (
                    applyingRemoteDepth
                    === 0
                ) {
                    scheduleLocalCapture(
                        key,
                    );
                }
            },
        );
    }

    const chatChangedEvents = [
        events.CHAT_CHANGED,
        events.CHAT_LOADED,
        events.CHAT_CREATED,
        events.GROUP_CHAT_CREATED,
    ].filter(Boolean);

    for (
        const event
        of new Set(
            chatChangedEvents,
        )
    ) {
        bindStEvent(
            event,
            () =>
                void handleChatChanged(),
        );
    }

    if (
        events.GROUP_UPDATED
    ) {
        bindStEvent(
            events.GROUP_UPDATED,
            () => {
                if (
                    applyingRemoteDepth
                    === 0
                    && settings
                        .syncGroupSettings
                ) {
                    void publishGroupSettings(
                        scopeEpoch,
                    );
                }
            },
        );
    }

    if (
        events.CHAT_METADATA_UPDATED
    ) {
        bindStEvent(
            events.CHAT_METADATA_UPDATED,
            () => {
                if (
                    applyingRemoteDepth
                    === 0
                ) {
                    scheduleLocalCapture(
                        'metadata-updated',
                    );
                }
            },
        );
    }

    if (
        events.CHAT_UPDATED
    ) {
        bindStEvent(
            events.CHAT_UPDATED,
            () => {
                if (
                    applyingRemoteDepth
                    === 0
                ) {
                    scheduleLocalCapture(
                        'chat-updated',
                    );
                }
            },
        );
    }

    if (
        events.GENERATION_STARTED
    ) {
        bindStEvent(
            events.GENERATION_STARTED,
            () => {
                if (
                    !localGeneration
                    || localGenerationLost
                ) {
                    return;
                }

                const last =
                    ctx.chat?.at?.(-1);

                void acknowledgeGenerationStarted(
                    localGeneration.type
                    || 'normal',
                    stableMessageId(
                        last,
                    ),
                );
            },
        );
    }

    if (
        events.STREAM_TOKEN_RECEIVED
    ) {
        bindStEvent(
            events.STREAM_TOKEN_RECEIVED,
            () =>
                scheduleStreamCapture(),
        );
    }

    if (
        events.GENERATION_STOPPED
    ) {
        bindStEvent(
            events.GENERATION_STOPPED,
            () => {
                if (
                    localGeneration
                    && !localGenerationLost
                ) {
                    void finishGeneration(
                        'stopped',
                    );
                }
            },
        );
    }

    if (
        events.GENERATION_ENDED
    ) {
        bindStEvent(
            events.GENERATION_ENDED,
            () => {
                if (
                    localGeneration
                    && !localGenerationLost
                ) {
                    void finishGeneration(
                        'completed',
                    );
                }
            },
        );
    }
}

/* -------------------------------------------------------------------------- */
/* Generation interceptor                                                      */
/* -------------------------------------------------------------------------- */

async function generationInterceptor(
    chat,
    contextSize,
    abort,
    type,
) {
    if (
        !settings?.enabled
        || !settings
            .coordinateGeneration
        || !currentScope
        || !serverCompatible
    ) {
        return;
    }

    /*
     * Quiet prompts are not user-visible conversation generation and are
     * intentionally outside synchronization ownership.
     */
    if (
        type === 'quiet'
    ) {
        return;
    }

    const actualScope =
        getCurrentScope();

    if (
        !sameScope(
            actualScope,
            currentScope,
        )
    ) {
        await switchScope(
            actualScope,
        );
    }

    const granted =
        await claimGeneration(
            type
            || 'normal',
        );

    if (!granted) {
        try {
            abort?.(
                true,
            );
        } catch {
            /* Host generation API changed. */
        }
    }
}

globalThis
    .multiClientSyncGenerateInterceptor =
    generationInterceptor;

/* -------------------------------------------------------------------------- */
/* Resync                                                                      */
/* -------------------------------------------------------------------------- */

async function resyncCurrentScope(
    options = {},
) {
    const expectedEpoch =
        scopeEpoch;

    const expectedScope =
        clone(
            currentScope,
        );

    if (
        !expectedScope
        || !serverCompatible
        || !scopeIsCurrent(
            expectedEpoch,
            expectedScope,
        )
    ) {
        return false;
    }

    try {
        const data =
            await api(
                '/state',
                {
                    method:
                        'POST',
                    body:
                        JSON.stringify({
                            scope:
                                expectedScope,
                            clientId,
                            deviceId,
                        }),
                },
            );

        if (
            !scopeIsCurrent(
                expectedEpoch,
                expectedScope,
            )
        ) {
            return false;
        }

        const serverState =
            data.state;

        const local =
            settings.syncMessages
                ? localSnapshot()
                : [];

        const queue =
            await listQueuedOps(
                expectedScope,
            );

        const hasLocalDivergence =
            (
                settings.syncMessages
                && JSON.stringify(
                    local,
                )
                    !== JSON.stringify(
                        serverState
                            .snapshot
                        || [],
                    )
            )
            || (
                settings.syncMetadata
                && JSON.stringify(
                    localMetadata(),
                )
                    !== JSON.stringify(
                        serverState
                            .chatMetadata
                        || {},
                    )
            );

        if (
            queue.length
            || options.preferLocal
            || hasLocalDivergence
        ) {
            const base =
                queue.length
                    ? (
                        queue[0]
                            .baseSnapshot
                        || []
                    )
                    : (
                        currentState
                            ?.snapshot
                        || serverState
                            .snapshot
                        || []
                    );

            const merged =
                settings.syncMessages
                    ? mergeSnapshots(
                        base,
                        local,
                        serverState
                            .snapshot
                        || [],
                    )
                    : local;

            if (
                settings.syncMessages
            ) {
                await applySnapshotLocally(
                    merged,
                    settings.syncMetadata
                        ? {
                            ...(
                                serverState
                                    .chatMetadata
                                || {}
                            ),
                            ...localMetadata(),
                        }
                        : localMetadata(),
                    expectedEpoch,
                    'resync-merge',
                    expectedScope,
                );
            }

            if (
                !queue.length
                && (
                    (
                        settings
                            .syncMessages
                    )
                    || (
                        settings
                            .syncMetadata
                    )
                )
            ) {
                await enqueueMutation(
                    'resync-merge',
                    expectedEpoch,
                );
            }
        } else {
            await applySnapshotLocally(
                serverState
                    .snapshot
                || [],
                settings.syncMetadata
                    ? (
                        serverState
                            .chatMetadata
                        || {}
                    )
                    : localMetadata(),
                expectedEpoch,
                'resync',
                expectedScope,
            );
        }

        await setServerState(
            serverState,
            data.cursor,
        );

        await flushQueue(
            expectedEpoch,
        );

        return true;
    } catch (error) {
        lastError =
            error.message;

        updateInfo();

        return false;
    }
}

/* -------------------------------------------------------------------------- */
/* Lifecycle                                                                   */
/* -------------------------------------------------------------------------- */

async function initialize() {
    if (
        startPromise
    ) {
        return startPromise;
    }

    startPromise =
        (async () => {
            ctx =
                getContext();

            settings =
                settingsRef();

            renderUi();

            initBroadcastChannel();

            bindBrowserEvent(
                'online',
                () =>
                    void reconnectCurrentScope(),
            );

            bindBrowserEvent(
                'pageshow',
                () =>
                    void reconnectCurrentScope(),
            );

            bindBrowserEvent(
                'visibilitychange',
                () => {
                    if (
                        document
                            .visibilityState
                            === 'visible'
                    ) {
                        void reconnectCurrentScope();
                    }
                },
            );

            bindBrowserEvent(
                'beforeunload',
                () => {
                    void leaveScope(
                        currentScope,
                    );
                },
            );

            bindStEvents();

            await checkHealth();

            if (
                !settings.enabled
            ) {
                updateUi();
                updateInfo();

                return;
            }

            const target =
                getCurrentScope();

            if (
                target
                && settings.autoConnect
                && serverCompatible
            ) {
                await switchScope(
                    target,
                );
            }

            started =
                true;

            updateUi();
            updateInfo();
        })().catch(
            error => {
                warn(
                    'extension initialization failed',
                    error,
                );

                lastError =
                    error.message;

                updateUi();
                updateInfo();
            },
        );

    await startPromise;

    return startPromise;
}

async function stop() {
    ++scopeEpoch;

    clearTimeout(
        captureTimer,
    );

    clearTimeout(
        streamTimer,
    );

    stopHeartbeat();
    stopGenerationHeartbeat();

    closeSse();

    unbindStEvents();
    unbindBrowserEvents();

    try {
        await leaveScope(
            currentScope,
        );
    } catch {}

    currentScope =
        null;

    currentState =
        null;

    localGeneration =
        null;

    localGenerationLost =
        false;

    pendingStreamMessage =
        null;

    started =
        false;

    startPromise =
        null;

    flushingQueueFlag =
        false;

    updateUi();
    updateInfo();
}

/* -------------------------------------------------------------------------- */
/* Manifest hooks                                                              */
/* -------------------------------------------------------------------------- */

export async function onInstall() {
    ctx =
        getContext();

    settings =
        settingsRef();

    await ctx
        .saveSettingsDebounced
        ?.();
}

export async function init() {
    await initialize();
}

export async function onEnable() {
    settings =
        settingsRef();

    settings.enabled =
        true;

    if (!started) {
        await initialize();
    } else {
        await reconnectCurrentScope();
    }
}

export async function onDisable() {
    if (settings) {
        settings.enabled =
            false;
    }

    await stop();

    await ctx
        ?.saveSettingsDebounced
        ?.();
}

export async function onUpdate() {
    ctx =
        getContext();

    settings =
        settingsRef();

    await ctx
        .saveSettingsDebounced
        ?.();
}

export async function onDelete() {
    await stop();
}

export async function onClean() {
    await stop();

    /*
     * Only this extension's current authenticated namespace is removed.
     * Other users' extension data remain intact.
     */
    if (serverUserId) {
        await clearOwnData();
    }
}