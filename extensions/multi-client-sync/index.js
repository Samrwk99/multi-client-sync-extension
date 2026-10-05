/**
 * Multi Client Sync - SillyTavern UI extension.
 *
 * Uses:
 * - SillyTavern.getContext() public extension API
 * - BroadcastChannel as a same-browser optimization
 * - Server SSE as the authoritative live transport
 * - IndexedDB for durable pending local mutations
 * - Full snapshots + server revisions for deterministic conflict control
 * - 3-way merge for concurrent message/metadata edits
 * - Generation ownership/leases/fencing
 *
 * Important:
 * - The server is authoritative for revision ordering.
 * - BroadcastChannel is never authoritative.
 * - ST itself remains responsible for persistent chat-file saving.
 */

const MODULE = 'multi_client_sync';
const PLUGIN_BASE = '/api/plugins/multi-client-sync';
const PROTOCOL_VERSION = 2;

const DB_NAME = 'multi-client-sync-v2';
const DB_VERSION = 1;

const CHANNEL_NAME = 'multi-client-sync-v2';

const MAX_RECONNECT_MS = 30_000;
const HEARTBEAT_MS = 10_000;
const STREAM_FLUSH_MS = 120;
const FINALIZE_DELAY_MS = 250;
const SNAPSHOT_DEBOUNCE_MS = 80;

const DEFAULTS = Object.freeze({
    enabled: true,
    debug: false,
});

let ctx = null;
let initialized = false;
let destroyed = false;

let listeners = [];

let broadcastChannel = null;
let eventSource = null;

let reconnectTimer = null;
let heartbeatTimer = null;
let pendingStreamTimer = null;
let localMutationTimer = null;
let finalizeTimer = null;

let localSaveChain = Promise.resolve();

let currentScope = null;
let currentState = null;
let currentClientId = null;
let currentDeviceId = null;

let scopeEpoch = 0;
let reconnectAttempt = 0;

let generationCandidate = null;
let localStopIssued = false;
let localGenerationClaimLost = false;
let lastGenerationStatus = null;

let streamInFlight = false;
let latestStreamSnapshot = null;
let latestStreamReason = null;

let uiNode = null;


/* -------------------------------------------------------------------------- */
/* Utility                                                                    */
/* -------------------------------------------------------------------------- */

function log(...args) {
    if (getSettings().debug) {
        console.debug('[MultiClientSync]', ...args);
    }
}

function warn(...args) {
    console.warn('[MultiClientSync]', ...args);
}

function clone(value) {
    if (value === undefined) return undefined;

    if (typeof structuredClone === 'function') {
        try {
            return structuredClone(value);
        } catch {
            // fallback below
        }
    }

    return JSON.parse(JSON.stringify(value));
}

function randomId() {
    try {
        if (globalThis.crypto?.randomUUID) {
            return globalThis.crypto.randomUUID();
        }
    } catch {
        // fallback below
    }

    return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}-${Math.random().toString(36).slice(2)}`;
}

function stableStringify(value) {
    if (value === null || typeof value !== 'object') {
        return JSON.stringify(value);
    }

    if (Array.isArray(value)) {
        return `[${value.map(stableStringify).join(',')}]`;
    }

    return `{${Object.keys(value).sort().map(
        key => `${JSON.stringify(key)}:${stableStringify(value[key])}`,
    ).join(',')}}`;
}

async function sha256(text) {
    if (!globalThis.crypto?.subtle) {
        return null;
    }

    const data = new TextEncoder().encode(text);
    const digest = await globalThis.crypto.subtle.digest('SHA-256', data);

    return [...new Uint8Array(digest)]
        .map(x => x.toString(16).padStart(2, '0'))
        .join('');
}

function safeGetContext() {
    try {
        return SillyTavern.getContext();
    } catch (error) {
        warn('SillyTavern.getContext() unavailable', error);
        return null;
    }
}

function getSettings() {
    const settingsRoot = ctx?.extensionSettings || {};

    if (!settingsRoot[MODULE]) {
        settingsRoot[MODULE] = structuredClone(DEFAULTS);
    }

    for (const [key, value] of Object.entries(DEFAULTS)) {
        if (!(key in settingsRoot[MODULE])) {
            settingsRoot[MODULE][key] = value;
        }
    }

    return settingsRoot[MODULE];
}


/* -------------------------------------------------------------------------- */
/* Identity                                                                    */
/* -------------------------------------------------------------------------- */

function loadIdentity() {
    let deviceId;
    let clientId;

    try {
        deviceId = localStorage.getItem(`${MODULE}:deviceId`);
    } catch {
        // ignored
    }

    if (!deviceId) {
        deviceId = randomId();

        try {
            localStorage.setItem(`${MODULE}:deviceId`, deviceId);
        } catch {
            // ignored
        }
    }

    try {
        clientId = sessionStorage.getItem(`${MODULE}:clientId`);
    } catch {
        // ignored
    }

    if (!clientId) {
        clientId = randomId();

        try {
            sessionStorage.setItem(`${MODULE}:clientId`, clientId);
        } catch {
            // ignored
        }
    }

    currentDeviceId = deviceId;
    currentClientId = clientId;
}


/* -------------------------------------------------------------------------- */
/* Scope                                                                      */
/* -------------------------------------------------------------------------- */

function getScope() {
    if (!ctx) return null;

    const groupId = ctx.groupId ?? null;
    const characterId = ctx.characterId ?? null;
    const chatId = ctx.chatId ?? ctx.getCurrentChatId?.();

    if (!chatId) {
        return null;
    }

    if (groupId !== null && groupId !== undefined && String(groupId) !== '') {
        return {
            scopeType: 'group',
            chatId: String(chatId),
            characterId: null,
            groupId: String(groupId),
        };
    }

    if (characterId !== null && characterId !== undefined && String(characterId) !== '') {
        return {
            scopeType: 'character',
            chatId: String(chatId),
            characterId: String(characterId),
            groupId: null,
        };
    }

    return null;
}

function scopeKey(scope) {
    return scope ? JSON.stringify(scope) : 'none';
}

function sameScope(a, b) {
    return Boolean(a && b && scopeKey(a) === scopeKey(b));
}


/* -------------------------------------------------------------------------- */
/* Message identity / branch safety                                          */
/* -------------------------------------------------------------------------- */

function messageHasId(message) {
    return Boolean(message?.extra?.multi_client_sync_id);
}

function ensureMessageIds(messages) {
    let changed = false;

    if (!Array.isArray(messages)) {
        return false;
    }

    for (const message of messages) {
        if (!message || typeof message !== 'object') {
            continue;
        }

        if (!message.extra || typeof message.extra !== 'object' || Array.isArray(message.extra)) {
            message.extra = {};
        }

        if (!messageHasId(message)) {
            message.extra.multi_client_sync_id = randomId();
            changed = true;
        }
    }

    return changed;
}

function repairBranchIntegrity() {
    /**
     * Current ST branch/checkpoint chat metadata can share lineage fields with
     * the parent. A separate integrity identity per child prevents the sync
     * extension from depending on a shared parent identity.
     *
     * Only branch/checkpoint chats carrying main_chat are changed.
     */
    try {
        const metadata = ctx?.chatMetadata;

        if (!metadata || typeof metadata !== 'object') {
            return false;
        }

        if (!metadata.main_chat) {
            return false;
        }

        if (metadata.multi_client_sync_branch_integrity_v1) {
            return false;
        }

        if (typeof ctx.uuidv4 !== 'function') {
            return false;
        }

        metadata.integrity = ctx.uuidv4();
        metadata.multi_client_sync_branch_integrity_v1 = true;

        return true;
    } catch (error) {
        warn('Branch integrity repair failed', error);
        return false;
    }
}


/* -------------------------------------------------------------------------- */
/* Snapshot                                                                    */
/* -------------------------------------------------------------------------- */

function makeSnapshot() {
    if (!ctx || !currentScope) {
        return null;
    }

    const idsChanged = ensureMessageIds(ctx.chat || []);
    const messages = clone(ctx.chat || []);
    const metadata = clone(ctx.chatMetadata || {});

    if (metadata?.main_chat && !metadata.multi_client_sync_parent_chat_id) {
        metadata.multi_client_sync_parent_chat_id = String(metadata.main_chat);
    }

    return {
        scopeType: currentScope.scopeType,
        chatId: currentScope.chatId,
        characterId: currentScope.characterId,
        groupId: currentScope.groupId,
        chat: messages,
        chatMetadata: metadata,
        idsChanged,
    };
}

function normalizeSnapshot(snapshot) {
    if (!snapshot || typeof snapshot !== 'object') {
        return null;
    }

    if (!Array.isArray(snapshot.chat)) {
        return null;
    }

    const out = {
        scopeType: snapshot.scopeType,
        chatId: snapshot.chatId,
        characterId: snapshot.characterId ?? null,
        groupId: snapshot.groupId ?? null,
        chat: clone(snapshot.chat),
        chatMetadata: clone(snapshot.chatMetadata || {}),
    };

    ensureMessageIds(out.chat);

    return out;
}

function snapshotForHash(snapshot) {
    const normalized = normalizeSnapshot(snapshot);

    return stableStringify(normalized);
}

async function snapshotHash(snapshot) {
    return sha256(snapshotForHash(snapshot));
}


/* -------------------------------------------------------------------------- */
/* API                                                                         */
/* -------------------------------------------------------------------------- */

function getHeaders(extra = {}) {
    const base = typeof ctx?.getRequestHeaders === 'function'
        ? ctx.getRequestHeaders()
        : {};

    return {
        Accept: 'application/json',
        'Content-Type': 'application/json',
        ...base,
        ...extra,
    };
}

async function api(pathname, options = {}) {
    const response = await fetch(`${PLUGIN_BASE}${pathname}`, {
        credentials: 'same-origin',
        cache: 'no-store',
        ...options,
        headers: {
            ...getHeaders(),
            ...(options.headers || {}),
        },
    });

    let body = null;

    try {
        body = await response.json();
    } catch {
        // non-JSON response
    }

    if (!response.ok) {
        const error = new Error(
            body?.message || `HTTP ${response.status}`,
        );

        error.status = response.status;
        error.code = body?.code || `http_${response.status}`;
        error.state = body?.state;

        throw error;
    }

    return body || { ok: true };
}


/* -------------------------------------------------------------------------- */
/* IndexedDB durable queue                                                     */
/* -------------------------------------------------------------------------- */

function openDb() {
    return new Promise((resolve, reject) => {
        const request = indexedDB.open(DB_NAME, DB_VERSION);

        request.onerror = () => reject(request.error);

        request.onupgradeneeded = () => {
            const db = request.result;

            if (!db.objectStoreNames.contains('kv')) {
                db.createObjectStore('kv');
            }
        };

        request.onsuccess = () => resolve(request.result);
    });
}

async function dbGet(key) {
    try {
        const db = await openDb();

        return await new Promise((resolve, reject) => {
            const tx = db.transaction('kv', 'readonly');
            const request = tx.objectStore('kv').get(key);

            request.onerror = () => reject(request.error);
            request.onsuccess = () => resolve(request.result);

            tx.oncomplete = () => db.close();
            tx.onerror = () => db.close();
        });
    } catch (error) {
        log('IndexedDB get failed', error);
        return null;
    }
}

async function dbPut(key, value) {
    try {
        const db = await openDb();

        await new Promise((resolve, reject) => {
            const tx = db.transaction('kv', 'readwrite');

            tx.objectStore('kv').put(value, key);

            tx.oncomplete = resolve;
            tx.onerror = () => reject(tx.error);
            tx.onabort = () => reject(tx.error);
        });

        db.close();
    } catch (error) {
        log('IndexedDB put failed', error);
    }
}

async function dbDelete(key) {
    try {
        const db = await openDb();

        await new Promise((resolve, reject) => {
            const tx = db.transaction('kv', 'readwrite');

            tx.objectStore('kv').delete(key);

            tx.oncomplete = resolve;
            tx.onerror = () => reject(tx.error);
            tx.onabort = () => reject(tx.error);
        });

        db.close();
    } catch (error) {
        log('IndexedDB delete failed', error);
    }
}

function pendingKey(scope) {
    return `${MODULE}:pending:${scopeKey(scope)}`;
}

function metaKey(scope) {
    return `${MODULE}:meta:${scopeKey(scope)}`;
}

async function savePending(pending) {
    if (!pending?.scope) {
        return;
    }

    await dbPut(
        pendingKey(pending.scope),
        clone(pending),
    );
}

async function loadPending(scope) {
    return dbGet(pendingKey(scope));
}

async function deletePending(scope) {
    await dbDelete(pendingKey(scope));
}

async function saveMeta(scope, meta) {
    await dbPut(
        metaKey(scope),
        clone(meta),
    );
}


/* -------------------------------------------------------------------------- */
/* UI                                                                          */
/* -------------------------------------------------------------------------- */

function setStatus(status, detail = '') {
    if (!uiNode) {
        return;
    }

    const stateNode = uiNode.querySelector('.mcs-state');
    const detailNode = uiNode.querySelector('.mcs-detail');
    const stopButton = uiNode.querySelector('.mcs-stop-remote');

    if (stateNode) {
        stateNode.textContent = status;
    }

    if (detailNode) {
        detailNode.textContent = detail;
    }

    const active = currentState?.generation;
    const remote = Boolean(
        active &&
        active.ownerClientId !== currentClientId,
    );

    if (stopButton) {
        stopButton.hidden = !remote;
    }
}

function renderUi() {
    if (uiNode || !document.body) {
        return;
    }

    uiNode = document.createElement('div');
    uiNode.id = 'mcs-status-panel';

    uiNode.innerHTML = `
        <div class="mcs-title">Multi-client sync</div>
        <div class="mcs-state">Starting…</div>
        <div class="mcs-detail"></div>

        <button type="button" class="mcs-stop-remote" hidden>
            Request remote stop
        </button>

        <label class="mcs-toggle">
            <input type="checkbox" class="mcs-enabled">
            Enabled
        </label>

        <label class="mcs-toggle">
            <input type="checkbox" class="mcs-debug">
            Debug
        </label>
    `;

    Object.assign(uiNode.style, {
        position: 'fixed',
        right: '12px',
        bottom: '12px',
        zIndex: '99999',
        background: 'rgba(20,20,20,.94)',
        color: '#fff',
        padding: '9px 11px',
        borderRadius: '8px',
        fontSize: '12px',
        lineHeight: '1.35',
        maxWidth: '280px',
        boxShadow: '0 3px 18px rgba(0,0,0,.35)',
    });

    const title = uiNode.querySelector('.mcs-title');
    if (title) {
        title.style.fontWeight = '700';
        title.style.marginBottom = '3px';
    }

    const detail = uiNode.querySelector('.mcs-detail');
    if (detail) {
        detail.style.opacity = '0.75';
        detail.style.wordBreak = 'break-word';
    }

    for (const node of uiNode.querySelectorAll('.mcs-toggle')) {
        node.style.display = 'block';
    }

    for (const node of uiNode.querySelectorAll('button')) {
        node.style.marginTop = '5px';
    }

    document.body.appendChild(uiNode);

    const settings = getSettings();

    const enabledCheckbox = uiNode.querySelector('.mcs-enabled');
    const debugCheckbox = uiNode.querySelector('.mcs-debug');

    if (enabledCheckbox) {
        enabledCheckbox.checked = settings.enabled;

        enabledCheckbox.addEventListener('change', async event => {
            settings.enabled = event.target.checked;
            ctx?.saveSettingsDebounced?.();

            if (settings.enabled) {
                await start();
            } else {
                await stop();
            }
        });
    }

    if (debugCheckbox) {
        debugCheckbox.checked = settings.debug;

        debugCheckbox.addEventListener('change', event => {
            settings.debug = event.target.checked;
            ctx?.saveSettingsDebounced?.();
        });
    }

    uiNode.querySelector('.mcs-stop-remote')?.addEventListener(
        'click',
        () => void requestRemoteStop(),
    );
}


/* -------------------------------------------------------------------------- */
/* BroadcastChannel                                                            */
/* -------------------------------------------------------------------------- */

function broadcastLocal(message) {
    try {
        broadcastChannel?.postMessage({
            protocolVersion: PROTOCOL_VERSION,
            sourceClientId: currentClientId,
            sourceDeviceId: currentDeviceId,
            ...message,
        });
    } catch (error) {
        log('BroadcastChannel send failed', error);
    }
}


/* -------------------------------------------------------------------------- */
/* SSE                                                                          */
/* -------------------------------------------------------------------------- */

function closeSse() {
    if (!eventSource) {
        return;
    }

    try {
        eventSource.close();
    } catch {
        // ignored
    }

    eventSource = null;
}

function clearReconnectTimer() {
    if (reconnectTimer) {
        clearTimeout(reconnectTimer);
    }

    reconnectTimer = null;
}

function clearHeartbeat() {
    if (heartbeatTimer) {
        clearInterval(heartbeatTimer);
    }

    heartbeatTimer = null;
}

function scheduleReconnect(reason = 'reconnect') {
    if (
        destroyed ||
        !getSettings().enabled ||
        !currentScope ||
        reconnectTimer
    ) {
        return;
    }

    const delay = Math.min(
        MAX_RECONNECT_MS,
        500 * (2 ** Math.min(reconnectAttempt, 6))
            + Math.floor(Math.random() * 400),
    );

    reconnectAttempt += 1;

    setStatus(
        'Reconnecting',
        `${reason}; ${Math.ceil(delay / 1000)}s`,
    );

    reconnectTimer = setTimeout(async () => {
        reconnectTimer = null;

        try {
            await joinAndConnect(
                currentScope,
                { reconnect: true },
            );
        } catch (error) {
            warn('Reconnect failed', error);
            scheduleReconnect(
                error.code || 'reconnect_failed',
            );
        }
    }, delay);
}

function startHeartbeat() {
    clearHeartbeat();

    heartbeatTimer = setInterval(async () => {
        if (!currentScope || !currentState) {
            return;
        }

        try {
            const response = await api('/heartbeat', {
                method: 'POST',
                body: JSON.stringify({
                    protocolVersion: PROTOCOL_VERSION,
                    clientId: currentClientId,
                    deviceId: currentDeviceId,
                    scope: currentScope,

                    generationId:
                        currentState.generation?.ownerClientId === currentClientId
                            ? currentState.generation.id
                            : null,
                }),
            });

            if (response.state) {
                applyServerMeta(response.state);
            }
        } catch (error) {
            if (
                error.code === 'not_member' ||
                error.code === 'membership_expired' ||
                error.code === 'device_mismatch'
            ) {
                scheduleReconnect(error.code);
            } else {
                log('Heartbeat failed', error);
            }
        }
    }, HEARTBEAT_MS);
}

function applyServerMeta(state) {
    if (!currentState || !state) {
        return;
    }

    currentState.serverRevision =
        Number(state.revision) || 0;

    currentState.serverSeq =
        Number(state.seq) || 0;

    currentState.serverEpoch =
        state.epoch ||
        currentState.serverEpoch ||
        null;

    currentState.snapshotHash =
        state.snapshotHash ||
        currentState.snapshotHash ||
        null;

    currentState.generation =
        state.generation
            ? clone(state.generation)
            : null;

    void saveMeta(
        currentScope,
        {
            serverRevision:
                currentState.serverRevision,

            serverSeq:
                currentState.serverSeq,

            serverEpoch:
                currentState.serverEpoch,

            snapshotHash:
                currentState.snapshotHash,
        },
    );
}


/* -------------------------------------------------------------------------- */
/* ST application / persistence                                                */
/* -------------------------------------------------------------------------- */

async function applyAuthoritativeSnapshot(
    snapshot,
    {
        persist = true,
        serverState = null,
        reason = 'remote',
    } = {},
) {
    if (
        !snapshot ||
        !currentScope ||
        !sameScope(snapshot, currentScope)
    ) {
        return false;
    }

    const normalized =
        normalizeSnapshot(snapshot);

    if (!normalized) {
        return false;
    }

    const currentAtStart = getScope();

    if (!sameScope(currentAtStart, currentScope)) {
        return false;
    }

    /*
     * Direct array mutation avoids creating another sync event.
     */
    if (Array.isArray(ctx.chat)) {
        ctx.chat.splice(
            0,
            ctx.chat.length,
            ...normalized.chat.map(clone),
        );
    }

    if (
        ctx.chatMetadata &&
        typeof ctx.chatMetadata === 'object'
    ) {
        for (
            const key of Object.keys(ctx.chatMetadata)
        ) {
            delete ctx.chatMetadata[key];
        }

        Object.assign(
            ctx.chatMetadata,
            clone(normalized.chatMetadata || {}),
        );
    }

    if (
        typeof ctx.clearChat === 'function' &&
        typeof ctx.printMessages === 'function'
    ) {
        try {
            ctx.clearChat();
            ctx.printMessages();
        } catch (error) {
            log(
                'Render after remote apply failed',
                error,
            );
        }
    }

    if (persist) {
        await persistCurrentChat('remote-apply');
    }

    if (serverState) {
        currentState.serverSnapshot =
            clone(normalized);

        currentState.serverRevision =
            Number(serverState.revision)
            || currentState.serverRevision
            || 0;

        currentState.serverSeq =
            Number(serverState.seq)
            || currentState.serverSeq
            || 0;

        currentState.serverEpoch =
            serverState.epoch
            || currentState.serverEpoch
            || null;

        currentState.snapshotHash =
            serverState.snapshotHash
            || await snapshotHash(normalized);

        currentState.generation =
            serverState.generation
            ? clone(serverState.generation)
            : null;
    } else {
        currentState.serverSnapshot =
            clone(normalized);

        currentState.snapshotHash =
            await snapshotHash(normalized);
    }

    setStatus(
        'Synced',
        `${reason}; rev ${currentState.serverRevision}`,
    );

    return true;
}

function persistCurrentChat(reason = 'local') {
    const scopeAtStart =
        currentScope
            ? clone(currentScope)
            : null;

    if (
        !scopeAtStart ||
        !ctx?.saveChat
    ) {
        return Promise.resolve(false);
    }

    localSaveChain =
        localSaveChain.then(
            async () => {
                if (
                    !sameScope(
                        scopeAtStart,
                        getScope(),
                    )
                ) {
                    return false;
                }

                try {
                    /*
                     * ST exposes this as its public conditional-save path.
                     * We serialize our calls so sync cannot create overlapping
                     * local save requests from this extension.
                     */
                    await ctx.saveChat();

                    log(
                        'ST save requested',
                        reason,
                    );

                    return true;
                } catch (error) {
                    warn(
                        `ST save failed (${reason})`,
                        error,
                    );

                    return false;
                }
            },
        );

    return localSaveChain;
}


/* -------------------------------------------------------------------------- */
/* Three-way merge                                                             */
/* -------------------------------------------------------------------------- */

function messageValueChanged(a, b) {
    return stableStringify(a) !== stableStringify(b);
}

function mapByMessageId(messages) {
    const map = new Map();
    const duplicates = new Set();

    for (
        let index = 0;
        index < messages.length;
        index++
    ) {
        const id =
            messages[index]
                ?.extra
                ?.multi_client_sync_id;

        if (!id) {
            continue;
        }

        if (map.has(id)) {
            duplicates.add(id);
        }

        map.set(
            id,
            {
                message: messages[index],
                index,
            },
        );
    }

    return {
        map,
        duplicates,
    };
}

function mergeMessages3Way(
    base,
    local,
    remote,
    conflicts,
) {
    const baseMessages =
        Array.isArray(base?.chat)
            ? base.chat
            : [];

    const localMessages =
        Array.isArray(local?.chat)
            ? local.chat
            : [];

    const remoteMessages =
        Array.isArray(remote?.chat)
            ? remote.chat
            : [];

    const baseMapInfo =
        mapByMessageId(baseMessages);

    const localMapInfo =
        mapByMessageId(localMessages);

    const remoteMapInfo =
        mapByMessageId(remoteMessages);

    /*
     * Legacy or duplicate IDs cannot be merged safely.
     */
    if (
        baseMapInfo.map.size !== baseMessages.length ||
        localMapInfo.map.size !== localMessages.length ||
        remoteMapInfo.map.size !== remoteMessages.length
    ) {
        const sameAsBase =
            messageValueChanged(
                localMessages,
                baseMessages,
            ) === false;

        if (sameAsBase) {
            return remoteMessages.map(clone);
        }

        const remoteSameAsBase =
            messageValueChanged(
                remoteMessages,
                baseMessages,
            ) === false;

        if (remoteSameAsBase) {
            return localMessages.map(clone);
        }

        conflicts.push({
            type: 'message_identity',
            policy: 'remote_wins',
            reason:
                'legacy_or_duplicate_message_ids',
        });

        return remoteMessages.map(clone);
    }

    const resultById = new Map();

    const allIds = new Set([
        ...baseMapInfo.map.keys(),
        ...localMapInfo.map.keys(),
        ...remoteMapInfo.map.keys(),
    ]);

    for (const id of allIds) {
        const b =
            baseMapInfo.map.get(id)?.message;

        const l =
            localMapInfo.map.get(id)?.message;

        const r =
            remoteMapInfo.map.get(id)?.message;

        const lPresent = Boolean(l);
        const rPresent = Boolean(r);
        const bPresent = Boolean(b);

        if (!lPresent && !rPresent) {
            continue;
        }

        /*
         * New message.
         */
        if (!bPresent) {
            if (lPresent && rPresent) {
                if (messageValueChanged(l, r)) {
                    conflicts.push({
                        type: 'concurrent_insert',
                        id,
                        policy: 'remote_wins',
                    });

                    resultById.set(
                        id,
                        clone(r),
                    );
                } else {
                    resultById.set(
                        id,
                        clone(l),
                    );
                }
            } else if (lPresent) {
                resultById.set(
                    id,
                    clone(l),
                );
            } else {
                resultById.set(
                    id,
                    clone(r),
                );
            }

            continue;
        }

        const localSameAsBase =
            lPresent &&
            bPresent &&
            !messageValueChanged(l, b);

        const remoteSameAsBase =
            rPresent &&
            bPresent &&
            !messageValueChanged(r, b);

        /*
         * Local deletion.
         */
        if (!lPresent) {
            if (remoteSameAsBase) {
                continue;
            }

            if (
                !rPresent ||
                messageValueChanged(r, b)
            ) {
                conflicts.push({
                    type: 'delete_vs_change',
                    id,
                    policy: 'remote_wins',
                });

                if (rPresent) {
                    resultById.set(
                        id,
                        clone(r),
                    );
                }
            }

            continue;
        }

        /*
         * Remote deletion.
         */
        if (!rPresent) {
            if (localSameAsBase) {
                continue;
            }

            conflicts.push({
                type: 'change_vs_delete',
                id,
                policy: 'remote_wins',
            });

            continue;
        }

        /*
         * Only remote changed.
         */
        if (
            localSameAsBase &&
            !remoteSameAsBase
        ) {
            resultById.set(
                id,
                clone(r),
            );

            continue;
        }

        /*
         * Only local changed.
         */
        if (
            remoteSameAsBase &&
            !localSameAsBase
        ) {
            resultById.set(
                id,
                clone(l),
            );

            continue;
        }

        /*
         * Both changed.
         */
        if (
            !localSameAsBase &&
            !remoteSameAsBase
        ) {
            if (messageValueChanged(l, r)) {
                conflicts.push({
                    type: 'concurrent_edit',
                    id,
                    policy: 'remote_wins',
                });

                resultById.set(
                    id,
                    clone(r),
                );
            } else {
                resultById.set(
                    id,
                    clone(l),
                );
            }

            continue;
        }

        /*
         * Neither changed.
         */
        resultById.set(
            id,
            clone(b),
        );
    }

    /*
     * Preserve remote order first.
     */
    const output = [];
    const emitted = new Set();

    for (const message of remoteMessages) {
        const id =
            message
                ?.extra
                ?.multi_client_sync_id;

        if (
            !id ||
            !resultById.has(id) ||
            emitted.has(id)
        ) {
            continue;
        }

        output.push(
            clone(resultById.get(id)),
        );

        emitted.add(id);
    }

    /*
     * Place local-only inserts beside their local predecessor.
     */
    const localIds =
        localMessages
            .map(
                message =>
                    message
                        ?.extra
                        ?.multi_client_sync_id,
            )
            .filter(Boolean);

    for (
        let i = 0;
        i < localIds.length;
        i++
    ) {
        const id = localIds[i];

        if (
            emitted.has(id) ||
            !resultById.has(id) ||
            remoteMapInfo.map.has(id)
        ) {
            continue;
        }

        let insertAt =
            output.length;

        for (
            let j = i - 1;
            j >= 0;
            j--
        ) {
            const previousId =
                localIds[j];

            const index =
                output.findIndex(
                    message =>
                        message
                            ?.extra
                            ?.multi_client_sync_id
                        === previousId,
                );

            if (index >= 0) {
                insertAt = index + 1;
                break;
            }
        }

        output.splice(
            insertAt,
            0,
            clone(resultById.get(id)),
        );

        emitted.add(id);

        conflicts.push({
            type: 'concurrent_insert',
            id,
            policy: 'local_position_near_anchor',
        });
    }

    return output;
}

function mergeObject3Way(
    base,
    local,
    remote,
    conflicts,
    fieldName,
) {
    const out =
        clone(remote || {});

    const keys = new Set([
        ...Object.keys(base || {}),
        ...Object.keys(local || {}),
        ...Object.keys(remote || {}),
    ]);

    for (const key of keys) {
        const b = base?.[key];
        const l = local?.[key];
        const r = remote?.[key];

        const localChanged =
            messageValueChanged(l, b);

        const remoteChanged =
            messageValueChanged(r, b);

        if (
            localChanged &&
            !remoteChanged
        ) {
            out[key] = clone(l);
        } else if (
            localChanged &&
            remoteChanged &&
            messageValueChanged(l, r)
        ) {
            conflicts.push({
                type: 'concurrent_metadata',
                field: fieldName,
                key,
                policy: 'remote_wins',
            });

            out[key] = clone(r);
        }
    }

    return out;
}

function mergeSnapshots3Way(
    base,
    local,
    remote,
) {
    const conflicts = [];

    const merged =
        clone(remote);

    merged.chat =
        mergeMessages3Way(
            base,
            local,
            remote,
            conflicts,
        );

    merged.chatMetadata =
        mergeObject3Way(
            base?.chatMetadata || {},
            local?.chatMetadata || {},
            remote?.chatMetadata || {},
            conflicts,
            'chatMetadata',
        );

    merged.scopeType =
        remote.scopeType;

    merged.chatId =
        remote.chatId;

    merged.characterId =
        remote.characterId;

    merged.groupId =
        remote.groupId;

    return {
        snapshot: merged,
        conflicts,
    };
}


/* -------------------------------------------------------------------------- */
/* Pending mutation pipeline                                                   */
/* -------------------------------------------------------------------------- */

async function sendPending(
    pending,
    depth = 0,
) {
    if (
        !pending ||
        !currentScope ||
        !sameScope(
            pending.scope,
            currentScope,
        )
    ) {
        return false;
    }

    if (depth > 5) {
        setStatus(
            'Pending',
            'rebase limit reached; retrying on next sync',
        );

        return false;
    }

    try {
        const result =
            await api('/event', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        pending.scope,

                    opId:
                        pending.opId,

                    type:
                        pending.type,

                    baseRevision:
                        pending.baseRevision,

                    payload:
                        pending.payload || {},

                    snapshot:
                        pending.snapshot,
                }),
            });

        if (result.state) {
            applyServerMeta(
                result.state,
            );
        }

        if (result.state?.snapshot) {
            currentState.serverSnapshot =
                normalizeSnapshot(
                    result.state.snapshot,
                );
        }

        await deletePending(
            pending.scope,
        );

        currentState.pending = null;

        setStatus(
            'Synced',
            `accepted ${pending.type}; rev ${currentState.serverRevision}`,
        );

        broadcastLocal({
            kind: 'accepted',
            scope: pending.scope,
            event: result.event,
            state: result.state,
        });

        return true;
    } catch (error) {
        /*
         * Optimistic concurrency conflict.
         */
        if (
            error.code === 'stale_revision' &&
            error.state?.snapshot
        ) {
            const remote =
                normalizeSnapshot(
                    error.state.snapshot,
                );

            const base =
                normalizeSnapshot(
                    pending.baseSnapshot ||
                    currentState.serverSnapshot ||
                    remote,
                );

            const local =
                normalizeSnapshot(
                    pending.snapshot,
                );

            const merged =
                mergeSnapshots3Way(
                    base,
                    local,
                    remote,
                );

            currentState.serverSnapshot =
                remote;

            currentState.serverRevision =
                Number(error.state.revision)
                || 0;

            currentState.serverSeq =
                Number(error.state.seq)
                || currentState.serverSeq
                || 0;

            currentState.serverEpoch =
                error.state.epoch
                || currentState.serverEpoch;

            currentState.generation =
                error.state.generation
                || null;

            currentState.pending = {
                ...pending,

                baseSnapshot:
                    remote,

                baseRevision:
                    currentState.serverRevision,

                snapshot:
                    merged.snapshot,

                opId:
                    randomId(),

                conflicts:
                    [
                        ...(pending.conflicts || []),
                        ...merged.conflicts,
                    ],
            };

            await savePending(
                currentState.pending,
            );

            /*
             * Show the server state first.
             */
            await applyAuthoritativeSnapshot(
                remote,
                {
                    persist: true,
                    serverState: error.state,
                    reason: 'conflict-resync',
                },
            );

            /*
             * Then apply the deterministic three-way merge locally.
             * Server revision remains the remote revision until the merged
             * snapshot is accepted.
             */
            await applyAuthoritativeSnapshot(
                merged.snapshot,
                {
                    persist: true,
                    reason: 'apply-three-way-merge',
                },
            );

            currentState.serverSnapshot =
                remote;

            currentState.serverRevision =
                Number(error.state.revision)
                || 0;

            currentState.serverSeq =
                Number(error.state.seq)
                || 0;

            currentState.serverEpoch =
                error.state.epoch
                || currentState.serverEpoch;

            currentState.generation =
                error.state.generation
                || null;

            if (merged.conflicts.length) {
                setStatus(
                    'Conflict resolved',
                    `${merged.conflicts.length} conflict(s); server-biased`,
                );
            }

            return sendPending(
                currentState.pending,
                depth + 1,
            );
        }

        if (
            error.code === 'generation_lock'
        ) {
            setStatus(
                'Generation active',
                'Remote generation owns this chat',
            );
        } else if (
            error.code === 'not_member' ||
            error.code === 'membership_expired'
        ) {
            scheduleReconnect(
                error.code,
            );
        } else {
            setStatus(
                'Pending',
                error.message ||
                error.code ||
                'event retry',
            );
        }

        return false;
    }
}

async function enqueueSnapshotMutation(
    type,
    payload = {},
    {
        persist = true,
    } = {},
) {
    if (
        !getSettings().enabled ||
        !currentScope ||
        !currentState
    ) {
        return;
    }

    if (currentState.suppressLocalEvents) {
        return;
    }

    /*
     * While another generation is active, non-owner clients do not send chat
     * mutations. Owner stream data is sent through generation_stream instead.
     */
    if (
        currentState.generation &&
        currentState.generation.ownerClientId !==
            currentClientId
    ) {
        setStatus(
            'Generation active',
            'Remote owner has the mutation lock',
        );

        return;
    }

    /*
     * Owner-side generation mutations are treated as stream state.
     */
    if (
        currentState.generation &&
        currentState.generation.ownerClientId ===
            currentClientId &&
        !localGenerationClaimLost
    ) {
        await queueStreamSnapshot(type);
        return;
    }

    if (persist) {
        await persistCurrentChat(type);
    }

    const snapshot =
        makeSnapshot();

    if (!snapshot) {
        return;
    }

    if (
        snapshot.idsChanged &&
        persist
    ) {
        await persistCurrentChat(
            'stable-message-ids',
        );
    }

    delete snapshot.idsChanged;

    const existing =
        currentState.pending;

    const pending = existing
        ? {
            ...existing,
            snapshot,
            type,
            payload,
            opId: randomId(),
        }
        : {
            scope:
                clone(currentScope),

            opId:
                randomId(),

            type,

            payload,

            baseRevision:
                currentState.serverRevision,

            baseSnapshot:
                clone(
                    currentState.serverSnapshot
                    || snapshot,
                ),

            snapshot,

            conflicts: [],
        };

    currentState.pending =
        pending;

    await savePending(
        pending,
    );

    broadcastLocal({
        kind: 'local_pending',
        scope: currentScope,
        type,
    });

    await sendPending(
        pending,
    );
}

function enqueueSnapshotMutationSoon(
    type,
    payload = {},
) {
    if (localMutationTimer) {
        clearTimeout(
            localMutationTimer,
        );
    }

    localMutationTimer =
        setTimeout(
            () => {
                localMutationTimer = null;

                void enqueueSnapshotMutation(
                    type,
                    payload,
                );
            },
            SNAPSHOT_DEBOUNCE_MS,
        );
}


/* -------------------------------------------------------------------------- */
/* Generation ownership / streaming                                           */
/* -------------------------------------------------------------------------- */

async function claimGeneration() {
    if (
        !currentScope ||
        !currentState
    ) {
        return false;
    }

    const generationId =
        randomId();

    generationCandidate =
        generationId;

    localStopIssued =
        false;

    localGenerationClaimLost =
        false;

    try {
        const result =
            await api('/event', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        currentScope,

                    opId:
                        randomId(),

                    type:
                        'generation_claim',

                    baseRevision:
                        currentState.serverRevision,

                    generationId,

                    payload: {},
                }),
            });

        if (result.state) {
            applyServerMeta(
                result.state,
            );
        }

        if (
            result.state?.generation?.id !==
            generationId
        ) {
            localGenerationClaimLost =
                true;

            try {
                ctx?.stopGeneration?.();
            } catch {
                // ignored
            }

            return false;
        }

        currentState.generation =
            clone(
                result.state.generation,
            );

        currentState.serverSnapshot =
            normalizeSnapshot(
                result.state.snapshot ||
                currentState.serverSnapshot,
            );

        setStatus(
            'Generating',
            'This client owns generation',
        );

        broadcastLocal({
            kind: 'generation_owner',
            scope: currentScope,
            state: result.state,
        });

        return true;
    } catch (error) {
        localGenerationClaimLost =
            true;

        if (
            error.code === 'generation_owned' ||
            error.code === 'generation_not_owner'
        ) {
            try {
                ctx?.stopGeneration?.();
            } catch {
                // ignored
            }

            setStatus(
                'Generation busy',
                'Stopped local generation; another client owns it',
            );
        } else if (
            error.code === 'stale_revision' &&
            error.state
        ) {
            applyServerMeta(
                error.state,
            );

            if (
                error.state.snapshot
            ) {
                await applyAuthoritativeSnapshot(
                    error.state.snapshot,
                    {
                        serverState:
                            error.state,

                        reason:
                            'claim-resync',
                    },
                );
            }

            try {
                ctx?.stopGeneration?.();
            } catch {
                // ignored
            }
        } else {
            warn(
                'Generation claim failed',
                error,
            );

            try {
                ctx?.stopGeneration?.();
            } catch {
                // ignored
            }
        }

        return false;
    }
}

async function queueStreamSnapshot(
    reason = 'token',
) {
    if (
        !currentScope ||
        !currentState?.generation ||
        currentState.generation.ownerClientId !==
            currentClientId ||
        localGenerationClaimLost
    ) {
        return;
    }

    latestStreamSnapshot =
        makeSnapshot();

    if (!latestStreamSnapshot) {
        return;
    }

    delete latestStreamSnapshot.idsChanged;

    latestStreamReason =
        reason;

    if (pendingStreamTimer) {
        return;
    }

    pendingStreamTimer =
        setTimeout(
            () => {
                pendingStreamTimer = null;
                void flushStreamSnapshot();
            },
            STREAM_FLUSH_MS,
        );
}

async function flushStreamSnapshot() {
    if (
        streamInFlight ||
        !latestStreamSnapshot ||
        !currentState?.generation
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

    streamInFlight =
        true;

    const generation =
        currentState.generation;

    const streamSeq =
        Number(
            generation.streamSeq || 0,
        ) + 1;

    try {
        const result =
            await api('/event', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        currentScope,

                    opId:
                        randomId(),

                    type:
                        'generation_stream',

                    baseRevision:
                        currentState.serverRevision,

                    generationId:
                        generation.id,

                    streamSeq,

                    payload: {
                        reason,
                    },

                    snapshot,
                }),
            });

        if (result.state) {
            applyServerMeta(
                result.state,
            );

            currentState.serverSnapshot =
                normalizeSnapshot(
                    result.state.snapshot ||
                    snapshot,
                );

            if (
                result.state.generation
            ) {
                currentState.generation =
                    clone(
                        result.state.generation,
                    );
            }
        }

        broadcastLocal({
            kind: 'stream',
            scope: currentScope,
            state: result.state,
            event: result.event,
        });
    } catch (error) {
        if (
            error.code === 'generation_stale' ||
            error.code === 'generation_not_owner' ||
            error.code === 'generation_expired'
        ) {
            localGenerationClaimLost =
                true;

            try {
                ctx?.stopGeneration?.();
            } catch {
                // ignored
            }

            setStatus(
                'Generation ended',
                'Ownership lost; local generation stopped',
            );
        } else if (
            error.code === 'stale_revision' &&
            error.state?.snapshot
        ) {
            currentState.serverRevision =
                Number(
                    error.state.revision,
                ) || 0;

            currentState.serverSeq =
                Number(
                    error.state.seq,
                ) || 0;

            currentState.serverEpoch =
                error.state.epoch ||
                currentState.serverEpoch;

            currentState.serverSnapshot =
                normalizeSnapshot(
                    error.state.snapshot,
                );

            currentState.generation =
                error.state.generation ||
                null;

            setStatus(
                'Generating',
                'Stream revision changed; state will resync',
            );
        } else {
            log(
                'Stream update failed',
                error,
            );
        }
    } finally {
        streamInFlight =
            false;

        if (latestStreamSnapshot) {
            void flushStreamSnapshot();
        }
    }
}

async function waitForStreamIdle() {
    if (latestStreamSnapshot) {
        await flushStreamSnapshot();
    }

    while (streamInFlight) {
        await new Promise(
            resolve => setTimeout(
                resolve,
                20,
            ),
        );
    }

    if (latestStreamSnapshot) {
        await flushStreamSnapshot();
    }
}

async function finishGeneration(
    status,
) {
    if (
        !currentScope ||
        !currentState?.generation ||
        currentState.generation.ownerClientId !==
            currentClientId ||
        localGenerationClaimLost
    ) {
        return;
    }

    await waitForStreamIdle();

    /*
     * Final persistence request before terminal state.
     */
    await persistCurrentChat(
        'generation-terminal',
    );

    const generation =
        currentState.generation;

    const snapshot =
        makeSnapshot();

    if (!snapshot) {
        return;
    }

    delete snapshot.idsChanged;

    try {
        const result =
            await api('/event', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        currentScope,

                    opId:
                        randomId(),

                    type:
                        'generation_terminal',

                    baseRevision:
                        currentState.serverRevision,

                    generationId:
                        generation.id,

                    status,

                    payload: {},

                    snapshot,
                }),
            });

        if (result.state) {
            applyServerMeta(
                result.state,
            );

            currentState.serverSnapshot =
                normalizeSnapshot(
                    result.state.snapshot ||
                    snapshot,
                );

            currentState.generation =
                result.state.generation ||
                null;
        }

        lastGenerationStatus =
            status;

        broadcastLocal({
            kind: 'generation_terminal',
            scope: currentScope,
            status,
            state: result.state,
        });

        setStatus(
            'Synced',
            `${status}; rev ${currentState.serverRevision}`,
        );
    } catch (error) {
        if (
            error.code === 'stale_revision' &&
            error.state?.snapshot
        ) {
            currentState.serverRevision =
                Number(
                    error.state.revision,
                ) || 0;

            currentState.serverSeq =
                Number(
                    error.state.seq,
                ) || 0;

            currentState.serverEpoch =
                error.state.epoch ||
                currentState.serverEpoch;

            currentState.serverSnapshot =
                normalizeSnapshot(
                    error.state.snapshot,
                );

            currentState.generation =
                error.state.generation ||
                null;

            if (
                currentState.generation?.ownerClientId ===
                currentClientId
            ) {
                setTimeout(
                    () => void finishGeneration(status),
                    0,
                );
            }
        } else {
            warn(
                'Generation terminal update failed',
                error,
            );
        }
    } finally {
        generationCandidate =
            null;

        localStopIssued =
            false;
    }
}

async function requestRemoteStop(
    retry = false,
) {
    if (
        !currentState?.generation ||
        !currentScope
    ) {
        return false;
    }

    const generationId =
        currentState.generation.id;

    try {
        const result =
            await api('/event', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        currentScope,

                    opId:
                        randomId(),

                    type:
                        'generation_stop_request',

                    baseRevision:
                        currentState.serverRevision,

                    generationId,

                    payload: {},
                }),
            });

        if (result.state) {
            applyServerMeta(
                result.state,
            );
        }

        setStatus(
            'Stop requested',
            `generation ${generationId.slice(0, 8)}`,
        );

        return true;
    } catch (error) {
        if (
            error.code === 'stale_revision' &&
            error.state
        ) {
            applyServerMeta(
                error.state,
            );

            if (
                error.state.snapshot
            ) {
                await applyAuthoritativeSnapshot(
                    error.state.snapshot,
                    {
                        serverState:
                            error.state,

                        persist:
                            false,

                        reason:
                            'stop-request-resync',
                    },
                );
            }

            if (
                currentState?.generation?.id ===
                    generationId &&
                !retry
            ) {
                return requestRemoteStop(
                    true,
                );
            }
        }

        warn(
            'Remote stop request failed',
            error,
        );

        return false;
    }
}


/* -------------------------------------------------------------------------- */
/* SSE event handling                                                          */
/* -------------------------------------------------------------------------- */

async function handleSseEvent(data) {
    if (!data) {
        return;
    }

    if (
        data.protocolVersion &&
        data.protocolVersion !==
            PROTOCOL_VERSION
    ) {
        setStatus(
            'Protocol mismatch',
            `server=${data.protocolVersion}, client=${PROTOCOL_VERSION}`,
        );

        closeSse();
        return;
    }

    if (
        data.type === 'shutdown'
    ) {
        closeSse();
        scheduleReconnect(
            'server shutdown',
        );
        return;
    }

    if (
        data.type ===
            'generation_stop_requested'
    ) {
        applyServerMeta(
            data.state || {},
        );

        if (
            currentState?.generation?.ownerClientId ===
                currentClientId &&
            currentState.generation.id ===
                data.generation?.id
        ) {
            try {
                ctx?.stopGeneration?.();
            } catch (error) {
                warn(
                    'Failed to execute remote stop',
                    error,
                );
            }
        }

        setStatus(
            'Stop requested',
            'owner is stopping generation',
        );

        return;
    }

    if (
        data.type ===
            'generation_claimed'
    ) {
        applyServerMeta(
            data.state || {},
        );

        if (
            data.generation?.ownerClientId !==
                currentClientId
        ) {
            if (
                generationCandidate &&
                !localGenerationClaimLost
            ) {
                localGenerationClaimLost =
                    true;

                try {
                    ctx?.stopGeneration?.();
                } catch {
                    // ignored
                }
            }

            setStatus(
                'Remote generation',
                'another client is generating',
            );
        }

        return;
    }

    if (
        data.type ===
            'generation_abandoned'
    ) {
        applyServerMeta(
            data.state || {},
        );

        currentState.generation =
            null;

        if (
            generationCandidate &&
            !localGenerationClaimLost
        ) {
            localGenerationClaimLost =
                true;

            try {
                ctx?.stopGeneration?.();
            } catch {
                // ignored
            }
        }

        setStatus(
            'Generation released',
            'owner lost/lease expired',
        );

        return;
    }

    if (
        data.type ===
            'generation_terminal'
    ) {
        applyServerMeta(
            data.state || {},
        );

        if (data.snapshot) {
            await applyAuthoritativeSnapshot(
                data.snapshot,
                {
                    serverState:
                        data.state,

                    persist:
                        true,

                    reason:
                        `remote ${
                            data.payload?.status
                            || 'generation terminal'
                        }`,
                },
            );
        }

        currentState.generation =
            null;

        return;
    }

    if (data.state) {
        applyServerMeta(
            data.state,
        );
    }

    const incomingSnapshot =
        data.snapshot ||
        data.event?.snapshot;

    if (!incomingSnapshot) {
        const incomingType =
            data.type ||
            data.event?.type ||
            'remote update';

        if (
            incomingType ===
                'generation_stream'
        ) {
            try {
                const state =
                    await api(
                        `/state?clientId=${
                            encodeURIComponent(
                                currentClientId,
                            )
                        }&scope=${
                            encodeURIComponent(
                                JSON.stringify(
                                    currentScope,
                                ),
                            )
                        }`,
                    );

                if (
                    state.state?.snapshot
                ) {
                    await applyAuthoritativeSnapshot(
                        state.state.snapshot,
                        {
                            serverState:
                                state.state,

                            persist:
                                !state.state.generation,

                            reason:
                                'stream-recovery',
                        },
                    );
                }
            } catch (error) {
                warn(
                    'Stream recovery state fetch failed',
                    error,
                );
            }
        }

        return;
    }

    const sourceClientId =
        data.sourceClientId ??
        data.event?.sourceClientId;

    if (
        sourceClientId ===
        currentClientId
    ) {
        currentState.serverSnapshot =
            normalizeSnapshot(
                incomingSnapshot,
            );

        return;
    }

    if (
        !currentScope ||
        !currentState
    ) {
        return;
    }

    if (
        !sameScope(
            incomingSnapshot,
            currentScope,
        ) &&
        incomingSnapshot.scopeType
    ) {
        return;
    }

    const incomingType =
        data.type ||
        data.event?.type ||
        'remote update';

    const isStream =
        incomingType ===
            'generation_stream';

    await applyAuthoritativeSnapshot(
        incomingSnapshot,
        {
            serverState:
                data.state,

            persist:
                !isStream,

            reason:
                incomingType,
        },
    );
}

function connectSse() {
    closeSse();

    if (
        !currentScope ||
        destroyed ||
        !getSettings().enabled
    ) {
        return;
    }

    const scope =
        encodeURIComponent(
            JSON.stringify(
                currentScope,
            ),
        );

    const url =
        `${location.origin}${PLUGIN_BASE}/events`
        + `?clientId=${encodeURIComponent(currentClientId)}`
        + `&deviceId=${encodeURIComponent(currentDeviceId)}`
        + `&scope=${scope}`;

    try {
        eventSource =
            new EventSource(
                url,
                {
                    withCredentials: true,
                },
            );
    } catch (error) {
        warn(
            'EventSource creation failed',
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
                    data.epoch &&
                    currentState.serverEpoch &&
                    data.epoch !==
                        currentState.serverEpoch
                ) {
                    void resyncCurrentScope(
                        'server epoch changed',
                    );
                }

                applyServerMeta(
                    data,
                );

                reconnectAttempt =
                    0;

                setStatus(
                    'Live',
                    `rev ${currentState.serverRevision}`,
                );
            } catch (error) {
                log(
                    'Invalid SSE hello',
                    error,
                );
            }
        },
    );

    eventSource.addEventListener(
        'sync',
        event => {
            try {
                const data =
                    JSON.parse(
                        event.data,
                    );

                void handleSseEvent(
                    data,
                );
            } catch (error) {
                warn(
                    'Invalid SSE sync event',
                    error,
                );
            }
        },
    );

    eventSource.addEventListener(
        'resync_required',
        event => {
            try {
                const data =
                    JSON.parse(
                        event.data,
                    );

                void resyncCurrentScope(
                    data.reason ||
                    'server requested resync',
                );
            } catch (error) {
                warn(
                    'Invalid SSE resync event',
                    error,
                );

                void resyncCurrentScope(
                    'malformed resync event',
                );
            }
        },
    );

    eventSource.addEventListener(
        'shutdown',
        () => {
            closeSse();

            scheduleReconnect(
                'server shutdown',
            );
        },
    );

    eventSource.onerror = () => {
        closeSse();

        scheduleReconnect(
            'SSE disconnected',
        );
    };
}


/* -------------------------------------------------------------------------- */
/* Server state/reconnect                                                       */
/* -------------------------------------------------------------------------- */

async function resyncCurrentScope(
    reason = 'manual',
) {
    if (
        !currentScope ||
        !currentState
    ) {
        return;
    }

    try {
        const response =
            await api(
                `/state?clientId=${
                    encodeURIComponent(
                        currentClientId,
                    )
                }&scope=${
                    encodeURIComponent(
                        JSON.stringify(
                            currentScope,
                        ),
                    )
                }`,
            );

        if (response.state) {
            applyServerMeta(
                response.state,
            );

            if (
                response.state.snapshot
            ) {
                await applyAuthoritativeSnapshot(
                    response.state.snapshot,
                    {
                        serverState:
                            response.state,

                        reason,
                    },
                );
            }
        }

        const pending =
            await loadPending(
                currentScope,
            );

        currentState.pending =
            pending;

        if (pending) {
            await sendPending(
                pending,
            );
        }

        connectSse();

        reconnectAttempt =
            0;
    } catch (error) {
        warn(
            'Resync failed',
            error,
        );

        scheduleReconnect(
            error.code ||
            'resync_failed',
        );
    }
}

async function joinAndConnect(
    scope,
    {
        reconnect = false,
    } = {},
) {
    if (
        !scope ||
        destroyed ||
        !getSettings().enabled
    ) {
        return;
    }

    const thisEpoch =
        scopeEpoch;

    const response =
        await api('/join', {
            method: 'POST',

            body: JSON.stringify({
                protocolVersion:
                    PROTOCOL_VERSION,

                clientId:
                    currentClientId,

                deviceId:
                    currentDeviceId,

                scope,
            }),
        });

    if (
        thisEpoch !== scopeEpoch ||
        !sameScope(
            scope,
            currentScope,
        )
    ) {
        return;
    }

    const serverState =
        response.state;

    if (!currentState) {
        currentState = {
            serverRevision:
                Number(
                    serverState?.revision,
                ) || 0,

            serverSeq:
                Number(
                    serverState?.seq,
                ) || 0,

            serverEpoch:
                serverState?.epoch ||
                null,

            serverSnapshot:
                serverState?.snapshot
                    ? normalizeSnapshot(
                        serverState.snapshot,
                    )
                    : null,

            snapshotHash:
                serverState?.snapshotHash
                || null,

            generation:
                serverState?.generation
                    ? clone(
                        serverState.generation,
                    )
                    : null,

            pending:
                null,

            suppressLocalEvents:
                false,

            conflictCount:
                0,
        };
    } else {
        applyServerMeta(
            serverState || {},
        );

        if (
            serverState?.snapshot
        ) {
            currentState.serverSnapshot =
                normalizeSnapshot(
                    serverState.snapshot,
                );
        }
    }

    /*
     * If the server already has canonical state, use it on initial join unless
     * there is a durable local pending mutation.
     */
    if (serverState?.snapshot) {
        const localSnapshot =
            makeSnapshot();

        if (
            !currentState.serverSnapshot
        ) {
            currentState.serverSnapshot =
                normalizeSnapshot(
                    serverState.snapshot,
                );
        }

        const localHash =
            localSnapshot
                ? await snapshotHash(
                    localSnapshot,
                )
                : null;

        const remoteHash =
            serverState.snapshotHash;

        if (
            remoteHash &&
            localHash &&
            remoteHash !== localHash &&
            !reconnect
        ) {
            const pending =
                await loadPending(
                    scope,
                );

            if (!pending) {
                await applyAuthoritativeSnapshot(
                    serverState.snapshot,
                    {
                        serverState,
                        reason:
                            'initial authoritative state',
                    },
                );
            }
        }
    } else {
        /*
         * First client for this scope bootstraps canonical server state.
         */
        const snapshot =
            makeSnapshot();

        if (snapshot) {
            const idsChanged =
                snapshot.idsChanged;

            delete snapshot.idsChanged;

            currentState.pending = {
                scope:
                    clone(scope),

                opId:
                    randomId(),

                type:
                    'snapshot_bootstrap',

                payload: {
                    bootstrap:
                        true,
                },

                baseRevision:
                    0,

                baseSnapshot:
                    clone(snapshot),

                snapshot,

                conflicts: [],
            };

            await savePending(
                currentState.pending,
            );

            if (idsChanged) {
                await persistCurrentChat(
                    'bootstrap-message-ids',
                );
            }

            await sendPending(
                currentState.pending,
            );
        }
    }

    const pending =
        await loadPending(
            scope,
        );

    currentState.pending =
        pending;

    if (pending) {
        await sendPending(
            pending,
        );
    }

    connectSse();
    startHeartbeat();

    if (reconnect) {
        setStatus(
            'Live',
            `reconnected; rev ${currentState.serverRevision}`,
        );
    }
}

async function switchScope(
    nextScope,
) {
    const previousScope =
        currentScope;

    scopeEpoch += 1;

    const myEpoch =
        scopeEpoch;

    clearReconnectTimer();
    closeSse();
    clearHeartbeat();

    latestStreamSnapshot =
        null;

    latestStreamReason =
        null;

    if (pendingStreamTimer) {
        clearTimeout(
            pendingStreamTimer,
        );
    }

    pendingStreamTimer =
        null;

    currentScope =
        nextScope
            ? clone(nextScope)
            : null;

    currentState =
        null;

    generationCandidate =
        null;

    localGenerationClaimLost =
        false;

    lastGenerationStatus =
        null;

    if (previousScope) {
        try {
            await api('/leave', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        previousScope,
                }),
            });
        } catch (error) {
            log(
                'Leave failed',
                error,
            );
        }
    }

    if (
        myEpoch !== scopeEpoch ||
        !currentScope ||
        destroyed ||
        !getSettings().enabled
    ) {
        return;
    }

    const repairedBranchIntegrity =
        repairBranchIntegrity();

    if (repairedBranchIntegrity) {
        await persistCurrentChat(
            'branch-integrity-repair',
        );
    }

    try {
        await joinAndConnect(
            currentScope,
        );
    } catch (error) {
        warn(
            'Scope join failed',
            error,
        );

        setStatus(
            'Offline',
            error.message ||
            error.code ||
            'join failed',
        );

        scheduleReconnect(
            error.code ||
            'join failed',
        );
    }
}

async function syncCurrentScope(
    {
        force = false,
    } = {},
) {
    if (
        !ctx ||
        !getSettings().enabled
    ) {
        return;
    }

    const nextScope =
        getScope();

    if (
        !force &&
        sameScope(
            nextScope,
            currentScope,
        ) &&
        currentState
    ) {
        return;
    }

    await switchScope(
        nextScope,
    );
}


/* -------------------------------------------------------------------------- */
/* ST event handling                                                           */
/* -------------------------------------------------------------------------- */

function eventMessageId(args) {
    const first =
        args?.[0];

    if (
        typeof first === 'number' &&
        Number.isInteger(first)
    ) {
        return first;
    }

    if (
        typeof first === 'string' &&
        /^\d+$/.test(first)
    ) {
        return Number(first);
    }

    if (
        first &&
        typeof first.messageId === 'number'
    ) {
        return first.messageId;
    }

    return null;
}

function onMessageMutation(
    type,
    ...args
) {
    if (
        !currentScope ||
        !currentState ||
        currentState.suppressLocalEvents
    ) {
        return;
    }

    const owner =
        currentState.generation?.ownerClientId ===
            currentClientId &&
        !localGenerationClaimLost;

    /*
     * During a local generation, message updates are stream state rather than
     * ordinary mutations, preventing concurrent revision races.
     */
    if (
        currentState.generation &&
        owner
    ) {
        void queueStreamSnapshot(
            type,
        );

        return;
    }

    /*
     * A remote generation owns the mutation lock.
     */
    if (currentState.generation) {
        return;
    }

    const messageId =
        eventMessageId(
            args,
        );

    enqueueSnapshotMutationSoon(
        type,
        messageId === null
            ? {}
            : { messageId },
    );
}

async function onGenerationStarted() {
    if (
        !currentScope ||
        !currentState ||
        !getSettings().enabled
    ) {
        return;
    }

    /*
     * If a remote owner already exists, stop the local ST generation immediately.
     * The server remains the final race arbiter.
     */
    if (
        currentState.generation &&
        currentState.generation.ownerClientId !==
            currentClientId
    ) {
        localGenerationClaimLost =
            true;

        try {
            ctx?.stopGeneration?.();
        } catch {
            // ignored
        }

        setStatus(
            'Generation busy',
            'Remote client owns generation',
        );

        return;
    }

    const claimed =
        await claimGeneration();

    if (!claimed) {
        return;
    }

    await queueStreamSnapshot(
        'generation_started',
    );
}

function onStreamToken() {
    if (
        !currentState?.generation ||
        currentState.generation.ownerClientId !==
            currentClientId ||
        localGenerationClaimLost
    ) {
        return;
    }

    void queueStreamSnapshot(
        'token',
    );
}

async function onGenerationStopped() {
    if (!currentState?.generation) {
        return;
    }

    if (
        currentState.generation.ownerClientId !==
            currentClientId ||
        localGenerationClaimLost
    ) {
        return;
    }

    localStopIssued =
        true;

    clearTimeout(
        finalizeTimer,
    );

    finalizeTimer =
        null;

    await finishGeneration(
        'stopped',
    );
}

async function onGenerationEnded() {
    if (!currentState?.generation) {
        return;
    }

    if (
        currentState.generation.ownerClientId !==
            currentClientId ||
        localGenerationClaimLost
    ) {
        return;
    }

    clearTimeout(
        finalizeTimer,
    );

    finalizeTimer =
        setTimeout(
            async () => {
                finalizeTimer =
                    null;

                await finishGeneration(
                    localStopIssued
                        ? 'stopped'
                        : 'completed',
                );
            },
            FINALIZE_DELAY_MS,
        );
}

function onChatChanged() {
    void syncCurrentScope({
        force: true,
    });
}

async function onChatLifecycle(
    type,
) {
    /*
     * Event arguments differ across ST versions, so reconciliation is based on
     * the actual live context rather than trusting an event payload.
     */
    if (
        type === 'chat_deleted' ||
        type === 'group_chat_deleted'
    ) {
        const active =
            getScope();

        if (
            !active &&
            currentScope
        ) {
            setStatus(
                'Chat changed',
                'Active chat no longer exists',
            );

            closeSse();
            clearHeartbeat();

            return;
        }
    }

    await syncCurrentScope({
        force: true,
    });
}


/* -------------------------------------------------------------------------- */
/* Same-browser transport                                                      */
/* -------------------------------------------------------------------------- */

async function onRemoteBroadcast(
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
        currentClientId
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

    if (
        message.kind ===
            'generation_owner' ||
        message.kind ===
            'accepted' ||
        message.kind ===
            'generation_terminal'
    ) {
        if (message.state) {
            applyServerMeta(
                message.state,
            );
        }

        return;
    }

    if (
        message.kind ===
            'local_pending'
    ) {
        /*
         * A same-browser peer changed the scope. Let the server/SSE state remain
         * authoritative; a cheap state refresh catches the change even before
         * the SSE delivery reaches us.
         */
        if (
            message.type &&
            currentState
        ) {
            void resyncCurrentScope(
                'same-browser peer pending',
            );
        }
    }
}


/* -------------------------------------------------------------------------- */
/* Listener lifecycle                                                          */
/* -------------------------------------------------------------------------- */

function bindEvent(
    name,
    handler,
) {
    const source =
        ctx?.eventSource;

    if (
        !source ||
        !name
    ) {
        return;
    }

    source.on(
        name,
        handler,
    );

    listeners.push([
        name,
        handler,
    ]);
}

function bindEvents() {
    const eventTypes =
        ctx?.eventTypes ||
        ctx?.event_types;

    if (!eventTypes) {
        return;
    }

    bindEvent(
        eventTypes.MESSAGE_SENT,
        (...args) =>
            onMessageMutation(
                'message_sent',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_RECEIVED,
        (...args) =>
            onMessageMutation(
                'message_received',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_EDITED,
        (...args) =>
            onMessageMutation(
                'message_edited',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_DELETED,
        (...args) =>
            onMessageMutation(
                'message_deleted',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_UPDATED,
        (...args) =>
            onMessageMutation(
                'message_updated',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_SWIPED,
        (...args) =>
            onMessageMutation(
                'message_swiped',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_SWIPE_DELETED,
        (...args) =>
            onMessageMutation(
                'message_swipe_deleted',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_FILE_EMBEDDED,
        (...args) =>
            onMessageMutation(
                'message_file_embedded',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_REASONING_EDITED,
        (...args) =>
            onMessageMutation(
                'message_reasoning_edited',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MESSAGE_REASONING_DELETED,
        (...args) =>
            onMessageMutation(
                'message_reasoning_deleted',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.TOOL_CALLS_PERFORMED,
        (...args) =>
            onMessageMutation(
                'tool_calls_performed',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.MEDIA_ATTACHMENT_DELETED,
        (...args) =>
            onMessageMutation(
                'media_attachment_deleted',
                ...args,
            ),
    );

    bindEvent(
        eventTypes.CHAT_CHANGED,
        onChatChanged,
    );

    bindEvent(
        eventTypes.CHAT_CREATED,
        () =>
            void onChatLifecycle(
                'chat_created',
            ),
    );

    bindEvent(
        eventTypes.CHAT_DELETED,
        () =>
            void onChatLifecycle(
                'chat_deleted',
            ),
    );

    bindEvent(
        eventTypes.CHAT_RENAMED,
        () =>
            void onChatLifecycle(
                'chat_renamed',
            ),
    );

    bindEvent(
        eventTypes.GROUP_CHAT_CREATED,
        () =>
            void onChatLifecycle(
                'group_chat_created',
            ),
    );

    bindEvent(
        eventTypes.GROUP_CHAT_DELETED,
        () =>
            void onChatLifecycle(
                'group_chat_deleted',
            ),
    );

    bindEvent(
        eventTypes.GROUP_UPDATED,
        () =>
            void onChatLifecycle(
                'group_updated',
            ),
    );

    bindEvent(
        eventTypes.GENERATION_STARTED,
        onGenerationStarted,
    );

    /*
     * Current ST has STREAM_TOKEN_RECEIVED and a deprecated alias.
     * Bind only one if available.
     */
    bindEvent(
        eventTypes.STREAM_TOKEN_RECEIVED ||
            eventTypes.SMOOTH_STREAM_TOKEN_RECEIVED,
        onStreamToken,
    );

    /*
     * A message_received can be the final generated message after the stream.
     */
    bindEvent(
        eventTypes.GENERATION_STOPPED,
        onGenerationStopped,
    );

    bindEvent(
        eventTypes.GENERATION_ENDED,
        onGenerationEnded,
    );
}

function unbindEvents() {
    if (!ctx?.eventSource) {
        return;
    }

    for (const [
        name,
        handler,
    ] of listeners) {
        try {
            ctx.eventSource.removeListener(
                name,
                handler,
            );
        } catch {
            // ignored
        }
    }

    listeners = [];
}


/* -------------------------------------------------------------------------- */
/* Startup/shutdown                                                            */
/* -------------------------------------------------------------------------- */

function initBroadcastChannel() {
    try {
        broadcastChannel =
            new BroadcastChannel(
                CHANNEL_NAME,
            );

        broadcastChannel.addEventListener(
            'message',
            event =>
                void onRemoteBroadcast(
                    event.data,
                ),
        );
    } catch (error) {
        broadcastChannel = null;

        log(
            'BroadcastChannel unavailable; server-only transport',
            error,
        );
    }
}

async function start() {
    if (
        initialized &&
        !destroyed
    ) {
        if (!currentScope) {
            await syncCurrentScope({
                force: true,
            });
        }

        return;
    }

    ctx =
        safeGetContext();

    if (!ctx) {
        return;
    }

    destroyed =
        false;

    loadIdentity();

    getSettings();

    renderUi();

    setStatus(
        'Starting',
        'initializing sync',
    );

    initBroadcastChannel();
    bindEvents();

    initialized =
        true;

    await syncCurrentScope({
        force: true,
    });
}

async function stop() {
    destroyed =
        true;

    clearReconnectTimer();
    clearHeartbeat();
    closeSse();

    clearTimeout(
        localMutationTimer,
    );

    clearTimeout(
        finalizeTimer,
    );

    if (pendingStreamTimer) {
        clearTimeout(
            pendingStreamTimer,
        );
    }

    localMutationTimer = null;
    finalizeTimer = null;
    pendingStreamTimer = null;

    try {
        if (currentScope) {
            await api('/leave', {
                method: 'POST',

                body: JSON.stringify({
                    protocolVersion:
                        PROTOCOL_VERSION,

                    clientId:
                        currentClientId,

                    deviceId:
                        currentDeviceId,

                    scope:
                        currentScope,
                }),
            });
        }
    } catch {
        // best effort during teardown
    }

    unbindEvents();

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

    initialized =
        false;

    setStatus(
        'Disabled',
        'synchronization stopped',
    );
}


/* -------------------------------------------------------------------------- */
/* Lifecycle hooks                                                             */
/* -------------------------------------------------------------------------- */

export async function onInstall() {
    const c =
        safeGetContext();

    if (!c) {
        return;
    }

    ctx = c;

    const settingsRoot =
        c.extensionSettings || {};

    if (!settingsRoot[MODULE]) {
        settingsRoot[MODULE] =
            structuredClone(
                DEFAULTS,
            );

        c.saveSettingsDebounced?.();
    }
}

export async function onActivate() {
    await start();
}

export async function onEnable() {
    getSettings().enabled =
        true;

    await start();
}

export async function onDisable() {
    getSettings().enabled =
        false;

    ctx?.saveSettingsDebounced?.();

    await stop();
}

export async function onDelete() {
    await stop();
}

export async function onClean() {
    try {
        const db =
            await openDb();

        await new Promise(
            (resolve, reject) => {
                const tx =
                    db.transaction(
                        'kv',
                        'readwrite',
                    );

                tx.objectStore(
                    'kv',
                ).clear();

                tx.oncomplete =
                    resolve;

                tx.onerror =
                    () => reject(
                        tx.error,
                    );
            },
        );

        db.close();
    } catch (error) {
        log(
            'Clean extension data failed',
            error,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Compatibility bootstrap                                                     */
/* -------------------------------------------------------------------------- */

/*
 * Also works when the existing manifest does not yet declare lifecycle hooks.
 * If the manifest later maps activate/enable/disable/etc. to the exported
 * hooks above, initialization remains idempotent.
 */
void (async () => {
    try {
        const waitForApp = () => {
            const c =
                safeGetContext();

            if (!c) {
                return false;
            }

            const eventTypes =
                c.eventTypes ||
                c.event_types;

            if (
                eventTypes?.APP_READY
            ) {
                c.eventSource.once(
                    eventTypes.APP_READY,
                    () => void start(),
                );
            } else {
                void start();
            }

            return true;
        };

        if (!waitForApp()) {
            if (
                document.readyState ===
                    'loading'
            ) {
                document.addEventListener(
                    'DOMContentLoaded',
                    () => {
                        void waitForApp();
                    },
                    { once: true },
                );
            } else {
                setTimeout(
                    () => {
                        void waitForApp();
                    },
                    0,
                );
            }
        }
    } catch (error) {
        console.error(
            '[MultiClientSync] startup failed',
            error,
        );
    }
})();