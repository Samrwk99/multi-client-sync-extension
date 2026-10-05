const EXTENSION_ID = 'multi-client-sync';
const PLUGIN_BASE = '/api/plugins/multi-client-sync';
const PROTOCOL = 10;
const SCHEMA = 10;
const DB_NAME = 'multi-client-sync';
const DB_VERSION = 10;
const MAX_QUEUE = 1000;
const HEARTBEAT_MS = 10_000;
const GENERATION_HEARTBEAT_MS = 5_000;
const STREAM_SEND_MS = 60;
const REMOTE_RENDER_MS = 45;
const STORAGE_KEY = 'multi-client-sync-settings-v1';
const CLIENT_KEY = 'multi-client-sync-client-id-v1';
const DEVICE_KEY = 'multi-client-sync-device-id-v1';
const BC_NAME = 'multi-client-sync';

const DEFAULT_SETTINGS = {
    enabled: true,
    autoConnect: true,
    syncMessages: true,
    syncMetadata: true,
    coordinateGeneration: true,
    remoteStop: true,
    notifications: true,
    debug: false,
};

const forbiddenKeys = new Set(['__proto__', 'prototype', 'constructor']);
let settings = loadSettings();
let clientId = loadStableId(CLIENT_KEY);
let deviceId = loadStableId(DEVICE_KEY);
let ctx = null;
let eventSource = null;
let currentScope = null;
let scopeKeyValue = '';
let scopeEpoch = 0;
let serverState = null;
let baseSnapshot = null;
let applyingRemoteDepth = 0;
let localGeneration = null;
let streamTimer = null;
let remoteRenderTimer = null;
let lastStreamSentAt = 0;
let pendingStream = null;
let terminalizingGenerationId = null;
let scopeRetryTimer = null;
let sseEpoch = 0;
const registeredEventHandlers = [];
const registeredUiHandlers = [];
let heartbeatTimer = null;
let generationHeartbeatTimer = null;
let sendLockReason = '';
let settingsPanelMounted = false;
let bc = null;
let previousChatId = null;
let lastNativeChatRef = null;

function log(...args) { if (settings.debug) console.debug('[MCS]', ...args); }
function warn(...args) { console.warn('[MCS]', ...args); }
function clone(value) { return value === undefined ? undefined : JSON.parse(JSON.stringify(value)); }
function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }
function stableStringify(value) {
    return JSON.stringify(value, (key, val) => forbiddenKeys.has(key) ? undefined : val);
}
function deepEqual(a, b) { return stableStringify(a) === stableStringify(b); }
function loadStableId(key) {
    try {
        const saved = localStorage.getItem(key);
        if (saved && /^[A-Za-z0-9._~:-]{1,240}$/.test(saved)) return saved;
    } catch { /* ignore */ }
    const value = crypto.randomUUID();
    try { localStorage.setItem(key, value); } catch { /* ignore */ }
    return value;
}
function loadSettings() {
    try {
        return { ...DEFAULT_SETTINGS, ...JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}') };
    } catch {
        return { ...DEFAULT_SETTINGS };
    }
}
function saveSettings() {
    try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch { /* ignore */ }
}
function newId() { return crypto.randomUUID(); }

function safeObject(value) {
    if (!value || typeof value !== 'object' || Array.isArray(value)) return {};
    const out = {};
    for (const [key, val] of Object.entries(value)) {
        if (forbiddenKeys.has(key)) continue;
        if (Array.isArray(val)) out[key] = val.map(item => typeof item === 'object' && item !== null ? safeClone(item) : item);
        else if (val && typeof val === 'object') out[key] = safeClone(val);
        else out[key] = val;
    }
    return out;
}
function safeClone(value) {
    if (value == null || typeof value !== 'object') return value;
    if (Array.isArray(value)) return value.map(safeClone);
    const out = {};
    for (const [key, val] of Object.entries(value)) {
        if (forbiddenKeys.has(key)) continue;
        out[key] = safeClone(val);
    }
    return out;
}
function ensureMessageIds(messages) {
    let changed = false;
    const seen = new Set();
    for (const message of messages) {
        if (!message || typeof message !== 'object') continue;
        message.extra = message.extra && typeof message.extra === 'object' ? message.extra : {};
        message.extra.multi_client_sync = message.extra.multi_client_sync && typeof message.extra.multi_client_sync === 'object'
            ? message.extra.multi_client_sync : {};
        let id = message.extra.multi_client_sync.messageId;
        if (typeof id !== 'string' || !id || seen.has(id)) {
            id = newId();
            message.extra.multi_client_sync.messageId = id;
            changed = true;
        }
        seen.add(id);
    }
    return changed;
}
function messageId(message) { return message?.extra?.multi_client_sync?.messageId || null; }
function durableMessages() { return clone(ctx?.chat || []).map(message => message); }
function durableSnapshot() {
    const messages = durableMessages();
    ensureMessageIds(messages);
    const metadata = clone(ctx?.chatMetadata || {});
    return { messages, metadata };
}
function syncSnapshot(snapshot) {
    const normalized = normalizeSnapshot(snapshot);
    return {
        messages: settings.syncMessages ? clone(normalized.messages) : clone(durableMessages()),
        metadata: settings.syncMetadata ? clone(normalized.metadata) : clone(ctx?.chatMetadata || {}),
    };
}
function incomingSnapshot(snapshot) {
    const remote = normalizeSnapshot(snapshot);
    return {
        messages: settings.syncMessages ? clone(remote.messages) : clone(durableMessages()),
        metadata: settings.syncMetadata ? clone(remote.metadata) : clone(ctx?.chatMetadata || {}),
    };
}
function normalizeSnapshot(snapshot) {
    if (!snapshot || !Array.isArray(snapshot.messages)) return { messages: [], metadata: {} };
    const out = { messages: clone(snapshot.messages), metadata: clone(snapshot.metadata || {}) };
    ensureMessageIds(out.messages);
    return out;
}

function scopeFromContext() {
    if (!ctx) return null;
    const isGroup = ctx.groupId !== undefined && ctx.groupId !== null && String(ctx.groupId) !== '';
    const ownerId = isGroup ? String(ctx.groupId) : String(ctx.characters?.[ctx.characterId]?.avatar || '');
    const chatId = String(ctx.chatId || ctx.getCurrentChatId?.() || '');
    if (!ownerId || !chatId) return null;
    const meta = ctx.chatMetadata || {};
    const branchId = meta?.main_chat && meta?.integrity ? String(meta.integrity) : '';
    return { kind: isGroup ? 'group' : 'character', ownerId, chatId, branchId };
}
function encodeScope(scope) {
    return btoa(unescape(encodeURIComponent(JSON.stringify(scope))))
        .replace(/\+/g, '-')
        .replace(/\//g, '_')
        .replace(/=+$/g, '');
}
function makeScopeKey(scope) {
    return scope
        ? JSON.stringify([
            String(scope.kind || ''),
            String(scope.ownerId || ''),
            String(scope.chatId || ''),
            String(scope.branchId || ''),
        ])
        : '';
}

function openDb() {
    return new Promise((resolve, reject) => {
        const request = indexedDB.open(DB_NAME, DB_VERSION);
        request.onupgradeneeded = () => {
            const db = request.result;
            if (!db.objectStoreNames.contains('ops')) {
                const store = db.createObjectStore('ops', { keyPath: 'id' });
                store.createIndex('scopeKey', 'scopeKey', { unique: false });
            } else {
                const store = request.transaction.objectStore('ops');
                if (!store.indexNames.contains('scopeKey')) store.createIndex('scopeKey', 'scopeKey', { unique: false });
            }
        };
        request.onsuccess = () => resolve(request.result);
        request.onerror = () => reject(request.error);
    });
}
async function idbPut(value) {
    const db = await openDb();
    return new Promise((resolve, reject) => {
        const tx = db.transaction('ops', 'readwrite');
        tx.objectStore('ops').put(value);
        tx.oncomplete = () => { db.close(); resolve(); };
        tx.onerror = () => { db.close(); reject(tx.error); };
    });
}
async function idbList(scopeKey) {
    const db = await openDb();
    return new Promise((resolve, reject) => {
        const tx = db.transaction('ops', 'readonly');
        const req = tx.objectStore('ops').index('scopeKey').getAll(scopeKey);
        req.onsuccess = () => resolve(req.result.sort((a, b) => a.createdAt - b.createdAt));
        req.onerror = () => reject(req.error);
        tx.oncomplete = () => db.close();
    });
}
async function idbDelete(id) {
    const db = await openDb();
    return new Promise((resolve, reject) => {
        const tx = db.transaction('ops', 'readwrite');
        tx.objectStore('ops').delete(id);
        tx.oncomplete = () => { db.close(); resolve(); };
        tx.onerror = () => { db.close(); reject(tx.error); };
    });
}
async function idbClearScope(scopeKey) {
    const rows = await idbList(scopeKey);
    for (const row of rows) await idbDelete(row.id);
}

async function api(path, method = 'GET', body = undefined, query = '') {
    const headers = { ...(ctx?.getRequestHeaders?.() || { 'Content-Type': 'application/json' }) };
    if (method !== 'GET') headers['Content-Type'] = 'application/json';
    const response = await fetch(`${PLUGIN_BASE}${path}${query}`, {
        method,
        headers,
        body: body === undefined ? undefined : JSON.stringify(body),
        credentials: 'same-origin',
    });
    let payload = null;
    try { payload = await response.json(); } catch { /* no json */ }
    if (!response.ok) {
        const err = new Error(payload?.error || `HTTP ${response.status}`);
        err.status = response.status;
        err.payload = payload;
        throw err;
    }
    return payload;
}
function currentScopeGuard(epoch) { return epoch === scopeEpoch && scopeKeyValue === makeScopeKey(currentScope); }

function statusText(text, notify = false) {
    const el = document.getElementById('mcs_status');
    if (el) el.textContent = text;
    if (notify && settings.notifications && typeof toastr !== 'undefined') toastr.info(text, 'Multi-Client Sync');
}
function renderBanner(text) {
    let el = document.getElementById('mcs_remote_generation_banner');
    if (!text) { el?.remove(); document.body.classList.remove('mcs-remote-streaming'); return; }
    if (!el) {
        el = document.createElement('div');
        el.id = 'mcs_remote_generation_banner';
        document.body.appendChild(el);
    }
    el.textContent = text;
    document.body.classList.add('mcs-remote-streaming');
}
function setSendLock(reason = '') {
    sendLockReason = reason;
    const active = !!reason;
    const remote = isRemoteGenerationActive();
    const selectors = ['#send_but', '#option_regenerate', '#regenerate_last_message', '#swipe_right', '#swipe_left'];
    for (const selector of selectors) {
        const el = document.querySelector(selector);
        if (!el) continue;
        const lockThisControl = active && (selector !== '#send_but' || remote);
        if (lockThisControl) {
            el.dataset.mcsLocked = '1';
            el.title = reason;
            el.classList.add('disabled');
        } else if (el.dataset.mcsLocked === '1') {
            delete el.dataset.mcsLocked;
            el.removeAttribute('title');
            el.classList.remove('disabled');
        }
    }
}
function isRemoteGenerationActive() {
    const g = serverState?.generation;
    return !!g && (!localGeneration || g.generationId !== localGeneration.generationId);
}

function mergeMetadata(base, local, remote) {
    if (deepEqual(local, base)) return clone(remote);
    if (deepEqual(remote, base)) return clone(local);
    if (deepEqual(local, remote)) return clone(local);

    if (
        Array.isArray(local) ||
        Array.isArray(remote) ||
        Array.isArray(base)
    ) {
        // Deterministic conflict resolution: the newer server-side value wins.
        return clone(remote);
    }

    const out = {};
    const keys = new Set([
        ...Object.keys(base || {}),
        ...Object.keys(local || {}),
        ...Object.keys(remote || {}),
    ]);

    for (const key of keys) {
        if (forbiddenKeys.has(key)) continue;

        const b = base?.[key];
        const l = local?.[key];
        const r = remote?.[key];

        if (deepEqual(l, b)) {
            out[key] = clone(r);
        } else if (deepEqual(r, b)) {
            out[key] = clone(l);
        } else if (
            l && r &&
            typeof l === 'object' &&
            typeof r === 'object'
        ) {
            out[key] = mergeMetadata(
                b,
                l,
                r,
            );
        } else {
            out[key] = clone(r);
        }
    }

    return out;
}
function mergeSnapshots(base, local, remote) {
    const b = normalizeSnapshot(base);
    const l = normalizeSnapshot(local);
    const r = normalizeSnapshot(remote);
    const bm = new Map(b.messages.map(m => [messageId(m), m]));
    const lm = new Map(l.messages.map(m => [messageId(m), m]));
    const rm = new Map(r.messages.map(m => [messageId(m), m]));
    const ids = new Set([...bm.keys(), ...lm.keys(), ...rm.keys()].filter(Boolean));
    const merged = [];
    for (const id of ids) {
        const bv = bm.get(id), lv = lm.get(id), rv = rm.get(id);
        let chosen;
        if (!lv && bv && deepEqual(rv, bv)) chosen = null;
        else if (!rv && bv && deepEqual(lv, bv)) chosen = null;
        else if (deepEqual(lv, bv)) chosen = rv;
        else if (deepEqual(rv, bv)) chosen = lv;
        else if (deepEqual(lv, rv)) chosen = lv;
        else if (!lv && !rv) chosen = null;
        else if (!lv) chosen = rv;
        else if (!rv) chosen = lv;
        else chosen = rv;
        if (chosen) merged.push(clone(chosen));
    }
    const rank = new Map();
    let n = 0;
    for (const arr of [r.messages, l.messages, b.messages]) {
        for (const m of arr) {
            const id = messageId(m);
            if (id && !rank.has(id)) rank.set(id, n++);
        }
    }
    merged.sort((a, z) => (rank.get(messageId(a)) ?? 1e9) - (rank.get(messageId(z)) ?? 1e9));
    return { messages: merged, metadata: mergeMetadata(b.metadata, l.metadata, r.metadata) };
}

async function applySnapshot(snapshot, { save = true, render = true } = {}) {
    const normalized = normalizeSnapshot(snapshot);
    applyingRemoteDepth += 1;
    try {
        if (!ctx) return;
        if (Array.isArray(ctx.chat)) {
            ctx.chat.splice(0, ctx.chat.length, ...clone(normalized.messages));
        }
        if (ctx.chatMetadata && typeof ctx.chatMetadata === 'object') {
            for (const key of Object.keys(ctx.chatMetadata)) delete ctx.chatMetadata[key];
            Object.assign(ctx.chatMetadata, clone(normalized.metadata));
        }
        if (render) {
            try {
                ctx.printMessages?.();
            } catch (error) {
                log('printMessages failed', error);
            }
        }
        if (save) await ctx.saveChat?.();
    } finally {
        applyingRemoteDepth -= 1;
    }
}

async function ensureIdsPersisted() {
    if (!ctx?.chat) return;
    const changed = ensureMessageIds(ctx.chat);
    if (changed) await ctx.saveChat?.();
}

async function enqueueSnapshot(snapshot, baseRev, baseSnap) {
    if (!settings.syncMessages) return;
    const row = {
        id: newId(),
        scopeKey: scopeKeyValue,
        createdAt: Date.now(),
        kind: 'snapshot',
        baseRevision: Number(baseRev || 0),
        baseSnapshot: clone(baseSnap || baseSnapshot || { messages: [], metadata: {} }),
        snapshot: clone(snapshot),
    };
    await idbPut(row);
    const rows = await idbList(scopeKeyValue);
    if (rows.length > MAX_QUEUE) {
        for (const old of rows.slice(0, rows.length - MAX_QUEUE)) await idbDelete(old.id);
    }
}
async function sendSnapshotDirect(snapshot, baseRev, opId) {
    return api('/snapshot', 'POST', {
        scope: currentScope,
        clientId,
        deviceId,
        opId,
        baseRevision: baseRev,
        snapshot,
    });
}
async function publishLocalSnapshot(snapshot = durableSnapshot()) {
    if (!currentScope || !settings.enabled || !settings.syncMessages) return false;
    const opId = newId();
    const base = clone(baseSnapshot || { messages: [], metadata: {} });
    const revision = Number(serverState?.revision || 0);
    try {
        const result = await sendSnapshotDirect(snapshot, revision, opId);
        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        broadcastWake('state');
        return true;
    } catch (error) {
        if (error?.status === 409 && error?.payload?.state) {
            const remoteState = error.payload.state;
            const merged = mergeSnapshots(base, snapshot, remoteState.snapshot);
            serverState = remoteState;
            baseSnapshot = clone(remoteState.snapshot);
            await applySnapshot(merged, { save: true, render: true });
            const retryBase = Number(remoteState.revision);
            try {
                const result = await sendSnapshotDirect(merged, retryBase, newId());
                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
                broadcastWake('state');
                return true;
            } catch (retryError) {
                if (retryError?.status === 409 && retryError?.payload?.state) {
                    await enqueueSnapshot(merged, retryError.payload.state.revision, retryError.payload.state.snapshot);
                } else {
                    await enqueueSnapshot(merged, retryBase, remoteState.snapshot);
                }
                return false;
            }
        }
        await enqueueSnapshot(snapshot, revision, base);
        return false;
    }
}

async function flushQueue() {
    if (!currentScope || !settings.enabled || !settings.syncMessages) return;

    const rows = await idbList(scopeKeyValue);

    for (const row of rows) {
        if (!currentScope) return;

        try {
            let nextSnapshot = clone(row.snapshot);
            let nextBase = clone(
                row.baseSnapshot ||
                baseSnapshot ||
                { messages: [], metadata: {} },
            );
            let nextRevision = Number(
                row.baseRevision || 0
            );

            const remote = serverState?.snapshot
                ? clone(serverState.snapshot)
                : null;

            const remoteRevision = Number(
                serverState?.revision ||
                nextRevision
            );

            if (
                remote &&
                remoteRevision !== nextRevision
            ) {
                nextSnapshot = mergeSnapshots(
                    nextBase,
                    nextSnapshot,
                    remote,
                );
                nextBase = clone(remote);
                nextRevision = remoteRevision;

                row.snapshot = clone(nextSnapshot);
                row.baseSnapshot = clone(nextBase);
                row.baseRevision = nextRevision;
                await idbPut(row);
            }

            const result = await sendSnapshotDirect(
                nextSnapshot,
                nextRevision,
                row.id,
            );

            serverState = result.state;
            baseSnapshot = clone(
                result.state.snapshot
            );

            await idbDelete(row.id);
        } catch (error) {
            if (
                error?.status === 409 &&
                error?.payload?.state
            ) {
                const remote = error.payload.state;

                if (
                    error.payload.error ===
                    'generation_active'
                ) {
                    serverState = remote;
                    baseSnapshot = clone(
                        remote.snapshot
                    );
                    break;
                }

                const merged = mergeSnapshots(
                    row.baseSnapshot,
                    row.snapshot,
                    remote.snapshot,
                );

                serverState = remote;
                baseSnapshot = clone(
                    remote.snapshot
                );

                row.snapshot = clone(merged);
                row.baseSnapshot = clone(
                    remote.snapshot
                );
                row.baseRevision = Number(
                    remote.revision
                );

                await applySnapshot(
                    incomingSnapshot(merged),
                    {
                        save: true,
                        render: true,
                    },
                );

                await idbPut(row);
                continue;
            }

            break;
        }
    }
}

function broadcastWake(kind) {
    try { bc?.postMessage({ kind, scopeKey: scopeKeyValue, at: Date.now() }); } catch { /* ignore */ }
}

async function openScope(epoch) {
    if (!settings.enabled || !settings.autoConnect || !currentScope) return;

    const localSnapshot = syncSnapshot(durableSnapshot());

    try {
        const result = await api('/join', 'POST', {
            scope: currentScope,
            clientId,
            deviceId,
            snapshot: localSnapshot,
        });

        if (!currentScopeGuard(epoch)) return;

        if (scopeRetryTimer) {
            clearTimeout(scopeRetryTimer);
            scopeRetryTimer = null;
        }

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);

        const incoming = incomingSnapshot(result.state.snapshot);
        const queued = await idbList(scopeKeyValue);

        if (queued.length) {
            await flushQueue();
        } else if (!deepEqual(localSnapshot, incoming)) {
            await applySnapshot(incoming, { save: true, render: true });
        }

        connectSse(epoch);
        startHeartbeats(epoch);

        if (result.state.generation?.message && result.state.generation?.clientId !== clientId) {
            pendingStream = {
                message: clone(result.state.generation.message),
                messageIndex: Number.isInteger(result.state.generation.messageIndex) ? result.state.generation.messageIndex : null,
                generationId: result.state.generation.generationId,
            };
            scheduleRemoteRender();
        }

        await flushQueue();
        updateGenerationUi();
        statusText(`Connected · rev ${serverState.revision}`);
    } catch (error) {
        warn('join failed', error);
        statusText(`Offline: ${error?.message || 'connection failed'}`);

        if (!currentScopeGuard(epoch) || scopeRetryTimer) return;

        scopeRetryTimer = setTimeout(() => {
            scopeRetryTimer = null;
            if (currentScopeGuard(epoch)) {
                openScope(epoch).catch(retryError => warn('scope retry failed', retryError));
            }
        }, 2000);
    }
}

function disconnectSse() {
    ++sseEpoch;
    if (eventSource) {
        try { eventSource.close(); } catch { /* ignore */ }
        eventSource = null;
    }
}
function stopHeartbeats() {
    if (heartbeatTimer) clearInterval(heartbeatTimer);
    heartbeatTimer = null;
    if (generationHeartbeatTimer) clearInterval(generationHeartbeatTimer);
    generationHeartbeatTimer = null;
}
function connectSse(epoch) {
    disconnectSse();
    if (!currentScope || !currentScopeGuard(epoch)) return;

    const localSseEpoch = sseEpoch;
    const query = `?scope=${encodeURIComponent(encodeScope(currentScope))}&clientId=${encodeURIComponent(clientId)}&deviceId=${encodeURIComponent(deviceId)}`;
    const source = new EventSource(`${PLUGIN_BASE}/events${query}`, { withCredentials: true });
    eventSource = source;

    const handle = (type, fn) => {
        source.addEventListener(type, event => {
            if (!currentScopeGuard(epoch) || localSseEpoch !== sseEpoch) return;
            try {
                fn(JSON.parse(event.data));
            } catch (error) {
                warn('bad SSE payload', type, error);
            }
        });
    };

    handle('hello', handleServerHello);
    handle('replay_complete', data => statusText(`Connected · rev ${data.revision}`));
    handle('resync_required', () => resyncCurrentScope(epoch));
    handle('snapshot', handleSnapshotEvent);
    handle('generation_claimed', handleGenerationEvent);
    handle('generation_started', handleGenerationEvent);
    handle('generation_stream', handleGenerationStreamEvent);
    handle('generation_stop_requested', handleRemoteStopEvent);
    handle('generation_terminal', handleGenerationTerminalEvent);
    handle('generation_recovered', handleGenerationRecovered);

    source.onerror = () => {
        if (!currentScopeGuard(epoch) || localSseEpoch !== sseEpoch) return;
        statusText('Reconnecting…');
        // EventSource performs automatic retries. Membership heartbeat recovers
        // cases where the browser slept long enough to expire membership.
    };
}
function handleServerHello(data) {
    if (data.protocol !== PROTOCOL || data.schema !== SCHEMA) {
        statusText(`Protocol mismatch (${data.protocol}/${data.schema})`);
        return;
    }

    const generation = clone(data.generation || null);
    const previousGenerationId = serverState?.generation?.generationId || null;

    serverState = {
        ...(serverState || {}),
        revision: Number(data.revision),
        generation,
        scope: clone(data.scope),
    };

    if (
        localGeneration &&
        previousGenerationId &&
        (!generation || generation.generationId !== previousGenerationId)
    ) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        localGeneration = null;
        stopGenerationHeartbeat();
    }

    if (generation?.message && generation.clientId !== clientId) {
        pendingStream = {
            message: clone(generation.message),
            messageIndex: Number.isInteger(generation.messageIndex) ? generation.messageIndex : null,
            generationId: generation.generationId,
        };
        scheduleRemoteRender();
    }

    updateGenerationUi();
}
function handleSnapshotEvent(data) {
    if (Number(data.revision) <= Number(serverState?.revision || 0)) return;

    serverState = {
        ...(serverState || {}),
        revision: Number(data.revision),
        snapshot: clone(data.snapshot),
    };
    baseSnapshot = clone(data.snapshot);

    if (data.sourceClientId === clientId) {
        updateGenerationUi();
        return;
    }

    const snapshot = incomingSnapshot(data.snapshot);
    applySnapshot(snapshot, { save: true, render: true })
        .catch(error => warn('remote snapshot apply failed', error));

    broadcastWake('state');
    updateGenerationUi();
}
function handleGenerationEvent(data) {
    serverState = { ...(serverState || {}), generation: clone(data.generation) };
    updateGenerationUi();
}
async function handleGenerationRecovered() {
    serverState = { ...(serverState || {}), generation: null };

    if (localGeneration) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        localGeneration = null;
        stopGenerationHeartbeat();
    }

    renderBanner('Generation was lost; chat was unlocked.');
    setTimeout(() => renderBanner(''), 1800);
    updateGenerationUi();
    await resyncCurrentScope(scopeEpoch);
}
function handleGenerationStreamEvent(data) {
    const g = data?.generation;
    if (!g) return;

    serverState = { ...(serverState || {}), generation: clone(g) };

    if (
        (g.clientId === clientId && g.deviceId === deviceId) ||
        !data.message
    ) {
        updateGenerationUi();
        return;
    }

    pendingStream = {
        message: clone(data.message),
        messageIndex: Number.isInteger(data.messageIndex) ? data.messageIndex : null,
        generationId: g.generationId,
    };

    scheduleRemoteRender();
    updateGenerationUi();
}
function scheduleRemoteRender() {
    if (remoteRenderTimer) return;

    remoteRenderTimer = setTimeout(() => {
        remoteRenderTimer = null;
        const item = pendingStream;
        pendingStream = null;

        if (!item || !ctx?.chat) return;

        const g = serverState?.generation;
        if (!g || g.generationId !== item.generationId || (g.clientId === clientId && g.deviceId === deviceId)) return;

        applyingRemoteDepth += 1;
        try {
            const id = messageId(item.message);
            if (!id) return;

            const index = ctx.chat.findIndex(message => messageId(message) === id);

            if (index < 0) {
                if (Number.isInteger(item.messageIndex) && item.messageIndex >= 0 && item.messageIndex <= ctx.chat.length) {
                    if (item.messageIndex === ctx.chat.length) ctx.chat.push(clone(item.message));
                    else ctx.chat[item.messageIndex] = clone(item.message);
                } else {
                    ctx.chat.push(clone(item.message));
                }

                try { ctx.printMessages?.(); } catch { /* ignore */ }
                return;
            }

            ctx.chat[index] = clone(item.message);

            try {
                ctx.updateMessageBlock?.(id, clone(item.message), { rerenderMessage: true });
            } catch {
                try { ctx.printMessages?.(); } catch { /* ignore */ }
            }
        } finally {
            applyingRemoteDepth -= 1;
        }
    }, REMOTE_RENDER_MS);
}
async function handleGenerationTerminalEvent(data) {
    serverState = {
        ...(serverState || {}),
        revision: Number(data.revision),
        snapshot: clone(data.snapshot),
        generation: null,
    };

    baseSnapshot = clone(data.snapshot);

    const mine =
        data.generation?.clientId === clientId &&
        data.generation?.deviceId === deviceId;

    if (mine) {
        localGeneration = null;
        stopGenerationHeartbeat();
        sendLockReason = '';
    } else {
        await applySnapshot(
            incomingSnapshot(data.snapshot),
            {
                save: true,
                render: true,
            },
        );

        renderBanner(
            'Generation finished in another client.'
        );

        setTimeout(
            () => renderBanner(''),
            1500,
        );
    }

    pendingStream = null;
    updateGenerationUi();
    await flushQueue();
}

function updateGenerationUi() {
    const g = serverState?.generation;
    if (!g) {
        setSendLock('');
        renderBanner('');
        return;
    }
    const mine = localGeneration && g.generationId === localGeneration.generationId;
    if (mine) {
        setSendLock('You are generating in this shared chat.');
        renderBanner('Generating here · shared with other clients');
    } else {
        setSendLock('Another client is generating this shared chat.');
        renderBanner('Another client is generating this shared chat · live mirror');
    }
}
function stopGenerationHeartbeat() {
    if (generationHeartbeatTimer) clearInterval(generationHeartbeatTimer);
    generationHeartbeatTimer = null;
}
function startHeartbeats(epoch) {
    stopHeartbeats();

    heartbeatTimer = setInterval(async () => {
        if (!currentScopeGuard(epoch) || !serverState) return;

        try {
            const oldRevision = Number(serverState.revision || 0);
            const oldGenerationId = serverState.generation?.generationId || null;

            const result = await api('/heartbeat', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
            });

            if (!currentScopeGuard(epoch)) return;
            if (!Number.isInteger(Number(result.revision))) return;

            const newRevision = Number(result.revision);
            const newGenerationId = result.generation?.generationId || null;

            serverState = {
                ...serverState,
                revision: newRevision,
                generation: clone(result.generation || null),
            };

            if (oldRevision !== newRevision || oldGenerationId !== newGenerationId) {
                await resyncCurrentScope(epoch);
            }

            updateGenerationUi();
        } catch (error) {
            if (error?.status === 403 && currentScopeGuard(epoch)) {
                await openScope(epoch);
                return;
            }
            log('membership heartbeat failed', error);
        }
    }, HEARTBEAT_MS);
}
function startGenerationHeartbeat(epoch) {
    stopGenerationHeartbeat();

    generationHeartbeatTimer = setInterval(async () => {
        if (!currentScopeGuard(epoch) || !localGeneration) return;

        try {
            const result = await api('/generation/heartbeat', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
                generationId: localGeneration.generationId,
            });

            if (!currentScopeGuard(epoch)) return;

            serverState = result.state;

            if (result.stopRequested || result.state?.generation?.stopRequested) {
                try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            }

            const current = result.state?.generation;
            if (!current || current.generationId !== localGeneration.generationId) {
                try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                localGeneration = null;
                stopGenerationHeartbeat();
                await resyncCurrentScope(epoch);
                return;
            }

            updateGenerationUi();
        } catch (error) {
            warn('generation heartbeat failed', error);
            try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            localGeneration = null;
            stopGenerationHeartbeat();
            await resyncCurrentScope(epoch);
        }
    }, GENERATION_HEARTBEAT_MS);
}

async function resyncCurrentScope(epoch = scopeEpoch) {
    if (!currentScope || !currentScopeGuard(epoch)) return;

    try {
        const result = await api('/state', 'POST', {
            scope: currentScope,
            clientId,
            deviceId,
        });

        if (!currentScopeGuard(epoch)) return;

        const local = durableSnapshot();
        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);

        const queued = await idbList(scopeKeyValue);
        if (queued.length) {
            await flushQueue();
        } else {
            const incoming = incomingSnapshot(result.state.snapshot);
            if (!deepEqual(local, incoming)) {
                await applySnapshot(incoming, { save: true, render: true });
            }
        }

        if (result.state.generation?.message && result.state.generation?.clientId !== clientId) {
            pendingStream = {
                message: clone(result.state.generation.message),
                messageIndex: Number.isInteger(result.state.generation.messageIndex) ? result.state.generation.messageIndex : null,
                generationId: result.state.generation.generationId,
            };
            scheduleRemoteRender();
        }

        updateGenerationUi();
    } catch (error) {
        warn('resync failed', error);
    }
}

async function leaveCurrentScope() {
    if (!currentScope) return;

    const leavingScope = clone(currentScope);

    if (localGeneration) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        try { await sendGenerationTerminal('stopped'); } catch (error) { warn('generation cleanup failed while leaving scope', error); }
    }

    try {
        await api('/leave', 'POST', {
            scope: leavingScope,
            clientId,
            deviceId,
        });
    } catch { /* ignore */ }

    disconnectSse();
    stopHeartbeats();
    stopGenerationHeartbeat();

    if (scopeRetryTimer) {
        clearTimeout(scopeRetryTimer);
        scopeRetryTimer = null;
    }

    serverState = null;
    baseSnapshot = null;
    localGeneration = null;
    pendingStream = null;

    if (streamTimer) clearTimeout(streamTimer);
    streamTimer = null;

    if (remoteRenderTimer) clearTimeout(remoteRenderTimer);
    remoteRenderTimer = null;

    setSendLock('');
    renderBanner('');
}
async function switchScope(reason = 'scope-change') {
    const nextScope = scopeFromContext();
    const nextKey = makeScopeKey(nextScope);
    if (nextKey === scopeKeyValue) return;
    ++scopeEpoch;
    const epoch = scopeEpoch;
    await leaveCurrentScope();
    currentScope = nextScope;
    scopeKeyValue = nextKey;
    previousChatId = ctx?.chatId || null;
    if (!nextScope) {
        statusText('No active chat');
        return;
    }
    log('switch scope', reason, nextScope);
    await ensureIdsPersisted();
    if (settings.enabled && settings.autoConnect) await openScope(epoch);
}

async function coordinatedGenerateInterceptor(chat, contextSize, abort, type) {
    if (!settings.enabled || !settings.coordinateGeneration || applyingRemoteDepth > 0 || !currentScope) return;

    const g = serverState?.generation;
    if (g && !localGeneration) {
        abort(false);
        if (settings.notifications) {
            statusText('Another client is already generating this shared chat.', true);
        }
        updateGenerationUi();
        return;
    }

    if (localGeneration) return;

    await ensureIdsPersisted();

    let desiredSnapshot = syncSnapshot(durableSnapshot());
    let claimBase = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });
    let revision = Number(serverState?.revision || 0);
    let claimResult = null;

    for (let attempt = 0; attempt < 3; attempt += 1) {
        try {
            claimResult = await api('/generation/claim', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
                opId: newId(),
                generationId: newId(),
                generationType: String(type || 'normal'),
                baseRevision: revision,
                snapshot: desiredSnapshot,
            });
            break;
        } catch (error) {
            const payload = error?.payload;

            if (error?.status === 409 && payload?.state) {
                if (payload.error === 'generation_active') {
                    serverState = payload.state;
                    baseSnapshot = clone(payload.state.snapshot);
                    abort(false);
                    updateGenerationUi();
                    return;
                }

                const merged = mergeSnapshots(claimBase, desiredSnapshot, payload.state.snapshot);
                serverState = payload.state;
                baseSnapshot = clone(payload.state.snapshot);
                await applySnapshot(merged, { save: true, render: true });

                desiredSnapshot = syncSnapshot(durableSnapshot());
                claimBase = clone(payload.state.snapshot);
                revision = Number(payload.state.revision);
                continue;
            }

            throw error;
        }
    }

    if (!claimResult) {
        abort(false);
        return;
    }

    serverState = claimResult.state;
    baseSnapshot = clone(claimResult.state.snapshot);
    localGeneration = clone(claimResult.state.generation);
    startGenerationHeartbeat(scopeEpoch);
    updateGenerationUi();
}

async function onGenerationStarted() {
    if (!localGeneration || !currentScope) return;
    try {
        const result = await api('/generation/started', 'POST', {
            scope: currentScope, clientId, deviceId, generationId: localGeneration.generationId,
        });
        serverState = result.state;
        localGeneration = clone(result.state.generation);
        updateGenerationUi();
    } catch (error) {
        warn('generation_started failed', error);
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
    }
}
function scheduleGenerationStream() {
    if (streamTimer || !pendingStream || !localGeneration || !currentScope) return;
    const delay = Math.max(0, STREAM_SEND_MS - (Date.now() - lastStreamSentAt));
    streamTimer = setTimeout(async () => {
        streamTimer = null;
        const payload = pendingStream;
        pendingStream = null;
        if (!payload || !localGeneration) return;
        try {
            const result = await api('/generation/stream', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
                generationId: localGeneration.generationId,
                seq: payload.seq,
                message: payload.message,
                messageIndex: payload.messageIndex,
            });
            lastStreamSentAt = Date.now();
            serverState = result.state;
            localGeneration = clone(result.state.generation);
            updateGenerationUi();
        } catch (error) {
            warn('generation stream failed', error);
            try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            localGeneration = null;
            stopGenerationHeartbeat();
            await resyncCurrentScope();
        }
        if (pendingStream) scheduleGenerationStream();
    }, delay);
}
function captureLocalStream() {
    if (!localGeneration || !ctx?.chat?.length) return;
    const messages = ctx.chat;
    let index = -1;
    for (let i = messages.length - 1; i >= 0; i -= 1) {
        if (!messages[i]?.is_user && !messages[i]?.is_system) { index = i; break; }
    }
    if (index < 0) return;
    ensureMessageIds(messages);
    const message = clone(messages[index]);
    pendingStream = {
        seq: (Number(localGeneration.seq || 0) + 1),
        message,
        messageIndex: index,
    };
    scheduleGenerationStream();
}

async function sendGenerationTerminal(phase = 'completed') {
    if (!localGeneration || !currentScope) return;
    if (terminalizingGenerationId === localGeneration.generationId) return;

    terminalizingGenerationId = localGeneration.generationId;
    const g = clone(localGeneration);
    let succeeded = false;

    try {
        const snapshot = syncSnapshot(durableSnapshot());
        let lastError = null;

        for (let attempt = 0; attempt < 3; attempt += 1) {
            try {
                const result = await api('/generation/terminal', 'POST', {
                    scope: currentScope,
                    clientId,
                    deviceId,
                    generationId: g.generationId,
                    phase,
                    snapshot,
                });

                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
                succeeded = true;
                break;
            } catch (error) {
                lastError = error;
                if (error?.status === 409 && error?.payload?.state) {
                    serverState = error.payload.state;
                    baseSnapshot = clone(error.payload.state.snapshot);
                    break;
                }
                if (attempt < 2) await sleep(250 * (attempt + 1));
            }
        }

        if (!succeeded && lastError) {
            warn('generation terminal failed', lastError);
            await enqueueSnapshot(
                snapshot,
                Number(serverState?.revision || 0),
                baseSnapshot,
            );
        }
    } finally {
        localGeneration = null;
        stopGenerationHeartbeat();
        if (streamTimer) clearTimeout(streamTimer);
        streamTimer = null;
        pendingStream = null;
        terminalizingGenerationId = null;
        updateGenerationUi();
    }

    if (!succeeded) await resyncCurrentScope(scopeEpoch);
}
async function handleRemoteStopEvent(data) {
    const g = data?.generation;
    if (!g || !localGeneration || g.generationId !== localGeneration.generationId) return;
    try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
}

function onStreamToken() {
    if (!localGeneration) return;
    captureLocalStream();
}
function onReasoningDone() {
    if (!localGeneration) return;
    captureLocalStream();
}
function onToolEvent() {
    if (!localGeneration) return;
    captureLocalStream();
}

async function onGenerationEnded() { if (localGeneration) await sendGenerationTerminal('completed'); }
async function onGenerationStopped() { if (localGeneration) await sendGenerationTerminal('stopped'); }

async function publishAfterLocalEvent() {
    if (applyingRemoteDepth > 0 || !currentScope || !settings.enabled || !settings.syncMessages) return;
    if (localGeneration && ['claimed', 'started', 'streaming'].includes(localGeneration.phase)) return;
    try {
        await publishLocalSnapshot(syncSnapshot(durableSnapshot()));
    } catch (error) {
        warn('publish after local event failed', error);
    }
}

function unwireEvents() {
    const es = ctx?.eventSource;
    if (!es) {
        registeredEventHandlers.length = 0;
        return;
    }

    for (const [eventType, handler] of registeredEventHandlers) {
        try {
            if (typeof es.removeListener === 'function') es.removeListener(eventType, handler);
            else if (typeof es.off === 'function') es.off(eventType, handler);
        } catch { /* ignore */ }
    }

    registeredEventHandlers.length = 0;
}

function wireEvents() {
    unwireEvents();

    const types = ctx.eventTypes;
    const es = ctx.eventSource;
    const listen = (eventType, fn) => {
        if (!eventType || !es?.on) return;
        es.on(eventType, fn);
        registeredEventHandlers.push([eventType, fn]);
    };

    listen(types.CHAT_CHANGED, () => switchScope('CHAT_CHANGED'));
    listen(types.CHAT_LOADED, () => switchScope('CHAT_LOADED'));
    listen(types.MESSAGE_SENT, publishAfterLocalEvent);
    listen(types.MESSAGE_RECEIVED, publishAfterLocalEvent);
    listen(types.MESSAGE_EDITED, publishAfterLocalEvent);
    listen(types.MESSAGE_UPDATED, publishAfterLocalEvent);
    listen(types.MESSAGE_DELETED, publishAfterLocalEvent);
    listen(types.MESSAGE_SWIPED, publishAfterLocalEvent);
    listen(types.MESSAGE_SWIPE_DELETED, publishAfterLocalEvent);
    listen(types.MESSAGE_REASONING_EDITED, publishAfterLocalEvent);
    listen(types.MESSAGE_REASONING_DELETED, publishAfterLocalEvent);
    listen(types.MORE_MESSAGES_LOADED, publishAfterLocalEvent);
    listen(types.GENERATION_STARTED, onGenerationStarted);
    listen(types.STREAM_TOKEN_RECEIVED, onStreamToken);
    listen(types.STREAM_REASONING_DONE, onReasoningDone);
    listen(types.TOOL_CALLS_PERFORMED, onToolEvent);
    listen(types.TOOL_CALLS_RENDERED, onToolEvent);
    listen(types.GENERATION_ENDED, onGenerationEnded);
    listen(types.GENERATION_STOPPED, onGenerationStopped);
    listen(types.GROUP_MEMBER_DRAFTED, onStreamToken);
    listen(types.GROUP_WRAPPER_STARTED, onGenerationStarted);
    listen(types.GROUP_WRAPPER_FINISHED, onGenerationEnded);
}

function unwireUiGuards() {
    for (const [type, handler, capture] of registeredUiHandlers) {
        try { document.removeEventListener(type, handler, capture); } catch { /* ignore */ }
    }
    registeredUiHandlers.length = 0;
}

function wireUiGuards() {
    unwireUiGuards();

    const clickHandler = async event => {
        const target = event.target instanceof Element
            ? event.target.closest('button, .menu_button, [role="button"]')
            : null;

        if (!target || !isRemoteGenerationActive()) return;

        if (target.matches('#send_but, #option_regenerate, #regenerate_last_message, #swipe_left, #swipe_right')) {
            event.preventDefault();
            event.stopImmediatePropagation();

            if (target.matches('#send_but') && settings.remoteStop && serverState?.generation) {
                try { await requestRemoteStop(); } catch (error) { warn('remote stop failed', error); }
            }
        }
    };

    const keydownHandler = async event => {
        if (!isRemoteGenerationActive()) return;
        if (event.key !== 'Enter' || event.shiftKey || event.isComposing) return;

        const target = event.target;
        if (!(target instanceof HTMLTextAreaElement || target instanceof HTMLInputElement)) return;
        if (!settings.remoteStop) return;

        event.preventDefault();
        event.stopImmediatePropagation();

        try { await requestRemoteStop(); } catch (error) { warn('remote stop failed', error); }
    };

    document.addEventListener('click', clickHandler, true);
    document.addEventListener('keydown', keydownHandler, true);

    registeredUiHandlers.push(
        ['click', clickHandler, true],
        ['keydown', keydownHandler, true],
    );
}
async function requestRemoteStop() {
    const g = serverState?.generation;
    if (!g || !currentScope) return;
    if (localGeneration) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        return;
    }
    if (!settings.remoteStop) return;
    await api('/generation/stop', 'POST', { scope: currentScope, clientId, deviceId });
}

async function onActivate() {
    ctx = SillyTavern.getContext();

    unwireEvents();
    unwireUiGuards();

    bc?.close?.();
    bc = 'BroadcastChannel' in window ? new BroadcastChannel(BC_NAME) : null;

    bc?.addEventListener('message', message => {
        if (message.data?.scopeKey !== scopeKeyValue) return;
        if (message.data?.kind === 'state' && currentScope) resyncCurrentScope();
    });

    wireEvents();
    wireUiGuards();
    await mountSettings();

    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;
    await switchScope('activate');
}

async function onEnable() {
    settings.enabled = true;
    settings.autoConnect = true;
    saveSettings();

    ++scopeEpoch;
    wireEvents();
    wireUiGuards();
    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

    currentScope = scopeFromContext();
    scopeKeyValue = makeScopeKey(currentScope);

    if (currentScope) await openScope(scopeEpoch);
    updateGenerationUi();
}
async function onDisable() {
    settings.enabled = false;
    saveSettings();
    ++scopeEpoch;

    unwireUiGuards();
    unwireEvents();
    delete globalThis.multiClientSyncGenerateInterceptor;

    await leaveCurrentScope();

    currentScope = null;
    scopeKeyValue = '';

    try { bc?.close?.(); } catch { /* ignore */ }
    bc = null;
}

async function mountSettings() {
    if (settingsPanelMounted) return;
    const host = document.querySelector('#extensions_settings') || document.querySelector('#extensions_settings2');
    if (!host) {
        setTimeout(mountSettings, 1000);
        return;
    }
    settingsPanelMounted = true;
    try {
        const html = await ctx.renderExtensionTemplateAsync?.('third-party/multi-client-sync', 'settings');
        if (html) host.insertAdjacentHTML('beforeend', html);
    } catch {
        host.insertAdjacentHTML('beforeend', '<div id="mcs_settings_panel"><b>Multi-Client Sync</b><div id="mcs_status">Offline</div><button id="mcs_reconnect" class="menu_button">Reconnect</button></div>');
    }
    const map = {
        mcs_enabled: 'enabled',
        mcs_auto_connect: 'autoConnect',
        mcs_sync_messages: 'syncMessages',
        mcs_sync_metadata: 'syncMetadata',
        mcs_coordinate_generation: 'coordinateGeneration',
        mcs_remote_stop: 'remoteStop',
        mcs_notifications: 'notifications',
        mcs_debug: 'debug',
    };
    for (const [id, key] of Object.entries(map)) {
        const el = document.getElementById(id);
        if (!el) continue;
        el.checked = !!settings[key];
        el.addEventListener('change', async () => {
            settings[key] = !!el.checked;
            saveSettings();

            if (key === 'enabled') {
                if (settings.enabled) await onEnable();
                else await onDisable();
                return;
            }

            if (settings.enabled && settings.autoConnect) {
                await switchScope(`setting:${key}`);
            }

            updateGenerationUi();
        });
    }
    document.getElementById('mcs_reconnect')?.addEventListener('click', () => switchScope('manual-reconnect'));
    document.getElementById('mcs_resync')?.addEventListener('click', () => resyncCurrentScope());
    updateGenerationUi();
}

export { onActivate, onEnable, onDisable };
globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;