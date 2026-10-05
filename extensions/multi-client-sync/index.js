const EXTENSION_ID = 'multi-client-sync';
const PLUGIN_BASE = '/api/plugins/multi-client-sync';
const PROTOCOL = 9;
const SCHEMA = 9;
const DB_NAME = 'multi-client-sync';
const DB_VERSION = 9;
const DEVICE_STORAGE_KEY = `${EXTENSION_ID}:device-id`;
const OFFLINE_PRINCIPAL_STORAGE_KEY = `${EXTENSION_ID}:offline-principal`;
const OFFLINE_PRINCIPAL_BINDING_STORAGE_KEY = `${EXTENSION_ID}:offline-principal-binding`;
const MAX_QUEUE = 1_000;
const SNAPSHOT_CAPTURE_DELAY = 100;
const STREAM_CAPTURE_INTERVAL = 200;
const REMOTE_APPLY_TIMEOUT = 15_000;
const STREAM_RENDER_INTERVAL = 150;
const GENERATION_INPUT_MAX_RETRIES = 3;

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
let serverInstanceId = null;
let currentScope = null;
let currentState = null;
let scopeEpoch = 0;
let sse = null;
let sseReconnectTimer = null;
let reconnectAttempt = 0;
let sseEventChain = Promise.resolve();
let heartbeatTimer = null;
let generationHeartbeatTimer = null;
let localGeneration = null;
let localGenerationLost = false;
let generationStartedAcknowledged = false;
let groupGenerationActive = false;
let groupGenerationStatus = 'completed';
let finishingGeneration = false;
let applyingRemoteDepth = 0;
let hostMessageIdsDirty = false;
let captureTimer = null;
let captureScheduled = false;
let streamTimer = null;
let streamFlushPromise = Promise.resolve();
let pendingStreamMessage = null;
let streamMessageFingerprints = new Map();
let sseHelloEventId = 0;
const flushingQueueKeys = new Set();
const enqueueMutationChains = new Map();
let uiRoot = null;
let listenerBindings = [];
let browserBindings = [];
let broadcastChannel = null;
let dbPromise = null;
let lastError = '';
let generationHeartbeatFailures = 0;
let generationFinishRetryTimer = null;
let deferredCaptureReason = null;
let streamRenderTimer = null;
let streamRenderPending = false;
let generationInputOpId = null;
let scopeTransitionChain = Promise.resolve();

function getContext() { return SillyTavern.getContext(); }
function log(...args) { if (settings?.debug) console.debug(`[${EXTENSION_ID}]`, ...args); }
function warn(...args) { console.warn(`[${EXTENSION_ID}]`, ...args); }
function toast(type, message) { if (!settings?.notifications) return; try { toastr[type]?.(message, 'Multi-Client Sync'); } catch {} }
function clone(value) { return value === undefined ? undefined : structuredClone(value); }
function now() { return Date.now(); }
function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }
function randomId(prefix = '') {
    if (globalThis.crypto?.randomUUID) return prefix + globalThis.crypto.randomUUID().replaceAll('-', '');
    return prefix + Date.now().toString(36) + Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
}

async function sha256(value) {
    const data = new TextEncoder().encode(String(value));
    if (!globalThis.crypto?.subtle) return null;
    const hash = await globalThis.crypto.subtle.digest('SHA-256', data);
    return [...new Uint8Array(hash)].map(byte => byte.toString(16).padStart(2, '0')).join('');
}

function canonicalize(value, seen = new WeakSet()) {
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return value;
    if (typeof value === 'number') {
        if (!Number.isFinite(value)) throw new Error('Non-finite number is not JSON-compatible');
        return value;
    }
    if (typeof value !== 'object') throw new Error('Unsupported non-JSON value');
    if (seen.has(value)) throw new Error('Cyclic value is not JSON-compatible');
    seen.add(value);
    try {
        if (Array.isArray(value)) return value.map(item => canonicalize(item, seen));
        const out = {};
        for (const key of Object.keys(value).sort()) {
            if (forbiddenKeys.has(key)) throw new Error(`Forbidden object key: ${key}`);
            out[key] = canonicalize(value[key], seen);
        }
        return out;
    } finally {
        seen.delete(value);
    }
}
function canonicalJson(value) { return JSON.stringify(canonicalize(value)); }

function sameScope(a, b) {
    return !!a && !!b && scopeKey(a) === scopeKey(b);
}
function scopeKey(scope) {
    if (!scope) return '';
    return canonicalJson([scope.kind, scope.kind === 'character' ? scope.character : scope.groupId, scope.chatId]);
}
function scopeIsCurrent(expectedEpoch, expectedScope) {
    return expectedEpoch === scopeEpoch && currentScope && (!expectedScope || sameScope(expectedScope, currentScope));
}
function isObject(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }

const forbiddenKeys = new Set(['__proto__', 'prototype', 'constructor']);
function validateDataTree(value, depth = 0, seen = new WeakSet()) {
    if (depth > 40) return false;
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return true;
    if (typeof value === 'number') return Number.isFinite(value);
    if (typeof value !== 'object' || seen.has(value)) return false;
    seen.add(value);
    if (Array.isArray(value)) return value.every(child => validateDataTree(child, depth + 1, seen));
    for (const [key, child] of Object.entries(value)) {
        if (forbiddenKeys.has(key) || !validateDataTree(child, depth + 1, seen)) return false;
    }
    return true;
}

function stableMessageId(message) {
    const id = message?.extra?.multi_client_sync?.messageId;
    return typeof id === 'string' && id.length > 0 ? id : null;
}
function ensureMessageIds(snapshot) {
    const out = clone(Array.isArray(snapshot) ? snapshot : []);
    const used = new Set();
    for (const message of out) {
        if (!isObject(message)) continue;
        if (!isObject(message.extra)) message.extra = {};
        if (!isObject(message.extra.multi_client_sync)) message.extra.multi_client_sync = {};
        let id = stableMessageId(message);
        if (!id || id.length > 128 || /[\\/\u0000-\u001f]/.test(id) || used.has(id)) {
            id = randomId('m_');
            message.extra.multi_client_sync.messageId = id;
        }
        used.add(id);
    }
    return out;
}
function normalizeSnapshot(snapshot) {
    const out = ensureMessageIds(snapshot);
    if (!validateDataTree(out)) throw new Error('Chat contains unsupported data.');
    return out;
}

const UNSYNCED_MESSAGE_FIELDS = Object.freeze(['swipes', 'swipe_info', 'swipe_id']);
const UNSYNCED_EXTRA_FIELDS = Object.freeze([
    'reasoning',
    'reasoning_duration',
    'reasoning_signature',
    'reasoning_display_text',
    'tool_invocations',
]);

function stripSyncMetadataForMatching(message) {
    const out = clone(message || {});
    if (isObject(out.extra)) delete out.extra.multi_client_sync;
    return out;
}

function referenceKey(message) {
    const out = stripSyncMetadataForMatching(message);
    if (!settings?.syncSwipes) {
        for (const key of UNSYNCED_MESSAGE_FIELDS) delete out[key];
        if (isObject(out.extra)) for (const key of UNSYNCED_EXTRA_FIELDS) delete out.extra[key];
    }
    return canonicalJson(out);
}

function alignMessageIdsToReference(referenceSnapshot) {
    if (!Array.isArray(ctx?.chat) || !Array.isArray(referenceSnapshot) || !referenceSnapshot.length) return false;
    const reference = normalizeSnapshot(referenceSnapshot);
    let changed = false;
    const positionLimit = Math.min(ctx.chat.length, reference.length);

    for (let index = 0; index < positionLimit; index++) {
        const local = ctx.chat[index];
        const remote = reference[index];
        const remoteId = stableMessageId(remote);
        if (!isObject(local) || !isObject(remote) || stableMessageId(local) || !remoteId) continue;
        if (referenceKey(local) !== referenceKey(remote)) continue;
        if (!isObject(local.extra)) local.extra = {};
        if (!isObject(local.extra.multi_client_sync)) local.extra.multi_client_sync = {};
        local.extra.multi_client_sync.messageId = remoteId;
        changed = true;
    }

    const buckets = new Map();
    for (const remote of reference) {
        const id = stableMessageId(remote);
        if (!id) continue;
        const key = referenceKey(remote);
        const bucket = buckets.get(key) || [];
        bucket.push(id);
        buckets.set(key, bucket);
    }
    const usedIds = new Set(
        ctx.chat.map(stableMessageId).filter(Boolean),
    );
    for (const local of ctx.chat) {
        if (!isObject(local) || stableMessageId(local)) continue;
        const bucket = buckets.get(referenceKey(local));
        while (bucket?.length && usedIds.has(bucket[0])) bucket.shift();
        const id = bucket?.shift();
        if (!id || usedIds.has(id)) continue;
        if (!isObject(local.extra)) local.extra = {};
        if (!isObject(local.extra.multi_client_sync)) local.extra.multi_client_sync = {};
        local.extra.multi_client_sync.messageId = id;
        usedIds.add(id);
        changed = true;
    }
    if (changed) hostMessageIdsDirty = true;
    return changed;
}

function findMessageById(snapshot, id) {
    return Array.isArray(snapshot) ? snapshot.find(message => stableMessageId(message) === id) || null : null;
}

function mergeDisabledFields(remoteMessage, localMessage) {
    const remote = clone(remoteMessage || {});
    if (!isObject(remote) || settings?.syncSwipes) return remote;
    const local = isObject(localMessage) ? localMessage : null;
    for (const key of UNSYNCED_MESSAGE_FIELDS) {
        if (local && Object.prototype.hasOwnProperty.call(local, key)) remote[key] = clone(local[key]);
        else delete remote[key];
    }
    if (!isObject(remote.extra)) remote.extra = {};
    for (const key of UNSYNCED_EXTRA_FIELDS) {
        if (local?.extra && Object.prototype.hasOwnProperty.call(local.extra, key)) remote.extra[key] = clone(local.extra[key]);
        else delete remote.extra[key];
    }
    return remote;
}

function applySyncProjection(snapshot, baseSnapshot = []) {
    const normalized = normalizeSnapshot(snapshot);
    if (settings?.syncSwipes) return normalized;
    const baseMap = new Map((Array.isArray(baseSnapshot) ? baseSnapshot : []).map(message => [stableMessageId(message), message]));
    return normalized.map(message => mergeDisabledFields(message, baseMap.get(stableMessageId(message))));
}

function generationSnapshotEntries(generation) {
    if (!generation) return [];
    if (Array.isArray(generation.streamMessages)) return generation.streamMessages.filter(entry => entry?.messageId && entry?.message);
    if (generation.streamMessage && generation.messageId) return [{ messageId: generation.messageId, message: generation.streamMessage }];
    return [];
}

function mergeGenerationProgress(current, incoming) {
    if (!incoming) return null;
    if (!current || current.id !== incoming.id) return clone(incoming);

    const currentSeq = Number(current.streamSeq || 0);
    const incomingSeq = Number(incoming.streamSeq || 0);
    const newer = incomingSeq >= currentSeq ? incoming : current;
    const older = incomingSeq >= currentSeq ? current : incoming;
    const merged = {
        ...clone(older),
        ...clone(newer),
        streamSeq: Math.max(currentSeq, incomingSeq),
        leaseUntil: Math.max(Number(current.leaseUntil || 0), Number(incoming.leaseUntil || 0)),
        startedAt: Math.min(Number(current.startedAt || now()), Number(incoming.startedAt || now())),
        stopRequested: !!(current.stopRequested || incoming.stopRequested),
    };

    const phases = ['claimed', 'started', 'streaming', 'completed', 'stopped', 'failed'];
    const currentRank = phases.indexOf(String(current.phase));
    const incomingRank = phases.indexOf(String(incoming.phase));
    merged.phase = currentRank >= incomingRank ? current.phase : incoming.phase;

    const byId = new Map();
    for (const entry of generationSnapshotEntries(newer)) byId.set(entry.messageId, clone(entry));
    for (const entry of generationSnapshotEntries(older)) if (!byId.has(entry.messageId)) byId.set(entry.messageId, clone(entry));
    merged.streamMessages = [...byId.values()];
    if (!merged.messageId) merged.messageId = current.messageId || incoming.messageId || null;
    if (merged.streamMessages.length) {
        const latest = merged.streamMessages.at(-1);
        merged.streamMessage = clone(latest.message);
    }
    return merged;
}

function durableLocalSnapshot() {
    const local = localSnapshot();
    const generation = currentState?.generation;
    if (!generation || !currentGenerationIsRemote()) return applySyncProjection(local, currentState?.snapshot || []);
    const base = applySyncProjection(currentState?.snapshot || []);
    const baseMap = new Map(base.map(message => [stableMessageId(message), message]));
    const overlayMap = new Map(generationSnapshotEntries(generation).map(entry => [entry.messageId, entry.message]));
    const result = [];
    for (const message of local) {
        const id = stableMessageId(message);
        const preview = overlayMap.get(id);
        if (preview && messageEqual(message, preview)) {
            if (baseMap.has(id)) result.push(clone(baseMap.get(id)));
            continue;
        }
        result.push(clone(message));
    }
    return applySyncProjection(result, base);
}
function ensureHostMessageIds() {
    if (!Array.isArray(ctx?.chat)) return false;
    const used = new Set();
    let changed = false;
    for (const message of ctx.chat) {
        if (!isObject(message)) continue;
        if (!isObject(message.extra)) { message.extra = {}; changed = true; }
        if (!isObject(message.extra.multi_client_sync)) { message.extra.multi_client_sync = {}; changed = true; }
        let id = stableMessageId(message);
        if (!id || id.length > 128 || /[\\/\u0000-\u001f]/.test(id) || used.has(id)) {
            id = randomId('m_');
            changed = true;
        }
        if (message.extra.multi_client_sync.messageId !== id) changed = true;
        message.extra.multi_client_sync.messageId = id;
        used.add(id);
    }
    if (changed) hostMessageIdsDirty = true;
    return changed;
}
function localSnapshot() { ensureHostMessageIds(); return normalizeSnapshot(ctx?.chat || []); }
function localMetadata() { return isObject(ctx?.chatMetadata) ? clone(ctx.chatMetadata) : {}; }
function projectSnapshotForDigest(snapshot, mode = 'full') {
    const out = normalizeSnapshot(snapshot || []);
    if (mode !== 'relevant' || settings?.syncSwipes) return out;
    for (const message of out) {
        if (isObject(message.extra)) delete message.extra.multi_client_sync;
        for (const key of UNSYNCED_MESSAGE_FIELDS) delete message[key];
        if (isObject(message.extra)) for (const key of UNSYNCED_EXTRA_FIELDS) delete message.extra[key];
    }
    return out;
}
async function snapshotDigest(snapshot, mode = 'full') { return sha256(canonicalJson(projectSnapshotForDigest(snapshot, mode))); }
function snapshotEquivalent(a, b) {
    return canonicalJson(projectSnapshotForDigest(a || [], settings?.syncSwipes ? 'full' : 'relevant'))
        === canonicalJson(projectSnapshotForDigest(b || [], settings?.syncSwipes ? 'full' : 'relevant'));
}

function settingsRef() {
    ctx = getContext();
    if (!isObject(ctx.extensionSettings[EXTENSION_ID])) ctx.extensionSettings[EXTENSION_ID] = clone(defaultSettings);
    const target = ctx.extensionSettings[EXTENSION_ID];
    for (const [key, value] of Object.entries(defaultSettings)) if (!(key in target)) target[key] = clone(value);
    settings = target;
    return target;
}
function deviceIdentifier() {
    try {
        const existing = localStorage.getItem(DEVICE_STORAGE_KEY);
        if (existing) return existing;
        const value = randomId('d_');
        localStorage.setItem(DEVICE_STORAGE_KEY, value);
        return value;
    } catch { return randomId('d_'); }
}
const deviceId = deviceIdentifier();
// Deliberately fresh per page. sessionStorage may be cloned by duplicated browser tabs.
const clientId = randomId('c_');
let offlinePrincipalMemo = null;
function offlinePrincipalKey() {
    if (offlinePrincipalMemo) return offlinePrincipalMemo;
    try {
        const existing = localStorage.getItem(OFFLINE_PRINCIPAL_STORAGE_KEY);
        if (existing && /^[a-zA-Z0-9_-]{8,128}$/.test(existing)) {
            offlinePrincipalMemo = `offline:${existing}`;
            return offlinePrincipalMemo;
        }
        const value = randomId('o_');
        localStorage.setItem(OFFLINE_PRINCIPAL_STORAGE_KEY, value);
        offlinePrincipalMemo = `offline:${value}`;
        return offlinePrincipalMemo;
    } catch {
        offlinePrincipalMemo = `offline:${deviceId}`;
        return offlinePrincipalMemo;
    }
}
function offlinePrincipalBinding() {
    try { return localStorage.getItem(OFFLINE_PRINCIPAL_BINDING_STORAGE_KEY) || ''; } catch { return ''; }
}
function setOfflinePrincipalBinding(userId) {
    try { localStorage.setItem(OFFLINE_PRINCIPAL_BINDING_STORAGE_KEY, String(userId)); } catch {}
}
function authenticatedPrincipalKey(userId = serverUserId) {
    return userId ? `user:${encodeURIComponent(String(userId))}` : '';
}
function principalKey() { return serverUserId ? authenticatedPrincipalKey(serverUserId) : offlinePrincipalKey(); }

function getCurrentScope() {
    ctx = getContext();
    if (ctx.groupId !== undefined && ctx.groupId !== null && String(ctx.groupId)) {
        const group = ctx.groups?.find(item => String(item.id) === String(ctx.groupId));
        const chatId = ctx.getCurrentChatId?.() || ctx.chatId || group?.chat_id;
        if (!chatId) return null;
        return {
            kind: 'group',
            groupId: String(ctx.groupId),
            chatId: String(chatId),
            branchId: ctx.chatMetadata?.main_chat && ctx.chatMetadata?.integrity ? String(ctx.chatMetadata.integrity) : '',
            parentChatId: ctx.chatMetadata?.main_chat ? String(ctx.chatMetadata.main_chat) : '',
        };
    }
    if (ctx.characterId === undefined || ctx.characterId === null || String(ctx.characterId) === '') return null;
    const character = ctx.characters?.[ctx.characterId];
    const avatar = character?.avatar;
    const chatId = ctx.getCurrentChatId?.() || ctx.chatId || character?.chat;
    if (!avatar || !chatId) return null;
    return {
        kind: 'character',
        character: String(avatar),
        chatId: String(chatId),
        branchId: ctx.chatMetadata?.main_chat && ctx.chatMetadata?.integrity ? String(ctx.chatMetadata.integrity) : '',
        parentChatId: ctx.chatMetadata?.main_chat ? String(ctx.chatMetadata.main_chat) : '',
    };
}

async function api(route, options = {}) {
    ctx = getContext();
    const headers = { Accept: 'application/json', ...(ctx.getRequestHeaders?.() || {}), ...(options.headers || {}) };
    if (options.body !== undefined) headers['Content-Type'] = 'application/json';
    const response = await fetch(`${PLUGIN_BASE}${route}`, { credentials: 'same-origin', cache: 'no-store', ...options, headers });
    const text = await response.text();
    let data = null;
    if (text) {
        try { data = JSON.parse(text); } catch { data = { ok: false, error: { code: 'invalid_json', message: text.slice(0, 500) } }; }
    }
    if (!response.ok) {
        const error = new Error(data?.error?.message || `HTTP ${response.status}`);
        error.status = response.status;
        error.code = data?.error?.code || `http_${response.status}`;
        error.data = data;
        throw error;
    }
    return data;
}
function eventBody(type, extra = {}, scope = currentScope) {
    return { protocol: PROTOCOL, schema: SCHEMA, type, clientId, deviceId, scope: clone(scope), ...extra };
}

function currentGenerationIsRemote() {
    const generation = currentState?.generation;
    return !!generation && !!generation.ownerClientId && (generation.ownerClientId !== clientId || generation.ownerDeviceId !== deviceId);
}
function generationActive() { return !!currentState?.generation; }
function updateSendLock() {
    const remote = settings?.enabled && settings?.coordinateGeneration && currentGenerationIsRemote();
    const button = document.querySelector('#send_but');
    if (button instanceof HTMLButtonElement) {
        button.disabled = remote;
        button.title = remote ? 'Another synchronized client is generating in this chat.' : '';
    }
    document.body?.classList.toggle('mcs-remote-generation', !!remote);
}

function setStatus(state, text) {
    if (!uiRoot) return;
    const dot = uiRoot.querySelector('.mcs-status');
    const label = uiRoot.querySelector('.mcs-state-text');
    dot?.classList.remove('mcs-connected', 'mcs-disconnected', 'mcs-disabled', 'mcs-owner', 'mcs-streaming', 'mcs-warning', 'mcs-follower');
    dot?.classList.add({ owner: 'mcs-owner', streaming: 'mcs-streaming', follower: 'mcs-follower', warning: 'mcs-warning', disabled: 'mcs-disabled', connected: 'mcs-connected' }[state] || 'mcs-disconnected');
    if (label) label.textContent = text || state;
}
function updateInfo() {
    if (!uiRoot) return;
    const info = uiRoot.querySelector('[data-mcs-info]');
    if (!info) return;
    const scope = currentScope ? `${currentScope.kind}:${currentScope.chatId}` : 'none';
    const generation = currentState?.generation;
    const generationText = generation
        ? (generation.ownerClientId === clientId && generation.ownerDeviceId === deviceId ? `generation ${generation.phase} · this tab` : `generation ${generation.phase} · another tab`)
        : 'idle';
    info.textContent = `Scope: ${scope} · revision ${Number(currentState?.revision || 0)} · ${generationText} · server ${String(serverInstanceId || 'unknown').slice(0, 12)}${lastError ? ` · ${lastError}` : ''}`;
}
function updateUi() {
    if (!settings?.enabled) { setStatus('disabled', 'disabled'); updateInfo(); updateSendLock(); return; }
    if (!serverAvailable) { setStatus('warning', 'server plugin required'); updateInfo(); updateSendLock(); return; }
    if (!serverCompatible) { setStatus('warning', 'plugin incompatible'); updateInfo(); updateSendLock(); return; }
    const generation = currentState?.generation;
    if (generation) {
        const mine = generation.ownerClientId === clientId && generation.ownerDeviceId === deviceId;
        const state = generation.phase === 'streaming' ? 'streaming' : mine ? 'owner' : 'follower';
        const text = mine ? generation.phase : (generation.phase === 'streaming' ? 'streaming on another client' : 'waiting for response');
        setStatus(state, text);
    } else setStatus('connected', 'synchronized');
    updateInfo();
    updateSendLock();
}

function renderUi() {
    if (uiRoot?.isConnected) return;
    const host = document.querySelector('#extensions_settings2') || document.querySelector('#extensions_settings');
    if (!host) return;
    const root = document.createElement('div');
    root.className = 'mcs-settings';
    root.innerHTML = `
        <h3>Multi-Client Sync</h3>
        <div class="mcs-status-row"><span class="mcs-status" title="Multi-client sync status"></span><span class="mcs-state-text">starting</span></div>
        <div class="mcs-info" data-mcs-info></div>
        <label class="checkbox_label"><input type="checkbox" data-mcs="enabled"> Enable synchronization</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="autoConnect"> Connect automatically</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="syncMessages"> Sync messages</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="syncMetadata"> Sync chat metadata</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="syncSwipes"> Sync swipes/reasoning/tools</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="syncGroupSettings"> Sync group settings</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="syncBranches"> Sync branches/checkpoints</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="coordinateGeneration"> Coordinate generation</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="remoteStop"> Allow remote generation stop</label>
        <label class="checkbox_label"><input type="checkbox" data-mcs="notifications"> Notifications</label>
        <div class="mcs-actions">
            <button type="button" class="menu_button" data-mcs-action="reconnect">Reconnect</button>
            <button type="button" class="menu_button" data-mcs-action="resync">Resync</button>
            <button type="button" class="menu_button" data-mcs-action="branch">Create branch</button>
            <button type="button" class="menu_button" data-mcs-action="checkpoint">Create checkpoint</button>
            <button type="button" class="menu_button" data-mcs-action="stop-remote">Stop remote generation</button>
        </div>`;
    host.append(root);
    uiRoot = root;

    for (const input of root.querySelectorAll('input[data-mcs]')) {
        const key = input.getAttribute('data-mcs');
        input.checked = !!settings?.[key];
        input.addEventListener('change', async () => {
            settings[key] = input.checked;
            await ctx.saveSettingsDebounced?.();
            if (key === 'enabled') { if (input.checked) await onEnable(); else await onDisable(); return; }
            if (key === 'autoConnect' && input.checked) await reconnectCurrentScope();
            updateUi();
        });
    }
    root.querySelector('[data-mcs-action="reconnect"]')?.addEventListener('click', () => void reconnectCurrentScope());
    root.querySelector('[data-mcs-action="resync"]')?.addEventListener('click', () => void resyncCurrentScope());
    root.querySelector('[data-mcs-action="branch"]')?.addEventListener('click', () => void createNativeBranch());
    root.querySelector('[data-mcs-action="checkpoint"]')?.addEventListener('click', () => void createNativeCheckpoint());
    root.querySelector('[data-mcs-action="stop-remote"]')?.addEventListener('click', () => void requestRemoteGenerationStop());
    updateUi();
}

async function checkHealth() {
    try {
        const result = await api('/health');
        serverAvailable = !!result.ok;
        serverInstanceId = result.serverInstanceId || serverInstanceId;
        serverCompatible = serverAvailable && Number(result.protocol) === PROTOCOL && Number(result.schema) === SCHEMA;
        let offlinePrincipalConflict = false;
        let offlinePrincipalMigrationFailed = false;
        if (result.userId) {
            const nextUserId = String(result.userId);
            const boundUserId = offlinePrincipalBinding();
            serverUserId = nextUserId;
            if (serverCompatible) {
                if (!boundUserId || boundUserId === nextUserId) {
                    const migrated = await migrateOfflinePrincipalToUser(nextUserId);
                    if (migrated) setOfflinePrincipalBinding(nextUserId);
                    else offlinePrincipalMigrationFailed = true;
                } else {
                    // There is no reliable way to attribute a cold-start offline queue
                    // to a different ST account. Discarding it is safer than ever sending
                    // one user's unsynced chat data into another user's account.
                    try { await clearPrincipalData(offlinePrincipalKey()); } catch (error) { warn('could not quarantine previous offline queue', error); }
                    setOfflinePrincipalBinding(nextUserId);
                    offlinePrincipalConflict = true;
                }
            }
        }
        if (!serverCompatible) lastError = 'Server plugin version is incompatible.';
        else if (offlinePrincipalConflict) lastError = 'Offline changes are retained locally because they belong to a different SillyTavern user.';
        else if (offlinePrincipalMigrationFailed) lastError = 'Offline synchronization data could not be attached to this SillyTavern user yet.';
        else lastError = '';
        return serverCompatible;
    } catch (error) {
        serverAvailable = false;
        serverCompatible = false;
        lastError = error.message;
        return false;
    }
}

/* -------------------------------------------------------------------------- */
/* IndexedDB                                                                  */
/* -------------------------------------------------------------------------- */
function openDb() {
    if (dbPromise) return dbPromise;
    dbPromise = new Promise((resolve, reject) => {
        const request = indexedDB.open(DB_NAME, DB_VERSION);
        request.onupgradeneeded = () => {
            const db = request.result;
            const tx = request.transaction;
            const ops = db.objectStoreNames.contains('ops') ? tx.objectStore('ops') : db.createObjectStore('ops', { keyPath: 'key' });
            if (!ops.indexNames.contains('principalScope')) ops.createIndex('principalScope', 'principalScope', { unique: false });
            if (!ops.indexNames.contains('createdAt')) ops.createIndex('createdAt', 'createdAt', { unique: false });
            if (!ops.indexNames.contains('scope')) ops.createIndex('scope', 'scope', { unique: false });
            const meta = db.objectStoreNames.contains('meta') ? tx.objectStore('meta') : db.createObjectStore('meta', { keyPath: 'key' });
            if (!meta.indexNames.contains('principal')) meta.createIndex('principal', 'principal', { unique: false });
        };
        request.onsuccess = () => resolve(request.result);
        request.onerror = () => reject(request.error);
    });
    return dbPromise;
}
function idb(storeName, mode, callback) {
    return openDb().then(db => new Promise((resolve, reject) => {
        const tx = db.transaction(storeName, mode);
        const store = tx.objectStore(storeName);
        let result;
        try { result = callback(store, tx); } catch (error) { reject(error); return; }
        tx.oncomplete = () => resolve(result);
        tx.onerror = () => reject(tx.error);
        tx.onabort = () => reject(tx.error || new Error('IndexedDB transaction aborted.'));
    }));
}
async function migratePrincipalNamespace(fromPrincipal, toPrincipal) {
    if (!fromPrincipal || !toPrincipal || fromPrincipal === toPrincipal) return true;
    let changed = false;
    try {
        await idb('ops', 'readwrite', store => new Promise((resolve, reject) => {
            const range = IDBKeyRange.bound(`${fromPrincipal}|`, `${fromPrincipal}|\uffff`);
            const request = store.index('principalScope').openCursor(range);
            request.onsuccess = () => {
                const cursor = request.result;
                if (!cursor) { resolve(); return; }
                const value = cursor.value;
                const scope = String(value.scope || '');
                const opId = String(value.opId || '');
                if (!scope || !opId) { cursor.delete(); cursor.continue(); return; }
                store.put({ ...value, key: `${toPrincipal}|${scope}|${opId}`, principalScope: `${toPrincipal}|${scope}` });
                cursor.delete();
                changed = true;
                cursor.continue();
            };
            request.onerror = () => reject(request.error);
        }));
        await idb('meta', 'readwrite', store => new Promise((resolve, reject) => {
            const request = store.index('principal').openCursor(IDBKeyRange.only(fromPrincipal));
            request.onsuccess = () => {
                const cursor = request.result;
                if (!cursor) { resolve(); return; }
                const value = cursor.value;
                const scope = String(value.scope || '');
                if (!scope) { cursor.delete(); cursor.continue(); return; }
                const targetKey = `${toPrincipal}|${scope}`;
                const targetRequest = store.get(targetKey);
                targetRequest.onerror = () => reject(targetRequest.error);
                targetRequest.onsuccess = () => {
                    const existing = targetRequest.result || null;
                    const migrated = existing ? {
                        ...existing,
                        principal: toPrincipal,
                        key: targetKey,
                        scope,
                        localSequence: Math.max(Number(existing.localSequence || 0), Number(value.localSequence || 0)),
                        lastEventId: Math.max(Number(existing.lastEventId || 0), Number(value.lastEventId || 0)),
                        revision: Math.max(Number(existing.revision || 0), Number(value.revision || 0)),
                        ...(Number(value.revision || 0) > Number(existing.revision || 0) ? { epoch: value.epoch || existing.epoch || '', baseSnapshot: clone(value.baseSnapshot || existing.baseSnapshot || []), baseMetadata: clone(value.baseMetadata || existing.baseMetadata || {}) } : {}),
                        updatedAt: Math.max(Number(existing.updatedAt || 0), Number(value.updatedAt || 0)),
                    } : { ...value, key: targetKey, principal: toPrincipal, scope };
                    store.put(migrated);
                    cursor.delete();
                    changed = true;
                    cursor.continue();
                };
            };
            request.onerror = () => reject(request.error);
        }));
        return true;
    } catch (error) {
        warn('IndexedDB principal namespace migration failed', { fromPrincipal, toPrincipal, error });
        return false;
    }
}
async function migrateOfflinePrincipalToUser(userId) {
    const toPrincipal = authenticatedPrincipalKey(userId);
    if (!toPrincipal) return false;
    const legacyPrincipal = String(userId);
    if (legacyPrincipal !== toPrincipal) await migratePrincipalNamespace(legacyPrincipal, toPrincipal);
    return migratePrincipalNamespace(offlinePrincipalKey(), toPrincipal);
}

function metadataKey(scope) { return `${principalKey()}|${scopeKey(scope)}`; }
function operationKey(operation) { return `${principalKey()}|${scopeKey(operation.scope)}|${operation.opId}`; }
function principalScopeKey(scope) { return `${principalKey()}|${scopeKey(scope)}`; }
function defaultMeta(scope, key = metadataKey(scope)) {
    return { key, principal: principalKey(), scope: scopeKey(scope), lastEventId: 0, epoch: '', revision: 0, localSequence: 0, baseSnapshot: [], baseMetadata: {} };
}
async function readMeta(scope) {
    const key = metadataKey(scope);
    return idb('meta', 'readonly', store => new Promise(resolve => {
        const request = store.get(key);
        request.onsuccess = () => resolve(request.result || defaultMeta(scope, key));
        request.onerror = () => resolve(defaultMeta(scope, key));
    }));
}
async function writeMeta(scope, patch) {
    const key = metadataKey(scope);
    return idb('meta', 'readwrite', store => new Promise((resolve, reject) => {
        const request = store.get(key);
        request.onerror = () => reject(request.error);
        request.onsuccess = () => {
            const current = request.result || defaultMeta(scope, key);
            const incomingEpoch = patch.epoch !== undefined ? String(patch.epoch || '') : String(current.epoch || '');
            const epochChanged = !!current.epoch && !!incomingEpoch && incomingEpoch !== String(current.epoch);
            const merged = { ...current, ...clone(patch), key, principal: principalKey(), scope: scopeKey(scope), updatedAt: now() };
            if (patch.lastEventId !== undefined) merged.lastEventId = epochChanged ? Number(patch.lastEventId || 0) : Math.max(Number(current.lastEventId || 0), Number(patch.lastEventId || 0));
            if (patch.revision !== undefined) merged.revision = epochChanged ? Number(patch.revision || 0) : Math.max(Number(current.revision || 0), Number(patch.revision || 0));
            if (epochChanged) {
                merged.epoch = incomingEpoch;
                merged.baseSnapshot = clone(patch.baseSnapshot || []);
                merged.baseMetadata = clone(patch.baseMetadata || {});
            }
            const write = store.put(merged);
            write.onerror = () => reject(write.error);
            write.onsuccess = () => resolve();
        };
    }));
}

async function nextLocalSequence(scope) {
    const key = metadataKey(scope);
    return idb('meta', 'readwrite', store => new Promise((resolve, reject) => {
        const request = store.get(key);
        request.onerror = () => reject(request.error);
        request.onsuccess = () => {
            const existing = request.result || defaultMeta(scope, key);
            const next = Number(existing.localSequence || 0) + 1;
            const write = store.put({ ...existing, localSequence: next, updatedAt: now(), key, principal: principalKey(), scope: scopeKey(scope) });
            write.onerror = () => reject(write.error);
            write.onsuccess = () => resolve(next);
        };
    }));
}
async function listQueuedOps(scope) {
    const principalScope = principalScopeKey(scope);
    return idb('ops', 'readonly', store => new Promise(resolve => {
        const result = [];
        const request = store.index('principalScope').openCursor(IDBKeyRange.only(principalScope));
        request.onsuccess = () => {
            const cursor = request.result;
            if (!cursor) {
                result.sort((a, b) => Number(a.localSequence) - Number(b.localSequence) || Number(a.createdAt) - Number(b.createdAt));
                resolve(result);
                return;
            }
            result.push(cursor.value);
            cursor.continue();
        };
        request.onerror = () => resolve(result);
    }));
}
async function putOperation(operation) {
    return idb('ops', 'readwrite', store => store.put({ ...clone(operation), key: operationKey(operation), principalScope: principalScopeKey(operation.scope), scope: scopeKey(operation.scope) }));
}
async function deleteOperation(operation) { return idb('ops', 'readwrite', store => store.delete(operation.key || operationKey(operation))); }
async function clearPrincipalData(principal) {
    if (!principal) return;
    for (const storeName of ['ops', 'meta']) await idb(storeName, 'readwrite', store => new Promise((resolve, reject) => {
        const index = storeName === 'ops' ? store.index('principalScope') : store.index('principal');
        const range = storeName === 'ops' ? IDBKeyRange.bound(`${principal}|`, `${principal}|\uffff`) : IDBKeyRange.only(principal);
        const request = index.openCursor(range);
        request.onsuccess = () => {
            const cursor = request.result;
            if (!cursor) { resolve(); return; }
            cursor.delete();
            cursor.continue();
        };
        request.onerror = () => reject(request.error);
    }));
}
async function clearOwnData() {
    await openDb();
    if (serverUserId) {
        await clearPrincipalData(authenticatedPrincipalKey(serverUserId));
        await clearPrincipalData(String(serverUserId));
    }
    await clearPrincipalData(offlinePrincipalKey());
    try {
        localStorage.removeItem(OFFLINE_PRINCIPAL_BINDING_STORAGE_KEY);
        localStorage.removeItem(OFFLINE_PRINCIPAL_STORAGE_KEY);
    } catch {}
    const db = await openDb();
    db.close();
    dbPromise = null;
}

/* -------------------------------------------------------------------------- */
/* Merge                                                                      */
/* -------------------------------------------------------------------------- */
function messageEqual(a, b) { return JSON.stringify(a) === JSON.stringify(b); }
function mergeMetadataThreeWay(base, local, remote) {
    const B = isObject(base) ? base : {};
    const L = isObject(local) ? local : {};
    const R = isObject(remote) ? remote : {};
    if (JSON.stringify(L) === JSON.stringify(B)) return clone(R);
    if (JSON.stringify(R) === JSON.stringify(B)) return clone(L);
    const result = {};
    const keys = new Set([...Object.keys(B), ...Object.keys(L), ...Object.keys(R)]);
    for (const key of keys) {
        const b = B[key], l = L[key], r = R[key];
        const hasB = Object.prototype.hasOwnProperty.call(B, key);
        const hasL = Object.prototype.hasOwnProperty.call(L, key);
        const hasR = Object.prototype.hasOwnProperty.call(R, key);
        if (hasL && hasR && JSON.stringify(l) === JSON.stringify(r)) { result[key] = clone(l); continue; }
        if (hasL && hasB && JSON.stringify(l) === JSON.stringify(b)) { if (hasR) result[key] = clone(r); continue; }
        if (hasR && hasB && JSON.stringify(r) === JSON.stringify(b)) { if (hasL) result[key] = clone(l); continue; }
        if (hasL && hasR && isObject(l) && isObject(r) && isObject(b)) result[key] = mergeMetadataThreeWay(b, l, r);
        else if (hasL) result[key] = clone(l);
        else if (hasR) result[key] = clone(r);
    }
    return result;
}
function mergeSnapshots(base, local, remote) {
    const B = normalizeSnapshot(base || []), L = normalizeSnapshot(local || []), R = normalizeSnapshot(remote || []);
    if (snapshotEquivalent(L, B)) return R;
    if (snapshotEquivalent(R, B)) return L;

    const mapById = list => new Map(list.map(message => [stableMessageId(message), message]));
    const bm = mapById(B), lm = mapById(L), rm = mapById(R);
    const allIds = new Set([...bm.keys(), ...lm.keys(), ...rm.keys()]);
    const chosen = new Map();

    for (const id of allIds) {
        const b = bm.get(id), l = lm.get(id), r = rm.get(id);
        if (l && r && snapshotEquivalent([l], [r])) { chosen.set(id, clone(l)); continue; }
        if ((!l && b) || (!r && b)) continue; // deletion wins
        if (l && b && snapshotEquivalent([l], [b])) { if (r) chosen.set(id, clone(r)); continue; }
        if (r && b && snapshotEquivalent([r], [b])) { if (l) chosen.set(id, clone(l)); continue; }
        if (r) chosen.set(id, clone(r)); else if (l) chosen.set(id, clone(l));
    }

    const active = new Set(chosen.keys());
    const edges = new Map(), indegree = new Map();
    for (const id of active) { edges.set(id, new Set()); indegree.set(id, 0); }
    function addConstraints(list) {
        let previous = null;
        for (const message of list) {
            const id = stableMessageId(message);
            if (!id || !active.has(id)) continue;
            if (previous && previous !== id && !edges.get(previous).has(id)) {
                edges.get(previous).add(id);
                indegree.set(id, indegree.get(id) + 1);
            }
            previous = id;
        }
    }
    addConstraints(B); addConstraints(L); addConstraints(R);
    const result = [], remaining = new Set(active);
    while (remaining.size) {
        const ready = [...remaining].filter(id => indegree.get(id) === 0).sort();
        const nextId = ready[0] || [...remaining].sort()[0];
        result.push(clone(chosen.get(nextId)));
        remaining.delete(nextId);
        for (const child of edges.get(nextId) || []) indegree.set(child, Math.max(0, indegree.get(child) - 1));
    }
    return normalizeSnapshot(result);
}

/* -------------------------------------------------------------------------- */
/* Local application                                                          */
/* -------------------------------------------------------------------------- */
async function saveCurrentChat() {
    ctx = getContext();
    if (typeof ctx.saveChatConditional === 'function') return ctx.saveChatConditional();
    return ctx.saveChat?.();
}

async function saveCurrentChatVerified(expectedEpoch = scopeEpoch, expectedScope = currentScope) {
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    await saveCurrentChat();
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    const data = await api('/state', {
        method: 'POST',
        body: JSON.stringify({ protocol: PROTOCOL, schema: SCHEMA, scope: expectedScope, clientId, deviceId }),
    });
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    const mode = settings.syncSwipes ? 'full' : 'relevant';
    const expectedDigest = await snapshotDigest(localSnapshot(), mode);
    if (expectedDigest && data.host?.snapshotDigest && mode === 'full' && expectedDigest !== data.host.snapshotDigest) throw new Error('Native SillyTavern chat save could not be verified.');
    if (expectedDigest && data.host?.relevantSnapshotDigest && mode === 'relevant' && expectedDigest !== data.host.relevantSnapshotDigest) throw new Error('Native SillyTavern chat save could not be verified.');
    if (settings.syncMetadata) {
        const metadataDigest = await sha256(canonicalJson(localMetadata()));
        if (metadataDigest && data.host?.metadataDigest && metadataDigest !== data.host.metadataDigest) throw new Error('Native SillyTavern metadata save could not be verified.');
    }
    return true;
}
async function applySnapshotLocally(snapshot, metadata, expectedEpoch, reason, expectedScope, { persist = false } = {}) {
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    ctx = getContext();
    const localBefore = Array.isArray(ctx.chat) ? clone(ctx.chat) : [];
    const next = applySyncProjection(snapshot, currentState?.snapshot || []).map(message => mergeDisabledFields(message, findMessageById(localBefore, stableMessageId(message))));
    const nextMetadata = isObject(metadata) ? clone(metadata) : {};
    applyingRemoteDepth++;
    try {
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
        ctx.chat.splice(0, ctx.chat.length, ...next);
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
        ctx.updateChatMetadata?.(nextMetadata, true);
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
        await ctx.printMessages?.();
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
        if (persist) {
            await saveCurrentChatVerified(expectedEpoch, expectedScope);
            hostMessageIdsDirty = false;
        }
        log('chat applied', reason, persist ? 'persisted' : 'preview');
        return true;
    } finally {
        applyingRemoteDepth = Math.max(0, applyingRemoteDepth - 1);
    }
}

async function applyGroupSettings(groupSettings, expectedEpoch) {
    if (!settings.syncGroupSettings || !currentScope || currentScope.kind !== 'group' || !isObject(groupSettings) || !scopeIsCurrent(expectedEpoch)) return false;
    const group = ctx.groups?.find(item => String(item.id) === String(currentScope.groupId));
    if (!group) return false;
    applyingRemoteDepth++;
    try {
        const allowedKeys = ['name', 'members', 'disabled_members', 'chats', 'generation_mode', 'generation_mode_join_prefix', 'generation_mode_join_suffix', 'activation_strategy', 'auto_mode_delay', 'allow_self_responses', 'avatar_url', 'hideMutedSprites', 'fav'];
        for (const key of allowedKeys) if (Object.prototype.hasOwnProperty.call(groupSettings, key)) group[key] = clone(groupSettings[key]);
        const groupModule = await import('/scripts/group-chats.js');
        if (typeof groupModule.editGroup === 'function') await groupModule.editGroup(String(currentScope.groupId), true, false);
        return scopeIsCurrent(expectedEpoch);
    } catch (error) {
        warn('group settings apply failed', error);
        return false;
    } finally { applyingRemoteDepth = Math.max(0, applyingRemoteDepth - 1); }
}

function generationPreviewSnapshot(state) {
    const base = clone(state?.snapshot || []);
    const generation = state?.generation;
    if (!generation) return normalizeSnapshot(base);

    const overlays = Array.isArray(generation.streamMessages) && generation.streamMessages.length
        ? generation.streamMessages
        : generation.streamMessage
            ? [{ messageId: generation.messageId || stableMessageId(generation.streamMessage), message: generation.streamMessage }]
            : [];

    for (const entry of overlays) {
        const message = entry?.message;
        const id = entry?.messageId || stableMessageId(message);
        if (!message || !id) continue;
        const index = base.findIndex(item => stableMessageId(item) === id);
        if (index >= 0) base[index] = clone(message);
        else base.push(clone(message));
    }
    return normalizeSnapshot(base);
}

async function applyGenerationPreview(generation, expectedEpoch, reason = 'generation-preview', metadata = null) {
    if (!settings?.syncMessages || !generationSnapshotEntries(generation).length || !scopeIsCurrent(expectedEpoch)) return false;
    const base = applySyncProjection(currentState?.snapshot || []);
    let snapshot = generationPreviewSnapshot({ snapshot: base, generation });

    // Preserve ordinary local edits made by a follower while the remote generation
    // is streaming. The live generated message(s) are treated as the remote side
    // of the three-way merge; they are never queued as local durable edits.
    try {
        const local = durableLocalSnapshot();
        if (!snapshotEquivalent(local, base)) {
            snapshot = mergeSnapshots(base, local, snapshot);
        }
    } catch (error) {
        warn('generation preview merge failed', error);
    }

    const nextMetadata = metadata && isObject(metadata) ? metadata : (currentState?.chatMetadata || localMetadata());
    return applySnapshotLocally(snapshot, nextMetadata, expectedEpoch, reason, currentScope, { persist: false });
}

/* -------------------------------------------------------------------------- */
/* Queue                                                                      */
/* -------------------------------------------------------------------------- */
async function coalesceSnapshotOperation(operation) {
    const queued = await listQueuedOps(operation.scope);
    const previous = queued.at(-1);
    if (!previous || previous.type !== 'snapshot' || operation.type !== 'snapshot' || previous.inFlight) return false;
    previous.snapshot = clone(operation.snapshot);
    if (operation.chatMetadata !== undefined) previous.chatMetadata = clone(operation.chatMetadata);
    previous.reason = operation.reason;
    previous.localSequence = operation.localSequence;
    previous.updatedAt = now();
    await putOperation(previous);
    return true;
}

async function enqueueMutation(reason, expectedEpoch = scopeEpoch, expectedScope = currentScope) {
    if (applyingRemoteDepth > 0 || generationActive() || !currentScope || !settings.enabled || !scopeIsCurrent(expectedEpoch, expectedScope)) return;
    const scopeAtStart = clone(expectedScope || currentScope);
    const key = scopeKey(scopeAtStart);
    if (!key) return;
    const previous = enqueueMutationChains.get(key) || Promise.resolve();
    const next = previous.catch(() => {}).then(() => enqueueMutationLocked(reason, expectedEpoch, scopeAtStart));
    const tracked = next.finally(() => {
        if (enqueueMutationChains.get(key) === tracked) enqueueMutationChains.delete(key);
    });
    tracked.catch(() => {});
    enqueueMutationChains.set(key, tracked);
    return next;
}
async function enqueueMutationLocked(reason, expectedEpoch, scopeAtStart) {
    if (!sameScope(scopeAtStart, currentScope) || !scopeIsCurrent(expectedEpoch, scopeAtStart)) return;
    const baseState = clone(currentState || {});
    if (!settings.syncMessages && !settings.syncMetadata) return;

    const baseSnapshot = applySyncProjection(baseState.snapshot || []);
    const baseMetadata = clone(baseState.chatMetadata || {});
    const snapshot = settings.syncMessages ? durableLocalSnapshot() : clone(baseSnapshot);
    if (settings.syncMessages && hostMessageIdsDirty) {
        try { await saveCurrentChatVerified(expectedEpoch, scopeAtStart); hostMessageIdsDirty = false; } catch (error) { warn('Could not persist message IDs', error); return; }
    }
    if (!scopeIsCurrent(expectedEpoch, scopeAtStart)) return;

    const metadata = settings.syncMetadata ? localMetadata() : undefined;
    if (snapshotEquivalent(snapshot, baseSnapshot) && (!settings.syncMetadata || canonicalJson(metadata) === canonicalJson(baseMetadata))) return;

    const localSequence = await nextLocalSequence(scopeAtStart);
    const operation = {
        opId: randomId('op_'),
        type: settings.syncMetadata && !settings.syncMessages ? 'metadata' : 'snapshot',
        reason, createdAt: now(), updatedAt: now(), localSequence, scope: scopeAtStart,
        baseRevision: Number(baseState.revision || 0),
        baseSnapshot, baseMetadata, snapshot,
        ...(settings.syncMetadata ? { chatMetadata: metadata } : {}),
    };
    const queued = await listQueuedOps(scopeAtStart);
    if (queued.length >= MAX_QUEUE) {
        const drop = queued.find(item => !item.inFlight) || queued[0];
        if (drop?.inFlight) {
            warn('Synchronization queue is full and oldest item is in flight; retaining queued data.');
            return;
        }
        await deleteOperation(drop);
        toast('warning', 'The synchronization queue was full; the oldest pending operation was dropped.');
    }
    if (await coalesceSnapshotOperation(operation)) {
        if (serverCompatible) void flushQueue(expectedEpoch);
        return;
    }
    await putOperation(operation);
    if (serverCompatible) void flushQueue(expectedEpoch);
}

async function rebaseOperation(operation, serverState) {
    const localDesired = mergeSnapshots(operation.baseSnapshot || [], operation.snapshot || [], serverState.snapshot || []);
    const hasMetadata = Object.prototype.hasOwnProperty.call(operation, 'chatMetadata');
    let mergedMetadata = clone(serverState.chatMetadata || {});
    if (hasMetadata) {
        const base = operation.baseMetadata || {}, local = operation.chatMetadata || {}, remote = serverState.chatMetadata || {};
        if (canonicalJson(local) === canonicalJson(base)) mergedMetadata = clone(remote);
        else if (canonicalJson(remote) === canonicalJson(base)) mergedMetadata = clone(local);
        else mergedMetadata = mergeMetadataThreeWay(base, local, remote);
    }
    operation.baseRevision = Number(serverState.revision);
    operation.baseSnapshot = clone(serverState.snapshot || []);
    operation.baseMetadata = clone(serverState.chatMetadata || {});
    operation.snapshot = localDesired;
    if (hasMetadata) operation.chatMetadata = mergedMetadata;
    operation.updatedAt = now();
    return operation;
}
async function applyRebasedOperationLocally(operation, expectedEpoch) {
    if (!scopeIsCurrent(expectedEpoch, operation.scope)) return;
    if (operation.type === 'metadata') {
        const messages = settings.syncMessages ? durableLocalSnapshot() : (currentState?.snapshot || []);
        await applySnapshotLocally(messages, operation.chatMetadata ?? currentState?.chatMetadata ?? {}, expectedEpoch, 'queue-rebase-metadata', operation.scope, { persist: false });
    } else {
        await applySnapshotLocally(operation.snapshot, operation.chatMetadata ?? currentState?.chatMetadata ?? {}, expectedEpoch, 'queue-rebase', operation.scope, { persist: false });
    }
    if (currentState?.generation && currentGenerationIsRemote()) await applyGenerationPreview(currentState.generation, expectedEpoch, 'queue-rebase-generation-preview');
}

async function refreshServerState(expectedEpoch) {
    const scopeAtStart = clone(currentScope);
    if (!scopeAtStart || !scopeIsCurrent(expectedEpoch, scopeAtStart)) return null;
    try {
        const data = await api('/state', { method: 'POST', body: JSON.stringify({ scope: scopeAtStart, clientId, deviceId }) });
        if (!scopeIsCurrent(expectedEpoch, scopeAtStart)) return null;
        await setServerState(data.state, data.cursor);
        await applyActiveGenerationPreview(data.state?.generation, expectedEpoch, 'refresh-generation-preview', data.state?.chatMetadata);
        return data.state;
    } catch (error) { lastError = error.message; updateInfo(); return null; }
}

async function flushQueue(expectedEpoch = scopeEpoch) {
    const flushKey = scopeKey(currentScope);
    if (!scopeIsCurrent(expectedEpoch) || !flushKey || flushingQueueKeys.has(flushKey)) return;
    flushingQueueKeys.add(flushKey);
    try {
        while (scopeIsCurrent(expectedEpoch)) {
            if (generationActive()) break;

            const queue = await listQueuedOps(currentScope);
            if (!queue.length) break;
            const operation = queue[0];
            if (!sameScope(operation.scope, currentScope)) { await deleteOperation(operation); continue; }
            operation.inFlight = true;
            await putOperation(operation);
            try {
                const payload = { opId: operation.opId, baseRevision: operation.baseRevision };
                if (operation.type === 'snapshot') {
                    payload.snapshot = clone(operation.snapshot);
                    payload.chatMetadata = clone(operation.chatMetadata ?? operation.baseMetadata ?? {});
                    const digestMode = settings.syncSwipes ? 'full' : 'relevant';
                    const digest = await snapshotDigest(durableLocalSnapshot(), digestMode);
                    if (digest) { payload.hostSnapshotDigest = digest; payload.hostSnapshotDigestMode = digestMode; payload.syncSwipes = !!settings.syncSwipes; }
                } else if (operation.type === 'metadata') {
                    payload.chatMetadata = clone(operation.chatMetadata || {});
                    const metadataDigest = await sha256(canonicalJson(localMetadata()));
                    if (metadataDigest) payload.hostMetadataDigest = metadataDigest;
                }

                const result = await api('/event', { method: 'POST', body: JSON.stringify(eventBody(operation.type, payload)) });
                if (!scopeIsCurrent(expectedEpoch)) { operation.inFlight = false; await putOperation(operation); return; }
                await setServerState(result.state, { epoch: result.epoch, revision: result.revision, lastEventId: result.eventId });
                await deleteOperation(operation);
                broadcastScopeEvent('accepted');
            } catch (error) {
                operation.inFlight = false;
                await putOperation(operation);
                if (error.code === 'revision_conflict' || error.code === 'stale_host') {
                    const state = await refreshServerState(expectedEpoch);
                    if (!state) break;
                    await rebaseOperation(operation, state);
                    await applyRebasedOperationLocally(operation, expectedEpoch);
                    await putOperation(operation);
                    continue;
                }
                if (error.code === 'not_member' || error.code === 'unauthenticated') { await reconnectCurrentScope(); break; }
                if (error.code === 'generation_active') break;
                if (error.code === 'branch_host_missing') break;
                warn('queue flush failed', error);
                break;
            }
        }
    } finally { flushingQueueKeys.delete(flushKey); updateUi(); updateInfo(); }
}


/* -------------------------------------------------------------------------- */
/* Server state / resync                                                      */
/* -------------------------------------------------------------------------- */
async function setServerState(state, cursor = {}, { preview = true } = {}) {
    if (!state || !currentScope) return;
    const token = currentState?.subscriptionToken;
    const previous = currentState || {};
    serverInstanceId = state.serverInstanceId || serverInstanceId;
    const merged = {
        ...clone(previous),
        ...clone(state),
        serverInstanceId: state.serverInstanceId || previous.serverInstanceId || serverInstanceId,
    };
    const epochChanged = !!previous.epoch && !!merged.epoch && previous.epoch !== merged.epoch;
    if (!epochChanged && Object.prototype.hasOwnProperty.call(state, 'generation') && state.generation && previous.generation && state.generation.id === previous.generation.id) {
        merged.generation = mergeGenerationProgress(previous.generation, state.generation);
    }
    if (!Object.prototype.hasOwnProperty.call(state, 'snapshot')) merged.snapshot = clone(previous.snapshot || []);
    if (!Object.prototype.hasOwnProperty.call(state, 'chatMetadata')) merged.chatMetadata = clone(previous.chatMetadata || {});
    if (token) merged.subscriptionToken = token;
    currentState = merged;

    const patch = {
        lastEventId: Number(cursor.lastEventId ?? cursor.eventId ?? 0),
        epoch: merged.epoch,
        revision: Number(merged.revision || 0),
    };
    if (Object.prototype.hasOwnProperty.call(state, 'snapshot')) patch.baseSnapshot = clone(merged.snapshot || []);
    if (Object.prototype.hasOwnProperty.call(state, 'chatMetadata')) patch.baseMetadata = clone(merged.chatMetadata || {});
    await writeMeta(currentScope, patch);

    if (preview && merged.generation && currentGenerationIsRemote()) await applyActiveGenerationPreview(merged.generation, scopeEpoch, 'state-update-generation-preview', merged.chatMetadata);
    updateUi(); updateInfo();
}

async function applyActiveGenerationPreview(generation, expectedEpoch, reason = 'active-generation-preview', metadata = null) {
    if (!generation || !currentGenerationIsRemote() || !scopeIsCurrent(expectedEpoch)) return false;
    return applyGenerationPreview(generation, expectedEpoch, reason, metadata);
}

async function localDiffersFromBase() {
    if (!currentState) return false;
    const local = settings.syncMessages ? durableLocalSnapshot() : null;
    const remoteBase = applySyncProjection(currentState.snapshot || []);
    const localMeta = settings.syncMetadata ? localMetadata() : null;
    const remoteMeta = currentState.chatMetadata || {};
    return (settings.syncMessages && !snapshotEquivalent(local, remoteBase))
        || (settings.syncMetadata && canonicalJson(localMeta) !== canonicalJson(remoteMeta));
}

async function protectRemoteApply(expectedEpoch, incomingState) {
    if (!scopeIsCurrent(expectedEpoch)) return false;
    if (applyingRemoteDepth > 0) return true;
    if (incomingState?.generation && currentGenerationIsRemote()) return true;
    const queue = await listQueuedOps(currentScope);
    if (queue.length) {
        await resyncCurrentScope({ preferLocal: true, incomingState });
        return false;
    }
    if (await localDiffersFromBase()) {
        await resyncCurrentScope({ preferLocal: true, incomingState });
        return false;
    }
    return true;
}

async function handleRemoteEvent(event, state, expectedEpoch) {
    if (!event || !scopeIsCurrent(expectedEpoch)) return;
    if (event.source?.clientId === clientId && event.source?.deviceId === deviceId) return;

    if (event.type === 'metadata') {
        if (!settings.syncMetadata || !(await protectRemoteApply(expectedEpoch, state))) return;
        const messages = settings.syncMessages ? clone(currentState?.snapshot || localSnapshot()) : localSnapshot();
        await applySnapshotLocally(messages, state?.chatMetadata || event.chatMetadata || {}, expectedEpoch, 'remote-metadata', currentScope, { persist: false });
        return;
    }

    if (['snapshot', 'reconcile_local', 'bootstrap'].includes(event.type)) {
        if (!settings.syncMessages || !(await protectRemoteApply(expectedEpoch, state)) ) return;
        await applySnapshotLocally(state?.snapshot || [], settings.syncMetadata ? (state?.chatMetadata || {}) : localMetadata(), expectedEpoch, `remote-${event.type}`, currentScope, { persist: false });
        return;
    }

    if (['generation_claim', 'generation_started', 'generation_heartbeat'].includes(event.type)) {
        const incomingGeneration = clone(event.generation || state?.generation || null);
        currentState = {
            ...(currentState || {}),
            generation: incomingGeneration
                ? mergeGenerationProgress(currentState?.generation, incomingGeneration)
                : null,
        };
        if (currentGenerationIsRemote()) await applyActiveGenerationPreview(currentState.generation, expectedEpoch, `remote-${event.type}`, state?.chatMetadata || currentState?.chatMetadata);
        updateUi(); updateInfo();
        return;
    }

    if (event.type === 'generation_input') {
        if (!settings.syncMessages || !(await protectRemoteApply(expectedEpoch, state))) return;
        const inputSnapshot = Array.isArray(event.snapshot) ? event.snapshot : state?.snapshot;
        if (inputSnapshot) await applySnapshotLocally(inputSnapshot, settings.syncMetadata ? (event.chatMetadata || state?.chatMetadata || {}) : localMetadata(), expectedEpoch, 'remote-generation-input', currentScope, { persist: false });
        const generation = clone(event.generation || state?.generation || currentState?.generation || null);
        currentState = { ...(currentState || {}), generation, snapshot: Array.isArray(inputSnapshot) ? clone(inputSnapshot) : currentState?.snapshot, chatMetadata: event.chatMetadata || state?.chatMetadata || currentState?.chatMetadata || {} };
        updateUi(); updateInfo();
        return;
    }

    if (event.type === 'generation_stream') {
        if (!settings.syncMessages) return;
        if (!event.message) {
            await resyncCurrentScope({ preferLocal: false });
            return;
        }
        await applyRemoteGenerationStream(event, expectedEpoch, state);
        return;
    }

    if (event.type === 'generation_stop_request') {
        if (settings.remoteStop && currentState?.generation?.id === event.generationId && currentGenerationIsRemote()) toast('info', 'Another client requested that generation stop.');
        if (settings.remoteStop && localGeneration?.id === event.generationId && !localGenerationLost) {
            try { ctx.stopGeneration?.(); } catch (error) { warn('remote stop failed', error); }
        }
        return;
    }

    if (event.type === 'generation_terminal') {
        const finalSnapshot = Array.isArray(event.snapshot) ? event.snapshot : state?.snapshot;
        const finalMetadata = settings.syncMetadata ? (event.chatMetadata || state?.chatMetadata || {}) : localMetadata();
        const serverBaseSnapshot = clone(currentState?.snapshot || []);
        const serverBaseMetadata = clone(currentState?.chatMetadata || {});
        const localBeforeTerminal = settings.syncMessages ? durableLocalSnapshot() : [];
        const localMetadataBeforeTerminal = settings.syncMetadata ? localMetadata() : {};
        const localSnapshotChanged = settings.syncMessages && !snapshotEquivalent(localBeforeTerminal, serverBaseSnapshot);
        const localMetadataChanged = settings.syncMetadata && canonicalJson(localMetadataBeforeTerminal) !== canonicalJson(serverBaseMetadata);
        let desiredSnapshot = Array.isArray(finalSnapshot) ? clone(finalSnapshot) : serverBaseSnapshot;
        let desiredMetadata = clone(finalMetadata);
        if (localSnapshotChanged && Array.isArray(finalSnapshot)) desiredSnapshot = mergeSnapshots(serverBaseSnapshot, localBeforeTerminal, finalSnapshot);
        if (localMetadataChanged) desiredMetadata = mergeMetadataThreeWay(serverBaseMetadata, localMetadataBeforeTerminal, finalMetadata);

        if (settings.syncMessages && Array.isArray(desiredSnapshot)) {
            await applySnapshotLocally(desiredSnapshot, desiredMetadata, expectedEpoch, 'remote-generation-terminal', currentScope, { persist: false });
        } else if (settings.syncMetadata) {
            await applySnapshotLocally(localSnapshot(), desiredMetadata, expectedEpoch, 'remote-generation-terminal-metadata', currentScope, { persist: false });
        }

        currentState = {
            ...(currentState || {}),
            generation: null,
            revision: Number(event.revision ?? state?.revision ?? currentState?.revision ?? 0),
            epoch: event.epoch || state?.epoch || currentState?.epoch,
            snapshot: clone(Array.isArray(finalSnapshot) ? finalSnapshot : serverBaseSnapshot),
            chatMetadata: clone(event.chatMetadata || state?.chatMetadata || currentState?.chatMetadata || {}),
        };
        streamMessageFingerprints.clear();
        generationStartedAcknowledged = false;
        groupGenerationStatus = 'completed';
        updateUi(); updateInfo();
        flushDeferredCapture();

        // Preserve unrelated edits made locally while the remote generation was running.
        // They are queued only after the distributed generation has been released.
        if (localSnapshotChanged || localMetadataChanged) {
            await enqueueMutation('post-generation-local-changes', expectedEpoch, expectedScope);
        }
        void flushQueue(expectedEpoch);
        return;
    }
    if (event.type === 'generation_recover') {
        currentState = { ...(currentState || {}), generation: null };
        streamMessageFingerprints.clear();
        await resyncCurrentScope({ preferLocal: true });
        flushDeferredCapture();
        updateUi(); updateInfo();
        return;
    }

    if (event.type === 'chat_renamed') { await handleRemoteChatRenamed(event, expectedEpoch); return; }
    if (event.type === 'chat_deleted' || event.type === 'group_chat_deleted') { await handleRemoteChatDeleted(event, expectedEpoch); return; }

    if (event.type === 'group_settings') {
        await applyGroupSettings(event.groupSettings, expectedEpoch);
        return;
    }

    if (event.type === 'branch_announce') return;
}

async function applyRemoteGenerationStream(event, expectedEpoch, serverState = null) {
    if (!scopeIsCurrent(expectedEpoch)) return;
    const generation = currentState?.generation || serverState?.generation;
    if (!generation || generation.id !== event.generationId) return;
    const sequence = Number(event.streamSeq);
    const currentSeq = Number(generation.streamSeq || 0);
    if (sequence <= currentSeq) return;
    if (sequence !== currentSeq + 1) { await resyncCurrentScope(); return; }

    const nextGeneration = clone(generation);
    nextGeneration.phase = 'streaming';
    nextGeneration.streamSeq = sequence;
    if (!Array.isArray(nextGeneration.streamMessages)) nextGeneration.streamMessages = [];
    if (event.message) {
        const message = normalizeSnapshot([event.message])[0];
        const messageId = event.messageId || stableMessageId(message);
        if (!messageId) { await resyncCurrentScope(); return; }
        const existing = nextGeneration.streamMessages.findIndex(entry => entry.messageId === messageId);
        const entry = { messageId, message };
        if (existing >= 0) nextGeneration.streamMessages[existing] = entry;
        else nextGeneration.streamMessages.push(entry);
        nextGeneration.messageId ||= messageId;
        nextGeneration.streamMessage = clone(message);
    } else if (serverState?.generation) {
        nextGeneration.streamMessages = clone(serverState.generation.streamMessages || []);
        nextGeneration.streamMessage = clone(serverState.generation.streamMessage || null);
        nextGeneration.messageId = serverState.generation.messageId || nextGeneration.messageId || null;
    } else {
        await resyncCurrentScope();
        return;
    }

    currentState = { ...(currentState || {}), generation: nextGeneration };
    scheduleFollowerGenerationRender(nextGeneration, expectedEpoch, serverState?.chatMetadata || currentState?.chatMetadata || localMetadata());
    updateUi(); updateInfo();
}

function scheduleFollowerGenerationRender(generation, expectedEpoch, metadata = null) {
    if (streamRenderPending) return;
    streamRenderPending = true;
    if (streamRenderTimer) clearTimeout(streamRenderTimer);
    streamRenderTimer = setTimeout(async () => {
        streamRenderTimer = null;
        streamRenderPending = false;
        if (!scopeIsCurrent(expectedEpoch) || !generation) return;
        try { await applyGenerationPreview(generation, expectedEpoch, 'remote-generation-stream', metadata); } catch (error) { warn('follower generation render failed', error); }
    }, STREAM_RENDER_INTERVAL);
}

function durableLocalSnapshotForComparison() { return durableLocalSnapshot(); }

async function resyncCurrentScope(options = {}) {
    const expectedEpoch = scopeEpoch;
    const expectedScope = clone(currentScope);
    if (!expectedScope || !serverCompatible || !scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    try {
        const data = await api('/state', { method: 'POST', body: JSON.stringify({ protocol: PROTOCOL, schema: SCHEMA, scope: expectedScope, clientId, deviceId }) });
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;

        const serverState = clone(data.state);
        const previousState = clone(currentState || {});
        alignMessageIdsToReference(serverState.snapshot || []);
        if (hostMessageIdsDirty && settings.syncMessages) {
            try { await saveCurrentChat(); hostMessageIdsDirty = false; } catch {}
        }

        // Adopt the fetched server revision before creating/rebasing local work.
        await setServerState(serverState, data.cursor, { preview: false });

        const queue = await listQueuedOps(expectedScope);
        const local = settings.syncMessages ? durableLocalSnapshot() : [];
        const remote = applySyncProjection(serverState.snapshot || []);
        const remoteGeneration = !!serverState.generation && (serverState.generation.ownerClientId !== clientId || serverState.generation.ownerDeviceId !== deviceId);
        const hasLocalDivergence = (settings.syncMessages && !snapshotEquivalent(local, remote))
            || (settings.syncMetadata && canonicalJson(localMetadata()) !== canonicalJson(serverState.chatMetadata || {}));

        if (remoteGeneration && !options.discardLocal) {
            // During another client's live generation, the durable server snapshot is authoritative.
            // Local queued work is retained for rebase after the generation terminates.
            if (settings.syncMessages) {
                await applySnapshotLocally(remote, settings.syncMetadata ? (serverState.chatMetadata || {}) : localMetadata(), expectedEpoch, 'resync-active-generation', expectedScope, { persist: false });
            } else if (settings.syncMetadata) {
                await applySnapshotLocally(localSnapshot(), serverState.chatMetadata || {}, expectedEpoch, 'resync-active-generation-metadata', expectedScope, { persist: false });
            }
        } else if (options.discardLocal) {
            for (const operation of queue) if (!operation.inFlight) await deleteOperation(operation);
            if (settings.syncMessages) {
                await applySnapshotLocally(remote, settings.syncMetadata ? (serverState.chatMetadata || {}) : localMetadata(), expectedEpoch, 'resync-discard-local', expectedScope, { persist: false });
            } else if (settings.syncMetadata) {
                await applySnapshotLocally(localSnapshot(), serverState.chatMetadata || {}, expectedEpoch, 'resync-discard-local-metadata', expectedScope, { persist: false });
            }
        } else if (queue.length || options.preferLocal || hasLocalDivergence) {
            const base = queue.length ? (queue[0].baseSnapshot || []) : (previousState?.snapshot || remote);
            const merged = settings.syncMessages ? mergeSnapshots(base, local, remote) : local;
            if (settings.syncMessages) {
                await applySnapshotLocally(merged, settings.syncMetadata ? mergeMetadataThreeWay(previousState?.chatMetadata || {}, localMetadata(), serverState.chatMetadata || {}) : localMetadata(), expectedEpoch, 'resync-merge', expectedScope, { persist: false });
            } else if (settings.syncMetadata) {
                await applySnapshotLocally(localSnapshot(), serverState.chatMetadata || {}, expectedEpoch, 'resync-merge-metadata', expectedScope, { persist: false });
            }
            if (!queue.length && (settings.syncMessages || settings.syncMetadata)) await enqueueMutation('resync-merge', expectedEpoch);
        } else if (settings.syncMessages || settings.syncMetadata) {
            const messages = settings.syncMessages ? remote : localSnapshot();
            const metadata = settings.syncMetadata ? (serverState.chatMetadata || {}) : localMetadata();
            await applySnapshotLocally(messages, metadata, expectedEpoch, 'resync', expectedScope, { persist: false });
        }

        if (currentScope?.kind === 'group' && settings.syncGroupSettings && serverState.groupSettings) await applyGroupSettings(serverState.groupSettings, expectedEpoch);
        if (serverState.generation && currentGenerationIsRemote()) await applyActiveGenerationPreview(serverState.generation, expectedEpoch, 'resync-generation-preview', serverState.chatMetadata);
        await flushQueue(expectedEpoch);
        return true;
    } catch (error) { lastError = error.message; updateInfo(); return false; }
}

/* -------------------------------------------------------------------------- */
/* SSE                                                                        */
/* -------------------------------------------------------------------------- */
function closeSse() {
    if (sseReconnectTimer) clearTimeout(sseReconnectTimer);
    sseReconnectTimer = null;
    if (sse) try { sse.close(); } catch {}
    sse = null;
    sseHelloEventId = 0;
}
function scheduleReconnect(expectedEpoch) {
    if (sseReconnectTimer || !scopeIsCurrent(expectedEpoch) || !serverCompatible || !settings.enabled) return;
    const delay = Math.min(30_000, 750 * (2 ** Math.min(reconnectAttempt, 6)));
    reconnectAttempt++;
    sseReconnectTimer = setTimeout(() => { sseReconnectTimer = null; if (scopeIsCurrent(expectedEpoch)) void reconnectCurrentScope(); }, delay);
}
async function connectSse() {
    if (!currentScope || !serverCompatible || !settings.enabled) return;
    closeSse();
    const expectedEpoch = scopeEpoch;
    const expectedScope = clone(currentScope);
    const token = currentState?.subscriptionToken;
    if (!token || !scopeIsCurrent(expectedEpoch, expectedScope)) return;
    const meta = await readMeta(expectedScope);
    const url = new URL(`${PLUGIN_BASE}/events`, location.origin);
    url.searchParams.set('token', token);
    if (meta.lastEventId) url.searchParams.set('lastEventId', String(meta.lastEventId));
    const stream = new EventSource(url, { withCredentials: true });
    sse = stream;
    sseEventChain = Promise.resolve();
    stream.onopen = () => { reconnectAttempt = 0; lastError = ''; updateUi(); updateInfo(); };
    const queue = (event, type) => {
        sseEventChain = sseEventChain.then(async () => {
            let data;
            try { data = JSON.parse(event.data); } catch { return; }
            if (!scopeIsCurrent(expectedEpoch, expectedScope) || sse !== stream) return;
            await handleSseData(type, data, event.lastEventId, expectedEpoch, expectedScope);
        }).catch(error => warn('SSE handling failed', error));
    };
    for (const eventName of ['hello', 'replay', 'replay_complete', 'resync_required', 'sync', 'shutdown']) stream.addEventListener(eventName, event => queue(event, eventName));
    stream.onerror = () => {
        try { stream.close(); } catch {}
        if (sse === stream) sse = null;
        scheduleReconnect(expectedEpoch);
        updateUi();
    };
}
async function handleSseData(type, data, lastEventId, expectedEpoch, expectedScope) {
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return;
    if (type === 'hello') {
        const serverChanged = !!serverInstanceId && !!data.serverInstanceId && serverInstanceId !== data.serverInstanceId;
        if (serverChanged && currentState?.generation) {
            await writeMeta(expectedScope, { lastEventId: 0 });
            await resyncCurrentScope();
            return;
        }
        serverInstanceId = data.serverInstanceId || serverInstanceId;
        if (currentState?.epoch && data.epoch && currentState.epoch !== data.epoch) { await writeMeta(expectedScope, { lastEventId: 0 }); await resyncCurrentScope(); return; }
        sseHelloEventId = Number(data.eventId || 0);
        currentState = { ...(currentState || {}), epoch: data.epoch, revision: Math.max(Number(currentState?.revision || 0), Number(data.revision || 0)), generation: clone(data.generation || null) };
        await applyActiveGenerationPreview(data.generation, expectedEpoch, 'sse-hello-generation-preview', currentState?.chatMetadata);
        updateUi();
        return;
    }
    if (type === 'replay') {
        if (data.epoch && currentState?.epoch && data.epoch !== currentState.epoch) return;
        if (data.event && sseHelloEventId && Number(data.event.id || 0) <= sseHelloEventId && !currentState?.generation && String(data.event.type || '').startsWith('generation_')) {
            await writeMeta(expectedScope, { lastEventId: Number(lastEventId || data.event?.id || 0) });
            return;
        }
        if (data.event) await handleRemoteEvent(data.event, currentState, expectedEpoch);
        await writeMeta(expectedScope, { lastEventId: Number(lastEventId || data.event?.id || 0) });
        return;
    }
    if (type === 'replay_complete') {
        await writeMeta(expectedScope, { lastEventId: Number(data.eventId || lastEventId || 0), epoch: data.epoch, revision: Number(data.revision || currentState?.revision || 0) });
        await resyncCurrentScope();
        return;
    }
    if (type === 'resync_required') { await writeMeta(expectedScope, { lastEventId: 0 }); await resyncCurrentScope(); return; }
    if (type === 'sync') {
        if (data.epoch && currentState?.epoch && data.epoch !== currentState.epoch) { await resyncCurrentScope(); return; }
        await handleRemoteEvent(data.event, data.state, expectedEpoch);
        if (scopeIsCurrent(expectedEpoch, expectedScope) && data.state) await setServerState(data.state, { epoch: data.epoch || data.state.epoch, revision: data.state.revision, lastEventId: lastEventId || data.event?.id || 0 });
        broadcastScopeEvent('remote');
        return;
    }
    if (type === 'shutdown') closeSse();
}

/* -------------------------------------------------------------------------- */
/* Join / scopes                                                              */
/* -------------------------------------------------------------------------- */
async function joinScope(scope, expectedEpoch) {
    if (!scope || !serverCompatible || !settings.enabled || !scopeIsCurrent(expectedEpoch, scope)) return false;
    const previousMeta = await readMeta(scope);
    if (settings.syncMessages) {
        ensureHostMessageIds();
        if (hostMessageIdsDirty) {
            try { await saveCurrentChat(); hostMessageIdsDirty = false; } catch (error) { warn('pre-join message-ID save failed', error); }
        }
    }
    try {
        const result = await api('/join', { method: 'POST', body: JSON.stringify({ protocol: PROTOCOL, schema: SCHEMA, scope, clientId, deviceId }) });
        if (!scopeIsCurrent(expectedEpoch, scope)) return false;
        serverUserId = String(result.userId || serverUserId || '');
        currentState = { ...clone(result.state), subscriptionToken: result.subscriptionToken, serverInstanceId: result.state?.serverInstanceId || result.serverInstanceId || serverInstanceId };
        serverInstanceId = result.state?.serverInstanceId || result.serverInstanceId || serverInstanceId;
        if (result.state?.deleted) {
            await handleRemoteChatDeleted({ type: 'chat_deleted' }, expectedEpoch);
            return true;
        }
        if (result.state?.renamedTo?.scope?.chatId && String(result.state.renamedTo.scope.chatId) !== String(scope.chatId)) {
            await handleRemoteChatRenamed({ newChatId: String(result.state.renamedTo.scope.chatId) }, expectedEpoch);
            return true;
        }
        if (result.host?.missingMessageIds && settings.syncMessages) {
            ensureHostMessageIds();
            if (hostMessageIdsDirty) {
                try { await saveCurrentChatVerified(expectedEpoch, scope); hostMessageIdsDirty = false; } catch (error) { warn('host synchronization ID persistence failed', error); }
            }
            if (Number(result.state?.revision || 0) === 0) {
                await enqueueMutation('host-message-id-bootstrap', expectedEpoch);
                await flushQueue(expectedEpoch);
                const refreshed = await refreshServerState(expectedEpoch);
                if (refreshed) result.state = refreshed;
            }
        }
        const sameEpoch = previousMeta.epoch === result.state.epoch;
        await writeMeta(scope, {
            lastEventId: sameEpoch ? Number(previousMeta.lastEventId || 0) : 0,
            epoch: result.state.epoch,
            revision: result.state.revision,
            baseSnapshot: clone(result.state.snapshot || []),
            baseMetadata: clone(result.state.chatMetadata || {}),
        });

        if (settings.syncMessages) {
            alignMessageIdsToReference(result.state.snapshot || []);
            if (hostMessageIdsDirty) {
                try { await saveCurrentChat(); hostMessageIdsDirty = false; } catch (error) { warn('message ID save failed', error); }
            }
        }

        const queue = await listQueuedOps(scope);
        const local = settings.syncMessages ? durableLocalSnapshot() : [];
        const remote = applySyncProjection(result.state.snapshot || []);
        const remoteGeneration = !!result.state.generation && (result.state.generation.ownerClientId !== clientId || result.state.generation.ownerDeviceId !== deviceId);
        const differs = settings.syncMessages && !snapshotEquivalent(local, remote);

        if (remoteGeneration) {
            if (settings.syncMessages) {
                await applySnapshotLocally(remote, settings.syncMetadata ? (result.state.chatMetadata || {}) : localMetadata(), expectedEpoch, 'join-active-generation', scope, { persist: false });
            } else if (settings.syncMetadata) {
                await applySnapshotLocally(localSnapshot(), result.state.chatMetadata || {}, expectedEpoch, 'join-active-generation-metadata', scope, { persist: false });
            }
        } else if (differs) {
            const base = queue.length ? (queue[0].baseSnapshot || []) : (sameEpoch ? previousMeta.baseSnapshot || [] : remote);
            const merged = mergeSnapshots(base, local, remote);
            if (settings.syncMessages) {
                await applySnapshotLocally(merged, settings.syncMetadata ? mergeMetadataThreeWay(currentState?.chatMetadata || {}, localMetadata(), result.state.chatMetadata || {}) : localMetadata(), expectedEpoch, 'join-merge', scope, { persist: false });
            } else if (settings.syncMetadata) {
                await applySnapshotLocally(localSnapshot(), result.state.chatMetadata || {}, expectedEpoch, 'join-merge-metadata', scope, { persist: false });
            }
            if (!queue.length && (settings.syncMessages || settings.syncMetadata)) await enqueueMutation('join-merge', expectedEpoch);
        } else if (settings.syncMessages || settings.syncMetadata) {
            const messages = settings.syncMessages ? remote : localSnapshot();
            const metadata = settings.syncMetadata ? (result.state.chatMetadata || {}) : localMetadata();
            await applySnapshotLocally(messages, metadata, expectedEpoch, 'join', scope, { persist: false });
        }

        if (currentScope?.kind === 'group' && settings.syncGroupSettings && result.state.groupSettings) await applyGroupSettings(result.state.groupSettings, expectedEpoch);
        if (remoteGeneration) await applyActiveGenerationPreview(result.state.generation, expectedEpoch, 'join-generation-preview', result.state.chatMetadata);

        reconnectAttempt = 0;
        await connectSse();
        startHeartbeat();
        void flushQueue(expectedEpoch);
        updateUi(); updateInfo();
        return true;
    } catch (error) {
        serverAvailable = error.code !== 'unauthenticated' && error.status !== 404;
        serverCompatible = error.status !== 404;
        lastError = error.message;
        updateUi(); updateInfo();
        return false;
    }
}

async function leaveScope(scope) {
    if (!scope || !serverCompatible) return;
    try { await api('/leave', { method: 'POST', body: JSON.stringify({ protocol: PROTOCOL, schema: SCHEMA, scope, clientId, deviceId }) }); } catch {}
}
async function switchScope(nextScope) {
    const previousScope = clone(currentScope);
    const previousGeneration = clone(localGeneration);
    const previousEpoch = scopeEpoch;
    const expectedEpoch = ++scopeEpoch;
    closeSse(); stopHeartbeat(); stopGenerationHeartbeat();
    clearTimeout(captureTimer);
    captureTimer = null;
    captureScheduled = false;
    clearTimeout(streamTimer);
    streamTimer = null;
    if (previousGeneration && previousScope) {
        localGenerationLost = true;
        try { ctx.stopGeneration?.(); } catch {}
    }
    if (previousScope) void leaveScope(previousScope);
    currentScope = nextScope ? clone(nextScope) : null;
    currentState = null;
    localGeneration = null;
    localGenerationLost = false;
    generationStartedAcknowledged = false;
    groupGenerationActive = false;
    groupGenerationStatus = 'completed';
    streamMessageFingerprints.clear();
    pendingStreamMessage = null;
    deferredCaptureReason = null;
    if (previousEpoch !== expectedEpoch && generationFinishRetryTimer) { clearTimeout(generationFinishRetryTimer); generationFinishRetryTimer = null; }
    if (!currentScope) { updateUi(); updateInfo(); return; }
    if (!settings.enabled || !settings.autoConnect || !serverCompatible) { updateUi(); updateInfo(); return; }
    await joinScope(currentScope, expectedEpoch);
}
async function reconnectCurrentScope() {
    await checkHealth();
    const target = getCurrentScope();
    if (!target) { closeSse(); stopHeartbeat(); currentScope = null; currentState = null; updateUi(); updateInfo(); return false; }
    if (sameScope(target, currentScope)) {
        const expectedEpoch = ++scopeEpoch;
        closeSse(); stopHeartbeat();
        await joinScope(clone(target), expectedEpoch);
        return true;
    }
    await switchScope(target);
    return true;
}

/* -------------------------------------------------------------------------- */
/* Heartbeat                                                                  */
/* -------------------------------------------------------------------------- */
function startHeartbeat() { stopHeartbeat(); heartbeatTimer = setInterval(() => void sendHeartbeat(), 10_000); }
function stopHeartbeat() { if (heartbeatTimer) clearInterval(heartbeatTimer); heartbeatTimer = null; }
async function sendHeartbeat() {
    if (!currentScope || !serverCompatible || !settings.enabled) return;
    const expectedEpoch = scopeEpoch;
    const expectedScope = clone(currentScope);
    try {
        const result = await api('/heartbeat', {
            method: 'POST',
            body: JSON.stringify({
                protocol: PROTOCOL,
                schema: SCHEMA,
                scope: expectedScope,
                clientId,
                deviceId,
            }),
        });
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return;

        const previousGeneration = clone(currentState?.generation || null);
        const returnedGeneration = clone(result.generation || null);

        currentState = {
            ...(currentState || {}),
            generation: returnedGeneration,
            revision: Math.max(
                Number(currentState?.revision || 0),
                Number(result.revision || 0),
            ),
        };

        if (localGeneration) {
            if (
                returnedGeneration
                && returnedGeneration.id === localGeneration.id
                && returnedGeneration.ownerClientId === clientId
                && returnedGeneration.ownerDeviceId === deviceId
            ) {
                localGenerationLost = false;
                await applyActiveGenerationPreview(
                    returnedGeneration,
                    expectedEpoch,
                    'heartbeat-generation-preview',
                    currentState?.chatMetadata,
                );
            } else if (!returnedGeneration) {
                // The lease may have expired while the owner is still generating.
                // Attempt to reclaim the exact same generation instead of killing a
                // potentially valid native generation on a transient heartbeat race.
                const reclaimed = await reclaimGeneration(
                    expectedEpoch,
                    expectedScope,
                );
                if (!reclaimed && previousGeneration?.id === localGeneration?.id) {
                    warn('generation lease disappeared and could not be reclaimed');
                    await stopLostGeneration();
                }
            } else {
                await stopLostGeneration();
            }
        } else if (
            returnedGeneration
            && returnedGeneration.ownerClientId !== clientId
            && returnedGeneration.ownerDeviceId !== deviceId
        ) {
            await applyActiveGenerationPreview(
                returnedGeneration,
                expectedEpoch,
                'heartbeat-remote-generation-preview',
                currentState?.chatMetadata,
            );
        }

        updateUi();
    } catch {
        scheduleReconnect(expectedEpoch);
    }
}

/* -------------------------------------------------------------------------- */
/* Generation                                                                 */
/* -------------------------------------------------------------------------- */
function startGenerationHeartbeat() {
    stopGenerationHeartbeat();
    generationHeartbeatFailures = 0;
    generationHeartbeatTimer = setInterval(() => void renewGeneration(), 5_000);
}
function stopGenerationHeartbeat() {
    if (generationHeartbeatTimer) clearInterval(generationHeartbeatTimer);
    generationHeartbeatTimer = null;
    generationHeartbeatFailures = 0;
}
async function stopLostGeneration() {
    const lostScope = clone(currentScope);
    const expectedEpoch = scopeEpoch;
    if (!localGeneration) return;
    localGenerationLost = true;
    generationStartedAcknowledged = false;
    stopGenerationHeartbeat();
    try { ctx.stopGeneration?.(); } catch {}
    updateUi(); updateInfo();
    if (lostScope && scopeIsCurrent(expectedEpoch, lostScope)) {
        try { await resyncCurrentScope({ discardLocal: true }); } catch {}
    }
}
async function reclaimGeneration(expectedEpoch = scopeEpoch, expectedScope = currentScope) {
    if (
        !localGeneration
        || !expectedScope
        || !scopeIsCurrent(expectedEpoch, expectedScope)
        || !serverCompatible
        || !settings.coordinateGeneration
    ) return false;

    const generationId = localGeneration.id;
    const generationType = localGeneration.type || 'normal';
    const scopeAtStart = clone(expectedScope);
    try {
        const result = await api('/event', {
            method: 'POST',
            body: JSON.stringify(eventBody('generation_claim', {
                opId: `reclaim_${generationId}`,
                generationId,
                generationType,
            }, scopeAtStart)),
        });

        if (!scopeIsCurrent(expectedEpoch, scopeAtStart)) return false;

        localGenerationLost = false;
        generationStartedAcknowledged = false;
        currentState = {
            ...(currentState || {}),
            generation: clone(result.generation),
        };
        startGenerationHeartbeat();

        // The native Generate() is already underway, so re-enter the server-side
        // started phase immediately and let the next captured stream update carry
        // the current complete message to followers.
        const started = await acknowledgeGenerationStarted(
            generationType,
            scopeAtStart,
        );
        if (!started) return false;

        updateUi();
        updateInfo();
        return true;
    } catch (error) {
        if (error.code === 'generation_busy') {
            return false;
        }
        if (error.code === 'client_id_conflict' || error.code === 'not_member') {
            return false;
        }
        warn('generation reclaim failed', error);
        return false;
    }
}
async function confirmGenerationAfterHeartbeatFailure(expectedEpoch, expectedScope) {
    if (!localGeneration || !scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    try {
        const data = await api('/state', {
            method: 'POST',
            body: JSON.stringify({
                protocol: PROTOCOL,
                schema: SCHEMA,
                scope: expectedScope,
                clientId,
                deviceId,
            }),
        });
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
        const generation = data.state?.generation || null;
        currentState = {
            ...(currentState || {}),
            ...clone(data.state || {}),
        };

        if (
            generation
            && generation.id === localGeneration.id
            && generation.ownerClientId === clientId
            && generation.ownerDeviceId === deviceId
        ) {
            localGenerationLost = false;
            generationHeartbeatFailures = 0;
            return true;
        }

        if (!generation) {
            return reclaimGeneration(expectedEpoch, expectedScope);
        }

        return false;
    } catch {
        return false;
    }
}
async function renewGeneration() {
    if (!localGeneration || localGenerationLost || !currentScope) return;
    const expectedEpoch = scopeEpoch;
    const expectedScope = clone(currentScope);
    const generationId = localGeneration.id;
    try {
        const result = await api('/heartbeat', {
            method: 'POST',
            body: JSON.stringify({
                protocol: PROTOCOL,
                schema: SCHEMA,
                scope: expectedScope,
                clientId,
                deviceId,
                generationId,
            }),
        });
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return;
        generationHeartbeatFailures = 0;
        const generation = result.generation || null;
        currentState = {
            ...(currentState || {}),
            generation: clone(generation),
            revision: Math.max(
                Number(currentState?.revision || 0),
                Number(result.revision || 0),
            ),
        };

        if (!generation) {
            const reclaimed = await reclaimGeneration(expectedEpoch, expectedScope);
            if (!reclaimed) await stopLostGeneration();
            return;
        }

        if (
            generation.id !== generationId
            || generation.ownerClientId !== clientId
            || generation.ownerDeviceId !== deviceId
        ) {
            const reclaimed = await confirmGenerationAfterHeartbeatFailure(expectedEpoch, expectedScope);
            if (!reclaimed) await stopLostGeneration();
            return;
        }

        localGenerationLost = false;
        updateUi();
    } catch (error) {
        generationHeartbeatFailures++;

        if (
            ['generation_mismatch', 'no_generation', 'not_generation_owner'].includes(error.code)
        ) {
            const reclaimed = await reclaimGeneration(expectedEpoch, expectedScope);
            if (!reclaimed) await stopLostGeneration();
            return;
        }

        if (generationHeartbeatFailures >= 3) {
            const confirmed = await confirmGenerationAfterHeartbeatFailure(expectedEpoch, expectedScope);
            if (!confirmed) await stopLostGeneration();
        }
    }
}
async function sendGenerationInput(expectedEpoch = scopeEpoch, expectedScope = currentScope) {
    if (!localGeneration || localGenerationLost || !expectedScope || !settings.coordinateGeneration || !scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    const generationId = localGeneration.id;
    ensureHostMessageIds();
    if (hostMessageIdsDirty) {
        try {
            await saveCurrentChatVerified(expectedEpoch, expectedScope);
            hostMessageIdsDirty = false;
        } catch (error) {
            warn('generation input message-ID save failed', error);
            return false;
        }
    }
    const snapshot = localSnapshot();
    const metadata = localMetadata();
    const digestMode = settings.syncSwipes ? 'full' : 'relevant';
    const digest = await snapshotDigest(snapshot, digestMode);
    const metadataDigest = settings.syncMetadata ? await sha256(canonicalJson(metadata)) : null;
    const opId = generationInputOpId || `input_${generationId}`;
    generationInputOpId = opId;
    for (let attempt = 0; attempt < GENERATION_INPUT_MAX_RETRIES; attempt++) {
        try {
            const result = await api('/event', {
                method: 'POST',
                body: JSON.stringify(eventBody('generation_input', {
                    opId,
                    generationId,
                    baseRevision: Number(currentState?.revision || 0),
                    snapshot,
                    chatMetadata: metadata,
                    syncSwipes: !!settings.syncSwipes,
                    ...(digest ? { hostSnapshotDigest: digest, hostSnapshotDigestMode: digestMode } : {}),
                    ...(metadataDigest ? { hostMetadataDigest: metadataDigest } : {}),
                }, expectedScope)),
            });
            if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
            await setServerState(result.state, { epoch: result.epoch, revision: result.revision, lastEventId: result.eventId });
            return true;
        } catch (error) {
            if (error.code === 'revision_conflict' || error.code === 'stale_host' || error.code === 'stale_host_metadata') {
                await refreshServerState(expectedEpoch);
                continue;
            }
            if (attempt < GENERATION_INPUT_MAX_RETRIES - 1 && (!error.status || error.status >= 500)) {
                await sleep(100 * (attempt + 1));
                continue;
            }
            warn('generation input synchronization failed', error);
            return false;
        }
    }
    return false;
}

async function claimGeneration(generationType = 'normal') {
    if (!settings.coordinateGeneration || !currentScope || !serverCompatible) return true;
    if (localGeneration && !localGenerationLost) return true;
    if (currentState?.generation) {
        const refreshed = await refreshServerState(scopeEpoch);
        if (refreshed?.generation) return false;
        if (!scopeIsCurrent(scopeEpoch)) return false;
    }
    if (generationType === 'group' && currentScope.kind !== 'group') return false;
    const generationId = randomId('g_');
    const opId = `claim_${generationId}`;
    for (let attempt = 0; attempt < 3; attempt++) {
        try {
            const scopeAtStart = clone(currentScope);
            const result = await api('/event', { method: 'POST', body: JSON.stringify(eventBody('generation_claim', { opId, generationId, generationType }, scopeAtStart)) });
            if (!scopeIsCurrent(scopeEpoch, scopeAtStart)) return false;
            localGeneration = { id: generationId, type: generationType, terminalOpId: `terminal_${generationId}` };
            localGenerationLost = false;
            generationStartedAcknowledged = false;
            generationInputOpId = null;
            streamMessageFingerprints.clear();
            currentState = { ...(currentState || {}), generation: clone(result.generation) };
            startGenerationHeartbeat();
            updateUi(); updateInfo();
            return true;
        } catch (error) {
            if (error.code === 'generation_busy') {
                toast('warning', 'Another synchronized client is generating in this chat.');
                await resyncCurrentScope({ discardLocal: true });
                return false;
            }
            if (attempt < 2 && (!error.status || error.status >= 500)) { await sleep(150 * (attempt + 1)); continue; }
            warn('generation claim failed', error);
            return false;
        }
    }
    return false;
}
async function acknowledgeGenerationStarted(type) {
    if (!localGeneration || localGenerationLost || generationStartedAcknowledged || !currentScope) return !!localGeneration;
    const scopeAtStart = clone(currentScope);
    const opId = `start_${localGeneration.id}`;
    for (let attempt = 0; attempt < 3; attempt++) {
        try {
            const result = await api('/event', { method: 'POST', body: JSON.stringify(eventBody('generation_started', { opId, generationId: localGeneration.id, generationType: type || localGeneration.type || 'normal' }, scopeAtStart)) });
            if (!scopeIsCurrent(scopeEpoch, scopeAtStart)) return false;
            generationStartedAcknowledged = true;
            currentState = { ...(currentState || {}), generation: clone(result.generation) };
            updateUi(); updateInfo();
            return true;
        } catch (error) {
            if (['generation_mismatch', 'no_generation', 'not_generation_owner'].includes(error.code)) {
                await stopLostGeneration();
                return false;
            }
            if (attempt < 2 && (!error.status || error.status >= 500)) { await sleep(150 * (attempt + 1)); continue; }
            await stopLostGeneration();
            warn('generation start acknowledgement failed', error);
            return false;
        }
    }
    return false;
}

async function attemptTerminalRecovery(status, generationId, expectedEpoch, expectedScope) {
    if (!expectedScope || !scopeIsCurrent(expectedEpoch, expectedScope) || !localGeneration || localGeneration.id !== generationId) return false;
    ensureHostMessageIds();
    const refreshed = await refreshServerState(expectedEpoch);
    if (!refreshed) return false;
    try {
        await saveCurrentChatVerified(expectedEpoch, expectedScope);
        hostMessageIdsDirty = false;
    } catch {
        return false;
    }
    const snapshot = localSnapshot();
    const metadata = localMetadata();
    const digestMode = settings.syncSwipes ? 'full' : 'relevant';
    const digest = await snapshotDigest(snapshot, digestMode);
    const metadataDigest = settings.syncMetadata ? await sha256(canonicalJson(metadata)) : null;
    try {
        const result = await api('/event', {
            method: 'POST',
            body: JSON.stringify(eventBody('generation_terminal_recover', {
                opId: localGeneration.terminalOpId || `terminal_${generationId}`,
                generationId,
                baseRevision: Number(refreshed.revision || 0),
                status,
                snapshot,
                chatMetadata: metadata,
                syncSwipes: !!settings.syncSwipes,
                ...(digest ? { hostSnapshotDigest: digest, hostSnapshotDigestMode: digestMode } : {}),
                ...(metadataDigest ? { hostMetadataDigest: metadataDigest } : {}),
            }, expectedScope)),
        });
        if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
        await setServerState(result.state, { epoch: result.epoch, revision: result.revision, lastEventId: result.eventId });
        stopGenerationHeartbeat();
        localGeneration = null;
        localGenerationLost = false;
        generationStartedAcknowledged = false;
        streamMessageFingerprints.clear();
        void flushQueue(expectedEpoch);
        return true;
    } catch (error) {
        if (['generation_busy', 'generation_recovery_unavailable'].includes(error.code)) return false;
        if (error.code === 'revision_conflict') {
            await refreshServerState(expectedEpoch);
        }
        return false;
    }
}

async function finishGeneration(status = 'completed') {
    if (finishingGeneration) return;
    if (!localGeneration || localGenerationLost || !currentScope || !serverCompatible) return;
    finishingGeneration = true;
    const generationId = localGeneration.id;
    const expectedEpoch = scopeEpoch;
    const scopeAtStart = clone(currentScope);
    try {
        if (streamTimer) {
            clearTimeout(streamTimer);
            streamTimer = null;
            pendingStreamMessage = null;
        }
        const candidates = streamCandidates();
        for (const message of candidates) streamFlushPromise = streamFlushPromise.then(() => sendGenerationStream(message, expectedEpoch, scopeAtStart));
        await streamFlushPromise;
        if (!scopeIsCurrent(expectedEpoch, scopeAtStart) || localGeneration?.id !== generationId) return;
        ensureHostMessageIds();
        try {
            await saveCurrentChatVerified(expectedEpoch, scopeAtStart);
            hostMessageIdsDirty = false;
        } catch (error) {
            warn('final native chat save failed', error);
            if (scopeIsCurrent(expectedEpoch, scopeAtStart) && localGeneration?.id === generationId) {
                if (!generationFinishRetryTimer) {
                    generationFinishRetryTimer = setTimeout(() => {
                        generationFinishRetryTimer = null;
                        void finishGeneration(status);
                    }, 1_000);
                }
            }
            return;
        }
        const snapshot = localSnapshot();
        const metadata = localMetadata();
        const opId = localGeneration.terminalOpId || `terminal_${generationId}`;
        for (let attempt = 0; attempt < 3; attempt++) {
            try {
                const digestMode = settings.syncSwipes ? 'full' : 'relevant';
                const digest = await snapshotDigest(snapshot, digestMode);
                const result = await api('/event', { method: 'POST', body: JSON.stringify(eventBody('generation_terminal', {
                    opId,
                    generationId,
                    status,
                    snapshot,
                    chatMetadata: metadata,
                    syncSwipes: !!settings.syncSwipes,
                    ...(digest ? { hostSnapshotDigest: digest, hostSnapshotDigestMode: digestMode } : {}),
                }, scopeAtStart)) });
                if (!scopeIsCurrent(expectedEpoch, scopeAtStart)) return;
                await setServerState(result.state, { epoch: result.epoch, revision: result.revision, lastEventId: result.eventId });
                stopGenerationHeartbeat();
                localGeneration = null;
                localGenerationLost = false;
                generationStartedAcknowledged = false;
                streamMessageFingerprints.clear();
                groupGenerationStatus = status;
                void flushQueue(expectedEpoch);
                return;
            } catch (error) {
                if (['generation_mismatch', 'no_generation', 'not_generation_owner'].includes(error.code)) {
                    if (await attemptTerminalRecovery(status, generationId, expectedEpoch, scopeAtStart)) return;
                    await stopLostGeneration();
                    return;
                }
                if (attempt < 2 && (!error.status || error.status >= 500)) { await sleep(200 * (attempt + 1)); continue; }
                warn('generation terminal failed', error);
                if (!generationFinishRetryTimer && scopeIsCurrent(expectedEpoch, scopeAtStart) && localGeneration?.id === generationId) {
                    generationFinishRetryTimer = setTimeout(() => { generationFinishRetryTimer = null; void finishGeneration(status); }, 1_000);
                }
                return;
            }
        }
    } finally {
        finishingGeneration = false;
        updateUi(); updateInfo();
    }
}
async function sendGenerationStream(message, expectedEpoch = scopeEpoch, expectedScope = currentScope) {
    if (!localGeneration || localGenerationLost || !expectedScope || !settings.coordinateGeneration || !message) return false;
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
    const generationId = localGeneration.id;
    const normalized = normalizeSnapshot([message])[0];
    const messageId = stableMessageId(normalized);
    if (!messageId) return false;
    const fingerprint = canonicalJson(projectSnapshotForDigest([normalized], settings.syncSwipes ? 'full' : 'relevant'));
    if (streamMessageFingerprints.get(messageId) === fingerprint) return true;
    const nextSequence = Number(currentState?.generation?.streamSeq || 0) + 1;
    const opId = `stream_${generationId}_${nextSequence}`;

    for (let attempt = 0; attempt < 3; attempt++) {
        try {
            const result = await api('/event', { method: 'POST', body: JSON.stringify(eventBody('generation_stream', { opId, generationId, streamSeq: nextSequence, messageId, message: normalized, syncSwipes: !!settings.syncSwipes }, expectedScope)) });
            if (!scopeIsCurrent(expectedEpoch, expectedScope)) return false;
            if (localGeneration?.id === generationId) {
                streamMessageFingerprints.set(messageId, fingerprint);
                currentState = { ...(currentState || {}), generation: clone(result.generation) };
            }
            updateUi();
            return true;
        } catch (error) {
            if (['generation_mismatch', 'not_generation_owner', 'no_generation'].includes(error.code)) { await stopLostGeneration(); return false; }
            if (error.code === 'stream_sequence_gap') {
                await refreshServerState(expectedEpoch);
                return false;
            }
            if (attempt < 2 && (!error.status || error.status >= 500)) { await sleep(100 * (attempt + 1)); continue; }
            if (error.status === 409 && error.code === 'generation_message_mismatch') { await stopLostGeneration(); return false; }
            warn('generation stream failed', error);
            return false;
        }
    }
    return false;
}
function streamCandidates() {
    if (!localGeneration || localGenerationLost || !Array.isArray(ctx?.chat)) return [];
    ensureHostMessageIds();
    const generation = currentState?.generation;
    const ids = new Set(generationSnapshotEntries(generation).map(entry => entry.messageId));
    if (generation?.messageId) ids.add(generation.messageId);
    const result = [];
    for (const id of ids) {
        const message = findMessageById(ctx.chat, id);
        if (message && message.is_user !== true) result.push(clone(message));
    }
    const last = ctx.chat.at(-1);
    if (last && last.is_user !== true && !result.some(message => stableMessageId(message) === stableMessageId(last))) result.push(clone(last));
    return result;
}
function scheduleStreamCapture() {
    if (!localGeneration || localGenerationLost || applyingRemoteDepth || !currentScope) return;
    if (streamTimer) return;
    const scheduledScope = clone(currentScope);
    streamTimer = setTimeout(() => {
        streamTimer = null;
        if (!currentScope || !sameScope(scheduledScope, currentScope) || !localGeneration || localGenerationLost) return;
        const expectedEpoch = scopeEpoch;
        const expectedScope = clone(currentScope);
        for (const message of streamCandidates()) {
            streamFlushPromise = streamFlushPromise.then(() => sendGenerationStream(message, expectedEpoch, expectedScope)).catch(error => warn('stream pipeline failed', error));
        }
    }, STREAM_CAPTURE_INTERVAL);
}

/* -------------------------------------------------------------------------- */
/* Branches / checkpoints                                                     */
/* -------------------------------------------------------------------------- */
async function fetchNativeChatHeader(scope, childChatId) {
    try {
        const url = scope.kind === 'character' ? '/api/chats/get' : '/api/chats/group/get';
        const body = scope.kind === 'character' ? { avatar_url: scope.character, file_name: childChatId } : { id: childChatId };
        const response = await fetch(url, { method: 'POST', credentials: 'same-origin', headers: ctx.getRequestHeaders?.() || {}, body: JSON.stringify(body) });
        if (!response.ok) return null;
        const data = await response.json();
        return { metadata: isObject(data?.[0]?.chat_metadata) ? clone(data[0].chat_metadata) : {} };
    } catch { return null; }
}
async function announceNativeChild(parentScope, childChatId, branchKind, expectedEpoch) {
    const header = await fetchNativeChatHeader(parentScope, childChatId);
    if (!header?.metadata?.integrity || !header?.metadata?.main_chat) {
        toast('warning', 'SillyTavern created the child chat, but its native branch metadata could not be read yet.');
        return false;
    }
    const childScope = { ...clone(parentScope), chatId: String(childChatId), branchId: String(header.metadata.integrity), parentChatId: String(header.metadata.main_chat) };
    for (let attempt = 0; attempt < 3; attempt++) {
        if (!scopeIsCurrent(expectedEpoch, parentScope)) return false;
        try {
            await api('/event', {
                method: 'POST',
                body: JSON.stringify(eventBody('branch_announce', {
                    opId: `branch_${childScope.branchId}`,
                    baseRevision: Number(currentState?.revision || 0),
                    branchKind,
                    childScope,
                }, parentScope)),
            });
            return true;
        } catch (error) {
            if (error.code === 'revision_conflict' && attempt < 2) {
                await resyncCurrentScope({ discardLocal: false });
                continue;
            }
            if (error.code === 'branch_host_missing' && attempt < 2) { await sleep(250 * (attempt + 1)); continue; }
            warn('branch announcement failed', error);
            return false;
        }
    }
    return false;
}

async function createNativeBranch() {
    if (!settings.syncBranches || !currentScope || !serverCompatible) return;
    if (currentState?.generation) { toast('warning', 'Wait for generation to finish before creating a branch.'); return; }
    const parentScope = clone(currentScope), expectedEpoch = scopeEpoch, index = Math.max(0, ctx.chat.length - 1);
    try {
        const bookmarks = await import('/scripts/bookmarks.js');
        const childChatId = await bookmarks.createBranch(index, {});
        if (!childChatId || !scopeIsCurrent(expectedEpoch, parentScope)) return;
        await saveCurrentChatVerified(expectedEpoch, parentScope);
        await enqueueMutation('native-branch-created', expectedEpoch);
        await flushQueue(expectedEpoch);
        await announceNativeChild(parentScope, String(childChatId), 'branch', expectedEpoch);
        toast('success', `Branch created: ${childChatId}`);
    } catch (error) { warn('native branch creation failed', error); toast('error', `Branch creation failed: ${error.message}`); }
}
async function createNativeCheckpoint() {
    if (!settings.syncBranches || !currentScope || !serverCompatible) return;
    if (currentState?.generation) { toast('warning', 'Wait for generation to finish before creating a checkpoint.'); return; }
    const parentScope = clone(currentScope), expectedEpoch = scopeEpoch, index = Math.max(0, ctx.chat.length - 1);
    try {
        const bookmarks = await import('/scripts/bookmarks.js');
        const childChatId = await bookmarks.createNewBookmark(index);
        if (!childChatId || !scopeIsCurrent(expectedEpoch, parentScope)) return;
        await saveCurrentChatVerified(expectedEpoch, parentScope);
        await enqueueMutation('native-checkpoint-created', expectedEpoch);
        await flushQueue(expectedEpoch);
        await announceNativeChild(parentScope, String(childChatId), 'checkpoint', expectedEpoch);
        toast('success', `Checkpoint created: ${childChatId}`);
    } catch (error) { warn('native checkpoint creation failed', error); toast('error', `Checkpoint creation failed: ${error.message}`); }
}

async function requestRemoteGenerationStop() {
    const generation = currentState?.generation;
    if (!generation || !currentGenerationIsRemote() || !settings.remoteStop || !currentScope || !serverCompatible) return;
    try {
        await api('/event', {
            method: 'POST',
            body: JSON.stringify(eventBody('generation_stop_request', {
                opId: randomId('op_'),
                generationId: generation.id,
                reason: 'remote_stop_button',
            })),
        });
        toast('success', 'Generation stop requested.');
    } catch (error) {
        warn('remote generation stop request failed', error);
    }
}

/* -------------------------------------------------------------------------- */
/* Group settings                                                             */
/* -------------------------------------------------------------------------- */
function currentGroupSettings() {
    if (!currentScope || currentScope.kind !== 'group') return null;
    const group = ctx.groups?.find(item => String(item.id) === String(currentScope.groupId));
    if (!group) return null;
    const allowedKeys = ['name', 'members', 'disabled_members', 'chats', 'generation_mode', 'generation_mode_join_prefix', 'generation_mode_join_suffix', 'activation_strategy', 'auto_mode_delay', 'allow_self_responses', 'avatar_url', 'hideMutedSprites', 'fav'];
    const snapshot = {};
    for (const key of allowedKeys) if (group[key] !== undefined) snapshot[key] = clone(group[key]);
    return snapshot;
}
async function publishGroupSettings(expectedEpoch = scopeEpoch) {
    if (!settings.syncGroupSettings || generationActive() || !currentScope || currentScope.kind !== 'group' || !serverCompatible || !scopeIsCurrent(expectedEpoch)) return;
    const snapshot = currentGroupSettings();
    if (!snapshot) return;
    if (canonicalJson(snapshot) === canonicalJson(currentState?.groupSettings || {})) return;
    try {
        const result = await api('/event', { method: 'POST', body: JSON.stringify(eventBody('group_settings', { opId: randomId('op_'), baseRevision: Number(currentState?.revision || 0), groupSettings: snapshot })) });
        if (scopeIsCurrent(expectedEpoch)) await setServerState(result.state, { epoch: result.epoch, revision: result.revision, lastEventId: result.eventId });
    } catch (error) { if (error.code === 'revision_conflict') await resyncCurrentScope(); else warn('group setting publish failed', error); }
}

/* -------------------------------------------------------------------------- */
/* Capture                                                                     */
/* -------------------------------------------------------------------------- */
function scheduleLocalCapture(reason) {
    if (applyingRemoteDepth || !currentScope || !settings.enabled) return;
    if (generationActive()) {
        deferredCaptureReason = reason || 'generation-deferred';
        return;
    }
    if (captureScheduled) return;
    captureScheduled = true;
    const expectedScope = clone(currentScope);
    clearTimeout(captureTimer);
    captureTimer = setTimeout(() => {
        captureScheduled = false;
        if (!currentScope || !sameScope(expectedScope, currentScope)) return;
        void enqueueMutation(reason, scopeEpoch, expectedScope);
    }, SNAPSHOT_CAPTURE_DELAY);
}
async function handleChatChanged() {
    if (applyingRemoteDepth) return;
    const nextScope = getCurrentScope();
    if (sameScope(nextScope, currentScope)) { scheduleLocalCapture('chat-changed'); return; }
    const requested = clone(nextScope);
    scopeTransitionChain = scopeTransitionChain.catch(() => {}).then(async () => {
        const latest = getCurrentScope();
        if (!sameScope(latest, requested) && !(requested === null && latest === null)) return;
        await switchScope(requested);
    });
    await scopeTransitionChain;
}
function flushDeferredCapture() {
    if (generationActive() || !deferredCaptureReason) return;
    const reason = deferredCaptureReason;
    deferredCaptureReason = null;
    scheduleLocalCapture(`deferred-${reason}`);
}

/* -------------------------------------------------------------------------- */
/* BroadcastChannel                                                            */
/* -------------------------------------------------------------------------- */
function initBroadcastChannel() {
    if (typeof BroadcastChannel === 'undefined' || broadcastChannel) return;
    try {
        broadcastChannel = new BroadcastChannel(EXTENSION_ID);
        broadcastChannel.onmessage = event => {
            const data = event.data;
            if (!data || data.type !== 'scope-event') return;
            if (data.scopeKey !== scopeKey(currentScope)) return;
            if (data.principal && data.principal !== principalKey()) return;
            void resyncCurrentScope();
        };
    } catch { broadcastChannel = null; }
}
function broadcastScopeEvent(type) { try { broadcastChannel?.postMessage({ type: 'scope-event', principal: principalKey(), scopeKey: scopeKey(currentScope), eventType: type }); } catch {} }

/* -------------------------------------------------------------------------- */
/* Events                                                                      */
/* -------------------------------------------------------------------------- */
function bindBrowserEvent(name, fn, options) { window.addEventListener(name, fn, options); browserBindings.push({ name, fn, options }); }
function unbindBrowserEvents() { for (const binding of browserBindings) window.removeEventListener(binding.name, binding.fn, binding.options); browserBindings = []; }
function bindStEvent(name, handler) {
    if (!name || !ctx?.eventSource) return;
    const wrapped = (...args) => {
        try {
            Promise.resolve(handler(...args)).catch(error => warn(`ST event handler failed: ${name}`, error));
        } catch (error) {
            warn(`ST event handler failed: ${name}`, error);
        }
    };
    ctx.eventSource.on(name, wrapped);
    listenerBindings.push({ name, wrapped });
}
function unbindStEvents() {
    for (const binding of listenerBindings) try { ctx.eventSource?.removeListener(binding.name, binding.wrapped); } catch {}
    listenerBindings = [];
}


async function sendChatLifecycleEvent(type, scope, extra = {}) {
    if (applyingRemoteDepth || !scope || !serverCompatible || !settings.enabled) return false;
    try {
        await api('/event', { method: 'POST', body: JSON.stringify(eventBody(type, {
            opId: randomId('op_'),
            baseRevision: Number(currentState?.revision || 0),
            ...extra,
        }, scope)) });
        return true;
    } catch (error) {
        warn(`${type} synchronization failed`, error);
        return false;
    }
}

async function handleLocalChatRenamed(...args) {
    if (applyingRemoteDepth || !currentState?.scope || !serverCompatible || !settings.enabled) return;
    const oldScope = clone(currentState.scope);
    const next = getCurrentScope();
    if (!next || sameScope(next, oldScope)) return;
    if (next.kind !== oldScope.kind) return;
    if (oldScope.kind === 'character' && next.character !== oldScope.character) return;
    if (oldScope.kind === 'group' && next.groupId !== oldScope.groupId) return;
    for (let attempt = 0; attempt < 3; attempt++) {
        if (!scopeIsCurrent(scopeEpoch)) return;
        const ok = await sendChatLifecycleEvent('chat_renamed', oldScope, {
            oldChatId: oldScope.chatId,
            newChatId: next.chatId,
            newScope: clone(next),
        });
        if (ok) return;
        await sleep(200 * (attempt + 1));
    }
}

async function handleRemoteChatRenamed(event, expectedEpoch) {
    if (!scopeIsCurrent(expectedEpoch) || !event.newChatId) return;
    const target = String(event.newChatId);
    applyingRemoteDepth++;
    try {
        if (currentScope.kind === 'group') {
            const groupModule = await import('/scripts/group-chats.js');
            if (typeof groupModule.openGroupChat === 'function') {
                await groupModule.openGroupChat(String(currentScope.groupId), target);
            }
        } else if (typeof ctx.openCharacterChat === 'function') {
            await ctx.openCharacterChat(target);
        } else if (typeof ctx.reloadCurrentChat === 'function') {
            await ctx.reloadCurrentChat();
        }
    } finally {
        applyingRemoteDepth = Math.max(0, applyingRemoteDepth - 1);
    }
    await handleChatChanged();
}

async function handleRemoteChatDeleted(event, expectedEpoch) {
    if (!scopeIsCurrent(expectedEpoch)) return;
    applyingRemoteDepth++;
    try {
        if (Array.isArray(ctx.chat)) ctx.chat.splice(0, ctx.chat.length);
        await ctx.updateChatMetadata?.({}, true);
        await ctx.printMessages?.();
    } finally {
        applyingRemoteDepth = Math.max(0, applyingRemoteDepth - 1);
    }
    toast('warning', 'This chat was deleted on another synchronized client.');
    await handleChatChanged();
}

function bindStEvents() {
    unbindStEvents();
    ctx = getContext();
    const events = ctx.eventTypes || ctx.event_types || {};
    const capture = [
        'MESSAGE_SENT', 'MESSAGE_RECEIVED', 'MESSAGE_EDITED', 'MESSAGE_DELETED', 'MESSAGE_UPDATED',
        'MESSAGE_SWIPED', 'MESSAGE_SWIPE_DELETED', 'MESSAGE_REASONING_EDITED', 'MESSAGE_REASONING_DELETED',
        'MESSAGE_FILE_EMBEDDED', 'FILE_ATTACHMENT_DELETED', 'MEDIA_ATTACHMENT_DELETED', 'TOOL_CALLS_PERFORMED',
        'MORE_MESSAGES_LOADED', 'IMAGE_SWIPED',
    ];
    const swipingKeys = new Set(['MESSAGE_SWIPED', 'MESSAGE_SWIPE_DELETED', 'IMAGE_SWIPED']);
    const reasoningToolKeys = new Set(['MESSAGE_REASONING_EDITED', 'MESSAGE_REASONING_DELETED', 'TOOL_CALLS_PERFORMED']);
    for (const key of capture) if (events[key]) bindStEvent(events[key], (...args) => {
        if (applyingRemoteDepth !== 0) return;
        if (key === 'MESSAGE_SENT' && localGeneration && !localGenerationLost && settings.coordinateGeneration) {
            void sendGenerationInput(scopeEpoch, clone(currentScope));
            return;
        }
        if (generationActive()) {
            deferredCaptureReason = key;
            return;
        }
        if (swipingKeys.has(key) && !settings.syncSwipes) return;
        if (reasoningToolKeys.has(key) && !settings.syncSwipes) return;
        scheduleLocalCapture(key);
    });

    if (events.CHAT_RENAMED) bindStEvent(events.CHAT_RENAMED, (...args) => void handleLocalChatRenamed(...args));
    if (events.CHAT_DELETED) bindStEvent(events.CHAT_DELETED, () => { if (applyingRemoteDepth === 0 && currentState?.scope) void sendChatLifecycleEvent('chat_deleted', clone(currentState.scope), { chatId: currentState.scope.chatId }); });
    if (events.GROUP_CHAT_DELETED) bindStEvent(events.GROUP_CHAT_DELETED, () => { if (applyingRemoteDepth === 0 && currentState?.scope) void sendChatLifecycleEvent('group_chat_deleted', clone(currentState.scope), { chatId: currentState.scope.chatId }); });

    const chatChangedEvents = [events.CHAT_CHANGED, events.CHAT_LOADED, events.CHAT_CREATED, events.GROUP_CHAT_CREATED].filter(Boolean);
    for (const event of new Set(chatChangedEvents)) bindStEvent(event, () => void handleChatChanged());

    if (events.GROUP_UPDATED) bindStEvent(events.GROUP_UPDATED, () => { if (applyingRemoteDepth === 0 && settings.syncGroupSettings) void publishGroupSettings(scopeEpoch); });
    if (events.CHAT_METADATA_UPDATED) bindStEvent(events.CHAT_METADATA_UPDATED, () => { if (applyingRemoteDepth === 0) scheduleLocalCapture('metadata-updated'); });
    if (events.CHAT_UPDATED) bindStEvent(events.CHAT_UPDATED, () => { if (applyingRemoteDepth === 0) scheduleLocalCapture('chat-updated'); });

    if (events.GROUP_WRAPPER_STARTED) bindStEvent(events.GROUP_WRAPPER_STARTED, () => {
        if (currentScope?.kind === 'group' && settings.coordinateGeneration) {
            groupGenerationActive = true;
            groupGenerationStatus = 'completed';
        }
        updateUi();
    });
    if (events.GROUP_MEMBER_DRAFTED) bindStEvent(events.GROUP_MEMBER_DRAFTED, () => { scheduleStreamCapture(); updateUi(); });
    if (events.GROUP_WRAPPER_FINISHED) bindStEvent(events.GROUP_WRAPPER_FINISHED, () => {
        if (groupGenerationActive && localGeneration && !localGenerationLost) void finishGeneration(groupGenerationStatus);
        groupGenerationActive = false;
        if (groupGenerationStatus !== 'stopped') groupGenerationStatus = 'completed';
        updateUi();
    });

    if (events.GENERATION_STARTED) bindStEvent(events.GENERATION_STARTED, () => updateUi());
    if (events.STREAM_TOKEN_RECEIVED) bindStEvent(events.STREAM_TOKEN_RECEIVED, () => scheduleStreamCapture());
    if (events.STREAM_REASONING_DONE) bindStEvent(events.STREAM_REASONING_DONE, () => scheduleStreamCapture());
    if (events.TOOL_CALLS_RENDERED) bindStEvent(events.TOOL_CALLS_RENDERED, () => scheduleStreamCapture());
    if (events.GENERATION_STOPPED) bindStEvent(events.GENERATION_STOPPED, () => {
        if (!localGeneration || localGenerationLost) return;
        if (groupGenerationActive) groupGenerationStatus = 'stopped';
        else void finishGeneration('stopped');
    });
    if (events.GENERATION_ENDED) bindStEvent(events.GENERATION_ENDED, () => {
        if (!localGeneration || localGenerationLost || groupGenerationActive) return;
        void finishGeneration('completed');
    });
}

/* -------------------------------------------------------------------------- */
/* Send interception / generation                                             */
/* -------------------------------------------------------------------------- */
function blockFollowerSendKeydown(event) {
    if (!currentGenerationIsRemote()) return;
    if (!(event.target instanceof HTMLTextAreaElement) || event.target.id !== 'send_textarea') return;
    if (event.key !== 'Enter' || event.shiftKey || event.ctrlKey || event.altKey || event.metaKey) return;
    event.preventDefault();
    event.stopImmediatePropagation();
    toast('warning', 'This chat is generating on another synchronized client.');
}
function blockFollowerSendClick(event) {
    if (!currentGenerationIsRemote()) return;
    const button = event.target instanceof Element ? event.target.closest('#send_but, #option_regenerate, #option_continue, #swipe_left, #swipe_right, .swipe_left, .swipe_right, #option_remove, #option_delete, #option_continue, #send_but') : null;
    if (!button) return;
    event.preventDefault();
    event.stopImmediatePropagation();
    toast('info', 'This chat is generating on another synchronized client. The response is being mirrored here.');
}

async function generationInterceptor(chat, contextSize, abort, type) {
    if (!settings?.enabled || !settings.coordinateGeneration || !currentScope || !serverCompatible) return;
    if (type === 'quiet') return;

    // Do not let a fast second Send (or group auto-mode) overlap the final
    // persistence/terminal acknowledgement of the previous distributed generation.
    if (finishingGeneration) {
        const deadline = now() + REMOTE_APPLY_TIMEOUT;
        while (finishingGeneration && now() < deadline) await sleep(50);
        if (finishingGeneration) {
            try { abort?.(true); } catch {}
            toast('warning', 'The previous synchronized generation is still being finalized.');
            return;
        }
    }
    const actualScope = getCurrentScope();
    if (!sameScope(actualScope, currentScope)) await switchScope(actualScope);
    const expectedEpoch = scopeEpoch;
    const expectedScope = clone(currentScope);
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return;

    // Another same-chat client already owns the generation. Abort this native attempt
    // and restore the durable server state, including removing the just-inserted user message.
    if (currentState?.generation && currentGenerationIsRemote()) {
        try { abort?.(true); } catch {}
        await resyncCurrentScope({ discardLocal: true });
        toast('warning', 'This chat is generating on another synchronized client.');
        return;
    }

    const generationType = currentScope?.kind === 'group' ? 'group' : (type || 'normal');

    // For group generations, the first member claims the wrapper-level lease and
    // subsequent member Generate() calls reuse it.
    if (localGeneration && !localGenerationLost) {
        if (!generationStartedAcknowledged) {
            const acknowledged = await acknowledgeGenerationStarted(generationType);
            if (!acknowledged) { try { abort?.(true); } catch {} }
        }
        return;
    }

    // The current SillyTavern generation interceptor runs before the native user
    // message is inserted. Do not snapshot the current chat here: MESSAGE_SENT
    // will publish the actual generation input after native persistence.
    await flushQueue(expectedEpoch);
    if (!scopeIsCurrent(expectedEpoch, expectedScope)) return;
    const remaining = await listQueuedOps(expectedScope);
    if (remaining.length) {
        try { abort?.(true); } catch {}
        toast('error', 'The chat could not be synchronized before generation started.');
        await resyncCurrentScope({ discardLocal: true });
        return;
    }

    const granted = await claimGeneration(generationType);
    if (!granted) {
        try { abort?.(true); } catch {}
        await resyncCurrentScope({ discardLocal: true });
        return;
    }

    const acknowledged = await acknowledgeGenerationStarted(generationType);
    if (!acknowledged) {
        try { abort?.(true); } catch {}
        return;
    }
}

globalThis.multiClientSyncGenerateInterceptor = generationInterceptor;

/* -------------------------------------------------------------------------- */
/* Lifecycle                                                                  */
/* -------------------------------------------------------------------------- */
async function initialize() {
    if (startPromise) return startPromise;
    startPromise = (async () => {
        ctx = getContext();
        settings = settingsRef();
        renderUi();
        initBroadcastChannel();
        bindBrowserEvent('online', () => void reconnectCurrentScope());
        bindBrowserEvent('pageshow', () => void reconnectCurrentScope());
        bindBrowserEvent('visibilitychange', () => { if (document.visibilityState === 'visible') void reconnectCurrentScope(); });
        bindBrowserEvent('beforeunload', () => { void leaveScope(currentScope); });
        bindBrowserEvent('keydown', blockFollowerSendKeydown, true);
        bindBrowserEvent('click', blockFollowerSendClick, true);
        bindStEvents();
        await checkHealth();
        if (!settings.enabled) { updateUi(); updateInfo(); return; }
        const target = getCurrentScope();
        if (target && settings.autoConnect) await switchScope(target);
        started = true;
        updateUi(); updateInfo();
    })().catch(error => { warn('extension initialization failed', error); lastError = error.message; updateUi(); updateInfo(); });
    await startPromise;
    return startPromise;
}

async function stop() {
    ++scopeEpoch;
    clearTimeout(captureTimer); clearTimeout(streamTimer); clearTimeout(streamRenderTimer);
    if (generationFinishRetryTimer) clearTimeout(generationFinishRetryTimer);
    generationFinishRetryTimer = null;
    stopHeartbeat(); stopGenerationHeartbeat(); closeSse();
    try { broadcastChannel?.close(); } catch {}
    broadcastChannel = null;
    unbindStEvents(); unbindBrowserEvents();
    try { await leaveScope(currentScope); } catch {}
    currentScope = null; currentState = null; localGeneration = null; localGenerationLost = false;
    generationStartedAcknowledged = false; groupGenerationActive = false; groupGenerationStatus = 'completed';
    pendingStreamMessage = null; streamMessageFingerprints.clear(); deferredCaptureReason = null; streamRenderPending = false; generationInputOpId = null; started = false; startPromise = null; flushingQueueKeys.clear(); enqueueMutationChains.clear();
    updateUi(); updateInfo();
}

export async function onInstall() {
    ctx = getContext(); settings = settingsRef(); await ctx.saveSettingsDebounced?.();
}
export async function init() { await initialize(); }
export async function onEnable() {
    settings = settingsRef(); settings.enabled = true;
    if (!started) await initialize(); else await reconnectCurrentScope();
}
export async function onDisable() {
    if (settings) settings.enabled = false;
    await stop();
    await ctx?.saveSettingsDebounced?.();
}
export async function onUpdate() {
    ctx = getContext(); settings = settingsRef(); await ctx.saveSettingsDebounced?.();
}
export async function onDelete() { await stop(); }
export async function onClean() { await stop(); await clearOwnData(); }
