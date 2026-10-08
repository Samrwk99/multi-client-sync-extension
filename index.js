const PLUGIN_BASE = '/api/plugins/multi-client-sync';
const PROTOCOL = 11;
const SCHEMA = 11;
const DB_NAME = 'multi-client-sync';
const DB_VERSION = 11;
const MAX_QUEUE = 1000;
const MAX_QUEUE_BYTES = 64 * 1024 * 1024;
const HEARTBEAT_MS = 10_000;
const GENERATION_HEARTBEAT_MS = 5_000;
const STREAM_SEND_MS = 60;
// Coalesced render on the next tick: pendingRemoteStream is overwritten by
// newer stream events, so only the latest message renders. No fixed latency.
const REMOTE_RENDER_MS = 16;
const STORAGE_KEY = 'multi-client-sync-settings-v1';
const CLIENT_KEY = 'multi-client-sync-client-id-v1';
const DEVICE_KEY = 'multi-client-sync-device-id-v1';
const BC_NAME = 'multi-client-sync';
const API_TIMEOUT_MS = 12_000;
const TERMINAL_API_TIMEOUT_MS = 15_000;
const STOP_API_TIMEOUT_MS = 8_000;
const TERMINAL_RETRY_MS = 1_000;
const REMOTE_STOP_CONFIRM_MS = 350;
// SSE now delivers terminal state promptly; the poll is only a fallback.
const REMOTE_STOP_CONFIRM_ATTEMPTS = 6;
const GENERATION_CONTINUATION_GRACE_MS = 350;
const OWNERSHIP_CONFLICT_GRACE_MS = 3_500;
const OWNERSHIP_RECOVERY_GRACE_MS = 1_200;
const STOP_REQUESTED_RETENTION_MS = 60 * 60 * 1000;

const CHUNK_MAX_BYTES = 512 * 1024;
// Headroom above the server's 12 MiB snapshot limit: the event envelope can
// push a legal snapshot past the assembly ceiling.
const MAX_CHUNK_ASSEMBLY_BYTES = 12 * 1024 * 1024 + 256 * 1024;
// Absolute bound on chunks per transfer; also cross-checked against
// totalBytes so a lying chunkCount can never wedge an assembly.
const MAX_CHUNK_COUNT = 256;
const MAX_CHUNK_ASSEMBLIES = 8;
const CHUNK_ASSEMBLY_TIMEOUT_MS = 30_000;
const MAX_CHUNK_BUFFER_BYTES = 16 * 1024 * 1024;

const DELTA_MAX_OPS = 500;
const DELTA_MAX_BYTES = 256 * 1024;

const MCS_META_KEY = 'multi_client_sync';
const TOMBSTONE_RETENTION_MS = 7 * 24 * 60 * 60 * 1000;

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
const terminalGenerationPhases = new Set(['completed', 'stopped', 'failed', 'terminal']);
const quietGenerationTypes = new Set(['quiet', 'quiet_escape', 'background']);

function normalizeSettings(incoming) {
    const source = incoming && typeof incoming === 'object' ? incoming : {};
    // Malformed persisted values never become program state: anything that is
    // not an explicit boolean falls back to the default.
    const bool = key => (typeof source[key] === 'boolean' ? source[key] : DEFAULT_SETTINGS[key]);
    return {
        enabled: bool('enabled'),
        autoConnect: bool('autoConnect'),
        syncMessages: bool('syncMessages'),
        syncMetadata: bool('syncMetadata'),
        coordinateGeneration: bool('coordinateGeneration'),
        remoteStop: bool('remoteStop'),
        notifications: bool('notifications'),
        debug: bool('debug'),
    };
}

function loadSettings() {
    try {
        return normalizeSettings(JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}'));
    } catch {
        return { ...DEFAULT_SETTINGS };
    }
}

let settings = loadSettings();

let clientId = loadSessionId(CLIENT_KEY);
let deviceId = loadStableId(DEVICE_KEY);
let tabId = crypto.randomUUID();

let ctx = null;
let eventSource = null;
let currentScope = null;
let scopeKeyValue = '';
let scopeEpoch = 0;
// scopeEpoch = distributed connection lifetime.
// nativeLoadEpoch = native ST chat-load lifetime. The two can move
// independently (a reconnect keeps the same native chat; a chat switch can
// race an in-flight reconciliation), so both must be captured and checked.
let nativeLoadEpoch = 0;
let serverState = null;
let baseSnapshot = null;
let applyingRemoteDepth = 0;
let localGeneration = null;
let generationServerReadyId = null;
let generationStartPromise = null;
let generationStartPromiseId = null;
let generationStartRetryTimer = null;
let streamTimer = null;
let streamInFlight = false;
let streamInFlightPromise = null;
let streamAbortController = null;
let remoteRenderTimer = null;
let lastStreamSentAt = 0;
let pendingStream = null;
let terminalizingGenerationId = null;
let scopeRetryTimer = null;
let queueRetryTimer = null;
let terminalRetryTimer = null;
let remoteUiObserver = null;
let remoteUiObservedParent = null;
let remoteUiRefreshTimer = null;
let sseEpoch = 0;
let scopeSwitchChain = Promise.resolve();
let stateApplyChain = Promise.resolve();
// Retain the legacy variable in case another lifecycle path still references
// it, but do not use it to serialize unrelated chats.
let publishChain = Promise.resolve();

const publishChains = new Map();
let nativeRestoreInProgress = false;
let activationInProgress = false;
let joinAbortController = null;
let generationTerminalTimer = null;
let nativeSaveChain = Promise.resolve();
let snapshotMutationChain = Promise.resolve();
let lifecycleChain = Promise.resolve();
const registeredEventHandlers = [];
const registeredUiHandlers = [];
let heartbeatTimer = null;
let generationHeartbeatTimer = null;
let settingsPanelMounted = false;
let bc = null;
// Exact membership connection identity: a delayed /leave or /heartbeat from
// a previous connection must never evict the current membership.
let membershipConnectionId = null;
let localGenerationScope = null;
let localGenerationEpoch = 0;
let localGenerationBaseSnapshot = null;
let localStreamMessageId = null;
let localStreamMessageIndex = null;
let pendingRemoteStream = null;
let remoteGenerationId = null;
let lastRemoteStreamSeq = -1;
let lastSseEventId = 0;
let generationHeartbeatFailures = 0;
let generationHeartbeatInFlight = null;
let generationMismatchSince = 0;
let generationClaimedThisPage = false;
let generationClaimInFlightId = null;
let generationRecoveryInFlight = null;
let localGenerationBaseRevision = 0;
let localGenerationSettings = null;
let lastTerminatedGenerationId = null;
let streamInFlightSeq = 0;
let streamRetryTimer = null;
let streamCaptureTimer = null;
let resyncChain = Promise.resolve();
let resyncInFlight = null;
let resyncInFlightKey = '';
let localPublishTimer = null;
let queueFlushChain = Promise.resolve();
let nativeMembershipHeartbeatInFlight = null;
let nativeHeartbeatRequestSeq = 0;
let nativeHeartbeatAppliedSeq = 0;
let remoteStopInFlight = null;
let remoteStopGenerationId = null;
let remoteStopRequestedAt = 0;
let remoteStopConfirmTimer = null;
let groupWrapperDepth = 0;
let pendingScopeSwitchReason = '';
let manualGenerationRequestAt = 0;
let leaveAfterLocalGeneration = false;
let localDirty = false;
let localDirtyScopeKey = '';
let generationTerminalPhase = null;
let remoteSendButtonState = null;
let storageHandler = null;
let queueSequenceCounter = 0;
let localMutationVersion = 0;
let activeLocalPublishPromise = null;
let activeLocalPublishScopeKey = '';

// Last-synced message fingerprints (id -> 64-bit hash). Hashes, not full
// serialized messages — the map must stay tiny even for huge chats.
let lastSyncedMessageMap = new Map();

const chunkAssemblies = new Map();
let chunkAssemblyTotalBytes = 0;
let sseProcessChain = Promise.resolve();
let sseResyncInProgress = false;

const stopRequestedGenerationIds = new Map();
const terminatedGenerationIds = new Map();
const suppressedRemoteStreamMessageIds = new Set();

function log(...args) {
    if (settings.debug) console.debug('[MCS]', ...args);
}

function warn(...args) {
    console.warn('[MCS]', ...args);
}

function clone(value) {
    if (value === undefined) return undefined;
    try {
        return structuredClone(value);
    } catch {
        try {
            return JSON.parse(JSON.stringify(value));
        } catch (error) {
            // Silently converting application state into null is more
            // dangerous than an explicit failure the caller can catch.
            throw new Error(`MCS clone failed: ${error?.message || 'invalid value'}`);
        }
    }
}

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

function newId() {
    return crypto.randomUUID();
}

function utf8ByteLength(value) {
    if (value === undefined || value === null) return 0;
    return new Blob([JSON.stringify(value)]).size;
}

function stableStringify(value, depth = 0, seen = new WeakSet()) {
    if (depth > 32) throw new Error('MCS serialization depth exceeded');
    if (value && typeof value === 'object') {
        if (seen.has(value)) throw new Error('MCS circular data detected');
        seen.add(value);
        try {
            if (Array.isArray(value)) {
                return `[${value.map(item => stableStringify(item, depth + 1, seen)).join(',')}]`;
            }
            const parts = [];
            for (const key of Object.keys(value).sort()) {
                if (forbiddenKeys.has(key)) continue;
                const val = value[key];
                if (val !== undefined) parts.push(`${JSON.stringify(key)}:${stableStringify(val, depth + 1, seen)}`);
            }
            return `{${parts.join(',')}}`;
        } finally {
            seen.delete(value);
        }
    }
    return JSON.stringify(value) ?? 'null';
}

function deepEqual(a, b) {
    return stableStringify(a) === stableStringify(b);
}

function loadStableId(key) {
    try {
        const saved = localStorage.getItem(key);
        if (saved && /^[A-Za-z0-9._~:-]{1,240}$/.test(saved)) return saved;
    } catch { /* ignore */ }
    const value = crypto.randomUUID();
    try { localStorage.setItem(key, value); } catch { /* ignore */ }
    return value;
}

function loadSessionId(key) {
    try {
        const saved = sessionStorage.getItem(key);
        if (saved && /^[A-Za-z0-9._~:-]{1,240}$/.test(saved)) return saved;
    } catch { /* ignore */ }
    const value = crypto.randomUUID();
    try { sessionStorage.setItem(key, value); } catch { /* ignore */ }
    return value;
}

function saveSettings() {
    try { localStorage.setItem(STORAGE_KEY, JSON.stringify(settings)); } catch { /* ignore */ }
}

function syncEnabled() {
    return !!settings.enabled && !!(settings.syncMessages || settings.syncMetadata);
}

function generationLeaseExpired(generation, graceMs = 5_000) {
    const leaseUntil = Number(generation?.leaseUntil || 0);
    if (!leaseUntil) return false;
    return leaseUntil <= Date.now() - Math.max(0, Number(graceMs) || 0);
}

function generationActive(generation) {
    if (!generation) return false;
    const phase = String(generation.phase || '').toLowerCase();
    if (terminalGenerationPhases.has(phase)) return false;
    return !generationLeaseExpired(generation, 5_000);
}

function generationIsMine(generation) {
    return !!generation && generation.clientId === clientId && generation.deviceId === deviceId;
}

function generationIsStopRequested(generationId) {
    if (!generationId) return false;
    return stopRequestedGenerationIds.has(String(generationId));
}

function rememberStopRequestedGeneration(generationId) {
    if (!generationId) return;
    const id = String(generationId);
    stopRequestedGenerationIds.set(id, Date.now());
    pruneGenerationMarkers();
}

function forgetStopRequestedGeneration(generationId) {
    if (!generationId) return;
    stopRequestedGenerationIds.delete(String(generationId));
}

function rememberTerminatedGeneration(generationId) {
    if (!generationId) return;
    const id = String(generationId);
    terminatedGenerationIds.set(id, Date.now());
    lastTerminatedGenerationId = id;
    pruneGenerationMarkers();
}

function pruneGenerationMarkers() {
    const cutoff = Date.now() - STOP_REQUESTED_RETENTION_MS;
    for (const [id, at] of stopRequestedGenerationIds) {
        if (at < cutoff) stopRequestedGenerationIds.delete(id);
    }
    for (const [id, at] of terminatedGenerationIds) {
        if (at < cutoff) terminatedGenerationIds.delete(id);
    }
    while (stopRequestedGenerationIds.size > 128) {
        const first = stopRequestedGenerationIds.keys().next().value;
        if (first === undefined) break;
        stopRequestedGenerationIds.delete(first);
    }
    while (terminatedGenerationIds.size > 128) {
        const first = terminatedGenerationIds.keys().next().value;
        if (first === undefined) break;
        terminatedGenerationIds.delete(first);
    }
}

function clearGenerationMarkers() {
    stopRequestedGenerationIds.clear();
    terminatedGenerationIds.clear();
    lastTerminatedGenerationId = null;
}

function localGenerationMatches(generationId, scope = null) {
    if (!localGeneration || localGeneration.generationId !== generationId) return false;
    if (scope && makeScopeKey(localGenerationScope) !== makeScopeKey(scope)) return false;
    return true;
}

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

function legacyMessageId(message, index, occurrence) {
    const seed = [
        message?.send_date || '',
        message?.gen_started || '',
        message?.name || '',
        message?.title || '',
        message?.is_user ? 'u' : 'a',
        message?.is_system ? 's' : '',
        occurrence || 0,
        !message?.send_date && !message?.gen_started ? index : '',
    ].join('\u001f');

    let hash = 2166136261;
    for (let i = 0; i < seed.length; i += 1) {
        hash ^= seed.charCodeAt(i);
        hash = Math.imul(hash, 16777619);
    }
    return `legacy-${(hash >>> 0).toString(16).padStart(8, '0')}`;
}

function ensureMessageIds(messages) {
    let changed = false;
    const seen = new Set();
    const occurrences = new Map();

    for (let index = 0; index < messages.length; index += 1) {
        const message = messages[index];
        if (!message || typeof message !== 'object') continue;

        message.extra = message.extra && typeof message.extra === 'object' ? message.extra : {};
        message.extra.multi_client_sync = message.extra.multi_client_sync && typeof message.extra.multi_client_sync === 'object'
            ? message.extra.multi_client_sync
            : {};

        let id = message.extra.multi_client_sync.messageId;
        if (typeof id !== 'string' || !id || seen.has(id)) {
            if (typeof id === 'string' && id && seen.has(id)) {
                warn('[MCS] duplicate message id detected; regenerating to preserve integrity:', id);
            }
            const legacyBase = legacyMessageId(message, index, occurrences.get(legacyMessageId(message, index, 0)) || 0);
            let candidate = legacyBase;
            let suffix = 0;
            while (seen.has(candidate)) {
                suffix += 1;
                candidate = `${legacyBase}-${suffix}`;
            }
            id = candidate;
            occurrences.set(legacyBase, suffix);
            message.extra.multi_client_sync.messageId = id;
            changed = true;
        }
        seen.add(id);
    }

    return changed;
}

function messageId(message) {
    const id = message?.extra?.multi_client_sync?.messageId;
    return typeof id === 'string' ? id : null;
}

function messageSyncMeta(message) {
    return message?.extra?.multi_client_sync || {};
}

function messageLastModified(message) {
    const meta = messageSyncMeta(message);
    const candidates = [
        meta.lastModified,
        message?.send_date,
        message?.gen_started,
        message?.gen_started_at,
    ];

    for (const raw of candidates) {
        if (raw == null) continue;

        const numeric = Number(raw);
        if (Number.isFinite(numeric) && numeric > 0) return numeric;

        if (typeof raw === 'string') {
            const parsed = Date.parse(raw);
            if (Number.isFinite(parsed) && parsed > 0) return parsed;
        }
    }

    return 0;
}

function durableMessages({ persistIds = true } = {}) {
    refreshLiveContext();
    if (persistIds && ctx?.chat && currentScope && nativeScopeStable(currentScope)) {
        ensureMessageIds(ctx.chat);
    }
    return clone(ctx?.chat || []);
}

function durableSnapshot() {
    const messages = durableMessages({ persistIds: true });
    ensureMessageIds(messages);
    return {
        messages,
        metadata: clone(ctx?.chatMetadata || {}),
    };
}

function normalizeSnapshot(snapshot) {
    if (!snapshot || !Array.isArray(snapshot.messages)) {
        return { messages: [], metadata: {} };
    }

    const out = {
        messages: clone(snapshot.messages),
        metadata: safeObject(snapshot.metadata || {}),
    };

    ensureMessageIds(out.messages);
    return out;
}

function syncSnapshot(snapshot) {
    const normalized = normalizeSnapshot(snapshot);
    const syncMessages = localGenerationSettings?.syncMessages ?? settings.syncMessages;
    const syncMetadata = localGenerationSettings?.syncMetadata ?? settings.syncMetadata;
    return {
        messages: syncMessages
            ? clone(normalized.messages)
            : clone(serverState?.snapshot?.messages || durableMessages({ persistIds: false })),
        metadata: syncMetadata
            ? clone(normalized.metadata)
            : clone(serverState?.snapshot?.metadata || ctx?.chatMetadata || {}),
    };
}

function incomingSnapshot(snapshot) {
    const remote = normalizeSnapshot(snapshot);
    return {
        messages: settings.syncMessages
            ? clone(remote.messages)
            : clone(durableMessages({ persistIds: false })),
        metadata: settings.syncMetadata
            ? clone(remote.metadata)
            : clone(ctx?.chatMetadata || {}),
    };
}

function refreshLiveContext() {
    try {
        const fresh = SillyTavern?.getContext?.();
        if (fresh) ctx = fresh;
    } catch { /* keep last usable context */ }
    return ctx;
}

function scopeFromContext() {
    refreshLiveContext();
    if (!ctx) return null;

    const groupId = ctx.groupId !== undefined && ctx.groupId !== null && String(ctx.groupId) !== ''
        ? String(ctx.groupId)
        : '';
    const isGroup = !!groupId;

    let contextChatId = '';
    try {
        if (typeof ctx.getCurrentChatId === 'function') {
            contextChatId = String(ctx.getCurrentChatId() || '').trim();
        }
    } catch { /* ignore */ }

    const contextFieldChatId = ctx.chatId ? String(ctx.chatId).trim() : '';
    const selectedChat = typeof document?.querySelector === 'function'
        ? String(document.querySelector('#selected_chat_pole')?.value || '').trim()
        : '';

    const chatId = isGroup
        ? contextChatId || contextFieldChatId
        : contextChatId || contextFieldChatId || selectedChat;

    if (!chatId) return null;

    let ownerId = '';

    if (isGroup) {
        ownerId = `group:${groupId}`;
        const group = Array.isArray(ctx.groups)
            ? ctx.groups.find(item => String(item?.id) === groupId)
            : null;
        const nativeGroupChat = group?.chat_id ? String(group.chat_id).trim() : '';

        if (!nativeGroupChat || nativeGroupChat !== chatId) {
            log('[MCS] group/chat mismatch:', { groupId, nativeGroupChat, chatId });
            return null;
        }
    } else {
        const characterId = ctx.characterId !== undefined && ctx.characterId !== null
            ? String(ctx.characterId)
            : '';

        let character = characterId && Array.isArray(ctx.characters)
            ? ctx.characters[characterId] || null
            : null;

        if (!character && ctx.name2 && Array.isArray(ctx.characters)) {
            character = ctx.characters.find(item => String(item?.name || '') === String(ctx.name2)) || null;
        }

        const ownerAvatar = character?.avatar ? String(character.avatar) : '';
        const ownerName = character?.name ? String(character.name) : '';
        ownerId = ownerAvatar || ownerName || '';
        if (!ownerId) return null;

        const nativeChat = character?.chat ? String(character.chat).trim() : '';
        if (!nativeChat || nativeChat !== chatId) {
            log('[MCS] character/chat mismatch:', { characterId, nativeChat, chatId, selectedChat });
            return null;
        }
    }

    const metadata = ctx.chatMetadata || {};
    const branchId = metadata?.main_chat ? String(metadata.main_chat) : '';

    return {
        kind: isGroup ? 'group' : 'character',
        ownerId,
        chatId,
        branchId,
    };
}

function nativeScopeStable(expectedScope = currentScope) {
    if (!expectedScope) return false;
    const actual = scopeFromContext();
    return !!actual && makeScopeKey(actual) === makeScopeKey(expectedScope);
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

async function negotiateClientId() {
    if (!bc) return;

    return new Promise(resolve => {
        let done = false;

        const finish = () => {
            if (done) return;
            done = true;
            clearTimeout(timer);
            try { bc.removeEventListener('message', onMessage); } catch { /* ignore */ }
            resolve();
        };

        const onMessage = event => {
            const data = event.data;
            if (!data || data.kind !== 'client-hello') return;
            if (data.clientId !== clientId || data.tabId === tabId) return;

            if (String(tabId) < String(data.tabId)) {
                finish();
                return;
            }

            clientId = crypto.randomUUID();
            try { sessionStorage.setItem(CLIENT_KEY, clientId); } catch { /* ignore */ }
            finish();
        };

        const timer = setTimeout(finish, 100);
        bc.addEventListener('message', onMessage);

        try {
            bc.postMessage({ kind: 'client-hello', clientId, deviceId, tabId });
        } catch {
            finish();
        }
    });
}

async function waitForNativeScope(expectedScope, timeoutMs = 2000, intervalMs = 75) {
    const deadline = Date.now() + Math.max(0, Number(timeoutMs) || 0);

    while (Date.now() <= deadline) {
        refreshLiveContext();
        if (
            currentScope &&
            makeScopeKey(currentScope) === makeScopeKey(expectedScope) &&
            nativeScopeStable(expectedScope)
        ) {
            return true;
        }

        if (Date.now() >= deadline) break;
        await sleep(intervalMs);
    }

    return false;
}

function clearGenerationTerminalTimer() {
    if (generationTerminalTimer) clearTimeout(generationTerminalTimer);
    generationTerminalTimer = null;
}

function clearTerminalRetryTimer() {
    if (terminalRetryTimer) clearTimeout(terminalRetryTimer);
    terminalRetryTimer = null;
}

function scheduleTerminalRetry(generationId, phase, delay = TERMINAL_RETRY_MS) {
    if (!generationId || terminalRetryTimer) return;

    terminalRetryTimer = setTimeout(() => {
        terminalRetryTimer = null;
        if (!localGeneration || localGeneration.generationId !== generationId) return;
        if (terminalizingGenerationId) return;
        void sendGenerationTerminal(phase).catch(error => warn('terminal retry failed', error));
    }, Math.max(250, delay));
}

function scheduleGenerationStartRetry(generationId, delay = 1000) {
    if (!generationId || generationStartRetryTimer) return;

    generationStartRetryTimer = setTimeout(() => {
        generationStartRetryTimer = null;
        if (!localGeneration || localGeneration.generationId !== generationId) return;
        if (generationIsStopRequested(generationId) || terminalizingGenerationId === generationId) return;
        void ensureGenerationStarted().catch(error => warn('generation start retry failed', error));
    }, Math.max(250, delay));
}

function safeSetTimer(fn, delay) {
    return setTimeout(fn, Math.max(0, Number(delay) || 0));
}

function openDb() {
    return new Promise((resolve, reject) => {
        let settled = false;
        const request = indexedDB.open(DB_NAME, DB_VERSION);

        request.onupgradeneeded = () => {
            const db = request.result;
            const tx = request.transaction;
            if (!db.objectStoreNames.contains('ops')) {
                const store = db.createObjectStore('ops', { keyPath: 'id' });
                store.createIndex('scopeKey', 'scopeKey', { unique: false });
            } else {
                const store = tx.objectStore('ops');
                if (!store.indexNames.contains('scopeKey')) {
                    store.createIndex('scopeKey', 'scopeKey', { unique: false });
                }
            }
        };

        request.onblocked = () => warn('[MCS] IndexedDB upgrade blocked by another tab');

        request.onsuccess = () => {
            if (settled) return;
            settled = true;
            const db = request.result;
            db.onversionchange = () => db.close();
            resolve(db);
        };

        request.onerror = () => {
            if (settled) return;
            settled = true;
            reject(request.error || new Error('IndexedDB open failed'));
        };
    });
}

async function idbPut(value) {
    const db = await openDb();

    return new Promise((resolve, reject) => {
        let settled = false;
        const finish = (error = null) => {
            if (settled) return;
            settled = true;
            try { db.close(); } catch { /* ignore */ }
            if (error) reject(error); else resolve();
        };

        try {
            const tx = db.transaction('ops', 'readwrite');
            tx.objectStore('ops').put(value);
            tx.oncomplete = () => finish();
            tx.onerror = () => finish(tx.error || new Error('IndexedDB put failed'));
            tx.onabort = () => finish(tx.error || new Error('IndexedDB transaction aborted'));
        } catch (error) {
            finish(error);
        }
    });
}

async function idbList(scopeKey) {
    const db = await openDb();

    return new Promise((resolve, reject) => {
        let settled = false;
        const finish = (error, value) => {
            if (settled) return;
            settled = true;
            try { db.close(); } catch { /* ignore */ }
            if (error) reject(error); else resolve(value);
        };

        try {
            const tx = db.transaction('ops', 'readonly');
            const req = tx.objectStore('ops').index('scopeKey').getAll(scopeKey);
            req.onsuccess = () => finish(null, req.result
                .map(row => ({
                    ...row,
                    // Migration for rows created before opId became separate
                    // from the stable queue-row key.
                    opId: row.opId || row.id,
                }))
                .sort((a, b) => {
                    if (a.createdAt !== b.createdAt) return a.createdAt - b.createdAt;
                    if ((a.queueSequence || 0) !== (b.queueSequence || 0)) return (a.queueSequence || 0) - (b.queueSequence || 0);
                    return String(a.id).localeCompare(String(b.id));
                }));
            req.onerror = () => finish(req.error || new Error('IndexedDB read failed'));
            tx.onerror = () => finish(tx.error || new Error('IndexedDB transaction failed'));
            tx.onabort = () => finish(tx.error || new Error('IndexedDB transaction aborted'));
        } catch (error) {
            finish(error);
        }
    });
}

async function idbDelete(id) {
    if (!id) return;
    const db = await openDb();

    return new Promise((resolve, reject) => {
        let settled = false;
        const finish = (error = null) => {
            if (settled) return;
            settled = true;
            try { db.close(); } catch { /* ignore */ }
            if (error) reject(error); else resolve();
        };

        try {
            const tx = db.transaction('ops', 'readwrite');
            tx.objectStore('ops').delete(id);
            tx.oncomplete = () => finish();
            tx.onerror = () => finish(tx.error || new Error('IndexedDB delete failed'));
            tx.onabort = () => finish(tx.error || new Error('IndexedDB transaction aborted'));
        } catch (error) {
            finish(error);
        }
    });
}

async function idbClearScope(scopeKey) {
    const rows = await idbList(scopeKey);
    for (const row of rows) await idbDelete(row.id);
}

// ---------------------------------------------------------------------------
// Tombstones / local mutation stamping
// ---------------------------------------------------------------------------

function comparableMessage(message) {
    const copy = clone(message);
    if (copy?.extra?.multi_client_sync) {
        delete copy.extra.multi_client_sync;
        if (Object.keys(copy.extra).length === 0) delete copy.extra;
    }
    return copy;
}

function fnv1a(str, seed) {
    let h = seed;
    for (let i = 0; i < str.length; i += 1) {
        h ^= str.charCodeAt(i);
        h = Math.imul(h, 16777619);
    }
    return h >>> 0;
}

// Canonical string built in-place (no clone of the message), then hashed to
// 16 chars — the last-synced map must never hold a second copy of the chat.
function comparableHash(message) {
    const walk = (value, inExtra) => {
        if (value === null || typeof value !== 'object') {
            return JSON.stringify(value) ?? 'null';
        }
        if (Array.isArray(value)) {
            return `[${value.map(item => walk(item, false)).join(',')}]`;
        }
        const keys = Object.keys(value)
            .filter(key => !forbiddenKeys.has(key))
            .filter(key => !(inExtra && key === MCS_META_KEY))
            .sort();
        const parts = [];
        for (const key of keys) {
            const val = value[key];
            if (val === undefined) continue;
            parts.push(`${JSON.stringify(key)}:${walk(val, key === 'extra' && value === message)}`);
        }
        return `{${parts.join(',')}}`;
    };
    const s = walk(message, false);
    return `${fnv1a(s, 0x811c9dc5).toString(16).padStart(8, '0')}${fnv1a(s, 0x9747b28c).toString(16).padStart(8, '0')}`;
}

// Null-prototype ledger: message IDs are arbitrary strings and must never
// resolve through Object.prototype.
function readLedger(metadata) {
    const meta = metadata?.[MCS_META_KEY];
    const tomb = meta?.tombstones;
    if (!tomb || typeof tomb !== 'object' || Array.isArray(tomb)) return Object.create(null);
    const out = Object.create(null);
    for (const [key, value] of Object.entries(tomb)) {
        if (forbiddenKeys.has(key)) continue;
        const ts = Number(value);
        if (Number.isFinite(ts) && ts > 0) out[key] = ts;
    }
    return out;
}

function rebuildLastSyncedMap(messages) {
    const map = new Map();
    for (const message of messages || []) {
        const id = messageId(message);
        if (!id) continue;
        map.set(id, comparableHash(message));
    }
    lastSyncedMessageMap = map;
}

function chatSyncMetaBucket() {
    refreshLiveContext();
    if (!ctx?.chatMetadata || typeof ctx.chatMetadata !== 'object' || Array.isArray(ctx.chatMetadata)) return null;
    let bucket = ctx.chatMetadata[MCS_META_KEY];
    if (!bucket || typeof bucket !== 'object' || Array.isArray(bucket)) {
        try {
            bucket = {};
            ctx.chatMetadata[MCS_META_KEY] = bucket;
        } catch { return null; }
    }
    return bucket;
}

function stampLocalMutations() {
    refreshLiveContext();
    if (!ctx?.chat || applyingRemoteDepth > 0) return;
    const bucket = chatSyncMetaBucket();
    if (!bucket) return;
    ensureMessageIds(ctx.chat);

    const nowTs = Date.now();
    const currentHashes = new Map();
    const byId = new Map();
    for (const message of ctx.chat) {
        const id = messageId(message);
        if (!id) continue;
        byId.set(id, message);
        currentHashes.set(id, comparableHash(message));
    }

    const tomb = readLedger(ctx.chatMetadata);
    let changed = false;

    for (const id of lastSyncedMessageMap.keys()) {
        if (!Object.hasOwn(currentHashes, id) && !Object.hasOwn(tomb, id)) {
            tomb[id] = nowTs;
            changed = true;
        }
    }

    for (const [id, hash] of currentHashes) {
        const previous = lastSyncedMessageMap.get(id);
        if (previous !== undefined && previous !== hash) {
            const message = byId.get(id);
            if (message) {
                message.extra.multi_client_sync.lastModified = nowTs;
                changed = true;
            }
        }
    }

    const cutoff = nowTs - TOMBSTONE_RETENTION_MS;
    for (const id of Object.keys(tomb)) {
        if (tomb[id] < cutoff || Object.hasOwn(currentHashes, id)) {
            delete tomb[id];
            changed = true;
        }
    }

    if (changed) bucket.tombstones = JSON.parse(JSON.stringify(tomb));
}

// ---------------------------------------------------------------------------
// Chunk reassembly
// ---------------------------------------------------------------------------

function resetChunkAssemblies() {
    chunkAssemblies.clear();
    chunkAssemblyTotalBytes = 0;
}

function pruneExpiredChunkAssemblies() {
    const cutoff = Date.now() - CHUNK_ASSEMBLY_TIMEOUT_MS;
    for (const [key, assembly] of chunkAssemblies) {
        if (assembly.createdAt < cutoff) {
            chunkAssemblyTotalBytes -= assembly.totalBytes;
            chunkAssemblies.delete(key);
            warn('chunk assembly expired; resync will be required', assembly.logicalType, assembly.logicalEventId);
        }
    }
}

function chunkAssemblyKey(scopeKey, transferId) {
    return `${scopeKey}::${transferId}`;
}

function validateChunkEnvelope(data) {
    if (!data || typeof data !== 'object') return 'invalid_envelope';
    if (data.type !== 'event_chunk') return 'not_chunk';
    if (data.transferVersion !== 1) return 'bad_transfer_version';
    if (!Number.isInteger(data.logicalEventId) || data.logicalEventId < 0) return 'bad_logical_event_id';
    if (!Number.isInteger(data.chunkIndex) || data.chunkIndex < 0) return 'bad_chunk_index';
    if (!Number.isInteger(data.chunkCount) || data.chunkCount <= 0) return 'bad_chunk_count';
    if (data.chunkCount > MAX_CHUNK_COUNT) return 'bad_chunk_count';
    if (data.chunkIndex >= data.chunkCount) return 'chunk_index_overflow';
    if (!Number.isInteger(data.totalBytes) || data.totalBytes <= 0 || data.totalBytes > MAX_CHUNK_ASSEMBLY_BYTES) return 'bad_total_bytes';
    // chunkCount must be sufficient to carry totalBytes at the per-chunk cap;
    // a lying count can never wedge an assembly open forever.
    if (Math.ceil(data.totalBytes / CHUNK_MAX_BYTES) > data.chunkCount) return 'bad_chunk_count';
    if (!Number.isInteger(data.chunkBytes) || data.chunkBytes <= 0 || data.chunkBytes > CHUNK_MAX_BYTES) return 'bad_chunk_bytes';
    if (typeof data.eventSha256 !== 'string' || !/^[a-f0-9]{64}$/.test(data.eventSha256)) return 'bad_event_hash';
    if (typeof data.chunkSha256 !== 'string' || !/^[a-f0-9]{64}$/.test(data.chunkSha256)) return 'bad_chunk_hash';
    if (data.encoding !== 'base64') return 'bad_encoding';
    if (typeof data.payload !== 'string' || !data.payload) return 'missing_payload';
    if (typeof data.transferId !== 'string' || !data.transferId) return 'missing_transfer_id';
    return null;
}

async function sha256Hex(buffer) {
    const digest = await crypto.subtle.digest('SHA-256', buffer);
    return Array.from(new Uint8Array(digest)).map(b => b.toString(16).padStart(2, '0')).join('');
}

function base64ToArrayBuffer(base64) {
    const binary = atob(base64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i += 1) bytes[i] = binary.charCodeAt(i);
    return bytes.buffer;
}

// Any throw (bad base64, invalid UTF-8, hash API failure) converts to 'resync'
// so a corrupt chunk can never silently strand the client.
async function handleEventChunk(data) {
    const error = validateChunkEnvelope(data);
    if (error) {
        warn('chunk validation failed', error);
        return null;
    }

    const key = chunkAssemblyKey(scopeKeyValue, data.transferId);

    try {
        let assembly = chunkAssemblies.get(key);

        if (!assembly) {
            pruneExpiredChunkAssemblies();
            if (chunkAssemblies.size >= MAX_CHUNK_ASSEMBLIES || chunkAssemblyTotalBytes + data.totalBytes > MAX_CHUNK_BUFFER_BYTES) {
                warn('chunk assembly budget exceeded');
                return 'resync';
            }
            assembly = {
                logicalEventId: data.logicalEventId,
                logicalType: data.logicalType,
                transferId: data.transferId,
                chunkCount: data.chunkCount,
                totalBytes: data.totalBytes,
                eventSha256: data.eventSha256,
                chunks: new Map(),
                receivedBytes: 0,
                createdAt: Date.now(),
            };
            chunkAssemblies.set(key, assembly);
            chunkAssemblyTotalBytes += assembly.totalBytes;
        }

        const failResync = () => {
            chunkAssemblyTotalBytes -= assembly.totalBytes;
            chunkAssemblies.delete(key);
            return 'resync';
        };

        if (
            assembly.chunkCount !== data.chunkCount ||
            assembly.totalBytes !== data.totalBytes ||
            assembly.eventSha256 !== data.eventSha256 ||
            assembly.transferId !== data.transferId
        ) {
            warn('chunk assembly conflict', data.transferId);
            return failResync();
        }

        const chunkBytes = base64ToArrayBuffer(data.payload);
        if (chunkBytes.byteLength !== data.chunkBytes) {
            warn('chunk byte length mismatch');
            return failResync();
        }
        const chunkHash = await sha256Hex(chunkBytes);
        if (chunkHash !== data.chunkSha256) {
            warn('chunk hash mismatch');
            return failResync();
        }

        // A duplicate chunk index must be byte-identical: a conflicting
        // duplicate is a corrupt transfer, never a silent ignore.
        const existing = assembly.chunks.get(data.chunkIndex);
        if (existing) {
            if (existing.hash === chunkHash) return null;
            warn('conflicting duplicate chunk', data.transferId, data.chunkIndex);
            return failResync();
        }

        assembly.chunks.set(data.chunkIndex, { bytes: chunkBytes, hash: chunkHash });
        assembly.receivedBytes += chunkBytes.byteLength;

        if (assembly.chunks.size < assembly.chunkCount) return null;

        const ordered = [];
        let totalLen = 0;
        for (let i = 0; i < assembly.chunkCount; i += 1) {
            const chunk = assembly.chunks.get(i);
            if (!chunk) { warn('missing chunk after completion', i); return failResync(); }
            ordered.push(chunk.bytes);
            totalLen += chunk.bytes.byteLength;
        }
        if (totalLen !== assembly.totalBytes) { warn('reconstructed byte count mismatch'); return failResync(); }

        const reconstructed = new Uint8Array(totalLen);
        let offset = 0;
        for (const buf of ordered) {
            reconstructed.set(new Uint8Array(buf), offset);
            offset += buf.byteLength;
        }

        const eventHash = await sha256Hex(reconstructed.buffer);
        if (eventHash !== assembly.eventSha256) { warn('whole-event hash mismatch'); return failResync(); }

        const text = new TextDecoder('utf-8', { fatal: true }).decode(reconstructed);
        let logicalEvent;
        try { logicalEvent = JSON.parse(text); } catch (e) { warn('chunked event JSON parse failed', e); return failResync(); }
        if (logicalEvent.type !== assembly.logicalType) { warn('chunked event type mismatch'); return failResync(); }

        chunkAssemblyTotalBytes -= assembly.totalBytes;
        chunkAssemblies.delete(key);

        return logicalEvent;
    } catch (e) {
        warn('chunk processing threw; forcing resync', e);
        const assembly = chunkAssemblies.get(key);
        if (assembly) {
            chunkAssemblyTotalBytes -= assembly.totalBytes;
            chunkAssemblies.delete(key);
        }
        return 'resync';
    }
}

// ---------------------------------------------------------------------------
// SSE processing
//
// Every queued item carries the epoch + scope key it was received under and
// is dropped if the scope changed before processing — an old chat's event can
// never mutate the new chat.
// ---------------------------------------------------------------------------

function connectSse(epoch) {
    disconnectSse();
    if (!currentScope || !currentScopeGuard(epoch)) return;

    const localSseEpoch = sseEpoch;
    const query = `?scope=${encodeURIComponent(encodeScope(currentScope))}&clientId=${encodeURIComponent(clientId)}&deviceId=${encodeURIComponent(deviceId)}&lastEventId=${encodeURIComponent(String(lastSseEventId || 0))}&delta=1`;
    const source = new EventSource(`${PLUGIN_BASE}/events${query}`, { withCredentials: true });
    eventSource = source;

    const listeners = [
        'hello',
        'generation_state',
        'replay_complete',
        'resync_required',
        'snapshot',
        'snapshot_delta',
        'generation_claimed',
        'generation_started',
        'generation_stream',
        'generation_stop_requested',
        'generation_terminal',
        'generation_recovered',
        'event_chunk',
    ];

    for (const type of listeners) {
        source.addEventListener(type, event => handleSseFrame(event, type, localSseEpoch, epoch));
    }

    source.onerror = () => {
        if (!currentScopeGuard(epoch) || localSseEpoch !== sseEpoch) return;
        statusText('Reconnecting…');
    };
}

function handleSseFrame(rawEvent, type, localSseEpoch, epoch) {
    if (!currentScopeGuard(epoch) || localSseEpoch !== sseEpoch) return;

    const eventId = Number(rawEvent.lastEventId || 0);
    let data;
    try { data = JSON.parse(rawEvent.data); } catch (error) {
        warn('bad SSE payload', type, error);
        return;
    }

    if (type === 'event_chunk') {
        enqueueSseLogicalEvent({ kind: 'chunk', eventId, data, epoch, scopeKey: scopeKeyValue });
        return;
    }

    if (type === 'generation_state') {
        enqueueSseLogicalEvent({ kind: 'generation_state', data, epoch, scopeKey: scopeKeyValue });
        return;
    }

    if (type === 'hello') {
        handleServerHello(data);
        return;
    }

    if (eventId > 0 && eventId <= lastSseEventId) return;

    enqueueSseLogicalEvent({ kind: 'logical', logicalType: type, eventId, data, epoch, scopeKey: scopeKeyValue });
}

function enqueueSseLogicalEvent(item) {
    sseProcessChain = sseProcessChain.then(async () => {
        if (sseResyncInProgress) return;
        const result = await processSseLogicalEvent(item);
        if (result === 'resync') {
            sseResyncInProgress = true;
            try {
                await performAuthoritativeResync();
            } catch (error) {
                warn('authoritative resync failed', error);
            } finally {
                sseResyncInProgress = false;
            }
        }
    }).catch(error => warn('SSE process chain failed', error));
}

async function processSseLogicalEvent(item) {
    // Stale item from a previous scope/connection: drop it.
    if (item.scopeKey !== scopeKeyValue || item.epoch !== scopeEpoch) return null;

    if (item.kind === 'chunk') {
        const logicalEvent = await handleEventChunk(item.data);
        if (logicalEvent === 'resync') return 'resync';
        if (!logicalEvent) return null;

        if (logicalEvent.type === 'generation_state') {
            handleGenerationState(logicalEvent);
            return null;
        }

        return processSseLogicalEvent({
            kind: 'logical',
            logicalType: logicalEvent.type,
            eventId: item.eventId,
            data: logicalEvent,
            epoch: item.epoch,
            scopeKey: item.scopeKey,
        });
    }

    if (item.kind === 'generation_state') {
        handleGenerationState(item.data);
        return null;
    }

    if (item.kind !== 'logical') return null;

    const { logicalType, eventId, data } = item;

    const accepted = await dispatchLogicalEvent(logicalType, data);
    if (!accepted) {
        warn('logical event not accepted; resyncing', logicalType, eventId);
        return 'resync';
    }

    if (eventId > 0) lastSseEventId = Math.max(lastSseEventId, eventId);
    return null;
}

async function dispatchLogicalEvent(type, data) {
    try {
        switch (type) {
            case 'replay_complete':
                statusText(`Connected · rev ${data.revision}`);
                return true;
            case 'resync_required':
                return false;
            case 'snapshot':
                return await handleSnapshotEvent(data);
            case 'snapshot_delta':
                return await handleSnapshotDeltaEvent(data);
            case 'generation_claimed':
                handleGenerationEvent(data);
                return true;
            case 'generation_started':
                handleGenerationEvent(data);
                return true;
            case 'generation_stream':
                handleGenerationStreamEvent(data);
                return true;
            case 'generation_stop_requested':
                return await handleRemoteStopEvent(data);
            case 'generation_terminal':
                return await handleGenerationTerminalEvent(data);
            case 'generation_recovered':
                return await handleGenerationRecovered(data);
            default:
                log('ignoring unknown SSE event type', type);
                return true;
        }
    } catch (error) {
        warn('dispatch logical event failed', type, error);
        return false;
    }
}

async function performAuthoritativeResync() {
    disconnectSse();
    try {
        await resyncCurrentScope(scopeEpoch);
    } finally {
        if (currentScope && currentScopeGuard(scopeEpoch)) connectSse(scopeEpoch);
    }
}

function handleGenerationState(data) {
    const generation = data?.generation || null;
    if (!generation || !currentScope) return;
    if (isGenerationTerminated(generation.generationId)) return;
    if (generationIsStopRequested(generation.generationId)) return;

    if (generationIsMine(generation)) {
        if (generationClaimedThisPage || generationClaimInFlightId === generation.generationId) {
            if (generationClaimedThisPage && localGeneration?.generationId === generation.generationId) {
                localGeneration = { ...localGeneration, ...clone(generation) };
            }
            if (['started', 'streaming'].includes(generation.phase)) {
                generationServerReadyId = generation.generationId;
            }
        }
        updateGenerationUi();
        return;
    }

    remoteGenerationId = generation.generationId;
    lastRemoteStreamSeq = Number(generation.seq || 0);
    if (generation.message) {
        pendingRemoteStream = {
            message: clone(generation.message),
            messageIndex: Number.isInteger(generation.messageIndex) ? generation.messageIndex : null,
            generationId: generation.generationId,
            seq: Number(generation.seq || 0),
        };
        scheduleRemoteRender();
    }
    updateGenerationUi();
}

// ---------------------------------------------------------------------------
// API
// ---------------------------------------------------------------------------

// The body is serialized exactly once. The char length is a sufficient
// proxy for the large-request timeout heuristic.
async function api(path, method = 'GET', body = undefined, query = '', options = {}) {
    const bodyText = body === undefined ? undefined : JSON.stringify(body);
    const isLarge = bodyText !== undefined && bodyText.length > 512 * 1024;
    const timeoutMs = Number(
        options.timeoutMs ??
        (path.startsWith('/generation/terminal') ? TERMINAL_API_TIMEOUT_MS :
            path === '/generation/stop' ? STOP_API_TIMEOUT_MS :
            isLarge ? API_TIMEOUT_MS * 3 : API_TIMEOUT_MS),
    );

    const controller = new AbortController();
    let timedOut = false;
    const timeout = setTimeout(() => {
        timedOut = true;
        try { controller.abort(); } catch { /* ignore */ }
    }, Math.max(1000, timeoutMs));

    const parentSignal = options.signal;
    const onParentAbort = () => {
        try { controller.abort(parentSignal?.reason); } catch { /* ignore */ }
    };

    if (parentSignal) {
        if (parentSignal.aborted) onParentAbort();
        else parentSignal.addEventListener('abort', onParentAbort, { once: true });
    }

    const headers = {
        ...(ctx?.getRequestHeaders?.() || { 'Content-Type': 'application/json' }),
    };

    if (method !== 'GET') headers['Content-Type'] = 'application/json';

    try {
        const response = await fetch(
            `${PLUGIN_BASE}${path}${query}`,
            {
                method,
                headers,
                body: bodyText,
                credentials: 'same-origin',
                cache: 'no-cache',
                signal: controller.signal,
                keepalive: !!options.keepalive,
            },
        );

        let payload = null;
        try { payload = await response.json(); } catch { /* no JSON */ }

        if (!response.ok) {
            const err = new Error(payload?.error || `HTTP ${response.status}`);
            err.status = response.status;
            err.payload = payload;
            throw err;
        }

        return payload;
    } catch (error) {
        if (timedOut) {
            const timeoutError = new Error(`Request timed out: ${method} ${path}`);
            timeoutError.name = 'TimeoutError';
            timeoutError.cause = error;
            throw timeoutError;
        }
        throw error;
    } finally {
        clearTimeout(timeout);
        if (parentSignal) {
            try { parentSignal.removeEventListener('abort', onParentAbort); } catch { /* ignore */ }
        }
    }
}

function currentScopeGuard(epoch) {
    return epoch === scopeEpoch && scopeKeyValue === makeScopeKey(currentScope);
}

// Core concurrency invariant: after any await, a destructive operation must
// confirm the distributed epoch, the native scope, AND the native chat-load
// epoch are all unchanged before side effects.
function asyncScopeStillCurrent(epoch, expectedScope, nativeEpoch = null) {
    if (!currentScopeGuard(epoch)) return false;
    if (!currentScope || !expectedScope) return false;
    if (makeScopeKey(currentScope) !== makeScopeKey(expectedScope)) return false;
    if (nativeEpoch != null && nativeLoadEpoch !== nativeEpoch) return false;
    return true;
}

// Compact server responses (generation heartbeat/started/stream/stop, delta
// success) carry no snapshot. Merge them into the existing serverState
// instead of replacing it, so the authoritative snapshot is never lost.
function mergeCompactState(compact) {
    if (!compact) return;
    serverState = { ...(serverState || {}), ...compact };
}

function statusText(text, notify = false) {
    const el = document.getElementById('mcs_status');
    if (el) el.textContent = text;

    const dot = document.getElementById('mcs_status_dot');
    if (dot) {
        dot.classList.remove('mcs-connected', 'mcs-disconnected', 'mcs-disabled', 'mcs-streaming', 'mcs-warning');
        if (/^Connected/.test(text)) dot.classList.add('mcs-connected');
        else if (/^Waiting|^Starting|^Reconnecting|^Stop requested|^Stopping/.test(text)) dot.classList.add('mcs-warning');
        else if (/^Offline|^Protocol mismatch/.test(text)) dot.classList.add('mcs-disconnected');
        else dot.classList.add('mcs-disabled');
    }

    if (notify && settings.notifications && typeof toastr !== 'undefined') {
        toastr.info(text, 'Multi-Client Sync');
    }
}

function renderBanner(text) {
    let el = document.getElementById('mcs_remote_generation_banner');

    if (!text) {
        el?.remove();
        document.body.classList.remove('mcs-remote-streaming');
        return;
    }

    if (!el) {
        el = document.createElement('div');
        el.id = 'mcs_remote_generation_banner';
        document.body.appendChild(el);
    }

    el.textContent = text;
    document.body.classList.add('mcs-remote-streaming');
}

function readInlineVisibilityState(el) {
    if (!el) return null;
    return {
        hidden: !!el.hidden,
        display: el.style.display || '',
        ariaHidden: el.getAttribute('aria-hidden'),
        title: el.getAttribute('title'),
        ariaLabel: el.getAttribute('aria-label'),
        ariaDisabled: el.getAttribute('aria-disabled'),
        role: el.getAttribute('role'),
    };
}

function restoreInlineVisibilityState(el, state) {
    if (!el || !state) return;

    el.hidden = !!state.hidden;

    if (state.display) el.style.display = state.display;
    else el.style.removeProperty('display');

    if (state.ariaHidden == null) el.removeAttribute('aria-hidden');
    else el.setAttribute('aria-hidden', state.ariaHidden);

    if (state.title == null) el.removeAttribute('title');
    else el.setAttribute('title', state.title);

    if (state.ariaLabel == null) el.removeAttribute('aria-label');
    else el.setAttribute('aria-label', state.ariaLabel);

    if (state.ariaDisabled == null) el.removeAttribute('aria-disabled');
    else el.setAttribute('aria-disabled', state.ariaDisabled);

    if (state.role == null) el.removeAttribute('role');
    else el.setAttribute('role', state.role);
}

function nativeShowElement(el) {
    if (!el) return;
    const visible = !el.hidden && getComputedStyle(el).display !== 'none';
    if (!visible) {
        try {
            if (typeof window.jQuery === 'function') window.jQuery(el).show();
            else if (typeof window.$ === 'function') window.$(el).show();
            else {
                el.hidden = false;
                el.style.removeProperty('display');
            }
        } catch {
            el.hidden = false;
            el.style.removeProperty('display');
        }
    }
    if (el.hidden) el.hidden = false;
    if (el.getAttribute('aria-hidden') === 'true') el.removeAttribute('aria-hidden');
}

function nativeHideElement(el) {
    if (!el) return;
    const hidden = el.hidden || getComputedStyle(el).display === 'none';
    if (!hidden) {
        try {
            if (typeof window.jQuery === 'function') window.jQuery(el).hide();
            else if (typeof window.$ === 'function') window.$(el).hide();
            else {
                el.hidden = true;
                el.style.display = 'none';
            }
        } catch {
            el.hidden = true;
            el.style.display = 'none';
        }
    }
    if (!el.hidden) el.hidden = true;
    if (el.getAttribute('aria-hidden') !== 'true') el.setAttribute('aria-hidden', 'true');
}

function installRemoteUiObserver() {
    const send = document.querySelector('#send_but');
    const stop = document.querySelector('#mes_stop');
    const parent = document.querySelector('#rightSendForm') || send?.parentElement || stop?.parentElement || document.body;
    if (!parent) return;

    if (remoteUiObserver && remoteUiObservedParent === parent) return;
    try { remoteUiObserver?.disconnect(); } catch { /* ignore */ }

    remoteUiObserver = new MutationObserver(() => {
        if (!isRemoteGenerationActive()) return;
        if (remoteUiRefreshTimer) return;
        remoteUiRefreshTimer = safeSetTimer(() => {
            remoteUiRefreshTimer = null;
            if (isRemoteGenerationActive()) setRemoteSendButtonMode(true);
        }, 0);
    });

    remoteUiObservedParent = parent;
    // subtree: true — SillyTavern mutates the attributes of the BUTTON nodes,
    // which are children of the observed parent. Without subtree, those
    // mutations are invisible and the observer cannot fight ST's show/hide.
    remoteUiObserver.observe(parent, {
        childList: true,
        subtree: true,
        attributes: true,
        attributeFilter: ['style', 'class', 'hidden', 'aria-hidden'],
    });
}

function uninstallRemoteUiObserver() {
    if (remoteUiRefreshTimer) clearTimeout(remoteUiRefreshTimer);
    remoteUiRefreshTimer = null;

    try { remoteUiObserver?.disconnect(); } catch { /* ignore */ }
    remoteUiObserver = null;
    remoteUiObservedParent = null;
}

function restoreRemoteSendButtonState() {
    if (!remoteSendButtonState) return;

    const send = document.querySelector('#send_but');
    const stop = document.querySelector('#mes_stop');

    if (remoteSendButtonState.sendEl?.isConnected) {
        delete remoteSendButtonState.sendEl.dataset.mcsRemoteStop;
        remoteSendButtonState.sendEl.classList.remove('mcs-remote-stop');
        restoreInlineVisibilityState(
            remoteSendButtonState.sendEl,
            remoteSendButtonState.sendState,
        );
        if (remoteSendButtonState.sendDisabled != null) {
            remoteSendButtonState.sendEl.disabled = remoteSendButtonState.sendDisabled;
        }
    }

    if (remoteSendButtonState.stopEl?.isConnected) {
        delete remoteSendButtonState.stopEl.dataset.mcsRemoteStop;
        remoteSendButtonState.stopEl.classList.remove('mcs-remote-stop');
        restoreInlineVisibilityState(
            remoteSendButtonState.stopEl,
            remoteSendButtonState.stopState,
        );
    }

    if (send && send !== remoteSendButtonState.sendEl && remoteSendButtonState.newSendState) {
        restoreInlineVisibilityState(send, remoteSendButtonState.newSendState);
    }

    if (stop && stop !== remoteSendButtonState.stopEl && remoteSendButtonState.newStopState) {
        restoreInlineVisibilityState(stop, remoteSendButtonState.newStopState);
    }

    remoteSendButtonState = null;
}

function setRemoteSendButtonMode(active) {
    const send = document.querySelector('#send_but');
    const stop = document.querySelector('#mes_stop');

    if (!active) {
        uninstallRemoteUiObserver();
        restoreRemoteSendButtonState();
        return;
    }

    if (!send || !stop) return;

    if (
        !remoteSendButtonState ||
        remoteSendButtonState.sendEl !== send ||
        remoteSendButtonState.stopEl !== stop
    ) {
        restoreRemoteSendButtonState();

        remoteSendButtonState = {
            sendEl: send,
            stopEl: stop,
            sendState: readInlineVisibilityState(send),
            stopState: readInlineVisibilityState(stop),
            sendDisabled: !!send.disabled,
            newSendState: null,
            newStopState: null,
        };
    }

    nativeHideElement(send);
    nativeShowElement(stop);

    stop.setAttribute('role', 'button');
    stop.dataset.mcsRemoteStop = '1';
    stop.classList.add('mcs-remote-stop');

    const stopRequested =
        !!remoteStopGenerationId &&
        serverState?.generation?.generationId === remoteStopGenerationId;

    const stopTitle = stopRequested
        ? 'Stop requested'
        : (remoteSendButtonState.stopState.title || remoteSendButtonState.stopState.ariaLabel || 'Stop generation');

    stop.setAttribute('title', stopTitle);
    stop.setAttribute('aria-label', stopTitle);
    stop.setAttribute('aria-disabled', 'false');
    stop.classList.remove('disabled');

    installRemoteUiObserver();
}

function setSendLock(reason = '') {
    const active = !!reason;
    const remote = isRemoteGenerationActive();
    const selectors = [
        '#send_but',
        '#option_regenerate',
        '#regenerate_last_message',
        '#swipe_right',
        '#swipe_left',
    ];

    for (const selector of selectors) {
        const el = document.querySelector(selector);
        if (!el) continue;

        const lockThisControl =
            active &&
            (selector !== '#send_but' || (remote && !settings.remoteStop));

        if (lockThisControl) {
            if (el.dataset.mcsLocked !== '1') {
                el.dataset.mcsLocked = '1';
                el.dataset.mcsPrevDisabled = el.disabled ? '1' : '0';
                el.dataset.mcsPrevTitle = el.getAttribute('title') || '';
            }

            el.title = reason;
            el.classList.add('disabled');
            if ('disabled' in el) el.disabled = true;
        } else if (selector === '#send_but' && remote && settings.remoteStop) {
            // Remote generation with remote Stop: the send button's visibility
            // is owned EXCLUSIVELY by setRemoteSendButtonMode(). Force-enabling
            // it here fights the hide and produces both buttons visible at
            // once. Do not touch it.
            continue;
        } else if (el.dataset.mcsLocked === '1') {
            delete el.dataset.mcsLocked;
            const wasDisabled = el.dataset.mcsPrevDisabled === '1';
            const previousTitle = el.dataset.mcsPrevTitle || '';
            delete el.dataset.mcsPrevDisabled;
            delete el.dataset.mcsPrevTitle;
            if ('disabled' in el) el.disabled = wasDisabled;
            if (previousTitle) el.setAttribute('title', previousTitle);
            else el.removeAttribute('title');
            el.classList.remove('disabled');
        }
    }

    setRemoteSendButtonMode(remote && settings.remoteStop);
}

function isRemoteGenerationActive() {
    const g = serverState?.generation;
    if (!generationActive(g)) return false;
    if (generationClaimInFlightId && g.generationId === generationClaimInFlightId) return false;
    if (generationIsStaleOwned(g)) return false;
    if (localGeneration && g.generationId === localGeneration.generationId) return false;
    if (generationIsMine(g) && localGeneration) return false;
    return true;
}

function generationIsStaleOwned(generation) {
    return !!generation && generationIsMine(generation) && !generationClaimedThisPage;
}

function markLocalDirty(scope = currentScope) {
    const key = makeScopeKey(scope);
    if (!key) return;
    localDirty = true;
    localDirtyScopeKey = key;
}

function clearLocalDirty(scope = currentScope) {
    const key = makeScopeKey(scope);
    if (!key || localDirtyScopeKey === key) {
        localDirty = false;
        localDirtyScopeKey = '';
    }
}

function isLocalDirty(scope = currentScope) {
    const key = makeScopeKey(scope);
    return !!key && localDirty && localDirtyScopeKey === key;
}

function clearLocalGenerationState() {
    localGeneration = null;
    localGenerationScope = null;
    localGenerationBaseSnapshot = null;
    generationClaimedThisPage = false;
    generationServerReadyId = null;
    generationStartPromise = null;
    generationStartPromiseId = null;
    generationHeartbeatFailures = 0;
    generationHeartbeatInFlight = null;
    generationMismatchSince = 0;
    generationClaimInFlightId = null;
    generationRecoveryInFlight = null;
    localGenerationBaseRevision = 0;
    localGenerationSettings = null;
    streamInFlightSeq = 0;
    localStreamMessageId = null;
    localStreamMessageIndex = null;
    generationTerminalPhase = null;
    remoteStopInFlight = null;
    remoteStopGenerationId = null;
    remoteStopRequestedAt = 0;
    pendingScopeSwitchReason = pendingScopeSwitchReason || '';
    manualGenerationRequestAt = 0;
    groupWrapperDepth = 0;

    if (generationStartRetryTimer) clearTimeout(generationStartRetryTimer);
    if (generationTerminalTimer) clearTimeout(generationTerminalTimer);
    if (terminalRetryTimer) clearTimeout(terminalRetryTimer);
    if (streamTimer) clearTimeout(streamTimer);
    if (streamRetryTimer) clearTimeout(streamRetryTimer);
    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);
    if (remoteStopConfirmTimer) clearTimeout(remoteStopConfirmTimer);

    generationStartRetryTimer = null;
    generationTerminalTimer = null;
    terminalRetryTimer = null;
    streamTimer = null;
    streamRetryTimer = null;
    streamCaptureTimer = null;
    remoteStopConfirmTimer = null;

    pendingStream = null;
    streamInFlight = false;
    streamInFlightPromise = null;
    terminalizingGenerationId = null;
    lastRemoteStreamSeq = -1;
    suppressedRemoteStreamMessageIds.clear();
    stopGenerationHeartbeat();
}

function clearRemoteStreamState() {
    if (remoteRenderTimer) clearTimeout(remoteRenderTimer);
    remoteRenderTimer = null;
    pendingRemoteStream = null;
    remoteGenerationId = null;
    lastRemoteStreamSeq = -1;
    suppressedRemoteStreamMessageIds.clear();
}

// Bounded-depth three-way metadata merge: depth capping prevents pathological
// (or hostile) nesting from blowing the stack; semantics are unchanged.
function mergeMetadata(base, local, remote, depth = 0) {
    if (depth > 32) return clone(remote);
    if (deepEqual(local, base)) return clone(remote);
    if (deepEqual(remote, base)) return clone(local);
    if (deepEqual(local, remote)) return clone(local);

    if (Array.isArray(local) || Array.isArray(remote) || Array.isArray(base)) {
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

        if (deepEqual(l, b)) out[key] = clone(r);
        else if (deepEqual(r, b)) out[key] = clone(l);
        else if (l && r && typeof l === 'object' && typeof r === 'object') out[key] = mergeMetadata(b, l, r, depth + 1);
        else out[key] = clone(r);
    }

    return out;
}

function messageStableKey(message) {
    const date = message?.send_date || message?.gen_started || '';
    const role = `${message?.is_user ? 'u' : 'a'}:${message?.is_system ? 's' : 'n'}`;
    const name = String(message?.name || '');
    if (date) return `time:${date}|role:${role}|name:${name}`;

    const seed = stableStringify({
        name,
        title: message?.title || '',
        role,
        mes: message?.mes || '',
    });

    let hash = 2166136261;
    for (let i = 0; i < seed.length; i += 1) {
        hash ^= seed.charCodeAt(i);
        hash = Math.imul(hash, 16777619);
    }
    return `content:${(hash >>> 0).toString(16)}`;
}

function messageIdentityList(messages) {
    const counts = new Map();
    return messages.map(message => {
        const durableId = messageId(message);
        if (durableId) return `id:${durableId}`;

        const base = messageStableKey(message);
        const occurrence = counts.get(base) || 0;
        counts.set(base, occurrence + 1);
        return `${base}#${occurrence}`;
    });
}

function messagesEqual(a, b) {
    return deepEqual(comparableMessage(a), comparableMessage(b));
}

function orderMergedMessages(baseMessages, localMessages, remoteMessages, chosenMessages) {
    const arrays = [remoteMessages, localMessages, baseMessages];
    const arrayIdentities = arrays.map(messageIdentityList);
    const chosenIds = new Set(messageIdentityList(chosenMessages));
    const rank = new Map();
    let rankValue = 0;

    for (const identities of arrayIdentities) {
        for (const id of identities) {
            if (!rank.has(id) && chosenIds.has(id)) rank.set(id, rankValue);
            rankValue += 1;
        }
    }

    const adjacency = new Map();
    const indegree = new Map();
    for (const id of chosenIds) {
        adjacency.set(id, new Set());
        indegree.set(id, 0);
    }

    for (const identities of arrayIdentities) {
        let previous = null;
        for (const id of identities) {
            if (!chosenIds.has(id)) continue;
            if (previous && previous !== id && !adjacency.get(previous).has(id)) {
                adjacency.get(previous).add(id);
                indegree.set(id, indegree.get(id) + 1);
            }
            previous = id;
        }
    }

    const selected = new Set();
    const orderedIds = [];

    while (orderedIds.length < chosenIds.size) {
        const candidates = [...chosenIds]
            .filter(id => !selected.has(id) && (indegree.get(id) || 0) === 0)
            .sort((a, b) => (rank.get(a) ?? Number.MAX_SAFE_INTEGER) - (rank.get(b) ?? Number.MAX_SAFE_INTEGER));

        let next = candidates[0];
        if (!next) {
            next = [...chosenIds]
                .filter(id => !selected.has(id))
                .sort((a, b) => (rank.get(a) ?? Number.MAX_SAFE_INTEGER) - (rank.get(b) ?? Number.MAX_SAFE_INTEGER))[0];
        }
        if (!next) break;

        selected.add(next);
        orderedIds.push(next);

        for (const child of adjacency.get(next) || []) {
            indegree.set(child, Math.max(0, indegree.get(child) - 1));
        }
    }

    const chosenIdentities = messageIdentityList(chosenMessages);
    const byId = new Map();
    for (let i = 0; i < chosenMessages.length; i += 1) byId.set(chosenIdentities[i], chosenMessages[i]);

    return orderedIds.map(id => clone(byId.get(id))).filter(Boolean);
}

function mergeSnapshots(base, local, remote) {
    const b = normalizeSnapshot(base);
    const l = normalizeSnapshot(local);
    const r = normalizeSnapshot(remote);

    const bIds = messageIdentityList(b.messages);
    const lIds = messageIdentityList(l.messages);
    const rIds = messageIdentityList(r.messages);
    const bm = new Map(bIds.map((id, i) => [id, b.messages[i]]));
    const lm = new Map(lIds.map((id, i) => [id, l.messages[i]]));
    const rm = new Map(rIds.map((id, i) => [id, r.messages[i]]));

    const localTomb = readLedger(l.metadata);
    const remoteTomb = readLedger(r.metadata);
    const baseTomb = readLedger(b.metadata);

    const mergedTomb = Object.create(null);
    for (const source of [baseTomb, localTomb, remoteTomb]) {
        for (const [id, ts] of Object.entries(source)) {
            if (!Object.hasOwn(mergedTomb, id) || ts > mergedTomb[id]) mergedTomb[id] = ts;
        }
    }

    const ids = new Set([...bm.keys(), ...lm.keys(), ...rm.keys()]);
    const chosen = [];
    const chosenDurableIds = new Set();

    for (const id of ids) {
        const bv = bm.get(id);
        const lv = lm.get(id);
        const rv = rm.get(id);

        const mid = id.startsWith('id:') ? id.slice(3) : null;
        const lt = mid ? (Object.hasOwn(localTomb, mid) ? localTomb[mid] : null) : null;
        const rt = mid ? (Object.hasOwn(remoteTomb, mid) ? remoteTomb[mid] : null) : null;

        let value = null;

        if (lt && rt) {
            value = null;
        } else if (lt && rv) {
            value = messageLastModified(rv) > lt ? rv : null;
        } else if (rt && lv) {
            value = messageLastModified(lv) > rt ? lv : null;
        } else if (!lv && !rv) {
            value = null;
        } else if (!lv && bv) {
            value = messagesEqual(rv, bv) ? null : rv;
        } else if (!rv && bv) {
            value = messagesEqual(lv, bv) ? null : lv;
        } else if (!lv) {
            value = rv;
        } else if (!rv) {
            value = lv;
        } else if (messagesEqual(lv, bv)) {
            value = rv;
        } else if (messagesEqual(rv, bv)) {
            value = lv;
        } else if (messagesEqual(lv, rv)) {
            value = rv;
        } else {
            const localTime = messageLastModified(lv);
            const remoteTime = messageLastModified(rv);
            value = localTime > remoteTime ? lv : rv;
        }

        if (value) {
            const out = clone(value);
            const preferredId = messageId(rv) || messageId(lv) || messageId(bv) || newId();
            out.extra = out.extra && typeof out.extra === 'object' ? out.extra : {};
            out.extra.multi_client_sync = out.extra.multi_client_sync && typeof out.extra.multi_client_sync === 'object'
                ? out.extra.multi_client_sync
                : {};
            out.extra.multi_client_sync.messageId = preferredId;
            chosen.push(out);
            chosenDurableIds.add(preferredId);
        }
    }

    const cutoff = Date.now() - TOMBSTONE_RETENTION_MS;
    for (const id of Object.keys(mergedTomb)) {
        if (chosenDurableIds.has(id) || mergedTomb[id] < cutoff) delete mergedTomb[id];
    }

    const stripMeta = meta => {
        const copy = clone(meta || {});
        delete copy[MCS_META_KEY];
        return copy;
    };
    let metadata = mergeMetadata(stripMeta(b.metadata), stripMeta(l.metadata), stripMeta(r.metadata));
    if (Object.keys(mergedTomb).length) {
        metadata = {
            ...metadata,
            [MCS_META_KEY]: { ...(metadata[MCS_META_KEY] || {}), tombstones: JSON.parse(JSON.stringify(mergedTomb)) },
        };
    }

    return {
        messages: orderMergedMessages(b.messages, l.messages, r.messages, chosen),
        metadata,
    };
}

async function safeNativeSave(expectedScope = currentScope) {
    const run = nativeSaveChain.then(async () => {
        refreshLiveContext();
        if (nativeRestoreInProgress || !ctx || !expectedScope) return false;
        if (localGeneration && makeScopeKey(localGenerationScope) === makeScopeKey(expectedScope)) return false;
        if (!nativeScopeStable(expectedScope)) return false;
        // A save belonging to a previously loaded chat must never land after
        // a chat transition.
        const nativeLoadEpochAtSave = nativeLoadEpoch;

        let chatId = '';
        try {
            chatId = String(ctx.getCurrentChatId?.() || ctx.chatId || '').trim();
        } catch {
            chatId = String(ctx.chatId || '').trim();
        }
        if (!chatId || chatId !== String(expectedScope.chatId || '')) return false;

        if (expectedScope.kind === 'group') {
            const groupId = String(expectedScope.ownerId || '').replace(/^group:/, '');
            const group = Array.isArray(ctx.groups)
                ? ctx.groups.find(item => String(item?.id) === groupId)
                : null;
            if (String(group?.chat_id || '').trim() !== chatId) return false;
        } else {
            const characterId = String(ctx.characterId ?? '');
            let character = Array.isArray(ctx.characters)
                ? ctx.characters[characterId]
                : null;
            if (!character && ctx.name2 && Array.isArray(ctx.characters)) {
                character = ctx.characters.find(item => String(item?.name || '') === String(ctx.name2)) || null;
            }
            if (String(character?.chat || '').trim() !== chatId) return false;
        }

        if (expectedScope.kind === 'group') return false;

        await sleep(50);
        if (nativeLoadEpochAtSave !== nativeLoadEpoch) return false;
        if (!nativeScopeStable(expectedScope)) return false;

        try {
            await ctx.saveChat?.();
            return true;
        } catch (error) {
            warn('native chat save failed', error);
            return false;
        }
    });

    nativeSaveChain = run.then(() => undefined, error => warn('native save chain failed', error));
    return run;
}

// Rollback-safe: the previous chat/metadata are captured before mutation, and
// the restore in finally runs ONLY if the native scope is still the one that
// was mutated. If the user switched chats mid-apply, ctx.chat now points at a
// different chat and restoring here would corrupt it.
async function applySnapshotNow(
    snapshot,
    {
        save = false,
        render = true,
        expectedScope = currentScope,
        clearDirty = true,
        allowDuringGeneration = false,
        expectedGenerationId = null,
    } = {},
) {
    const normalized = normalizeSnapshot(snapshot);
    if (!ctx || !expectedScope || !nativeScopeStable(expectedScope)) {
        log('[MCS] refused snapshot apply because native scope is not stable', expectedScope);
        return false;
    }

    const expectedKey = makeScopeKey(expectedScope);
    const epochAtStart = scopeEpoch;
    const nativeLoadEpochAtStart = nativeLoadEpoch;

    if (expectedGenerationId) {
        const expectedId = String(expectedGenerationId);
        const currentLocalId = localGeneration?.generationId || null;
        const currentServerId = serverState?.generation?.generationId || null;
        if (currentLocalId && currentLocalId !== expectedId) return false;
        if (currentServerId && currentServerId !== expectedId) return false;
    }

    if (!allowDuringGeneration && (localGeneration || generationActive(serverState?.generation))) {
        log('[MCS] refused snapshot apply during active generation');
        return false;
    }

    applyingRemoteDepth += 1;

    let previousMessages = null;
    let previousMetadata = null;
    let applied = false;

    try {
        refreshLiveContext();
        if (!currentScope || makeScopeKey(currentScope) !== expectedKey || !nativeScopeStable(expectedScope)) return false;

        if (!Array.isArray(ctx.chat)) return false;
        previousMessages = clone(ctx.chat);
        previousMetadata = ctx.chatMetadata && typeof ctx.chatMetadata === 'object' ? clone(ctx.chatMetadata) : {};

        ctx.chat.splice(0, ctx.chat.length, ...clone(normalized.messages));

        if (ctx.chatMetadata && typeof ctx.chatMetadata === 'object') {
            for (const key of Object.keys(ctx.chatMetadata)) delete ctx.chatMetadata[key];
            Object.assign(ctx.chatMetadata, clone(normalized.metadata));
        }

        if (render) {
            try {
                await Promise.resolve(ctx.printMessages?.());
            } catch (error) {
                log('printMessages failed', error);
                throw error;
            }
        }

        if (
            save &&
            epochAtStart === scopeEpoch &&
            nativeLoadEpochAtStart === nativeLoadEpoch &&
            !nativeRestoreInProgress &&
            nativeScopeStable(expectedScope) &&
            makeScopeKey(currentScope) === expectedKey
        ) {
            const saved = await safeNativeSave(expectedScope);
            if (!saved) throw new Error('native_save_failed');
        }

        if (clearDirty) clearLocalDirty(expectedScope);
        applied = true;
        rebuildLastSyncedMap(normalized.messages);
        return true;
    } catch (error) {
        warn('applySnapshotNow failed', error);
        applied = false;
        return false;
    } finally {
        applyingRemoteDepth -= 1;
        if (!applied && previousMessages && ctx) {
            if (
                scopeEpoch === epochAtStart &&
                nativeLoadEpochAtStart === nativeLoadEpoch &&
                currentScope &&
                makeScopeKey(currentScope) === expectedKey
            ) {
                try {
                    ctx.chat.splice(0, ctx.chat.length, ...previousMessages);
                    if (ctx.chatMetadata && typeof ctx.chatMetadata === 'object') {
                        for (const key of Object.keys(ctx.chatMetadata)) delete ctx.chatMetadata[key];
                        Object.assign(ctx.chatMetadata, previousMetadata);
                    }
                    try { ctx.printMessages?.(); } catch { /* best effort restore */ }
                } catch (restoreError) {
                    warn('applySnapshotNow rollback failed', restoreError);
                }
            } else {
                warn('[MCS] skipped snapshot rollback because the native scope changed during apply');
            }
        }
    }
}

function applySnapshot(snapshot, options = {}) {
    const run = snapshotMutationChain.then(() => applySnapshotNow(snapshot, options));
    snapshotMutationChain = run.then(() => undefined, error => warn('snapshot mutation failed', error));
    return run;
}

async function ensureIdsPersisted(expectedScope = currentScope) {
    refreshLiveContext();

    if (
        !ctx?.chat ||
        !Array.isArray(ctx.chat) ||
        !expectedScope ||
        !nativeScopeStable(expectedScope)
    ) {
        return false;
    }

    // Existing chats can briefly expose an empty/incomplete in-memory chat
    // while ST is still finishing the native file load. Never persist that
    // transient state and risk triggering ST's integrity overwrite protection.
    if (
        expectedScope.chatId &&
        ctx.chat.length === 0
    ) {
        log(
            '[MCS] refusing to persist message IDs while an existing chat is transiently empty',
            expectedScope,
        );
        return false;
    }

    const changed = ensureMessageIds(ctx.chat);

    if (changed) {
        // Re-check the native scope immediately before saving. A chat switch
        // can happen while ensureMessageIds()/other async work is in flight.
        refreshLiveContext();

        if (
            !nativeScopeStable(expectedScope)
        ) {
            markLocalDirty(expectedScope);
            return false;
        }

        const saved =
            await safeNativeSave(
                expectedScope,
            );

        if (!saved) {
            markLocalDirty(expectedScope);
        }
    }

    return true;
}

// ---------------------------------------------------------------------------
// Delta fast path
// ---------------------------------------------------------------------------

function stripDeltaMetadata(metadata) {
    const copy = clone(metadata || {});
    delete copy[MCS_META_KEY];
    return copy;
}

// One live-chat scan producing the minimal op set. fallback:true whenever the
// change isn't safely expressible as a small delta.
function computeDeltaOpsFromLiveChat() {
    refreshLiveContext();
    if (!ctx?.chat || !serverState?.snapshot) return { fallback: true, reason: 'no_state' };
    if (!settings.syncMessages) return { fallback: true, reason: 'message_sync_disabled' };
    if (localGeneration || generationActive(serverState?.generation)) return { fallback: true, reason: 'generation_active' };

    ensureMessageIds(ctx.chat);

    const baseMessages = serverState.snapshot.messages || [];
    const baseById = new Map();
    for (const message of baseMessages) {
        const id = messageId(message);
        if (id) baseById.set(id, message);
    }

    const localIds = new Set();
    for (const message of ctx.chat) {
        const id = messageId(message);
        if (!id) return { fallback: true, reason: 'missing_message_id' };
        localIds.add(id);
    }

    const deletedIds = new Set();
    for (const id of baseById.keys()) {
        if (!localIds.has(id)) deletedIds.add(id);
    }

    // Each surviving base message's previous surviving neighbour — so a
    // deletion is never mistaken for a cascade of moves.
    const basePrevious = new Map();
    let previousBaseId = null;
    for (const message of baseMessages) {
        const id = messageId(message);
        if (!id || deletedIds.has(id)) continue;
        basePrevious.set(id, previousBaseId);
        previousBaseId = id;
    }

    const bucket = chatSyncMetaBucket();
    const tombstones = bucket ? readLedger(ctx.chatMetadata) : Object.create(null);
    const nowTs = Date.now();
    const ops = [];
    let previousLocalId = null;

    for (const message of ctx.chat) {
        const id = messageId(message);
        const base = baseById.get(id);
        const currentHash = comparableHash(message);
        const previouslySynced = lastSyncedMessageMap.get(id);

        const changed = !base || previouslySynced === undefined || previouslySynced !== currentHash;
        if (changed) {
            const meta = message.extra.multi_client_sync;
            let modifiedAt = Number(meta.lastModified || 0);
            if (!modifiedAt) {
                modifiedAt = nowTs;
                meta.lastModified = modifiedAt;
            }
            const upsert = { op: 'upsert', message: clone(message), modifiedAt };
            // New messages need an explicit insertion anchor.
            if (!base) upsert.afterMessageId = previousLocalId;
            ops.push(upsert);
        }

        // Existing message whose actual predecessor changed = a real move.
        if (base && basePrevious.get(id) !== previousLocalId) {
            ops.push({ op: 'move', messageId: id, afterMessageId: previousLocalId });
        }

        previousLocalId = id;
    }

    // Deletes last: anchors used by surviving messages already exist when applied.
    for (const id of deletedIds) {
        let deletedAt = Object.hasOwn(tombstones, id) ? Number(tombstones[id]) : 0;
        if (!deletedAt) {
            deletedAt = nowTs;
            tombstones[id] = deletedAt;
        }
        ops.push({ op: 'delete', messageId: id, deletedAt });
    }

    if (bucket) bucket.tombstones = JSON.parse(JSON.stringify(tombstones));

    if (settings.syncMetadata && !deepEqual(
        stripDeltaMetadata(ctx.chatMetadata || {}),
        stripDeltaMetadata(serverState.snapshot.metadata || {}),
    )) {
        return { fallback: true, reason: 'metadata_changed' };
    }

    if (!ops.length) return { fallback: false, ops: [] };
    if (ops.length > DELTA_MAX_OPS) return { fallback: true, reason: 'too_many_ops' };
    if (utf8ByteLength({ ops }) > DELTA_MAX_BYTES) return { fallback: true, reason: 'delta_too_large' };

    return { fallback: false, ops };
}

function writeDeltaTombstonesClient(metadata, tombstones) {
    const out = clone(metadata || {});
    if (!Object.keys(tombstones).length) {
        if (out[MCS_META_KEY]?.tombstones) {
            delete out[MCS_META_KEY].tombstones;
            if (out[MCS_META_KEY] && Object.keys(out[MCS_META_KEY]).length === 0) delete out[MCS_META_KEY];
        }
        return out;
    }
    out[MCS_META_KEY] = { ...(out[MCS_META_KEY] || {}), tombstones: JSON.parse(JSON.stringify(tombstones)) };
    return out;
}

// Client-side mirror of the server projector: identical op semantics,
// including stale-tombstone rejection.
function applyDeltaToSnapshotFast(baseSnapshot, ops) {
    const messages = Array.isArray(baseSnapshot?.messages) ? baseSnapshot.messages.slice() : [];
    let metadata = baseSnapshot?.metadata || {};
    let metadataChanged = false;
    const tombstones = readLedger(metadata);
    const ensureMetadataCopy = () => {
        if (metadataChanged) return;
        metadata = clone(metadata);
        metadataChanged = true;
    };
    const reindex = () => {
        const map = new Map();
        for (let i = 0; i < messages.length; i += 1) {
            const id = messageId(messages[i]);
            if (id) map.set(id, i);
        }
        return map;
    };
    let indexById = reindex();

    for (const op of ops) {
        if (op.op === 'delete') {
            const id = String(op.messageId);
            const index = indexById.get(id);
            if (index !== undefined) {
                messages.splice(index, 1);
                indexById = reindex();
            }
            ensureMetadataCopy();
            const deletedAt = Number(op.deletedAt || Date.now());
            if (!Number.isFinite(deletedAt) || deletedAt <= 0) throw new Error('invalid_delete_timestamp');
            if (!Object.hasOwn(tombstones, id) || deletedAt > tombstones[id]) tombstones[id] = deletedAt;
            continue;
        }

        if (op.op === 'upsert') {
            const message = clone(op.message);
            const id = messageId(message);
            const modifiedAt = Number(op.modifiedAt || Date.now());
            if (!id) throw new Error('message_ids_required');
            if (!Number.isFinite(modifiedAt) || modifiedAt <= 0) throw new Error('invalid_modified_timestamp');
            if (Object.hasOwn(tombstones, id) && modifiedAt <= tombstones[id]) throw new Error('delta_stale_message');

            const existing = indexById.get(id);
            if (existing !== undefined) {
                messages[existing] = message;
            } else {
                const afterId = op.afterMessageId == null ? null : String(op.afterMessageId);
                let insertAt = 0;
                if (afterId) {
                    const afterIndex = indexById.get(afterId);
                    if (afterIndex === undefined) throw new Error('delta_anchor_missing');
                    insertAt = afterIndex + 1;
                }
                messages.splice(insertAt, 0, message);
                indexById = reindex();
            }
            if (Object.hasOwn(tombstones, id)) {
                ensureMetadataCopy();
                delete tombstones[id];
            }
            continue;
        }

        if (op.op === 'move') {
            const id = String(op.messageId);
            const currentIndex = indexById.get(id);
            if (currentIndex === undefined) throw new Error('delta_move_target_missing');
            const afterId = op.afterMessageId == null ? null : String(op.afterMessageId);
            if (afterId === id) throw new Error('delta_move_self');
            const moved = messages[currentIndex];
            messages.splice(currentIndex, 1);
            indexById = reindex();
            let insertAt = 0;
            if (afterId) {
                const afterIndex = indexById.get(afterId);
                if (afterIndex === undefined) throw new Error('delta_move_anchor_missing');
                insertAt = afterIndex + 1;
            }
            messages.splice(insertAt, 0, moved);
            indexById = reindex();
        }
    }

    if (metadataChanged) metadata = writeDeltaTombstonesClient(metadata, tombstones);
    return { messages, metadata };
}

function recordRemoteTombstone(id, timestamp = Date.now()) {
    if (!id) return;
    const bucket = chatSyncMetaBucket();
    if (!bucket) return;
    const tombstones = readLedger(ctx.chatMetadata);
    const ts = Number(timestamp);
    if (!Object.hasOwn(tombstones, id) || ts > tombstones[id]) tombstones[id] = ts;
    bucket.tombstones = JSON.parse(JSON.stringify(tombstones));
}

// Try a cheap delta publish first. Result {ok, fallback, abandoned, ambiguous}:
// - ok: committed (or proven already committed)
// - fallback: delta unsuitable or definitively conflicted — caller falls back
//   to the full snapshot path with a NEW opId (different payload ⇒ new op)
// - ambiguous: outcome unknown — a durable full-snapshot retry carrying the
//   ORIGINAL delta opId has been queued; caller must not issue anything new
// - abandoned: scope changed mid-flight
async function publishLocalDelta({ scope = currentScope, opId, mutationVersion } = {}) {
    if (!scope || !settings.enabled || !syncEnabled()) return { ok: false, fallback: true };
    if (!nativeScopeStable(scope)) return { ok: false, fallback: true };
    if (!serverState?.snapshot) return { ok: false, fallback: true };

    const computed = computeDeltaOpsFromLiveChat();
    if (computed.fallback) return { ok: false, fallback: true, reason: computed.reason };

    const ops = computed.ops;
    if (!ops.length) {
        if (mutationVersion === localMutationVersion) {
            clearLocalDirty(scope);
            rebuildLastSyncedMap(serverState.snapshot.messages);
        }
        return { ok: true, fallback: false };
    }

    const scopeAtPublish = clone(scope);
    const scopeKeyAtPublish = makeScopeKey(scopeAtPublish);
    const baseRevision = Number(serverState.revision || 0);
    const localOpId = opId || newId();

    // Project the accepted ops locally so the compact response is enough.
    const projected = applyDeltaToSnapshotFast(serverState.snapshot, ops);

    for (let attempt = 0; attempt < 3; attempt += 1) {
        try {
            const result = await api('/delta', 'POST', {
                scope: scopeAtPublish,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
                opId: localOpId,
                baseRevision,
                ops,
            });

            if (scopeKeyValue !== scopeKeyAtPublish || !currentScope || makeScopeKey(currentScope) !== scopeKeyAtPublish) {
                return { ok: false, abandoned: true };
            }

            // Duplicate: the delta response is compact, so confirm against
            // the authoritative state before deciding anything.
            if (result.duplicate) {
                const confirmation = await api('/state', 'POST', {
                    scope: scopeAtPublish,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                }).catch(() => null);

                const authoritative = confirmation?.state || null;
                if (!authoritative) return { ok: false, fallback: false, ambiguous: true };

                serverState = authoritative;
                baseSnapshot = clone(authoritative.snapshot);

                if (deepEqual(authoritative.snapshot, projected)) {
                    if (mutationVersion === localMutationVersion) {
                        clearLocalDirty(scopeAtPublish);
                        rebuildLastSyncedMap(authoritative.snapshot.messages);
                    }
                    return { ok: true, fallback: false };
                }

                // Original delta committed and the server has since moved on.
                // Any further publish is a NEW logical operation.
                return { ok: false, fallback: true, conflict: true };
            }

            serverState = {
                ...(serverState || {}),
                ...(result.state || {}),
                revision: Number(result.state?.revision ?? baseRevision + 1),
                snapshot: projected,
            };
            baseSnapshot = projected;

            if (Number(result.deltaEventId || 0) > 0) {
                lastSseEventId = Math.max(lastSseEventId, Number(result.deltaEventId));
            }

            if (mutationVersion === localMutationVersion) {
                clearLocalDirty(scopeAtPublish);
                rebuildLastSyncedMap(projected.messages);
            }
            return { ok: true, fallback: false };
        } catch (error) {
            if (scopeKeyValue !== scopeKeyAtPublish) return { ok: false, abandoned: true };

            if (error?.status === 409 && error?.payload?.state) {
                serverState = error.payload.state;
                baseSnapshot = clone(error.payload.state.snapshot);
                // Definitive conflict: caller uses the full merge path, new opId.
                return { ok: false, fallback: true, conflict: true };
            }

            if (error?.status === 413 || error?.payload?.error === 'delta_too_large') {
                return { ok: false, fallback: true };
            }

            // Timeout/network = UNKNOWN outcome. Retry the SAME opId.
            if (attempt < 2) {
                await sleep(100 * (attempt + 1));
                continue;
            }
        }
    }

    // Repeated ambiguous failures: confirm against authoritative state.
    try {
        const confirmation = await api('/state', 'POST', {
            scope: scopeAtPublish,
            clientId,
            deviceId,
            connectionId: membershipConnectionId,
        });
        const authoritative = confirmation.state;
        serverState = authoritative;
        baseSnapshot = clone(authoritative.snapshot);

        if (deepEqual(authoritative.snapshot, projected)) {
            if (mutationVersion === localMutationVersion) {
                clearLocalDirty(scopeAtPublish);
                rebuildLastSyncedMap(authoritative.snapshot.messages);
            }
            return { ok: true, fallback: false };
        }

        // Ambiguous: durable retry carrying the ORIGINAL delta opId. The
        // queue rotates the opId itself if it rebases the payload.
        const fallbackSnapshot = syncSnapshot(durableSnapshot());
        await enqueueSnapshot(
            fallbackSnapshot,
            Number(authoritative.revision || baseRevision),
            clone(authoritative.snapshot),
            scopeAtPublish,
            'snapshot',
            null,
            localOpId,
        );
        scheduleQueueFlushRetry();
        return { ok: false, fallback: false, ambiguous: true };
    } catch {
        // Still unknown. Durable retry with the original opId; never issue a
        // second live operation that could double-commit.
        const fallbackSnapshot = syncSnapshot(durableSnapshot());
        await enqueueSnapshot(
            fallbackSnapshot,
            Number(serverState?.revision || baseRevision),
            clone(serverState?.snapshot || { messages: [], metadata: {} }),
            scopeAtPublish,
            'snapshot',
            null,
            localOpId,
        );
        scheduleQueueFlushRetry();
        return { ok: false, fallback: false, ambiguous: true };
    }
}

async function handleSnapshotDeltaEvent(data) {
    return new Promise(resolve => {
        const run = stateApplyChain.then(async () => {
            const revision = Number(data?.revision || 0);
            const baseRevision = Number(data?.baseRevision ?? -1);
            const currentRevision = Number(
                serverState?.revision || 0,
            );

            if (!revision) return false;

            // Already consumed (own HTTP response or SSE echo arrived first).
            if (revision <= currentRevision) return true;

            // We must hold exactly the revision this delta chains from.
            if (
                baseRevision !== currentRevision ||
                revision !== currentRevision + 1
            ) {
                await resyncCurrentScope(scopeEpoch);
                return true;
            }

            const ops = Array.isArray(data?.ops)
                ? data.ops
                : null;

            if (
                !ops ||
                ops.length === 0 ||
                ops.length > DELTA_MAX_OPS
            ) {
                await resyncCurrentScope(scopeEpoch);
                return true;
            }

            const scopeAtEvent = clone(currentScope);
            if (!scopeAtEvent) return false;

            const eventScopeKey = makeScopeKey(
                scopeAtEvent,
            );

            const eventPublishScopeKey =
                `${eventScopeKey}:${scopeEpoch}`;

            // A remote mutation during an in-flight local publish must wait
            // only for THAT publish if it belongs to this exact scope+epoch.
            // Never wait on a publish belonging to another chat or an older
            // lifecycle epoch.
            if (
                data.sourceClientId !== clientId &&
                activeLocalPublishPromise &&
                activeLocalPublishScopeKey ===
                    eventPublishScopeKey
            ) {
                try {
                    await activeLocalPublishPromise;
                } catch {
                    // The local publish path performs its own authoritative
                    // reconciliation. Do not let its failure break SSE.
                }
            }

            if (
                !currentScopeGuard(scopeEpoch) ||
                makeScopeKey(currentScope) !== eventScopeKey
            ) {
                return false;
            }

            // Never merge a remote delta over locally dirty / generating state.
            if (
                data.sourceClientId !== clientId &&
                (
                    isLocalDirty(scopeAtEvent) ||
                    localGeneration ||
                    generationActive(
                        serverState?.generation,
                    )
                )
            ) {
                await resyncCurrentScope(scopeEpoch);
                return true;
            }

            let projected;

            try {
                projected = applyDeltaToSnapshotFast(
                    serverState.snapshot,
                    ops,
                );
            } catch (error) {
                warn(
                    'snapshot delta projection failed',
                    error,
                );

                await resyncCurrentScope(
                    scopeEpoch,
                );

                return true;
            }

            // Own echo: the local HTTP request already mutated ctx.chat.
            // Only advance the authoritative projection.
            if (data.sourceClientId === clientId) {
                serverState = {
                    ...(serverState || {}),
                    revision,
                    snapshot: projected,
                };

                baseSnapshot = projected;
                return true;
            }

            refreshLiveContext();

            if (
                !ctx?.chat ||
                !nativeScopeStable(
                    scopeAtEvent,
                )
            ) {
                await resyncCurrentScope(
                    scopeEpoch,
                );

                return true;
            }

            applyingRemoteDepth += 1;

            let structuralChange = false;

            try {
                for (const op of ops) {
                    if (op.op === 'delete') {
                        const id = String(
                            op.messageId,
                        );

                        const index =
                            ctx.chat.findIndex(
                                message =>
                                    messageId(message) ===
                                    id,
                            );

                        if (index >= 0) {
                            ctx.chat.splice(
                                index,
                                1,
                            );

                            structuralChange = true;
                        }

                        recordRemoteTombstone(
                            id,
                            Number(
                                op.deletedAt ||
                                Date.now(),
                            ),
                        );

                        continue;
                    }

                    if (op.op === 'upsert') {
                        const message = clone(
                            op.message,
                        );

                        const id =
                            messageId(message);

                        if (!id) {
                            throw new Error(
                                'delta_message_id_missing',
                            );
                        }

                        const index =
                            ctx.chat.findIndex(
                                item =>
                                    messageId(item) ===
                                    id,
                            );

                        if (index >= 0) {
                            ctx.chat[index] =
                                message;

                            try {
                                const result =
                                    ctx.updateMessageBlock?.(
                                        index,
                                        clone(message),
                                        {
                                            rerenderMessage:
                                                true,
                                        },
                                    );

                                const domBlock =
                                    document.querySelector(
                                        `[mesid="${index}"]`,
                                    );

                                if (
                                    result === false ||
                                    !domBlock
                                ) {
                                    structuralChange =
                                        true;
                                }
                            } catch {
                                structuralChange = true;
                            }
                        } else {
                            let insertAt =
                                ctx.chat.length;

                            if (
                                op.afterMessageId != null
                            ) {
                                const afterIndex =
                                    ctx.chat.findIndex(
                                        item =>
                                            messageId(item) ===
                                            String(
                                                op.afterMessageId,
                                            ),
                                    );

                                if (
                                    afterIndex < 0
                                ) {
                                    throw new Error(
                                        'delta_anchor_missing',
                                    );
                                }

                                insertAt =
                                    afterIndex + 1;
                            }

                            ctx.chat.splice(
                                insertAt,
                                0,
                                message,
                            );

                            structuralChange = true;
                        }

                        const modifiedAt =
                            Number(
                                op.modifiedAt ||
                                Date.now(),
                            );

                        const bucket =
                            chatSyncMetaBucket();

                        if (bucket) {
                            const tomb =
                                readLedger(
                                    ctx.chatMetadata,
                                );

                            if (
                                Object.hasOwn(
                                    tomb,
                                    id,
                                ) &&
                                modifiedAt >
                                    tomb[id]
                            ) {
                                delete tomb[id];

                                bucket.tombstones =
                                    JSON.parse(
                                        JSON.stringify(
                                            tomb,
                                        ),
                                    );
                            }
                        }

                        continue;
                    }

                    if (op.op === 'move') {
                        const id = String(
                            op.messageId,
                        );

                        const currentIndex =
                            ctx.chat.findIndex(
                                message =>
                                    messageId(message) ===
                                    id,
                            );

                        if (
                            currentIndex < 0
                        ) {
                            throw new Error(
                                'delta_move_target_missing',
                            );
                        }

                        const moved =
                            ctx.chat[
                                currentIndex
                            ];

                        ctx.chat.splice(
                            currentIndex,
                            1,
                        );

                        let insertAt = 0;

                        if (
                            op.afterMessageId != null
                        ) {
                            const afterIndex =
                                ctx.chat.findIndex(
                                    item =>
                                        messageId(item) ===
                                        String(
                                            op.afterMessageId,
                                        ),
                                );

                            if (
                                afterIndex < 0
                            ) {
                                throw new Error(
                                    'delta_move_anchor_missing',
                                );
                            }

                            insertAt =
                                afterIndex + 1;
                        }

                        ctx.chat.splice(
                            insertAt,
                            0,
                            moved,
                        );

                        structuralChange = true;
                    }
                }

                if (structuralChange) {
                    try {
                        await awaitablePrintMessages();
                    } catch (error) {
                        log(
                            'delta printMessages failed',
                            error,
                        );

                        throw error;
                    }
                }

                serverState = {
                    ...(serverState || {}),
                    revision,
                    snapshot: projected,
                };

                baseSnapshot = projected;

                rebuildLastSyncedMap(
                    projected.messages,
                );

                // Persist the remotely-applied change without blocking SSE
                // processing — but never silently accept a failed native save.
                if (
                    scopeAtEvent.kind !== 'group'
                ) {
                    void safeNativeSave(
                        scopeAtEvent,
                    )
                        .then(saved => {
                            if (
                                !saved &&
                                currentScopeGuard(
                                    scopeEpoch,
                                )
                            ) {
                                void resyncCurrentScope(
                                    scopeEpoch,
                                ).catch(error =>
                                    warn(
                                        'remote delta persistence recovery failed',
                                        error,
                                    ),
                                );
                            }
                        })
                        .catch(error => {
                            warn(
                                'remote delta native save failed',
                                error,
                            );

                            if (
                                currentScopeGuard(
                                    scopeEpoch,
                                )
                            ) {
                                void resyncCurrentScope(
                                    scopeEpoch,
                                ).catch(
                                    recoveryError =>
                                        warn(
                                            'remote delta persistence recovery failed',
                                            recoveryError,
                                        ),
                                );
                            }
                        });
                }

                updateGenerationUi();
                return true;
            } catch (error) {
                warn(
                    'snapshot delta application failed; resyncing',
                    error,
                );

                await resyncCurrentScope(
                    scopeEpoch,
                );

                return true;
            } finally {
                applyingRemoteDepth -= 1;
            }
        });

        stateApplyChain = run.then(
            () => undefined,
            error =>
                warn(
                    'snapshot delta state chain failed',
                    error,
                ),
        );

        run.then(
            value => resolve(value),
            () => resolve(false),
        );
    });
}

async function enqueueSnapshot(snapshot, baseRev, baseSnap, scope = currentScope, kind = 'snapshot', generationId = null, opId = null) {
    if (!syncEnabled() || !scope) return;
    const scopeKey = makeScopeKey(scope);
    if (!scopeKey) return;

    // Row identity and idempotency identity are SEPARATE: the queue may
    // rebase a row's payload (rotating its opId) while keeping the row key
    // stable across retries.
    const row = {
        id: newId(),
        opId: opId || newId(),
        scopeKey,
        createdAt: Date.now(),
        queueSequence: ++queueSequenceCounter,
        kind,
        generationId: generationId ? String(generationId) : null,
        baseRevision: Number(baseRev || 0),
        baseSnapshot: clone(baseSnap || { messages: [], metadata: {} }),
        snapshot: clone(snapshot),
    };

    const byteSize = utf8ByteLength(row);
    let existingRows = await idbList(scopeKey);

    // Proactive coalescing: pending normal rows are absolute desired states,
    // so the newest subsumes the older ones long before capacity is hit.
    // Keeps the earliest base so conflict merges stay anchored.
    if (kind === 'snapshot' && !generationId) {
        const normalSnapshots = existingRows
            .filter(existing => existing.kind === 'snapshot' && !existing.generationId)
            .sort((a, b) => (a.queueSequence || 0) - (b.queueSequence || 0));

        if (normalSnapshots.length) {
            const latest = normalSnapshots[normalSnapshots.length - 1];
            if (deepEqual(latest.snapshot, row.snapshot)) return;

            const earliest = normalSnapshots[0];
            row.baseRevision = Math.min(row.baseRevision, Number(earliest.baseRevision || 0));
            row.baseSnapshot = clone(earliest.baseSnapshot || row.baseSnapshot);
            for (const old of normalSnapshots) {
                await idbDelete(old.id);
            }
            existingRows = existingRows.filter(existing => !normalSnapshots.includes(existing));
        }
    }

    const duplicate = existingRows.find(existing =>
        existing.kind === kind &&
        existing.generationId === row.generationId &&
        deepEqual(existing.snapshot, row.snapshot),
    );
    if (duplicate) return;

    let currentBytes = existingRows.reduce((sum, r) => sum + utf8ByteLength(r), 0);

    // Over capacity: consolidate, never evict or reject. Pending rows are
    // full snapshots (absolute desired state), so the newest subsumes the
    // older ones — keep the earliest base, drop the rest.
    if (currentBytes + byteSize > MAX_QUEUE_BYTES || existingRows.length >= MAX_QUEUE) {
        const snapshotRows = existingRows
            .filter(r => r.kind === 'snapshot' && !r.generationId)
            .sort((a, b) => (a.queueSequence || 0) - (b.queueSequence || 0));
        if (snapshotRows.length) {
            const earliest = snapshotRows[0];
            row.baseRevision = Math.min(row.baseRevision, Number(earliest.baseRevision || 0));
            row.baseSnapshot = clone(earliest.baseSnapshot || row.baseSnapshot);
            for (const old of snapshotRows) {
                await idbDelete(old.id);
                currentBytes -= utf8ByteLength(old);
            }
            existingRows = existingRows.filter(r => !snapshotRows.includes(r));
        }
        if (currentBytes + byteSize > MAX_QUEUE_BYTES || existingRows.length >= MAX_QUEUE) {
            // Only generation-bound rows remain: retain the change in the
            // live chat (localDirty stays set) rather than drop it.
            warn('[MCS] queue capacity reached; retaining local change for later retry');
            scheduleQueueFlushRetry();
            return;
        }
    }

    await idbPut(row);
}

function scheduleQueueFlushRetry(delay = 2000) {
    if (queueRetryTimer) return;
    queueRetryTimer = setTimeout(() => {
        queueRetryTimer = null;
        if (currentScope && settings.enabled && syncEnabled() && !localGeneration && !serverState?.generation) {
            flushQueue().catch(error => warn('queue retry failed', error));
        }
    }, Math.max(500, delay));
}

async function sendSnapshotDirect(snapshot, baseRev, opId, scope = currentScope) {
    if (!scope) throw new Error('no_scope');
    return api('/snapshot', 'POST', {
        scope: clone(scope),
        clientId,
        deviceId,
        connectionId: membershipConnectionId,
        opId,
        baseRevision: baseRev,
        snapshot,
    });
}

async function publishLocalSnapshot(
    snapshot = durableSnapshot(),
    {
        allowDuringGeneration = false,
        scope = currentScope,
        opId = null,
        expectedMutationVersion = null,
    } = {},
) {
    if (!scope || !settings.enabled || !syncEnabled()) return false;
    if (!nativeScopeStable(scope)) return false;

    if (localGeneration && !allowDuringGeneration) return false;

    if (localGeneration && allowDuringGeneration && localGeneration.phase === 'streaming') {
        return false;
    }

    if (generationActive(serverState?.generation) && !localGeneration) {
        return false;
    }

    const desiredSnapshot = syncSnapshot(snapshot);

    if (deepEqual(desiredSnapshot, serverState?.snapshot)) {
        if (expectedMutationVersion == null || expectedMutationVersion === localMutationVersion) {
            clearLocalDirty(scope);
            rebuildLastSyncedMap(desiredSnapshot.messages);
        }
        return true;
    }

    const scopeAtPublish = clone(scope);
    const scopeKeyAtPublish = makeScopeKey(scopeAtPublish);
    // Immutable baseline reference: snapshots are never mutated in place, so
    // cloning the baseline is pure memory waste on a large chat.
    const baseline = baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} };
    const revision = Number(serverState?.revision || 0);
    const localOpId = opId || newId();

    try {
        const result = await sendSnapshotDirect(desiredSnapshot, revision, localOpId, scopeAtPublish);
        if (scopeKeyValue !== scopeKeyAtPublish || !currentScope || makeScopeKey(currentScope) !== scopeKeyAtPublish) return false;
        serverState = result.state;
        baseSnapshot = result.state.snapshot;

        if (expectedMutationVersion == null || expectedMutationVersion === localMutationVersion) {
            clearLocalDirty(scopeAtPublish);
            rebuildLastSyncedMap(desiredSnapshot.messages);
        } else {
            // A newer local mutation happened while the request was in
            // flight. Never clear its dirty flag — durably capture it.
            const latest = syncSnapshot(durableSnapshot());
            await enqueueSnapshot(
                latest,
                Number(result.state.revision || 0),
                result.state.snapshot,
                scopeAtPublish,
                'snapshot',
                null,
                newId(),
            );
            scheduleQueueFlushRetry();
        }

        return true;
    } catch (error) {
        if (scopeKeyValue !== scopeKeyAtPublish) return false;

        if (error?.status === 409 && error?.payload?.state) {
            const remoteState = error.payload.state;
            if (error.payload.error === 'generation_active') return false;

            // The request may have actually committed and only the response
            // was lost: an authoritative snapshot equal to the desired one
            // proves the commit.
            if (deepEqual(remoteState.snapshot, desiredSnapshot)) {
                serverState = remoteState;
                baseSnapshot = remoteState.snapshot;

                if (expectedMutationVersion == null || expectedMutationVersion === localMutationVersion) {
                    clearLocalDirty(scopeAtPublish);
                    rebuildLastSyncedMap(desiredSnapshot.messages);
                }

                return true;
            }

            const merged = mergeSnapshots(baseline, desiredSnapshot, remoteState.snapshot);
            serverState = remoteState;
            baseSnapshot = remoteState.snapshot;

            // The payload changed, therefore it is a NEW logical operation.
            const retryOpId = deepEqual(merged, desiredSnapshot) ? localOpId : newId();

            try {
                const result = await sendSnapshotDirect(merged, Number(remoteState.revision), retryOpId, scopeAtPublish);
                if (scopeKeyValue !== scopeKeyAtPublish || !currentScope || makeScopeKey(currentScope) !== scopeKeyAtPublish) return false;
                serverState = result.state;
                baseSnapshot = result.state.snapshot;

                const applied = await applySnapshot(merged, {
                    save: true,
                    render: true,
                    expectedScope: scopeAtPublish,
                    clearDirty: false,
                });
                if (!applied) return false;

                if (expectedMutationVersion == null || expectedMutationVersion === localMutationVersion) {
                    clearLocalDirty(scopeAtPublish);
                    rebuildLastSyncedMap(merged.messages);
                } else {
                    const latest = syncSnapshot(durableSnapshot());
                    await enqueueSnapshot(
                        latest,
                        Number(result.state.revision || 0),
                        result.state.snapshot,
                        scopeAtPublish,
                        'snapshot',
                        null,
                        newId(),
                    );
                    scheduleQueueFlushRetry();
                }

                return true;
            } catch (retryError) {
                if (retryError?.status === 409 && retryError?.payload?.error === 'generation_active') return false;
                await enqueueSnapshot(
                    merged,
                    retryError?.payload?.state?.revision ?? Number(remoteState.revision),
                    retryError?.payload?.state?.snapshot ?? remoteState.snapshot,
                    scopeAtPublish,
                    'snapshot',
                    null,
                    newId(),
                );
                scheduleQueueFlushRetry();
                return false;
            }
        }

        // Network timeout/connection failure is ambiguous. Confirm
        // authoritative server state before generating another operation.
        try {
            const confirmation = await api('/state', 'POST', {
                scope: scopeAtPublish,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
            });

            if (scopeKeyValue === scopeKeyAtPublish && confirmation?.state) {
                serverState = confirmation.state;
                baseSnapshot = confirmation.state.snapshot;

                if (deepEqual(confirmation.state.snapshot, desiredSnapshot)) {
                    if (expectedMutationVersion == null || expectedMutationVersion === localMutationVersion) {
                        clearLocalDirty(scopeAtPublish);
                        rebuildLastSyncedMap(desiredSnapshot.messages);
                    }
                    return true;
                }
            }
        } catch {
            /* fall through to durable queue */
        }

        if (localGeneration && allowDuringGeneration) return false;

        let queuePayload = desiredSnapshot;
        if (expectedMutationVersion != null && expectedMutationVersion !== localMutationVersion) {
            queuePayload = syncSnapshot(durableSnapshot());
        }

        await enqueueSnapshot(
            queuePayload,
            Number(serverState?.revision || revision),
            serverState?.snapshot || baseline,
            scopeAtPublish,
            'snapshot',
            null,
            newId(),
        );

        scheduleQueueFlushRetry();
        return false;
    }
}

async function flushQueueInternal() {
    if (!currentScope || !settings.enabled || !syncEnabled() || !scopeKeyValue) return;
    if (!nativeScopeStable(currentScope)) return;
    if (localGeneration || generationActive(serverState?.generation)) return;

    const scopeAtFlush = clone(currentScope);
    const scopeKeyAtFlush = makeScopeKey(scopeAtFlush);
    const nativeLoadEpochAtFlush = nativeLoadEpoch;

    const rows = await idbList(scopeKeyAtFlush);

    for (const originalRow of rows) {
        if (
            !currentScope ||
            scopeKeyValue !== scopeKeyAtFlush ||
            !nativeScopeStable(scopeAtFlush) ||
            nativeLoadEpoch !== nativeLoadEpochAtFlush
        ) {
            return;
        }

        if (localGeneration || generationActive(serverState?.generation)) return;

        // Work on a detached row so an in-flight local edit can never mutate
        // the object being sent underneath us.
        const row = {
            ...originalRow,
            snapshot: clone(originalRow.snapshot),
            baseSnapshot: clone(originalRow.baseSnapshot || { messages: [], metadata: {} }),
            baseRevision: Number(originalRow.baseRevision || 0),
            opId: String(originalRow.opId || newId()),
        };

        const mutationVersionAtStart = localMutationVersion;

        try {
            let nextSnapshot = clone(row.snapshot);
            let nextBase = clone(row.baseSnapshot);
            let nextRevision = Number(row.baseRevision || 0);

            const remote = serverState?.snapshot || null;
            const remoteRevision = Number(serverState?.revision || nextRevision);

            // Before sending, reconcile against the newest authoritative
            // server revision.
            if (remote && remoteRevision !== nextRevision) {
                // The queued desired state may already be the server state
                // (a lost response committed it after all).
                if (deepEqual(remote, nextSnapshot)) {
                    await idbDelete(row.id);
                    rebuildLastSyncedMap(remote.messages);
                    continue;
                }

                nextSnapshot = mergeSnapshots(nextBase, nextSnapshot, remote);
                nextBase = clone(remote);
                nextRevision = remoteRevision;
                row.snapshot = clone(nextSnapshot);
                row.baseSnapshot = clone(nextBase);
                row.baseRevision = nextRevision;

                // Rebasing changes the logical payload: rotate the
                // idempotency key so a duplicate check cannot discard it.
                row.opId = newId();

                await idbPut(row);
            }

            if (deepEqual(nextSnapshot, serverState?.snapshot)) {
                await idbDelete(row.id);
                if (mutationVersionAtStart === localMutationVersion) {
                    clearLocalDirty(scopeAtFlush);
                }
                rebuildLastSyncedMap(nextSnapshot.messages);
                continue;
            }

            let result = null;
            let sendError = null;
            for (let sendAttempt = 0; sendAttempt < 3; sendAttempt += 1) {
                try {
                    result = await sendSnapshotDirect(nextSnapshot, nextRevision, row.opId, scopeAtFlush);
                    sendError = null;
                    break;
                } catch (error) {
                    sendError = error;
                    if (error?.status === 409) break;
                    if (sendAttempt < 2) await sleep(150 * (sendAttempt + 1));
                }
            }

            if (sendError) {
                // A timeout/network failure is not proof that the server
                // rejected the mutation — confirm before deciding.
                if (!sendError.status || sendError.status >= 500 || sendError.name === 'AbortError' || sendError.name === 'TimeoutError') {
                    const confirmation = await api('/state', 'POST', {
                        scope: scopeAtFlush,
                        clientId,
                        deviceId,
                        connectionId: membershipConnectionId,
                    }).catch(() => null);

                    const confirmedState = confirmation?.state || null;

                    if (confirmedState) {
                        serverState = confirmedState;
                        baseSnapshot = confirmedState.snapshot;

                        if (deepEqual(confirmedState.snapshot, nextSnapshot)) {
                            await idbDelete(row.id);
                            if (mutationVersionAtStart === localMutationVersion) {
                                clearLocalDirty(scopeAtFlush);
                            }
                            rebuildLastSyncedMap(nextSnapshot.messages);
                            continue;
                        }
                    }
                }

                throw sendError;
            }

            if (!result?.state) throw new Error('snapshot_flush_missing_state');
            if (scopeKeyValue !== scopeKeyAtFlush || nativeLoadEpoch !== nativeLoadEpochAtFlush) return;

            serverState = result.state;
            baseSnapshot = result.state.snapshot;

            // A new local mutation occurred while this row was in flight.
            // Never overwrite that newer native state with the older row.
            if (mutationVersionAtStart !== localMutationVersion) {
                const latestLocal = syncSnapshot(durableSnapshot());
                const rebasedLatest = mergeSnapshots(nextSnapshot, latestLocal, result.state.snapshot);

                row.baseSnapshot = clone(result.state.snapshot);
                row.baseRevision = Number(result.state.revision || 0);
                row.snapshot = clone(rebasedLatest);
                row.opId = newId();

                await idbPut(row);
                markLocalDirty(scopeAtFlush);
                rebuildLastSyncedMap(result.state.snapshot.messages);
                continue;
            }

            // Scope transition during the network request must never turn
            // into a native-chat overwrite.
            if (!nativeScopeStable(scopeAtFlush) || !currentScope || scopeKeyValue !== scopeKeyAtFlush) {
                return;
            }

            const applied = await applySnapshot(incomingSnapshot(result.state.snapshot), {
                save: true,
                render: true,
                expectedScope: scopeAtFlush,
            });
            if (!applied) return;

            await idbDelete(row.id);

            if (mutationVersionAtStart === localMutationVersion) {
                clearLocalDirty(scopeAtFlush);
            } else {
                markLocalDirty(scopeAtFlush);
            }

            rebuildLastSyncedMap(result.state.snapshot.messages);
        } catch (error) {
            if (scopeKeyValue !== scopeKeyAtFlush) return;

            if (error?.status === 409 && error?.payload?.state) {
                const remoteState = error.payload.state;

                // The rejected send may actually have committed (lost
                // response): an authoritative match proves it.
                if (remoteState.snapshot && deepEqual(remoteState.snapshot, row.snapshot)) {
                    await idbDelete(row.id);
                    serverState = remoteState;
                    baseSnapshot = remoteState.snapshot;
                    if (localMutationVersion === mutationVersionAtStart) {
                        clearLocalDirty(scopeAtFlush);
                    }
                    continue;
                }

                if (remoteState.generation || error.payload.error === 'generation_active') {
                    serverState = remoteState;
                    baseSnapshot = remoteState.snapshot;
                    scheduleQueueFlushRetry();
                    return;
                }

                const merged = mergeSnapshots(row.baseSnapshot, row.snapshot, remoteState.snapshot);

                row.opId = newId();
                row.snapshot = clone(merged);
                row.baseSnapshot = clone(remoteState.snapshot);
                row.baseRevision = Number(remoteState.revision || 0);

                serverState = remoteState;
                baseSnapshot = remoteState.snapshot;

                await idbPut(row);
                continue;
            }

            scheduleQueueFlushRetry();
            return;
        }
    }

    if (queueRetryTimer) {
        clearTimeout(queueRetryTimer);
        queueRetryTimer = null;
    }
}

function flushQueue() {
    const run = queueFlushChain.then(() => flushQueueInternal());
    queueFlushChain = run.then(() => undefined, error => warn('queue flush failed', error));
    return run;
}

function broadcastWake(kind, extra = {}) {
    try {
        bc?.postMessage({
            kind,
            scopeKey: scopeKeyValue,
            at: Date.now(),
            clientId,
            deviceId,
            tabId,
            ...extra,
        });
    } catch { /* ignore */ }
}

// Two-phase join: join WITHOUT the snapshot first. Only when the server has
// no state at all does it request a seed — an established chat never pays the
// giant upload.
async function openScope(epoch) {
    if (!settings.enabled || !settings.autoConnect || !currentScope) return;

    const scopeAtJoin = clone(currentScope);

    if (!nativeScopeStable(scopeAtJoin)) {
        statusText('Waiting for active chat…');
        if (!scopeRetryTimer && !nativeRestoreInProgress) {
            scopeRetryTimer = safeSetTimer(() => {
                scopeRetryTimer = null;
                if (currentScopeGuard(epoch)) openScope(epoch).catch(error => warn('scope retry failed', error));
            }, 500);
        }
        return;
    }

    if (joinAbortController) {
        try { joinAbortController.abort(); } catch { /* ignore */ }
    }

    const joinController = new AbortController();
    joinAbortController = joinController;

    // Fresh membership connection identity for THIS join attempt: a delayed
    // leave/heartbeat from a previous attempt can never evict this one.
    const connectionIdAtJoin = newId();
    membershipConnectionId = connectionIdAtJoin;

    try {
        let result = await api('/join', 'POST', {
            scope: scopeAtJoin,
            clientId,
            deviceId,
            connectionId: connectionIdAtJoin,
        }, '', { signal: joinController.signal, timeoutMs: API_TIMEOUT_MS });

        if (result?.seedRequired) {
            result = await api('/join', 'POST', {
                scope: scopeAtJoin,
                clientId,
                deviceId,
                connectionId: connectionIdAtJoin,
                snapshot: syncSnapshot(durableSnapshot()),
            }, '', { signal: joinController.signal, timeoutMs: API_TIMEOUT_MS * 3 });
        }

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtJoin)) {
            try {
                await api('/leave', 'POST', { scope: scopeAtJoin, clientId, deviceId, connectionId: connectionIdAtJoin });
            } catch { /* best effort */ }
            if (membershipConnectionId === connectionIdAtJoin) membershipConnectionId = null;
            return;
        }

        if (!nativeScopeStable(scopeAtJoin)) return;
        if (joinAbortController === joinController) joinAbortController = null;

        if (scopeRetryTimer) {
            clearTimeout(scopeRetryTimer);
            scopeRetryTimer = null;
        }

        serverState = result.state;
        baseSnapshot = result.state.snapshot;
        lastSseEventId = Number(result.state?.lastEventId || 0);
        resetChunkAssemblies();
        remoteGenerationId = null;
        lastRemoteStreamSeq = -1;
        generationMismatchSince = 0;

        const staleOwnedGenerationId =
            serverState?.generation && generationIsStaleOwned(serverState.generation)
                ? serverState.generation.generationId
                : null;

        if (staleOwnedGenerationId && generationClaimInFlightId !== staleOwnedGenerationId) {
            try {
                const cleared = await api('/generation/terminal', 'POST', {
                    scope: scopeAtJoin,
                    clientId,
                    deviceId,
                    connectionId: connectionIdAtJoin,
                    generationId: staleOwnedGenerationId,
                    phase: 'stopped',
                    snapshot: clone(serverState.snapshot),
                    opId: newId(),
                });
                if (currentScopeGuard(epoch)) {
                    serverState = cleared.state;
                    baseSnapshot = cleared.state.snapshot;
                    lastSseEventId = Number(cleared.state?.lastEventId || lastSseEventId);
                    rememberTerminatedGeneration(staleOwnedGenerationId);
                }
            } catch (staleError) {
                if (staleError?.status === 409 && staleError?.payload?.state) {
                    serverState = staleError.payload.state;
                    baseSnapshot = staleError.payload.state.snapshot;
                } else {
                    warn('stale generation cleanup failed', staleError);
                }
            }
        }

        if (serverState?.generation && generationLeaseExpired(serverState.generation)) {
            await resyncCurrentScope(epoch);
        }
        if (!currentScopeGuard(epoch)) return;
        if (!nativeScopeStable(scopeAtJoin)) {
            statusText('Waiting for active chat…');
            return;
        }

        const queued = await idbList(scopeKeyValue);

        if (!queued.length || serverState.generation) {
            const incoming = incomingSnapshot(serverState.snapshot);
            const localSnapshot = syncSnapshot(durableSnapshot());
            if (!deepEqual(localSnapshot, incoming) && !generationIsMine(serverState.generation)) {
                const applied = await applySnapshot(incoming, {
                    save: true,
                    render: true,
                    expectedScope: scopeAtJoin,
                    allowDuringGeneration: true,
                });
                if (!applied) return;
            } else {
                rebuildLastSyncedMap(serverState.snapshot.messages);
            }
            if (!queued.length) clearLocalDirty(scopeAtJoin);
        }

        // Live connection first; queue reconciliation must never delay it.
        connectSse(epoch);
        startHeartbeats(epoch);
        statusText(`Connected · rev ${serverState.revision}`);
        updateGenerationUi();

        await flushQueue();
    } catch (error) {
        if (joinAbortController === joinController) joinAbortController = null;
        if (membershipConnectionId === connectionIdAtJoin) membershipConnectionId = null;
        if (error?.name === 'AbortError') return;
        warn('join failed', error);
        statusText(`Offline: ${error?.message || 'connection failed'}`);

        if (!currentScopeGuard(epoch) || scopeRetryTimer || nativeRestoreInProgress) return;
        scopeRetryTimer = safeSetTimer(() => {
            scopeRetryTimer = null;
            if (currentScopeGuard(epoch)) openScope(epoch).catch(retryError => warn('scope retry failed', retryError));
        }, 2000);
    }
}

function disconnectSse() {
    ++sseEpoch;
    resetChunkAssemblies();
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
    nativeMembershipHeartbeatInFlight = null;
}

function handleServerHello(data) {
    // hello is always the first event of a fresh SSE connection. Any assembly
    // still in the map belongs to a dead connection and can never complete —
    // clear it now instead of waiting out the 30s expiry.
    resetChunkAssemblies();

    if (data.protocol !== PROTOCOL || data.schema !== SCHEMA) {
        statusText(`Protocol mismatch (${data.protocol}/${data.schema})`);
        // Do not leave an incompatible EventSource alive.
        disconnectSse();
        return;
    }

    const incomingGeneration = clone(data.generation || null);
    const incomingGenerationId = incomingGeneration?.generationId || null;

    if (incomingGenerationId && isGenerationTerminated(incomingGenerationId)) {
        serverState = {
            ...(serverState || {}),
            revision: Math.max(Number(serverState?.revision || 0), Number(data.revision || 0)),
            scope: clone(data.scope),
            generation: null,
        };
        clearRemoteStreamState();
        updateGenerationUi();
        return;
    }

    const generation = incomingGeneration;
    const previousGeneration = serverState?.generation || null;
    const previousTime = Number(previousGeneration?.startedAt || previousGeneration?.claimedAt || 0);
    const incomingTime = Number(generation?.startedAt || generation?.claimedAt || 0);

    if (
        previousGeneration &&
        generation &&
        previousGeneration.generationId !== generation.generationId &&
        generationActive(previousGeneration) &&
        previousTime &&
        incomingTime &&
        incomingTime < previousTime
    ) {
        return;
    }

    serverState = {
        ...(serverState || {}),
        revision: Math.max(Number(serverState?.revision || 0), Number(data.revision || 0)),
        generation,
        scope: clone(data.scope),
    };

    if (generation?.stopRequested) {
        rememberStopRequestedGeneration(generation.generationId);
        remoteStopGenerationId = generation.generationId;
        clearRemoteStreamState();
    } else if (generation?.generationId && !generationIsStopRequested(generation.generationId)) {
        if (remoteStopGenerationId && remoteStopGenerationId !== generation.generationId) {
            remoteStopGenerationId = null;
            remoteStopRequestedAt = 0;
        }
    }

    if (generationIsStopRequested(generation?.generationId)) {
        clearRemoteStreamState();
        updateGenerationUi();
        return;
    }

    if (generationIsMine(generation)) {
        if (generationClaimedThisPage || generationClaimInFlightId === generation.generationId) {
            if (generationClaimedThisPage && localGeneration?.generationId === generation.generationId) {
                localGeneration = { ...localGeneration, ...clone(generation) };
            }
            if (generationClaimInFlightId === generation.generationId && ['started', 'streaming'].includes(generation.phase)) {
                generationServerReadyId = generation.generationId;
            }
        } else {
            resyncCurrentScope(scopeEpoch).catch(error => warn('stale generation hello resync failed', error));
        }
    } else if (generation) {
        remoteGenerationId = generation.generationId;
        lastRemoteStreamSeq = Number(generation.seq ?? 0);
    } else {
        clearRemoteStreamState();
    }

    updateGenerationUi();
}

function isGenerationTerminated(generationId) {
    if (!generationId) return false;
    const id = String(generationId);
    return terminatedGenerationIds.has(id) || String(lastTerminatedGenerationId || '') === id;
}

async function handleSnapshotEvent(data) {
    return new Promise(resolve => {
        const run = stateApplyChain.then(async () => {
            const revision = Number(data?.revision || 0);
            const mutationVersionAtStart = localMutationVersion;
            if (!revision || revision <= Number(serverState?.revision || 0)) return true;
            if (!currentScope || !nativeScopeStable(currentScope)) {
                log('[MCS] snapshot arrived during transient scope instability; deferring to scope switch');
                return true;
            }

            const scopeAtEvent = clone(currentScope);
            const remote = incomingSnapshot(data.snapshot);
            const knownBase = baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} };
            const local = syncSnapshot(durableSnapshot());
            const dirty = isLocalDirty(scopeAtEvent);
            const incomingGenerationId = String(data?.generationId || '');

            serverState = { ...(serverState || {}), revision, snapshot: clone(data.snapshot) };
            baseSnapshot = data.snapshot;

            if (serverState?.generation || incomingGenerationId) {
                updateGenerationUi();
                return true;
            }

            // Self-echo clears dirty ONLY when no newer local edit happened
            // and the live chat actually matches what the server committed —
            // an old echo must never clear a newer edit.
            if (
                data.sourceClientId === clientId &&
                mutationVersionAtStart === localMutationVersion &&
                deepEqual(remote, local)
            ) {
                clearLocalDirty(scopeAtEvent);
                rebuildLastSyncedMap(remote.messages);
                updateGenerationUi();
                return true;
            }

            let appliedSnapshot = remote;
            if (dirty) appliedSnapshot = mergeSnapshots(knownBase, local, remote);

            if (!deepEqual(local, appliedSnapshot)) {
                const applied = await applySnapshot(appliedSnapshot, {
                    save: true,
                    render: true,
                    expectedScope: scopeAtEvent,
                });
                if (!applied) {
                    await resyncCurrentScope(scopeEpoch);
                    return false;
                }
                if (mutationVersionAtStart !== localMutationVersion) markLocalDirty(scopeAtEvent);
            } else {
                rebuildLastSyncedMap(appliedSnapshot.messages);
            }

            if (!deepEqual(appliedSnapshot, remote)) {
                if (!nativeScopeStable(scopeAtEvent) || scopeKeyValue !== makeScopeKey(scopeAtEvent)) return false;
                try {
                    const result = await sendSnapshotDirect(appliedSnapshot, revision, newId(), scopeAtEvent);
                    if (scopeKeyValue === makeScopeKey(scopeAtEvent)) {
                        serverState = result.state;
                        baseSnapshot = result.state.snapshot;
                        if (mutationVersionAtStart === localMutationVersion) {
                            clearLocalDirty(scopeAtEvent);
                        }
                    }
                } catch (publishError) {
                    if (publishError?.status === 409 && publishError?.payload?.state) {
                        serverState = publishError.payload.state;
                        baseSnapshot = publishError.payload.state.snapshot;
                    } else {
                        await enqueueSnapshot(appliedSnapshot, revision, knownBase, scopeAtEvent);
                        scheduleQueueFlushRetry();
                    }
                }
            } else if (mutationVersionAtStart === localMutationVersion) {
                clearLocalDirty(scopeAtEvent);
            }

            updateGenerationUi();
            return true;
        });

        stateApplyChain = run.then(() => undefined, error => warn('remote snapshot apply failed', error));
        run.then(resolve, () => resolve(false));
    });
}

function handleGenerationEvent(data) {
    const generation = clone(data?.generation || null);
    if (!generation || !currentScope || !generation.generationId) return;
    if (isGenerationTerminated(generation.generationId)) return;

    const eventRevision = Number(data?.revision || 0);
    const currentRevision = Number(serverState?.revision || 0);
    if (eventRevision && eventRevision < currentRevision) return;

    const oldGeneration = serverState?.generation || null;
    const oldTime = Number(oldGeneration?.startedAt || oldGeneration?.claimedAt || 0);
    const incomingTime = Number(generation?.startedAt || generation?.claimedAt || 0);
    const sameGeneration = oldGeneration?.generationId === generation.generationId;

    if (oldGeneration && !sameGeneration && generationActive(oldGeneration) && incomingTime && oldTime && incomingTime < oldTime) return;

    serverState = {
        ...(serverState || {}),
        revision: Math.max(currentRevision, eventRevision),
        generation,
    };

    if (generation.stopRequested) {
        rememberStopRequestedGeneration(generation.generationId);
        remoteStopGenerationId = generation.generationId;
    } else if (remoteStopGenerationId && remoteStopGenerationId !== generation.generationId && !generationIsStopRequested(generation.generationId)) {
        remoteStopGenerationId = null;
        remoteStopRequestedAt = 0;
    }

    if (generationIsStopRequested(generation.generationId)) {
        clearRemoteStreamState();
        updateGenerationUi();
        return;
    }

    if (generationIsMine(generation)) {
        if (generationClaimedThisPage || generationClaimInFlightId === generation.generationId) {
            if (generationClaimedThisPage) {
                if (!localGeneration || localGeneration.generationId === generation.generationId) {
                    localGeneration = clone(generation);
                    localGenerationScope = localGenerationScope || clone(currentScope);
                    localGenerationEpoch = scopeEpoch;
                    localGenerationBaseSnapshot = localGenerationBaseSnapshot || baseSnapshot || serverState.snapshot;
                }
            }

            if (['started', 'streaming'].includes(generation.phase)) {
                generationServerReadyId = generation.generationId;
            }
        } else {
            resyncCurrentScope(scopeEpoch).catch(error => warn('stale generation event resync failed', error));
        }
    } else {
        if (remoteGenerationId !== generation.generationId) {
            remoteGenerationId = generation.generationId;
            lastRemoteStreamSeq = -1;
            suppressedRemoteStreamMessageIds.clear();
        }

        const seq = Number(generation.seq || 0);
        if (sameGeneration && seq <= lastRemoteStreamSeq) {
            updateGenerationUi();
            return;
        }

        lastRemoteStreamSeq = Math.max(lastRemoteStreamSeq, seq);
    }

    updateGenerationUi();
}

async function handleGenerationRecovered(data) {
    if (!currentScope) return false;

    const epoch = scopeEpoch;
    const scopeAtRecovery = clone(currentScope);

    try {
        const result = await api('/state', 'POST', {
            scope: scopeAtRecovery,
            clientId,
            deviceId,
            connectionId: membershipConnectionId,
        });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtRecovery)) return true;

        const authoritative = result.state || null;
        const generation = authoritative?.generation || null;
        const localId = localGeneration?.generationId || null;

        serverState = authoritative;
        baseSnapshot = authoritative?.snapshot || baseSnapshot || { messages: [], metadata: {} };
        lastSseEventId = Number(authoritative?.lastEventId || lastSseEventId);

        if (generation) {
            if (localId && generation.generationId === localId && generationIsMine(generation)) {
                localGeneration = { ...localGeneration, ...clone(generation) };
                localGenerationScope = clone(scopeAtRecovery);
                localGenerationEpoch = epoch;
                generationServerReadyId = ['started', 'streaming'].includes(generation.phase) ? generation.generationId : generationServerReadyId;
                generationMismatchSince = 0;
                updateGenerationUi();
                return true;
            }

            if (localGeneration && generation.generationId !== localId) {
                generationMismatchSince = generationMismatchSince || Date.now();
                updateGenerationUi();
                return true;
            }

            clearRemoteStreamState();
            updateGenerationUi();
            return true;
        }

if (localGeneration) {
    const localGenerationId =
        localGeneration.generationId;

    generationMismatchSince =
        generationMismatchSince || Date.now();

    const terminalPhase = String(
        generationTerminalPhase || '',
    ).toLowerCase();

    const alreadyTerminal =
        terminalizingGenerationId ===
            localGenerationId ||
        generationIsStopRequested(
            localGenerationId,
        ) ||
        terminalGenerationPhases.has(
            terminalPhase,
        );

    if (alreadyTerminal) {
        generationTerminalPhase =
            generationIsStopRequested(
                localGenerationId,
            )
                ? 'stopped'
                : (
                    terminalGenerationPhases.has(
                        terminalPhase,
                    )
                        ? terminalPhase
                        : 'stopped'
                );

        clearGenerationStreamWork(
            localGenerationId,
        );

        clearGenerationTerminalTimer();

        // Do not try to reacquire or start a generation that is already
        // terminalizing/terminal. Its terminal path owns cleanup.
        if (
            terminalizingGenerationId !==
                localGenerationId
        ) {
            void sendGenerationTerminal(
                generationTerminalPhase,
            ).catch(error => warn(
                '[MCS] terminal confirmation after generation recovery failed',
                error,
            ));
        }

        updateGenerationUi();
        return true;
    }

    // The server generation disappeared, but this tab still has a live
    // native generation. Attempt authoritative ownership recovery rather
    // than blindly scheduling /generation/started against a generation
    // that the server no longer knows about.
    generationHeartbeatFailures = 0;

    renderBanner(
        'Reconnecting shared generation…',
    );

    void reacquireGenerationOwnership(
        'generation_recovered',
    ).then(recovered => {
        if (
            recovered &&
            localGeneration?.generationId ===
                localGenerationId &&
            terminalizingGenerationId !==
                localGenerationId &&
            !generationIsStopRequested(
                localGenerationId,
            )
        ) {
            generationMismatchSince = 0;
            updateGenerationUi();
        }
    }).catch(error => {
        warn(
            '[MCS] generation recovery reacquisition failed',
            error,
        );
    });

    updateGenerationUi();
    return true;
}

        generationServerReadyId = null;
        clearGenerationTerminalTimer();
        clearRemoteStreamState();
        pendingStream = null;
        streamInFlight = false;
        streamInFlightSeq = 0;
        generationHeartbeatFailures = 0;
        generationMismatchSince = 0;
        generationClaimInFlightId = null;
        generationStartPromise = null;
        generationStartPromiseId = null;

        renderBanner('Generation was recovered; shared chat was unlocked.');
        safeSetTimer(() => renderBanner(''), 1800);
        updateGenerationUi();
        return true;
    } catch (error) {
        warn('generation recovery confirmation failed', error);
        return false;
    }
}

function handleGenerationStreamEvent(data) {
    const g = data?.generation;
    if (!g || !g.generationId || !currentScope) return;
    if (isGenerationTerminated(g.generationId)) return;
    if (generationIsStopRequested(g.generationId)) return;

    const current = serverState?.generation;
    const currentTime = Number(current?.startedAt || current?.claimedAt || 0);
    const incomingTime = Number(g?.startedAt || g?.claimedAt || 0);
    if (current && current.generationId !== g.generationId && generationActive(current) && incomingTime && currentTime && incomingTime < currentTime) return;

    const eventRevision = Number(data?.revision || 0);
    if (eventRevision && eventRevision < Number(serverState?.revision || 0)) return;

    const seq = Number(data?.seq ?? g.seq ?? 0);
    const sameGeneration = current?.generationId === g.generationId;
    if (sameGeneration && current && seq < Number(current.seq || 0)) return;

    if (generationIsMine(g)) {
        if (generationClaimedThisPage || generationClaimInFlightId === g.generationId) {
            serverState = { ...(serverState || {}), revision: Math.max(Number(serverState?.revision || 0), eventRevision), generation: clone(g) };
            if (generationClaimedThisPage && localGeneration?.generationId === g.generationId) localGeneration = clone(g);
        }
        return;
    }

    if (remoteGenerationId !== g.generationId) {
        remoteGenerationId = g.generationId;
        lastRemoteStreamSeq = -1;
        suppressedRemoteStreamMessageIds.clear();
    }

    if (seq <= lastRemoteStreamSeq) return;

    const hadGap = seq > 0 && lastRemoteStreamSeq >= 0 && seq > lastRemoteStreamSeq + 1;
    if (hadGap) {
        // A stream gap invalidates the preview ordering. Start authoritative
        // reconciliation, but do not treat this event as proof that the
        // native chat is fully caught up — applyRemoteStreamNow stays a
        // preview path only.
        void resyncCurrentScope(scopeEpoch).catch(error => warn('stream gap resync failed', error));
    }

    lastRemoteStreamSeq = seq;
    serverState = {
        ...(serverState || {}),
        revision: Math.max(Number(serverState?.revision || 0), eventRevision),
        generation: clone(g),
    };

    if (!data.message || !currentScope || !nativeScopeStable(currentScope)) {
        updateGenerationUi();
        return;
    }

    pendingRemoteStream = {
        message: clone(data.message),
        messageIndex: Number.isInteger(data.messageIndex) ? data.messageIndex : null,
        generationId: g.generationId,
        seq,
    };
    scheduleRemoteRender();
    updateGenerationUi();
}

async function applyRemoteStreamNow(item) {
    if (!item || !ctx?.chat || !currentScope || !nativeScopeStable(currentScope)) return false;

    const g = serverState?.generation;
    if (!g || g.generationId !== item.generationId || generationIsMine(g)) return false;
    if (generationIsStopRequested(item.generationId)) return false;

    const id = messageId(item.message);
    if (!id || suppressedRemoteStreamMessageIds.has(id)) return false;
    if (Number(item.seq || 0) < Number(lastRemoteStreamSeq || 0)) return false;

    applyingRemoteDepth += 1;

    const epochAtStart = scopeEpoch;
    const nativeLoadEpochAtStart = nativeLoadEpoch;
    const expectedKey = makeScopeKey(currentScope);
    // Slim rollback state: only the touched message/index, never the whole chat.
    let previousIndex = -1;
    let previousMessage = null;
    let insertedIndex = -1;

    try {
        refreshLiveContext();
        if (!currentScope || !nativeScopeStable(currentScope)) return false;

        let index = ctx.chat.findIndex(message => messageId(message) === id);

        if (index < 0) {
            if (Number.isInteger(item.messageIndex) && item.messageIndex >= 0 && item.messageIndex < ctx.chat.length) {
                const existingAtIndex = ctx.chat[item.messageIndex];
                if (existingAtIndex && !existingAtIndex.is_user && !existingAtIndex.is_system) {
                    index = item.messageIndex;
                    previousIndex = index;
                    previousMessage = clone(ctx.chat[index]);
                    ctx.chat[index] = clone(item.message);
                } else {
                    return false;
                }
            } else {
                // Only reject an append when it would place a user/system
                // message after a user message; a normal assistant generation
                // preview appends legitimately.
                if (
                    ctx.chat.length &&
                    ctx.chat[ctx.chat.length - 1]?.is_user &&
                    (item.message?.is_user || item.message?.is_system)
                ) {
                    return false;
                }
                ctx.chat.push(clone(item.message));
                index = ctx.chat.length - 1;
                insertedIndex = index;
            }
        } else {
            previousIndex = index;
            previousMessage = clone(ctx.chat[index]);
            ctx.chat[index] = clone(item.message);
        }

        let updated = false;
        try {
            const result = ctx.updateMessageBlock?.(index, clone(ctx.chat[index]), { rerenderMessage: true });
            const domBlock = document.querySelector(`[mesid="${index}"]`);
            updated = result !== false && !!domBlock;
        } catch (error) {
            log('updateMessageBlock failed', error);
        }

        if (!updated) {
            try {
                await awaitablePrintMessages();
            } catch (error) {
                log('printMessages fallback failed', error);
                throw error;
            }
        }

        return true;
    } catch (error) {
        warn('applyRemoteStreamNow failed; rolling back preview', error);
        const scopeIntact = ctx?.chat &&
            scopeEpoch === epochAtStart &&
            nativeLoadEpoch === nativeLoadEpochAtStart &&
            currentScope &&
            makeScopeKey(currentScope) === expectedKey;

        if (scopeIntact) {
            try {
                if (insertedIndex >= 0) {
                    ctx.chat.splice(insertedIndex, 1);
                } else if (previousIndex >= 0 && previousMessage) {
                    ctx.chat[previousIndex] = previousMessage;
                }
                try { ctx.printMessages?.(); } catch { /* best effort restore */ }
            } catch (restoreError) {
                warn('applyRemoteStreamNow rollback failed', restoreError);
            }
        } else {
            warn('[MCS] skipped stream rollback because the native scope changed during apply');
        }
        return false;
    } finally {
        applyingRemoteDepth -= 1;
    }
}

function awaitablePrintMessages() {
    try {
        const result = ctx?.printMessages?.();
        if (result && typeof result.catch === 'function') result.catch(error => log('async printMessages fallback failed', error));
        return result;
    } catch (error) {
        throw error;
    }
}

function scheduleRemoteRender() {
    if (remoteRenderTimer) return;

    remoteRenderTimer = safeSetTimer(() => {
        remoteRenderTimer = null;
        const item = pendingRemoteStream;
        pendingRemoteStream = null;
        if (!item) return;

        const run = stateApplyChain.then(() => {
            if (isGenerationTerminated(item.generationId)) return false;
            return applyRemoteStreamNow(item);
        });

        stateApplyChain = run.then(() => undefined, error => warn('remote stream render failed', error));
        void run.finally(() => {
            if (pendingRemoteStream && !remoteRenderTimer) scheduleRemoteRender();
        });
    }, REMOTE_RENDER_MS);
}

async function handleGenerationTerminalEvent(data) {
    const terminalGeneration = data?.generation || null;
    const generationId = terminalGeneration?.generationId || data?.generationId || null;
    const revision = Number(data?.revision || 0);
    const currentRevision = Number(serverState?.revision || 0);
    if (!generationId) return false;

    const epochAtEvent = scopeEpoch;
    const mutationVersionAtStart = localMutationVersion;
    const nativeLoadEpochAtStart = nativeLoadEpoch;

    const activeId = localGeneration?.generationId || serverState?.generation?.generationId || null;
    if (activeId && activeId !== generationId) {
        rememberTerminatedGeneration(generationId);
        return true;
    }

    if (revision && currentRevision && revision < currentRevision) return true;
    if (isGenerationTerminated(generationId) && !localGenerationMatches(generationId)) return true;

    const scopeAtEvent = clone(currentScope);
    const hadLocalGeneration = !!localGeneration && localGeneration.generationId === generationId;
    const mine = hadLocalGeneration && !!terminalGeneration && generationIsMine(terminalGeneration);

    const terminalSnapshot = incomingSnapshot(data.snapshot || serverState?.snapshot || { messages: [], metadata: {} });
    const knownBase = baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} };
    const dirty = !mine && isLocalDirty(scopeAtEvent);
    const local = !mine && dirty ? syncSnapshot(durableSnapshot()) : null;

    rememberTerminatedGeneration(generationId);

    serverState = {
        ...(serverState || {}),
        revision: Math.max(currentRevision, revision),
        snapshot: clone(data.snapshot || serverState?.snapshot || { messages: [], metadata: {} }),
        generation: null,
    };
    baseSnapshot = serverState.snapshot;

    if (mine) {
        clearLocalGenerationState();
        if (mutationVersionAtStart === localMutationVersion) {
            clearLocalDirty(scopeAtEvent);
        } else {
            markLocalDirty(scopeAtEvent);
        }
    } else if (
        scopeAtEvent &&
        nativeScopeStable(scopeAtEvent) &&
        currentScopeGuard(epochAtEvent) &&
        nativeLoadEpochAtStart === nativeLoadEpoch &&
        data?.snapshot
    ) {
        let finalSnapshot = terminalSnapshot;
        if (dirty) finalSnapshot = mergeSnapshots(knownBase, local, terminalSnapshot);

        const applied = await applySnapshot(finalSnapshot, {
            save: true,
            render: true,
            expectedScope: scopeAtEvent,
            clearDirty: false,
            allowDuringGeneration: false,
            expectedGenerationId: generationId,
        });

        if (applied) {
            if (!deepEqual(finalSnapshot, terminalSnapshot) && currentScopeGuard(scopeEpoch)) {
                try {
                    const committed = await sendSnapshotDirect(finalSnapshot, Number(serverState?.revision || 0), newId(), scopeAtEvent);
                    serverState = committed.state;
                    baseSnapshot = committed.state.snapshot;
                } catch (error) {
                    if (error?.status === 409 && error?.payload?.state) {
                        serverState = error.payload.state;
                        baseSnapshot = error.payload.state.snapshot;
                    } else {
                        await enqueueSnapshot(finalSnapshot, Number(serverState?.revision || 0), baseSnapshot, scopeAtEvent);
                        scheduleQueueFlushRetry();
                    }
                }
            }
            if (mutationVersionAtStart === localMutationVersion) {
                clearLocalDirty(scopeAtEvent);
            } else {
                markLocalDirty(scopeAtEvent);
            }
        } else {
            await resyncCurrentScope(scopeEpoch);
        }

        renderBanner('Generation finished in another client.');
        safeSetTimer(() => renderBanner(''), 1500);
    }

    pendingStream = null;
    clearRemoteStreamState();
    streamInFlightSeq = 0;
    remoteStopInFlight = null;
    remoteStopGenerationId = null;
    remoteStopRequestedAt = 0;

    if (generationId === localGeneration?.generationId) {
        clearLocalGenerationState();
    }

    updateGenerationUi();
    await flushQueue();

    if (leaveAfterLocalGeneration && !localGeneration) {
        leaveAfterLocalGeneration = false;
        pendingScopeSwitchReason = '';
        await leaveCurrentScope();
        currentScope = null;
        scopeKeyValue = '';
        statusText('Disconnected');
        return true;
    }

    if (!nativeRestoreInProgress) {
        const pendingReason = pendingScopeSwitchReason;
        pendingScopeSwitchReason = '';
        void switchScope(pendingReason || 'post-generation-terminal');
    }

    return true;
}

function updateGenerationUi() {
    const g = serverState?.generation;

    if (localGeneration && (!g || g.generationId === localGeneration.generationId)) {
        const id = localGeneration.generationId;
        if (generationIsStopRequested(id) || generationTerminalPhase === 'stopped') {
            setSendLock('Stopping shared generation…');
            renderBanner('Stopping shared generation…');
        } else if (generationServerReadyId === id) {
            setSendLock('You are generating in this shared chat.');
            renderBanner(groupWrapperDepth > 0 ? 'Generating group response · shared with other clients' : 'Generating here · shared with other clients');
        } else {
            setSendLock('Reconnecting shared generation…');
            renderBanner('Reconnecting shared generation…');
        }
        return;
    }

    if (!generationActive(g)) {
        setSendLock('');
        renderBanner('');
        return;
    }

    if (generationIsStaleOwned(g)) {
        setSendLock('');
        renderBanner('Recovering abandoned generation…');
        return;
    }

    if (generationIsMine(g) && !localGeneration) {
        setSendLock('');
        renderBanner('Recovering abandoned generation…');
        return;
    }

    if (g.stopRequested || generationIsStopRequested(g.generationId)) {
        setSendLock('Another client requested Stop for this generation.');
        renderBanner('Stopping generation in another client…');
        return;
    }

    setSendLock('Another client is generating this shared chat.');
    renderBanner('Another client is generating this shared chat · live mirror');
}

function stopGenerationHeartbeat() {
    if (generationHeartbeatTimer) clearInterval(generationHeartbeatTimer);
    generationHeartbeatTimer = null;
    generationHeartbeatFailures = 0;
    generationHeartbeatInFlight = null;
    generationMismatchSince = 0;
}

function sseIsOpen() {
    if (!eventSource) return false;
    try {
        return eventSource.readyState === EventSource.OPEN;
    } catch {
        return false;
    }
}

function startHeartbeats(epoch) {
    if (heartbeatTimer) clearInterval(heartbeatTimer);

    heartbeatTimer = setInterval(async () => {
        if (!currentScopeGuard(epoch) || !serverState || nativeMembershipHeartbeatInFlight) return;

        refreshLiveContext();
        const nativeStable = nativeScopeStable(currentScope);
        if (!nativeStable && !localGeneration) {
            await switchScope('heartbeat-context-mismatch');
            return;
        }

        const scopeAtHeartbeat = clone(currentScope);
        const requestSeq = ++nativeHeartbeatRequestSeq;
        nativeMembershipHeartbeatInFlight = requestSeq;

        try {
            const result = await api('/heartbeat', 'POST', {
                scope: scopeAtHeartbeat,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
            });

            if (!currentScopeGuard(epoch) || requestSeq < nativeHeartbeatAppliedSeq) return;
            nativeHeartbeatAppliedSeq = requestSeq;

            const oldRevision = Number(serverState.revision || 0);
            const oldGenerationId = serverState.generation?.generationId || null;
            const newRevision = Number(result.revision || 0);
            const newGenerationId = result.generation?.generationId || null;

            if (newRevision < oldRevision) return;

            // While SSE is open or reconnecting, SSE is the sole authority for
            // revision, cursor, AND generation state. The heartbeat is only a
            // membership/lease channel; adopting its view here races the event
            // stream (e.g., stamping a revision before the matching SSE delta
            // is processed, making that delta look stale).
            // OPEN means SSE is currently authoritative. CONNECTING does not:
            // during a reconnect, heartbeat state is useful for detecting missed
            // revisions/generation changes and triggering an authoritative resync.
            if (sseIsOpen()) {
                updateGenerationUi();
                return;
            }

            serverState = {
                ...serverState,
                revision: newRevision,
                generation: clone(result.generation || null),
            };

            if (oldRevision !== newRevision || oldGenerationId !== newGenerationId) {
                await resyncCurrentScope(epoch);
                return;
            }

            updateGenerationUi();
        } catch (error) {
            if (error?.status === 403 && error?.payload?.error === 'not_member' && currentScopeGuard(epoch)) {
                await openScope(epoch);
                return;
            }
            log('membership heartbeat failed', error);
        } finally {
            if (nativeMembershipHeartbeatInFlight === requestSeq) nativeMembershipHeartbeatInFlight = null;
        }
    }, HEARTBEAT_MS);
}

async function reacquireGenerationOwnership(reason = 'recovery') {
    if (
        !localGeneration ||
        !localGenerationScope ||
        generationRecoveryInFlight ||
        terminalizingGenerationId
    ) {
        return false;
    }

    const generation = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration =
        localGenerationEpoch || scopeEpoch;
    const generationId = generation.generationId;

    if (
        !currentScopeGuard(epochAtGeneration) ||
        !nativeScopeStable(scopeAtGeneration)
    ) {
        return false;
    }

    if (
        generationIsStopRequested(generationId) ||
        terminalGenerationPhases.has(
            String(generationTerminalPhase || '').toLowerCase(),
        )
    ) {
        return false;
    }

    const run = (async () => {
        try {
            const stateResult = await api('/state', 'POST', {
                scope: scopeAtGeneration,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
            });

            if (
                !localGenerationMatches(
                    generationId,
                    scopeAtGeneration,
                ) ||
                !currentScopeGuard(epochAtGeneration) ||
                terminalizingGenerationId === generationId
            ) {
                return false;
            }

            const state = stateResult?.state || null;
            const current = state?.generation || null;

            if (
                current &&
                current.generationId === generationId &&
                generationIsMine(current)
            ) {
                serverState = state;
                baseSnapshot = state.snapshot;

                localGeneration = {
                    ...localGeneration,
                    ...clone(current),
                };

                localGenerationScope = clone(scopeAtGeneration);
                localGenerationEpoch = epochAtGeneration;

                generationMismatchSince = 0;

                if (current.stopRequested) {
                    rememberStopRequestedGeneration(generationId);
                    generationTerminalPhase = 'stopped';
                    clearGenerationStreamWork(generationId);
                    return false;
                }

                const phase = String(
                    current.phase || '',
                ).toLowerCase();

                if (terminalGenerationPhases.has(phase)) {
                    generationTerminalPhase = phase;
                    clearGenerationStreamWork(generationId);
                    return false;
                }

                if (
                    phase === 'started' ||
                    phase === 'streaming'
                ) {
                    generationServerReadyId = generationId;
                    startGenerationHeartbeat(epochAtGeneration);
                    updateGenerationUi();
                    return true;
                }

                generationServerReadyId = null;
                startGenerationHeartbeat(epochAtGeneration);

                scheduleGenerationStartRetry(
                    generationId,
                    250,
                );

                return await ensureGenerationStarted();
            }

            if (
                current &&
                generationActive(current) &&
                current.generationId !== generationId
            ) {
                generationMismatchSince =
                    generationMismatchSince || Date.now();

                log(
                    '[MCS] competing generation observed during recovery',
                    {
                        reason,
                        generationId,
                        competing: current.generationId,
                    },
                );

                return false;
            }

            if (
                current &&
                current.generationId === generationId &&
                !generationIsMine(current)
            ) {
                generationMismatchSince =
                    generationMismatchSince || Date.now();
                return false;
            }

            const authoritativeSnapshot = normalizeSnapshot(
                state?.snapshot || {
                    messages: [],
                    metadata: {},
                },
            );

            const localSnapshot = syncSnapshot(
                durableSnapshot(),
            );

            const recoveryBase =
                localGenerationBaseSnapshot ||
                baseSnapshot ||
                serverState?.snapshot || {
                    messages: [],
                    metadata: {},
                };

            let desired = mergeSnapshots(
                recoveryBase,
                localSnapshot,
                authoritativeSnapshot,
            );

            let claimBase = authoritativeSnapshot;
            let revision = Number(
                state?.revision || 0,
            );

            let claimResult = null;
            let claimOpId = newId();

            for (
                let attempt = 0;
                attempt < 4;
                attempt += 1
            ) {
                if (
                    !localGenerationMatches(
                        generationId,
                        scopeAtGeneration,
                    ) ||
                    !currentScopeGuard(epochAtGeneration) ||
                    !nativeScopeStable(scopeAtGeneration) ||
                    terminalizingGenerationId === generationId ||
                    generationIsStopRequested(generationId)
                ) {
                    return false;
                }

                try {
                    claimResult = await api(
                        '/generation/claim',
                        'POST',
                        {
                            scope: scopeAtGeneration,
                            clientId,
                            deviceId,
                            connectionId: membershipConnectionId,
                            opId: claimOpId,
                            generationId,
                            generationType: String(
                                generation.generationType ||
                                'normal',
                            ),
                            baseRevision: revision,
                            snapshot: desired,
                        },
                    );

                    break;
                } catch (error) {
                    if (
                        error?.status === 409 &&
                        error?.payload?.state
                    ) {
                        const conflictState =
                            error.payload.state;

                        const conflictGeneration =
                            conflictState.generation ||
                            null;

                        if (
                            conflictGeneration &&
                            conflictGeneration.generationId !==
                                generationId &&
                            generationActive(
                                conflictGeneration,
                            )
                        ) {
                            serverState = conflictState;
                            baseSnapshot =
                                conflictState.snapshot;

                            generationMismatchSince =
                                generationMismatchSince ||
                                Date.now();

                            return false;
                        }

                        const remoteSnapshot =
                            conflictState.snapshot || {
                                messages: [],
                                metadata: {},
                            };

                        desired = mergeSnapshots(
                            claimBase,
                            desired,
                            remoteSnapshot,
                        );

                        claimBase = remoteSnapshot;
                        revision = Number(
                            conflictState.revision || 0,
                        );

                        serverState = conflictState;
                        baseSnapshot = remoteSnapshot;

                        // New payload => new logical operation ID.
                        claimOpId = newId();

                        continue;
                    }

                    // The request may have committed even though the
                    // response was lost. Prove it before retrying.
                    const confirmedResult = await api(
                        '/state',
                        'POST',
                        {
                            scope: scopeAtGeneration,
                            clientId,
                            deviceId,
                            connectionId: membershipConnectionId,
                        },
                    ).catch(() => null);

                    const confirmedState =
                        confirmedResult?.state || null;

                    const confirmedGeneration =
                        confirmedState?.generation || null;

                    if (
                        confirmedState &&
                        confirmedGeneration?.generationId ===
                            generationId &&
                        generationIsMine(
                            confirmedGeneration,
                        )
                    ) {
                        claimResult = {
                            state: confirmedState,
                        };
                        break;
                    }

                    if (
                        confirmedGeneration &&
                        confirmedGeneration.generationId !==
                            generationId &&
                        generationActive(
                            confirmedGeneration,
                        ) &&
                        !generationIsMine(
                            confirmedGeneration,
                        )
                    ) {
                        serverState = confirmedState;
                        baseSnapshot =
                            confirmedState.snapshot;

                        generationMismatchSince =
                            generationMismatchSince ||
                            Date.now();

                        return false;
                    }

                    // Exact same payload => same opId.
                    if (attempt < 3) {
                        await sleep(
                            Math.min(
                                250 * 2 ** attempt,
                                1000,
                            ),
                        );
                        continue;
                    }

                    throw error;
                }
            }

            if (!claimResult?.state) {
                return false;
            }

            if (
                !currentScopeGuard(epochAtGeneration) ||
                !nativeScopeStable(scopeAtGeneration)
            ) {
                return false;
            }

            const claimed =
                claimResult.state.generation;

            if (
                !claimed ||
                claimed.generationId !== generationId ||
                !generationIsMine(claimed)
            ) {
                return false;
            }

            serverState = claimResult.state;
            baseSnapshot =
                claimResult.state.snapshot;

            localGeneration = clone(claimed);
            localGenerationScope =
                clone(scopeAtGeneration);
            localGenerationEpoch =
                epochAtGeneration;

            localGenerationBaseSnapshot =
                clone(
                    claimResult.state.snapshot || {
                        messages: [],
                        metadata: {},
                    },
                );

            localGenerationBaseRevision =
                Number(
                    claimResult.state.revision || 0,
                );

            localGenerationSettings = {
                syncMessages:
                    !!settings.syncMessages,
                syncMetadata:
                    !!settings.syncMetadata,
            };

            localStreamMessageId = null;
            localStreamMessageIndex = null;
            generationClaimedThisPage = true;
            generationTerminalPhase = null;
            generationMismatchSince = 0;
            leaveAfterLocalGeneration = false;

            // The claim has now committed. Bring native ST to the exact
            // snapshot the server accepted. Do this AFTER the claim, never
            // before it, so a failed recovery claim cannot silently rewrite
            // native chat state.
            if (
                !deepEqual(
                    syncSnapshot(durableSnapshot()),
                    normalizeSnapshot(
                        claimResult.state.snapshot || {
                            messages: [],
                            metadata: {},
                        },
                    ),
                )
            ) {
                const applied = await applySnapshot(
                    desired,
                    {
                        save: true,
                        render: true,
                        expectedScope:
                            scopeAtGeneration,
                        clearDirty: false,
                    },
                );

                if (
                    !applied ||
                    !currentScopeGuard(
                        epochAtGeneration,
                    ) ||
                    !nativeScopeStable(
                        scopeAtGeneration,
                    )
                ) {
                    return false;
                }
            }

            markLocalDirty(scopeAtGeneration);

            rebuildLastSyncedMap(
                syncSnapshot(
                    durableSnapshot(),
                ).messages,
            );

            updateGenerationUi();
            startGenerationHeartbeat(
                epochAtGeneration,
            );

            return await ensureGenerationStarted();
        } catch (error) {
            if (
                error?.status === 409 &&
                error?.payload?.state
            ) {
                const state =
                    error.payload.state;

                if (
                    currentScopeGuard(
                        epochAtGeneration,
                    )
                ) {
                    serverState = state;
                    baseSnapshot = state.snapshot;
                }

                const competing =
                    state?.generation;

                if (
                    competing &&
                    competing.generationId !==
                        generationId &&
                    generationActive(
                        competing,
                    )
                ) {
                    generationMismatchSince =
                        generationMismatchSince ||
                        Date.now();
                }
            }

            log(
                '[MCS] generation ownership recovery failed; keeping native generation alive',
                reason,
                error,
            );

            return false;
        }
    })();

    generationRecoveryInFlight = run;

    try {
        return await run;
    } finally {
        if (generationRecoveryInFlight === run) {
            generationRecoveryInFlight = null;
        }
    }
}

function startGenerationHeartbeat(epoch) {
    stopGenerationHeartbeat();
    if (!localGeneration || !localGenerationScope) return;

    const generationId = localGeneration.generationId;
    const scopeAtGeneration = clone(localGenerationScope);
    localGenerationEpoch = epoch;

    generationHeartbeatTimer = setInterval(async () => {
        if (!localGeneration || localGeneration.generationId !== generationId || !currentScopeGuard(epoch)) return;
        if (generationHeartbeatInFlight) return;

        refreshLiveContext();
        if (!nativeScopeStable(scopeAtGeneration)) generationMismatchSince = generationMismatchSince || Date.now();
        else generationMismatchSince = 0;

        const heartbeatRun = (async () => {
            try {
                const result = await api('/generation/heartbeat', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                    generationId,
                });

if (
    !localGeneration ||
    localGeneration.generationId !== generationId ||
    !currentScopeGuard(epoch) ||
    terminalizingGenerationId === generationId
) {
    return;
}

// A heartbeat response can have been generated before terminalization
// committed. Never let that stale response resurrect readiness or streaming.
if (generationIsStopRequested(generationId)) {
    rememberStopRequestedGeneration(generationId);
    return;
}

// Compact response: merge, never replace.
mergeCompactState(result.state);

                if (result.stopRequested || result.state?.generation?.stopRequested) {
                    rememberStopRequestedGeneration(generationId);
                    generationTerminalPhase = 'stopped';
                    remoteStopGenerationId = generationId;
                    clearGenerationTerminalTimer();
                    if (streamTimer) clearTimeout(streamTimer);
                    if (streamRetryTimer) clearTimeout(streamRetryTimer);
                    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);
                    streamTimer = null;
                    streamRetryTimer = null;
                    streamCaptureTimer = null;
                    pendingStream = null;
                    renderBanner('Stopping generation…');
                    try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                    return;
                }

                const stateGeneration = result.state?.generation || null;
if (
    stateGeneration &&
    stateGeneration.generationId === generationId &&
    generationIsMine(stateGeneration)
) {
    const phase = String(
        stateGeneration.phase || '',
    ).toLowerCase();

    if (terminalGenerationPhases.has(phase)) {
        generationTerminalPhase = phase;

        if (
            stateGeneration.stopRequested ||
            phase === 'stopped'
        ) {
            rememberStopRequestedGeneration(
                generationId,
            );
        }

        clearGenerationStreamWork(
            generationId,
        );
        clearGenerationTerminalTimer();

        void sendGenerationTerminal(phase)
            .catch(error => warn(
                '[MCS] terminal cleanup after heartbeat terminal state failed',
                error,
            ));

        return;
    }

    if (terminalizingGenerationId === generationId) {
        return;
    }

    localGeneration = {
        ...localGeneration,
        ...clone(stateGeneration),
    };

    generationServerReadyId =
        ['started', 'streaming'].includes(phase)
            ? generationId
            : generationServerReadyId;

    generationHeartbeatFailures = 0;
    generationMismatchSince = 0;

    updateGenerationUi();
    return;
}

                const confirmedResult = await api('/state', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                }).catch(() => null);

                if (!localGeneration || localGeneration.generationId !== generationId || !currentScopeGuard(epoch)) return;

                const confirmedState = confirmedResult?.state || null;
                const confirmed = confirmedState?.generation || null;

                if (confirmed && confirmed.generationId === generationId && generationIsMine(confirmed)) {
                    serverState = confirmedState;
                    localGeneration = clone(confirmed);
                    generationServerReadyId = ['started', 'streaming'].includes(confirmed.phase) ? generationId : generationServerReadyId;
                    generationMismatchSince = 0;
                    return;
                }

if (!confirmed) {
    const terminalPhase = String(
        generationTerminalPhase || '',
    ).toLowerCase();

    const alreadyTerminal =
        terminalizingGenerationId === generationId ||
        generationIsStopRequested(generationId) ||
        terminalGenerationPhases.has(terminalPhase);

    if (alreadyTerminal) {
        clearGenerationStreamWork(
            generationId,
        );
        clearGenerationTerminalTimer();

        if (
            terminalizingGenerationId !==
                generationId &&
            localGeneration?.generationId ===
                generationId
        ) {
            void sendGenerationTerminal(
                generationIsStopRequested(
                    generationId,
                )
                    ? 'stopped'
                    : terminalPhase ||
                        'stopped',
            ).catch(error => warn(
                '[MCS] terminal after lost generation failed',
                error,
            ));
        }

        return;
    }

    generationMismatchSince = 0;

    await openScope(epoch);

    if (
        localGeneration?.generationId ===
            generationId &&
        !generationIsStopRequested(
            generationId,
        ) &&
        terminalizingGenerationId !==
            generationId &&
        !terminalGenerationPhases.has(
            String(
                generationTerminalPhase || '',
            ).toLowerCase(),
        )
    ) {
        void reacquireGenerationOwnership(
            'heartbeat-recovery',
        ).catch(error => warn(
            '[MCS] heartbeat recovery failed',
            error,
        ));
    }

    return;
}

                if (confirmed.generationId !== generationId && generationActive(confirmed)) {
                    generationMismatchSince = generationMismatchSince || Date.now();
                    if (Date.now() - generationMismatchSince < OWNERSHIP_CONFLICT_GRACE_MS) return;

                    const finalStateResult = await api('/state', 'POST', {
                        scope: scopeAtGeneration,
                        clientId,
                        deviceId,
                        connectionId: membershipConnectionId,
                    }).catch(() => null);

                    const finalState = finalStateResult?.state || null;
                    const finalGeneration = finalState?.generation || null;

if (
    finalGeneration &&
    finalGeneration.generationId !== generationId &&
    generationActive(finalGeneration) &&
    !generationIsMine(finalGeneration)
) {
    generationTerminalPhase = 'stopped';
    rememberStopRequestedGeneration(
        generationId,
    );
    clearGenerationStreamWork(
        generationId,
    );

    try {
        const stopped =
            ctx?.stopGeneration?.();

        if (
            stopped === false &&
            localGeneration?.generationId ===
                generationId
        ) {
            void sendGenerationTerminal(
                'stopped',
            ).catch(error => warn(
                '[MCS] terminal after ownership loss failed',
                error,
            ));
        }
    } catch (error) {
        warn(
            '[MCS] failed stopping local generation after ownership loss',
            error,
        );

        if (
            localGeneration?.generationId ===
            generationId
        ) {
            void sendGenerationTerminal(
                'stopped',
            ).catch(terminalError => warn(
                '[MCS] fallback ownership-loss terminal failed',
                terminalError,
            ));
        }
    }
} else if (
    finalGeneration?.generationId ===
        generationId &&
    generationIsMine(finalGeneration)
) {
                        serverState = finalState;
                        localGeneration = clone(finalGeneration);
                        generationMismatchSince = 0;
                    } else {
                        generationMismatchSince = 0;
                        void reacquireGenerationOwnership('post-conflict-recovery');
                    }
                }
} catch (error) {
    generationHeartbeatFailures += 1;

    // Terminalization owns this generation now. Do not start recovery,
    // readiness retries, or ownership reacquisition from a stale heartbeat.
    if (terminalizingGenerationId === generationId) {
        return;
    }

                if (error?.status === 403 && error?.payload?.error === 'not_member') {
                    await openScope(epoch);
                    return;
                }

                if (error?.status === 409 && ['generation_not_owned', 'generation_expired'].includes(error?.payload?.error)) {
                    const immediate = error?.payload?.state || null;
                    const immediateGeneration = immediate?.generation || null;

                    if (immediateGeneration && immediateGeneration.generationId === generationId && generationIsMine(immediateGeneration)) {
                        serverState = immediate;
                        localGeneration = clone(immediateGeneration);
                        generationServerReadyId = ['started', 'streaming'].includes(immediateGeneration.phase) ? generationId : generationServerReadyId;
                        generationMismatchSince = 0;
                        return;
                    }

                    generationMismatchSince = generationMismatchSince || Date.now();
if (
    !generationIsStopRequested(generationId) &&
    !terminalizingGenerationId &&
    !terminalGenerationPhases.has(
        String(
            generationTerminalPhase || '',
        ).toLowerCase(),
    ) &&
    Date.now() - generationMismatchSince >=
        OWNERSHIP_RECOVERY_GRACE_MS
) {
    void reacquireGenerationOwnership(
        'heartbeat-409-recovery',
    ).catch(error => warn(
        '[MCS] heartbeat ownership recovery failed',
        error,
    ));
}
                    return;
                }

                if (localGeneration?.generationId === generationId && !generationServerReadyId) {
                    scheduleGenerationStartRetry(generationId, 1000);
                }

                log('generation heartbeat failed; continuing local generation', error);
            } finally {
                generationHeartbeatInFlight = null;
            }
        })();

        generationHeartbeatInFlight = heartbeatRun;
        await heartbeatRun.catch(() => { /* handled */ });
    }, GENERATION_HEARTBEAT_MS);
}

async function resyncCurrentScopeInternal(epoch = scopeEpoch) {
    if (!currentScope || !currentScopeGuard(epoch)) return;
    if (!nativeScopeStable(currentScope)) return;

    const scopeAtRequest = clone(currentScope);
    const mutationVersionAtStart = localMutationVersion;
    const nativeLoadEpochAtStart = nativeLoadEpoch;

    try {
        const result = await api('/state', 'POST', {
            scope: scopeAtRequest,
            clientId,
            deviceId,
            connectionId: membershipConnectionId,
        });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtRequest)) return;

        const state = result.state;
        const serverGeneration = state.generation || null;
        if (serverGeneration?.stopRequested) rememberStopRequestedGeneration(serverGeneration.generationId);

        // Native chat changed while the resync request was in flight: never
        // apply the stale remote snapshot over it. Record the authoritative
        // state and durably queue the local one for reconciliation.
        if (mutationVersionAtStart !== localMutationVersion || nativeLoadEpochAtStart !== nativeLoadEpoch) {
            serverState = state;
            baseSnapshot = state.snapshot;
            lastSseEventId = Number(state?.lastEventId || lastSseEventId);

            if (currentScopeGuard(epoch) && nativeScopeStable(scopeAtRequest)) {
                const latestLocal = syncSnapshot(durableSnapshot());
                markLocalDirty(scopeAtRequest);
                await enqueueSnapshot(
                    latestLocal,
                    Number(state.revision || 0),
                    state.snapshot || { messages: [], metadata: {} },
                    scopeAtRequest,
                    'snapshot',
                    null,
                    newId(),
                );
                scheduleQueueFlushRetry();
            }
            return;
        }

        const remote = incomingSnapshot(state.snapshot);
        const dirty = isLocalDirty(scopeAtRequest);
        const local = syncSnapshot(durableSnapshot());
        const knownBase = baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} };

        serverState = state;
        baseSnapshot = state.snapshot;
        lastSseEventId = Number(state?.lastEventId || lastSseEventId);

        if (localGeneration) {
            const localId = localGeneration.generationId;

            if (serverGeneration && serverGeneration.generationId === localId && generationIsMine(serverGeneration)) {
                localGeneration = { ...localGeneration, ...clone(serverGeneration) };
                localGenerationScope = clone(scopeAtRequest);
                localGenerationEpoch = epoch;
                generationServerReadyId = ['started', 'streaming'].includes(serverGeneration.phase) ? localId : generationServerReadyId;
                generationMismatchSince = 0;
                if (serverGeneration.stopRequested) rememberStopRequestedGeneration(localId);
            } else if (serverGeneration && serverGeneration.generationId !== localId && generationActive(serverGeneration) && !generationIsMine(serverGeneration)) {
                generationMismatchSince = generationMismatchSince || Date.now();
                if (Date.now() - generationMismatchSince >= OWNERSHIP_CONFLICT_GRACE_MS) {
                    const confirm = await api('/state', 'POST', {
                        scope: scopeAtRequest,
                        clientId,
                        deviceId,
                        connectionId: membershipConnectionId,
                    }).catch(() => null);
                    const confirmed = confirm?.state?.generation || null;
                    if (confirmed?.generationId === localId && generationIsMine(confirmed)) {
                        serverState = confirm.state;
                        localGeneration = clone(confirmed);
                        generationMismatchSince = 0;
                    } else if (confirmed && confirmed.generationId !== localId && generationActive(confirmed) && !generationIsMine(confirmed)) {
                        generationTerminalPhase = 'stopped';
                        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                    }
                }
} else if (!serverGeneration) {
    generationMismatchSince = 0;

    const terminalPhase = String(
        generationTerminalPhase || '',
    ).toLowerCase();

    const alreadyTerminal =
        terminalizingGenerationId === localId ||
        generationIsStopRequested(localId) ||
        terminalGenerationPhases.has(terminalPhase);

    if (!alreadyTerminal) {
        void reacquireGenerationOwnership(
            'resync-no-generation',
        ).catch(error => warn(
            '[MCS] generation reacquisition after resync failed',
            error,
        ));
    }
}
        } else if (serverGeneration && generationIsMine(serverGeneration)) {
            if (!generationClaimedThisPage && generationClaimInFlightId !== serverGeneration.generationId) {
                const staleId = serverGeneration.generationId;
                try {
                    const cleared = await api('/generation/terminal', 'POST', {
                        scope: scopeAtRequest,
                        clientId,
                        deviceId,
                        connectionId: membershipConnectionId,
                        generationId: staleId,
                        phase: 'stopped',
                        snapshot: clone(state.snapshot),
                        opId: newId(),
                    });
                    serverState = cleared.state;
                    baseSnapshot = cleared.state.snapshot;
                    lastSseEventId = Number(cleared.state?.lastEventId || lastSseEventId);
                } catch (error) {
                    if (error?.status === 409 && error?.payload?.state) {
                        serverState = error.payload.state;
                        baseSnapshot = error.payload.state.snapshot;
                    }
                }
            }
        }

        const effectiveGeneration = serverState.generation || null;
        if (effectiveGeneration?.stopRequested) rememberStopRequestedGeneration(effectiveGeneration.generationId);

        if (!effectiveGeneration && !localGeneration) {
            if (dirty) {
                const merged = mergeSnapshots(knownBase, local, remote);
                if (!deepEqual(local, merged)) {
                    const applied = await applySnapshot(merged, {
                        save: true,
                        render: true,
                        expectedScope: scopeAtRequest,
                        clearDirty: false,
                    });
                    if (!applied) return;
                }

                if (!deepEqual(merged, remote) && nativeScopeStable(scopeAtRequest)) {
                    try {
                        const publishResult = await sendSnapshotDirect(merged, Number(serverState.revision), newId(), scopeAtRequest);
                        serverState = publishResult.state;
                        baseSnapshot = publishResult.state.snapshot;
                        if (mutationVersionAtStart === localMutationVersion) {
                            clearLocalDirty(scopeAtRequest);
                        }
                        rebuildLastSyncedMap(merged.messages);
                    } catch (publishError) {
                        if (publishError?.status === 409 && publishError?.payload?.state) {
                            serverState = publishError.payload.state;
                            baseSnapshot = publishError.payload.state.snapshot;
                        } else {
                            await enqueueSnapshot(merged, Number(serverState.revision), serverState.snapshot, scopeAtRequest);
                            scheduleQueueFlushRetry();
                        }
                    }
                } else {
                    if (mutationVersionAtStart === localMutationVersion) {
                        clearLocalDirty(scopeAtRequest);
                    }
                    rebuildLastSyncedMap(merged.messages);
                }
            } else if (!deepEqual(local, remote)) {
                const applied = await applySnapshot(remote, {
                    save: true,
                    render: true,
                    expectedScope: scopeAtRequest,
                });
                if (!applied) return;
                if (mutationVersionAtStart === localMutationVersion) {
                    clearLocalDirty(scopeAtRequest);
                }
            } else {
                rebuildLastSyncedMap(remote.messages);
            }
        }

        updateGenerationUi();
    } catch (error) {
        warn('resync failed', error);
    }
}

// Single-flight: N concurrent callers for the same scope+epoch share ONE
// /state request instead of queueing N sequential ones.
function resyncCurrentScope(epoch = scopeEpoch) {
    if (!currentScope) return Promise.resolve();

    const key = `${scopeKeyValue}:${epoch}`;

    if (resyncInFlight && resyncInFlightKey === key) {
        return resyncInFlight;
    }

    // Do not globally serialize different scopes behind one stale /state
    // request. Epoch/scope guards make an old result harmless.
    const run = Promise.resolve()
        .then(() => resyncCurrentScopeInternal(epoch))
        .catch(error => warn('resync failed', error));

    resyncInFlight = run;
    resyncInFlightKey = key;

    void run.finally(() => {
        if (resyncInFlight === run) {
            resyncInFlight = null;
            resyncInFlightKey = '';
        }
    });

    return run;
}

async function terminateGenerationOnServer(generation, scope, phase, snapshot, opId = null) {
    let lastError = null;
    const terminalOpId = opId || newId();

    for (let attempt = 0; attempt < 4; attempt += 1) {
        try {
            const result = await api('/generation/terminal', 'POST', {
                scope,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
                generationId: generation.generationId,
                phase,
                snapshot,
                opId: terminalOpId,
            });
            return { success: true, state: result.state, error: null };
        } catch (error) {
            lastError = error;
            if (error?.status === 409 && error?.payload?.state) {
                const state = error.payload.state;
                const current = state.generation;
                if (!current) return { success: true, state, error: null };
                if (current.generationId !== generation.generationId) return { success: true, state, error: null };
            }
            if (attempt < 3) await sleep(200 * (attempt + 1));
        }
    }

    try {
        const stateResult = await api('/state', 'POST', {
            scope,
            clientId,
            deviceId,
            connectionId: membershipConnectionId,
        });
        const state = stateResult.state;
        if (!state?.generation || state.generation.generationId !== generation.generationId) {
            return { success: true, state, error: null };
        }
        return { success: false, state, error: lastError };
    } catch (error) {
        return { success: false, state: null, error: lastError || error };
    }
}

async function leaveCurrentScope({
    preserveNativeGeneration = false,
} = {}) {
    if (joinAbortController) {
        try {
            joinAbortController.abort();
        } catch {
            /* ignore */
        }

        joinAbortController = null;
    }

    if (!currentScope) return;

    const leavingScope = clone(currentScope);
    const leavingGenerationId =
        localGeneration?.generationId || null;

    // Do not queue a pre-terminalization generation snapshot. The generation
    // terminal snapshot is newer and authoritative. Queueing the older state
    // first could later overwrite the final generation state.
    if (
        isLocalDirty(leavingScope) &&
        nativeScopeStable(leavingScope) &&
        (!localGeneration || preserveNativeGeneration)
    ) {
        try {
            const latestSnapshot =
                syncSnapshot(
                    durableSnapshot(),
                );

            await enqueueSnapshot(
                latestSnapshot,
                Number(
                    serverState?.revision || 0,
                ),
                serverState?.snapshot || {
                    messages: [],
                    metadata: {},
                },
                leavingScope,
                'snapshot',
                null,
                newId(),
            );
        } catch (error) {
            warn(
                '[MCS] failed to durably queue local state before leaving scope',
                error,
            );
        }
    }

    if (
        localGeneration &&
        localGenerationScope &&
        !preserveNativeGeneration
    ) {
        const generationIdBeforeLeave =
            localGeneration.generationId;

        try {
            ctx?.stopGeneration?.();
        } catch {
            /* ignore */
        }

        let terminalized = false;

        try {
            terminalized =
                await sendGenerationTerminal(
                    'stopped',
                );
        } catch (error) {
            warn(
                'generation cleanup failed while leaving scope',
                error,
            );
        }

        // If terminalization was ambiguous/failed, preserve the latest native
        // generation state in the durable queue before tearing the scope down.
        if (
            !terminalized &&
            nativeScopeStable(leavingScope)
        ) {
            try {
                refreshLiveContext();

                const finalSnapshot =
                    syncSnapshot(
                        durableSnapshot(),
                    );

                markLocalDirty(
                    leavingScope,
                );

                await enqueueSnapshot(
                    finalSnapshot,
                    Number(
                        serverState?.revision || 0,
                    ),
                    serverState?.snapshot ||
                        localGenerationBaseSnapshot || {
                            messages: [],
                            metadata: {},
                        },
                    leavingScope,
                    'snapshot',
                    null,
                    newId(),
                );

                scheduleQueueFlushRetry();
            } catch (error) {
                warn(
                    `[MCS] failed to queue final generation snapshot while leaving scope (${generationIdBeforeLeave})`,
                    error,
                );
            }
        }
    }

    try {
        await api('/leave', 'POST', {
            scope: leavingScope,
            clientId,
            deviceId,
            connectionId: membershipConnectionId,
        });
    } catch {
        /* best effort */
    }

    disconnectSse();
    stopHeartbeats();
    stopGenerationHeartbeat();

    if (scopeRetryTimer) {
        clearTimeout(scopeRetryTimer);
    }

    if (queueRetryTimer) {
        clearTimeout(queueRetryTimer);
    }

    if (generationStartRetryTimer) {
        clearTimeout(generationStartRetryTimer);
    }

    if (terminalRetryTimer) {
        clearTimeout(terminalRetryTimer);
    }

    if (streamTimer) {
        clearTimeout(streamTimer);
    }

    if (streamRetryTimer) {
        clearTimeout(streamRetryTimer);
    }

    if (remoteRenderTimer) {
        clearTimeout(remoteRenderTimer);
    }

    if (streamCaptureTimer) {
        clearTimeout(streamCaptureTimer);
    }

    if (remoteUiRefreshTimer) {
        clearTimeout(remoteUiRefreshTimer);
    }

    if (localPublishTimer) {
        clearTimeout(localPublishTimer);
    }

    scopeRetryTimer = null;
    queueRetryTimer = null;
    generationStartRetryTimer = null;
    terminalRetryTimer = null;
    streamTimer = null;
    streamRetryTimer = null;
    streamCaptureTimer = null;
    remoteUiRefreshTimer = null;
    localPublishTimer = null;

    serverState = null;
    baseSnapshot = null;

    clearLocalGenerationState();
    clearRemoteStreamState();
    resetChunkAssemblies();

    lastSyncedMessageMap = new Map();
    lastSseEventId = 0;
    nativeHeartbeatAppliedSeq = 0;
    nativeHeartbeatRequestSeq = 0;
    membershipConnectionId = null;

    setSendLock('');
    setRemoteSendButtonMode(false);
    renderBanner('');
    clearLocalDirty();

    log(
        '[MCS] left scope',
        leavingScope,
        leavingGenerationId,
    );
}

function switchScopeInternal(reason = 'scope-change') {
    return (async () => {
        if (nativeRestoreInProgress) return;

        refreshLiveContext();
        const nextScope = scopeFromContext();
        const nextKey = makeScopeKey(nextScope);

        if (!nextScope) {
            statusText('Waiting for active chat…');
            if (settings.enabled && settings.autoConnect && !scopeRetryTimer && !activationInProgress) {
                scopeRetryTimer = safeSetTimer(() => {
                    scopeRetryTimer = null;
                    switchScope('startup-retry').catch(error => warn('startup scope retry failed', error));
                }, 500);
            }
            return;
        }

if (nextKey === scopeKeyValue && currentScope) {
    if (!nativeScopeStable(nextScope)) {
        const stable = await waitForNativeScope(
            nextScope,
            5000,
            100,
        );

        if (!stable || !currentScopeGuard(scopeEpoch)) {
            return;
        }
    }

    if (
        !serverState &&
        settings.enabled &&
        settings.autoConnect
    ) {
        await openScope(scopeEpoch);
    } else {
        updateGenerationUi();
    }

    return;
}

        if (localGeneration && currentScope) {
            pendingScopeSwitchReason = reason;
            log('[MCS] deferring scope switch until active generation ends', { reason, from: currentScope, to: nextScope });
            return;
        }

        // The native chat-load lifetime advances with the distributed
        // connection lifetime, but they are checked independently.
        ++nativeLoadEpoch;
        ++scopeEpoch;
        const epoch = scopeEpoch;
        clearGenerationTerminalTimer();
        await leaveCurrentScope();

currentScope = nextScope;
scopeKeyValue = nextKey;
localDirty = false;
localDirtyScopeKey = '';
lastSseEventId = 0;
lastSyncedMessageMap = new Map();

// CRITICAL: establish the authoritative server membership/snapshot first.
// Do not write IDs into native ST while the native chat loader may still be
// replacing ctx.chat or chat metadata.
if (
    settings.enabled &&
    settings.autoConnect
) {
    await openScope(epoch);

    if (
        !currentScopeGuard(epoch) ||
        !nativeScopeStable(nextScope)
    ) {
        return;
    }

    // The chat is now connected and the native scope has stabilized.
    // Only now is it safe to persist message IDs.
    await ensureIdsPersisted(nextScope);
}
    })();
}

function switchScope(reason = 'scope-change') {
    const run = scopeSwitchChain.then(() => switchScopeInternal(reason));
    scopeSwitchChain = run.then(() => undefined, error => warn('scope switch failed', error));
    return run;
}

function shouldBypassMcsGeneration(type) {
    return quietGenerationTypes.has(String(type || '').toLowerCase());
}

function markManualGenerationRequest() {
    manualGenerationRequestAt = Date.now();
}

function consumeManualGenerationRequest(maxAgeMs = 1500) {
    if (!manualGenerationRequestAt) return false;
    const age = Date.now() - manualGenerationRequestAt;
    manualGenerationRequestAt = 0;
    return age >= 0 && age <= maxAgeMs;
}

function nativeGenerationLooksActive() {
    refreshLiveContext();
    const stop = document.querySelector('#mes_stop');
    let stopVisible = false;
    if (stop) {
        try {
            const style = getComputedStyle(stop);
            stopVisible = !stop.hidden && style.display !== 'none' && style.visibility !== 'hidden';
        } catch {
            stopVisible = !stop.hidden;
        }
    }
    return !!(ctx?.streamingProcessor || document.body?.dataset?.generating === 'true' || stopVisible);
}

async function ensureGenerationStarted() {
    if (!localGeneration || !localGenerationScope) return false;

    const generationId = localGeneration.generationId;
    const scopeAtGeneration = clone(localGenerationScope);

    // No start/continuation racing an in-flight terminalization of the same
    // generation — that is the terminal/continuation race.
    if (terminalizingGenerationId === generationId) return false;
    if (generationIsStopRequested(generationId)) return false;
    if (generationServerReadyId === generationId) return true;
    if (!localGenerationMatches(generationId, scopeAtGeneration)) return false;

    if (generationStartPromise && generationStartPromiseId === generationId) return await generationStartPromise;

    generationStartPromiseId = generationId;
    generationStartPromise = (async () => {
        let lastError = null;

        for (let attempt = 0; attempt < 10; attempt += 1) {
            try {
                if (!localGenerationMatches(generationId, scopeAtGeneration)) return false;
                if (generationIsStopRequested(generationId)) return false;
                if (terminalizingGenerationId === generationId) return false;

                const result = await api('/generation/started', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                    generationId,
                });

                if (
                    !localGenerationMatches(generationId, scopeAtGeneration) ||
                    terminalizingGenerationId === generationId ||
                    generationIsStopRequested(generationId)
                ) {
                    return false;
                }

const current = result.state?.generation || null;
if (
    !current ||
    current.generationId !== generationId ||
    !generationIsMine(current) ||
    terminalizingGenerationId === generationId ||
    generationIsStopRequested(generationId)
) {
    return false;
}

                // Compact response: merge, never replace.
                mergeCompactState(result.state);
                localGeneration = { ...localGeneration, ...clone(current) };
                generationServerReadyId = generationId;
                generationHeartbeatFailures = 0;
                updateGenerationUi();
                return true;
} catch (error) {
    lastError = error;

    // A terminalization/stop can begin while /generation/started is still
    // in flight. Do not let the late response resurrect local readiness.
    if (
        terminalizingGenerationId === generationId ||
        generationIsStopRequested(generationId)
    ) {
        return false;
    }

    if (error?.status === 409 && error?.payload?.state) {
                    const state = error.payload.state;
                    serverState = state;
                    baseSnapshot = state.snapshot;
                    const current = state.generation;

                    if (current?.generationId === generationId && generationIsMine(current)) {
                        localGeneration = { ...localGeneration, ...clone(current) };
                        if (current.stopRequested) {
                            rememberStopRequestedGeneration(generationId);
                            return false;
                        }
                        if (['started', 'streaming'].includes(current.phase)) {
                            generationServerReadyId = generationId;
                            return true;
                        }
                    }

                    if (current?.generationId && current.generationId !== generationId && generationActive(current)) {
                        return false;
                    }
                }

                await sleep(Math.min(250 * 2 ** attempt, 1500));
            }
        }

        log('generation start retries exhausted', lastError);
        return false;
    })();

    try {
        const started = await generationStartPromise;
        if (!started && localGenerationMatches(generationId, scopeAtGeneration) && !generationIsStopRequested(generationId)) {
            scheduleGenerationStartRetry(generationId, 1000);
        }
        return started;
    } finally {
        if (generationStartPromiseId === generationId) {
            generationStartPromise = null;
            generationStartPromiseId = null;
        }
    }
}

async function coordinatedGenerateInterceptor(chat, contextSize, abort, type) {
    refreshLiveContext();

    if (shouldBypassMcsGeneration(type)) return;

    if (!settings.enabled || !settings.coordinateGeneration || applyingRemoteDepth > 0) return;

    if (localGeneration) {
        const generationId = localGeneration.generationId;

        // The previous shared generation is still finalizing: a new
        // start/continuation here would race its terminal commit.
        if (terminalizingGenerationId === generationId) {
            abort(false);
            statusText('The shared generation is finishing; please try again after it releases.', true);
            return;
        }

        const manualRequest = consumeManualGenerationRequest();
        const internalContinuation =
            !manualRequest &&
            (groupWrapperDepth > 0 ||
            generationTerminalPhase === 'completed');

        if (manualRequest) {
            abort(false);
            statusText('The previous shared generation is still finishing; please generate again once it has fully released.', true);
            return;
        }

        if (generationIsStopRequested(generationId)) {
            abort(false);
            return;
        }

        if (internalContinuation) {
            clearGenerationTerminalTimer();
            clearTerminalRetryTimer();
            generationTerminalPhase = null;
            if (!generationServerReadyId) void ensureGenerationStarted();
            return;
        }

        abort(false);
        statusText('A shared generation is already active in this tab.', true);
        return;
    }

    if (!currentScope) {
        await switchScope('generation-no-scope');
        if (!currentScope || !serverState) {
            abort(false);
            statusText('Multi-Client Sync is not connected to this chat yet.', true);
            return;
        }
    }

    const scopeAtClaim = clone(currentScope);
    const epochAtClaim = scopeEpoch;

    if (!serverState) {
        abort(false);
        statusText('Multi-Client Sync is not connected to this chat.', true);
        return;
    }

    if (generationClaimInFlightId) {
        abort(false);
        return;
    }

    if (!nativeScopeStable(scopeAtClaim)) {
        const stable = await waitForNativeScope(scopeAtClaim, 2500, 75);
        if (!stable) {
            warn('[MCS] generation blocked because native chat scope did not stabilize');
            abort(false);
            return;
        }
    }

    let existing = serverState?.generation || null;

    if (existing) {
        if (generationIsStaleOwned(existing)) {
            try {
                const cleared = await api('/generation/terminal', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                    generationId: existing.generationId,
                    phase: 'stopped',
                    snapshot: clone(serverState?.snapshot || { messages: [], metadata: {} }),
                    opId: newId(),
                });
                serverState = cleared.state;
                baseSnapshot = cleared.state.snapshot;
                rememberTerminatedGeneration(existing.generationId);
                existing = serverState?.generation || null;
            } catch (error) {
                warn('failed to clear stale same-client generation before new generation', error);
                abort(false);
                return;
            }
        }

if (existing && generationActive(existing)) {
    if (generationIsMine(existing)) {
        // The server still proves this client owns the generation, even
        // though local generation bookkeeping was lost during reconnect,
        // reload, or a lifecycle transition.
        localGeneration = clone(existing);
        localGenerationScope = clone(scopeAtClaim);
        localGenerationEpoch = epochAtClaim;

        localGenerationBaseSnapshot =
            clone(
                serverState?.snapshot ||
                baseSnapshot || {
                    messages: [],
                    metadata: {},
                },
            );

        localGenerationBaseRevision =
            Number(serverState?.revision || 0);

        localGenerationSettings = {
            syncMessages: !!settings.syncMessages,
            syncMetadata: !!settings.syncMetadata,
        };

        localStreamMessageId = null;
        localStreamMessageIndex = null;
        generationClaimedThisPage = true;
        generationMismatchSince = 0;
        generationTerminalPhase = null;

        if (existing.stopRequested) {
            rememberStopRequestedGeneration(
                existing.generationId,
            );

            generationTerminalPhase = 'stopped';
            abort(false);
            return;
        }

        startGenerationHeartbeat(epochAtClaim);

        const recovered =
            await ensureGenerationStarted();

        if (!recovered) {
            abort(false);
            updateGenerationUi();
        }

        return;
    }

    abort(false);

    if (settings.notifications) {
        statusText(
            'Another client is already generating this shared chat.',
            true,
        );
    }

    updateGenerationUi();
    return;
}
    }

const generationId = newId();
generationClaimInFlightId = generationId;

// Same exact payload => same opId across transport retries.
// Changed payload after a conflict => new opId.
let claimOpId = newId();

let desired = null;
let claimBase =
    baseSnapshot ||
    serverState?.snapshot || {
        messages: [],
        metadata: {},
    };
let revision = Number(serverState?.revision || 0);
let claimResult = null;

try {
    const idsReady = await ensureIdsPersisted(scopeAtClaim);

    if (!idsReady || !currentScopeGuard(epochAtClaim)) {
        abort(false);
        return;
    }

    desired = syncSnapshot(durableSnapshot());

    for (let attempt = 0; attempt < 4; attempt += 1) {
        if (
            !currentScopeGuard(epochAtClaim) ||
            !nativeScopeStable(scopeAtClaim) ||
            terminalizingGenerationId === generationId
        ) {
            abort(false);
            return;
        }

        try {
            claimResult = await api('/generation/claim', 'POST', {
                scope: scopeAtClaim,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
                opId: claimOpId,
                generationId,
                generationType: String(type || 'normal'),
                baseRevision: revision,
                snapshot: desired,
            });

            break;
        } catch (error) {
            const payload = error?.payload;

            if (error?.status === 409 && payload?.state) {
                if (payload.error === 'generation_active') {
                    const other = payload.state.generation;

                    // If the original claim actually committed and only its
                    // response was lost, the server proves success here.
                    if (
                        other?.generationId === generationId &&
                        generationIsMine(other)
                    ) {
                        claimResult = payload;
                        break;
                    }

                    serverState = payload.state;
                    baseSnapshot = payload.state.snapshot;

                    abort(false);

                    if (settings.notifications) {
                        statusText(
                            'Another client is already generating this shared chat.',
                            true,
                        );
                    }

                    updateGenerationUi();
                    return;
                }

                const remoteSnapshot =
                    payload.state.snapshot || {
                        messages: [],
                        metadata: {},
                    };

                const merged = mergeSnapshots(
                    claimBase,
                    desired,
                    remoteSnapshot,
                );

                serverState = payload.state;
                baseSnapshot = remoteSnapshot;
                desired = merged;
                claimBase = remoteSnapshot;
                revision = Number(payload.state.revision || 0);

                // Payload changed. This is a new logical operation.
                claimOpId = newId();

                continue;
            }

            // Ambiguous transport failure: first prove whether the exact
            // generation claim committed before issuing another claim.
            const confirmedResult = await api('/state', 'POST', {
                scope: scopeAtClaim,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
            }).catch(() => null);

            const confirmedState = confirmedResult?.state || null;
            const confirmedGeneration =
                confirmedState?.generation || null;

            if (
                confirmedState &&
                confirmedGeneration?.generationId === generationId &&
                generationIsMine(confirmedGeneration)
            ) {
                claimResult = {
                    state: confirmedState,
                };
                break;
            }

            if (
                confirmedState &&
                confirmedGeneration &&
                confirmedGeneration.generationId !== generationId &&
                generationActive(confirmedGeneration) &&
                !generationIsMine(confirmedGeneration)
            ) {
                serverState = confirmedState;
                baseSnapshot = confirmedState.snapshot;

                abort(false);

                if (settings.notifications) {
                    statusText(
                        'Another client is already generating this shared chat.',
                        true,
                    );
                }

                updateGenerationUi();
                return;
            }

            // No proof of commit and no conflicting generation. Retry the
            // exact same payload using the same opId.
            if (attempt < 3) {
                await sleep(Math.min(250 * 2 ** attempt, 1000));
                continue;
            }

            throw error;
        }
    }

    if (!claimResult) {
        abort(false);
        return;
    }

        if (!currentScopeGuard(epochAtClaim) || !nativeScopeStable(scopeAtClaim)) {
            try {
                await api('/generation/terminal', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                    generationId,
                    phase: 'stopped',
                    snapshot: clone(claimResult.state?.snapshot || claimBase),
                    opId: newId(),
                });
            } catch { /* best effort */ }
            abort(false);
            return;
        }

        const claimed = claimResult.state?.generation;
        if (!claimed || claimed.generationId !== generationId || !generationIsMine(claimed)) {
            abort(false);
            return;
        }

        serverState = claimResult.state;
        baseSnapshot = claimResult.state.snapshot;
        localGeneration = clone(claimed);
        localGenerationScope = clone(scopeAtClaim);
        localGenerationEpoch = epochAtClaim;
        localGenerationBaseSnapshot = baseSnapshot;
        localGenerationBaseRevision = Number(claimResult.state.revision || 0);
        localGenerationSettings = {
            syncMessages: !!settings.syncMessages,
            syncMetadata: !!settings.syncMetadata,
        };
        localStreamMessageId = null;
        localStreamMessageIndex = null;
        generationClaimedThisPage = true;
        generationTerminalPhase = null;
        leaveAfterLocalGeneration = false;
        markLocalDirty(scopeAtClaim);
        rebuildLastSyncedMap(desired.messages);
        updateGenerationUi();
        startGenerationHeartbeat(epochAtClaim);

        const started = await ensureGenerationStarted();
        if (!started) {
            statusText('Reconnecting shared generation…');
            renderBanner('Reconnecting shared generation…');
            scheduleGenerationStartRetry(generationId, 500);
            updateGenerationUi();
        }
    } catch (error) {
        warn('generation claim failed', error);
        if (localGeneration?.generationId === generationId) {
            try { await releaseGenerationClaim('stopped'); } catch { /* ignore */ }
        } else {
            abort(false);
        }
        return;
    } finally {
        if (generationClaimInFlightId === generationId) generationClaimInFlightId = null;
    }
}

async function onGenerationStarted(type) {
    if (shouldBypassMcsGeneration(type)) return;
    if (!localGeneration || !currentScope) return;

    clearGenerationTerminalTimer();
    clearTerminalRetryTimer();

    if (generationTerminalPhase === 'completed') generationTerminalPhase = null;
    if (generationIsStopRequested(localGeneration.generationId)) return;

    try {
        const started = await ensureGenerationStarted();
        if (!started) scheduleGenerationStartRetry(localGeneration.generationId, 500);
    } catch (error) {
        warn('generation_started failed', error);
    }
}

function scheduleGenerationStream(delayOverride = null) {
    if (streamTimer || !pendingStream || !localGeneration || !currentScope) return;
    if (terminalizingGenerationId || generationIsStopRequested(localGeneration.generationId)) return;

    const delay = delayOverride != null
        ? Math.max(0, Number(delayOverride) || 0)
        : Math.max(0, STREAM_SEND_MS - (Date.now() - lastStreamSentAt));

    streamTimer = safeSetTimer(async () => {
        streamTimer = null;
        if (!pendingStream || !localGeneration || terminalizingGenerationId) return;
        if (generationIsStopRequested(localGeneration.generationId)) {
            pendingStream = null;
            return;
        }

        if (generationServerReadyId !== localGeneration.generationId) {
            const started = await ensureGenerationStarted();
            if (started) scheduleGenerationStream(0);
            else scheduleGenerationStartRetry(localGeneration.generationId, 500);
            return;
        }

        if (streamInFlight) {
            scheduleGenerationStream(STREAM_SEND_MS);
            return;
        }

        const payload = pendingStream;
        pendingStream = null;
        const generationId = localGeneration.generationId;
        const scopeAtStream = clone(localGenerationScope || currentScope);
        const epochAtStream = localGenerationEpoch || scopeEpoch;

        if (!scopeAtStream || !currentScopeGuard(epochAtStream) || generationIsStopRequested(generationId)) {
            return;
        }

        streamInFlight = true;
        streamInFlightSeq = Number(payload.seq || 0);

        // Abortable stream transport: terminalization cancels an in-flight
        // stream POST so the last token can never race the terminal snapshot.
        const controller = new AbortController();
        streamAbortController = controller;

        const request = (async () => {
            try {
                const result = await api('/generation/stream', 'POST', {
                    scope: scopeAtStream,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                    generationId,
                    seq: payload.seq,
                    message: payload.message,
                    messageIndex: payload.messageIndex,
                }, '', { signal: controller.signal });

                if (!localGenerationMatches(generationId, scopeAtStream) || generationIsStopRequested(generationId)) return;

                // Compact response: merge, never replace.
                mergeCompactState(result.state);
                const returned = result.state?.generation || null;
                if (returned?.generationId === generationId && generationIsMine(returned)) {
                    localGeneration = { ...localGeneration, ...clone(returned) };
                    generationServerReadyId = generationId;
                    if (returned.stopRequested) rememberStopRequestedGeneration(generationId);
                }
                lastStreamSentAt = Date.now();
            } catch (error) {
                const code = error?.payload?.error || '';

                if (generationIsStopRequested(generationId) || terminalizingGenerationId === generationId) return;

                // The server is the final authority: a terminalizing or
                // stop-requested generation accepts no more frames.
                if (code === 'generation_stop_requested' || code === 'generation_terminal') {
                    pendingStream = null;
                    return;
                }

                if (code === 'generation_not_started') {
                    if (localGenerationMatches(generationId, scopeAtStream)) {
                        if (!pendingStream || Number(pendingStream.seq || 0) <= Number(payload.seq || 0)) pendingStream = payload;
                        const started = await ensureGenerationStarted();
                        if (started) scheduleGenerationStream(0);
                        else scheduleGenerationStartRetry(generationId, 500);
                    }
                } else if (code === 'stream_sequence_conflict') {
                    const expected = Number(error?.payload?.expected || 0);
                    if (expected > 0 && localGenerationMatches(generationId, scopeAtStream)) {
                        const pending = pendingStream;
                        if (Number(payload.seq) < expected) {
                            localGeneration.seq = Math.max(Number(localGeneration.seq || 0), expected - 1);
                            if (pending) pendingStream = { ...pending, seq: Math.max(expected, Number(pending.seq || 0)) };
                        } else {
                            pendingStream = pending && Number(pending.seq) > expected ? pending : { ...payload, seq: expected };
                            localGeneration.seq = expected - 1;
                        }
                        scheduleGenerationStream(0);
                    }
                } else if (error?.status === 409 && code === 'generation_not_owned') {
                    const confirmed = await api('/state', 'POST', {
                        scope: scopeAtStream,
                        clientId,
                        deviceId,
                        connectionId: membershipConnectionId,
                    }).catch(() => null);
                    const state = confirmed?.state || null;
                    const g = state?.generation;

                    if (g?.generationId === generationId && generationIsMine(g)) {
                        serverState = state;
                        localGeneration = clone(g);
                        generationServerReadyId = ['started', 'streaming'].includes(g.phase) ? generationId : generationServerReadyId;
                        pendingStream = pendingStream || payload;
                        if (generationServerReadyId) scheduleGenerationStream(0);
                        else scheduleGenerationStartRetry(generationId, 500);
                    } else if (g && g.generationId !== generationId && generationActive(g) && !generationIsMine(g)) {
                        generationMismatchSince = generationMismatchSince || Date.now();
                    } else if (state && localGenerationMatches(generationId, scopeAtStream)) {
                        pendingStream = pendingStream || payload;
                        void reacquireGenerationOwnership('stream-ownership-loss').then(recovered => {
                            if (recovered) scheduleGenerationStream(0);
                        });
                    }
                } else if (error?.status === 403 && error?.payload?.error === 'not_member') {
                    if (localGenerationMatches(generationId, scopeAtStream)) pendingStream = pendingStream || payload;
                    await openScope(epochAtStream);
                    if (!generationIsStopRequested(generationId)) scheduleGenerationStream(STREAM_SEND_MS);
                } else {
                    if (error?.name === 'AbortError' && terminalizingGenerationId === generationId) return;
                    if (localGenerationMatches(generationId, scopeAtStream)) {
                        if (!pendingStream || Number(pendingStream.seq || 0) < Number(payload.seq || 0)) pendingStream = payload;
                        if (!streamRetryTimer && terminalizingGenerationId !== generationId) {
                            streamRetryTimer = safeSetTimer(() => {
                                streamRetryTimer = null;
                                if (!generationIsStopRequested(generationId)) scheduleGenerationStream();
                            }, 500);
                        }
                    }
                    log('generation stream failed; retrying without aborting local generation', error);
                }
            } finally {
                streamInFlight = false;
                if (streamInFlightSeq === Number(payload.seq || 0)) streamInFlightSeq = 0;
                if (streamAbortController === controller) streamAbortController = null;
            }
        })();

        streamInFlightPromise = request;
        try { await request; } finally {
            if (streamInFlightPromise === request) streamInFlightPromise = null;
            if (pendingStream && localGeneration && generationServerReadyId === localGeneration.generationId && !terminalizingGenerationId && !generationIsStopRequested(localGeneration.generationId)) {
                if (streamRetryTimer) {
                    clearTimeout(streamRetryTimer);
                    streamRetryTimer = null;
                }
                scheduleGenerationStream();
            }
        }
    }, delay);
}

// Hot path: runs on every stream token. Only the streaming MESSAGE is
// captured — never a full-chat snapshot. The full snapshot is built at
// terminalization, where it is actually needed.
function captureLocalStream() {
    if (terminalizingGenerationId || !localGeneration || !localGenerationScope) return;
    if (!Array.isArray(ctx?.chat) || !ctx.chat.length) return;
    const generationId = localGeneration.generationId;
    if (generationIsStopRequested(generationId)) return;
    if (!currentScope || makeScopeKey(currentScope) !== makeScopeKey(localGenerationScope)) return;
    if (!nativeScopeStable(localGenerationScope)) return;

    const messages = ctx.chat;
    let index = Number.isInteger(ctx.streamingProcessor?.messageId) ? Number(ctx.streamingProcessor.messageId) : -1;

    if (index < 0 || index >= messages.length || messages[index]?.is_user || messages[index]?.is_system) {
        if (localStreamMessageId) index = messages.findIndex(message => messageId(message) === localStreamMessageId);
    }

    if (index < 0 || index >= messages.length) {
        for (let i = messages.length - 1; i >= 0; i -= 1) {
            if (!messages[i]?.is_user && !messages[i]?.is_system) {
                index = i;
                break;
            }
        }
    }

if (index < 0) return;

const target = messages[index];
if (!target || typeof target !== 'object') return;

// IDs are normally guaranteed by ensureIdsPersisted() before generation.
// Do not scan the entire chat on every stream token. Only repair the
// streaming message when its ID is actually missing.
if (
    !target.extra ||
    typeof target.extra !== 'object' ||
    Array.isArray(target.extra)
) {
    target.extra = {};
}

if (
    !target.extra[MCS_META_KEY] ||
    typeof target.extra[MCS_META_KEY] !== 'object' ||
    Array.isArray(target.extra[MCS_META_KEY])
) {
    target.extra[MCS_META_KEY] = {};
}

const syncMeta = target.extra[MCS_META_KEY];

let id = messageId(target);

if (!id) {
    const usedIds = new Set();

    for (const message of messages) {
        const existingId = messageId(message);
        if (existingId) usedIds.add(existingId);
    }

    do {
        id = newId();
    } while (usedIds.has(id));

    syncMeta.messageId = id;
}

// Streaming content is a local mutation: stamp lastModified so a
// concurrent remote edit conflict resolves by timestamp.
syncMeta.lastModified = Date.now();

let message;

try {
    message = clone(target);
} catch (error) {
    // A malformed/native extension object must never crash the token hot path.
    warn(
        '[MCS] unable to clone streaming message; skipping this stream frame',
        error,
    );
    return;
}

id = messageId(message);
if (!id) return;

    localStreamMessageId = id;
    localStreamMessageIndex = index;

    const previousSeq = Number(localGeneration.seq || 0);
    const queuedSeq = Number(pendingStream?.seq || 0);
    const inFlightNextSeq = streamInFlightSeq > 0 ? streamInFlightSeq + 1 : 0;
    const seq = Math.max(previousSeq + 1, queuedSeq, inFlightNextSeq);

    pendingStream = { seq, message, messageIndex: index };

    if (generationServerReadyId === generationId) scheduleGenerationStream();
    else {
        void ensureGenerationStarted();
        scheduleGenerationStartRetry(generationId, 250);
    }
}

function clearGenerationStreamWork(generationId = null) {
    if (generationId && localGeneration?.generationId !== generationId) return;

    if (streamTimer) clearTimeout(streamTimer);
    if (streamRetryTimer) clearTimeout(streamRetryTimer);
    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);

    streamTimer = null;
    streamRetryTimer = null;
    streamCaptureTimer = null;
    pendingStream = null;
}

async function handleRemoteStopEvent(data) {
    if (!currentScope) return false;

    const eventScope = data?.scope || null;
    if (eventScope && makeScopeKey(eventScope) !== makeScopeKey(currentScope)) return true;

    const eventGeneration = data?.generation || null;
    const generationId = String(
        eventGeneration?.generationId ||
        data?.generationId ||
        serverState?.generation?.generationId ||
        '',
    );
    if (!generationId) return false;
    if (isGenerationTerminated(generationId)) return true;

    // Idempotent: if this exact generation is already stopping (SSE event +
    // BroadcastChannel can both arrive), do not run the stop path twice.
    if (generationIsStopRequested(generationId) && (generationTerminalPhase === 'stopped' || terminalizingGenerationId === generationId)) {
        return true;
    }

    if (serverState?.generation?.generationId === generationId) {
        serverState = {
            ...serverState,
            generation: {
                ...serverState.generation,
                ...(eventGeneration ? clone(eventGeneration) : {}),
                stopRequested: true,
            },
        };
    }

    rememberStopRequestedGeneration(generationId);
    remoteStopGenerationId = generationId;

    if (!localGeneration) {
        // Server-authoritative ownership confirmation only. BroadcastChannel
        // payloads are a wake-up hint, never proof of ownership.
        const stateResult = await api('/state', 'POST', {
            scope: clone(currentScope),
            clientId,
            deviceId,
            connectionId: membershipConnectionId,
        }).catch(() => null);
        const state = stateResult?.state || null;
        const current = state?.generation || null;
        if (!current || current.generationId !== generationId || !generationIsMine(current)) return true;

        if (!nativeGenerationLooksActive()) return true;

        serverState = state;
        localGeneration = { ...clone(current), stopRequested: true };
        localGenerationScope = clone(currentScope);
        localGenerationEpoch = scopeEpoch;
        generationClaimedThisPage = true;
    }

    if (!localGenerationMatches(generationId, currentScope)) return true;

generationTerminalPhase = 'stopped';
clearGenerationTerminalTimer();
clearTerminalRetryTimer();

// Stop any in-flight stream POST as well as queued stream work. Otherwise a
// final token can still arrive at the server after the stop request.
try { streamAbortController?.abort(); } catch { /* ignore */ }
streamAbortController = null;

clearGenerationStreamWork(generationId);
pendingStream = null;
renderBanner('Stopping generation…');
    setRemoteSendButtonMode(true);
    updateGenerationUi();

    try {
        const stopped = ctx?.stopGeneration?.();
        if (stopped === false && localGenerationMatches(generationId, currentScope)) {
            void sendGenerationTerminal('stopped').catch(error => warn('remote stop fallback terminal failed', error));
        }
    } catch (error) {
        warn('remote stopGeneration failed', error);
        if (localGenerationMatches(generationId, currentScope)) {
            void sendGenerationTerminal('stopped').catch(terminalError => warn('remote stop fallback terminal failed', terminalError));
        }
    }

    return true;
}

function scheduleDeferredStreamCapture() {
    if (streamCaptureTimer || !localGeneration || generationIsStopRequested(localGeneration.generationId)) return;
    streamCaptureTimer = safeSetTimer(() => {
        streamCaptureTimer = null;
        if (localGeneration && !generationIsStopRequested(localGeneration.generationId)) captureLocalStream();
    }, 0);
}

function onStreamToken() {
    if (!localGeneration) return;
    scheduleDeferredStreamCapture();
}

function onReasoningDone() {
    if (!localGeneration) return;
    scheduleDeferredStreamCapture();
}

function onToolEvent() {
    if (!localGeneration) return;
    scheduleDeferredStreamCapture();
}

function onGenerationEnded() {
    if (!localGeneration) return;

    const generationId = localGeneration.generationId;

    if (generationIsStopRequested(generationId) || generationTerminalPhase === 'stopped') {
        generationTerminalPhase = 'stopped';
        clearGenerationStreamWork(generationId);
        clearGenerationTerminalTimer();
        if (groupWrapperDepth > 0) return;
        generationTerminalTimer = safeSetTimer(() => {
            generationTerminalTimer = null;
            if (localGeneration?.generationId !== generationId) return;
            void sendGenerationTerminal('stopped').catch(error => warn('stopped terminal failed', error));
        }, 60);
        return;
    }

    if (groupWrapperDepth > 0) return;

generationTerminalPhase = 'completed';
clearGenerationTerminalTimer();

generationTerminalTimer = safeSetTimer(() => {
    generationTerminalTimer = null;

    if (
        !localGeneration ||
        localGeneration.generationId !== generationId
    ) {
        return;
    }

    if (terminalizingGenerationId === generationId) {
        return;
    }

    if (generationIsStopRequested(generationId)) {
        generationTerminalPhase = 'stopped';

        void sendGenerationTerminal('stopped')
            .catch(error => warn(
                'stopped terminal after late stop failed',
                error,
            ));

        return;
    }

    if (generationTerminalPhase !== 'completed') {
        return;
    }

    void sendGenerationTerminal('completed')
        .catch(error => warn(
            'completed terminal failed',
            error,
        ));
}, GENERATION_CONTINUATION_GRACE_MS);
}

function onGenerationStopped() {
    if (!localGeneration) return;

    const generationId = localGeneration.generationId;
    generationTerminalPhase = 'stopped';
    rememberStopRequestedGeneration(generationId);
    clearGenerationStreamWork(generationId);
    clearGenerationTerminalTimer();

    if (groupWrapperDepth > 0) return;

    generationTerminalTimer = safeSetTimer(() => {
        generationTerminalTimer = null;
        if (!localGeneration || localGeneration.generationId !== generationId) return;
        void sendGenerationTerminal('stopped').catch(error => warn('stopped terminal failed', error));
    }, 60);
}

function onGroupWrapperStarted() {
    groupWrapperDepth += 1;
    clearGenerationTerminalTimer();
    if (localGeneration && generationTerminalPhase === 'completed') generationTerminalPhase = null;
    updateGenerationUi();
}

function onGroupWrapperFinished() {
    groupWrapperDepth = Math.max(0, groupWrapperDepth - 1);
    if (!localGeneration || groupWrapperDepth > 0) {
        updateGenerationUi();
        return;
    }

    const generationId = localGeneration.generationId;
    clearGenerationTerminalTimer();

if (
    generationIsStopRequested(generationId) ||
    generationTerminalPhase === 'stopped'
) {
    generationTerminalPhase = 'stopped';

    generationTerminalTimer = safeSetTimer(() => {
        generationTerminalTimer = null;

        if (
            localGeneration?.generationId !== generationId ||
            terminalizingGenerationId === generationId
        ) {
            return;
        }

        void sendGenerationTerminal('stopped')
            .catch(error => warn(
                'group stopped terminal failed',
                error,
            ));
    }, 60);
} else {
    generationTerminalPhase = 'completed';

    generationTerminalTimer = safeSetTimer(() => {
        generationTerminalTimer = null;

        if (
            !localGeneration ||
            localGeneration.generationId !== generationId ||
            terminalizingGenerationId === generationId
        ) {
            return;
        }

        if (generationIsStopRequested(generationId)) {
            generationTerminalPhase = 'stopped';

            void sendGenerationTerminal('stopped')
                .catch(error => warn(
                    'group late-stop terminal failed',
                    error,
                ));

            return;
        }

        if (generationTerminalPhase !== 'completed') {
            return;
        }

        void sendGenerationTerminal('completed')
            .catch(error => warn(
                'group completed terminal failed',
                error,
            ));
    }, GENERATION_CONTINUATION_GRACE_MS);
}

    updateGenerationUi();
}

function capturePotentialDeletedStreamingMessage() {
    if (!localGeneration || !localStreamMessageId || !Array.isArray(ctx?.chat)) return;
    const stillExists = ctx.chat.some(message => messageId(message) === localStreamMessageId);
    if (!stillExists) log('[MCS] local streaming message disappeared before terminalization', localStreamMessageId);
}

function publishAfterLocalEvent(_event = undefined, { allowDuringGeneration = false } = {}) {
    if (applyingRemoteDepth > 0 || !currentScope || !settings.enabled || !syncEnabled()) {
        return Promise.resolve(false);
    }

    refreshLiveContext();
    capturePotentialDeletedStreamingMessage();

    const scopeAtEvent = clone(currentScope);
    const epochAtEvent = scopeEpoch;
    const mutationVersion = ++localMutationVersion;

    if (!nativeScopeStable(scopeAtEvent)) {
        if (localGeneration) {
            log('[MCS] local event arrived during transient generation context swap; deferring sync');
            return Promise.resolve(false);
        }
        return switchScope('local-event-context-mismatch');
    }

    stampLocalMutations();
    markLocalDirty(scopeAtEvent);

    // Never silently drop a real local edit merely because terminalization is
    // in progress: the server generation can finish independently while the
    // edit belongs in the durable queue and flushes afterwards.
    if (terminalizingGenerationId) {
        const snapshot = syncSnapshot(durableSnapshot());
        const queued = enqueueSnapshot(
            snapshot,
            Number(serverState?.revision || 0),
            serverState?.snapshot || { messages: [], metadata: {} },
            scopeAtEvent,
            'snapshot',
            null,
            newId(),
        ).then(() => {
            scheduleQueueFlushRetry();
            return true;
        }).catch(error => {
            warn('[MCS] failed to durably queue edit during terminalization', error);
            return false;
        });
        return queued;
    }

const publishKey =
    `${makeScopeKey(scopeAtEvent)}:${epochAtEvent}`;

const previousChain =
    publishChains.get(publishKey) ||
    Promise.resolve();

let run;

run = previousChain.then(async () => {
    if (
        scopeEpoch !== epochAtEvent ||
        scopeKeyValue !== makeScopeKey(scopeAtEvent)
    ) {
        return false;
    }

    if (!nativeScopeStable(scopeAtEvent)) {
        return false;
    }

    if (
        localGeneration &&
        makeScopeKey(localGenerationScope) ===
            makeScopeKey(scopeAtEvent) &&
        !allowDuringGeneration
    ) {
        return false;
    }

    if (
        localGeneration &&
        generationIsStopRequested(
            localGeneration.generationId,
        )
    ) {
        return false;
    }

    if (
        localGeneration &&
        localGeneration.phase === 'streaming' &&
        allowDuringGeneration
    ) {
        return false;
    }

    activeLocalPublishPromise = run;
    activeLocalPublishScopeKey = publishKey;

    try {
        const deltaResult = await publishLocalDelta({
            scope: scopeAtEvent,
            opId: newId(),
            mutationVersion,
        });

        if (deltaResult.ok) return true;

        if (
            deltaResult.abandoned ||
            deltaResult.ambiguous
        ) {
            return false;
        }

        if (
            scopeEpoch !== epochAtEvent ||
            scopeKeyValue !== makeScopeKey(scopeAtEvent) ||
            !nativeScopeStable(scopeAtEvent)
        ) {
            return false;
        }

        const currentSnapshot =
            syncSnapshot(durableSnapshot());

        return await publishLocalSnapshot(
            currentSnapshot,
            {
                allowDuringGeneration,
                scope: scopeAtEvent,
                opId: newId(),
                expectedMutationVersion:
                    mutationVersion,
            },
        );
    } catch (error) {
        warn(
            'publish after local event failed',
            error,
        );

        return false;
    } finally {
        if (activeLocalPublishPromise === run) {
            activeLocalPublishPromise = null;
            activeLocalPublishScopeKey = '';
        }
    }
});

const chain = run.then(
    () => undefined,
    error => warn(
        'local publish chain failed',
        error,
    ),
);

publishChains.set(publishKey, chain);

void chain.finally(() => {
    if (publishChains.get(publishKey) === chain) {
        publishChains.delete(publishKey);
    }
});

return run;
}

// Noisy render-adjacent events (edit-box rerenders, reasoning panels) are
// coalesced into a single next-tick publish instead of one publish each.
function scheduleDeferredLocalPublish(delay = 0) {
    if (localPublishTimer) return;
    localPublishTimer = safeSetTimer(() => {
        localPublishTimer = null;
        void publishAfterLocalEvent().catch(error => warn('deferred local publish failed', error));
    }, delay);
}

async function handleChatLifecycleEvent() {
    // Invalidate every in-flight operation immediately. The native chat loader
    // may still be replacing ctx.chat / chat_metadata after the lifecycle
    // event fires.
    ++nativeLoadEpoch;

    if (nativeRestoreInProgress) return;

    if (localGeneration) {
        pendingScopeSwitchReason = 'chat-lifecycle';
        return;
    }

    // Do not touch/save the native chat while ST is still settling the load.
    // A short fixed delay is insufficient because chat loading can involve
    // asynchronous file/network/UI work.
    refreshLiveContext();

    const expectedScope = scopeFromContext();

    if (!expectedScope) {
        await sleep(100);
        refreshLiveContext();
    }

    const stable = expectedScope
        ? await waitForNativeScope(
            expectedScope,
            5000,
            100,
        )
        : false;

    if (nativeRestoreInProgress) return;

    refreshLiveContext();

    const actualScope = scopeFromContext();

    if (
        !actualScope ||
        !stable ||
        makeScopeKey(actualScope) !==
            makeScopeKey(expectedScope || actualScope)
    ) {
        // The native loader is still transitioning. Let the subsequent
        // lifecycle event/retry drive the next reconciliation instead of
        // saving an incomplete chat.
        log(
            '[MCS] chat lifecycle ignored until native scope stabilizes',
            {
                expected: expectedScope,
                actual: actualScope,
                stable,
            },
        );

        return;
    }

    await switchScope('chat-lifecycle');
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
    refreshLiveContext();

    const types = ctx?.eventTypes || {};
    const es = ctx?.eventSource;

    // Multiple ST event constants can resolve to the same event string.
    // Keep one native listener per event string, but preserve all distinct
    // logical handlers registered for that event.
    const registrations = new Map();

    const listen = (eventType, fn) => {
        if (!eventType || !es?.on || typeof fn !== 'function') return;

        const existing = registrations.get(eventType);

        if (existing) {
            if (!existing.handlers.includes(fn)) {
                existing.handlers.push(fn);
            }
            return;
        }

        const handlers = [fn];

        const wrapper = (...args) => {
            for (const handler of handlers) {
                try {
                    const result = handler(...args);

                    if (result && typeof result.then === 'function') {
                        Promise.resolve(result).catch(error => {
                            warn(
                                `[MCS] async event handler failed: ${String(eventType)}`,
                                error,
                            );
                        });
                    }
                } catch (error) {
                    warn(
                        `[MCS] event handler failed: ${String(eventType)}`,
                        error,
                    );
                }
            }
        };

        registrations.set(eventType, { handlers, wrapper });

        es.on(eventType, wrapper);
        registeredEventHandlers.push([eventType, wrapper]);
    };

    listen(types.APP_INITIALIZED, () => switchScope('APP_INITIALIZED'));
    listen(types.APP_READY, () => switchScope('APP_READY'));

    listen(types.CHAT_CHANGED, handleChatLifecycleEvent);
    listen(types.CHAT_LOADED, handleChatLifecycleEvent);
    listen(types.CHAT_CREATED, handleChatLifecycleEvent);
    listen(types.CHAT_RENAMED, handleChatLifecycleEvent);

    listen(types.CHAT_DELETED, async data => {
        const old = typeof data === 'string'
            ? data.replace(/\.jsonl$/, '')
            : '';

        if (old && currentScope?.chatId === old && scopeKeyValue) {
            await idbClearScope(scopeKeyValue).catch(() => {});
        }

        await handleChatLifecycleEvent();
    });

    listen(types.GROUP_CHAT_CREATED, handleChatLifecycleEvent);
    listen(types.GROUP_CHAT_DELETED, handleChatLifecycleEvent);

    listen(types.MESSAGE_SENT, event => {
        return publishAfterLocalEvent(event, {
            allowDuringGeneration: true,
        });
    });

    listen(types.MESSAGE_RECEIVED, publishAfterLocalEvent);
    listen(types.MESSAGE_EDITED, publishAfterLocalEvent);
    listen(types.MESSAGE_UPDATED, scheduleDeferredLocalPublish);
    listen(types.MESSAGE_DELETED, publishAfterLocalEvent);
    listen(types.MESSAGE_SWIPED, publishAfterLocalEvent);
    listen(types.MESSAGE_SWIPE_DELETED, publishAfterLocalEvent);
    listen(types.MESSAGE_REASONING_EDITED, scheduleDeferredLocalPublish);
    listen(types.MESSAGE_REASONING_DELETED, scheduleDeferredLocalPublish);
    listen(types.MESSAGE_FILE_EMBEDDED, publishAfterLocalEvent);
    listen(types.FILE_ATTACHMENT_DELETED, publishAfterLocalEvent);
    listen(types.MEDIA_ATTACHMENT_DELETED, publishAfterLocalEvent);
    listen(types.IMAGE_SWIPED, publishAfterLocalEvent);
    listen(types.MORE_MESSAGES_LOADED, publishAfterLocalEvent);

    listen(types.GENERATION_STARTED, onGenerationStarted);
    listen(types.STREAM_TOKEN_RECEIVED, onStreamToken);
    listen(types.STREAM_REASONING_DONE, onReasoningDone);
    listen(types.TOOL_CALLS_PERFORMED, onToolEvent);
    listen(types.TOOL_CALLS_RENDERED, onToolEvent);
    listen(types.GENERATION_ENDED, onGenerationEnded);
    listen(types.GENERATION_STOPPED, onGenerationStopped);

    listen(types.GROUP_MEMBER_DRAFTED, onStreamToken);
    listen(types.GROUP_WRAPPER_STARTED, onGroupWrapperStarted);
    listen(types.GROUP_WRAPPER_FINISHED, onGroupWrapperFinished);
}

function remoteGenerationActionSelector() {
    return [
        '#mes_stop',
        '.mes_stop',
        '#send_but',
        '#option_regenerate',
        '#regenerate_last_message',
        '#mes_impersonate',
        '#option_impersonate',
        '#swipe_left',
        '#swipe_right',
        '.swipe_left',
        '.swipe_right',
        '.group_member [data-action="speak"]',
    ].join(', ');
}

function remoteMutationGuardSelector() {
    return [
        '#option_delete_mes',
        '#option_delete_chat',
        '#dialogue_del_mes_ok',
        '.mes_edit',
        '.mes_edit_done',
        '.mes_edit_delete',
        '.mes_edit_up',
        '.mes_edit_down',
        '.mes_edit_cancel',
        '.mes_reasoning_edit',
        '.mes_reasoning_edit_done',
        '.mes_reasoning_delete',
        '.mes_reasoning_edit_cancel',
        '.mes_del',
        '.mes_delete',
        '.delete_message',
        '.edit_message',
        '.mes_hide',
        '.mes_unhide',
        '.mes_embed',
        '.mes_create_bookmark',
        '.mes_create_branch',
        '[data-action="edit"]',
        '[data-action="delete"]',
    ].join(', ');
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
        if (!(event.target instanceof Element)) return;

        const target = event.target.closest(remoteGenerationActionSelector());

        if (
            localGeneration &&
            generationTerminalPhase === 'completed' &&
            target &&
            target.matches('#send_but, #option_regenerate, #regenerate_last_message, #mes_impersonate, #option_impersonate, #swipe_left, #swipe_right, .swipe_left, .swipe_right, .group_member [data-action="speak"]')
        ) {
            markManualGenerationRequest();
        }

        if (!isRemoteGenerationActive()) return;

        const mutationTarget = event.target.closest(remoteMutationGuardSelector());

        if (mutationTarget) {
            event.preventDefault();
            event.stopImmediatePropagation();
            statusText('The shared chat is generating in another client; message editing is temporarily locked.', true);
            return;
        }

        if (!target) return;

        const isStop = target.matches('#mes_stop, .mes_stop');
        const isSend = target.matches('#send_but');
        const isGenerationMutation = target.matches('#option_regenerate, #regenerate_last_message, #mes_impersonate, #option_impersonate, #swipe_left, #swipe_right, .swipe_left, .swipe_right, .group_member [data-action="speak"]');

        if (isStop || isSend || isGenerationMutation) {
            event.preventDefault();
            event.stopImmediatePropagation();
            event.stopPropagation();

            if (isStop || isSend) {
                if (!settings.remoteStop) {
                    statusText('Another client is generating this shared chat.', true);
                    return;
                }
                try {
                    await requestRemoteStop();
                } catch (error) {
                    warn('remote stop failed', error);
                }
            } else if (isGenerationMutation) {
                statusText('Another client is generating this shared chat.', true);
            }
        }
    };

    const keydownHandler = async event => {
        if (
            localGeneration &&
            generationTerminalPhase === 'completed' &&
            event.key === 'Enter' &&
            !event.shiftKey &&
            !event.isComposing &&
            !event.repeat &&
            event.target instanceof HTMLTextAreaElement &&
            (event.target.id === 'send_textarea' || event.target.closest?.('#send_form, #send_form_inner'))
        ) {
            markManualGenerationRequest();
        }

        if (!isRemoteGenerationActive()) return;

        if (event.key === 'Escape' && settings.remoteStop) {
            event.preventDefault();
            event.stopImmediatePropagation();
            event.stopPropagation();
            try { await requestRemoteStop(); } catch (error) { warn('remote Stop via Escape failed', error); }
            return;
        }

        if (event.key !== 'Enter' || event.shiftKey || event.isComposing || event.repeat) return;
        if (!(event.target instanceof HTMLTextAreaElement || event.target instanceof HTMLInputElement)) return;

        const isChatInput = event.target.id === 'send_textarea' || event.target.closest?.('#send_form, #send_form_inner');
        if (!isChatInput) return;

        event.preventDefault();
        event.stopImmediatePropagation();
        event.stopPropagation();

        if (!settings.remoteStop) {
            statusText('Another client is generating this shared chat.', true);
            return;
        }

        try { await requestRemoteStop(); } catch (error) { warn('remote stop via Enter failed', error); }
    };

    document.addEventListener('click', clickHandler, true);
    document.addEventListener('keydown', keydownHandler, true);
    registeredUiHandlers.push(['click', clickHandler, true], ['keydown', keydownHandler, true]);
}

async function waitForRemoteStopConfirmation(scope, generationId, epoch) {
    let lastSeenRevision =
        Number(serverState?.revision || 0);

    for (
        let attempt = 0;
        attempt < REMOTE_STOP_CONFIRM_ATTEMPTS;
        attempt += 1
    ) {
        if (!currentScopeGuard(epoch)) {
            return false;
        }

        try {
            const result = await api(
                '/state',
                'POST',
                {
                    scope,
                    clientId,
                    deviceId,
                    connectionId:
                        membershipConnectionId,
                },
                '',
                {
                    timeoutMs:
                        STOP_API_TIMEOUT_MS,
                },
            );

            if (!currentScopeGuard(epoch)) {
                return false;
            }

            const incomingState =
                result?.state || null;

            if (!incomingState) {
                await sleep(
                    REMOTE_STOP_CONFIRM_MS,
                );
                continue;
            }

            const incomingRevision =
                Number(
                    incomingState.revision || 0,
                );

            // Never let an older confirmation poll overwrite a newer SSE/API
            // state that this tab has already accepted.
            if (incomingRevision < lastSeenRevision) {
                await sleep(
                    REMOTE_STOP_CONFIRM_MS,
                );
                continue;
            }

            lastSeenRevision = Math.max(
                lastSeenRevision,
                incomingRevision,
            );

            const currentRevision =
                Number(
                    serverState?.revision || 0,
                );

            if (
                incomingRevision >=
                currentRevision
            ) {
                serverState = incomingState;
            }

            const generation =
                incomingState.generation || null;

            if (!generation) {
                rememberTerminatedGeneration(
                    generationId,
                );

                remoteStopGenerationId = null;
                updateGenerationUi();
                return true;
            }

            if (
                generation.generationId !==
                generationId
            ) {
                // A newly created generation necessarily advances the
                // authoritative revision. Equal revision is not enough proof.
                if (
                    incomingRevision >
                        currentRevision &&
                    generationActive(
                        generation,
                    )
                ) {
                    rememberTerminatedGeneration(
                        generationId,
                    );

                    remoteStopGenerationId =
                        generation.generationId;

                    updateGenerationUi();
                    return true;
                }

                await sleep(
                    REMOTE_STOP_CONFIRM_MS,
                );
                continue;
            }

            if (generation.stopRequested) {
                rememberStopRequestedGeneration(
                    generationId,
                );

                remoteStopGenerationId =
                    generationId;

                updateGenerationUi();
                return true;
            }

            const phase = String(
                generation.phase || '',
            ).toLowerCase();

            if (
                terminalGenerationPhases.has(
                    phase,
                )
            ) {
                rememberTerminatedGeneration(
                    generationId,
                );

                updateGenerationUi();
                return true;
            }
        } catch (error) {
            log(
                'remote stop confirmation poll failed',
                error,
            );
        }

        await sleep(
            REMOTE_STOP_CONFIRM_MS,
        );
    }

    return false;
}

async function requestRemoteStop() {
    if (!settings.remoteStop) {
        statusText('Remote Stop is disabled.', true);
        return false;
    }

if (localGeneration) {
    const generationId = localGeneration.generationId;

    rememberStopRequestedGeneration(generationId);
    generationTerminalPhase = 'stopped';
    clearGenerationTerminalTimer();
    clearTerminalRetryTimer();
    clearGenerationStreamWork(generationId);

    try { streamAbortController?.abort(); } catch { /* ignore */ }
    streamAbortController = null;

    renderBanner('Stopping generation…');
    updateGenerationUi();

    try {
        const stopped = ctx?.stopGeneration?.();

        // Native ST normally emits GENERATION_STOPPED. Keep a fallback so a
        // missing/late event cannot strand the server-side generation.
        if (stopped === false) {
            void sendGenerationTerminal('stopped').catch(error => {
                warn('local stopGeneration fallback terminal failed', error);
            });
        } else {
            safeSetTimer(() => {
                if (localGeneration?.generationId !== generationId) return;
                if (!generationIsStopRequested(generationId)) return;
                if (generationTerminalPhase !== 'stopped') return;
                if (terminalizingGenerationId === generationId) return;

                void sendGenerationTerminal('stopped').catch(error => {
                    warn('local stop fallback terminal failed', error);
                });
            }, 250);
        }
    } catch (error) {
        warn('local stopGeneration failed', error);

        if (localGeneration?.generationId === generationId) {
            void sendGenerationTerminal('stopped').catch(terminalError => {
                warn('local stopGeneration exception terminal failed', terminalError);
            });
        }
    }

    return true;
}

    let g = serverState?.generation;
    if (!g || !currentScope) {
        await resyncCurrentScope(scopeEpoch);
        g = serverState?.generation;
        if (!g || !currentScope) {
            statusText('No active shared generation found.');
            return false;
        }
    }

    if (!generationActive(g)) {
        await resyncCurrentScope(scopeEpoch);
        g = serverState?.generation;
        if (!g || !generationActive(g)) {
            updateGenerationUi();
            return false;
        }
    }

    if (generationIsMine(g) && !localGeneration) {
        await resyncCurrentScope(scopeEpoch);
        g = serverState?.generation;
        if (!g || (generationIsMine(g) && !localGeneration)) {
            updateGenerationUi();
            return false;
        }
    }

    const generationId = String(g.generationId || '');
    if (!generationId) return false;

    if (remoteStopInFlight && remoteStopGenerationId === generationId) {
        return await remoteStopInFlight;
    }

    const scopeAtRequest = clone(currentScope);
    const epochAtRequest = scopeEpoch;
    remoteStopGenerationId = generationId;
    remoteStopRequestedAt = Date.now();
    rememberStopRequestedGeneration(generationId);
    updateGenerationUi();
    setRemoteSendButtonMode(true);
    statusText('Stop requested…');

    const stopOpId = newId();

    broadcastWake('generation-stop-requested', {
        scope: scopeAtRequest,
        generationId,
        generation: clone(g),
        stopRequested: true,
        requestedAt: remoteStopRequestedAt,
    });

    const run = (async () => {
        try {
            let result;
            try {
                result = await api('/generation/stop', 'POST', {
                    scope: scopeAtRequest,
                    clientId,
                    deviceId,
                    connectionId: membershipConnectionId,
                    generationId,
                    opId: stopOpId,
                }, '', { timeoutMs: STOP_API_TIMEOUT_MS });
            } catch (error) {
                if (error?.status === 409 && error?.payload?.state) {
                    result = { state: error.payload.state };
                    const current = result.state?.generation;
                    if (current?.generationId === generationId && !current.stopRequested) throw error;
                } else {
                    throw error;
                }
            }

            if (currentScopeGuard(epochAtRequest) && result?.state) {
                // Compact response: merge, never replace.
                mergeCompactState(result.state);
            }

            updateGenerationUi();
            const confirmed = await waitForRemoteStopConfirmation(scopeAtRequest, generationId, epochAtRequest);

            if (!confirmed && currentScopeGuard(epochAtRequest)) {
                statusText('Stop request sent; waiting for the generating client…');
                updateGenerationUi();
            }

            return confirmed;
        } catch (error) {
            const confirmation = await api('/state', 'POST', {
                scope: scopeAtRequest,
                clientId,
                deviceId,
                connectionId: membershipConnectionId,
            }, '', { timeoutMs: STOP_API_TIMEOUT_MS }).catch(() => null);

            const confirmationState = confirmation?.state || null;
            const confirmationGeneration = confirmationState?.generation || null;

if (
    confirmationState &&
    currentScopeGuard(epochAtRequest)
) {
    const incomingRevision =
        Number(
            confirmationState.revision || 0,
        );

    const currentRevision =
        Number(
            serverState?.revision || 0,
        );

    if (incomingRevision >= currentRevision) {
        serverState = confirmationState;
    }
}

            if (
                confirmationState &&
                (
                    !confirmationGeneration ||
                    confirmationGeneration.generationId !== generationId ||
                    confirmationGeneration.stopRequested
                )
            ) {
                if (!confirmationGeneration || confirmationGeneration.generationId !== generationId) {
                    rememberTerminatedGeneration(generationId);
                    updateGenerationUi();
                    return true;
                }
                rememberStopRequestedGeneration(generationId);
                updateGenerationUi();
                return true;
            }

            forgetStopRequestedGeneration(generationId);
            remoteStopGenerationId = null;
            remoteStopRequestedAt = 0;

            if (currentScopeGuard(epochAtRequest)) {
                statusText(`Stop request failed: ${error?.message || 'request failed'}`, true);
                updateGenerationUi();
            }
            throw error;
        } finally {
            if (currentScopeGuard(epochAtRequest)) updateGenerationUi();
        }
    })();

    remoteStopInFlight = run;
    try {
        return await run;
    } finally {
        if (remoteStopInFlight === run) remoteStopInFlight = null;
    }
}

async function releaseGenerationClaim(phase = 'stopped') {
    if (!localGeneration || !localGenerationScope) return false;

    const generation = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration = localGenerationEpoch || scopeEpoch;
    const mutationVersionAtStart = localMutationVersion;

    terminalizingGenerationId = generation.generationId;
    stopGenerationHeartbeat();
    clearGenerationStreamWork(generation.generationId);

    try { streamAbortController?.abort(); } catch { /* ignore */ }
    streamAbortController = null;

    // Terminalization is the authoritative final capture point. Let an
    // already-started stream request observe the abort before committing the
    // terminal snapshot, otherwise stream and terminal can cross in flight.
    if (streamInFlightPromise) {
        try {
            await Promise.race([
                streamInFlightPromise,
                sleep(2500),
            ]);
        } catch { /* ignore */ }
    }

    if (streamCaptureTimer) {
        clearTimeout(streamCaptureTimer);
        streamCaptureTimer = null;
    }

    await sleep(60);

    if (!localGenerationMatches(generation.generationId, scopeAtGeneration)) {
        terminalizingGenerationId = null;
        return false;
    }

    refreshLiveContext();

    try {
        const snapshot = nativeScopeStable(scopeAtGeneration)
            ? syncSnapshot(durableSnapshot())
            : clone(
                serverState?.snapshot ||
                localGenerationBaseSnapshot ||
                { messages: [], metadata: {} },
            );

        const result = await terminateGenerationOnServer(
            generation,
            scopeAtGeneration,
            phase,
            snapshot,
        );

        if (result.state && currentScopeGuard(epochAtGeneration)) {
            serverState = result.state;
            baseSnapshot = result.state.snapshot;
        }

if (result.success) {
    rememberTerminatedGeneration(
        generation.generationId,
    );

    if (
        mutationVersionAtStart === localMutationVersion
    ) {
        clearLocalDirty(scopeAtGeneration);
    } else {
        // A local edit happened after terminalization began. The terminal
        // snapshot therefore cannot be considered authoritative for that edit.
        markLocalDirty(scopeAtGeneration);

        try {
            refreshLiveContext();

            const latestSnapshot =
                syncSnapshot(
                    durableSnapshot(),
                );

            await enqueueSnapshot(
                latestSnapshot,
                Number(
                    serverState?.revision || 0,
                ),
                serverState?.snapshot ||
                    localGenerationBaseSnapshot || {
                        messages: [],
                        metadata: {},
                    },
                scopeAtGeneration,
                'snapshot',
                null,
                newId(),
            );

            scheduleQueueFlushRetry();
        } catch (queueError) {
            warn(
                '[MCS] failed to queue mutation made during generation release',
                queueError,
            );
        }
    }

    clearLocalGenerationState();
    terminalizingGenerationId = null;

    updateGenerationUi();

    void flushQueue().catch(error => {
        warn(
            '[MCS] queue flush after generation release failed',
            error,
        );
    });

    return true;
}

        terminalizingGenerationId = null;
        generationTerminalPhase = phase;

        if (localGenerationMatches(generation.generationId, scopeAtGeneration)) {
            startGenerationHeartbeat(epochAtGeneration);
        }

        scheduleTerminalRetry(
            generation.generationId,
            phase,
            TERMINAL_RETRY_MS,
        );

        updateGenerationUi();
        return false;
    } catch (error) {
        terminalizingGenerationId = null;
        generationTerminalPhase = phase;

        if (localGenerationMatches(generation.generationId, scopeAtGeneration)) {
            startGenerationHeartbeat(epochAtGeneration);
        }

        scheduleTerminalRetry(
            generation.generationId,
            phase,
            TERMINAL_RETRY_MS,
        );

        warn('generation release/terminal failed', error);
        return false;
    } finally {
        if (
            !localGeneration &&
            terminalizingGenerationId === generation.generationId
        ) {
            terminalizingGenerationId = null;
        }
    }
}

async function sendGenerationTerminal(phase = 'completed') {
    if (!localGeneration || !localGenerationScope) return false;

    const g = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration = localGenerationEpoch || scopeEpoch;
    const mutationVersionAtStart = localMutationVersion;

if (terminalizingGenerationId === g.generationId) {
    return false;
}

if (generationIsStopRequested(g.generationId)) {
    phase = 'stopped';
}

// Set this BEFORE waiting for an in-flight start request. This prevents the
// start path from establishing readiness after terminalization has begun.
terminalizingGenerationId = g.generationId;

stopGenerationHeartbeat();
clearGenerationTerminalTimer();
clearTerminalRetryTimer();

if (
    generationStartPromiseId === g.generationId &&
    generationStartPromise
) {
    try {
        await Promise.race([
            generationStartPromise,
            sleep(2500),
        ]);
    } catch {
        /* terminalization remains authoritative */
    }
}
    clearGenerationStreamWork(g.generationId);

    // Abort the in-flight stream transport: the last token must never race
    // the terminal snapshot commit.
    try { streamAbortController?.abort(); } catch { /* ignore */ }
    streamAbortController = null;

    // Terminalization is the authoritative final capture point. A deferred
    // stream-capture timer is not sufficient — event-loop ordering must never
    // determine whether the final token reaches the durable snapshot.
    if (streamCaptureTimer) {
        clearTimeout(streamCaptureTimer);
        streamCaptureTimer = null;
    }

    const terminalOpId = newId();

    try {
        if (streamInFlightPromise) {
            try { await Promise.race([streamInFlightPromise, sleep(2500)]); } catch { /* ignore */ }
        }

        await sleep(60);

        if (!localGenerationMatches(g.generationId, scopeAtGeneration)) return false;

        refreshLiveContext();
        const snapshot = nativeScopeStable(scopeAtGeneration)
            ? syncSnapshot(durableSnapshot())
            : clone(serverState?.snapshot || localGenerationBaseSnapshot || { messages: [], metadata: {} });

        // A remote Stop arriving during the finalization window wins.
        if (generationIsStopRequested(g.generationId)) phase = 'stopped';

        const result = await terminateGenerationOnServer(g, scopeAtGeneration, phase, snapshot, terminalOpId);
        const stillSameLocal = localGenerationMatches(g.generationId, scopeAtGeneration);
        const stillCurrent =
            currentScopeGuard(epochAtGeneration) &&
            !!currentScope &&
            makeScopeKey(currentScope) === makeScopeKey(scopeAtGeneration);

        // Never mutate the current scope's state with an old generation's
        // result after a scope switch.
        if (result.state && stillCurrent) {
            serverState = result.state;
            baseSnapshot = result.state.snapshot;
        }

        if (result.success) {
            rememberTerminatedGeneration(g.generationId);
            if (stillSameLocal && mutationVersionAtStart === localMutationVersion) {
                clearLocalDirty(scopeAtGeneration);
            } else if (stillSameLocal) {
                markLocalDirty(scopeAtGeneration);
            }

            if (stillSameLocal) clearLocalGenerationState();
            else if (localGeneration?.generationId === g.generationId) clearLocalGenerationState();

            if (leaveAfterLocalGeneration && !localGeneration) {
                leaveAfterLocalGeneration = false;
                if (!nativeRestoreInProgress) {
                    await leaveCurrentScope();
                    currentScope = null;
                    scopeKeyValue = '';
                    statusText('Disconnected');
                }
            } else if (!nativeRestoreInProgress && currentScopeGuard(epochAtGeneration)) {
                const reason = pendingScopeSwitchReason;
                pendingScopeSwitchReason = '';
                void switchScope(reason || 'post-generation-terminal');
            }

            updateGenerationUi();
            await flushQueue();
            return true;
        }

        terminalizingGenerationId = null;
        generationTerminalPhase = phase;
        if (localGenerationMatches(g.generationId, scopeAtGeneration)) {
            startGenerationHeartbeat(epochAtGeneration);
        }
        scheduleTerminalRetry(g.generationId, phase, TERMINAL_RETRY_MS);
        updateGenerationUi();
        return false;
    } catch (error) {
        terminalizingGenerationId = null;
        generationTerminalPhase = phase;
        if (localGenerationMatches(g.generationId, scopeAtGeneration)) {
            startGenerationHeartbeat(epochAtGeneration);
        }
        scheduleTerminalRetry(g.generationId, phase, TERMINAL_RETRY_MS);
        warn('generation terminal failed', error);
        return false;
    }
}

async function onActivate() {
    activationInProgress = true;

    try {
        ctx = SillyTavern.getContext();
        unwireEvents();
        unwireUiGuards();
        uninstallRemoteUiObserver();

try {
    bc?.close?.();
} catch {
    /* ignore */
}

bc = null;

try {
    if (typeof BroadcastChannel === 'function') {
        bc = new BroadcastChannel(BC_NAME);
    }
} catch (error) {
    // Sync must continue via SSE/API when BroadcastChannel is blocked by the
    // browser, private mode, permissions policy, or site-storage restrictions.
    bc = null;

    log(
        '[MCS] BroadcastChannel unavailable; continuing without tab wakeups',
        error,
    );
}

bc?.addEventListener('message', message => {
            const data = message.data;
            if (data?.scopeKey !== scopeKeyValue) return;

            if (data?.kind === 'generation-stop-requested' && currentScope) {
                handleRemoteStopEvent({
                    scope: data.scope || currentScope,
                    generationId: data.generationId,
                    generation: data.generation || null,
                }).catch(error => warn('BroadcastChannel remote stop handling failed', error));
            }
        });

if (!storageHandler) {
    storageHandler = event => {
        if (event.key !== STORAGE_KEY || !event.newValue) return;

        try {
            const incoming = JSON.parse(event.newValue);
            if (!incoming || typeof incoming !== 'object') return;

            const previousSettings = { ...settings };
            const previousEnabled = !!settings.enabled;
            const previousAutoConnect = !!settings.autoConnect;

            settings = normalizeSettings(incoming);
            updateSettingsControls();

            if (previousEnabled !== !!settings.enabled) {
                if (settings.enabled) {
                    onEnable().catch(error => {
                        warn('storage-driven enable failed', error);
                    });
                } else {
                    onDisable().catch(error => {
                        warn('storage-driven disable failed', error);
                    });
                }
                return;
            }

            // Settings are shared through localStorage, so autoConnect must
            // also be enforced in tabs that did not originate the change.
            if (
                settings.enabled &&
                previousAutoConnect !== !!settings.autoConnect
            ) {
                if (!settings.autoConnect) {
                    if (localGeneration) {
                        leaveAfterLocalGeneration = true;
                        statusText(
                            'Auto-connect disabled; the current generation will finish normally.',
                        );
                    } else {
                        ++scopeEpoch;

                        void leaveCurrentScope()
                            .then(() => {
                                currentScope = null;
                                scopeKeyValue = '';
                                statusText('Disconnected');
                                updateGenerationUi();
                            })
                            .catch(error => {
                                warn(
                                    'storage-driven autoConnect disconnect failed',
                                    error,
                                );
                            });
                    }
                } else {
                    switchScope('storage:autoConnect')
                        .catch(error => {
                            warn(
                                'storage-driven autoConnect reconnect failed',
                                error,
                            );
                        });
                }

                return;
            }

            // Keep all other shared settings immediately reflected locally.
            if (
                previousSettings.coordinateGeneration !== settings.coordinateGeneration ||
                previousSettings.remoteStop !== settings.remoteStop ||
                previousSettings.syncMessages !== settings.syncMessages ||
                previousSettings.syncMetadata !== settings.syncMetadata ||
                previousSettings.notifications !== settings.notifications ||
                previousSettings.debug !== settings.debug
            ) {
                updateGenerationUi();
            } else {
                updateGenerationUi();
            }
        } catch {
            /* ignore invalid storage */
        }
    };

    window.addEventListener('storage', storageHandler);
}

        await negotiateClientId();
        await mountSettings();

        await sleep(100);
        refreshLiveContext();
    } finally {
        activationInProgress = false;
    }

    wireEvents();
    wireUiGuards();
    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

    // No artificial startup delay: if ST hasn't loaded a chat yet,
    // scopeFromContext returns null and the 500ms retry loop handles it.
    void switchScope('post-activate').catch(error => warn('post-activate scope check failed', error));

    updateGenerationUi();
}

function updateSettingsControls() {
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
        if (el && document.activeElement !== el) el.checked = !!settings[key];
    }
}

function onEnableInternal() {
    return (async () => {
        settings.enabled = true;
        saveSettings();
        refreshLiveContext();
        ++scopeEpoch;
        wireEvents();
        wireUiGuards();
        globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

        currentScope = scopeFromContext();
        scopeKeyValue = makeScopeKey(currentScope);

        if (currentScope && settings.autoConnect) await openScope(scopeEpoch);
        else if (!currentScope) statusText('Waiting for active chat…');
        updateGenerationUi();
    })();
}

function onDisableInternal() {
    return (async () => {
        settings.enabled = false;
        saveSettings();
        ++scopeEpoch;
        unwireUiGuards();
        unwireEvents();
        uninstallRemoteUiObserver();
        delete globalThis.multiClientSyncGenerateInterceptor;

        await leaveCurrentScope();
        currentScope = null;
        scopeKeyValue = '';
        generationClaimInFlightId = null;
        generationRecoveryInFlight = null;
        localGenerationBaseRevision = 0;
        streamInFlightSeq = 0;
        membershipConnectionId = null;
        clearLocalDirty();
        setRemoteSendButtonMode(false);
        clearGenerationMarkers();
        manualGenerationRequestAt = 0;

        try { bc?.close?.(); } catch { /* ignore */ }
        bc = null;
    })();
}

function onEnable() {
    const run = lifecycleChain.then(() => onEnableInternal());
    lifecycleChain = run.then(() => undefined, error => warn('enable lifecycle failed', error));
    return run;
}

function onDisable() {
    const run = lifecycleChain.then(() => onDisableInternal());
    lifecycleChain = run.then(() => undefined, error => warn('disable lifecycle failed', error));
    return run;
}

async function onReconnect() {
    return switchScope('manual-reconnect');
}

async function mountSettings() {
    if (settingsPanelMounted) {
        updateSettingsControls();
        return;
    }

    const host = document.querySelector('#extensions_settings') || document.querySelector('#extensions_settings2');
    if (!host) {
        safeSetTimer(() => mountSettings().catch(error => warn('settings mount retry failed', error)), 1000);
        return;
    }

    settingsPanelMounted = true;
    const panel = document.createElement('div');
    panel.id = 'mcs_settings_panel';
    panel.className = 'mcs-settings';

    panel.innerHTML = `
        <h3>Multi-Client Sync</h3>

        <div class="mcs-status-row">
            <span id="mcs_status_dot" class="mcs-status mcs-disabled" title="Multi-Client Sync status"></span>
            <span id="mcs_status" class="mcs-state-text">Starting…</span>
        </div>

        <div class="mcs-info">
            Tabs/devices viewing the same chat share messages,
            edits, generation state, and live streaming.
            Different chats remain independent.
        </div>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_enabled">
            <span>Enable synchronization</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_auto_connect">
            <span>Auto-connect to active chats</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_sync_messages">
            <span>Sync messages</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_sync_metadata">
            <span>Sync chat metadata</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_coordinate_generation">
            <span>Coordinate generation between clients</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_remote_stop">
            <span>Allow remote Stop</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_notifications">
            <span>Show synchronization notifications</span>
        </label>

        <label class="checkbox_label">
            <input type="checkbox" id="mcs_debug">
            <span>Debug logging</span>
        </label>

        <div class="mcs-actions">
            <button id="mcs_reconnect" class="menu_button" type="button">Reconnect</button>
            <button id="mcs_resync" class="menu_button" type="button">Resync Current Chat</button>
        </div>
    `;

    host.appendChild(panel);

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
                updateGenerationUi();
                return;
            }

            if (key === 'autoConnect' && !settings.autoConnect) {
                if (localGeneration) {
                    leaveAfterLocalGeneration = true;
                    statusText('Auto-connect disabled; the current generation will finish normally.');
                } else {
                    ++scopeEpoch;
                    await leaveCurrentScope();
                    currentScope = null;
                    scopeKeyValue = '';
                    statusText('Disconnected');
                }
            } else if (settings.enabled && settings.autoConnect) {
                await switchScope(`setting:${key}`);
            }

            updateGenerationUi();
        });
    }

    document.getElementById('mcs_reconnect')?.addEventListener('click', () => {
        onReconnect().catch(error => warn('manual reconnect failed', error));
    });

    document.getElementById('mcs_resync')?.addEventListener('click', async () => {
        try {
            await resyncCurrentScope();
        } catch (error) {
            warn('manual resync failed', error);
        }
    });

    updateSettingsControls();
    updateGenerationUi();
}

export { onActivate, onEnable, onDisable };
globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;