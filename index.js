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
const REMOTE_RENDER_MS = 45;
const STORAGE_KEY = 'multi-client-sync-settings-v1';
const CLIENT_KEY = 'multi-client-sync-client-id-v1';
const DEVICE_KEY = 'multi-client-sync-device-id-v1';
const BC_NAME = 'multi-client-sync';
const API_TIMEOUT_MS = 12_000;
const TERMINAL_API_TIMEOUT_MS = 15_000;
const STOP_API_TIMEOUT_MS = 8_000;
const TERMINAL_RETRY_MS = 1_000;
const REMOTE_STOP_CONFIRM_MS = 350;
const REMOTE_STOP_CONFIRM_ATTEMPTS = 12;
const GENERATION_CONTINUATION_GRACE_MS = 350;
const OWNERSHIP_CONFLICT_GRACE_MS = 3_500;
const OWNERSHIP_RECOVERY_GRACE_MS = 1_200;
const STOP_REQUESTED_RETENTION_MS = 60 * 60 * 1000;

const CHUNK_MAX_BYTES = 512 * 1024;
const MAX_CHUNK_ASSEMBLY_BYTES = 12 * 1024 * 1024;
const MAX_CHUNK_ASSEMBLIES = 8;
const CHUNK_ASSEMBLY_TIMEOUT_MS = 30_000;
const MAX_CHUNK_BUFFER_BYTES = 16 * 1024 * 1024;

// Tombstones travel inside chatMetadata under this reserved key so deletes
// survive snapshot merges deterministically. Retention bounds the ledger.
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

let settings = loadSettings();

// clientId identifies this browser tab/session. It must NOT live in localStorage.
let clientId = loadSessionId(CLIENT_KEY);
let deviceId = loadStableId(DEVICE_KEY);
let tabId = crypto.randomUUID();

let ctx = null;
let eventSource = null;
let currentScope = null;
let scopeKeyValue = '';
let scopeEpoch = 0;
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
let publishChain = Promise.resolve();
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
let localGenerationScope = null;
let localGenerationEpoch = 0;
let localGenerationBaseSnapshot = null;
let localGenerationLastSnapshot = null;
let localStreamMessageId = null;
let localStreamMessageIndex = null;
let pendingRemoteStream = null;
let remoteGenerationId = null;
let lastRemoteStreamSeq = -1;
// lastSseEventId is the LOGICAL event cursor: the highest logical event id
// this client has fully accepted (normal event or complete chunked transfer).
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

// Last-synced message state (id -> comparable hash). Diffing current chat
// against this detects local deletions and edits so tombstones and
// lastModified timestamps get stamped before publishing.
let lastSyncedMessageMap = new Map();

// SSE chunking state. Assemblies are keyed by scope + transferId so both
// durable logical events and transient generation_state transfers are safe.
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
    return value === undefined ? undefined : JSON.parse(JSON.stringify(value));
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

function stableStringify(value) {
    const normalize = input => {
        if (Array.isArray(input)) return input.map(normalize);
        if (input && typeof input === 'object') {
            const out = {};
            for (const key of Object.keys(input).sort()) {
                if (forbiddenKeys.has(key)) continue;
                const val = input[key];
                if (val !== undefined) out[key] = normalize(val);
            }
            return out;
        }
        return input;
    };
    return JSON.stringify(normalize(value));
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

function loadSettings() {
    try {
        const stored = JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}');
        return { ...DEFAULT_SETTINGS, ...(stored && typeof stored === 'object' ? stored : {}) };
    } catch {
        return { ...DEFAULT_SETTINGS };
    }
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
            // A duplicate durable id is a local integrity failure: identity is
            // unstable and merges may mis-associate messages. Regenerate to
            // keep sync functional, but surface it loudly.
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
    return message?.extra?.multi_client_sync?.messageId || null;
}

function messageSyncMeta(message) {
    return message?.extra?.multi_client_sync || {};
}

function messageLastModified(message) {
    return Number(messageSyncMeta(message).lastModified || message?.send_date || message?.gen_started || 0);
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

        // The avatar filename is SillyTavern's persistent unique character key
        // (the card's on-disk identity). The array index is NOT stable. Name
        // is the last-resort fallback.
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
            req.onsuccess = () => finish(null, req.result.sort((a, b) => {
                // Deterministic ordering: createdAt, then local sequence, then id.
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
//
// The tombstone ledger lives in chatMetadata under MCS_META_KEY and travels
// with every snapshot. Before publishing a local change, the current chat is
// diffed against the last-synced state: vanished ids become tombstones,
// changed messages get a fresh lastModified. mergeSnapshots then resolves
// delete-vs-edit races by timestamp instead of resurrecting silently.
// ---------------------------------------------------------------------------

function comparableMessage(message) {
    const copy = clone(message);
    if (copy?.extra?.multi_client_sync) {
        delete copy.extra.multi_client_sync;
        if (Object.keys(copy.extra).length === 0) delete copy.extra;
    }
    return copy;
}

function comparableHash(message) {
    return stableStringify(comparableMessage(message));
}

function readLedger(metadata) {
    const meta = metadata?.[MCS_META_KEY];
    const tomb = meta?.tombstones;
    if (!tomb || typeof tomb !== 'object' || Array.isArray(tomb)) return {};
    const out = {};
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

// Stamp tombstones + lastModified for local mutations since the last sync.
// Must run BEFORE the snapshot is built. No-op while applying remote data.
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

    // Deletions: ids present at last sync, absent now.
    for (const id of lastSyncedMessageMap.keys()) {
        if (!currentHashes.has(id) && !tomb[id]) {
            tomb[id] = nowTs;
            changed = true;
        }
    }

    // Edits: same id, different comparable content. lastModified is excluded
    // from the comparable hash, so stamping it cannot retrigger the diff.
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

    // Prune: expired entries and ids that are present again (resurrected).
    const cutoff = nowTs - TOMBSTONE_RETENTION_MS;
    for (const id of Object.keys(tomb)) {
        if (tomb[id] < cutoff || currentHashes.has(id)) {
            delete tomb[id];
            changed = true;
        }
    }

    if (changed) bucket.tombstones = tomb;
}

// ---------------------------------------------------------------------------
// Chunk reassembly
//
// Chunks are transport fragments ONLY. No chunk ever mutates state. A logical
// event is dispatched exactly once, after every chunk validates, the whole
// byte count matches, and the whole-event SHA-256 verifies.
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
    if (data.chunkIndex >= data.chunkCount) return 'chunk_index_overflow';
    if (!Number.isInteger(data.totalBytes) || data.totalBytes <= 0 || data.totalBytes > MAX_CHUNK_ASSEMBLY_BYTES) return 'bad_total_bytes';
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

// Returns the reconstructed logical event, null (incomplete/duplicate), or
// the string 'resync' (unrecoverable corruption — caller must resync).
// Every resync path cleans up the assembly and refunds its byte budget.
async function handleEventChunk(data) {
    const error = validateChunkEnvelope(data);
    if (error) {
        warn('chunk validation failed', error);
        return null;
    }

    const key = chunkAssemblyKey(scopeKeyValue, data.transferId);
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

    if (assembly.chunks.has(data.chunkIndex)) return null; // duplicate chunk, ignore

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

    assembly.chunks.set(data.chunkIndex, chunkBytes);
    assembly.receivedBytes += chunkBytes.byteLength;

    if (assembly.chunks.size < assembly.chunkCount) return null; // incomplete

    // Complete: reconstruct, verify, dispatch exactly once.
    const ordered = [];
    let totalLen = 0;
    for (let i = 0; i < assembly.chunkCount; i += 1) {
        const buf = assembly.chunks.get(i);
        if (!buf) { warn('missing chunk after completion', i); return failResync(); }
        ordered.push(buf);
        totalLen += buf.byteLength;
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
}

// ---------------------------------------------------------------------------
// SSE processing
//
// receive → parse → validate → process logical event → advance cursor.
// The cursor NEVER advances before the logical event is fully accepted.
// Chunked events share one id; the later-chunk dedupe check is bypassed.
// ---------------------------------------------------------------------------

function connectSse(epoch) {
    disconnectSse();
    if (!currentScope || !currentScopeGuard(epoch)) return;

    const localSseEpoch = sseEpoch;
    const query = `?scope=${encodeURIComponent(encodeScope(currentScope))}&clientId=${encodeURIComponent(clientId)}&deviceId=${encodeURIComponent(deviceId)}&lastEventId=${encodeURIComponent(String(lastSseEventId || 0))}`;
    const source = new EventSource(`${PLUGIN_BASE}/events${query}`, { withCredentials: true });
    eventSource = source;

    const listeners = {
        hello: 'hello',
        generation_state: 'generation_state',
        replay_complete: 'replay_complete',
        resync_required: 'resync_required',
        snapshot: 'snapshot',
        generation_claimed: 'generation_claimed',
        generation_started: 'generation_started',
        generation_stream: 'generation_stream',
        generation_stop_requested: 'generation_stop_requested',
        generation_terminal: 'generation_terminal',
        generation_recovered: 'generation_recovered',
        event_chunk: 'event_chunk',
    };

    for (const type of Object.keys(listeners)) {
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

    // Chunks share one logical id — the stale-id drop must NOT run here.
    if (type === 'event_chunk') {
        enqueueSseLogicalEvent({ kind: 'chunk', eventId, data });
        return;
    }

    // Transient current-state transfer: never touches the cursor.
    if (type === 'generation_state') {
        enqueueSseLogicalEvent({ kind: 'generation_state', data });
        return;
    }

    if (type === 'hello') {
        handleServerHello(data);
        return;
    }

    if (eventId > 0 && eventId <= lastSseEventId) return; // already accepted

    enqueueSseLogicalEvent({ kind: 'logical', logicalType: type, eventId, data });
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
    if (item.kind === 'chunk') {
        const logicalEvent = await handleEventChunk(item.data);
        if (logicalEvent === 'resync') return 'resync';
        if (!logicalEvent) return null;

        if (logicalEvent.type === 'generation_state') {
            // Reconstructed transient transfer: same handling as the direct
            // frame path, and never advances the cursor.
            handleGenerationState(logicalEvent);
            return null;
        }

        return processSseLogicalEvent({
            kind: 'logical',
            logicalType: logicalEvent.type,
            eventId: item.eventId,
            data: logicalEvent,
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

// Every branch returns an explicit boolean. false = event not safely
// consumed → caller resyncs instead of silently skipping.
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

// Current remote generation state (metadata + live message) arriving via SSE.
// This is the only path that materializes the live remote message; routine
// /state and /join responses carry metadata only.
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

async function api(path, method = 'GET', body = undefined, query = '', options = {}) {
    const bodyBytes = body === undefined ? 0 : utf8ByteLength(body);
    const isLarge = bodyBytes > 512 * 1024;
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
                body: body === undefined ? undefined : JSON.stringify(body),
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
            // A timeout means OUTCOME UNKNOWN, not rejection. Callers must
            // treat this as ambiguous and retry with the SAME opId.
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
    remoteUiObserver.observe(parent, {
        childList: true,
        subtree: false,
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

    // Remote generation uses SillyTavern's actual native Stop control.
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
            delete el.dataset.mcsLocked;
            delete el.dataset.mcsPrevDisabled;
            delete el.dataset.mcsPrevTitle;
            el.classList.remove('disabled');
            if ('disabled' in el) el.disabled = false;
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
    localGenerationLastSnapshot = null;
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

function mergeMetadata(base, local, remote) {
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
        else if (l && r && typeof l === 'object' && typeof r === 'object') out[key] = mergeMetadata(b, l, r);
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

// Merge policy (deterministic), with tombstones resolved by timestamp:
//  - tombstone vs surviving edit: the later timestamp wins
//  - tombstone vs tombstone: deleted
//  - edit vs edit (both changed from base): later lastModified wins
//  - one-sided change: the changed side wins
//  - both unchanged from base / both equal: remote wins
// Tombstone ledgers are read from snapshot metadata (MCS_META_KEY), keyed by
// raw durable messageId — the same key the per-id loop extracts from
// `id:<messageId>` identities, so lookups always match.
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

    // Merged ledger: union of all three sides, newest deletion timestamp wins.
    const mergedTomb = {};
    for (const source of [baseTomb, localTomb, remoteTomb]) {
        for (const [id, ts] of Object.entries(source)) {
            if (!mergedTomb[id] || ts > mergedTomb[id]) mergedTomb[id] = ts;
        }
    }

    const ids = new Set([...bm.keys(), ...lm.keys(), ...rm.keys()]);
    const chosen = [];
    const chosenDurableIds = new Set();

    for (const id of ids) {
        const bv = bm.get(id);
        const lv = lm.get(id);
        const rv = rm.get(id);

        // Tombstone lookups use the raw durable messageId extracted from the
        // identity string, matching the ledger keys exactly.
        const mid = id.startsWith('id:') ? id.slice(3) : null;
        const lt = mid ? (localTomb[mid] || null) : null;
        const rt = mid ? (remoteTomb[mid] || null) : null;

        let value = null;

        if (lt && rt) {
            value = null; // both sides deleted
        } else if (lt && rv) {
            value = messageLastModified(rv) > lt ? rv : null; // remote edit newer than local delete?
        } else if (rt && lv) {
            value = messageLastModified(lv) > rt ? lv : null; // local edit newer than remote delete?
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

    // Ledger post-processing: drop entries for messages that survived the
    // merge, and expire old entries.
    const cutoff = Date.now() - TOMBSTONE_RETENTION_MS;
    for (const id of Object.keys(mergedTomb)) {
        if (chosenDurableIds.has(id) || mergedTomb[id] < cutoff) delete mergedTomb[id];
    }

    // Metadata: merge normally with the MCS key stripped, then re-inject the
    // resolved ledger so tombstone state is never clobbered by generic
    // metadata merge rules.
    const stripMeta = meta => {
        const copy = clone(meta || {});
        delete copy[MCS_META_KEY];
        return copy;
    };
    let metadata = mergeMetadata(stripMeta(b.metadata), stripMeta(l.metadata), stripMeta(r.metadata));
    if (Object.keys(mergedTomb).length) {
        metadata = {
            ...metadata,
            [MCS_META_KEY]: { ...(metadata[MCS_META_KEY] || {}), tombstones: mergedTomb },
        };
    }

    return {
        messages: orderMergedMessages(b.messages, l.messages, r.messages, chosen),
        metadata,
    };
}

// false must always mean "not durably saved". No caller may clear localDirty
// after a false return.
async function safeNativeSave(expectedScope = currentScope) {
    const run = nativeSaveChain.then(async () => {
        refreshLiveContext();
        if (nativeRestoreInProgress || !ctx || !expectedScope) return false;
        if (localGeneration && makeScopeKey(localGenerationScope) === makeScopeKey(expectedScope)) return false;
        if (!nativeScopeStable(expectedScope)) return false;

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

        // Group chats are already persisted authoritatively by MCS.
        if (expectedScope.kind === 'group') return false;

        await sleep(50);
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

// Snapshot application is rollback-safe: ctx.chat/chatMetadata are snapshotted
// before mutation, and any render or save failure restores the previous state.
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
    if (!ctx?.chat || !expectedScope || !nativeScopeStable(expectedScope)) return false;
    const changed = ensureMessageIds(ctx.chat);
    if (changed) {
        const saved = await safeNativeSave(expectedScope);
        if (!saved) markLocalDirty(expectedScope);
    }
    return true;
}

// The row id IS the opId. When queueing an operation whose HTTP outcome is
// uncertain, pass the SAME opId so the retry is recognized as a duplicate by
// the server instead of creating a second logical mutation.
async function enqueueSnapshot(snapshot, baseRev, baseSnap, scope = currentScope, kind = 'snapshot', generationId = null, opId = null) {
    if (!syncEnabled() || !scope) return;
    const scopeKey = makeScopeKey(scope);
    if (!scopeKey) return;

    const row = {
        id: opId || newId(),
        scopeKey,
        createdAt: Date.now(),
        queueSequence: ++queueSequenceCounter,
        kind,
        generationId: generationId ? String(generationId) : null,
        baseRevision: Number(baseRev || 0),
        baseSnapshot: clone(baseSnap || { messages: [], metadata: {} }),
        snapshot: clone(snapshot),
    };

    const existingRows = await idbList(scopeKey);
    const duplicate = existingRows.find(existing =>
        existing.kind === kind &&
        existing.generationId === row.generationId &&
        deepEqual(existing.snapshot, row.snapshot),
    );
    if (duplicate) return;

    const byteSize = utf8ByteLength(row);
    const currentBytes = existingRows.reduce((sum, r) => sum + utf8ByteLength(r), 0);
    if (currentBytes + byteSize > MAX_QUEUE_BYTES) {
        warn('queue byte budget exceeded; dropping oldest queued snapshots');
        const sorted = [...existingRows];
        let budget = currentBytes;
        while (sorted.length && budget + byteSize > MAX_QUEUE_BYTES) {
            const oldest = sorted.shift();
            await idbDelete(oldest.id);
            budget -= utf8ByteLength(oldest);
        }
    }

    await idbPut(row);

    const rows = await idbList(scopeKey);
    if (rows.length > MAX_QUEUE) {
        for (const old of rows.slice(0, rows.length - MAX_QUEUE)) await idbDelete(old.id);
    }
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
        opId,
        baseRevision: baseRev,
        snapshot,
    });
}

async function publishLocalSnapshot(snapshot = durableSnapshot(), { allowDuringGeneration = false, scope = currentScope, opId = null } = {}) {
    if (!scope || !settings.enabled || !syncEnabled()) return false;
    if (!nativeScopeStable(scope)) return false;
    if (localGeneration && !allowDuringGeneration) return false;
    if (localGeneration && allowDuringGeneration && localGeneration.phase === 'streaming') return false;
    if (generationActive(serverState?.generation) && !localGeneration) return false;

    if (deepEqual(snapshot, serverState?.snapshot)) {
        clearLocalDirty(scope);
        rebuildLastSyncedMap(snapshot.messages);
        return true;
    }

    const scopeAtPublish = clone(scope);
    const scopeKeyAtPublish = makeScopeKey(scopeAtPublish);
    const base = clone(baseSnapshot || { messages: [], metadata: {} });
    const revision = Number(serverState?.revision || 0);
    // One opId per logical snapshot; retries after ambiguous outcomes reuse it.
    const localOpId = opId || newId();

    try {
        const result = await sendSnapshotDirect(snapshot, revision, localOpId, scopeAtPublish);
        if (scopeKeyValue !== scopeKeyAtPublish || !currentScope || makeScopeKey(currentScope) !== scopeKeyAtPublish) return false;
        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        clearLocalDirty(scopeAtPublish);
        rebuildLastSyncedMap(snapshot.messages);
        broadcastWake('state');
        return true;
    } catch (error) {
        if (scopeKeyValue !== scopeKeyAtPublish) return false;

        if (error?.status === 409 && error?.payload?.state) {
            const remoteState = error.payload.state;
            if (error.payload.error === 'generation_active') return false;

            const merged = mergeSnapshots(base, snapshot, remoteState.snapshot);
            serverState = remoteState;
            baseSnapshot = clone(remoteState.snapshot);

            const retryBase = Number(remoteState.revision);
            try {
                const result = await sendSnapshotDirect(merged, retryBase, localOpId, scopeAtPublish);
                if (scopeKeyValue !== scopeKeyAtPublish) return false;
                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
                const applied = await applySnapshot(merged, {
                    save: true,
                    render: true,
                    expectedScope: scopeAtPublish,
                    clearDirty: false,
                });
                if (!applied) return false;
                clearLocalDirty(scopeAtPublish);
                broadcastWake('state');
                return true;
            } catch (retryError) {
                if (retryError?.status === 409 && retryError?.payload?.error === 'generation_active') return false;
                await enqueueSnapshot(
                    merged,
                    retryError?.payload?.state?.revision ?? retryBase,
                    retryError?.payload?.state?.snapshot ?? remoteState.snapshot,
                    scopeAtPublish,
                    'snapshot',
                    null,
                    localOpId,
                );
                scheduleQueueFlushRetry();
                return false;
            }
        }

        if (localGeneration && allowDuringGeneration) return false;
        // Ambiguous or failed: queue with the SAME opId for idempotent retry.
        await enqueueSnapshot(snapshot, revision, base, scopeAtPublish, 'snapshot', null, localOpId);
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
    const rows = await idbList(scopeKeyAtFlush);

    for (const row of rows) {
        if (!currentScope || scopeKeyValue !== scopeKeyAtFlush || !nativeScopeStable(scopeAtFlush)) return;
        if (localGeneration || generationActive(serverState?.generation)) return;

        try {
            let nextSnapshot = clone(row.snapshot);
            let nextBase = clone(row.baseSnapshot || { messages: [], metadata: {} });
            let nextRevision = Number(row.baseRevision || 0);
            const remote = serverState?.snapshot ? clone(serverState.snapshot) : null;
            const remoteRevision = Number(serverState?.revision || nextRevision);

            if (remote && remoteRevision !== nextRevision) {
                nextSnapshot = mergeSnapshots(nextBase, nextSnapshot, remote);
                nextBase = clone(remote);
                nextRevision = remoteRevision;
                row.snapshot = clone(nextSnapshot);
                row.baseSnapshot = clone(nextBase);
                row.baseRevision = nextRevision;
                await idbPut(row);
            }

            // Already-satisfied operation: a previous response was lost but
            // the server committed it. Do not create another revision.
            if (deepEqual(nextSnapshot, serverState?.snapshot)) {
                await idbDelete(row.id);
                rebuildLastSyncedMap(nextSnapshot.messages);
                continue;
            }

            let result = null;
            let sendError = null;
            for (let sendAttempt = 0; sendAttempt < 3; sendAttempt += 1) {
                try {
                    // row.id is the stable opId across all retries.
                    result = await sendSnapshotDirect(nextSnapshot, nextRevision, row.id, scopeAtFlush);
                    sendError = null;
                    break;
                } catch (error) {
                    sendError = error;
                    if (error?.status === 409) break;
                    if (sendAttempt < 2) await sleep(150 * (sendAttempt + 1));
                }
            }

            if (sendError) throw sendError;
            if (!result || scopeKeyValue !== scopeKeyAtFlush) return;

            serverState = result.state;
            baseSnapshot = clone(result.state.snapshot);

            // Apply BEFORE deleting the row: a failed local application keeps
            // the row, and the server's opId idempotency makes the retry safe.
            const applied = await applySnapshot(incomingSnapshot(result.state.snapshot), {
                save: true,
                render: true,
                expectedScope: scopeAtFlush,
            });
            if (!applied) return;

            await idbDelete(row.id);
            clearLocalDirty(scopeAtFlush);
        } catch (error) {
            if (scopeKeyValue !== scopeKeyAtFlush) return;

            if (error?.status === 409 && error?.payload?.state) {
                const remote = error.payload.state;
                if (remote.generation || error.payload.error === 'generation_active') {
                    serverState = remote;
                    baseSnapshot = clone(remote.snapshot);
                    return;
                }

                const merged = mergeSnapshots(row.baseSnapshot, row.snapshot, remote.snapshot);
                row.snapshot = clone(merged);
                row.baseSnapshot = clone(remote.snapshot);
                row.baseRevision = Number(remote.revision);
                serverState = remote;
                baseSnapshot = clone(remote.snapshot);
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

    const localSnapshot = syncSnapshot(durableSnapshot());

    if (joinAbortController) {
        try { joinAbortController.abort(); } catch { /* ignore */ }
    }

    const joinController = new AbortController();
    joinAbortController = joinController;

    try {
        const result = await api('/join', 'POST', {
            scope: scopeAtJoin,
            clientId,
            deviceId,
            snapshot: localSnapshot,
        }, '', { signal: joinController.signal, timeoutMs: API_TIMEOUT_MS });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtJoin)) {
            try { await api('/leave', 'POST', { scope: scopeAtJoin, clientId, deviceId }); } catch { /* best effort */ }
            return;
        }

        if (!nativeScopeStable(scopeAtJoin)) return;
        if (joinAbortController === joinController) joinAbortController = null;

        if (scopeRetryTimer) {
            clearTimeout(scopeRetryTimer);
            scopeRetryTimer = null;
        }

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        // The join response carries the authoritative SSE cursor. This
        // prevents replaying stale history after a full authoritative join.
        lastSseEventId = Number(result.state?.lastEventId || 0);
        resetChunkAssemblies();
        remoteGenerationId = null;
        lastRemoteStreamSeq = -1;
        generationMismatchSince = 0;

        // A page reload cannot continue ST's in-flight request. Same-client
        // ownership left by a previous page instance is stale and must not be
        // resurrected.
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
                    generationId: staleOwnedGenerationId,
                    phase: 'stopped',
                    snapshot: clone(serverState.snapshot),
                    opId: newId(),
                });
                if (currentScopeGuard(epoch)) {
                    serverState = cleared.state;
                    baseSnapshot = clone(cleared.state.snapshot);
                    lastSseEventId = Number(cleared.state?.lastEventId || lastSseEventId);
                    rememberTerminatedGeneration(staleOwnedGenerationId);
                }
            } catch (staleError) {
                if (staleError?.status === 409 && staleError?.payload?.state) {
                    serverState = staleError.payload.state;
                    baseSnapshot = clone(staleError.payload.state.snapshot);
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

        const incoming = incomingSnapshot(serverState.snapshot);
        const queued = await idbList(scopeKeyValue);

        // Existing server state remains authoritative on first join.
        if (queued.length && !serverState.generation) {
            await flushQueue();
        } else if (!deepEqual(localSnapshot, incoming) && !generationIsMine(serverState.generation)) {
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

        // SSE hello + generation_state deliver the live remote message; the
        // join response deliberately carries generation metadata only.
        connectSse(epoch);
        startHeartbeats(epoch);

        await flushQueue();
        updateGenerationUi();
        statusText(`Connected · rev ${serverState.revision}`);
    } catch (error) {
        if (joinAbortController === joinController) joinAbortController = null;
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
    // Chunks from the old connection never apply to the new one. The process
    // chain is NOT reset: its in-flight tail re-checks scope/epoch guards, so
    // letting it drain is safer than racing a fresh chain against it.
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

// hello carries generation METADATA only; the live message arrives via the
// generation_state transfer immediately after.
function handleServerHello(data) {
    // hello is always the first event of a fresh SSE connection. Any assembly
    // still in the map belongs to a dead connection and can never complete —
    // clear it now instead of waiting out the 30s expiry.
    resetChunkAssemblies();

    if (data.protocol !== PROTOCOL || data.schema !== SCHEMA) {
        statusText(`Protocol mismatch (${data.protocol}/${data.schema})`);
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
        // No live message here: generation_state supplies it.
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

// Returns true when the event is safely consumed, false when the SSE layer
// should resync. Stale-but-consistent events count as consumed. Transient
// native-scope instability counts as consumed too: the scope switch in
// flight will resync authoritatively, and treating it as failure would cause
// a reconnect storm against an event that cannot be applied right now.
async function handleSnapshotEvent(data) {
    return new Promise(resolve => {
        const run = stateApplyChain.then(async () => {
            const revision = Number(data?.revision || 0);
            if (!revision || revision <= Number(serverState?.revision || 0)) return true; // stale, safely consumed
            if (!currentScope || !nativeScopeStable(currentScope)) {
                log('[MCS] snapshot arrived during transient scope instability; deferring to scope switch');
                return true;
            }

            const scopeAtEvent = clone(currentScope);
            const remote = incomingSnapshot(data.snapshot);
            const knownBase = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });
            const local = syncSnapshot(durableSnapshot());
            const dirty = isLocalDirty(scopeAtEvent);
            const incomingGenerationId = String(data?.generationId || '');

            serverState = { ...(serverState || {}), revision, snapshot: clone(data.snapshot) };
            baseSnapshot = clone(data.snapshot);

            if (serverState?.generation || incomingGenerationId) {
                updateGenerationUi();
                return true;
            }

            if (data.sourceClientId === clientId) {
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
            } else {
                rebuildLastSyncedMap(appliedSnapshot.messages);
            }

            if (!deepEqual(appliedSnapshot, remote)) {
                if (!nativeScopeStable(scopeAtEvent) || scopeKeyValue !== makeScopeKey(scopeAtEvent)) return false;
                try {
                    const result = await sendSnapshotDirect(appliedSnapshot, revision, newId(), scopeAtEvent);
                    if (scopeKeyValue === makeScopeKey(scopeAtEvent)) {
                        serverState = result.state;
                        baseSnapshot = clone(result.state.snapshot);
                        clearLocalDirty(scopeAtEvent);
                    }
                } catch (publishError) {
                    if (publishError?.status === 409 && publishError?.payload?.state) {
                        serverState = publishError.payload.state;
                        baseSnapshot = clone(publishError.payload.state.snapshot);
                    } else {
                        await enqueueSnapshot(appliedSnapshot, revision, knownBase, scopeAtEvent);
                        scheduleQueueFlushRetry();
                    }
                }
            } else {
                clearLocalDirty(scopeAtEvent);
            }

            broadcastWake('state');
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
                    localGenerationBaseSnapshot = localGenerationBaseSnapshot || clone(baseSnapshot || serverState.snapshot || { messages: [], metadata: {} });
                    localGenerationLastSnapshot = localGenerationLastSnapshot || clone(serverState.snapshot || baseSnapshot || { messages: [], metadata: {} });
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
        // Claimed/started events carry no live message; generation_state and
        // stream events deliver content.
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
        });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtRecovery)) return true;

        const authoritative = result.state || null;
        const generation = authoritative?.generation || null;
        const localId = localGeneration?.generationId || null;

        serverState = authoritative;
        baseSnapshot = clone(authoritative?.snapshot || baseSnapshot || { messages: [], metadata: {} });
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
            // Live remote message is reacquired via generation_state on the
            // next SSE reconnect/resync cycle.
            updateGenerationUi();
            return true;
        }

        if (localGeneration) {
            const localGenerationId = localGeneration.generationId;
            generationMismatchSince = generationMismatchSince || Date.now();

            if (generationIsStopRequested(localGenerationId) || generationTerminalPhase === 'stopped') {
                generationTerminalPhase = 'stopped';
                clearGenerationStreamWork(localGenerationId);
                scheduleTerminalRetry(localGenerationId, 'stopped', 250);
                updateGenerationUi();
                return true;
            }

            void reacquireGenerationOwnership('generation_recovered').then(recovered => {
                if (recovered) {
                    generationMismatchSince = 0;
                    updateGenerationUi();
                }
            });

            generationHeartbeatFailures = 0;
            renderBanner('Reconnecting shared generation…');
            scheduleGenerationStartRetry(localGenerationId, 500);
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
    if (hadGap) resyncCurrentScope(scopeEpoch).catch(error => warn('stream gap resync failed', error));

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

// Remote stream preview. The chat array is snapshotted before mutation and
// restored if the DOM update fails, so a bad render never poisons the final
// sync state — the terminal snapshot remains authoritative.
async function applyRemoteStreamNow(item) {
    if (!item || !ctx?.chat || !currentScope || !nativeScopeStable(currentScope)) return false;

    const g = serverState?.generation;
    if (!g || g.generationId !== item.generationId || generationIsMine(g)) return false;
    if (generationIsStopRequested(item.generationId)) return false;

    const id = messageId(item.message);
    if (!id || suppressedRemoteStreamMessageIds.has(id)) return false;
    if (Number(item.seq || 0) < Number(lastRemoteStreamSeq || 0)) return false;

    applyingRemoteDepth += 1;

    let previousMessages = null;
    let mutated = false;

    try {
        refreshLiveContext();
        if (!currentScope || !nativeScopeStable(currentScope)) return false;

        previousMessages = clone(ctx.chat);

        let index = ctx.chat.findIndex(message => messageId(message) === id);

        if (index < 0) {
            if (Number.isInteger(item.messageIndex) && item.messageIndex >= 0 && item.messageIndex < ctx.chat.length) {
                const existingAtIndex = ctx.chat[item.messageIndex];
                if (existingAtIndex && !existingAtIndex.is_user && !existingAtIndex.is_system) {
                    index = item.messageIndex;
                    ctx.chat[index] = clone(item.message);
                    mutated = true;
                } else {
                    return false;
                }
            } else {
                // Do not resurrect an arbitrary deleted assistant message; the
                // terminal snapshot is authoritative for structural changes.
                if (ctx.chat.length && ctx.chat[ctx.chat.length - 1]?.is_user) return false;
                ctx.chat.push(clone(item.message));
                index = ctx.chat.length - 1;
                mutated = true;
            }
        } else {
            ctx.chat[index] = clone(item.message);
            mutated = true;
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
        if (mutated && previousMessages && ctx?.chat) {
            try {
                ctx.chat.splice(0, ctx.chat.length, ...previousMessages);
                try { ctx.printMessages?.(); } catch { /* best effort */ }
            } catch (restoreError) {
                warn('applyRemoteStreamNow rollback failed', restoreError);
            }
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

    const activeId = localGeneration?.generationId || serverState?.generation?.generationId || null;
    if (activeId && activeId !== generationId) {
        // A terminal for an older generation can never mutate a newer one.
        rememberTerminatedGeneration(generationId);
        return true;
    }

    // Duplicate detection happens BEFORE we mark this generation terminated,
    // otherwise the marker we set would suppress our own processing.
    if (revision && currentRevision && revision < currentRevision) return true;
    if (isGenerationTerminated(generationId) && !localGenerationMatches(generationId)) return true;

    const scopeAtEvent = clone(currentScope);
    const hadLocalGeneration = !!localGeneration && localGeneration.generationId === generationId;
    const mine = hadLocalGeneration && !!terminalGeneration && generationIsMine(terminalGeneration);

    const terminalSnapshot = incomingSnapshot(data.snapshot || serverState?.snapshot || { messages: [], metadata: {} });
    const knownBase = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });
    const dirty = !mine && isLocalDirty(scopeAtEvent);
    const local = !mine && dirty ? syncSnapshot(durableSnapshot()) : null;

    rememberTerminatedGeneration(generationId);

    serverState = {
        ...(serverState || {}),
        revision: Math.max(currentRevision, revision),
        snapshot: clone(data.snapshot || serverState?.snapshot || { messages: [], metadata: {} }),
        generation: null,
    };
    baseSnapshot = clone(serverState.snapshot);

    if (mine) {
        clearLocalGenerationState();
        clearLocalDirty(scopeAtEvent);
    } else if (scopeAtEvent && nativeScopeStable(scopeAtEvent) && data?.snapshot) {
        let finalSnapshot = terminalSnapshot;
        if (dirty) finalSnapshot = mergeSnapshots(knownBase, local, terminalSnapshot);

        // Never apply an old terminal snapshot over a new local generation.
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
                    baseSnapshot = clone(committed.state.snapshot);
                } catch (error) {
                    if (error?.status === 409 && error?.payload?.state) {
                        serverState = error.payload.state;
                        baseSnapshot = clone(error.payload.state.snapshot);
                    } else {
                        await enqueueSnapshot(finalSnapshot, Number(serverState?.revision || 0), baseSnapshot, scopeAtEvent);
                        scheduleQueueFlushRetry();
                    }
                }
            }
            clearLocalDirty(scopeAtEvent);
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
            });

            if (!currentScopeGuard(epoch) || requestSeq < nativeHeartbeatAppliedSeq) return;
            nativeHeartbeatAppliedSeq = requestSeq;

            const oldRevision = Number(serverState.revision || 0);
            const oldGenerationId = serverState.generation?.generationId || null;
            const newRevision = Number(result.revision || 0);
            const newGenerationId = result.generation?.generationId || null;

            // Server revision is monotonic within a scope; never let a stale
            // heartbeat erase a newer generation response.
            if (newRevision < oldRevision) return;

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
    if (!localGeneration || !localGenerationScope || generationRecoveryInFlight || terminalizingGenerationId) return false;

    const generation = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration = localGenerationEpoch || scopeEpoch;
    const generationId = generation.generationId;

    if (!currentScopeGuard(epochAtGeneration) || !nativeScopeStable(scopeAtGeneration)) return false;
    if (generationIsStopRequested(generationId) || generationTerminalPhase === 'stopped') return false;

    const run = (async () => {
        try {
            const stateResult = await api('/state', 'POST', {
                scope: scopeAtGeneration,
                clientId,
                deviceId,
            });

            if (!localGenerationMatches(generationId, scopeAtGeneration) || !currentScopeGuard(epochAtGeneration)) return false;

            const state = stateResult.state;
            const current = state?.generation || null;

            if (current && current.generationId === generationId && generationIsMine(current)) {
                serverState = state;
                localGeneration = { ...localGeneration, ...clone(current) };
                generationMismatchSince = 0;
                if (current.stopRequested) {
                    rememberStopRequestedGeneration(generationId);
                    return false;
                }
                if (['started', 'streaming'].includes(current.phase)) {
                    generationServerReadyId = generationId;
                    return true;
                }
                generationServerReadyId = null;
                scheduleGenerationStartRetry(generationId, 250);
                return await ensureGenerationStarted();
            }

            if (current && generationActive(current) && current.generationId !== generationId) {
                generationMismatchSince = generationMismatchSince || Date.now();
                log('[MCS] competing generation observed during recovery; preserving local generation until confirmed', { reason, generationId, competing: current.generationId });
                return false;
            }

            // Merge against the current authoritative snapshot before
            // reclaiming. A revision advance is normal during streaming.
            const authoritativeSnapshot = normalizeSnapshot(state?.snapshot || { messages: [], metadata: {} });
            const localSnapshot = syncSnapshot(durableSnapshot());
            const recoveryBase = clone(localGenerationBaseSnapshot || baseSnapshot || { messages: [], metadata: {} });
            const desired = mergeSnapshots(recoveryBase, localSnapshot, authoritativeSnapshot);

            // One claim opId for this entire recovery operation; retries of
            // this claim are idempotent on the server.
            const claimOpId = newId();
            const claimed = await api('/generation/claim', 'POST', {
                scope: scopeAtGeneration,
                clientId,
                deviceId,
                opId: claimOpId,
                generationId,
                generationType: String(generation.generationType || 'normal'),
                baseRevision: Number(state.revision || 0),
                snapshot: desired,
            });

            if (!localGenerationMatches(generationId, scopeAtGeneration) || !currentScopeGuard(epochAtGeneration)) return false;

            const nextGeneration = claimed.state?.generation;
            if (!nextGeneration || nextGeneration.generationId !== generationId || !generationIsMine(nextGeneration)) return false;

            serverState = claimed.state;
            baseSnapshot = clone(claimed.state.snapshot);
            localGeneration = clone(nextGeneration);
            localGenerationBaseSnapshot = clone(claimed.state.snapshot);
            localGenerationBaseRevision = Number(claimed.state.revision || 0);
            generationServerReadyId = null;
            generationMismatchSince = 0;
            updateGenerationUi();

            startGenerationHeartbeat(epochAtGeneration);
            return await ensureGenerationStarted();
        } catch (error) {
            if (error?.status === 409 && error?.payload?.state) {
                const state = error.payload.state;
                serverState = state;
                baseSnapshot = clone(state.snapshot);
                const competing = state.generation;
                if (competing && competing.generationId !== generationId && generationActive(competing)) {
                    generationMismatchSince = generationMismatchSince || Date.now();
                }
            }
            log('[MCS] generation ownership recovery failed; keeping native generation alive', reason, error);
            return false;
        }
    })();

    generationRecoveryInFlight = run;
    try {
        return await run;
    } finally {
        if (generationRecoveryInFlight === run) generationRecoveryInFlight = null;
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
                    generationId,
                });

                if (!localGeneration || localGeneration.generationId !== generationId || !currentScopeGuard(epoch)) return;

                const state = result.state || null;
                const stateGeneration = state?.generation || null;
                serverState = state;

                if (result.stopRequested || stateGeneration?.stopRequested) {
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

                if (stateGeneration && stateGeneration.generationId === generationId && generationIsMine(stateGeneration)) {
                    localGeneration = { ...localGeneration, ...clone(stateGeneration) };
                    generationServerReadyId = ['started', 'streaming'].includes(stateGeneration.phase) ? generationId : generationServerReadyId;
                    generationHeartbeatFailures = 0;
                    generationMismatchSince = 0;
                    updateGenerationUi();
                    return;
                }

                const confirmedResult = await api('/state', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
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
                    if (generationIsStopRequested(generationId) || generationTerminalPhase === 'stopped') {
                        clearGenerationStreamWork(generationId);
                        void sendGenerationTerminal('stopped').catch(error => warn('terminal after lost stop-requested generation failed', error));
                        return;
                    }
                    generationMismatchSince = 0;
                    await openScope(epoch);
                    void reacquireGenerationOwnership('heartbeat-recovery').catch(error => warn('heartbeat recovery failed', error));
                    return;
                }

                if (confirmed.generationId !== generationId && generationActive(confirmed)) {
                    generationMismatchSince = generationMismatchSince || Date.now();
                    if (Date.now() - generationMismatchSince < OWNERSHIP_CONFLICT_GRACE_MS) return;

                    const finalStateResult = await api('/state', 'POST', {
                        scope: scopeAtGeneration,
                        clientId,
                        deviceId,
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
                        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                    } else if (finalGeneration?.generationId === generationId && generationIsMine(finalGeneration)) {
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
                    if (!generationIsStopRequested(generationId) && generationTerminalPhase !== 'stopped' && Date.now() - generationMismatchSince >= OWNERSHIP_RECOVERY_GRACE_MS) {
                        void reacquireGenerationOwnership('heartbeat-409-recovery');
                    }
                    return;
                }

                // Never kill the native LLM on transport errors alone.
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

    try {
        const result = await api('/state', 'POST', {
            scope: scopeAtRequest,
            clientId,
            deviceId,
        });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtRequest)) return;

        const state = result.state;
        const serverGeneration = state.generation || null;
        if (serverGeneration?.stopRequested) rememberStopRequestedGeneration(serverGeneration.generationId);
        const remote = incomingSnapshot(state.snapshot);
        const dirty = isLocalDirty(scopeAtRequest);
        const local = syncSnapshot(durableSnapshot());
        const knownBase = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });

        serverState = state;
        baseSnapshot = clone(state.snapshot);
        // Adopt the authoritative SSE cursor from the state response.
        lastSseEventId = Number(state?.lastEventId || lastSseEventId);

        if (localGeneration) {
            const localId = localGeneration.generationId;

            if (serverGeneration && serverGeneration.generationId === localId && generationIsMine(serverGeneration)) {
                // /state carries no live message; the SSE generation_state
                // transfer reacquires it on reconnect.
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
                if (!generationIsStopRequested(localId) && generationTerminalPhase !== 'stopped') {
                    void reacquireGenerationOwnership('resync-no-generation');
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
                        generationId: staleId,
                        phase: 'stopped',
                        snapshot: clone(state.snapshot),
                        opId: newId(),
                    });
                    serverState = cleared.state;
                    baseSnapshot = clone(cleared.state.snapshot);
                    lastSseEventId = Number(cleared.state?.lastEventId || lastSseEventId);
                } catch (error) {
                    if (error?.status === 409 && error?.payload?.state) {
                        serverState = error.payload.state;
                        baseSnapshot = clone(error.payload.state.snapshot);
                    }
                }
            }
        }

        const effectiveGeneration = serverState.generation || null;
        if (effectiveGeneration?.stopRequested) rememberStopRequestedGeneration(effectiveGeneration.generationId);

        // The live remote message is NOT in /state; if this resync replaced a
        // remote generation we know, the next generation_state transfer (SSE
        // reconnect) reacquires it. Render nothing stale here.

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
                        baseSnapshot = clone(publishResult.state.snapshot);
                        clearLocalDirty(scopeAtRequest);
                        rebuildLastSyncedMap(merged.messages);
                    } catch (publishError) {
                        if (publishError?.status === 409 && publishError?.payload?.state) {
                            serverState = publishError.payload.state;
                            baseSnapshot = clone(publishError.payload.state.snapshot);
                        } else {
                            await enqueueSnapshot(merged, Number(serverState.revision), serverState.snapshot, scopeAtRequest);
                            scheduleQueueFlushRetry();
                        }
                    }
                } else {
                    clearLocalDirty(scopeAtRequest);
                    rebuildLastSyncedMap(merged.messages);
                }
            } else if (!deepEqual(local, remote)) {
                const applied = await applySnapshot(remote, {
                    save: true,
                    render: true,
                    expectedScope: scopeAtRequest,
                });
                if (!applied) return;
                clearLocalDirty(scopeAtRequest);
            } else {
                rebuildLastSyncedMap(remote.messages);
            }
        }

        updateGenerationUi();
    } catch (error) {
        warn('resync failed', error);
    }
}

function resyncCurrentScope(epoch = scopeEpoch) {
    const run = resyncChain.then(() => resyncCurrentScopeInternal(epoch));
    resyncChain = run.then(() => undefined, error => warn('resync chain failed', error));
    return run;
}

// One stable opId per logical termination; every retry attempt reuses it so a
// lost response can never produce two terminal revisions.
async function terminateGenerationOnServer(generation, scope, phase, snapshot, opId = null) {
    let lastError = null;
    const terminalOpId = opId || newId();

    for (let attempt = 0; attempt < 4; attempt += 1) {
        try {
            const result = await api('/generation/terminal', 'POST', {
                scope,
                clientId,
                deviceId,
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

async function leaveCurrentScope({ preserveNativeGeneration = false } = {}) {
    if (joinAbortController) {
        try { joinAbortController.abort(); } catch { /* ignore */ }
        joinAbortController = null;
    }
    if (!currentScope) return;

    const leavingScope = clone(currentScope);
    const leavingGenerationId = localGeneration?.generationId || null;

    if (localGeneration && localGenerationScope && !preserveNativeGeneration) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        try { await sendGenerationTerminal('stopped'); } catch (error) { warn('generation cleanup failed while leaving scope', error); }
    }

    try {
        await api('/leave', 'POST', {
            scope: leavingScope,
            clientId,
            deviceId,
        });
    } catch { /* best effort */ }

    disconnectSse();
    stopHeartbeats();
    stopGenerationHeartbeat();

    if (scopeRetryTimer) clearTimeout(scopeRetryTimer);
    if (queueRetryTimer) clearTimeout(queueRetryTimer);
    if (generationStartRetryTimer) clearTimeout(generationStartRetryTimer);
    if (terminalRetryTimer) clearTimeout(terminalRetryTimer);
    if (streamTimer) clearTimeout(streamTimer);
    if (streamRetryTimer) clearTimeout(streamRetryTimer);
    if (remoteRenderTimer) clearTimeout(remoteRenderTimer);
    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);
    if (remoteUiRefreshTimer) clearTimeout(remoteUiRefreshTimer);

    scopeRetryTimer = null;
    queueRetryTimer = null;
    generationStartRetryTimer = null;
    terminalRetryTimer = null;
    streamTimer = null;
    streamRetryTimer = null;
    streamCaptureTimer = null;
    remoteUiRefreshTimer = null;

    serverState = null;
    baseSnapshot = null;
    clearLocalGenerationState();
    clearRemoteStreamState();
    resetChunkAssemblies();
    lastSyncedMessageMap = new Map();
    lastSseEventId = 0;
    nativeHeartbeatAppliedSeq = 0;
    nativeHeartbeatRequestSeq = 0;
    setSendLock('');
    setRemoteSendButtonMode(false);
    renderBanner('');
    clearLocalDirty();

    log('[MCS] left scope', leavingScope, leavingGenerationId);
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
            if (nativeScopeStable(nextScope)) {
                if (!serverState && settings.enabled && settings.autoConnect) await openScope(scopeEpoch);
                else updateGenerationUi();
            }
            return;
        }

        if (localGeneration && currentScope) {
            pendingScopeSwitchReason = reason;
            log('[MCS] deferring scope switch until active generation ends', { reason, from: currentScope, to: nextScope });
            return;
        }

        ++scopeEpoch;
        const epoch = scopeEpoch;
        clearGenerationTerminalTimer();
        await leaveCurrentScope();

        // Chains are NOT reset: their in-flight tails re-check scope/epoch
        // guards (applySnapshotNow refuses unstable scopes), so draining is
        // safer than racing a fresh chain against an old one.
        currentScope = nextScope;
        scopeKeyValue = nextKey;
        localDirty = false;
        localDirtyScopeKey = '';
        lastSseEventId = 0;
        lastSyncedMessageMap = new Map();

        await ensureIdsPersisted(nextScope);
        if (settings.enabled && settings.autoConnect) await openScope(epoch);
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

    if (generationIsStopRequested(generationId) || terminalizingGenerationId === generationId) return false;
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

                const result = await api('/generation/started', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                    generationId,
                });

                if (!localGenerationMatches(generationId, scopeAtGeneration)) return false;

                const current = result.state?.generation || null;
                if (!current || current.generationId !== generationId || !generationIsMine(current)) return false;

                serverState = result.state;
                localGeneration = { ...localGeneration, ...clone(current) };
                generationServerReadyId = generationId;
                generationHeartbeatFailures = 0;
                updateGenerationUi();
                return true;
            } catch (error) {
                lastError = error;
                if (error?.status === 409 && error?.payload?.state) {
                    const state = error.payload.state;
                    serverState = state;
                    baseSnapshot = clone(state.snapshot);
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

    // Quiet/background generations are outside the shared foreground lease.
    if (shouldBypassMcsGeneration(type)) return;

    if (!settings.enabled || !settings.coordinateGeneration || applyingRemoteDepth > 0) return;

    if (localGeneration) {
        const generationId = localGeneration.generationId;
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
                    generationId: existing.generationId,
                    phase: 'stopped',
                    snapshot: clone(serverState?.snapshot || { messages: [], metadata: {} }),
                    opId: newId(),
                });
                serverState = cleared.state;
                baseSnapshot = clone(cleared.state.snapshot);
                rememberTerminatedGeneration(existing.generationId);
                existing = serverState?.generation || null;
            } catch (error) {
                warn('failed to clear stale same-client generation before new generation', error);
                abort(false);
                return;
            }
        }

        if (existing && generationActive(existing)) {
            abort(false);
            if (settings.notifications) statusText('Another client is already generating this shared chat.', true);
            updateGenerationUi();
            return;
        }
    }

    const generationId = newId();
    generationClaimInFlightId = generationId;
    // One claim opId for the whole logical claim; every retry attempt reuses
    // it so a timed-out accepted claim resolves to the existing state.
    const claimOpId = newId();

    let desired = null;
    let claimBase = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });
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
            if (!currentScopeGuard(epochAtClaim) || !nativeScopeStable(scopeAtClaim)) {
                abort(false);
                return;
            }

            try {
                claimResult = await api('/generation/claim', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
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
                        if (other?.generationId === generationId) {
                            claimResult = payload;
                            break;
                        }

                        serverState = payload.state;
                        baseSnapshot = clone(payload.state.snapshot);
                        abort(false);
                        if (settings.notifications) statusText('Another client is already generating this shared chat.', true);
                        updateGenerationUi();
                        return;
                    }

                    const merged = mergeSnapshots(claimBase, desired, payload.state.snapshot);
                    serverState = payload.state;
                    baseSnapshot = clone(payload.state.snapshot);
                    desired = merged;
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

        if (!currentScopeGuard(epochAtClaim) || !nativeScopeStable(scopeAtClaim)) {
            try {
                await api('/generation/terminal', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
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
        baseSnapshot = clone(claimResult.state.snapshot);
        localGeneration = clone(claimed);
        localGenerationScope = clone(scopeAtClaim);
        localGenerationEpoch = epochAtClaim;
        localGenerationBaseSnapshot = clone(baseSnapshot);
        localGenerationBaseRevision = Number(claimResult.state.revision || 0);
        localGenerationSettings = {
            syncMessages: !!settings.syncMessages,
            syncMetadata: !!settings.syncMetadata,
        };
        localGenerationLastSnapshot = clone(desired);
        localStreamMessageId = null;
        localStreamMessageIndex = null;
        generationClaimedThisPage = true;
        generationTerminalPhase = null;
        leaveAfterLocalGeneration = false;
        markLocalDirty(scopeAtClaim);
        rebuildLastSyncedMap(desired.messages);
        updateGenerationUi();
        startGenerationHeartbeat(epochAtClaim);

        // Keep the lease alive and let ST continue if the handshake hiccups.
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

        const request = (async () => {
            try {
                const result = await api('/generation/stream', 'POST', {
                    scope: scopeAtStream,
                    clientId,
                    deviceId,
                    generationId,
                    seq: payload.seq,
                    message: payload.message,
                    messageIndex: payload.messageIndex,
                });

                if (!localGenerationMatches(generationId, scopeAtStream) || generationIsStopRequested(generationId)) return;

                const returned = result.state?.generation || null;
                serverState = result.state;
                if (returned?.generationId === generationId && generationIsMine(returned)) {
                    localGeneration = { ...localGeneration, ...clone(returned) };
                    generationServerReadyId = generationId;
                    if (returned.stopRequested) rememberStopRequestedGeneration(generationId);
                }
                lastStreamSentAt = Date.now();
            } catch (error) {
                const code = error?.payload?.error || '';

                if (generationIsStopRequested(generationId) || terminalizingGenerationId === generationId) return;

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
                            // Server already has this seq: it was accepted and
                            // the response was lost. Do not resend it.
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
                    // Timeout = outcome unknown. The server's same-seq
                    // idempotency check makes resending this seq safe.
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

function captureLocalStream() {
    if (terminalizingGenerationId || !localGeneration || !localGenerationScope || !ctx?.chat?.length) return;
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
    ensureMessageIds(messages);

    // Streaming content is a local mutation: stamp lastModified so a
    // concurrent remote edit conflict resolves by timestamp.
    messages[index].extra.multi_client_sync.lastModified = Date.now();

    const message = clone(messages[index]);
    const id = messageId(message);
    if (!id) return;

    localGenerationLastSnapshot = syncSnapshot(durableSnapshot());
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
        const eventProvesOwnership =
            !!eventGeneration &&
            eventGeneration.generationId === generationId &&
            generationIsMine(eventGeneration) &&
            nativeGenerationLooksActive();

        if (eventProvesOwnership) {
            const adopted = {
                ...(serverState?.generation?.generationId === generationId
                    ? clone(serverState.generation)
                    : {}),
                ...clone(eventGeneration),
                generationId,
                stopRequested: true,
            };
            serverState = {
                ...(serverState || {}),
                generation: adopted,
                scope: clone(currentScope),
            };
            localGeneration = adopted;
            localGenerationScope = clone(currentScope);
            localGenerationEpoch = scopeEpoch;
            generationClaimedThisPage = true;
        } else {
            const stateResult = await api('/state', 'POST', {
                scope: clone(currentScope),
                clientId,
                deviceId,
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
    }

    if (!localGenerationMatches(generationId, currentScope)) return true;

    generationTerminalPhase = 'stopped';
    clearGenerationTerminalTimer();
    clearTerminalRetryTimer();
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
        if (!localGeneration || localGeneration.generationId !== generationId) return;
        if (generationIsStopRequested(generationId)) {
            void sendGenerationTerminal('stopped').catch(error => warn('stopped terminal after late stop failed', error));
            return;
        }
        void sendGenerationTerminal('completed').catch(error => warn('completed terminal failed', error));
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

    if (generationIsStopRequested(generationId) || generationTerminalPhase === 'stopped') {
        generationTerminalPhase = 'stopped';
        generationTerminalTimer = safeSetTimer(() => {
            generationTerminalTimer = null;
            if (localGeneration?.generationId !== generationId) return;
            void sendGenerationTerminal('stopped').catch(error => warn('group stopped terminal failed', error));
        }, 60);
    } else {
        generationTerminalPhase = 'completed';
        generationTerminalTimer = safeSetTimer(() => {
            generationTerminalTimer = null;
            if (!localGeneration || localGeneration.generationId !== generationId) return;
            if (generationIsStopRequested(generationId)) {
                void sendGenerationTerminal('stopped').catch(error => warn('group late-stop terminal failed', error));
            } else {
                void sendGenerationTerminal('completed').catch(error => warn('group completed terminal failed', error));
            }
        }, GENERATION_CONTINUATION_GRACE_MS);
    }

    updateGenerationUi();
}

function capturePotentialDeletedStreamingMessage() {
    if (!localGeneration || !localStreamMessageId || !ctx?.chat) return;
    const stillExists = ctx.chat.some(message => messageId(message) === localStreamMessageId);
    if (!stillExists) log('[MCS] local streaming message disappeared before terminalization', localStreamMessageId);
}

function publishAfterLocalEvent(_event = undefined, { allowDuringGeneration = false } = {}) {
    if (applyingRemoteDepth > 0 || !currentScope || !settings.enabled || !syncEnabled() || terminalizingGenerationId) return Promise.resolve(false);

    refreshLiveContext();
    capturePotentialDeletedStreamingMessage();

    const scopeAtEvent = clone(currentScope);
    const epochAtEvent = scopeEpoch;

    if (!nativeScopeStable(scopeAtEvent)) {
        if (localGeneration) {
            log('[MCS] local event arrived during transient generation context swap; deferring sync');
            return Promise.resolve(false);
        }
        return switchScope('local-event-context-mismatch');
    }

    // Stamp tombstones/lastModified for local deletions and edits BEFORE the
    // snapshot is built, so the published snapshot carries the evidence the
    // merge policy needs.
    stampLocalMutations();

    markLocalDirty(scopeAtEvent);
    const snapshotAtEvent = syncSnapshot(durableSnapshot());

    const run = publishChain.then(async () => {
        if (scopeEpoch !== epochAtEvent || scopeKeyValue !== makeScopeKey(scopeAtEvent)) return false;
        if (!nativeScopeStable(scopeAtEvent)) return false;
        if (localGeneration && makeScopeKey(localGenerationScope) === makeScopeKey(scopeAtEvent) && !allowDuringGeneration) return false;
        if (localGeneration && generationIsStopRequested(localGeneration.generationId)) return false;
        if (localGeneration && localGeneration.phase === 'streaming' && allowDuringGeneration) return false;

        try {
            if (localGeneration) localGenerationLastSnapshot = clone(snapshotAtEvent);
            return await publishLocalSnapshot(snapshotAtEvent, { allowDuringGeneration, scope: scopeAtEvent });
        } catch (error) {
            warn('publish after local event failed', error);
            return false;
        }
    });

    publishChain = run.then(() => undefined, error => warn('local publish chain failed', error));
    return run;
}

async function handleChatLifecycleEvent() {
    await sleep(150);
    refreshLiveContext();
    if (nativeRestoreInProgress) return;
    if (localGeneration) {
        pendingScopeSwitchReason = 'chat-lifecycle';
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

    const listen = (eventType, fn) => {
        if (!eventType || !es?.on) return;
        es.on(eventType, fn);
        registeredEventHandlers.push([eventType, fn]);
    };

    listen(types.APP_INITIALIZED, () => switchScope('APP_INITIALIZED'));
    listen(types.APP_READY, () => switchScope('APP_READY'));
    listen(types.CHAT_CHANGED, handleChatLifecycleEvent);
    listen(types.CHAT_LOADED, handleChatLifecycleEvent);
    listen(types.CHAT_CREATED, handleChatLifecycleEvent);
    listen(types.CHAT_RENAMED, handleChatLifecycleEvent);
    listen(types.CHAT_DELETED, async data => {
        const old = typeof data === 'string' ? data.replace(/\.jsonl$/, '') : '';
        if (old && currentScope?.chatId === old && scopeKeyValue) await idbClearScope(scopeKeyValue).catch(() => {});
        await handleChatLifecycleEvent();
    });
    listen(types.GROUP_CHAT_CREATED, handleChatLifecycleEvent);
    listen(types.GROUP_CHAT_DELETED, handleChatLifecycleEvent);

    listen(types.MESSAGE_SENT, event => publishAfterLocalEvent(event, { allowDuringGeneration: true }));
    listen(types.MESSAGE_RECEIVED, publishAfterLocalEvent);
    listen(types.MESSAGE_EDITED, publishAfterLocalEvent);
    listen(types.MESSAGE_UPDATED, publishAfterLocalEvent);
    listen(types.MESSAGE_DELETED, publishAfterLocalEvent);
    listen(types.MESSAGE_SWIPED, publishAfterLocalEvent);
    listen(types.MESSAGE_SWIPE_DELETED, publishAfterLocalEvent);
    listen(types.MESSAGE_REASONING_EDITED, publishAfterLocalEvent);
    listen(types.MESSAGE_REASONING_DELETED, publishAfterLocalEvent);
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
    for (let attempt = 0; attempt < REMOTE_STOP_CONFIRM_ATTEMPTS; attempt += 1) {
        if (!currentScopeGuard(epoch)) return false;

        try {
            const result = await api('/state', 'POST', {
                scope,
                clientId,
                deviceId,
            }, '', { timeoutMs: STOP_API_TIMEOUT_MS });

            if (!currentScopeGuard(epoch)) return false;

            serverState = result.state;
            const generation = result.state?.generation || null;

            if (!generation) {
                rememberTerminatedGeneration(generationId);
                remoteStopGenerationId = null;
                updateGenerationUi();
                return true;
            }

            if (generation.generationId !== generationId) {
                const replacementTime = Number(generation.startedAt || generation.claimedAt || 0);
                const replacementIsNewer = !remoteStopRequestedAt || !replacementTime || replacementTime >= remoteStopRequestedAt;
                if (replacementIsNewer && generationActive(generation)) {
                    rememberTerminatedGeneration(generationId);
                    remoteStopGenerationId = generation.generationId;
                    updateGenerationUi();
                    return true;
                }
                return false;
            }

            if (generation.stopRequested) {
                rememberStopRequestedGeneration(generationId);
                remoteStopGenerationId = generationId;
                updateGenerationUi();
                return true;
            }

            const phase = String(generation.phase || '').toLowerCase();
            if (terminalGenerationPhases.has(phase) && generation.generationId === generationId) {
                rememberTerminatedGeneration(generationId);
                updateGenerationUi();
                return true;
            }
        } catch (error) {
            log('remote stop confirmation poll failed', error);
        }

        await sleep(REMOTE_STOP_CONFIRM_MS);
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
        clearGenerationStreamWork(generationId);
        renderBanner('Stopping generation…');
        try { ctx?.stopGeneration?.(); } catch (error) { warn('local stopGeneration failed', error); }
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

    // One opId for the entire stop request, honored by the server for
    // duplicate detection across any retry/confirmation path.
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
                serverState = result.state;
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
            }, '', { timeoutMs: STOP_API_TIMEOUT_MS }).catch(() => null);

            const confirmationState = confirmation?.state || null;
            const confirmationGeneration = confirmationState?.generation || null;

            if (confirmationState && currentScopeGuard(epochAtRequest)) {
                serverState = confirmationState;
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
    terminalizingGenerationId = generation.generationId;
    clearGenerationStreamWork(generation.generationId);

    try {
        const snapshot = nativeScopeStable(scopeAtGeneration)
            ? syncSnapshot(durableSnapshot())
            : clone(localGenerationLastSnapshot || serverState?.snapshot || localGenerationBaseSnapshot || { messages: [], metadata: {} });

        const result = await terminateGenerationOnServer(generation, scopeAtGeneration, phase, snapshot);

        if (result.state) {
            serverState = result.state;
            baseSnapshot = clone(result.state.snapshot);
        }

        if (result.success) {
            rememberTerminatedGeneration(generation.generationId);
            clearLocalDirty(scopeAtGeneration);
            clearLocalGenerationState();
            updateGenerationUi();
            return true;
        }

        terminalizingGenerationId = null;
        generationTerminalPhase = phase;
        scheduleTerminalRetry(generation.generationId, phase, TERMINAL_RETRY_MS);
        updateGenerationUi();
        return false;
    } finally {
        if (!localGeneration && terminalizingGenerationId === generation.generationId) terminalizingGenerationId = null;
    }
}

async function sendGenerationTerminal(phase = 'completed') {
    if (!localGeneration || !localGenerationScope) return false;

    const g = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration = localGenerationEpoch || scopeEpoch;

    if (terminalizingGenerationId === g.generationId) return false;

    if (generationIsStopRequested(g.generationId)) phase = 'stopped';
    if (generationStartPromiseId === g.generationId && generationStartPromise) {
        try { await generationStartPromise; } catch { /* ignore */ }
    }

    terminalizingGenerationId = g.generationId;
    clearGenerationStreamWork(g.generationId);

    // One terminal opId for this entire logical termination, including the
    // scheduled retries below.
    const terminalOpId = newId();

    try {
        if (streamInFlightPromise) {
            try { await Promise.race([streamInFlightPromise, sleep(2500)]); } catch { /* ignore */ }
        }

        await sleep(60);

        if (!localGenerationMatches(g.generationId, scopeAtGeneration)) return false;

        const snapshot = nativeScopeStable(scopeAtGeneration)
            ? syncSnapshot(durableSnapshot())
            : clone(localGenerationLastSnapshot || serverState?.snapshot || localGenerationBaseSnapshot || { messages: [], metadata: {} });

        const result = await terminateGenerationOnServer(g, scopeAtGeneration, phase, snapshot, terminalOpId);
        const stillSameLocal = localGenerationMatches(g.generationId, scopeAtGeneration);

        if (result.state) {
            if (currentScopeGuard(epochAtGeneration) || makeScopeKey(currentScope) === makeScopeKey(scopeAtGeneration)) {
                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
            }
        }

        if (result.success) {
            rememberTerminatedGeneration(g.generationId);
            if (stillSameLocal) clearLocalDirty(scopeAtGeneration);

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

        // Do not drop localGeneration on a failed terminal POST; the lease
        // state enables a safe retry and prevents a phantom server lease.
        terminalizingGenerationId = null;
        generationTerminalPhase = phase;
        scheduleTerminalRetry(g.generationId, phase, TERMINAL_RETRY_MS);
        updateGenerationUi();
        return false;
    } catch (error) {
        terminalizingGenerationId = null;
        generationTerminalPhase = phase;
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

        try { bc?.close?.(); } catch { /* ignore */ }
        bc = 'BroadcastChannel' in window ? new BroadcastChannel(BC_NAME) : null;

        bc?.addEventListener('message', message => {
            const data = message.data;
            if (data?.scopeKey !== scopeKeyValue) return;

            if (data?.kind === 'state' && currentScope) {
                resyncCurrentScope().catch(error => warn('BroadcastChannel state resync failed', error));
                return;
            }

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
                    const previousEnabled = !!settings.enabled;
                    settings = { ...DEFAULT_SETTINGS, ...incoming };
                    updateSettingsControls();

                    if (previousEnabled !== !!settings.enabled) {
                        if (settings.enabled) onEnable().catch(error => warn('storage-driven enable failed', error));
                        else onDisable().catch(error => warn('storage-driven disable failed', error));
                    } else if (settings.enabled && settings.autoConnect) {
                        updateGenerationUi();
                    }
                } catch { /* ignore invalid storage */ }
            };
            window.addEventListener('storage', storageHandler);
        }

        await negotiateClientId();
        await mountSettings();

        // Let SillyTavern own startup chat restoration.
        await sleep(250);
        refreshLiveContext();
    } finally {
        activationInProgress = false;
    }

    wireEvents();
    wireUiGuards();
    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

    safeSetTimer(() => {
        switchScope('post-activate').catch(error => warn('post-activate scope check failed', error));
    }, 900);

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
