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
const LAST_SCOPE_KEY = 'multi-client-sync-last-scope-v2';
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

// clientId identifies this tab/session. It must NOT live in localStorage,
// otherwise two tabs on the same browser look like the same MCS client.
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
let streamTimer = null;
let streamInFlight = false;
let streamInFlightPromise = null;
let remoteRenderTimer = null;
let lastStreamSentAt = 0;
let pendingStream = null;
let terminalizingGenerationId = null;
let scopeRetryTimer = null;
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
const registeredEventHandlers = [];
const registeredUiHandlers = [];
let heartbeatTimer = null;
let generationHeartbeatTimer = null;
let sendLockReason = '';
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
let lastRemoteStreamSeq = 0;
let lastSseEventId = 0;
let generationHeartbeatFailures = 0;
let generationHeartbeatInFlight = null;
let generationMismatchSince = 0;
let generationClaimedThisPage = false;
let generationClaimInFlightId = null;
let lastTerminatedGenerationId = null;
let streamInFlightSeq = 0;
let streamRetryTimer = null;
let resyncChain = Promise.resolve();
let queueFlushChain = Promise.resolve();

// Dirty-state tracking prevents a freshly reloaded/stale tab from reintroducing
// an old in-memory chat into an authoritative server snapshot.
let localDirty = false;
let localDirtyScopeKey = '';
let streamCaptureTimer = null;
let generationTerminalPhase = null;

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
    } catch {
        /* ignore */
    }
    const value = crypto.randomUUID();
    try { localStorage.setItem(key, value); } catch { /* ignore */ }
    return value;
}

function loadSessionId(key) {
    try {
        const saved = sessionStorage.getItem(key);
        if (saved && /^[A-Za-z0-9._~:-]{1,240}$/.test(saved)) return saved;
    } catch {
        /* ignore */
    }
    const value = crypto.randomUUID();
    try { sessionStorage.setItem(key, value); } catch { /* ignore */ }
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

function syncEnabled() {
    return !!settings.enabled && !!(settings.syncMessages || settings.syncMetadata);
}

function generationLeaseExpired(generation, graceMs = 0) {
    const leaseUntil = Number(generation?.leaseUntil || 0);
    return !!leaseUntil && leaseUntil <= Date.now() - Math.max(0, Number(graceMs) || 0);
}

function generationActive(generation) {
    return !!generation && !generationLeaseExpired(generation);
}

function localGenerationMatches(generationId, scope = null) {
    if (!localGeneration || localGeneration.generationId !== generationId) return false;
    if (scope && makeScopeKey(localGenerationScope) !== makeScopeKey(scope)) return false;
    return true;
}

function readLastScope() {
    try {
        const raw = sessionStorage.getItem(LAST_SCOPE_KEY);
        if (!raw) return null;
        const value = JSON.parse(raw);
        if (!value || typeof value !== 'object') return null;
        if (!value.kind || !value.ownerId || !value.chatId) return null;
        return {
            kind: String(value.kind),
            ownerId: String(value.ownerId),
            chatId: String(value.chatId),
            branchId: value.branchId ? String(value.branchId) : '',
        };
    } catch {
        return null;
    }
}

function writeLastScope(scope) {
    if (!scope) return;
    try {
        sessionStorage.setItem(LAST_SCOPE_KEY, JSON.stringify({
            kind: String(scope.kind || ''),
            ownerId: String(scope.ownerId || ''),
            chatId: String(scope.chatId || ''),
            branchId: String(scope.branchId || ''),
            tabId,
            savedAt: Date.now(),
        }));
    } catch {
        /* ignore */
    }
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
            const base = legacyMessageId(message, index, occurrences.get(legacyMessageId(message, index, 0)) || 0);
            let candidate = base;
            let suffix = 0;
            while (seen.has(candidate)) {
                suffix += 1;
                candidate = `${base}-${suffix}`;
            }
            id = candidate;
            occurrences.set(base, suffix);
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
    const metadata = clone(ctx?.chatMetadata || {});
    return { messages, metadata };
}

function syncSnapshot(snapshot) {
    const normalized = normalizeSnapshot(snapshot);
    return {
        messages: settings.syncMessages
            ? clone(normalized.messages)
            : clone(serverState?.snapshot?.messages || durableMessages({ persistIds: false })),
        metadata: settings.syncMetadata
            ? clone(normalized.metadata)
            : clone(serverState?.snapshot?.metadata || ctx?.chatMetadata || {}),
    };
}

function incomingSnapshot(snapshot) {
    const remote = normalizeSnapshot(snapshot);
    return {
        messages: settings.syncMessages ? clone(remote.messages) : clone(durableMessages({ persistIds: false })),
        metadata: settings.syncMetadata ? clone(remote.metadata) : clone(ctx?.chatMetadata || {}),
    };
}







function normalizeSnapshot(snapshot) {
    if (!snapshot || !Array.isArray(snapshot.messages)) return { messages: [], metadata: {} };
    const out = {
        messages: clone(snapshot.messages),
        metadata: safeObject(snapshot.metadata || {}),
    };
    ensureMessageIds(out.messages);
    return out;
}

function refreshLiveContext() {
    try {
        const fresh = SillyTavern?.getContext?.();
        if (fresh) ctx = fresh;
    } catch {
        /* keep the last usable context */
    }
    return ctx;
}

function getContextChatSources() {
    const live = refreshLiveContext();
    const selectedChat = document.querySelector('#selected_chat_pole')?.value;
    let currentChatId = '';
    let contextChatId = '';

    try {
        if (typeof live?.getCurrentChatId === 'function') {
            currentChatId = String(live.getCurrentChatId() || '').trim();
        }
    } catch {
        /* ignore */
    }

    if (live?.chatId) contextChatId = String(live.chatId).trim();

    return {
        selectedChat: typeof selectedChat === 'string' ? selectedChat.trim() : '',
        currentChatId,
        contextChatId,
    };
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
    } catch {
        /* ignore */
    }

    const contextFieldChatId = ctx.chatId ? String(ctx.chatId).trim() : '';
    const selectedChat = typeof document?.querySelector === 'function'
        ? String(document.querySelector('#selected_chat_pole')?.value || '').trim()
        : '';

    let chatId = '';
    if (isGroup) {
        chatId = contextChatId || contextFieldChatId || '';
    } else {
        // getCurrentChatId()/ctx.chatId are the authoritative native values.
        // The DOM selector can lag behind during ST chat loading.
        chatId = contextChatId || contextFieldChatId || selectedChat;
    }

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
    const scope = {
        kind: isGroup ? 'group' : 'character',
        ownerId,
        chatId,
        branchId,
    };

    log('[MCS] resolved scope:', scope);
    return scope;
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
            // Deterministic tie-breaker: only the lexicographically larger tab
            // rotates the duplicated session client ID.
            if (String(tabId) < String(data.tabId)) {
                finish();
                return;
            }
            clientId = crypto.randomUUID();
            try { sessionStorage.setItem(CLIENT_KEY, clientId); } catch { /* ignore */ }
            finish();
        };
        const timer = setTimeout(finish, 80);
        bc.addEventListener('message', onMessage);
        try { bc.postMessage({ kind: 'client-hello', clientId, deviceId, tabId }); } catch { finish(); }
    });
}

async function waitForNativeScope(expectedScope, timeoutMs = 2000, intervalMs = 75) {
    const deadline = Date.now() + Math.max(0, Number(timeoutMs) || 0);
    while (Date.now() <= deadline) {
        refreshLiveContext();
        if (currentScope && makeScopeKey(currentScope) === makeScopeKey(expectedScope) && nativeScopeStable(expectedScope)) return true;
        if (Date.now() >= deadline) break;
        await sleep(intervalMs);
    }
    return false;
}

function clearGenerationTerminalTimer() {
    if (generationTerminalTimer) clearTimeout(generationTerminalTimer);
    generationTerminalTimer = null;
}

async function maybeRestoreLastNativeScope() {
    const saved = readLastScope();
    if (!saved || !ctx) return false;

    refreshLiveContext();
    let current = scopeFromContext();
    if (current && makeScopeKey(current) === makeScopeKey(saved)) return false;

    // This scope is stored in sessionStorage, so it belongs to this browser tab.
    // ST's active-character setting is shared across tabs, therefore the per-tab
    // saved scope is preferred during activation/reload.

    const deadline = Date.now() + 8_000;
    while (Date.now() < deadline) {
        refreshLiveContext();
        current = scopeFromContext();
        if (current && makeScopeKey(current) === makeScopeKey(saved)) return false;

        if (saved.kind === 'group') {
            if (Array.isArray(ctx?.groups) && ctx.groups.length) break;
        } else if (Array.isArray(ctx?.characters) && ctx.characters.length) {
            break;
        }
        await sleep(100);
    }

    // Re-check before making any native selection. Another tab may have caused
    // ST's shared character state to settle on a real context meanwhile.
    refreshLiveContext();
    current = scopeFromContext();
    if (current && makeScopeKey(current) !== makeScopeKey(saved) && String(ctx?.name2 || '').trim().toLowerCase() !== 'assistant') {
        return false;
    }

    try {
        nativeRestoreInProgress = true;

        if (saved.kind === 'group') {
            const groupId = saved.ownerId.startsWith('group:') ? saved.ownerId.slice(6) : saved.ownerId;
            const group = Array.isArray(ctx?.groups)
                ? ctx.groups.find(item => String(item?.id) === String(groupId))
                : null;
            if (!group || typeof ctx?.openGroupChat !== 'function') return false;
            await ctx.openGroupChat(groupId, saved.chatId);
        } else {
            const desiredOwner = String(saved.ownerId);
            const index = Array.isArray(ctx?.characters)
                ? ctx.characters.findIndex(character =>
                    String(character?.avatar || '') === desiredOwner ||
                    String(character?.name || '') === desiredOwner,
                )
                : -1;

            if (index < 0) return false;
            if (typeof ctx?.selectCharacterById !== 'function' || typeof ctx?.openCharacterChat !== 'function') return false;
            await ctx.selectCharacterById(index, { switchMenu: false });
            await ctx.openCharacterChat(saved.chatId);
        }

        const convergeDeadline = Date.now() + 6_000;
        while (Date.now() < convergeDeadline) {
            await sleep(100);
            const restored = scopeFromContext();
            if (restored && makeScopeKey(restored) === makeScopeKey(saved)) {
                writeLastScope(restored);
                log('[MCS] restored last native scope:', restored);
                return true;
            }
        }

        log('[MCS] native scope restore did not converge:', { saved, current: scopeFromContext() });
        return false;
    } catch (error) {
        warn('native scope restore failed', error);
        return false;
    } finally {
        nativeRestoreInProgress = false;
    }
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
                if (!store.indexNames.contains('scopeKey')) store.createIndex('scopeKey', 'scopeKey', { unique: false });
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
            req.onsuccess = () => finish(null, req.result.sort((a, b) => a.createdAt - b.createdAt));
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









async function api(path, method = 'GET', body = undefined, query = '', options = {}) {
    const headers = {
        ...(ctx?.getRequestHeaders?.() || { 'Content-Type': 'application/json' }),
    };
    if (method !== 'GET') headers['Content-Type'] = 'application/json';

    const response = await fetch(`${PLUGIN_BASE}${path}${query}`, {
        method,
        headers,
        body: body === undefined ? undefined : JSON.stringify(body),
        credentials: 'same-origin',
        cache: 'no-cache',
        signal: options.signal,
        keepalive: !!options.keepalive,
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
        else if (/^Waiting|^Starting/.test(text)) dot.classList.add('mcs-warning');
        else if (/^Offline|^Reconnecting|^Protocol mismatch/.test(text)) dot.classList.add('mcs-disconnected');
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
            if (el.dataset.mcsLocked !== '1') el.dataset.mcsPrevDisabled = el.disabled ? '1' : '0';
            el.dataset.mcsLocked = '1';
            el.title = reason;
            el.classList.add('disabled');
            if ('disabled' in el) el.disabled = true;
        } else if (el.dataset.mcsLocked === '1') {
            delete el.dataset.mcsLocked;
            const wasDisabled = el.dataset.mcsPrevDisabled === '1';
            delete el.dataset.mcsPrevDisabled;
            if ('disabled' in el) el.disabled = wasDisabled;
            el.removeAttribute('title');
            el.classList.remove('disabled');
        }
    }
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
function generationIsMine(generation) {
    return !!generation && generation.clientId === clientId && generation.deviceId === deviceId;
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
    streamInFlightSeq = 0;
    localStreamMessageId = null;
    localStreamMessageIndex = null;
    generationTerminalPhase = null;
    if (streamTimer) clearTimeout(streamTimer);
    if (streamRetryTimer) clearTimeout(streamRetryTimer);
    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);
    streamTimer = null;
    streamRetryTimer = null;
    streamCaptureTimer = null;
    pendingStream = null;
    streamInFlight = false;
    terminalizingGenerationId = null;
    stopGenerationHeartbeat();
}

function clearRemoteStreamState() {
    if (remoteRenderTimer) clearTimeout(remoteRenderTimer);
    remoteRenderTimer = null;
    pendingRemoteStream = null;
    remoteGenerationId = null;
    lastRemoteStreamSeq = 0;
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
    return messages.map((message, index) => {
        const durableId = messageId(message);
        if (durableId) return `id:${durableId}`;

        const base = messageStableKey(message);
        const occurrence = counts.get(base) || 0;
        counts.set(base, occurrence + 1);
        return `${base}#${occurrence}`;
    });
}

function comparableMessage(message) {
    const copy = clone(message);
    if (copy?.extra?.multi_client_sync) {
        delete copy.extra.multi_client_sync;
        if (Object.keys(copy.extra).length === 0) delete copy.extra;
    }
    return copy;
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

    for (let ai = 0; ai < arrays.length; ai += 1) {
        for (const id of arrayIdentities[ai]) {
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
    const ids = new Set([...bm.keys(), ...lm.keys(), ...rm.keys()]);
    const chosen = [];

    for (const id of ids) {
        const bv = bm.get(id);
        const lv = lm.get(id);
        const rv = rm.get(id);
        let value = null;

        if (!lv && !rv) {
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
            // Both changed the same logical message: prefer server/remote data.
            value = rv;
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
        }
    }

    return {
        messages: orderMergedMessages(b.messages, l.messages, r.messages, chosen),
        metadata: mergeMetadata(b.metadata, l.metadata, r.metadata),
    };
}

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

        // Confirm that ST still has the native file for this exact scope.
        if (expectedScope.kind === 'group') {
            const groupId = String(expectedScope.ownerId || '').replace(/^group:/, '');
            const group = Array.isArray(ctx.groups)
                ? ctx.groups.find(item => String(item?.id) === groupId)
                : null;
            if (String(group?.chat_id || '').trim() !== chatId) return false;
        } else {
            const character = Array.isArray(ctx.characters)
                ? ctx.characters[String(ctx.characterId ?? '')]
                : null;
            if (String(character?.chat || '').trim() !== chatId) return false;
        }

        // Group chats cannot use ST's character-chat save endpoint. MCS already
        // persists the authoritative group snapshot on the server.
        if (expectedScope.kind === 'group') return false;

        // Confirm the same native scope again to reduce the shared-active-character
        // race on multi-tab reloads.
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
    nativeSaveChain = run.catch(error => warn('native save chain failed', error));
    return run;
}
async function applySnapshotNow(snapshot, { save = false, render = true, expectedScope = currentScope, clearDirty = true, allowDuringGeneration = false } = {}) {
    const normalized = normalizeSnapshot(snapshot);
    if (!ctx || !expectedScope || !nativeScopeStable(expectedScope)) {
        log('[MCS] refused snapshot apply because native scope is not stable', expectedScope);
        return false;
    }

    const expectedKey = makeScopeKey(expectedScope);
    const epochAtStart = scopeEpoch;
    if (!allowDuringGeneration && (localGeneration || generationActive(serverState?.generation))) {
        log('[MCS] refused snapshot apply during active generation');
        return false;
    }

    applyingRemoteDepth += 1;
    try {
        refreshLiveContext();
        if (!currentScope || makeScopeKey(currentScope) !== expectedKey || !nativeScopeStable(expectedScope)) return false;

        if (Array.isArray(ctx.chat)) {
            ctx.chat.splice(0, ctx.chat.length, ...clone(normalized.messages));
        }

        if (ctx.chatMetadata && typeof ctx.chatMetadata === 'object') {
            for (const key of Object.keys(ctx.chatMetadata)) delete ctx.chatMetadata[key];
            Object.assign(ctx.chatMetadata, clone(normalized.metadata));
        }

        if (render) {
            try { ctx.printMessages?.(); }
            catch (error) { log('printMessages failed', error); }
        }

        if (save && epochAtStart === scopeEpoch && !nativeRestoreInProgress && nativeScopeStable(expectedScope) && makeScopeKey(currentScope) === expectedKey) {
            await safeNativeSave(expectedScope);
        }
        if (clearDirty) clearLocalDirty(expectedScope);
        return true;
    } finally {
        applyingRemoteDepth -= 1;
    }
}
function applySnapshot(snapshot, options = {}) {
    const run = snapshotMutationChain.then(() => applySnapshotNow(snapshot, options));
    snapshotMutationChain = run.catch(error => warn('snapshot mutation failed', error));
    return run;
}

async function ensureIdsPersisted(expectedScope = currentScope) {
    refreshLiveContext();
    if (!ctx?.chat || !expectedScope || !nativeScopeStable(expectedScope)) return false;
    const changed = ensureMessageIds(ctx.chat);
    if (changed) await safeNativeSave(expectedScope);
    return true;
}





async function enqueueSnapshot(snapshot, baseRev, baseSnap, scope = currentScope, kind = 'snapshot', generationId = null) {
    if (!syncEnabled() || !scope) return;
    const scopeKey = makeScopeKey(scope);
    if (!scopeKey) return;

    const row = {
        id: newId(),
        scopeKey,
        createdAt: Date.now(),
        kind,
        generationId: generationId ? String(generationId) : null,
        baseRevision: Number(baseRev || 0),
        baseSnapshot: clone(baseSnap || { messages: [], metadata: {} }),
        snapshot: clone(snapshot),
    };

    await idbPut(row);
    const rows = await idbList(scopeKey);
    if (rows.length > MAX_QUEUE) {
        for (const old of rows.slice(0, rows.length - MAX_QUEUE)) await idbDelete(old.id);
    }
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



async function publishLocalSnapshot(snapshot = durableSnapshot(), { allowDuringGeneration = false, scope = currentScope } = {}) {
    if (!scope || !settings.enabled || !syncEnabled()) return false;
    if (!nativeScopeStable(scope)) return false;

    if (localGeneration && !allowDuringGeneration) return false;
    if (localGeneration && allowDuringGeneration && localGeneration.phase === 'streaming') return false;
    if (serverState?.generation && !localGeneration) return false;
    if (deepEqual(snapshot, serverState?.snapshot)) {
        clearLocalDirty(scope);
        return true;
    }

    const scopeAtPublish = clone(scope);
    const scopeKeyAtPublish = makeScopeKey(scopeAtPublish);
    const base = clone(baseSnapshot || { messages: [], metadata: {} });
    const revision = Number(serverState?.revision || 0);

    try {
        const result = await sendSnapshotDirect(snapshot, revision, newId(), scopeAtPublish);
        if (scopeKeyValue !== scopeKeyAtPublish || !currentScope || makeScopeKey(currentScope) !== scopeKeyAtPublish) return false;
        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        clearLocalDirty(scopeAtPublish);
        writeLastScope(scopeAtPublish);
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

            // Do not native-save an uncommitted merge. Commit to the server first.
            const retryBase = Number(remoteState.revision);
            try {
                const result = await sendSnapshotDirect(merged, retryBase, newId(), scopeAtPublish);
                if (scopeKeyValue !== scopeKeyAtPublish) return false;
                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
                const applied = await applySnapshot(merged, { save: true, render: true, expectedScope: scopeAtPublish, clearDirty: false });
                if (!applied) return false;
                clearLocalDirty(scopeAtPublish);
                writeLastScope(scopeAtPublish);
                broadcastWake('state');
                return true;
            } catch (retryError) {
                if (retryError?.status === 409 && retryError?.payload?.error === 'generation_active') return false;
                await enqueueSnapshot(merged, retryError?.payload?.state?.revision ?? retryBase, retryError?.payload?.state?.snapshot ?? remoteState.snapshot, scopeAtPublish);
                return false;
            }
        }

        if (localGeneration && allowDuringGeneration) return false;
        await enqueueSnapshot(snapshot, revision, base, scopeAtPublish);
        return false;
    }
}
async function flushQueueInternal() {
    if (!currentScope || !settings.enabled || !syncEnabled() || !scopeKeyValue) return;
    if (!nativeScopeStable(currentScope)) return;
    if (localGeneration || serverState?.generation) return;

    const scopeAtFlush = clone(currentScope);
    const scopeKeyAtFlush = makeScopeKey(scopeAtFlush);
    const rows = await idbList(scopeKeyAtFlush);

    for (const row of rows) {
        if (!currentScope || scopeKeyValue !== scopeKeyAtFlush || !nativeScopeStable(scopeAtFlush)) return;
        if (localGeneration || serverState?.generation) return;

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

            const result = await sendSnapshotDirect(nextSnapshot, nextRevision, row.id, scopeAtFlush);
            if (scopeKeyValue !== scopeKeyAtFlush) return;

            serverState = result.state;
            baseSnapshot = clone(result.state.snapshot);
            await idbDelete(row.id);

            // The committed server snapshot is now safe to materialize locally.
            const applied = await applySnapshot(incomingSnapshot(result.state.snapshot), {
                save: true,
                render: true,
                expectedScope: scopeAtFlush,
            });
            if (!applied) return;
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
            return;
        }
    }
}
function flushQueue() {
    const run = queueFlushChain.then(() => flushQueueInternal());
    queueFlushChain = run.catch(error => warn('queue flush failed', error));
    return run;
}

function broadcastWake(kind) {
    try {
        bc?.postMessage({ kind, scopeKey: scopeKeyValue, at: Date.now(), clientId, deviceId, tabId });
    } catch {
        /* ignore */
    }
}

async function openScope(epoch) {
    if (!settings.enabled || !settings.autoConnect || !currentScope) return;
    const scopeAtJoin = clone(currentScope);

    if (!nativeScopeStable(scopeAtJoin)) {
        statusText('Waiting for active chat…');
        if (!scopeRetryTimer && !nativeRestoreInProgress) {
            scopeRetryTimer = setTimeout(() => {
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
        }, '', { signal: joinController.signal });

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
        lastTerminatedGenerationId = null;
        remoteGenerationId = null;
        lastRemoteStreamSeq = -1;
        generationMismatchSince = 0;
        writeLastScope(scopeAtJoin);

        // A page reload cannot continue ST's in-flight request. A generation
        // owned by this client from a previous page is therefore stale. Clear it
        // before showing the scope as locked. Capture its ID before replacing state
        // so late SSE replay cannot resurrect it.
        const staleOwnedGenerationId = serverState?.generation && generationIsStaleOwned(serverState.generation)
            ? serverState.generation.generationId
            : null;
        if (staleOwnedGenerationId && generationClaimInFlightId !== staleOwnedGenerationId) {
            lastTerminatedGenerationId = staleOwnedGenerationId;
            try {
                const cleared = await api('/generation/terminal', 'POST', {
                    scope: scopeAtJoin,
                    clientId,
                    deviceId,
                    generationId: staleOwnedGenerationId,
                    phase: 'stopped',
                    snapshot: clone(serverState.snapshot),
                });
                if (currentScopeGuard(epoch)) {
                    serverState = cleared.state;
                    baseSnapshot = clone(cleared.state.snapshot);
                    lastTerminatedGenerationId = staleOwnedGenerationId;
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

        // Existing server state is authoritative on first join. Only queued
        // offline mutations are merged back in. This prevents a stale reload
        // from recreating/deleting history on the server.
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
        }
        if (!queued.length) clearLocalDirty(scopeAtJoin);

        connectSse(epoch);
        startHeartbeats(epoch);

        if (serverState.generation?.message && !generationIsMine(serverState.generation)) {
            remoteGenerationId = serverState.generation.generationId;
            lastRemoteStreamSeq = Number(serverState.generation.seq || 0);
            pendingRemoteStream = {
                message: clone(serverState.generation.message),
                messageIndex: Number.isInteger(serverState.generation.messageIndex) ? serverState.generation.messageIndex : null,
                generationId: serverState.generation.generationId,
                seq: Number(serverState.generation.seq || 0),
            };
            scheduleRemoteRender();
        }

        await flushQueue();
        updateGenerationUi();
        statusText(`Connected · rev ${serverState.revision}`);
    } catch (error) {
        if (joinAbortController === joinController) joinAbortController = null;
        if (error?.name === 'AbortError') return;
        warn('join failed', error);
        statusText(`Offline: ${error?.message || 'connection failed'}`);
        if (!currentScopeGuard(epoch) || scopeRetryTimer || nativeRestoreInProgress) return;
        scopeRetryTimer = setTimeout(() => {
            scopeRetryTimer = null;
            if (currentScopeGuard(epoch)) openScope(epoch).catch(retryError => warn('scope retry failed', retryError));
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
    const query = `?scope=${encodeURIComponent(encodeScope(currentScope))}&clientId=${encodeURIComponent(clientId)}&deviceId=${encodeURIComponent(deviceId)}&lastEventId=${encodeURIComponent(String(lastSseEventId || 0))}`;
    const source = new EventSource(`${PLUGIN_BASE}/events${query}`, { withCredentials: true });
    eventSource = source;

    const handle = (type, fn) => {
        source.addEventListener(type, event => {
            if (!currentScopeGuard(epoch) || localSseEpoch !== sseEpoch) return;

            const eventId = Number(event.lastEventId || 0);
            if (eventId > 0) {
                if (eventId <= lastSseEventId) return;
                lastSseEventId = eventId;
            }

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
    };
}

function handleServerHello(data) {
    if (data.protocol !== PROTOCOL || data.schema !== SCHEMA) {
        statusText(`Protocol mismatch (${data.protocol}/${data.schema})`);
        return;
    }

    const incomingGeneration = clone(data.generation || null);
    const incomingGenerationId = incomingGeneration?.generationId || null;

    // A terminal event is authoritative for this generation. SSE replay can
    // arrive out of order and must not resurrect an old lease/stream.
    if (incomingGenerationId && incomingGenerationId === lastTerminatedGenerationId) {
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

    if (generation?.generationId && generation.generationId !== lastTerminatedGenerationId) {
        // A genuinely new generation supersedes the previous terminal marker.
        lastTerminatedGenerationId = null;
    }

    if (generationIsMine(generation)) {
        const claimPending = generationClaimInFlightId === generation.generationId;
        if (generationClaimedThisPage || claimPending) {
            if (generationClaimedThisPage && localGeneration?.generationId === generation.generationId) {
                localGeneration = clone(generation);
            }
            if (claimPending && ['started', 'streaming'].includes(generation.phase)) {
                generationServerReadyId = generation.generationId;
            }
        } else {
            // Same client/device lease from another page is stale. Reconcile via
            // /state instead of stopping the native LLM from an SSE callback.
            resyncCurrentScope(scopeEpoch).catch(error => warn('stale generation hello resync failed', error));
        }
    } else if (generation) {
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
    } else {
        clearRemoteStreamState();
    }

    updateGenerationUi();

    if (generation && generationLeaseExpired(generation)) {
        resyncCurrentScope(scopeEpoch).catch(error => warn('expired generation resync failed', error));
    }
}
function handleSnapshotEvent(data) {
    const run = stateApplyChain.then(async () => {
        const revision = Number(data?.revision || 0);
        if (!revision || revision <= Number(serverState?.revision || 0)) return;
        if (!currentScope || !nativeScopeStable(currentScope)) return;

        const scopeAtEvent = clone(currentScope);
        const remote = incomingSnapshot(data.snapshot);
        const incomingGenerationId = String(data?.generationId || '');
        const knownBase = clone(
            baseSnapshot ||
            serverState?.snapshot ||
            { messages: [], metadata: {} },
        );
        const local = syncSnapshot(durableSnapshot());
        const dirty = isLocalDirty(scopeAtEvent);

        serverState = { ...(serverState || {}), revision, snapshot: clone(data.snapshot) };
        baseSnapshot = clone(data.snapshot);

        if (serverState?.generation || incomingGenerationId) {
            updateGenerationUi();
            return;
        }

        if (data.sourceClientId === clientId) {
            clearLocalDirty(scopeAtEvent);
            updateGenerationUi();
            return;
        }

        let appliedSnapshot = remote;
        if (dirty) appliedSnapshot = mergeSnapshots(knownBase, local, remote);

        if (!deepEqual(local, appliedSnapshot)) {
            const applied = await applySnapshot(appliedSnapshot, {
                save: true,
                render: true,
                expectedScope: scopeAtEvent,
                clearDirty: false,
            });
            if (!applied) return;
        }

        if (!deepEqual(appliedSnapshot, remote)) {
            if (!nativeScopeStable(scopeAtEvent) || scopeKeyValue !== makeScopeKey(scopeAtEvent)) return;
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
                }
            }
        } else {
            clearLocalDirty(scopeAtEvent);
        }

        broadcastWake('state');
        updateGenerationUi();
    });

    stateApplyChain = run.catch(error => warn('remote snapshot apply failed', error));
    return run;
}
function handleGenerationEvent(data) {
    const generation = clone(data?.generation || null);
    if (!generation || !currentScope || !generation.generationId) return;
    if (generation.generationId === lastTerminatedGenerationId) return;

    const eventRevision = Number(data?.revision || 0);
    if (eventRevision && eventRevision < Number(serverState?.revision || 0)) return;

    const oldGeneration = serverState?.generation || null;
    const oldTime = Number(oldGeneration?.startedAt || oldGeneration?.claimedAt || 0);
    const incomingTime = Number(generation?.startedAt || generation?.claimedAt || 0);
    const sameGeneration = oldGeneration?.generationId === generation.generationId;

    if (oldGeneration && !sameGeneration && generationActive(oldGeneration) && incomingTime && oldTime && incomingTime < oldTime) return;

    serverState = {
        ...(serverState || {}),
        revision: Math.max(Number(serverState?.revision || 0), eventRevision),
        generation,
    };

    if (generationIsMine(generation)) {
        const claimPending = generationClaimInFlightId === generation.generationId;
        if (claimPending && !generationClaimedThisPage) {
            // Claim SSE may beat the POST response. Keep the server state but do
            // not adopt/clear it as if it belonged to a previous page.
            updateGenerationUi();
            return;
        }

        if (generationClaimedThisPage) {
            if (!localGeneration || localGeneration.generationId === generation.generationId) {
                localGeneration = clone(generation);
                localGenerationScope = localGenerationScope || clone(currentScope);
                localGenerationEpoch = scopeEpoch;
                localGenerationBaseSnapshot = localGenerationBaseSnapshot || clone(baseSnapshot || serverState.snapshot || { messages: [], metadata: {} });
                localGenerationLastSnapshot = localGenerationLastSnapshot || clone(serverState.snapshot || baseSnapshot || { messages: [], metadata: {} });
                if (['started', 'streaming'].includes(generation.phase)) generationServerReadyId = generation.generationId;
            }
        } else {
            resyncCurrentScope(scopeEpoch).catch(error => warn('stale generation event resync failed', error));
        }
    } else {
        if (remoteGenerationId !== generation.generationId) {
            remoteGenerationId = generation.generationId;
            lastRemoteStreamSeq = -1;
        }
        const seq = Number(generation.seq || 0);
        if (seq <= lastRemoteStreamSeq && sameGeneration) {
            updateGenerationUi();
            return;
        }
        lastRemoteStreamSeq = Math.max(lastRemoteStreamSeq, seq);
        if (generation.message) {
            pendingRemoteStream = {
                message: clone(generation.message),
                messageIndex: Number.isInteger(generation.messageIndex) ? generation.messageIndex : null,
                generationId: generation.generationId,
                seq,
            };
            scheduleRemoteRender();
        }
    }

    updateGenerationUi();
}
async function handleGenerationRecovered(data) {
    if (!currentScope) return;

    const epoch = scopeEpoch;
    const scopeAtRecovery = clone(currentScope);

    // The recovery SSE event intentionally has no generationId. It can be an old
    // replay arriving after a newer generation was created, so never clear a live
    // generation based on the event alone. Ask the server for authoritative state.
    try {
        const result = await api('/state', 'POST', {
            scope: scopeAtRecovery,
            clientId,
            deviceId,
        });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtRecovery)) return;

        const authoritative = result.state || null;
        const generation = authoritative?.generation || null;
        const localId = localGeneration?.generationId || null;

        serverState = authoritative;
        baseSnapshot = clone(authoritative?.snapshot || baseSnapshot || { messages: [], metadata: {} });

        if (generation) {
            if (localId && generation.generationId === localId && generationIsMine(generation)) {
                // Our lease is still authoritative; the recovery event was stale.
                localGeneration = clone(generation);
                localGenerationScope = clone(scopeAtRecovery);
                localGenerationEpoch = epoch;
                if (['started', 'streaming'].includes(generation.phase)) generationServerReadyId = generation.generationId;
                generationMismatchSince = 0;
                updateGenerationUi();
                return;
            }

            // A different, live generation is authoritative. Do not abort a local
            // request from a stale recovery event; normal ownership reconciliation
            // will decide what to do.
            if (localGeneration && generation.generationId !== localId) {
                generationMismatchSince = generationMismatchSince || Date.now();
                updateGenerationUi();
                return;
            }

            clearRemoteStreamState();
            if (generation.message && !generationIsMine(generation)) {
                remoteGenerationId = generation.generationId;
                lastRemoteStreamSeq = Number(generation.seq || 0);
                pendingRemoteStream = {
                    message: clone(generation.message),
                    messageIndex: Number.isInteger(generation.messageIndex) ? generation.messageIndex : null,
                    generationId: generation.generationId,
                    seq: Number(generation.seq || 0),
                };
                scheduleRemoteRender();
            }
            updateGenerationUi();
            return;
        }

        if (localGeneration) {
            const lostId = localGeneration.generationId;
            try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            lastTerminatedGenerationId = lostId;
            clearLocalGenerationState();
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

        renderBanner('Generation was lost; chat was unlocked.');
        setTimeout(() => renderBanner(''), 1800);
        updateGenerationUi();
    } catch (error) {
        // Do not alter local generation state if authoritative confirmation fails.
        warn('generation recovery confirmation failed', error);
    }
}
function handleGenerationStreamEvent(data) {
    const g = data?.generation;
    if (!g || !g.generationId) return;
    if (g.generationId === lastTerminatedGenerationId) return;

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
            serverState = { ...(serverState || {}), generation: clone(g) };
            if (generationClaimedThisPage && localGeneration?.generationId === g.generationId) localGeneration = clone(g);
        }
        return;
    }

    if (remoteGenerationId !== g.generationId) {
        remoteGenerationId = g.generationId;
        lastRemoteStreamSeq = -1;
    }
    if (seq <= lastRemoteStreamSeq) return;
    const hadGap = seq > 0 && lastRemoteStreamSeq >= 0 && seq > lastRemoteStreamSeq + 1;
    if (hadGap) {
        resyncCurrentScope(scopeEpoch).catch(error => warn('stream gap resync failed', error));
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
function applyRemoteStreamNow(item) {
    if (!item || !ctx?.chat || !currentScope || !nativeScopeStable(currentScope)) return false;

    const g = serverState?.generation;
    if (!g || g.generationId !== item.generationId || generationIsMine(g)) return false;
    if (Number(item.seq || 0) < Number(lastRemoteStreamSeq || 0)) return false;

    applyingRemoteDepth += 1;
    try {
        const id = messageId(item.message);
        if (!id) return false;

        let index = ctx.chat.findIndex(message => messageId(message) === id);
        if (index < 0) {
            if (Number.isInteger(item.messageIndex) && item.messageIndex >= 0 && item.messageIndex <= ctx.chat.length) {
                index = item.messageIndex;
                ctx.chat.splice(index, 0, clone(item.message));
            } else {
                ctx.chat.push(clone(item.message));
                index = ctx.chat.length - 1;
            }
        } else {
            ctx.chat[index] = clone(item.message);
        }

        try {
            // Current ST context API expects the numeric message index here.
            ctx.updateMessageBlock?.(index, clone(ctx.chat[index]), { rerenderMessage: true });
        } catch {
            try { ctx.printMessages?.(); } catch { /* ignore */ }
        }
        return true;
    } finally {
        applyingRemoteDepth -= 1;
    }
}
function scheduleRemoteRender() {
    if (remoteRenderTimer) return;

    remoteRenderTimer = setTimeout(() => {
        remoteRenderTimer = null;
        const item = pendingRemoteStream;
        pendingRemoteStream = null;
        if (!item) return;

        const run = stateApplyChain.then(() => applyRemoteStreamNow(item));
        stateApplyChain = run.catch(error => warn('remote stream render failed', error));
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

    if (!generationId) return;
    if (revision && currentRevision && revision < currentRevision) return;
    if (serverState?.generation && serverState.generation.generationId !== generationId) return;
    if (generationId === lastTerminatedGenerationId) return;

    const scopeAtEvent = clone(currentScope);
    const hadLocalGeneration = !!localGeneration && localGeneration.generationId === generationId;
    const mine = !!terminalGeneration && generationIsMine(terminalGeneration) && hadLocalGeneration;
    const terminalSnapshot = incomingSnapshot(data.snapshot || serverState?.snapshot || { messages: [], metadata: {} });
    const knownBase = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });
    const dirty = !mine && isLocalDirty(scopeAtEvent);
    const local = !mine && dirty ? syncSnapshot(durableSnapshot()) : null;

    lastTerminatedGenerationId = generationId;
    serverState = {
        ...(serverState || {}),
        revision: Math.max(currentRevision, revision),
        snapshot: clone(data.snapshot || serverState?.snapshot || { messages: [], metadata: {} }),
        generation: null,
    };
    baseSnapshot = clone(serverState.snapshot);

    if (mine) {
        // ST already finalized the local assistant message. Do not overwrite it.
        clearLocalGenerationState();
        clearLocalDirty(scopeAtEvent);
    } else if (scopeAtEvent && nativeScopeStable(scopeAtEvent) && data?.snapshot) {
        let finalSnapshot = terminalSnapshot;
        if (dirty) finalSnapshot = mergeSnapshots(knownBase, local, terminalSnapshot);

        const applied = await applySnapshot(finalSnapshot, {
            save: true,
            render: true,
            expectedScope: scopeAtEvent,
            clearDirty: false,
            allowDuringGeneration: true,
        });

        if (applied) {
            if (!deepEqual(finalSnapshot, terminalSnapshot) && currentScopeGuard(scopeEpoch)) {
                try {
                    const committed = await sendSnapshotDirect(
                        finalSnapshot,
                        Number(serverState?.revision || 0),
                        newId(),
                        scopeAtEvent,
                    );
                    serverState = committed.state;
                    baseSnapshot = clone(committed.state.snapshot);
                } catch (error) {
                    if (error?.status === 409 && error?.payload?.state) {
                        serverState = error.payload.state;
                        baseSnapshot = clone(error.payload.state.snapshot);
                    } else {
                        await enqueueSnapshot(finalSnapshot, Number(serverState?.revision || 0), baseSnapshot, scopeAtEvent);
                    }
                }
            }
            clearLocalDirty(scopeAtEvent);
        }

        renderBanner('Generation finished in another client.');
        setTimeout(() => renderBanner(''), 1500);
    }

    pendingStream = null;
    clearRemoteStreamState();
    streamInFlight = false;
    streamInFlightSeq = 0;
    terminalizingGenerationId = null;
    updateGenerationUi();
    await flushQueue();
    if (!localGeneration) void switchScope('post-generation-terminal');
}
function updateGenerationUi() {
    const g = serverState?.generation;
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

    const mine = !!localGeneration && g.generationId === localGeneration.generationId && generationIsMine(g);
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
    generationHeartbeatFailures = 0;
    generationHeartbeatInFlight = null;
    generationMismatchSince = 0;
}

function startHeartbeats(epoch) {
    if (heartbeatTimer) clearInterval(heartbeatTimer);
    heartbeatTimer = setInterval(async () => {
        if (!currentScopeGuard(epoch) || !serverState) return;
        refreshLiveContext();
        const nativeStable = nativeScopeStable(currentScope);
        if (!nativeStable && !localGeneration) {
            await switchScope('heartbeat-context-mismatch');
            return;
        }

        const scopeAtHeartbeat = clone(currentScope);
        try {
            const result = await api('/heartbeat', 'POST', {
                scope: scopeAtHeartbeat,
                clientId,
                deviceId,
            });
            if (!currentScopeGuard(epoch)) return;

            const oldRevision = Number(serverState.revision || 0);
            const oldGenerationId = serverState.generation?.generationId || null;
            const newRevision = Number(result.revision || 0);
            const newGenerationId = result.generation?.generationId || null;

            serverState = {
                ...serverState,
                revision: Math.max(oldRevision, newRevision),
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
        }
    }, HEARTBEAT_MS);
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
        if (!nativeScopeStable(scopeAtGeneration)) {
            generationMismatchSince = generationMismatchSince || Date.now();
        } else {
            generationMismatchSince = 0;
        }

        const heartbeatRun = (async () => {
            try {
                const result = await api('/generation/heartbeat', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                    generationId,
                });

                if (!localGeneration || localGeneration.generationId !== generationId || !currentScopeGuard(epoch)) return;

                const stateGeneration = result.state?.generation || null;
                serverState = result.state;

                if (result.stopRequested || stateGeneration?.stopRequested) {
                    // Server explicitly requested a stop. This is intentional.
                    try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                    return;
                }

                if (!stateGeneration || stateGeneration.generationId !== generationId || !generationIsMine(stateGeneration)) {
                    // Confirm ownership loss once with the state endpoint before
                    // aborting the actual ST request. This prevents false aborts
                    // caused by a transient/reordered SSE update.
                    const confirm = await api('/state', 'POST', {
                        scope: scopeAtGeneration,
                        clientId,
                        deviceId,
                    }).catch(() => null);
                    const confirmed = confirm?.state?.generation || null;
                    if (confirmed && confirmed.generationId === generationId && generationIsMine(confirmed)) {
                        serverState = confirm.state;
                        localGeneration = clone(confirmed);
                        updateGenerationUi();
                        return;
                    }
                    // If membership was lost, rejoin rather than killing the LLM.
                    if (!confirmed && currentScopeGuard(epoch)) {
                        // Membership may have expired transiently. Rejoin without
                        // aborting the LLM; terminal recovery will reconcile if needed.
                        await openScope(epoch);
                        return;
                    }
                    if (confirmed?.generation && !generationIsMine(confirmed.generation)) {
                        generationMismatchSince = generationMismatchSince || Date.now();
                        if (Date.now() - generationMismatchSince < 3500) return;
                        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                        return;
                    }
                    return;
                }

                localGeneration = clone(stateGeneration);
                generationServerReadyId = ['started', 'streaming'].includes(stateGeneration.phase) ? generationId : generationServerReadyId;
                generationHeartbeatFailures = 0;
                updateGenerationUi();
            } catch (error) {
                generationHeartbeatFailures += 1;

                // Transport errors are never grounds to abort ST generation.
                if (error?.status === 409 && ['generation_not_owned', 'generation_expired'].includes(error?.payload?.error)) {
                    const immediate = error?.payload?.state || null;
                    if (immediate?.generation?.generationId === generationId && generationIsMine(immediate.generation)) {
                        serverState = immediate;
                        localGeneration = clone(immediate.generation);
                        generationMismatchSince = 0;
                        return;
                    }

                    let confirmed = null;
                    try {
                        const stateResult = await api('/state', 'POST', {
                            scope: scopeAtGeneration,
                            clientId,
                            deviceId,
                        });
                        confirmed = stateResult.state;
                    } catch {
                        confirmed = null;
                    }

                    if (!localGeneration || localGeneration.generationId !== generationId || !currentScopeGuard(epoch)) return;

                    if (confirmed?.generation?.generationId === generationId && generationIsMine(confirmed.generation)) {
                        serverState = confirmed;
                        localGeneration = clone(confirmed.generation);
                        generationMismatchSince = 0;
                        return;
                    }

                    if (confirmed?.generation && !generationIsMine(confirmed.generation) && generationActive(confirmed.generation)) {
                        generationMismatchSince = generationMismatchSince || Date.now();
                        if (Date.now() - generationMismatchSince < 3500) return;
                        // Confirmed different active owner: genuine conflict.
                        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                        return;
                    }

                    // No confirmed competing owner. Keep ST generation alive and let
                    // terminal recovery reconcile the final snapshot.
                    generationMismatchSince = generationMismatchSince || Date.now();
                    return;
                }

                if (error?.status === 403 && error?.payload?.error === 'not_member') {
                    await openScope(epoch);
                    return;
                }

                log('generation heartbeat failed; continuing local generation', error);
            } finally {
                generationHeartbeatInFlight = null;
            }
        })();

        generationHeartbeatInFlight = heartbeatRun;
        await heartbeatRun.catch(() => { /* handled above */ });
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

        const serverGeneration = result.state.generation || null;
        const remote = incomingSnapshot(result.state.snapshot);
        const dirty = isLocalDirty(scopeAtRequest);
        const local = syncSnapshot(durableSnapshot());
        const knownBase = clone(
            baseSnapshot ||
            serverState?.snapshot ||
            { messages: [], metadata: {} },
        );

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);

        if (localGeneration) {
            if (serverGeneration && serverGeneration.generationId === localGeneration.generationId && generationIsMine(serverGeneration)) {
                localGeneration = clone(serverGeneration);
                localGenerationScope = clone(scopeAtRequest);
                localGenerationEpoch = epoch;
                generationServerReadyId = ['started', 'streaming'].includes(serverGeneration.phase) ? serverGeneration.generationId : generationServerReadyId;
            } else {
                // One authoritative check is enough here; generation heartbeat
                // handles the transient network case. Do not immediately abort
                // just because an SSE/state response is briefly behind.
                if (generationMismatchSince === 0) generationMismatchSince = Date.now();
                if (Date.now() - generationMismatchSince > 3500 && !generationClaimInFlightId) {
                    try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                }
            }
        } else if (serverGeneration && generationIsMine(serverGeneration)) {
            if (!generationClaimedThisPage && generationClaimInFlightId !== serverGeneration.generationId) {
                // Stale previous-page ownership. Clean it without reviving it.
                const staleId = serverGeneration.generationId;
                lastTerminatedGenerationId = staleId;
                try {
                    const cleared = await api('/generation/terminal', 'POST', {
                        scope: scopeAtRequest,
                        clientId,
                        deviceId,
                        generationId: serverGeneration.generationId,
                        phase: 'stopped',
                        snapshot: clone(result.state.snapshot),
                    });
                    serverState = cleared.state;
                    baseSnapshot = clone(cleared.state.snapshot);
                    lastTerminatedGenerationId = serverGeneration.generationId;
                } catch (error) {
                    if (error?.status === 409 && error?.payload?.state) {
                        serverState = error.payload.state;
                        baseSnapshot = clone(error.payload.state.snapshot);
                        if (!error.payload.state.generation) lastTerminatedGenerationId = staleId;
                    }
                }
            }
        }

        const effectiveGeneration = serverState.generation || null;

        if (effectiveGeneration?.message && !generationIsMine(effectiveGeneration)) {
            remoteGenerationId = effectiveGeneration.generationId;
            lastRemoteStreamSeq = Number(effectiveGeneration.seq || 0);
            pendingRemoteStream = {
                message: clone(effectiveGeneration.message),
                messageIndex: Number.isInteger(effectiveGeneration.messageIndex) ? effectiveGeneration.messageIndex : null,
                generationId: effectiveGeneration.generationId,
                seq: Number(effectiveGeneration.seq || 0),
            };
            scheduleRemoteRender();
        }

        if (!effectiveGeneration && !localGeneration) {
            if (dirty) {
                const merged = mergeSnapshots(knownBase, local, remote);
                if (!deepEqual(local, merged)) {
                    const applied = await applySnapshot(merged, { save: true, render: true, expectedScope: scopeAtRequest, clearDirty: false });
                    if (!applied) return;
                }
                if (!deepEqual(merged, remote) && nativeScopeStable(scopeAtRequest)) {
                    try {
                        const publishResult = await sendSnapshotDirect(merged, Number(serverState.revision), newId(), scopeAtRequest);
                        serverState = publishResult.state;
                        baseSnapshot = clone(publishResult.state.snapshot);
                        clearLocalDirty(scopeAtRequest);
                    } catch (publishError) {
                        if (publishError?.status === 409 && publishError?.payload?.state) {
                            serverState = publishError.payload.state;
                            baseSnapshot = clone(publishError.payload.state.snapshot);
                        } else {
                            await enqueueSnapshot(merged, Number(serverState.revision), serverState.snapshot, scopeAtRequest);
                        }
                    }
                } else {
                    clearLocalDirty(scopeAtRequest);
                }
            } else if (!deepEqual(local, remote)) {
                // On a clean resync, server is authoritative. This is the key
                // protection against stale reloads resurrecting old history.
                const applied = await applySnapshot(remote, { save: true, render: true, expectedScope: scopeAtRequest });
                if (!applied) return;
                clearLocalDirty(scopeAtRequest);
            }
        }

        updateGenerationUi();
    } catch (error) {
        warn('resync failed', error);
    }
}
function resyncCurrentScope(epoch = scopeEpoch) {
    const run = resyncChain.then(() => resyncCurrentScopeInternal(epoch));
    resyncChain = run.catch(error => warn('resync chain failed', error));
    return run;
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
        // A genuine scope switch should stop the local LLM first, then release
        // the distributed lease. This is intentional, unlike heartbeat/SSE races.
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

    if (scopeRetryTimer) { clearTimeout(scopeRetryTimer); scopeRetryTimer = null; }
    if (streamTimer) clearTimeout(streamTimer);
    if (streamRetryTimer) clearTimeout(streamRetryTimer);
    if (remoteRenderTimer) clearTimeout(remoteRenderTimer);
    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);

    serverState = null;
    baseSnapshot = null;
    localGeneration = null;
    localGenerationLastSnapshot = null;
    generationClaimedThisPage = false;
    localGenerationScope = null;
    localGenerationBaseSnapshot = null;
    generationServerReadyId = null;
    generationStartPromise = null;
    generationStartPromiseId = null;
    generationHeartbeatInFlight = null;
    pendingStream = null;
    clearRemoteStreamState();
    streamInFlight = false;
    streamTimer = null;
    streamRetryTimer = null;
    terminalizingGenerationId = null;
    lastSseEventId = 0;
    generationMismatchSince = 0;
    generationClaimInFlightId = null;
    lastTerminatedGenerationId = null;
    streamInFlightSeq = 0;
    generationTerminalPhase = null;
    setSendLock('');
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
                scopeRetryTimer = setTimeout(() => {
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

        // During a live generation, a transient ST context change can happen
        // while the backend request is still running. Never turn that transient
        // mismatch into an abort. ST's real generation-stopped event will trigger
        // the eventual scope switch.
        if (localGeneration && currentScope) {
            log('[MCS] deferring scope switch until active generation ends', { reason, from: currentScope, to: nextScope });
            return;
        }

        ++scopeEpoch;
        const epoch = scopeEpoch;
        clearGenerationTerminalTimer();
        await leaveCurrentScope();

        stateApplyChain = Promise.resolve();
        currentScope = nextScope;
        scopeKeyValue = nextKey;
        localDirty = false;
        localDirtyScopeKey = '';
        lastSseEventId = 0;
        log('switch scope', reason, nextScope);

        await ensureIdsPersisted(nextScope);
        if (settings.enabled && settings.autoConnect) await openScope(epoch);
    })();
}
function switchScope(reason = 'scope-change') {
    const run = scopeSwitchChain.then(() => switchScopeInternal(reason));
    scopeSwitchChain = run.catch(error => warn('scope switch failed', error));
    return run;
}

async function ensureGenerationStarted() {
    if (!localGeneration || !localGenerationScope) return false;

    const generationId = localGeneration.generationId;
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration = localGenerationEpoch || scopeEpoch;

    if (generationServerReadyId === generationId) return true;
    if (!localGenerationMatches(generationId, scopeAtGeneration)) return false;

    if (generationStartPromise && generationStartPromiseId === generationId) return await generationStartPromise;

    generationStartPromiseId = generationId;
    generationStartPromise = (async () => {
        let lastError = null;
        for (let attempt = 0; attempt < 10; attempt += 1) {
            try {
                if (!localGenerationMatches(generationId, scopeAtGeneration)) return false;
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
                localGeneration = clone(current);
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
                    if (current?.generationId === generationId && generationIsMine(current) && ['started', 'streaming'].includes(current.phase)) {
                        localGeneration = clone(current);
                        generationServerReadyId = generationId;
                        return true;
                    }
                    if (current?.generationId && current.generationId !== generationId) return false;
                }
                await sleep(Math.min(250 * 2 ** attempt, 1500));
            }
        }

        log('generation start retries exhausted', lastError);
        return false;
    })();

    try {
        return await generationStartPromise;
    } finally {
        if (generationStartPromiseId === generationId) {
            generationStartPromise = null;
            generationStartPromiseId = null;
        }
    }
}
async function coordinatedGenerateInterceptor(chat, contextSize, abort, type) {
    refreshLiveContext();

    if (!settings.enabled || !settings.coordinateGeneration || applyingRemoteDepth > 0 || !currentScope) return;

    const scopeAtClaim = clone(currentScope);
    const epochAtClaim = scopeEpoch;

    // Prevent concurrent Generate calls in the same tab from creating multiple
    // distributed leases before the first claim response arrives.
    if (generationClaimInFlightId) {
        abort(false);
        return;
    }

    // Never claim against a transient/reloading native context.
    if (!nativeScopeStable(scopeAtClaim)) {
        const stable = await waitForNativeScope(scopeAtClaim, 2500, 75);
        if (!stable) {
            warn('[MCS] generation blocked because native chat scope did not stabilize');
            abort(false);
            return;
        }
    }

    let existing = serverState?.generation || null;
    if (existing && !localGeneration) {
        if (generationIsMine(existing) && generationClaimInFlightId === existing.generationId) {
            await sleep(25);
            existing = serverState?.generation || existing;
        } else if (generationIsMine(existing) && generationIsStaleOwned(existing)) {
            try {
                const cleared = await api('/generation/terminal', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
                    generationId: existing.generationId,
                    phase: 'stopped',
                    snapshot: clone(serverState?.snapshot || { messages: [], metadata: {} }),
                });
                serverState = cleared.state;
                baseSnapshot = clone(cleared.state.snapshot);
                lastTerminatedGenerationId = existing.generationId;
            } catch (error) {
                warn('failed to clear stale same-client generation before new generation', error);
                abort(false);
                return;
            }
            existing = serverState?.generation || null;
        }

        if (existing && !generationIsMine(existing)) {
            abort(false);
            if (settings.notifications) statusText('Another client is already generating this shared chat.', true);
            updateGenerationUi();
            return;
        }
    }

    if (localGeneration) {
        // Do not allow a second independent Generate() to run against the same
        // distributed lease. Group wrapper callbacks are handled by the existing
        // generation lifecycle events, so a real second claim must be blocked.
        abort(false);
        statusText(generationTerminalPhase ? 'Finishing the current shared generation…' : 'A shared generation is already active in this tab.', true);
        return;
    }

    const generationId = newId();
    generationClaimInFlightId = generationId;

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

            if (!currentScopeGuard(epochAtClaim) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtClaim) || !nativeScopeStable(scopeAtClaim)) {
                abort(false);
                return;
            }

            try {
                claimResult = await api('/generation/claim', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
                    opId: newId(),
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
                        if (other && generationIsMine(other) && generationIsStaleOwned(other)) {
                            try {
                                const cleared = await api('/generation/terminal', 'POST', {
                                    scope: scopeAtClaim,
                                    clientId,
                                    deviceId,
                                    generationId: other.generationId,
                                    phase: 'stopped',
                                    snapshot: clone(payload.state.snapshot),
                                });
                                serverState = cleared.state;
                                baseSnapshot = clone(cleared.state.snapshot);
                                lastTerminatedGenerationId = other.generationId;
                                revision = Number(cleared.state.revision);
                                claimBase = clone(cleared.state.snapshot);
                                desired = syncSnapshot(durableSnapshot());
                                continue;
                            } catch (clearError) {
                                warn('stale generation cleanup after claim conflict failed', clearError);
                                abort(false);
                                return;
                            }
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

        if (!currentScopeGuard(epochAtClaim) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtClaim) || !nativeScopeStable(scopeAtClaim)) {
            try {
                await api('/generation/terminal', 'POST', {
                    scope: scopeAtClaim,
                    clientId,
                    deviceId,
                    generationId,
                    phase: 'stopped',
                    snapshot: clone(claimResult.state?.snapshot || claimBase),
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

        // Install local ownership before claim/started SSE can arrive.
        serverState = claimResult.state;
        baseSnapshot = clone(claimResult.state.snapshot);
        localGeneration = clone(claimed);
        localGenerationScope = clone(scopeAtClaim);
        localGenerationEpoch = epochAtClaim;
        localGenerationBaseSnapshot = clone(baseSnapshot);
        localGenerationLastSnapshot = clone(desired);
        localStreamMessageId = null;
        localStreamMessageIndex = null;
        generationClaimedThisPage = true;
        generationTerminalPhase = null;
        lastTerminatedGenerationId = null;
        markLocalDirty(scopeAtClaim);
        updateGenerationUi();
        startGenerationHeartbeat(epochAtClaim);

        // Server start is completed before ST is allowed to make the LLM request.
        const started = await ensureGenerationStarted();
        if (!started) {
            try { await releaseGenerationClaim('stopped'); } catch { /* ignore */ }
            abort(false);
            return;
        }

        if (!localGeneration || localGeneration.generationId !== generationId || generationServerReadyId !== generationId) {
            try { await releaseGenerationClaim('stopped'); } catch { /* ignore */ }
            abort(false);
            return;
        }
    } catch (error) {
        warn('generation claim failed', error);
        if (localGeneration?.generationId === generationId) {
            try { await releaseGenerationClaim('stopped'); } catch { /* ignore */ }
        }
        abort(false);
        return;
    } finally {
        if (generationClaimInFlightId === generationId) generationClaimInFlightId = null;
    }
}
async function onGenerationStarted() {
    if (!localGeneration || !currentScope) return;
    try {
        const started = await ensureGenerationStarted();
        if (!started) {
            log('[MCS] native generation_started observed but server is not ready yet');
        }
    } catch (error) {
        warn('generation_started failed', error);
    }
}
function scheduleGenerationStream(delayOverride = null) {
    if (streamTimer || !pendingStream || !localGeneration || !currentScope) return;
    if (generationServerReadyId !== localGeneration.generationId) return;
    if (terminalizingGenerationId) return;

    const delay = delayOverride != null
        ? Math.max(0, Number(delayOverride) || 0)
        : Math.max(0, STREAM_SEND_MS - (Date.now() - lastStreamSentAt));

    streamTimer = setTimeout(async () => {
        streamTimer = null;
        if (!pendingStream || !localGeneration || terminalizingGenerationId) return;

        if (generationServerReadyId !== localGeneration.generationId) {
            const started = await ensureGenerationStarted();
            if (started) scheduleGenerationStream(0);
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

        if (!scopeAtStream || !currentScopeGuard(epochAtStream)) {
            pendingStream = payload;
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

                if (!localGenerationMatches(generationId, scopeAtStream)) return;

                const returned = result.state?.generation || null;
                serverState = result.state;
                if (returned?.generationId === generationId && generationIsMine(returned)) {
                    localGeneration = clone(returned);
                    generationServerReadyId = generationId;
                }
                lastStreamSentAt = Date.now();
            } catch (error) {
                const code = error?.payload?.error || '';

                if (code === 'generation_not_started') {
                    if (localGenerationMatches(generationId, scopeAtStream)) {
                        // Preserve the payload that failed; otherwise the first
                        // real token/message can disappear forever.
                        if (!pendingStream || Number(pendingStream.seq || 0) <= Number(payload.seq || 0)) pendingStream = payload;
                        const started = await ensureGenerationStarted();
                        if (started) scheduleGenerationStream(0);
                    }
                } else if (code === 'stream_sequence_conflict') {
                    const expected = Number(error?.payload?.expected || 0);
                    if (expected > 0 && localGenerationMatches(generationId, scopeAtStream)) {
                        const pending = pendingStream;
                        if (Number(payload.seq) < expected) {
                            localGeneration.seq = Math.max(Number(localGeneration.seq || 0), expected - 1);
                            if (pending) pendingStream = { ...pending, seq: Math.max(expected, Number(pending.seq || 0)) };
                        } else {
                            pendingStream = pending && Number(pending.seq) > expected
                                ? pending
                                : { ...payload, seq: expected };
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
                    const g = confirmed?.state?.generation;
                    if (g?.generationId === generationId && generationIsMine(g)) {
                        serverState = confirmed.state;
                        localGeneration = clone(g);
                        generationServerReadyId = ['started', 'streaming'].includes(g.phase) ? generationId : generationServerReadyId;
                        pendingStream = pendingStream || payload;
                        scheduleGenerationStream(0);
                    } else if (!g || g.generationId !== generationId) {
                        // Only an authoritative ownership loss may stop the native
                        // LLM request. Generic transport failure never does.
                        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
                    }
                } else if (error?.status === 403 && error?.payload?.error === 'not_member') {
                    if (localGenerationMatches(generationId, scopeAtStream)) pendingStream = pendingStream || payload;
                    await openScope(epochAtStream);
                    scheduleGenerationStream(STREAM_SEND_MS);
                } else {
                    if (localGenerationMatches(generationId, scopeAtStream)) {
                        if (!pendingStream || Number(pendingStream.seq || 0) < Number(payload.seq || 0)) pendingStream = payload;
                        if (!streamRetryTimer && terminalizingGenerationId !== generationId) {
                            streamRetryTimer = setTimeout(() => {
                                streamRetryTimer = null;
                                scheduleGenerationStream();
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
            if (pendingStream && localGeneration && generationServerReadyId === localGeneration.generationId && !terminalizingGenerationId) {
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
    if (!currentScope || makeScopeKey(currentScope) !== makeScopeKey(localGenerationScope)) return;
    if (!nativeScopeStable(localGenerationScope)) return;

    const messages = ctx.chat;
    let index = Number.isInteger(ctx.streamingProcessor?.messageId)
        ? Number(ctx.streamingProcessor.messageId)
        : -1;

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
    pendingStream = {
        seq,
        message,
        messageIndex: index,
    };

    if (generationServerReadyId === localGeneration.generationId) scheduleGenerationStream();
    else void ensureGenerationStarted();
}
async function releaseGenerationClaim(phase = 'stopped') {
    if (!localGeneration || !localGenerationScope) return false;
    const generation = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);

    terminalizingGenerationId = generation.generationId;
    try {
        try {
            const result = await api('/generation/terminal', 'POST', {
                scope: scopeAtGeneration,
                clientId,
                deviceId,
                generationId: generation.generationId,
                phase,
                snapshot: nativeScopeStable(scopeAtGeneration)
                    ? syncSnapshot(durableSnapshot())
                    : clone(localGenerationLastSnapshot || serverState?.snapshot || localGenerationBaseSnapshot || { messages: [], metadata: {} }),
            });
            serverState = result.state;
            baseSnapshot = clone(result.state.snapshot);
            lastTerminatedGenerationId = generation.generationId;
            clearLocalDirty(scopeAtGeneration);
            return true;
        } catch (error) {
            if (error?.status === 409 && error?.payload?.state) {
                serverState = error.payload.state;
                baseSnapshot = clone(error.payload.state.snapshot);
                return !error.payload.state.generation;
            }
            warn('generation claim release failed', error);
            return false;
        }
    } finally {
        clearLocalGenerationState();
        updateGenerationUi();
    }
}
async function sendGenerationTerminal(phase = 'completed') {
    if (!localGeneration || !localGenerationScope) return;
    if (terminalizingGenerationId === localGeneration.generationId) return;

    const g = clone(localGeneration);
    const scopeAtGeneration = clone(localGenerationScope);
    const epochAtGeneration = localGenerationEpoch || scopeEpoch;
    terminalizingGenerationId = g.generationId;

    try {
        if (generationStartPromiseId === g.generationId && generationStartPromise) {
            try { await generationStartPromise; } catch { /* ignore */ }
        }
        if (streamInFlightPromise) {
            try { await Promise.race([streamInFlightPromise, sleep(2500)]); } catch { /* ignore */ }
        }

        await sleep(60);
        const snapshot = nativeScopeStable(scopeAtGeneration)
            ? syncSnapshot(durableSnapshot())
            : clone(localGenerationLastSnapshot || serverState?.snapshot || localGenerationBaseSnapshot || { messages: [], metadata: {} });

        let succeeded = false;
        let lastError = null;

        for (let attempt = 0; attempt < 4; attempt += 1) {
            try {
                const result = await api('/generation/terminal', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                    generationId: g.generationId,
                    phase,
                    snapshot,
                });

                if (scopeKeyValue !== makeScopeKey(scopeAtGeneration)) return;
                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
                lastTerminatedGenerationId = g.generationId;
                clearLocalDirty(scopeAtGeneration);
                succeeded = true;
                break;
            } catch (error) {
                lastError = error;
                if (error?.status === 409 && error?.payload?.state) {
                    serverState = error.payload.state;
                    baseSnapshot = clone(error.payload.state.snapshot);
                    if (error.payload.state.generation && error.payload.state.generation.generationId !== g.generationId) break;
                    if (!error.payload.state.generation) break;
                }
                if (attempt < 3) await sleep(200 * (attempt + 1));
            }
        }

        if (!succeeded) {
            try {
                const stateResult = await api('/state', 'POST', {
                    scope: scopeAtGeneration,
                    clientId,
                    deviceId,
                });
                const state = stateResult.state;
                if (!state.generation) {
                    const recoveryBase = clone(localGenerationBaseSnapshot || baseSnapshot || { messages: [], metadata: {} });
                    const mergedRecovery = mergeSnapshots(recoveryBase, snapshot, state.snapshot);
                    if (!deepEqual(mergedRecovery, state.snapshot)) {
                        const recovered = await sendSnapshotDirect(mergedRecovery, Number(state.revision), newId(), scopeAtGeneration);
                        serverState = recovered.state;
                        baseSnapshot = clone(recovered.state.snapshot);
                    } else {
                        serverState = state;
                        baseSnapshot = clone(state.snapshot);
                    }
                    clearLocalDirty(scopeAtGeneration);
                    succeeded = true;
                }
            } catch (recoveryError) {
                lastError = recoveryError;
            }
        }

        if (!succeeded && lastError) {
            warn('generation terminal failed', lastError);
            if (scopeKeyValue === makeScopeKey(scopeAtGeneration)) {
                await enqueueSnapshot(snapshot, Number(serverState?.revision || 0), localGenerationBaseSnapshot || baseSnapshot, scopeAtGeneration, 'generation-terminal', g.generationId).catch(queueError => warn('terminal snapshot queue failed', queueError));
            }
        }
    } finally {
        // Do not let an old terminal response touch a newer scope/generation.
        if (currentScopeGuard(epochAtGeneration) || makeScopeKey(currentScope) === makeScopeKey(scopeAtGeneration)) {
            clearLocalGenerationState();
            updateGenerationUi();
        } else {
            clearLocalGenerationState();
        }
        if (generationTerminalPhase === phase) generationTerminalPhase = null;
    }

    await flushQueue();
    if (!nativeRestoreInProgress) void switchScope('post-generation-terminal');
}
async function handleRemoteStopEvent(data) {
    const g = data?.generation;
    if (!g || !localGeneration || g.generationId !== localGeneration.generationId) return;
    try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
}

function scheduleDeferredStreamCapture() {
    if (streamCaptureTimer || !localGeneration) return;
    streamCaptureTimer = setTimeout(() => {
        streamCaptureTimer = null;
        if (localGeneration) captureLocalStream();
    }, 0);
}

function onStreamToken() {
    if (!localGeneration) return;
    // ST emits STREAM_TOKEN_RECEIVED before its own progress handler updates the
    // message object. Capture on the next task so ctx.chat contains the new text.
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
async function onGenerationEnded() {
    if (!localGeneration) return;
    const generationId = localGeneration.generationId;
    generationTerminalPhase = 'completed';
    clearGenerationTerminalTimer();
    generationTerminalTimer = setTimeout(() => {
        generationTerminalTimer = null;
        if (!localGeneration || localGeneration.generationId !== generationId) return;
        sendGenerationTerminal('completed').catch(error => warn('completed terminal failed', error));
    }, 100);
}
async function onGenerationStopped() {
    if (!localGeneration) return;
    const generationId = localGeneration.generationId;
    // GENERATION_STOPPED can follow GENERATION_ENDED in ST's lifecycle. Completed
    // has precedence once observed.
    if (generationTerminalPhase === 'completed') return;
    generationTerminalPhase = 'stopped';
    clearGenerationTerminalTimer();
    generationTerminalTimer = setTimeout(() => {
        generationTerminalTimer = null;
        if (!localGeneration || localGeneration.generationId !== generationId) return;
        sendGenerationTerminal('stopped').catch(error => warn('stopped terminal failed', error));
    }, 100);
}
function publishAfterLocalEvent(_event = undefined, { allowDuringGeneration = false } = {}) {
    if (applyingRemoteDepth > 0 || !currentScope || !settings.enabled || !syncEnabled() || terminalizingGenerationId) return Promise.resolve(false);

    refreshLiveContext();
    const scopeAtEvent = clone(currentScope);
    const epochAtEvent = scopeEpoch;
    if (!nativeScopeStable(scopeAtEvent)) {
        if (localGeneration) {
            log('[MCS] local event arrived during transient generation context swap; deferring sync');
            return Promise.resolve(false);
        }
        return switchScope('local-event-context-mismatch');
    }

    markLocalDirty(scopeAtEvent);
    const snapshotAtEvent = syncSnapshot(durableSnapshot());

    const run = publishChain.then(async () => {
        if (scopeEpoch !== epochAtEvent || scopeKeyValue !== makeScopeKey(scopeAtEvent)) return false;
        if (!nativeScopeStable(scopeAtEvent)) return false;
        if (localGeneration && makeScopeKey(localGenerationScope) === makeScopeKey(scopeAtEvent) && !allowDuringGeneration) return false;
        if (localGeneration && localGeneration.phase === 'streaming' && allowDuringGeneration) return false;

        try {
            if (localGeneration) localGenerationLastSnapshot = clone(snapshotAtEvent);
            return await publishLocalSnapshot(snapshotAtEvent, {
                allowDuringGeneration,
                scope: scopeAtEvent,
            });
        } catch (error) {
            warn('publish after local event failed', error);
            return false;
        }
    });

    publishChain = run.catch(error => warn('local publish chain failed', error));
    return run;
}
async function handleChatLifecycleEvent() {
    await sleep(150);
    refreshLiveContext();
    if (nativeRestoreInProgress || localGeneration) return;
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
        } catch {
            /* ignore */
        }
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
            if (target.matches('#send_but') && settings.remoteStop) {
                try { await requestRemoteStop(); } catch (error) { warn('remote stop failed', error); }
            } else if (target.matches('#send_but')) {
                statusText('Another client is generating this shared chat.', true);
            }
        }
    };

    const keydownHandler = async event => {
        if (!isRemoteGenerationActive()) return;
        if (event.key !== 'Enter' || event.shiftKey || event.isComposing) return;
        if (!(event.target instanceof HTMLTextAreaElement || event.target instanceof HTMLInputElement)) return;
        if (event.target.id !== 'send_textarea') return;

        event.preventDefault();
        event.stopImmediatePropagation();
        if (!settings.remoteStop) {
            statusText('Another client is generating this shared chat.', true);
            return;
        }

        try { await requestRemoteStop(); } catch (error) { warn('remote stop failed', error); }
    };

    document.addEventListener('click', clickHandler, true);
    document.addEventListener('keydown', keydownHandler, true);
    registeredUiHandlers.push(['click', clickHandler, true], ['keydown', keydownHandler, true]);
}

async function requestRemoteStop() {
    let g = serverState?.generation;
    if (!g || !currentScope) return;

    if (generationLeaseExpired(g)) {
        await resyncCurrentScope(scopeEpoch);
        g = serverState?.generation;
        if (!g) return;
    }

    if (localGeneration) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        return;
    }
    if (!settings.remoteStop) return;

    const scopeAtRequest = clone(currentScope);
    await api('/generation/stop', 'POST', {
        scope: scopeAtRequest,
        clientId,
        deviceId,
    });
}

async function onActivate() {
    ctx = SillyTavern.getContext();
    activationInProgress = true;

    unwireEvents();
    unwireUiGuards();

    try { bc?.close?.(); } catch { /* ignore */ }
    bc = 'BroadcastChannel' in window ? new BroadcastChannel(BC_NAME) : null;

    bc?.addEventListener('message', message => {
        if (message.data?.scopeKey !== scopeKeyValue) return;
        if (message.data?.kind === 'state' && currentScope) resyncCurrentScope();
    });

    await negotiateClientId();
    await mountSettings();

    // Give ST a brief chance to finish its own restore. Only if it remains in the
    // default Assistant/empty context do we invoke our per-tab last-scope restore.
    await sleep(250);
    await maybeRestoreLastNativeScope();
    refreshLiveContext();

    activationInProgress = false;
    refreshLiveContext();
    wireEvents();
    wireUiGuards();
    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;
    await switchScope('activate');

    setTimeout(() => {
        switchScope('post-activate').catch(error => warn('post-activate scope check failed', error));
    }, 800);
}
async function onEnable() {
    settings.enabled = true;
    settings.autoConnect = true;
    saveSettings();
    refreshLiveContext();

    ++scopeEpoch;
    wireEvents();
    wireUiGuards();
    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

    currentScope = scopeFromContext();
    scopeKeyValue = makeScopeKey(currentScope);

    if (currentScope) await openScope(scopeEpoch);
    else statusText('Waiting for active chat…');
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
    generationClaimInFlightId = null;
    lastTerminatedGenerationId = null;
    streamInFlightSeq = 0;
    clearLocalDirty();
    try { bc?.close?.(); } catch { /* ignore */ }
    bc = null;
}
async function mountSettings() {
    if (settingsPanelMounted) return;

    const host =
        document.querySelector('#extensions_settings') ||
        document.querySelector('#extensions_settings2');

    if (!host) {
        setTimeout(() => mountSettings(), 1000);
        return;
    }

    settingsPanelMounted = true;

    const panel = document.createElement('div');
    panel.id = 'mcs_settings_panel';
    panel.className = 'mcs-settings';

    panel.innerHTML = `
        <h3>Multi-Client Sync</h3>

        <div class="mcs-status-row">
            <span
                id="mcs_status_dot"
                class="mcs-status mcs-disabled"
                title="Multi-Client Sync status"
            ></span>

            <span
                id="mcs_status"
                class="mcs-state-text"
            >
                Starting…
            </span>
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
            <button id="mcs_reconnect" class="menu_button" type="button">
                Reconnect
            </button>

            <button id="mcs_resync" class="menu_button" type="button">
                Resync Current Chat
            </button>
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
                ++scopeEpoch;
                await leaveCurrentScope();
                currentScope = null;
                scopeKeyValue = '';
                statusText('Disconnected');
            } else if (settings.enabled && settings.autoConnect) {
                await switchScope(`setting:${key}`);
            }

            updateGenerationUi();
        });
    }

    document.getElementById('mcs_reconnect')?.addEventListener('click', async () => {
        try {
            ++scopeEpoch;
            const epoch = scopeEpoch;

            await leaveCurrentScope();

            currentScope = scopeFromContext();
            scopeKeyValue = makeScopeKey(currentScope);

            if (currentScope && settings.enabled && settings.autoConnect) {
                writeLastScope(currentScope);
                await openScope(epoch);
            } else {
                statusText('No active chat');
            }
        } catch (error) {
            warn('manual reconnect failed', error);
        }
    });

    document.getElementById('mcs_resync')?.addEventListener('click', async () => {
        try {
            await resyncCurrentScope();
        } catch (error) {
            warn('manual resync failed', error);
        }
    });

    updateGenerationUi();
}

export { onActivate, onEnable, onDisable };
globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;
