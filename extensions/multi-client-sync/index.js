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
let generationRecoveryInFlight = null;
let localGenerationBaseRevision = 0;
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
let remoteSendButtonState = null;
let remoteStopInFlight = null;
let remoteStopGenerationId = null;
let pendingScopeSwitchReason = '';

const terminatedGenerationIds = new Map();

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

function rememberTerminatedGeneration(generationId) {
    if (!generationId) return;
    const id = String(generationId);
    lastTerminatedGenerationId = id;
    terminatedGenerationIds.set(id, Date.now());

    const cutoff = Date.now() - 60 * 60 * 1000;
    for (const [key, at] of terminatedGenerationIds) {
        if (at < cutoff) terminatedGenerationIds.delete(key);
    }

    while (terminatedGenerationIds.size > 64) {
        const first = terminatedGenerationIds.keys().next().value;
        if (first === undefined) break;
        terminatedGenerationIds.delete(first);
    }
}

function isTerminatedGeneration(generationId) {
    if (!generationId) return false;
    const id = String(generationId);
    if (terminatedGenerationIds.has(id)) return true;
    return String(lastTerminatedGenerationId || '') === id;
}

function clearTerminatedGenerationHistory() {
    terminatedGenerationIds.clear();
    lastTerminatedGenerationId = null;
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

function scheduleGenerationStartRetry(generationId, delay = 1000) {
    if (!generationId) return;
    if (generationStartRetryTimer) return;

    generationStartRetryTimer = setTimeout(() => {
        generationStartRetryTimer = null;
        if (!localGeneration || localGeneration.generationId !== generationId || terminalizingGenerationId === generationId) return;

        void ensureGenerationStarted().catch(error => warn('generation start retry failed', error));
    }, Math.max(250, delay));
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
            if (error) reject(error);
            else resolve();
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
            if (error) reject(error);
            else resolve(value);
        };

        try {
            const tx = db.transaction('ops', 'readonly');
            const req = tx.objectStore('ops').index('scopeKey').getAll(scopeKey);

            req.onsuccess = () => {
                finish(null, req.result.sort((a, b) => a.createdAt - b.createdAt));
            };

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
            if (error) reject(error);
            else resolve();
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

function restoreRemoteSendButtonState() {
    const button = remoteSendButtonState?.el;

    if (button) {
        button.innerHTML = remoteSendButtonState.html;

        if (remoteSendButtonState.title == null) button.removeAttribute('title');
        else button.setAttribute('title', remoteSendButtonState.title);

        if (remoteSendButtonState.ariaLabel == null) button.removeAttribute('aria-label');
        else button.setAttribute('aria-label', remoteSendButtonState.ariaLabel);

        if (remoteSendButtonState.disabled) button.disabled = true;
        else button.disabled = false;

        if (remoteSendButtonState.className != null) {
            button.className = remoteSendButtonState.className;
        } else {
            button.classList.remove('mcs-remote-stop');
        }

        if (remoteSendButtonState.dataset) {
            for (const [key, value] of Object.entries(remoteSendButtonState.dataset)) {
                if (value == null) delete button.dataset[key];
                else button.dataset[key] = value;
            }
        }
    }

    const nativeStopState = remoteSendButtonState?.nativeStop;

    if (nativeStopState?.el) {
        const stop = nativeStopState.el;

        stop.hidden = !!nativeStopState.hidden;
        stop.style.display = nativeStopState.display || '';
        if (nativeStopState.visibility == null) stop.style.removeProperty('visibility');
        else stop.style.visibility = nativeStopState.visibility;

        if (nativeStopState.ariaHidden == null) stop.removeAttribute('aria-hidden');
        else stop.setAttribute('aria-hidden', nativeStopState.ariaHidden);

        stop.disabled = !!nativeStopState.disabled;
    }

    remoteSendButtonState = null;
}

function setRemoteSendButtonMode(active) {
    const button = document.querySelector('#send_but');
    const nativeStop = document.querySelector('#mes_stop');

    if (!active) {
        restoreRemoteSendButtonState();
        return;
    }

    if (!button) return;

    if (remoteSendButtonState?.el !== button) {
        restoreRemoteSendButtonState();

        const dataset = {};
        for (const [key, value] of Object.entries(button.dataset || {})) {
            dataset[key] = value;
        }

        remoteSendButtonState = {
            el: button,
            html: button.innerHTML,
            title: button.getAttribute('title'),
            ariaLabel: button.getAttribute('aria-label'),
            disabled: !!button.disabled,
            className: button.className,
            dataset,
            nativeStop: null,
        };
    }

    if (nativeStop && remoteSendButtonState.nativeStop?.el !== nativeStop) {
        remoteSendButtonState.nativeStop = {
            el: nativeStop,
            hidden: !!nativeStop.hidden,
            display: nativeStop.style.display || '',
            visibility: nativeStop.style.visibility || '',
            ariaHidden: nativeStop.getAttribute('aria-hidden'),
            disabled: !!nativeStop.disabled,
        };

        nativeStop.hidden = true;
        nativeStop.style.display = 'none';
        nativeStop.setAttribute('aria-hidden', 'true');
    }

    const stopRequested = remoteStopGenerationId && serverState?.generation?.generationId === remoteStopGenerationId;

    if (nativeStop) {
        button.innerHTML = nativeStop.innerHTML || '<i class="fa-solid fa-stop"></i>';

        const stopTitle =
            (stopRequested ? 'Stop requested' : null) ||
            nativeStop.getAttribute('title') ||
            nativeStop.getAttribute('aria-label') ||
            'Stop generation';

        button.setAttribute('title', stopTitle);
        button.setAttribute('aria-label', stopTitle);
    } else {
        button.innerHTML = '<i class="fa-solid fa-stop"></i>';
        button.setAttribute('title', stopRequested ? 'Stop requested' : 'Stop generation');
        button.setAttribute('aria-label', stopRequested ? 'Stop requested' : 'Stop generation');
    }

    button.dataset.mcsRemoteStop = '1';
    button.classList.add('mcs-remote-stop');
    button.classList.remove('disabled');
    button.disabled = false;
}

function setSendLock(reason = '') {
    sendLockReason = reason;

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
            (
                selector !== '#send_but' ||
                (remote && !settings.remoteStop)
            );

        if (lockThisControl) {
            if (el.dataset.mcsLocked !== '1') {
                el.dataset.mcsPrevDisabled = el.disabled ? '1' : '0';
            }

            el.dataset.mcsLocked = '1';
            el.title = reason;
            el.classList.add('disabled');

            if ('disabled' in el) el.disabled = true;
        } else if (selector === '#send_but' && remote && settings.remoteStop) {
            delete el.dataset.mcsLocked;
            delete el.dataset.mcsPrevDisabled;

            el.classList.remove('disabled');

            if ('disabled' in el) el.disabled = false;
        } else if (el.dataset.mcsLocked === '1') {
            delete el.dataset.mcsLocked;

            const wasDisabled = el.dataset.mcsPrevDisabled === '1';
            delete el.dataset.mcsPrevDisabled;

            if ('disabled' in el) el.disabled = wasDisabled;

            el.removeAttribute('title');
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
    generationRecoveryInFlight = null;
    localGenerationBaseRevision = 0;
    streamInFlightSeq = 0;
    localStreamMessageId = null;
    localStreamMessageIndex = null;
    generationTerminalPhase = null;

    remoteStopInFlight = null;
    remoteStopGenerationId = null;
    pendingScopeSwitchReason = '';

    if (generationStartRetryTimer) clearTimeout(generationStartRetryTimer);
    if (streamTimer) clearTimeout(streamTimer);
    if (streamRetryTimer) clearTimeout(streamRetryTimer);
    if (streamCaptureTimer) clearTimeout(streamCaptureTimer);

    generationStartRetryTimer = null;
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
            .sort(
                (a, b) =>
                    (rank.get(a) ?? Number.MAX_SAFE_INTEGER) -
                    (rank.get(b) ?? Number.MAX_SAFE_INTEGER)
            );

        let next = candidates[0];

        if (!next) {
            next = [...chosenIds]
                .filter(id => !selected.has(id))
                .sort(
                    (a, b) =>
                        (rank.get(a) ?? Number.MAX_SAFE_INTEGER) -
                        (rank.get(b) ?? Number.MAX_SAFE_INTEGER)
                )[0];
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

    for (let i = 0; i < chosenMessages.length; i += 1) {
        byId.set(chosenIdentities[i], chosenMessages[i]);
    }

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
            value = rv;
        }

        if (value) {
            const out = clone(value);
            const preferredId =
                messageId(rv) ||
                messageId(lv) ||
                messageId(bv) ||
                newId();

            out.extra = out.extra && typeof out.extra === 'object'
                ? out.extra
                : {};

            out.extra.multi_client_sync =
                out.extra.multi_client_sync &&
                typeof out.extra.multi_client_sync === 'object'
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
                character = ctx.characters.find(
                    item => String(item?.name || '') === String(ctx.name2)
                ) || null;
            }

            if (String(character?.chat || '').trim() !== chatId) return false;
        }

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

    nativeSaveChain = run.catch(error => warn('native save chain failed', error));
    return run;
}

async function applySnapshotNow(
    snapshot,
    {
        save = false,
        render = true,
        expectedScope = currentScope,
        clearDirty = true,
        allowDuringGeneration = false,
    } = {},
) {
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

        if (!currentScope || makeScopeKey(currentScope) !== expectedKey || !nativeScopeStable(expectedScope)) {
            return false;
        }

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

        if (
            save &&
            epochAtStart === scopeEpoch &&
            !nativeRestoreInProgress &&
            nativeScopeStable(expectedScope) &&
            makeScopeKey(currentScope) === expectedKey
        ) {
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

    snapshotMutationChain = run.then(
        () => undefined,
        error => { warn('snapshot mutation failed', error); },
    );

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

async function enqueueSnapshot(
    snapshot,
    baseRev,
    baseSnap,
    scope = currentScope,
    kind = 'snapshot',
    generationId = null,
) {
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

    const existingRows = await idbList(scopeKey);
    const duplicate = existingRows.find(
        existing =>
            existing.kind === kind &&
            existing.generationId === row.generationId &&
            deepEqual(existing.snapshot, row.snapshot),
    );

    if (duplicate) return;

    await idbPut(row);

    const rows = await idbList(scopeKey);

    if (rows.length > MAX_QUEUE) {
        for (const old of rows.slice(0, rows.length - MAX_QUEUE)) {
            await idbDelete(old.id);
        }
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

async function publishLocalSnapshot(
    snapshot = durableSnapshot(),
    { allowDuringGeneration = false, scope = currentScope } = {},
) {
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
        const result = await sendSnapshotDirect(
            snapshot,
            revision,
            newId(),
            scopeAtPublish,
        );

        if (
            scopeKeyValue !== scopeKeyAtPublish ||
            !currentScope ||
            makeScopeKey(currentScope) !== scopeKeyAtPublish
        ) {
            return false;
        }

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        clearLocalDirty(scopeAtPublish);
        broadcastWake('state');

        return true;
    } catch (error) {
        if (scopeKeyValue !== scopeKeyAtPublish) return false;

        if (error?.status === 409 && error?.payload?.state) {
            const remoteState = error.payload.state;
            if (error.payload.error === 'generation_active') return false;

            const merged = mergeSnapshots(
                base,
                snapshot,
                remoteState.snapshot,
            );

            serverState = remoteState;
            baseSnapshot = clone(remoteState.snapshot);

            const retryBase = Number(remoteState.revision);

            try {
                const result = await sendSnapshotDirect(
                    merged,
                    retryBase,
                    newId(),
                    scopeAtPublish,
                );

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
                if (
                    retryError?.status === 409 &&
                    retryError?.payload?.error === 'generation_active'
                ) {
                    return false;
                }

                await enqueueSnapshot(
                    merged,
                    retryError?.payload?.state?.revision ?? retryBase,
                    retryError?.payload?.state?.snapshot ?? remoteState.snapshot,
                    scopeAtPublish,
                );

                scheduleQueueFlushRetry();
                return false;
            }
        }

        if (localGeneration && allowDuringGeneration) return false;

        await enqueueSnapshot(
            snapshot,
            revision,
            base,
            scopeAtPublish,
        );

        scheduleQueueFlushRetry();
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
        if (
            !currentScope ||
            scopeKeyValue !== scopeKeyAtFlush ||
            !nativeScopeStable(scopeAtFlush)
        ) {
            return;
        }

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

            let result = null;
            let sendError = null;

            for (let sendAttempt = 0; sendAttempt < 3; sendAttempt += 1) {
                try {
                    result = await sendSnapshotDirect(
                        nextSnapshot,
                        nextRevision,
                        row.id,
                        scopeAtFlush,
                    );

                    sendError = null;
                    break;
                } catch (error) {
                    sendError = error;

                    if (error?.status === 409) break;

                    if (sendAttempt < 2) {
                        await sleep(150 * (sendAttempt + 1));
                    }
                }
            }

            if (sendError) throw sendError;
            if (!result || scopeKeyValue !== scopeKeyAtFlush) return;

            serverState = result.state;
            baseSnapshot = clone(result.state.snapshot);

            await idbDelete(row.id);

            const applied = await applySnapshot(
                incomingSnapshot(result.state.snapshot),
                {
                    save: true,
                    render: true,
                    expectedScope: scopeAtFlush,
                },
            );

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

                const merged = mergeSnapshots(
                    row.baseSnapshot,
                    row.snapshot,
                    remote.snapshot,
                );

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
}

function flushQueue() {
    const run = queueFlushChain.then(() => flushQueueInternal());

    queueFlushChain = run.then(
        () => undefined,
        error => { warn('queue flush failed', error); },
    );

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

                if (currentScopeGuard(epoch)) {
                    openScope(epoch).catch(error => warn('scope retry failed', error));
                }
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
        const result = await api(
            '/join',
            'POST',
            {
                scope: scopeAtJoin,
                clientId,
                deviceId,
                snapshot: localSnapshot,
            },
            '',
            { signal: joinController.signal },
        );

        if (
            !currentScopeGuard(epoch) ||
            makeScopeKey(currentScope) !== makeScopeKey(scopeAtJoin)
        ) {
            try {
                await api('/leave', 'POST', {
                    scope: scopeAtJoin,
                    clientId,
                    deviceId,
                });
            } catch {
                /* best effort */
            }

            return;
        }

        if (!nativeScopeStable(scopeAtJoin)) return;

        if (joinAbortController === joinController) {
            joinAbortController = null;
        }

        if (scopeRetryTimer) {
            clearTimeout(scopeRetryTimer);
            scopeRetryTimer = null;
        }

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        remoteGenerationId = null;
        lastRemoteStreamSeq = -1;
        generationMismatchSince = 0;

        const staleOwnedGenerationId =
            serverState?.generation &&
            generationIsStaleOwned(serverState.generation)
                ? serverState.generation.generationId
                : null;

        if (
            staleOwnedGenerationId &&
            generationClaimInFlightId !== staleOwnedGenerationId
        ) {
            rememberTerminatedGeneration(staleOwnedGenerationId);

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
                    rememberTerminatedGeneration(staleOwnedGenerationId);
                }
            } catch (staleError) {
                if (
                    staleError?.status === 409 &&
                    staleError?.payload?.state
                ) {
                    serverState = staleError.payload.state;
                    baseSnapshot = clone(staleError.payload.state.snapshot);
                } else {
                    warn('stale generation cleanup failed', staleError);
                }
            }
        }

        if (
            serverState?.generation &&
            generationLeaseExpired(serverState.generation)
        ) {
            await resyncCurrentScope(epoch);
        }

        if (!currentScopeGuard(epoch)) return;

        if (!nativeScopeStable(scopeAtJoin)) {
            statusText('Waiting for active chat…');
            return;
        }

        const incoming = incomingSnapshot(serverState.snapshot);
        const queued = await idbList(scopeKeyValue);

        if (queued.length && !serverState.generation) {
            await flushQueue();
        } else if (
            !deepEqual(localSnapshot, incoming) &&
            !generationIsMine(serverState.generation)
        ) {
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

        if (
            serverState.generation?.message &&
            !generationIsMine(serverState.generation)
        ) {
            remoteGenerationId = serverState.generation.generationId;
            lastRemoteStreamSeq = Number(serverState.generation.seq || 0);

            pendingRemoteStream = {
                message: clone(serverState.generation.message),
                messageIndex: Number.isInteger(serverState.generation.messageIndex)
                    ? serverState.generation.messageIndex
                    : null,
                generationId: serverState.generation.generationId,
                seq: Number(serverState.generation.seq || 0),
            };

            scheduleRemoteRender();
        }

        await flushQueue();
        updateGenerationUi();
        statusText(`Connected · rev ${serverState.revision}`);
    } catch (error) {
        if (joinAbortController === joinController) {
            joinAbortController = null;
        }

        if (error?.name === 'AbortError') return;

        warn('join failed', error);
        statusText(`Offline: ${error?.message || 'connection failed'}`);

        if (
            !currentScopeGuard(epoch) ||
            scopeRetryTimer ||
            nativeRestoreInProgress
        ) {
            return;
        }

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

    const query =
        `?scope=${encodeURIComponent(encodeScope(currentScope))}` +
        `&clientId=${encodeURIComponent(clientId)}` +
        `&deviceId=${encodeURIComponent(deviceId)}` +
        `&lastEventId=${encodeURIComponent(String(lastSseEventId || 0))}`;

    const source = new EventSource(
        `${PLUGIN_BASE}/events${query}`,
        { withCredentials: true },
    );

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

    if (incomingGenerationId && isTerminatedGeneration(incomingGenerationId)) {
        serverState = {
            ...(serverState || {}),
            revision: Math.max(
                Number(serverState?.revision || 0),
                Number(data.revision || 0),
            ),
            scope: clone(data.scope),
            generation: null,
        };

        clearRemoteStreamState();
        updateGenerationUi();
        return;
    }

    const generation = incomingGeneration;
    const previousGeneration = serverState?.generation || null;
    const previousTime = Number(
        previousGeneration?.startedAt ||
        previousGeneration?.claimedAt ||
        0,
    );
    const incomingTime = Number(
        generation?.startedAt ||
        generation?.claimedAt ||
        0,
    );

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
        revision: Math.max(
            Number(serverState?.revision || 0),
            Number(data.revision || 0),
        ),
        generation,
        scope: clone(data.scope),
    };

    if (generationIsMine(generation)) {
        const claimPending =
            generationClaimInFlightId === generation.generationId;

        if (generationClaimedThisPage || claimPending) {
            if (
                generationClaimedThisPage &&
                localGeneration?.generationId === generation.generationId
            ) {
                localGeneration = clone(generation);
            }

            if (
                claimPending &&
                ['started', 'streaming'].includes(generation.phase)
            ) {
                generationServerReadyId = generation.generationId;
            }
        } else {
            resyncCurrentScope(scopeEpoch).catch(
                error => warn('stale generation hello resync failed', error),
            );
        }
    } else if (generation) {
        remoteGenerationId = generation.generationId;
        lastRemoteStreamSeq = Number(generation.seq || 0);

        if (generation.message) {
            pendingRemoteStream = {
                message: clone(generation.message),
                messageIndex: Number.isInteger(generation.messageIndex)
                    ? generation.messageIndex
                    : null,
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
        resyncCurrentScope(scopeEpoch).catch(
            error => warn('expired generation resync failed', error),
        );
    }
}

function handleSnapshotEvent(data) {
    const run = stateApplyChain.then(async () => {
        const revision = Number(data?.revision || 0);

        if (!revision || revision <= Number(serverState?.revision || 0)) return;
        if (!currentScope || !nativeScopeStable(currentScope)) return;

        const scopeAtEvent = clone(currentScope);
        const remote = incomingSnapshot(data.snapshot);

        const knownBase = clone(
            baseSnapshot ||
            serverState?.snapshot ||
            { messages: [], metadata: {} },
        );

        const local = syncSnapshot(durableSnapshot());
        const incomingGenerationId = String(data?.generationId || '');
        const dirty = isLocalDirty(scopeAtEvent);

        serverState = {
            ...(serverState || {}),
            revision,
            snapshot: clone(data.snapshot),
        };

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

        if (dirty) {
            appliedSnapshot = mergeSnapshots(
                knownBase,
                local,
                remote,
            );
        }

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
            if (
                !nativeScopeStable(scopeAtEvent) ||
                scopeKeyValue !== makeScopeKey(scopeAtEvent)
            ) {
                return;
            }

            try {
                const result = await sendSnapshotDirect(
                    appliedSnapshot,
                    revision,
                    newId(),
                    scopeAtEvent,
                );

                if (scopeKeyValue === makeScopeKey(scopeAtEvent)) {
                    serverState = result.state;
                    baseSnapshot = clone(result.state.snapshot);
                    clearLocalDirty(scopeAtEvent);
                }
            } catch (publishError) {
                if (
                    publishError?.status === 409 &&
                    publishError?.payload?.state
                ) {
                    serverState = publishError.payload.state;
                    baseSnapshot = clone(publishError.payload.state.snapshot);
                } else {
                    await enqueueSnapshot(
                        appliedSnapshot,
                        revision,
                        knownBase,
                        scopeAtEvent,
                    );
                    scheduleQueueFlushRetry();
                }
            }
        } else {
            clearLocalDirty(scopeAtEvent);
        }

        broadcastWake('state');
        updateGenerationUi();
    });

    stateApplyChain = run.catch(
        error => warn('remote snapshot apply failed', error),
    );

    return run;
}

function handleGenerationEvent(data) {
    const generation = clone(data?.generation || null);

    if (!generation || !currentScope || !generation.generationId) return;
    if (isTerminatedGeneration(generation.generationId)) return;

    const eventRevision = Number(data?.revision || 0);

    if (
        eventRevision &&
        eventRevision < Number(serverState?.revision || 0)
    ) {
        return;
    }

    const oldGeneration = serverState?.generation || null;
    const oldTime = Number(
        oldGeneration?.startedAt ||
        oldGeneration?.claimedAt ||
        0,
    );
    const incomingTime = Number(
        generation?.startedAt ||
        generation?.claimedAt ||
        0,
    );
    const sameGeneration =
        oldGeneration?.generationId === generation.generationId;

    if (
        oldGeneration &&
        !sameGeneration &&
        generationActive(oldGeneration) &&
        incomingTime &&
        oldTime &&
        incomingTime < oldTime
    ) {
        return;
    }

    serverState = {
        ...(serverState || {}),
        revision: Math.max(
            Number(serverState?.revision || 0),
            eventRevision,
        ),
        generation,
    };

    if (generationIsMine(generation)) {
        const claimPending =
            generationClaimInFlightId === generation.generationId;

        if (claimPending && !generationClaimedThisPage) {
            updateGenerationUi();
            return;
        }

        if (generationClaimedThisPage) {
            if (
                !localGeneration ||
                localGeneration.generationId === generation.generationId
            ) {
                localGeneration = clone(generation);
                localGenerationScope =
                    localGenerationScope || clone(currentScope);
                localGenerationEpoch = scopeEpoch;

                localGenerationBaseSnapshot =
                    localGenerationBaseSnapshot ||
                    clone(
                        baseSnapshot ||
                        serverState.snapshot ||
                        { messages: [], metadata: {} },
                    );

                localGenerationLastSnapshot =
                    localGenerationLastSnapshot ||
                    clone(
                        serverState.snapshot ||
                        baseSnapshot ||
                        { messages: [], metadata: {} },
                    );

                if (
                    ['started', 'streaming'].includes(generation.phase)
                ) {
                    generationServerReadyId = generation.generationId;
                }
            }
        } else {
            resyncCurrentScope(scopeEpoch).catch(
                error => warn('stale generation event resync failed', error),
            );
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
                messageIndex: Number.isInteger(generation.messageIndex)
                    ? generation.messageIndex
                    : null,
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

    try {
        const result = await api('/state', 'POST', {
            scope: scopeAtRecovery,
            clientId,
            deviceId,
        });

        if (
            !currentScopeGuard(epoch) ||
            makeScopeKey(currentScope) !== makeScopeKey(scopeAtRecovery)
        ) {
            return;
        }

        const authoritative = result.state || null;
        const generation = authoritative?.generation || null;
        const localId = localGeneration?.generationId || null;

        serverState = authoritative;
        baseSnapshot = clone(
            authoritative?.snapshot ||
            baseSnapshot ||
            { messages: [], metadata: {} },
        );

        if (generation) {
            if (
                localId &&
                generation.generationId === localId &&
                generationIsMine(generation)
            ) {
                localGeneration = clone(generation);
                localGenerationScope = clone(scopeAtRecovery);
                localGenerationEpoch = epoch;

                if (
                    ['started', 'streaming'].includes(generation.phase)
                ) {
                    generationServerReadyId = generation.generationId;
                }

                generationMismatchSince = 0;
                updateGenerationUi();
                return;
            }

            if (
                localGeneration &&
                generation.generationId !== localId
            ) {
                generationMismatchSince =
                    generationMismatchSince || Date.now();

                updateGenerationUi();
                return;
            }

            clearRemoteStreamState();

            if (
                generation.message &&
                !generationIsMine(generation)
            ) {
                remoteGenerationId = generation.generationId;
                lastRemoteStreamSeq = Number(generation.seq || 0);

                pendingRemoteStream = {
                    message: clone(generation.message),
                    messageIndex: Number.isInteger(generation.messageIndex)
                        ? generation.messageIndex
                        : null,
                    generationId: generation.generationId,
                    seq: Number(generation.seq || 0),
                };

                scheduleRemoteRender();
            }

            updateGenerationUi();
            return;
        }

        if (localGeneration) {
            const localId = localGeneration.generationId;

            generationMismatchSince =
                generationMismatchSince || Date.now();

            void reacquireGenerationOwnership('generation_recovered').then(
                recovered => {
                    if (recovered) {
                        generationMismatchSince = 0;
                        updateGenerationUi();
                    }
                },
            );

            generationServerReadyId =
                generationServerReadyId || null;

            generationHeartbeatFailures = 0;

            renderBanner('Reconnecting shared generation…');

            scheduleGenerationStartRetry(localId, 500);

            setTimeout(() => {
                if (localGeneration?.generationId === localId) {
                    updateGenerationUi();
                }
            }, 1200);

            return;
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

        setTimeout(() => renderBanner(''), 1800);
        updateGenerationUi();
    } catch (error) {
        warn('generation recovery confirmation failed', error);
    }
}

function handleGenerationStreamEvent(data) {
    const g = data?.generation;

    if (!g || !g.generationId) return;
    if (isTerminatedGeneration(g.generationId)) return;

    const current = serverState?.generation;
    const currentTime = Number(
        current?.startedAt ||
        current?.claimedAt ||
        0,
    );
    const incomingTime = Number(
        g?.startedAt ||
        g?.claimedAt ||
        0,
    );

    if (
        current &&
        current.generationId !== g.generationId &&
        generationActive(current) &&
        incomingTime &&
        currentTime &&
        incomingTime < currentTime
    ) {
        return;
    }

    const eventRevision = Number(data?.revision || 0);

    if (
        eventRevision &&
        eventRevision < Number(serverState?.revision || 0)
    ) {
        return;
    }

    const seq = Number(data?.seq ?? g.seq ?? 0);
    const sameGeneration =
        current?.generationId === g.generationId;

    if (
        sameGeneration &&
        current &&
        seq < Number(current.seq || 0)
    ) {
        return;
    }

    if (generationIsMine(g)) {
        if (
            generationClaimedThisPage ||
            generationClaimInFlightId === g.generationId
        ) {
            serverState = {
                ...(serverState || {}),
                generation: clone(g),
            };

            if (
                generationClaimedThisPage &&
                localGeneration?.generationId === g.generationId
            ) {
                localGeneration = clone(g);
            }
        }

        return;
    }

    if (remoteGenerationId !== g.generationId) {
        remoteGenerationId = g.generationId;
        lastRemoteStreamSeq = -1;
    }

    if (seq <= lastRemoteStreamSeq) return;

    const hadGap =
        seq > 0 &&
        lastRemoteStreamSeq >= 0 &&
        seq > lastRemoteStreamSeq + 1;

    if (hadGap) {
        resyncCurrentScope(scopeEpoch).catch(
            error => warn('stream gap resync failed', error),
        );
    }

    lastRemoteStreamSeq = seq;

    serverState = {
        ...(serverState || {}),
        revision: Math.max(
            Number(serverState?.revision || 0),
            eventRevision,
        ),
        generation: clone(g),
    };

    if (
        !data.message ||
        !currentScope ||
        !nativeScopeStable(currentScope)
    ) {
        updateGenerationUi();
        return;
    }

    pendingRemoteStream = {
        message: clone(data.message),
        messageIndex: Number.isInteger(data.messageIndex)
            ? data.messageIndex
            : null,
        generationId: g.generationId,
        seq,
    };

    scheduleRemoteRender();
    updateGenerationUi();
}

function applyRemoteStreamNow(item) {
    if (
        !item ||
        !ctx?.chat ||
        !currentScope ||
        !nativeScopeStable(currentScope)
    ) {
        return false;
    }

    const g = serverState?.generation;

    if (
        !g ||
        g.generationId !== item.generationId ||
        generationIsMine(g)
    ) {
        return false;
    }

    if (Number(item.seq || 0) < Number(lastRemoteStreamSeq || 0)) {
        return false;
    }

    applyingRemoteDepth += 1;

    try {
        const id = messageId(item.message);
        if (!id) return false;

        let index = ctx.chat.findIndex(
            message => messageId(message) === id,
        );

        if (index < 0) {
            if (
                Number.isInteger(item.messageIndex) &&
                item.messageIndex >= 0 &&
                item.messageIndex <= ctx.chat.length
            ) {
                index = item.messageIndex;
                ctx.chat.splice(
                    index,
                    0,
                    clone(item.message),
                );
            } else {
                ctx.chat.push(clone(item.message));
                index = ctx.chat.length - 1;
            }
        } else {
            ctx.chat[index] = clone(item.message);
        }

        let updated = false;

        try {
            const result = ctx.updateMessageBlock?.(
                index,
                clone(ctx.chat[index]),
                { rerenderMessage: true },
            );

            updated = result !== false;

            const domBlock = document.querySelector(
                `[mesid="${index}"]`,
            );

            if (!domBlock) updated = false;
        } catch (error) {
            log('updateMessageBlock failed', error);
            updated = false;
        }

        if (!updated) {
            try {
                ctx.printMessages?.();
            } catch (error) {
                log('printMessages fallback failed', error);
            }
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

        const run = stateApplyChain.then(
            () => applyRemoteStreamNow(item),
        );

        stateApplyChain = run.catch(
            error => warn('remote stream render failed', error),
        );

        void run.finally(() => {
            if (pendingRemoteStream && !remoteRenderTimer) {
                scheduleRemoteRender();
            }
        });
    }, REMOTE_RENDER_MS);
}

async function handleGenerationTerminalEvent(data) {
    const terminalGeneration = data?.generation || null;

    const generationId =
        terminalGeneration?.generationId ||
        data?.generationId ||
        null;

    const revision = Number(data?.revision || 0);
    const currentRevision = Number(serverState?.revision || 0);

    if (!generationId) return;

    if (
        revision &&
        currentRevision &&
        revision < currentRevision
    ) {
        return;
    }

    if (
        serverState?.generation &&
        serverState.generation.generationId !== generationId
    ) {
        return;
    }

    if (isTerminatedGeneration(generationId)) return;

    const scopeAtEvent = clone(currentScope);

    const hadLocalGeneration =
        !!localGeneration &&
        localGeneration.generationId === generationId;

    const mine =
        !!terminalGeneration &&
        generationIsMine(terminalGeneration) &&
        hadLocalGeneration;

    const terminalSnapshot = incomingSnapshot(
        data.snapshot ||
        serverState?.snapshot ||
        { messages: [], metadata: {} },
    );

    const knownBase = clone(
        baseSnapshot ||
        serverState?.snapshot ||
        { messages: [], metadata: {} },
    );

    const dirty =
        !mine &&
        isLocalDirty(scopeAtEvent);

    const local =
        !mine && dirty
            ? syncSnapshot(durableSnapshot())
            : null;

    rememberTerminatedGeneration(generationId);

    serverState = {
        ...(serverState || {}),
        revision: Math.max(
            currentRevision,
            revision,
        ),
        snapshot: clone(
            data.snapshot ||
            serverState?.snapshot ||
            { messages: [], metadata: {} },
        ),
        generation: null,
    };

    baseSnapshot = clone(serverState.snapshot);

    if (mine) {
        clearLocalGenerationState();
        clearLocalDirty(scopeAtEvent);
    } else if (
        scopeAtEvent &&
        nativeScopeStable(scopeAtEvent) &&
        data?.snapshot
    ) {
        let finalSnapshot = terminalSnapshot;

        if (dirty) {
            finalSnapshot = mergeSnapshots(
                knownBase,
                local,
                terminalSnapshot,
            );
        }

        const applied = await applySnapshot(
            finalSnapshot,
            {
                save: true,
                render: true,
                expectedScope: scopeAtEvent,
                clearDirty: false,
                allowDuringGeneration: true,
            },
        );

        if (applied) {
            if (
                !deepEqual(
                    finalSnapshot,
                    terminalSnapshot,
                ) &&
                currentScopeGuard(scopeEpoch)
            ) {
                try {
                    const committed = await sendSnapshotDirect(
                        finalSnapshot,
                        Number(serverState?.revision || 0),
                        newId(),
                        scopeAtEvent,
                    );

                    serverState = committed.state;
                    baseSnapshot = clone(
                        committed.state.snapshot,
                    );
                } catch (error) {
                    if (
                        error?.status === 409 &&
                        error?.payload?.state
                    ) {
                        serverState = error.payload.state;
                        baseSnapshot = clone(
                            error.payload.state.snapshot,
                        );
                    } else {
                        await enqueueSnapshot(
                            finalSnapshot,
                            Number(serverState?.revision || 0),
                            baseSnapshot,
                            scopeAtEvent,
                        );
                        scheduleQueueFlushRetry();
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
    remoteStopInFlight = null;
    remoteStopGenerationId = null;

    updateGenerationUi();
    await flushQueue();

    const pendingReason = pendingScopeSwitchReason;
    pendingScopeSwitchReason = '';

    if (!nativeRestoreInProgress) {
        void switchScope(
            pendingReason ||
            'post-generation-terminal',
        );
    }
}

function updateGenerationUi() {
    const g = serverState?.generation;

    if (
        localGeneration &&
        (!g || g.generationId === localGeneration.generationId)
    ) {
        if (
            generationServerReadyId ===
            localGeneration.generationId
        ) {
            setSendLock(
                'You are generating in this shared chat.',
            );
            renderBanner(
                generationTerminalPhase === 'stopped'
                    ? 'Stopping shared generation…'
                    : 'Generating here · shared with other clients',
            );
        } else {
            setSendLock(
                'Reconnecting shared generation…',
            );
            renderBanner(
                'Reconnecting shared generation…',
            );
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
        renderBanner(
            'Recovering abandoned generation…',
        );
        return;
    }

    if (generationIsMine(g) && !localGeneration) {
        setSendLock('');
        renderBanner(
            'Recovering abandoned generation…',
        );
        return;
    }

    if (g.stopRequested) {
        setSendLock(
            'Another client requested Stop for this generation.',
        );
        renderBanner(
            'Stopping generation in another client…',
        );
        return;
    }

    setSendLock(
        'Another client is generating this shared chat.',
    );

    renderBanner(
        'Another client is generating this shared chat · live mirror',
    );
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

            const oldRevision = Number(
                serverState.revision || 0,
            );

            const oldGenerationId =
                serverState.generation?.generationId ||
                null;

            const newRevision = Number(
                result.revision || 0,
            );

            const newGenerationId =
                result.generation?.generationId ||
                null;

            serverState = {
                ...serverState,
                revision: Math.max(
                    oldRevision,
                    newRevision,
                ),
                generation: clone(
                    result.generation || null,
                ),
            };

            if (
                oldRevision !== newRevision ||
                oldGenerationId !== newGenerationId
            ) {
                await resyncCurrentScope(epoch);
            }

            updateGenerationUi();
        } catch (error) {
            if (
                error?.status === 403 &&
                error?.payload?.error === 'not_member' &&
                currentScopeGuard(epoch)
            ) {
                await openScope(epoch);
                return;
            }

            log('membership heartbeat failed', error);
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

    const run = (async () => {
        try {
            const stateResult = await api('/state', 'POST', {
                scope: scopeAtGeneration,
                clientId,
                deviceId,
            });

            if (
                !localGenerationMatches(
                    generationId,
                    scopeAtGeneration,
                ) ||
                !currentScopeGuard(epochAtGeneration)
            ) {
                return false;
            }

            const state = stateResult.state;
            const current = state?.generation || null;

            if (
                current &&
                current.generationId === generationId &&
                generationIsMine(current)
            ) {
                serverState = state;
                localGeneration = clone(current);
                generationMismatchSince = 0;

                if (
                    ['started', 'streaming'].includes(
                        current.phase,
                    )
                ) {
                    generationServerReadyId = generationId;
                    return true;
                }

                generationServerReadyId = null;
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

                // Do not kill the native request from this recovery pass.
                // The generation heartbeat performs the deliberate,
                // multi-step competing-owner confirmation.
                return false;
            }

            // A revision change by itself is not enough reason to kill the
            // native generation. Generation stream snapshots legitimately
            // advance the shared revision while the same generation is alive.
            if (
                localGenerationBaseRevision &&
                Number(state.revision || 0) !==
                    localGenerationBaseRevision
            ) {
                log(
                    '[MCS] generation recovery observed shared revision advance',
                    {
                        reason,
                        expected: localGenerationBaseRevision,
                        actual: state.revision,
                    },
                );
            }

            const claimed = await api('/generation/claim', 'POST', {
                scope: scopeAtGeneration,
                clientId,
                deviceId,
                opId: newId(),
                generationId,
                generationType: String(
                    generation.generationType || 'normal',
                ),
                baseRevision: Number(
                    state.revision || 0,
                ),
                snapshot: syncSnapshot(
                    durableSnapshot(),
                ),
            });

            if (
                !localGenerationMatches(
                    generationId,
                    scopeAtGeneration,
                ) ||
                !currentScopeGuard(epochAtGeneration)
            ) {
                return false;
            }

            const nextGeneration =
                claimed.state?.generation;

            if (
                !nextGeneration ||
                nextGeneration.generationId !== generationId ||
                !generationIsMine(nextGeneration)
            ) {
                return false;
            }

            serverState = claimed.state;
            baseSnapshot = clone(
                claimed.state.snapshot,
            );

            localGeneration = clone(nextGeneration);
            localGenerationBaseRevision = Number(
                claimed.state.revision || 0,
            );

            generationServerReadyId = null;
            generationMismatchSince = 0;

            updateGenerationUi();

            scheduleGenerationStartRetry(
                generationId,
                250,
            );

            return await ensureGenerationStarted();
        } catch (error) {
            if (
                error?.status === 409 &&
                error?.payload?.state
            ) {
                const state = error.payload.state;

                serverState = state;
                baseSnapshot = clone(
                    state.snapshot,
                );

                const competing = state.generation;

                if (
                    competing &&
                    competing.generationId !== generationId
                ) {
                    generationMismatchSince =
                        generationMismatchSince ||
                        Date.now();

                    return false;
                }
            }

            log(
                '[MCS] generation ownership recovery failed; keeping local LLM alive',
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
    const scopeAtGeneration =
        clone(localGenerationScope);

    localGenerationEpoch = epoch;

    generationHeartbeatTimer = setInterval(
        async () => {
            if (
                !localGeneration ||
                localGeneration.generationId !== generationId ||
                !currentScopeGuard(epoch)
            ) {
                return;
            }

            if (generationHeartbeatInFlight) return;

            refreshLiveContext();

            if (!nativeScopeStable(scopeAtGeneration)) {
                generationMismatchSince =
                    generationMismatchSince ||
                    Date.now();
            } else {
                generationMismatchSince = 0;
            }

            const heartbeatRun = (async () => {
                try {
                    const result = await api(
                        '/generation/heartbeat',
                        'POST',
                        {
                            scope: scopeAtGeneration,
                            clientId,
                            deviceId,
                            generationId,
                        },
                    );

                    if (
                        !localGeneration ||
                        localGeneration.generationId !== generationId ||
                        !currentScopeGuard(epoch)
                    ) {
                        return;
                    }

                    const stateGeneration =
                        result.state?.generation || null;

                    serverState = result.state;

                    if (
                        result.stopRequested ||
                        stateGeneration?.stopRequested
                    ) {
                        generationTerminalPhase = 'stopped';
                        remoteStopGenerationId =
                            generationId;

                        clearGenerationTerminalTimer();
                        renderBanner(
                            'Stopping generation…',
                        );

                        try {
                            ctx?.stopGeneration?.();
                        } catch {
                            /* ignore */
                        }

                        return;
                    }

                    if (!stateGeneration ||
                        stateGeneration.generationId !== generationId ||
                        !generationIsMine(stateGeneration)
                    ) {
                        const confirm =
                            await api('/state', 'POST', {
                                scope: scopeAtGeneration,
                                clientId,
                                deviceId,
                            }).catch(() => null);

                        const confirmed =
                            confirm?.state?.generation ||
                            null;

                        if (
                            confirmed &&
                            confirmed.generationId === generationId &&
                            generationIsMine(confirmed)
                        ) {
                            serverState = confirm.state;
                            localGeneration = clone(
                                confirmed,
                            );

                            updateGenerationUi();
                            return;
                        }

                        if (
                            !confirmed &&
                            currentScopeGuard(epoch)
                        ) {
                            await openScope(epoch);
                            return;
                        }

                        if (
                            confirmed?.generation &&
                            !generationIsMine(
                                confirmed.generation,
                            )
                        ) {
                            generationMismatchSince =
                                generationMismatchSince ||
                                Date.now();

                            if (
                                Date.now() -
                                generationMismatchSince <
                                3500
                            ) {
                                return;
                            }

                            const secondConfirm =
                                await api('/state', 'POST', {
                                    scope: scopeAtGeneration,
                                    clientId,
                                    deviceId,
                                }).catch(() => null);

                            const competing =
                                secondConfirm?.state?.generation ||
                                null;

                            if (
                                competing &&
                                competing.generationId !==
                                    generationId &&
                                generationActive(competing)
                            ) {
                                generationTerminalPhase =
                                    'stopped';

                                try {
                                    ctx?.stopGeneration?.();
                                } catch {
                                    /* ignore */
                                }
                            } else if (
                                secondConfirm?.state?.generation?.generationId ===
                                generationId
                            ) {
                                serverState =
                                    secondConfirm.state;
                                localGeneration =
                                    clone(
                                        secondConfirm.state.generation,
                                    );
                                generationMismatchSince = 0;
                                updateGenerationUi();
                            }

                            return;
                        }

                        return;
                    }

                    localGeneration = clone(
                        stateGeneration,
                    );

                    generationServerReadyId =
                        ['started', 'streaming'].includes(
                            stateGeneration.phase,
                        )
                            ? generationId
                            : generationServerReadyId;

                    if (
                        !generationServerReadyId
                    ) {
                        scheduleGenerationStartRetry(
                            generationId,
                            250,
                        );
                    }

                    generationHeartbeatFailures = 0;
                    generationMismatchSince = 0;

                    updateGenerationUi();
                } catch (error) {
                    generationHeartbeatFailures += 1;

                    if (
                        error?.status === 409 &&
                        [
                            'generation_not_owned',
                            'generation_expired',
                        ].includes(
                            error?.payload?.error,
                        )
                    ) {
                        const immediate =
                            error?.payload?.state ||
                            null;

                        if (
                            immediate?.generation?.generationId ===
                                generationId &&
                            generationIsMine(
                                immediate.generation,
                            )
                        ) {
                            serverState = immediate;
                            localGeneration = clone(
                                immediate.generation,
                            );
                            generationMismatchSince = 0;
                            return;
                        }

                        let confirmed = null;

                        try {
                            const stateResult =
                                await api('/state', 'POST', {
                                    scope: scopeAtGeneration,
                                    clientId,
                                    deviceId,
                                });

                            confirmed =
                                stateResult.state;
                        } catch {
                            confirmed = null;
                        }

                        if (
                            !localGeneration ||
                            localGeneration.generationId !==
                                generationId ||
                            !currentScopeGuard(epoch)
                        ) {
                            return;
                        }

                        if (
                            confirmed?.generation?.generationId ===
                                generationId &&
                            generationIsMine(
                                confirmed.generation,
                            )
                        ) {
                            serverState = confirmed;
                            localGeneration = clone(
                                confirmed.generation,
                            );
                            generationMismatchSince = 0;

                            if (
                                ['started', 'streaming'].includes(
                                    confirmed.generation.phase,
                                )
                            ) {
                                generationServerReadyId =
                                    generationId;
                            }

                            return;
                        }

                        if (
                            confirmed?.generation &&
                            !generationIsMine(
                                confirmed.generation,
                            ) &&
                            generationActive(
                                confirmed.generation,
                            )
                        ) {
                            generationMismatchSince =
                                generationMismatchSince ||
                                Date.now();

                            if (
                                Date.now() -
                                    generationMismatchSince <
                                3500
                            ) {
                                return;
                            }

                            const finalConfirm =
                                await api('/state', 'POST', {
                                    scope: scopeAtGeneration,
                                    clientId,
                                    deviceId,
                                }).catch(() => null);

                            const finalGeneration =
                                finalConfirm?.state?.generation ||
                                null;

                            if (
                                finalGeneration &&
                                finalGeneration.generationId !==
                                    generationId &&
                                generationActive(
                                    finalGeneration,
                                )
                            ) {
                                generationTerminalPhase =
                                    'stopped';

                                try {
                                    ctx?.stopGeneration?.();
                                } catch {
                                    /* ignore */
                                }
                            } else if (
                                finalGeneration?.generationId ===
                                generationId
                            ) {
                                serverState =
                                    finalConfirm.state;
                                localGeneration =
                                    clone(
                                        finalGeneration,
                                    );
                                generationMismatchSince = 0;
                            }

                            return;
                        }

                        generationMismatchSince =
                            generationMismatchSince ||
                            Date.now();

                        if (
                            Date.now() -
                                generationMismatchSince >=
                            1200
                        ) {
                            void reacquireGenerationOwnership(
                                'heartbeat-recovery',
                            );
                        }

                        return;
                    }

                    if (
                        error?.status === 403 &&
                        error?.payload?.error ===
                            'not_member'
                    ) {
                        await openScope(epoch);
                        return;
                    }

                    if (
                        localGeneration &&
                        localGeneration.generationId ===
                            generationId &&
                        !generationServerReadyId
                    ) {
                        scheduleGenerationStartRetry(
                            generationId,
                            1000,
                        );
                    }

                    log(
                        'generation heartbeat failed; continuing local generation',
                        error,
                    );
                } finally {
                    generationHeartbeatInFlight = null;
                }
            })();

            generationHeartbeatInFlight = heartbeatRun;
            await heartbeatRun.catch(() => {
                /* handled above */
            });
        },
        GENERATION_HEARTBEAT_MS,
    );
}

async function resyncCurrentScopeInternal(
    epoch = scopeEpoch,
) {
    if (!currentScope || !currentScopeGuard(epoch)) return;
    if (!nativeScopeStable(currentScope)) return;

    const scopeAtRequest = clone(currentScope);

    try {
        const result = await api('/state', 'POST', {
            scope: scopeAtRequest,
            clientId,
            deviceId,
        });

        if (
            !currentScopeGuard(epoch) ||
            makeScopeKey(currentScope) !==
                makeScopeKey(scopeAtRequest)
        ) {
            return;
        }

        const serverGeneration =
            result.state.generation || null;

        const remote =
            incomingSnapshot(
                result.state.snapshot,
            );

        const dirty =
            isLocalDirty(scopeAtRequest);

        const local =
            syncSnapshot(durableSnapshot());

        const knownBase = clone(
            baseSnapshot ||
            serverState?.snapshot ||
            { messages: [], metadata: {} },
        );

        serverState = result.state;
        baseSnapshot = clone(
            result.state.snapshot,
        );

        if (localGeneration) {
            if (
                serverGeneration &&
                serverGeneration.generationId ===
                    localGeneration.generationId &&
                generationIsMine(
                    serverGeneration,
                )
            ) {
                localGeneration =
                    clone(serverGeneration);

                localGenerationScope =
                    clone(scopeAtRequest);

                localGenerationEpoch = epoch;

                generationServerReadyId =
                    ['started', 'streaming'].includes(
                        serverGeneration.phase,
                    )
                        ? serverGeneration.generationId
                        : generationServerReadyId;

                generationMismatchSince = 0;
            } else {
                if (
                    generationMismatchSince === 0
                ) {
                    generationMismatchSince = Date.now();
                }

                if (
                    Date.now() -
                        generationMismatchSince >
                    3500 &&
                    !generationClaimInFlightId
                ) {
                    const confirm =
                        await api('/state', 'POST', {
                            scope: scopeAtRequest,
                            clientId,
                            deviceId,
                        }).catch(() => null);

                    const confirmed =
                        confirm?.state?.generation ||
                        null;

                    if (
                        confirmed &&
                        confirmed.generationId ===
                            localGeneration.generationId &&
                        generationIsMine(confirmed)
                    ) {
                        serverState =
                            confirm.state;
                        localGeneration =
                            clone(confirmed);
                        generationMismatchSince = 0;
                    } else if (
                        confirmed &&
                        confirmed.generationId !==
                            localGeneration.generationId &&
                        generationActive(confirmed)
                    ) {
                        generationTerminalPhase =
                            'stopped';

                        try {
                            ctx?.stopGeneration?.();
                        } catch {
                            /* ignore */
                        }
                    } else if (!confirmed) {
                        generationMismatchSince = 0;
                        void reacquireGenerationOwnership(
                            'resync-recovery',
                        );
                    }
                }
            }
        } else if (
            serverGeneration &&
            generationIsMine(serverGeneration)
        ) {
            if (
                !generationClaimedThisPage &&
                generationClaimInFlightId !==
                    serverGeneration.generationId
            ) {
                const staleId =
                    serverGeneration.generationId;

                rememberTerminatedGeneration(
                    staleId,
                );

                try {
                    const cleared =
                        await api(
                            '/generation/terminal',
                            'POST',
                            {
                                scope: scopeAtRequest,
                                clientId,
                                deviceId,
                                generationId:
                                    serverGeneration.generationId,
                                phase: 'stopped',
                                snapshot: clone(
                                    result.state.snapshot,
                                ),
                            },
                        );

                    serverState =
                        cleared.state;

                    baseSnapshot = clone(
                        cleared.state.snapshot,
                    );

                    rememberTerminatedGeneration(
                        staleId,
                    );
                } catch (error) {
                    if (
                        error?.status === 409 &&
                        error?.payload?.state
                    ) {
                        serverState =
                            error.payload.state;

                        baseSnapshot =
                            clone(
                                error.payload.state.snapshot,
                            );

                        if (
                            !error.payload.state
                                .generation
                        ) {
                            rememberTerminatedGeneration(
                                staleId,
                            );
                        }
                    }
                }
            }
        }

        const effectiveGeneration =
            serverState.generation || null;

        if (
            effectiveGeneration?.message &&
            !generationIsMine(
                effectiveGeneration,
            )
        ) {
            remoteGenerationId =
                effectiveGeneration.generationId;

            lastRemoteStreamSeq =
                Number(
                    effectiveGeneration.seq || 0,
                );

            pendingRemoteStream = {
                message: clone(
                    effectiveGeneration.message,
                ),
                messageIndex:
                    Number.isInteger(
                        effectiveGeneration.messageIndex,
                    )
                        ? effectiveGeneration.messageIndex
                        : null,
                generationId:
                    effectiveGeneration.generationId,
                seq: Number(
                    effectiveGeneration.seq || 0,
                ),
            };

            scheduleRemoteRender();
        }

        if (
            !effectiveGeneration &&
            !localGeneration
        ) {
            if (dirty) {
                const merged =
                    mergeSnapshots(
                        knownBase,
                        local,
                        remote,
                    );

                if (
                    !deepEqual(local, merged)
                ) {
                    const applied =
                        await applySnapshot(
                            merged,
                            {
                                save: true,
                                render: true,
                                expectedScope:
                                    scopeAtRequest,
                                clearDirty: false,
                            },
                        );

                    if (!applied) return;
                }

                if (
                    !deepEqual(
                        merged,
                        remote,
                    ) &&
                    nativeScopeStable(
                        scopeAtRequest,
                    )
                ) {
                    try {
                        const publishResult =
                            await sendSnapshotDirect(
                                merged,
                                Number(
                                    serverState.revision,
                                ),
                                newId(),
                                scopeAtRequest,
                            );

                        serverState =
                            publishResult.state;

                        baseSnapshot = clone(
                            publishResult.state.snapshot,
                        );

                        clearLocalDirty(
                            scopeAtRequest,
                        );
                    } catch (publishError) {
                        if (
                            publishError?.status ===
                                409 &&
                            publishError?.payload
                                ?.state
                        ) {
                            serverState =
                                publishError.payload.state;

                            baseSnapshot =
                                clone(
                                    publishError
                                        .payload
                                        .state
                                        .snapshot,
                                );
                        } else {
                            await enqueueSnapshot(
                                merged,
                                Number(
                                    serverState.revision,
                                ),
                                serverState.snapshot,
                                scopeAtRequest,
                            );

                            scheduleQueueFlushRetry();
                        }
                    }
                } else {
                    clearLocalDirty(
                        scopeAtRequest,
                    );
                }
            } else if (
                !deepEqual(local, remote)
            ) {
                const applied =
                    await applySnapshot(
                        remote,
                        {
                            save: true,
                            render: true,
                            expectedScope:
                                scopeAtRequest,
                        },
                    );

                if (!applied) return;

                clearLocalDirty(
                    scopeAtRequest,
                );
            }
        }

        updateGenerationUi();
    } catch (error) {
        warn('resync failed', error);
    }
}

function resyncCurrentScope(epoch = scopeEpoch) {
    const run = resyncChain.then(
        () => resyncCurrentScopeInternal(epoch),
    );

    resyncChain = run.then(
        () => undefined,
        error => {
            warn('resync chain failed', error);
        },
    );

    return run;
}

async function leaveCurrentScope(
    { preserveNativeGeneration = false } = {},
) {
    if (joinAbortController) {
        try { joinAbortController.abort(); } catch { /* ignore */ }
        joinAbortController = null;
    }

    if (!currentScope) return;

    const leavingScope = clone(currentScope);
    const leavingGenerationId =
        localGeneration?.generationId || null;

    if (
        localGeneration &&
        localGenerationScope &&
        !preserveNativeGeneration
    ) {
        try {
            ctx?.stopGeneration?.();
        } catch {
            /* ignore */
        }

        try {
            await sendGenerationTerminal(
                'stopped',
            );
        } catch (error) {
            warn(
                'generation cleanup failed while leaving scope',
                error,
            );
        }
    }

    try {
        await api('/leave', 'POST', {
            scope: leavingScope,
            clientId,
            deviceId,
        });
    } catch {
        /* best effort */
    }

    disconnectSse();
    stopHeartbeats();
    stopGenerationHeartbeat();

    if (scopeRetryTimer) {
        clearTimeout(scopeRetryTimer);
        scopeRetryTimer = null;
    }

    if (queueRetryTimer) {
        clearTimeout(queueRetryTimer);
        queueRetryTimer = null;
    }

    if (generationStartRetryTimer) {
        clearTimeout(generationStartRetryTimer);
        generationStartRetryTimer = null;
    }

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
    generationRecoveryInFlight = null;
    localGenerationBaseRevision = 0;
    streamInFlightSeq = 0;
    generationTerminalPhase = null;
    remoteStopInFlight = null;
    remoteStopGenerationId = null;
    pendingScopeSwitchReason = '';

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

function switchScopeInternal(
    reason = 'scope-change',
) {
    return (async () => {
        if (nativeRestoreInProgress) return;

        refreshLiveContext();

        const nextScope =
            scopeFromContext();

        const nextKey =
            makeScopeKey(nextScope);

        if (!nextScope) {
            statusText(
                'Waiting for active chat…',
            );

            if (
                settings.enabled &&
                settings.autoConnect &&
                !scopeRetryTimer &&
                !activationInProgress
            ) {
                scopeRetryTimer = setTimeout(
                    () => {
                        scopeRetryTimer = null;

                        switchScope(
                            'startup-retry',
                        ).catch(
                            error =>
                                warn(
                                    'startup scope retry failed',
                                    error,
                                ),
                        );
                    },
                    500,
                );
            }

            return;
        }

        if (
            nextKey === scopeKeyValue &&
            currentScope
        ) {
            if (nativeScopeStable(nextScope)) {
                if (
                    !serverState &&
                    settings.enabled &&
                    settings.autoConnect
                ) {
                    await openScope(scopeEpoch);
                } else {
                    updateGenerationUi();
                }
            }

            return;
        }

        if (
            localGeneration &&
            currentScope
        ) {
            pendingScopeSwitchReason =
                reason ||
                'deferred-scope-change';

            log(
                '[MCS] deferring scope switch until active generation ends',
                {
                    reason,
                    from: currentScope,
                    to: nextScope,
                },
            );

            return;
        }

        ++scopeEpoch;
        const epoch = scopeEpoch;

        clearGenerationTerminalTimer();
        await leaveCurrentScope();

        stateApplyChain =
            Promise.resolve();

        currentScope = nextScope;
        scopeKeyValue = nextKey;

        localDirty = false;
        localDirtyScopeKey = '';
        lastSseEventId = 0;

        log(
            'switch scope',
            reason,
            nextScope,
        );

        await ensureIdsPersisted(nextScope);

        if (
            settings.enabled &&
            settings.autoConnect
        ) {
            await openScope(epoch);
        }
    })();
}

function switchScope(
    reason = 'scope-change',
) {
    const run =
        scopeSwitchChain.then(
            () =>
                switchScopeInternal(
                    reason,
                ),
        );

    scopeSwitchChain = run.then(
        () => undefined,
        error => {
            warn(
                'scope switch failed',
                error,
            );
        },
    );

    return run;
}

async function ensureGenerationStarted() {
    if (
        !localGeneration ||
        !localGenerationScope
    ) {
        return false;
    }

    const generationId =
        localGeneration.generationId;

    const scopeAtGeneration =
        clone(localGenerationScope);

    const epochAtGeneration =
        localGenerationEpoch ||
        scopeEpoch;

    if (
        generationServerReadyId ===
        generationId
    ) {
        return true;
    }

    if (
        !localGenerationMatches(
            generationId,
            scopeAtGeneration,
        )
    ) {
        return false;
    }

    if (
        generationStartPromise &&
        generationStartPromiseId ===
            generationId
    ) {
        return await generationStartPromise;
    }

    generationStartPromiseId =
        generationId;

    generationStartPromise =
        (async () => {
            let lastError = null;

            for (
                let attempt = 0;
                attempt < 10;
                attempt += 1
            ) {
                try {
                    if (
                        !localGenerationMatches(
                            generationId,
                            scopeAtGeneration,
                        )
                    ) {
                        return false;
                    }

                    const result =
                        await api(
                            '/generation/started',
                            'POST',
                            {
                                scope:
                                    scopeAtGeneration,
                                clientId,
                                deviceId,
                                generationId,
                            },
                        );

                    if (
                        !localGenerationMatches(
                            generationId,
                            scopeAtGeneration,
                        )
                    ) {
                        return false;
                    }

                    const current =
                        result.state
                            ?.generation ||
                        null;

                    if (
                        !current ||
                        current.generationId !==
                            generationId ||
                        !generationIsMine(
                            current,
                        )
                    ) {
                        return false;
                    }

                    serverState =
                        result.state;

                    localGeneration =
                        clone(current);

                    generationServerReadyId =
                        generationId;

                    generationHeartbeatFailures = 0;
                    updateGenerationUi();

                    return true;
                } catch (error) {
                    lastError = error;

                    if (
                        error?.status ===
                            409 &&
                        error?.payload?.state
                    ) {
                        const state =
                            error.payload.state;

                        serverState = state;
                        baseSnapshot = clone(
                            state.snapshot,
                        );

                        const current =
                            state.generation;

                        if (
                            current?.generationId ===
                                generationId &&
                            generationIsMine(
                                current,
                            ) &&
                            [
                                'started',
                                'streaming',
                            ].includes(
                                current.phase,
                            )
                        ) {
                            localGeneration =
                                clone(current);

                            generationServerReadyId =
                                generationId;

                            return true;
                        }

                        if (
                            current?.generationId &&
                            current.generationId !==
                                generationId
                        ) {
                            return false;
                        }
                    }

                    await sleep(
                        Math.min(
                            250 *
                                2 ** attempt,
                            1500,
                        ),
                    );
                }
            }

            log(
                'generation start retries exhausted',
                lastError,
            );

            return false;
        })();

    try {
        const started =
            await generationStartPromise;

        if (
            !started &&
            localGenerationMatches(
                generationId,
                scopeAtGeneration,
            )
        ) {
            scheduleGenerationStartRetry(
                generationId,
                1000,
            );
        }

        return started;
    } finally {
        if (
            generationStartPromiseId ===
            generationId
        ) {
            generationStartPromise = null;
            generationStartPromiseId = null;
        }
    }
}

async function coordinatedGenerateInterceptor(
    chat,
    contextSize,
    abort,
    type,
) {
    refreshLiveContext();

    if (
        !settings.enabled ||
        !settings.coordinateGeneration ||
        applyingRemoteDepth > 0
    ) {
        return;
    }

    if (!currentScope) {
        await switchScope(
            'generation-no-scope',
        );

        if (!currentScope || !serverState) {
            abort(false);
            statusText(
                'Multi-Client Sync is not connected to this chat yet.',
                true,
            );
            return;
        }
    }

    const scopeAtClaim =
        clone(currentScope);

    const epochAtClaim =
        scopeEpoch;

    if (!serverState) {
        abort(false);
        statusText(
            'Multi-Client Sync is not connected to this chat.',
            true,
        );
        return;
    }

    if (generationClaimInFlightId) {
        abort(false);
        return;
    }

    if (!nativeScopeStable(scopeAtClaim)) {
        const stable =
            await waitForNativeScope(
                scopeAtClaim,
                2500,
                75,
            );

        if (!stable) {
            warn(
                '[MCS] generation blocked because native chat scope did not stabilize',
            );

            abort(false);
            return;
        }
    }

    let existing =
        serverState?.generation ||
        null;

    if (
        existing &&
        !localGeneration
    ) {
        if (
            generationIsMine(existing) &&
            generationClaimInFlightId ===
                existing.generationId
        ) {
            await sleep(25);
            existing =
                serverState?.generation ||
                existing;
        } else if (
            generationIsMine(existing) &&
            generationIsStaleOwned(existing)
        ) {
            try {
                const cleared =
                    await api(
                        '/generation/terminal',
                        'POST',
                        {
                            scope:
                                scopeAtClaim,
                            clientId,
                            deviceId,
                            generationId:
                                existing.generationId,
                            phase: 'stopped',
                            snapshot: clone(
                                serverState
                                    ?.snapshot ||
                                {
                                    messages: [],
                                    metadata: {},
                                },
                            ),
                        },
                    );

                serverState =
                    cleared.state;

                baseSnapshot =
                    clone(
                        cleared.state.snapshot,
                    );

                rememberTerminatedGeneration(
                    existing.generationId,
                );
            } catch (error) {
                warn(
                    'failed to clear stale same-client generation before new generation',
                    error,
                );

                abort(false);
                return;
            }

            existing =
                serverState?.generation ||
                null;
        }

        if (
            existing &&
            !generationIsMine(existing)
        ) {
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

    if (localGeneration) {
        abort(false);

        statusText(
            generationTerminalPhase
                ? 'Finishing the current shared generation…'
                : 'A shared generation is already active in this tab.',
            true,
        );

        return;
    }

    const generationId =
        newId();

    generationClaimInFlightId =
        generationId;

    let desired = null;

    let claimBase =
        clone(
            baseSnapshot ||
            serverState?.snapshot ||
            {
                messages: [],
                metadata: {},
            },
        );

    let revision =
        Number(
            serverState?.revision ||
            0,
        );

    let claimResult = null;

    try {
        const idsReady =
            await ensureIdsPersisted(
                scopeAtClaim,
            );

        if (
            !idsReady ||
            !currentScopeGuard(
                epochAtClaim,
            )
        ) {
            abort(false);
            return;
        }

        desired =
            syncSnapshot(
                durableSnapshot(),
            );

        for (
            let attempt = 0;
            attempt < 4;
            attempt += 1
        ) {
            if (
                !currentScopeGuard(
                    epochAtClaim,
                ) ||
                makeScopeKey(
                    currentScope,
                ) !==
                    makeScopeKey(
                        scopeAtClaim,
                    ) ||
                !nativeScopeStable(
                    scopeAtClaim,
                )
            ) {
                abort(false);
                return;
            }

            try {
                claimResult =
                    await api(
                        '/generation/claim',
                        'POST',
                        {
                            scope:
                                scopeAtClaim,
                            clientId,
                            deviceId,
                            opId: newId(),
                            generationId,
                            generationType:
                                String(
                                    type ||
                                        'normal',
                                ),
                            baseRevision:
                                revision,
                            snapshot: desired,
                        },
                    );

                break;
            } catch (error) {
                const payload =
                    error?.payload;

                if (
                    error?.status ===
                        409 &&
                    payload?.state
                ) {
                    if (
                        payload.error ===
                        'generation_active'
                    ) {
                        const other =
                            payload.state
                                .generation;

                        if (
                            other?.generationId ===
                            generationId
                        ) {
                            claimResult =
                                payload;
                            break;
                        }

                        if (
                            other &&
                            generationIsMine(
                                other,
                            ) &&
                            generationIsStaleOwned(
                                other,
                            )
                        ) {
                            try {
                                const cleared =
                                    await api(
                                        '/generation/terminal',
                                        'POST',
                                        {
                                            scope:
                                                scopeAtClaim,
                                            clientId,
                                            deviceId,
                                            generationId:
                                                other.generationId,
                                            phase:
                                                'stopped',
                                            snapshot:
                                                clone(
                                                    payload
                                                        .state
                                                        .snapshot,
                                                ),
                                        },
                                    );

                                serverState =
                                    cleared.state;

                                baseSnapshot =
                                    clone(
                                        cleared
                                            .state
                                            .snapshot,
                                    );

                                rememberTerminatedGeneration(
                                    other.generationId,
                                );

                                revision =
                                    Number(
                                        cleared
                                            .state
                                            .revision,
                                    );

                                claimBase =
                                    clone(
                                        cleared
                                            .state
                                            .snapshot,
                                    );

                                desired =
                                    syncSnapshot(
                                        durableSnapshot(),
                                    );

                                continue;
                            } catch (clearError) {
                                warn(
                                    'stale generation cleanup after claim conflict failed',
                                    clearError,
                                );

                                abort(false);
                                return;
                            }
                        }

                        serverState =
                            payload.state;

                        baseSnapshot =
                            clone(
                                payload.state.snapshot,
                            );

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

                    const merged =
                        mergeSnapshots(
                            claimBase,
                            desired,
                            payload.state.snapshot,
                        );

                    serverState =
                        payload.state;

                    baseSnapshot =
                        clone(
                            payload.state.snapshot,
                        );

                    desired = merged;
                    claimBase =
                        clone(
                            payload.state.snapshot,
                        );

                    revision =
                        Number(
                            payload.state.revision,
                        );

                    continue;
                }

                throw error;
            }
        }

        if (!claimResult) {
            abort(false);
            return;
        }

        if (
            !currentScopeGuard(
                epochAtClaim,
            ) ||
            makeScopeKey(
                currentScope,
            ) !==
                makeScopeKey(
                    scopeAtClaim,
                ) ||
            !nativeScopeStable(
                scopeAtClaim,
            )
        ) {
            try {
                await api(
                    '/generation/terminal',
                    'POST',
                    {
                        scope:
                            scopeAtClaim,
                        clientId,
                        deviceId,
                        generationId,
                        phase: 'stopped',
                        snapshot: clone(
                            claimResult
                                .state
                                ?.snapshot ||
                            claimBase,
                        ),
                    },
                );
            } catch {
                /* best effort */
            }

            abort(false);
            return;
        }

        const claimed =
            claimResult
                .state
                ?.generation;

        if (
            !claimed ||
            claimed.generationId !==
                generationId ||
            !generationIsMine(
                claimed,
            )
        ) {
            abort(false);
            return;
        }

        serverState =
            claimResult.state;

        baseSnapshot =
            clone(
                claimResult.state.snapshot,
            );

        localGeneration =
            clone(claimed);

        localGenerationScope =
            clone(scopeAtClaim);

        localGenerationEpoch =
            epochAtClaim;

        localGenerationBaseSnapshot =
            clone(baseSnapshot);

        localGenerationBaseRevision =
            Number(
                claimResult
                    .state
                    .revision ||
                0,
            );

        localGenerationLastSnapshot =
            clone(desired);

        localStreamMessageId =
            null;

        localStreamMessageIndex =
            null;

        generationClaimedThisPage =
            true;

        generationTerminalPhase =
            null;

        remoteStopGenerationId =
            null;

        lastTerminatedGenerationId =
            null;

        markLocalDirty(
            scopeAtClaim,
        );

        updateGenerationUi();

        startGenerationHeartbeat(
            epochAtClaim,
        );

        const started =
            await ensureGenerationStarted();

        if (!started) {
            // Do not abort a valid native ST generation simply because the
            // coordination endpoint is temporarily unreachable. Keep the
            // lease/local generation alive and retry the start handshake.
            statusText(
                'Reconnecting shared generation…',
            );

            renderBanner(
                'Reconnecting shared generation…',
            );

            scheduleGenerationStartRetry(
                generationId,
                500,
            );

            updateGenerationUi();
            return;
        }

        if (
            !localGeneration ||
            localGeneration.generationId !==
                generationId ||
            generationServerReadyId !==
                generationId
        ) {
            statusText(
                'Reconnecting shared generation…',
            );

            scheduleGenerationStartRetry(
                generationId,
                500,
            );

            return;
        }
    } catch (error) {
        warn(
            'generation claim failed',
            error,
        );

        if (
            localGeneration?.generationId ===
            generationId
        ) {
            try {
                await releaseGenerationClaim(
                    'stopped',
                );
            } catch {
                /* ignore */
            }
        }

        abort(false);
        return;
    } finally {
        if (
            generationClaimInFlightId ===
            generationId
        ) {
            generationClaimInFlightId =
                null;
        }
    }
}

async function onGenerationStarted() {
    if (!localGeneration || !currentScope) return;

    try {
        const started =
            await ensureGenerationStarted();

        if (!started) {
            scheduleGenerationStartRetry(
                localGeneration.generationId,
                1000,
            );
        }
    } catch (error) {
        warn(
            'generation_started failed',
            error,
        );
    }
}

function scheduleGenerationStream(
    delayOverride = null,
) {
    if (
        streamTimer ||
        !pendingStream ||
        !localGeneration ||
        !currentScope
    ) {
        return;
    }

    if (
        terminalizingGenerationId
    ) {
        return;
    }

    const delay =
        delayOverride != null
            ? Math.max(
                0,
                Number(
                    delayOverride,
                ) || 0,
            )
            : Math.max(
                0,
                STREAM_SEND_MS -
                    (
                        Date.now() -
                        lastStreamSentAt
                    ),
            );

    streamTimer = setTimeout(
        async () => {
            streamTimer = null;

            if (
                !pendingStream ||
                !localGeneration ||
                terminalizingGenerationId
            ) {
                return;
            }

            if (
                generationServerReadyId !==
                localGeneration.generationId
            ) {
                const started =
                    await ensureGenerationStarted();

                if (started) {
                    scheduleGenerationStream(
                        0,
                    );
                } else {
                    scheduleGenerationStartRetry(
                        localGeneration.generationId,
                        500,
                    );

                    scheduleGenerationStream(
                        500,
                    );
                }

                return;
            }

            if (streamInFlight) {
                scheduleGenerationStream(
                    STREAM_SEND_MS,
                );

                return;
            }

            const payload =
                pendingStream;

            pendingStream = null;

            const generationId =
                localGeneration.generationId;

            const scopeAtStream =
                clone(
                    localGenerationScope ||
                    currentScope,
                );

            const epochAtStream =
                localGenerationEpoch ||
                scopeEpoch;

            if (
                !scopeAtStream ||
                !currentScopeGuard(
                    epochAtStream,
                )
            ) {
                pendingStream =
                    payload;

                return;
            }

            streamInFlight = true;
            streamInFlightSeq =
                Number(
                    payload.seq || 0,
                );

            const request =
                (async () => {
                    try {
                        const result =
                            await api(
                                '/generation/stream',
                                'POST',
                                {
                                    scope:
                                        scopeAtStream,
                                    clientId,
                                    deviceId,
                                    generationId,
                                    seq:
                                        payload.seq,
                                    message:
                                        payload.message,
                                    messageIndex:
                                        payload.messageIndex,
                                },
                            );

                        if (
                            !localGenerationMatches(
                                generationId,
                                scopeAtStream,
                            )
                        ) {
                            return;
                        }

                        const returned =
                            result.state
                                ?.generation ||
                            null;

                        serverState =
                            result.state;

                        if (
                            returned?.generationId ===
                                generationId &&
                            generationIsMine(
                                returned,
                            )
                        ) {
                            localGeneration =
                                clone(
                                    returned,
                                );

                            generationServerReadyId =
                                generationId;
                        }

                        lastStreamSentAt =
                            Date.now();
                    } catch (error) {
                        const code =
                            error?.payload
                                ?.error ||
                            '';

                        if (
                            code ===
                            'generation_not_started'
                        ) {
                            if (
                                localGenerationMatches(
                                    generationId,
                                    scopeAtStream,
                                )
                            ) {
                                if (
                                    !pendingStream ||
                                    Number(
                                        pendingStream.seq ||
                                        0,
                                    ) <=
                                        Number(
                                            payload.seq ||
                                            0,
                                        )
                                ) {
                                    pendingStream =
                                        payload;
                                }

                                const started =
                                    await ensureGenerationStarted();

                                if (started) {
                                    scheduleGenerationStream(
                                        0,
                                    );
                                } else {
                                    scheduleGenerationStartRetry(
                                        generationId,
                                        500,
                                    );

                                    scheduleGenerationStream(
                                        500,
                                    );
                                }
                            }
                        } else if (
                            code ===
                            'stream_sequence_conflict'
                        ) {
                            const expected =
                                Number(
                                    error
                                        ?.payload
                                        ?.expected ||
                                    0,
                                );

                            if (
                                expected > 0 &&
                                localGenerationMatches(
                                    generationId,
                                    scopeAtStream,
                                )
                            ) {
                                const pending =
                                    pendingStream;

                                if (
                                    Number(
                                        payload.seq,
                                    ) <
                                    expected
                                ) {
                                    localGeneration.seq =
                                        Math.max(
                                            Number(
                                                localGeneration.seq ||
                                                0,
                                            ),
                                            expected -
                                                1,
                                        );

                                    if (pending) {
                                        pendingStream = {
                                            ...pending,
                                            seq: Math.max(
                                                expected,
                                                Number(
                                                    pending.seq ||
                                                    0,
                                                ),
                                            ),
                                        };
                                    }
                                } else {
                                    pendingStream =
                                        pending &&
                                        Number(
                                            pending.seq,
                                        ) >
                                            expected
                                            ? pending
                                            : {
                                                ...payload,
                                                seq:
                                                    expected,
                                            };

                                    localGeneration.seq =
                                        expected -
                                        1;
                                }

                                scheduleGenerationStream(
                                    0,
                                );
                            }
                        } else if (
                            error?.status ===
                                409 &&
                            code ===
                                'generation_not_owned'
                        ) {
                            const confirmed =
                                await api(
                                    '/state',
                                    'POST',
                                    {
                                        scope:
                                            scopeAtStream,
                                        clientId,
                                        deviceId,
                                    },
                                ).catch(
                                    () => null,
                                );

                            const state =
                                confirmed?.state ||
                                null;

                            const g =
                                state
                                    ?.generation;

                            if (
                                g?.generationId ===
                                    generationId &&
                                generationIsMine(g)
                            ) {
                                serverState =
                                    state;

                                localGeneration =
                                    clone(g);

                                generationServerReadyId =
                                    [
                                        'started',
                                        'streaming',
                                    ].includes(
                                        g.phase,
                                    )
                                        ? generationId
                                        : generationServerReadyId;

                                pendingStream =
                                    pendingStream ||
                                    payload;

                                if (
                                    generationServerReadyId
                                ) {
                                    scheduleGenerationStream(
                                        0,
                                    );
                                } else {
                                    scheduleGenerationStartRetry(
                                        generationId,
                                        500,
                                    );
                                }
                            } else if (
                                g &&
                                g.generationId !==
                                    generationId &&
                                generationActive(g)
                            ) {
                                generationMismatchSince =
                                    generationMismatchSince ||
                                    Date.now();

                                // Preserve local generation and let the
                                // generation heartbeat perform deliberate
                                // competing-owner confirmation.
                            } else if (
                                state &&
                                localGenerationMatches(
                                    generationId,
                                    scopeAtStream,
                                )
                            ) {
                                pendingStream =
                                    pendingStream ||
                                    payload;

                                void reacquireGenerationOwnership(
                                    'stream-ownership-loss',
                                ).then(
                                    recovered => {
                                        if (recovered) {
                                            scheduleGenerationStream(
                                                0,
                                            );
                                        }
                                    },
                                );
                            }
                        } else if (
                            error?.status ===
                                403 &&
                            error?.payload
                                ?.error ===
                                'not_member'
                        ) {
                            if (
                                localGenerationMatches(
                                    generationId,
                                    scopeAtStream,
                                )
                            ) {
                                pendingStream =
                                    pendingStream ||
                                    payload;
                            }

                            await openScope(
                                epochAtStream,
                            );

                            scheduleGenerationStream(
                                STREAM_SEND_MS,
                            );
                        } else {
                            if (
                                localGenerationMatches(
                                    generationId,
                                    scopeAtStream,
                                )
                            ) {
                                if (
                                    !pendingStream ||
                                    Number(
                                        pendingStream.seq ||
                                        0,
                                    ) <
                                        Number(
                                            payload.seq ||
                                            0,
                                        )
                                ) {
                                    pendingStream =
                                        payload;
                                }

                                if (
                                    !streamRetryTimer &&
                                    terminalizingGenerationId !==
                                        generationId
                                ) {
                                    streamRetryTimer =
                                        setTimeout(
                                            () => {
                                                streamRetryTimer =
                                                    null;

                                                scheduleGenerationStream();
                                            },
                                            500,
                                        );
                                }
                            }

                            log(
                                'generation stream failed; retrying without aborting local generation',
                                error,
                            );
                        }
                    } finally {
                        streamInFlight =
                            false;

                        if (
                            streamInFlightSeq ===
                            Number(
                                payload.seq ||
                                0,
                            )
                        ) {
                            streamInFlightSeq =
                                0;
                        }
                    }
                })();

            streamInFlightPromise =
                request;

            try {
                await request;
            } finally {
                if (
                    streamInFlightPromise ===
                    request
                ) {
                    streamInFlightPromise =
                        null;
                }

                if (
                    pendingStream &&
                    localGeneration &&
                    generationServerReadyId ===
                        localGeneration.generationId &&
                    !terminalizingGenerationId
                ) {
                    if (streamRetryTimer) {
                        clearTimeout(
                            streamRetryTimer,
                        );

                        streamRetryTimer =
                            null;
                    }

                    scheduleGenerationStream();
                }
            }
        },
        delay,
    );
}

function captureLocalStream() {
    if (
        terminalizingGenerationId ||
        !localGeneration ||
        !localGenerationScope ||
        !ctx?.chat?.length
    ) {
        return;
    }

    if (
        !currentScope ||
        makeScopeKey(currentScope) !==
            makeScopeKey(
                localGenerationScope,
            )
    ) {
        return;
    }

    if (
        !nativeScopeStable(
            localGenerationScope,
        )
    ) {
        return;
    }

    const messages =
        ctx.chat;

    let index =
        Number.isInteger(
            ctx.streamingProcessor
                ?.messageId,
        )
            ? Number(
                ctx.streamingProcessor
                    .messageId,
            )
            : -1;

    if (
        index < 0 ||
        index >= messages.length ||
        messages[index]?.is_user ||
        messages[index]?.is_system
    ) {
        if (localStreamMessageId) {
            index =
                messages.findIndex(
                    message =>
                        messageId(message) ===
                        localStreamMessageId,
                );
        }
    }

    if (
        index < 0 ||
        index >= messages.length
    ) {
        for (
            let i =
                messages.length - 1;
            i >= 0;
            i -= 1
        ) {
            if (
                !messages[i]?.is_user &&
                !messages[i]?.is_system
            ) {
                index = i;
                break;
            }
        }
    }

    if (index < 0) return;

    ensureMessageIds(messages);

    const message =
        clone(messages[index]);

    const id =
        messageId(message);

    if (!id) return;

    localGenerationLastSnapshot =
        syncSnapshot(
            durableSnapshot(),
        );

    localStreamMessageId =
        id;

    localStreamMessageIndex =
        index;

    const previousSeq =
        Number(
            localGeneration.seq ||
            0,
        );

    const queuedSeq =
        Number(
            pendingStream?.seq ||
            0,
        );

    const inFlightNextSeq =
        streamInFlightSeq > 0
            ? streamInFlightSeq + 1
            : 0;

    const seq =
        Math.max(
            previousSeq + 1,
            queuedSeq,
            inFlightNextSeq,
        );

    pendingStream = {
        seq,
        message,
        messageIndex: index,
    };

    if (
        generationServerReadyId ===
        localGeneration.generationId
    ) {
        scheduleGenerationStream();
    } else {
        void ensureGenerationStarted();
        scheduleGenerationStartRetry(
            localGeneration.generationId,
            250,
        );
    }
}

async function releaseGenerationClaim(
    phase = 'stopped',
) {
    if (
        !localGeneration ||
        !localGenerationScope
    ) {
        return false;
    }

    const generation =
        clone(localGeneration);

    const scopeAtGeneration =
        clone(localGenerationScope);

    terminalizingGenerationId =
        generation.generationId;

    try {
        try {
            const result =
                await api(
                    '/generation/terminal',
                    'POST',
                    {
                        scope:
                            scopeAtGeneration,
                        clientId,
                        deviceId,
                        generationId:
                            generation.generationId,
                        phase,
                        snapshot:
                            nativeScopeStable(
                                scopeAtGeneration,
                            )
                                ? syncSnapshot(
                                    durableSnapshot(),
                                )
                                : clone(
                                    localGenerationLastSnapshot ||
                                    serverState
                                        ?.snapshot ||
                                    localGenerationBaseSnapshot ||
                                    {
                                        messages: [],
                                        metadata: {},
                                    },
                                ),
                    },
                );

            serverState =
                result.state;

            baseSnapshot =
                clone(
                    result.state.snapshot,
                );

            rememberTerminatedGeneration(
                generation.generationId,
            );

            clearLocalDirty(
                scopeAtGeneration,
            );

            return true;
        } catch (error) {
            if (
                error?.status ===
                    409 &&
                error?.payload?.state
            ) {
                serverState =
                    error.payload.state;

                baseSnapshot =
                    clone(
                        error.payload.state.snapshot,
                    );

                return !error.payload
                    .state
                    .generation;
            }

            warn(
                'generation claim release failed',
                error,
            );

            return false;
        }
    } finally {
        clearLocalGenerationState();
        updateGenerationUi();
    }
}

async function sendGenerationTerminal(
    phase = 'completed',
) {
    if (
        !localGeneration ||
        !localGenerationScope
    ) {
        return;
    }

    if (
        terminalizingGenerationId ===
        localGeneration.generationId
    ) {
        return;
    }

    const g =
        clone(localGeneration);

    const scopeAtGeneration =
        clone(localGenerationScope);

    const epochAtGeneration =
        localGenerationEpoch ||
        scopeEpoch;

    terminalizingGenerationId =
        g.generationId;

    try {
        if (
            generationStartPromiseId ===
                g.generationId &&
            generationStartPromise
        ) {
            try {
                await generationStartPromise;
            } catch {
                /* ignore */
            }
        }

        if (streamInFlightPromise) {
            try {
                await Promise.race([
                    streamInFlightPromise,
                    sleep(2500),
                ]);
            } catch {
                /* ignore */
            }
        }

        await sleep(60);

        const snapshot =
            nativeScopeStable(
                scopeAtGeneration,
            )
                ? syncSnapshot(
                    durableSnapshot(),
                )
                : clone(
                    localGenerationLastSnapshot ||
                    serverState?.snapshot ||
                    localGenerationBaseSnapshot ||
                    {
                        messages: [],
                        metadata: {},
                    },
                );

        let succeeded = false;
        let lastError = null;

        for (
            let attempt = 0;
            attempt < 4;
            attempt += 1
        ) {
            try {
                const result =
                    await api(
                        '/generation/terminal',
                        'POST',
                        {
                            scope:
                                scopeAtGeneration,
                            clientId,
                            deviceId,
                            generationId:
                                g.generationId,
                            phase,
                            snapshot,
                        },
                    );

                if (
                    scopeKeyValue !==
                    makeScopeKey(
                        scopeAtGeneration,
                    )
                ) {
                    return;
                }

                serverState =
                    result.state;

                baseSnapshot =
                    clone(
                        result.state.snapshot,
                    );

                rememberTerminatedGeneration(
                    g.generationId,
                );

                clearLocalDirty(
                    scopeAtGeneration,
                );

                succeeded = true;
                break;
            } catch (error) {
                lastError = error;

                if (
                    error?.status ===
                        409 &&
                    error?.payload?.state
                ) {
                    serverState =
                        error.payload.state;

                    baseSnapshot =
                        clone(
                            error.payload.state.snapshot,
                        );

                    if (
                        error.payload.state.generation &&
                        error.payload.state
                            .generation
                            .generationId !==
                            g.generationId
                    ) {
                        break;
                    }

                    if (
                        !error.payload.state
                            .generation
                    ) {
                        rememberTerminatedGeneration(
                            g.generationId,
                        );
                        break;
                    }
                }

                if (attempt < 3) {
                    await sleep(
                        200 *
                            (attempt + 1),
                    );
                }
            }
        }

        if (!succeeded) {
            try {
                const stateResult =
                    await api(
                        '/state',
                        'POST',
                        {
                            scope:
                                scopeAtGeneration,
                            clientId,
                            deviceId,
                        },
                    );

                const state =
                    stateResult.state;

                if (!state.generation) {
                    const recoveryBase =
                        clone(
                            localGenerationBaseSnapshot ||
                            baseSnapshot ||
                            {
                                messages: [],
                                metadata: {},
                            },
                        );

                    const mergedRecovery =
                        mergeSnapshots(
                            recoveryBase,
                            snapshot,
                            state.snapshot,
                        );

                    if (
                        !deepEqual(
                            mergedRecovery,
                            state.snapshot,
                        )
                    ) {
                        const recovered =
                            await sendSnapshotDirect(
                                mergedRecovery,
                                Number(
                                    state.revision,
                                ),
                                newId(),
                                scopeAtGeneration,
                            );

                        serverState =
                            recovered.state;

                        baseSnapshot =
                            clone(
                                recovered.state.snapshot,
                            );
                    } else {
                        serverState =
                            state;

                        baseSnapshot =
                            clone(
                                state.snapshot,
                            );
                    }

                    clearLocalDirty(
                        scopeAtGeneration,
                    );

                    rememberTerminatedGeneration(
                        g.generationId,
                    );

                    succeeded = true;
                }
            } catch (recoveryError) {
                lastError =
                    recoveryError;
            }
        }

        if (
            !succeeded &&
            lastError
        ) {
            warn(
                'generation terminal failed',
                lastError,
            );

            if (
                scopeKeyValue ===
                makeScopeKey(
                    scopeAtGeneration,
                )
            ) {
                await enqueueSnapshot(
                    snapshot,
                    Number(
                        serverState?.revision ||
                        0,
                    ),
                    localGenerationBaseSnapshot ||
                        baseSnapshot,
                    scopeAtGeneration,
                    'generation-terminal',
                    g.generationId,
                ).catch(
                    queueError =>
                        warn(
                            'terminal snapshot queue failed',
                            queueError,
                        ),
                );

                scheduleQueueFlushRetry(
                    1500,
                );
            }
        }
    } finally {
        if (generationStartRetryTimer) {
            clearTimeout(
                generationStartRetryTimer,
            );
            generationStartRetryTimer =
                null;
        }

        if (
            currentScopeGuard(
                epochAtGeneration,
            ) ||
            makeScopeKey(
                currentScope,
            ) ===
                makeScopeKey(
                    scopeAtGeneration,
                )
        ) {
            clearLocalGenerationState();
            updateGenerationUi();
        } else {
            clearLocalGenerationState();
        }

        if (
            generationTerminalPhase ===
            phase
        ) {
            generationTerminalPhase =
                null;
        }
    }

    await flushQueue();

    if (!nativeRestoreInProgress) {
        void switchScope(
            pendingScopeSwitchReason ||
                'post-generation-terminal',
        );

        pendingScopeSwitchReason =
            '';
    }
}

async function handleRemoteStopEvent(
    data,
) {
    if (!currentScope) return;

    const eventScope =
        data?.scope || null;

    if (
        eventScope &&
        makeScopeKey(eventScope) !==
            makeScopeKey(currentScope)
    ) {
        return;
    }

    const eventGeneration =
        data?.generation || null;

    const generationId =
        eventGeneration?.generationId ||
        data?.generationId ||
        serverState?.generation
            ?.generationId ||
        null;

    if (!generationId) return;

    if (
        !localGeneration ||
        localGeneration.generationId !==
            generationId
    ) {
        return;
    }

    if (
        eventGeneration &&
        eventGeneration.generationId !==
            localGeneration.generationId
    ) {
        return;
    }

    if (
        generationIsMine(
            eventGeneration,
        ) === false &&
        eventGeneration
    ) {
        // A remote stop event must target the local generator lease.
        // The event itself may be emitted to every subscribed client,
        // so keep the exact generation-id guard above.
    }

    generationTerminalPhase =
        'stopped';

    remoteStopGenerationId =
        generationId;

    clearGenerationTerminalTimer();

    renderBanner(
        'Stopping generation…',
    );

    try {
        ctx?.stopGeneration?.();
    } catch (error) {
        warn(
            'SillyTavern stopGeneration failed',
            error,
        );
    }
}

function scheduleDeferredStreamCapture() {
    if (
        streamCaptureTimer ||
        !localGeneration
    ) {
        return;
    }

    streamCaptureTimer =
        setTimeout(() => {
            streamCaptureTimer =
                null;

            if (localGeneration) {
                captureLocalStream();
            }
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

async function onGenerationEnded() {
    if (!localGeneration) return;
    if (generationTerminalPhase === 'stopped') return;

    const generationId =
        localGeneration.generationId;

    generationTerminalPhase =
        'completed';

    clearGenerationTerminalTimer();

    generationTerminalTimer =
        setTimeout(() => {
            generationTerminalTimer =
                null;

            if (
                !localGeneration ||
                localGeneration.generationId !==
                    generationId
            ) {
                return;
            }

            sendGenerationTerminal(
                'completed',
            ).catch(
                error =>
                    warn(
                        'completed terminal failed',
                        error,
                    ),
            );
        }, 100);
}

async function onGenerationStopped() {
    if (!localGeneration) return;

    const generationId =
        localGeneration.generationId;

    if (
        generationTerminalPhase ===
        'completed'
    ) {
        return;
    }

    generationTerminalPhase =
        'stopped';

    clearGenerationTerminalTimer();

    generationTerminalTimer =
        setTimeout(() => {
            generationTerminalTimer =
                null;

            if (
                !localGeneration ||
                localGeneration.generationId !==
                    generationId
            ) {
                return;
            }

            sendGenerationTerminal(
                'stopped',
            ).catch(
                error =>
                    warn(
                        'stopped terminal failed',
                        error,
                    ),
            );
        }, 100);
}

function publishAfterLocalEvent(
    _event = undefined,
    {
        allowDuringGeneration = false,
    } = {},
) {
    if (
        applyingRemoteDepth > 0 ||
        !currentScope ||
        !settings.enabled ||
        !syncEnabled() ||
        terminalizingGenerationId
    ) {
        return Promise.resolve(false);
    }

    refreshLiveContext();

    const scopeAtEvent =
        clone(currentScope);

    const epochAtEvent =
        scopeEpoch;

    if (
        !nativeScopeStable(
            scopeAtEvent,
        )
    ) {
        if (localGeneration) {
            log(
                '[MCS] local event arrived during transient generation context swap; deferring sync',
            );

            return Promise.resolve(
                false,
            );
        }

        return switchScope(
            'local-event-context-mismatch',
        );
    }

    markLocalDirty(
        scopeAtEvent,
    );

    const snapshotAtEvent =
        syncSnapshot(
            durableSnapshot(),
        );

    const run =
        publishChain.then(
            async () => {
                if (
                    scopeEpoch !==
                        epochAtEvent ||
                    scopeKeyValue !==
                        makeScopeKey(
                            scopeAtEvent,
                        )
                ) {
                    return false;
                }

                if (
                    !nativeScopeStable(
                        scopeAtEvent,
                    )
                ) {
                    return false;
                }

                if (
                    localGeneration &&
                    makeScopeKey(
                        localGenerationScope,
                    ) ===
                        makeScopeKey(
                            scopeAtEvent,
                        ) &&
                    !allowDuringGeneration
                ) {
                    return false;
                }

                if (
                    localGeneration &&
                    localGeneration.phase ===
                        'streaming' &&
                    allowDuringGeneration
                ) {
                    return false;
                }

                try {
                    if (localGeneration) {
                        localGenerationLastSnapshot =
                            clone(
                                snapshotAtEvent,
                            );
                    }

                    return await publishLocalSnapshot(
                        snapshotAtEvent,
                        {
                            allowDuringGeneration,
                            scope:
                                scopeAtEvent,
                        },
                    );
                } catch (error) {
                    warn(
                        'publish after local event failed',
                        error,
                    );

                    return false;
                }
            },
        );

    publishChain =
        run.then(
            () => undefined,
            error => {
                warn(
                    'local publish chain failed',
                    error,
                );
            },
        );

    return run;
}

async function handleChatLifecycleEvent() {
    await sleep(150);
    refreshLiveContext();

    if (nativeRestoreInProgress) return;

    if (localGeneration) {
        pendingScopeSwitchReason =
            'chat-lifecycle';

        return;
    }

    await switchScope(
        'chat-lifecycle',
    );
}

function unwireEvents() {
    const es = ctx?.eventSource;

    if (!es) {
        registeredEventHandlers.length =
            0;

        return;
    }

    for (
        const [eventType, handler] of
        registeredEventHandlers
    ) {
        try {
            if (
                typeof es.removeListener ===
                'function'
            ) {
                es.removeListener(
                    eventType,
                    handler,
                );
            } else if (
                typeof es.off ===
                'function'
            ) {
                es.off(
                    eventType,
                    handler,
                );
            }
        } catch {
            /* ignore */
        }
    }

    registeredEventHandlers.length =
        0;
}

function wireEvents() {
    unwireEvents();
    refreshLiveContext();

    const types =
        ctx?.eventTypes || {};

    const es =
        ctx?.eventSource;

    const listen = (
        eventType,
        fn,
    ) => {
        if (
            !eventType ||
            !es?.on
        ) {
            return;
        }

        es.on(
            eventType,
            fn,
        );

        registeredEventHandlers.push([
            eventType,
            fn,
        ]);
    };

    listen(
        types.APP_INITIALIZED,
        () =>
            switchScope(
                'APP_INITIALIZED',
            ),
    );

    listen(
        types.APP_READY,
        () =>
            switchScope(
                'APP_READY',
            ),
    );

    listen(
        types.CHAT_CHANGED,
        handleChatLifecycleEvent,
    );

    listen(
        types.CHAT_LOADED,
        handleChatLifecycleEvent,
    );

    listen(
        types.CHAT_CREATED,
        handleChatLifecycleEvent,
    );

    listen(
        types.CHAT_RENAMED,
        handleChatLifecycleEvent,
    );

    listen(
        types.CHAT_DELETED,
        async data => {
            const old =
                typeof data ===
                'string'
                    ? data.replace(
                        /\.jsonl$/,
                        '',
                    )
                    : '';

            if (
                old &&
                currentScope?.chatId ===
                    old &&
                scopeKeyValue
            ) {
                await idbClearScope(
                    scopeKeyValue,
                ).catch(
                    () => {},
                );
            }

            await handleChatLifecycleEvent();
        },
    );

    listen(
        types.GROUP_CHAT_CREATED,
        handleChatLifecycleEvent,
    );

    listen(
        types.GROUP_CHAT_DELETED,
        handleChatLifecycleEvent,
    );

    listen(
        types.MESSAGE_SENT,
        event =>
            publishAfterLocalEvent(
                event,
                {
                    allowDuringGeneration:
                        true,
                },
            ),
    );

    listen(
        types.MESSAGE_RECEIVED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_EDITED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_UPDATED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_DELETED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_SWIPED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_SWIPE_DELETED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_REASONING_EDITED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_REASONING_DELETED,
        publishAfterLocalEvent,
    );

    listen(
        types.MESSAGE_FILE_EMBEDDED,
        publishAfterLocalEvent,
    );

    listen(
        types.FILE_ATTACHMENT_DELETED,
        publishAfterLocalEvent,
    );

    listen(
        types.MEDIA_ATTACHMENT_DELETED,
        publishAfterLocalEvent,
    );

    listen(
        types.IMAGE_SWIPED,
        publishAfterLocalEvent,
    );

    listen(
        types.MORE_MESSAGES_LOADED,
        publishAfterLocalEvent,
    );

    listen(
        types.GENERATION_STARTED,
        onGenerationStarted,
    );

    listen(
        types.STREAM_TOKEN_RECEIVED,
        onStreamToken,
    );

    listen(
        types.STREAM_REASONING_DONE,
        onReasoningDone,
    );

    listen(
        types.TOOL_CALLS_PERFORMED,
        onToolEvent,
    );

    listen(
        types.TOOL_CALLS_RENDERED,
        onToolEvent,
    );

    listen(
        types.GENERATION_ENDED,
        onGenerationEnded,
    );

    listen(
        types.GENERATION_STOPPED,
        onGenerationStopped,
    );

    listen(
        types.GROUP_MEMBER_DRAFTED,
        onStreamToken,
    );

    listen(
        types.GROUP_WRAPPER_STARTED,
        onGenerationStarted,
    );

    listen(
        types.GROUP_WRAPPER_FINISHED,
        onGenerationEnded,
    );
}

function unwireUiGuards() {
    for (
        const [
            type,
            handler,
            capture,
        ] of registeredUiHandlers
    ) {
        try {
            document.removeEventListener(
                type,
                handler,
                capture,
            );
        } catch {
            /* ignore */
        }
    }

    registeredUiHandlers.length =
        0;
}

function wireUiGuards() {
    unwireUiGuards();

    const clickHandler =
        async event => {
            const target =
                event.target instanceof
                Element
                    ? event.target.closest(
                        'button, .menu_button, [role="button"]',
                    )
                    : null;

            if (
                !target ||
                !isRemoteGenerationActive()
            ) {
                return;
            }

            if (
                target.matches(
                    '#send_but, #mes_stop, #option_regenerate, #regenerate_last_message, #swipe_left, #swipe_right',
                )
            ) {
                event.preventDefault();
                event.stopImmediatePropagation();

                if (
                    (
                        target.matches(
                            '#send_but',
                        ) ||
                        target.matches(
                            '#mes_stop',
                        )
                    ) &&
                    settings.remoteStop
                ) {
                    try {
                        await requestRemoteStop();
                    } catch (error) {
                        warn(
                            'remote stop failed',
                            error,
                        );
                    }
                } else if (
                    target.matches(
                        '#send_but',
                    )
                ) {
                    statusText(
                        'Another client is generating this shared chat.',
                        true,
                    );
                }
            }
        };

    const keydownHandler =
        async event => {
            if (
                !isRemoteGenerationActive()
            ) {
                return;
            }

            if (
                event.key !== 'Enter' ||
                event.shiftKey ||
                event.isComposing ||
                event.repeat
            ) {
                return;
            }

            if (
                !(
                    event.target instanceof
                    HTMLTextAreaElement ||
                    event.target instanceof
                    HTMLInputElement
                )
            ) {
                return;
            }

            const isChatInput =
                event.target.id ===
                    'send_textarea' ||
                event.target.closest?.(
                    '#send_form, #send_form_inner',
                );

            if (!isChatInput) return;

            event.preventDefault();
            event.stopImmediatePropagation();

            if (!settings.remoteStop) {
                statusText(
                    'Another client is generating this shared chat.',
                    true,
                );

                return;
            }

            try {
                await requestRemoteStop();
            } catch (error) {
                warn(
                    'remote stop failed',
                    error,
                );
            }
        };

    document.addEventListener(
        'click',
        clickHandler,
        true,
    );

    document.addEventListener(
        'keydown',
        keydownHandler,
        true,
    );

    registeredUiHandlers.push(
        [
            'click',
            clickHandler,
            true,
        ],
        [
            'keydown',
            keydownHandler,
            true,
        ],
    );
}

async function waitForRemoteStopConfirmation(
    scope,
    generationId,
    epoch,
) {
    for (
        let attempt = 0;
        attempt < 8;
        attempt += 1
    ) {
        if (
            !currentScopeGuard(epoch)
        ) {
            return false;
        }

        try {
            const result =
                await api(
                    '/state',
                    'POST',
                    {
                        scope,
                        clientId,
                        deviceId,
                    },
                );

            if (
                !currentScopeGuard(
                    epoch,
                )
            ) {
                return false;
            }

            serverState =
                result.state;

            const generation =
                result.state
                    ?.generation ||
                null;

            if (!generation) {
                rememberTerminatedGeneration(
                    generationId,
                );

                remoteStopInFlight =
                    null;

                remoteStopGenerationId =
                    null;

                updateGenerationUi();

                return true;
            }

            if (
                generation.generationId !==
                generationId
            ) {
                updateGenerationUi();
                return true;
            }

            if (
                generation.stopRequested
            ) {
                remoteStopGenerationId =
                    generationId;

                setRemoteSendButtonMode(
                    true,
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

        await sleep(350);
    }

    return false;
}

async function requestRemoteStop() {
    if (!settings.remoteStop) {
        statusText(
            'Remote Stop is disabled.',
            true,
        );

        return;
    }

    if (localGeneration) {
        generationTerminalPhase =
            'stopped';

        renderBanner(
            'Stopping generation…',
        );

        try {
            ctx?.stopGeneration?.();
        } catch {
            /* ignore */
        }

        return;
    }

    let g =
        serverState?.generation;

    if (!g || !currentScope) {
        await resyncCurrentScope(
            scopeEpoch,
        );

        g =
            serverState?.generation;

        if (
            !g ||
            !currentScope
        ) {
            statusText(
                'No active shared generation found.',
            );

            return;
        }
    }

    if (
        generationLeaseExpired(g)
    ) {
        await resyncCurrentScope(
            scopeEpoch,
        );

        g =
            serverState?.generation;

        if (!g) return;
    }

    if (
        !generationActive(g)
    ) {
        updateGenerationUi();
        return;
    }

    if (
        generationIsMine(g) &&
        !localGeneration
    ) {
        await resyncCurrentScope(
            scopeEpoch,
        );

        g =
            serverState?.generation;

        if (
            !g ||
            generationIsMine(g)
        ) {
            updateGenerationUi();
            return;
        }
    }

    const generationId =
        String(
            g.generationId ||
            '',
        );

    if (!generationId) return;

    if (
        remoteStopInFlight &&
        remoteStopGenerationId ===
            generationId
    ) {
        return remoteStopInFlight;
    }

    const scopeAtRequest =
        clone(currentScope);

    const epochAtRequest =
        scopeEpoch;

    remoteStopGenerationId =
        generationId;

    setRemoteSendButtonMode(
        true,
    );

    statusText(
        'Stop requested…',
    );

    const run =
        (async () => {
            let result = null;

            try {
                result =
                    await api(
                        '/generation/stop',
                        'POST',
                        {
                            scope:
                                scopeAtRequest,
                            clientId,
                            deviceId,
                            generationId,
                            opId: newId(),
                        },
                    );

                if (
                    currentScopeGuard(
                        epochAtRequest,
                    )
                ) {
                    if (
                        result?.state
                    ) {
                        serverState =
                            result.state;
                    }

                    updateGenerationUi();
                }
            } catch (error) {
                if (
                    error?.status ===
                        409 &&
                    error?.payload?.state
                ) {
                    serverState =
                        error.payload.state;

                    const current =
                        serverState?.generation ||
                        null;

                    if (
                        !current ||
                        current.generationId !==
                            generationId
                    ) {
                        return true;
                    }

                    if (
                        current.stopRequested
                    ) {
                        result = {
                            state:
                                serverState,
                        };
                    } else {
                        throw error;
                    }
                } else {
                    throw error;
                }
            }

            // Same-browser fast path. Cross-device Stop is still handled by
            // the server/SSE path below.
            broadcastWake(
                'generation-stop-requested',
                {
                    scope:
                        scopeAtRequest,
                    generationId,
                    generation:
                        clone(
                            result?.state
                                ?.generation ||
                            g,
                        ),
                },
            );

            const confirmed =
                await waitForRemoteStopConfirmation(
                    scopeAtRequest,
                    generationId,
                    epochAtRequest,
                );

            if (
                !confirmed &&
                currentScopeGuard(
                    epochAtRequest,
                )
            ) {
                statusText(
                    'Stop request sent; waiting for the generating client…',
                );

                updateGenerationUi();
            }

            return confirmed;
        })();

    remoteStopInFlight =
        run;

    try {
        return await run;
    } finally {
        if (
            remoteStopInFlight ===
            run
        ) {
            remoteStopInFlight =
                null;
        }

        if (
            currentScopeGuard(
                epochAtRequest,
            )
        ) {
            updateGenerationUi();
        }
    }
}

async function onActivate() {
    ctx =
        SillyTavern.getContext();

    activationInProgress =
        true;

    unwireEvents();
    unwireUiGuards();

    try {
        bc?.close?.();
    } catch {
        /* ignore */
    }

    bc =
        'BroadcastChannel' in window
            ? new BroadcastChannel(
                BC_NAME,
            )
            : null;

    bc?.addEventListener(
        'message',
        message => {
            const data =
                message.data;

            if (
                data?.scopeKey !==
                scopeKeyValue
            ) {
                return;
            }

            if (
                data?.kind ===
                'state' &&
                currentScope
            ) {
                resyncCurrentScope().catch(
                    error =>
                        warn(
                            'BroadcastChannel state resync failed',
                            error,
                        ),
                );

                return;
            }

            if (
                data?.kind ===
                'generation-stop-requested' &&
                currentScope
            ) {
                handleRemoteStopEvent(
                    {
                        scope:
                            data.scope ||
                            currentScope,
                        generationId:
                            data.generationId,
                        generation:
                            data.generation ||
                            null,
                    },
                ).catch(
                    error =>
                        warn(
                            'BroadcastChannel remote stop handling failed',
                            error,
                        ),
                );
            }
        },
    );

    await negotiateClientId();
    await mountSettings();

    // Let SillyTavern own startup chat restoration. The native
    // Auto-load Last Chat setting decides whether ST opens the previous chat.
    // MCS only connects after ST has established whatever context it chose.
    await sleep(250);

    refreshLiveContext();

    activationInProgress =
        false;

    refreshLiveContext();

    wireEvents();
    wireUiGuards();

    globalThis.multiClientSyncGenerateInterceptor =
        coordinatedGenerateInterceptor;

    // Let SillyTavern finish its own Auto-load Last Chat decision first. MCS does
    // not restore chats itself; it only connects to the resulting native scope.
    setTimeout(
        () => {
            switchScope(
                'post-activate',
            ).catch(
                error =>
                    warn(
                        'post-activate scope check failed',
                        error,
                    ),
            );
        },
        900,
    );

    updateGenerationUi();
}

async function onEnable() {
    settings.enabled =
        true;

    saveSettings();
    refreshLiveContext();

    ++scopeEpoch;

    wireEvents();
    wireUiGuards();

    globalThis.multiClientSyncGenerateInterceptor =
        coordinatedGenerateInterceptor;

    currentScope =
        scopeFromContext();

    scopeKeyValue =
        makeScopeKey(
            currentScope,
        );

    if (currentScope) {
        await openScope(
            scopeEpoch,
        );
    } else {
        statusText(
            'Waiting for active chat…',
        );
    }

    updateGenerationUi();
}

async function onDisable() {
    settings.enabled =
        false;

    saveSettings();

    ++scopeEpoch;

    unwireUiGuards();
    unwireEvents();

    delete globalThis
        .multiClientSyncGenerateInterceptor;

    await leaveCurrentScope();

    currentScope = null;
    scopeKeyValue = '';
    generationClaimInFlightId = null;
    generationRecoveryInFlight = null;
    localGenerationBaseRevision = 0;
    clearTerminatedGenerationHistory();
    streamInFlightSeq = 0;
    remoteStopInFlight = null;
    remoteStopGenerationId = null;

    clearLocalDirty();
    setRemoteSendButtonMode(false);

    try {
        bc?.close?.();
    } catch {
        /* ignore */
    }

    bc = null;
}

async function mountSettings() {
    if (settingsPanelMounted) return;

    const host =
        document.querySelector(
            '#extensions_settings',
        ) ||
        document.querySelector(
            '#extensions_settings2',
        );

    if (!host) {
        setTimeout(
            () => mountSettings(),
            1000,
        );

        return;
    }

    settingsPanelMounted =
        true;

    const panel =
        document.createElement(
            'div',
        );

    panel.id =
        'mcs_settings_panel';

    panel.className =
        'mcs-settings';

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

    for (
        const [id, key] of
        Object.entries(map)
    ) {
        const el =
            document.getElementById(id);

        if (!el) continue;

        el.checked =
            !!settings[key];

        el.addEventListener(
            'change',
            async () => {
                settings[key] =
                    !!el.checked;

                saveSettings();

                if (
                    key === 'enabled'
                ) {
                    if (
                        settings.enabled
                    ) {
                        await onEnable();
                    } else {
                        await onDisable();
                    }

                    updateGenerationUi();
                    return;
                }

                if (
                    key === 'autoConnect' &&
                    !settings.autoConnect
                ) {
                    ++scopeEpoch;

                    await leaveCurrentScope();

                    currentScope = null;
                    scopeKeyValue = '';

                    statusText(
                        'Disconnected',
                    );
                } else if (
                    settings.enabled &&
                    settings.autoConnect
                ) {
                    await switchScope(
                        `setting:${key}`,
                    );
                }

                updateGenerationUi();
            },
        );
    }

    document
        .getElementById(
            'mcs_reconnect',
        )
        ?.addEventListener(
            'click',
            async () => {
                try {
                    ++scopeEpoch;

                    const epoch =
                        scopeEpoch;

                    await leaveCurrentScope();

                    currentScope =
                        scopeFromContext();

                    scopeKeyValue =
                        makeScopeKey(
                            currentScope,
                        );

                    if (
                        currentScope &&
                        settings.enabled &&
                        settings.autoConnect
                    ) {
                        await openScope(
                            epoch,
                        );
                    } else {
                        statusText(
                            'No active chat',
                        );
                    }
                } catch (error) {
                    warn(
                        'manual reconnect failed',
                        error,
                    );
                }
            },
        );

    document
        .getElementById(
            'mcs_resync',
        )
        ?.addEventListener(
            'click',
            async () => {
                try {
                    await resyncCurrentScope();
                } catch (error) {
                    warn(
                        'manual resync failed',
                        error,
                    );
                }
            },
        );

    updateGenerationUi();
}

export {
    onActivate,
    onEnable,
    onDisable,
};

globalThis.multiClientSyncGenerateInterceptor =
    coordinatedGenerateInterceptor;