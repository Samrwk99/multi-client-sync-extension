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
let clientId = crypto.randomUUID();
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
let localGenerationScopeKey = '';
let generationServerReadyId = null;
let generationStartPromise = null;
let generationStartPromiseId = null;
let streamTimer = null;
let streamInFlight = false;
let remoteRenderTimer = null;
let lastStreamSentAt = 0;
let pendingStream = null;
let pendingRemoteStream = null;
let terminalizingGenerationId = null;
let scopeRetryTimer = null;
let sseEpoch = 0;
let scopeSwitchChain = Promise.resolve();
let stateApplyChain = Promise.resolve();
let publishChain = Promise.resolve();
let nativeRestoreInProgress = false;
let startupRestoreComplete = false;
let activationInProgress = false;
const registeredEventHandlers = [];
const registeredUiHandlers = [];
let heartbeatTimer = null;
let generationHeartbeatTimer = null;
let sendLockReason = '';
let settingsPanelMounted = false;
let bc = null;
let previousChatId = null;

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

function stableStringify(value) {
    return JSON.stringify(value, (key, val) => forbiddenKeys.has(key) ? undefined : val);
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

function newId() {
    return crypto.randomUUID();
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

function ensureMessageIds(messages) {
    let changed = false;
    const seen = new Set();
    for (const message of messages) {
        if (!message || typeof message !== 'object') continue;
        message.extra = message.extra && typeof message.extra === 'object' ? message.extra : {};
        message.extra.multi_client_sync = message.extra.multi_client_sync && typeof message.extra.multi_client_sync === 'object'
            ? message.extra.multi_client_sync
            : {};
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

function messageId(message) {
    return message?.extra?.multi_client_sync?.messageId || null;
}

function durableMessages() {
    return clone(ctx?.chat || []).map(message => message);
}

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

    const groupId =
        ctx.groupId !== undefined &&
        ctx.groupId !== null &&
        String(ctx.groupId) !== ''
            ? String(ctx.groupId)
            : '';

    const isGroup = !!groupId;
    const sources = getContextChatSources();
    const chatCandidates = [
        sources.selectedChat,
        sources.currentChatId,
        sources.contextChatId,
    ].filter(Boolean);

    if (!chatCandidates.length) return null;

    // During ST chat switching these values can temporarily disagree. Do not
    // join/save anything until the native context has converged.
    const firstChatId = chatCandidates[0];
    if (chatCandidates.some(value => value !== firstChatId)) {
        log('[MCS] native chat identity is transient:', sources);
        return null;
    }

    const chatId = firstChatId;
    if (!chatId) return null;

    let ownerId = '';

    if (isGroup) {
        ownerId = `group:${groupId}`;
    } else {
        const characterId =
            ctx.characterId !== undefined && ctx.characterId !== null
                ? String(ctx.characterId)
                : '';

        const character =
            characterId && Array.isArray(ctx.characters)
                ? ctx.characters[characterId] || null
                : null;

        const ownerAvatar = character?.avatar ? String(character.avatar) : '';
        const ownerName = character?.name ? String(character.name) : '';

        ownerId = ownerAvatar || ownerName || '';
        if (!ownerId) return null;

        // Never treat a character scope as stable unless ST's native chat
        // filename agrees with the selected/current chat. A missing native
        // filename is also transitional and must not be persisted by MCS.
        const nativeChat = character?.chat ? String(character.chat).trim() : '';
        if (!nativeChat || nativeChat !== chatId) {
            log('[MCS] character/chat mismatch during transition:', {
                characterId,
                characterChat: nativeChat,
                chatId,
            });
            return null;
        }
    }

    if (isGroup) {
        const group = Array.isArray(ctx.groups)
            ? ctx.groups.find(item => String(item?.id) === groupId)
            : null;
        const nativeGroupChat = group?.chat_id ? String(group.chat_id).trim() : '';
        if (!nativeGroupChat || nativeGroupChat !== chatId) {
            log('[MCS] group/chat mismatch during transition:', {
                groupId,
                groupChat: nativeGroupChat,
                chatId,
            });
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

async function maybeRestoreLastNativeScope() {
    const saved = readLastScope();
    if (!saved) return false;
    if (!ctx) return false;

    const current = scopeFromContext();
    if (current && makeScopeKey(current) === makeScopeKey(saved)) return false;

    const deadline = Date.now() + 10_000;
    while (Date.now() < deadline) {
        if (saved.kind === 'group') {
            if (Array.isArray(ctx.groups) && ctx.groups.length) break;
        } else if (Array.isArray(ctx.characters) && ctx.characters.length) {
            break;
        }
        await sleep(150);
    }

    try {
        nativeRestoreInProgress = true;

        if (saved.kind === 'group') {
            const groupId = saved.ownerId.startsWith('group:') ? saved.ownerId.slice(6) : saved.ownerId;
            const group = Array.isArray(ctx.groups)
                ? ctx.groups.find(item => String(item?.id) === String(groupId))
                : null;

            if (!group || !Array.isArray(group.chats) || !group.chats.some(chat => String(chat) === saved.chatId)) {
                log('[MCS] saved group scope no longer exists:', saved);
                return false;
            }

            if (typeof ctx.openGroupChat !== 'function') {
                warn('[MCS] SillyTavern does not expose openGroupChat; cannot restore saved group chat.');
                return false;
            }

            await ctx.openGroupChat(groupId, saved.chatId);
        } else {
            const desiredOwner = String(saved.ownerId);
            const index = Array.isArray(ctx.characters)
                ? ctx.characters.findIndex(character =>
                    String(character?.avatar || '') === desiredOwner ||
                    String(character?.name || '') === desiredOwner,
                )
                : -1;

            if (index < 0) {
                log('[MCS] saved character scope no longer exists:', saved);
                return false;
            }

            if (typeof ctx.selectCharacterById !== 'function' || typeof ctx.openCharacterChat !== 'function') {
                warn('[MCS] SillyTavern does not expose the native character chat APIs needed for restore.');
                return false;
            }

            await ctx.selectCharacterById(index, { switchMenu: false });
            await ctx.openCharacterChat(saved.chatId);
        }

        // Let ST finish the event cascade and make the context internally consistent.
        await sleep(50);
        const restored = scopeFromContext();
        if (restored && makeScopeKey(restored) === makeScopeKey(saved)) {
            writeLastScope(restored);
            log('[MCS] restored last native scope:', restored);
            return true;
        }

        log('[MCS] native scope restore did not converge:', {
            saved,
            current: scopeFromContext(),
        });
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
        const request = indexedDB.open(DB_NAME, DB_VERSION);
        request.onupgradeneeded = () => {
            const db = request.result;
            if (!db.objectStoreNames.contains('ops')) {
                const store = db.createObjectStore('ops', { keyPath: 'id' });
                store.createIndex('scopeKey', 'scopeKey', { unique: false });
            } else {
                const store = request.transaction.objectStore('ops');
                if (!store.indexNames.contains('scopeKey')) {
                    store.createIndex('scopeKey', 'scopeKey', { unique: false });
                }
            }
        };
        request.onsuccess = () => {
            const db = request.result;
            db.onversionchange = () => db.close();
            resolve(db);
        };
        request.onerror = () => reject(request.error);
    });
}

async function idbPut(value) {
    if (!value?.id || !value?.scopeKey) throw new Error('Invalid offline queue entry');
    const db = await openDb();
    return new Promise((resolve, reject) => {
        const tx = db.transaction('ops', 'readwrite');
        tx.objectStore('ops').put(value);
        tx.oncomplete = () => {
            db.close();
            resolve();
        };
        tx.onerror = () => {
            const error = tx.error || new Error('IndexedDB write failed');
            db.close();
            reject(error);
        };
        tx.onabort = () => {
            const error = tx.error || new Error('IndexedDB transaction aborted');
            db.close();
            reject(error);
        };
    });
}

async function idbList(scopeKey) {
    if (!scopeKey) return [];
    const db = await openDb();
    return new Promise((resolve, reject) => {
        const tx = db.transaction('ops', 'readonly');
        const req = tx.objectStore('ops').index('scopeKey').getAll(scopeKey);
        req.onsuccess = () => resolve(req.result.sort((a, b) => a.createdAt - b.createdAt));
        req.onerror = () => reject(req.error);
        tx.oncomplete = () => db.close();
        tx.onerror = () => db.close();
    });
}

async function idbDelete(id) {
    if (!id) return;
    const db = await openDb();
    return new Promise((resolve, reject) => {
        const tx = db.transaction('ops', 'readwrite');
        tx.objectStore('ops').delete(id);
        tx.oncomplete = () => {
            db.close();
            resolve();
        };
        tx.onerror = () => {
            const error = tx.error || new Error('IndexedDB delete failed');
            db.close();
            reject(error);
        };
    });
}

async function idbClearScope(scopeKey) {
    const rows = await idbList(scopeKey);
    for (const row of rows) await idbDelete(row.id);
}

async function api(path, method = 'GET', body = undefined, query = '') {
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

function generationIsMine(generation) {
    return !!generation && generation.clientId === clientId && generation.deviceId === deviceId;
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

        if (deepEqual(l, b)) {
            out[key] = clone(r);
        } else if (deepEqual(r, b)) {
            out[key] = clone(l);
        } else if (l && r && typeof l === 'object' && typeof r === 'object') {
            out[key] = mergeMetadata(b, l, r);
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
        const bv = bm.get(id);
        const lv = lm.get(id);
        const rv = rm.get(id);
        let chosen;

        if (!lv && bv) chosen = null;
        else if (!rv && bv) chosen = null;
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

    merged.sort((a, z) =>
        (rank.get(messageId(a)) ?? 1e9) - (rank.get(messageId(z)) ?? 1e9),
    );

    return {
        messages: merged,
        metadata: mergeMetadata(b.metadata, l.metadata, r.metadata),
    };
}

async function safeNativeSave(expectedScope = currentScope) {
    if (!ctx || !expectedScope || !nativeScopeStable(expectedScope)) {
        log('[MCS] skipped native save because native scope is not stable', expectedScope);
        return false;
    }

    try {
        await ctx.saveChat?.();
        return true;
    } catch (error) {
        warn('native chat save failed', error);
        return false;
    }
}

async function applySnapshot(snapshot, { save = false, render = true, expectedScope = currentScope } = {}) {
    const normalized = normalizeSnapshot(snapshot);
    if (!ctx || !expectedScope || !nativeScopeStable(expectedScope)) {
        log('[MCS] refused snapshot apply because native scope is not stable', expectedScope);
        return false;
    }

    const expectedKey = makeScopeKey(expectedScope);
    const epochAtStart = scopeEpoch;

    applyingRemoteDepth += 1;
    try {
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
                await Promise.resolve(ctx.printMessages?.());
            } catch (error) {
                log('printMessages failed', error);
            }
        }

        // MCS keeps shared state on the server. Avoid writing remote/stale
        // in-memory state into ST's native chat file.
        if (save && epochAtStart === scopeEpoch && nativeScopeStable(expectedScope)) {
            await safeNativeSave(expectedScope);
        }

        return true;
    } finally {
        applyingRemoteDepth -= 1;
    }
}

async function ensureIdsPersisted() {
    refreshLiveContext();
    if (!ctx?.chat || !currentScope || !nativeScopeStable(currentScope)) return false;
    ensureMessageIds(ctx.chat);
    return true;
}

async function enqueueSnapshot(snapshot, baseRev, baseSnap) {
    if (!settings.syncMessages || !scopeKeyValue) return;

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

async function publishLocalSnapshot(snapshot = durableSnapshot()) {
    if (!currentScope || !settings.enabled || !settings.syncMessages) return false;
    if (!nativeScopeStable(currentScope)) return false;

    const scopeAtPublish = clone(currentScope);
    const scopeKeyAtPublish = makeScopeKey(scopeAtPublish);
    const base = clone(baseSnapshot || { messages: [], metadata: {} });
    const revision = Number(serverState?.revision || 0);

    try {
        const result = await sendSnapshotDirect(snapshot, revision, newId(), scopeAtPublish);
        if (scopeKeyValue !== scopeKeyAtPublish || !currentScope || makeScopeKey(currentScope) !== scopeKeyAtPublish) return false;
        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        writeLastScope(scopeAtPublish);
        broadcastWake('state');
        return true;
    } catch (error) {
        if (scopeKeyValue !== scopeKeyAtPublish) return false;

        if (error?.status === 409 && error?.payload?.state) {
            const remoteState = error.payload.state;
            const merged = mergeSnapshots(base, snapshot, remoteState.snapshot);

            serverState = remoteState;
            baseSnapshot = clone(remoteState.snapshot);
            await applySnapshot(merged, { save: false, render: true, expectedScope: scopeAtPublish });

            if (!nativeScopeStable(scopeAtPublish) || scopeKeyValue !== scopeKeyAtPublish) return false;

            const retryBase = Number(remoteState.revision);
            try {
                const result = await sendSnapshotDirect(merged, retryBase, newId(), scopeAtPublish);
                if (scopeKeyValue !== scopeKeyAtPublish) return false;
                serverState = result.state;
                baseSnapshot = clone(result.state.snapshot);
                writeLastScope(scopeAtPublish);
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
    if (!currentScope || !settings.enabled || !settings.syncMessages || !scopeKeyValue) return;
    if (!nativeScopeStable(currentScope)) return;

    const scopeAtFlush = clone(currentScope);
    const scopeKeyAtFlush = makeScopeKey(scopeAtFlush);
    const rows = await idbList(scopeKeyAtFlush);

    for (const row of rows) {
        if (!currentScope || scopeKeyValue !== scopeKeyAtFlush || !nativeScopeStable(scopeAtFlush)) return;

        try {
            let nextSnapshot = clone(row.snapshot);
            let nextBase = clone(row.baseSnapshot || baseSnapshot || { messages: [], metadata: {} });
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
        } catch (error) {
            if (scopeKeyValue !== scopeKeyAtFlush) return;

            if (error?.status === 409 && error?.payload?.state) {
                const remote = error.payload.state;

                if (error.payload.error === 'generation_active') {
                    serverState = remote;
                    baseSnapshot = clone(remote.snapshot);
                    break;
                }

                const merged = mergeSnapshots(row.baseSnapshot, row.snapshot, remote.snapshot);
                serverState = remote;
                baseSnapshot = clone(remote.snapshot);

                row.snapshot = clone(merged);
                row.baseSnapshot = clone(remote.snapshot);
                row.baseRevision = Number(remote.revision);

                await applySnapshot(incomingSnapshot(merged), {
                    save: false,
                    render: true,
                    expectedScope: scopeAtFlush,
                });

                await idbPut(row);
                continue;
            }

            break;
        }
    }
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
    if (!nativeScopeStable(currentScope)) {
        statusText('Waiting for active chat…');
        return;
    }

    const scopeAtJoin = clone(currentScope);
    const localSnapshot = syncSnapshot(durableSnapshot());

    try {
        const result = await api('/join', 'POST', {
            scope: scopeAtJoin,
            clientId,
            deviceId,
            snapshot: localSnapshot,
        });

        if (!currentScopeGuard(epoch) || makeScopeKey(currentScope) !== makeScopeKey(scopeAtJoin)) return;
        if (!nativeScopeStable(scopeAtJoin)) return;

        if (scopeRetryTimer) {
            clearTimeout(scopeRetryTimer);
            scopeRetryTimer = null;
        }

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);
        writeLastScope(scopeAtJoin);

        // The server state is the shared source of truth after joining. This
        // prevents an old tab from immediately reintroducing stale history.
        const incoming = incomingSnapshot(result.state.snapshot);
        const queued = await idbList(scopeKeyValue);

        if (queued.length) {
            await flushQueue();
        } else if (!deepEqual(localSnapshot, incoming)) {
            await applySnapshot(incoming, {
                save: false,
                render: true,
                expectedScope: scopeAtJoin,
            });
        }

        connectSse(epoch);
        startHeartbeats(epoch);

        if (result.state.generation?.message && !generationIsMine(result.state.generation)) {
            pendingRemoteStream = {
                message: clone(result.state.generation.message),
                messageIndex: Number.isInteger(result.state.generation.messageIndex)
                    ? result.state.generation.messageIndex
                    : null,
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

        if (!currentScopeGuard(epoch) || scopeRetryTimer || nativeRestoreInProgress) return;

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
        localGenerationScopeKey = '';
        stopGenerationHeartbeat();
        generationServerReadyId = null;
    }

    if (generation?.message && !generationIsMine(generation)) {
        pendingRemoteStream = {
            message: clone(generation.message),
            messageIndex: Number.isInteger(generation.messageIndex) ? generation.messageIndex : null,
            generationId: generation.generationId,
        };
        scheduleRemoteRender();
    }

    updateGenerationUi();
}

function handleSnapshotEvent(data) {
    const run = stateApplyChain.then(async () => {
        if (Number(data.revision) <= Number(serverState?.revision || 0)) return;
        if (!currentScope || !nativeScopeStable(currentScope)) return;

        const remoteSnapshot = incomingSnapshot(data.snapshot);
        const base = clone(baseSnapshot || serverState?.snapshot || { messages: [], metadata: {} });
        const local = syncSnapshot(durableSnapshot());
        const merged = mergeSnapshots(base, local, remoteSnapshot);
        const scopeAtEvent = clone(currentScope);
        const revision = Number(data.revision);

        serverState = { ...(serverState || {}), revision, snapshot: clone(data.snapshot) };
        baseSnapshot = clone(data.snapshot);

        if (data.sourceClientId === clientId && data.sourceDeviceId === deviceId) {
            updateGenerationUi();
            return;
        }

        if (!deepEqual(local, merged)) {
            const applied = await applySnapshot(merged, { save: false, render: true, expectedScope: scopeAtEvent });
            if (!applied) return;
        }

        if (!deepEqual(merged, remoteSnapshot) && nativeScopeStable(scopeAtEvent) && scopeKeyValue === makeScopeKey(scopeAtEvent)) {
            try {
                const result = await sendSnapshotDirect(merged, revision, newId(), scopeAtEvent);
                if (scopeKeyValue === makeScopeKey(scopeAtEvent)) {
                    serverState = result.state;
                    baseSnapshot = clone(result.state.snapshot);
                }
            } catch (publishError) {
                if (publishError?.status === 409 && publishError?.payload?.state) {
                    serverState = publishError.payload.state;
                    baseSnapshot = clone(publishError.payload.state.snapshot);
                }
                await enqueueSnapshot(merged, Number(serverState?.revision || revision), baseSnapshot || data.snapshot);
            }
        }

        broadcastWake('state');
        updateGenerationUi();
    });

    stateApplyChain = run.catch(error => warn('remote snapshot apply failed', error));
    return run;
}

function handleGenerationEvent(data) {
    const generation = clone(data.generation || null);
    serverState = { ...(serverState || {}), generation };

    if (generation?.message && !generationIsMine(generation)) {
        pendingRemoteStream = {
            message: clone(generation.message),
            messageIndex: Number.isInteger(generation.messageIndex) ? generation.messageIndex : null,
            generationId: generation.generationId,
        };
        scheduleRemoteRender();
    }

    updateGenerationUi();
}

async function handleGenerationRecovered() {
    serverState = { ...(serverState || {}), generation: null };

    if (localGeneration) {
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        localGeneration = null;
        localGenerationScopeKey = '';
        stopGenerationHeartbeat();
    }

    generationServerReadyId = null;
    generationStartPromise = null;
    generationStartPromiseId = null;
    streamInFlight = false;
    pendingStream = null;
    pendingRemoteStream = null;

    renderBanner('Generation was lost; chat was unlocked.');
    setTimeout(() => renderBanner(''), 1800);
    updateGenerationUi();
    await resyncCurrentScope(scopeEpoch);
}

function handleGenerationStreamEvent(data) {
    const g = data?.generation;
    if (!g) return;

    serverState = { ...(serverState || {}), generation: clone(g) };

    if (generationIsMine(g) || !data.message || !currentScope || !nativeScopeStable(currentScope)) {
        updateGenerationUi();
        return;
    }

    pendingRemoteStream = {
        message: clone(data.message),
        messageIndex: Number.isInteger(data.messageIndex) ? data.messageIndex : null,
        generationId: g.generationId,
    };

    scheduleRemoteRender();
    updateGenerationUi();
}

function scheduleRemoteRender() {
    if (remoteRenderTimer) return;

    remoteRenderTimer = setTimeout(async () => {
        remoteRenderTimer = null;
        const item = pendingRemoteStream;
        pendingRemoteStream = null;

        if (!item || !ctx?.chat || !currentScope || !nativeScopeStable(currentScope)) return;

        const g = serverState?.generation;
        if (!g || g.generationId !== item.generationId || generationIsMine(g)) return;

        applyingRemoteDepth += 1;
        try {
            const id = messageId(item.message);
            if (!id) return;

            const index = ctx.chat.findIndex(message => messageId(message) === id);

            if (index < 0) {
                ctx.chat.push(clone(item.message));
                try { await Promise.resolve(ctx.printMessages?.()); } catch { /* ignore */ }
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
    const remoteGeneration = data?.generation || null;
    const mine = generationIsMine(remoteGeneration);

    serverState = {
        ...(serverState || {}),
        revision: Number(data.revision),
        snapshot: clone(data.snapshot),
        generation: null,
    };

    baseSnapshot = clone(data.snapshot);
    generationServerReadyId = null;
    generationStartPromise = null;
    generationStartPromiseId = null;
    pendingStream = null;
    pendingRemoteStream = null;
    streamInFlight = false;

    if (mine) {
        localGeneration = null;
        localGenerationScopeKey = '';
        stopGenerationHeartbeat();
        sendLockReason = '';
    } else if (currentScope && nativeScopeStable(currentScope)) {
        await applySnapshot(
            incomingSnapshot(data.snapshot),
            {
                save: false,
                render: true,
                expectedScope: currentScope,
            },
        );

        renderBanner('Generation finished in another client.');
        setTimeout(() => renderBanner(''), 1500);
    }

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
        refreshLiveContext();
        if (!nativeScopeStable(currentScope)) {
            await switchScope('heartbeat-context-mismatch');
            return;
        }

        try {
            const oldRevision = Number(serverState.revision || 0);
            const oldGenerationId = serverState.generation?.generationId || null;

            const result = await api('/heartbeat', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
            });

            if (!currentScopeGuard(epoch) || !nativeScopeStable(currentScope)) return;
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
        if (!nativeScopeStable(currentScope)) {
            try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            return;
        }

        try {
            const result = await api('/generation/heartbeat', 'POST', {
                scope: scopeAtStream,
                clientId,
                deviceId,
                generationId,
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
                localGenerationScopeKey = '';
                generationServerReadyId = null;
                stopGenerationHeartbeat();
                await resyncCurrentScope(epoch);
                return;
            }

            updateGenerationUi();
        } catch (error) {
            warn('generation heartbeat failed', error);
            try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            localGeneration = null;
            localGenerationScopeKey = '';
            generationServerReadyId = null;
            stopGenerationHeartbeat();
            await resyncCurrentScope(epoch);
        }
    }, GENERATION_HEARTBEAT_MS);
}

async function resyncCurrentScope(epoch = scopeEpoch) {
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
        if (!nativeScopeStable(scopeAtRequest)) return;

        const local = durableSnapshot();
        const remote = incomingSnapshot(result.state.snapshot);
        const base = clone(baseSnapshot || result.state.snapshot);
        const merged = mergeSnapshots(base, syncSnapshot(local), remote);

        serverState = result.state;
        baseSnapshot = clone(result.state.snapshot);

        const queued = await idbList(scopeKeyValue);
        if (queued.length) {
            await flushQueue();
        } else if (!deepEqual(local, merged)) {
            await applySnapshot(merged, {
                save: false,
                render: true,
                expectedScope: scopeAtRequest,
            });

            // If the local tab had genuine uncommitted changes in addition to
            // the server state, publish the merged result against the fresh
            // revision rather than silently discarding either side.
            if (!deepEqual(merged, remote) && nativeScopeStable(scopeAtRequest)) {
                try {
                    const publishResult = await sendSnapshotDirect(merged, Number(result.state.revision), newId());
                    serverState = publishResult.state;
                    baseSnapshot = clone(publishResult.state.snapshot);
                } catch (publishError) {
                    if (publishError?.status === 409 && publishError?.payload?.state) {
                        serverState = publishError.payload.state;
                        baseSnapshot = clone(publishError.payload.state.snapshot);
                    }
                    await enqueueSnapshot(
                        merged,
                        Number(serverState?.revision || result.state.revision),
                        baseSnapshot || result.state.snapshot,
                    );
                }
            }
        }

        if (result.state.generation?.message && !generationIsMine(result.state.generation)) {
            pendingRemoteStream = {
                message: clone(result.state.generation.message),
                messageIndex: Number.isInteger(result.state.generation.messageIndex)
                    ? result.state.generation.messageIndex
                    : null,
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
        try {
            await sendGenerationTerminal('stopped');
        } catch (error) {
            warn('generation cleanup failed while leaving scope', error);
        }
    }

    try {
        await api('/leave', 'POST', {
            scope: leavingScope,
            clientId,
            deviceId,
        });
    } catch {
        /* ignore */
    }

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
    localGenerationScopeKey = '';
    generationServerReadyId = null;
    generationStartPromise = null;
    generationStartPromiseId = null;
    pendingStream = null;
    pendingRemoteStream = null;
    streamInFlight = false;

    if (streamTimer) clearTimeout(streamTimer);
    streamTimer = null;

    if (remoteRenderTimer) clearTimeout(remoteRenderTimer);
    remoteRenderTimer = null;

    terminalizingGenerationId = null;
    setSendLock('');
    renderBanner('');
}

function switchScopeInternal(reason = 'scope-change') {
    return (async () => {
        if (nativeRestoreInProgress) return;

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
                writeLastScope(nextScope);
                if (!serverState && settings.enabled && settings.autoConnect) {
                    await openScope(scopeEpoch);
                }
            }
            return;
        }

        ++scopeEpoch;
        const epoch = scopeEpoch;

        await leaveCurrentScope();

        currentScope = nextScope;
        scopeKeyValue = nextKey;
        previousChatId = ctx?.chatId || null;
        writeLastScope(nextScope);

        log('switch scope', reason, nextScope);

        await ensureIdsPersisted();

        if (settings.enabled && settings.autoConnect) {
            await openScope(epoch);
        }
    })();
}

function switchScope(reason = 'scope-change') {
    const run = scopeSwitchChain.then(() => switchScopeInternal(reason));
    scopeSwitchChain = run.catch(error => warn('scope switch failed', error));
    return run;
}

async function ensureGenerationStarted() {
    if (!localGeneration || !currentScope) return false;

    const generationId = localGeneration.generationId;
    if (generationServerReadyId === generationId) return true;

    if (generationStartPromise && generationStartPromiseId === generationId) {
        return await generationStartPromise;
    }

    generationStartPromiseId = generationId;
    generationStartPromise = (async () => {
        try {
            const result = await api('/generation/started', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
                generationId,
            });

            serverState = result.state;
            localGeneration = clone(result.state.generation);
            generationServerReadyId = generationId;
            lastStreamSentAt = 0;

            updateGenerationUi();
            if (pendingStream) scheduleGenerationStream();
            return true;
        } catch (error) {
            // A duplicate started notification is harmless if the server already
            // considers this generation started and returns its current state.
            if (error?.status === 409 && error?.payload?.state?.generation?.generationId === generationId) {
                const current = error.payload.state.generation;
                if (current.phase === 'started' || current.phase === 'streaming') {
                    serverState = error.payload.state;
                    localGeneration = clone(current);
                    generationServerReadyId = generationId;
                    updateGenerationUi();
                    if (pendingStream) scheduleGenerationStream();
                    return true;
                }
            }

            warn('generation_started failed', error);
            return false;
        } finally {
            generationStartPromise = null;
            generationStartPromiseId = null;
        }
    })();

    return await generationStartPromise;
}

async function coordinatedGenerateInterceptor(chat, contextSize, abort, type) {
    if (!settings.enabled || !settings.coordinateGeneration || applyingRemoteDepth > 0 || !currentScope) return;

    if (!nativeScopeStable(currentScope)) {
        abort(false);
        statusText('Chat context changed; generation was blocked until synchronization catches up.', true);
        await switchScope('generation-context-mismatch');
        return;
    }

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

                const merged = mergeSnapshots(
                    claimBase,
                    desiredSnapshot,
                    payload.state.snapshot,
                );

                serverState = payload.state;
                baseSnapshot = clone(payload.state.snapshot);
                await applySnapshot(
                    merged,
                    {
                        save: false,
                        render: true,
                        expectedScope: currentScope,
                    },
                );

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

    if (!currentScope || !nativeScopeStable(currentScope)) {
        abort(false);
        return;
    }

    serverState = claimResult.state;
    baseSnapshot = clone(claimResult.state.snapshot);
    localGeneration = clone(claimResult.state.generation);
    localGenerationScopeKey = makeScopeKey(currentScope);
    generationServerReadyId = null;
    lastStreamSentAt = 0;
    pendingStream = null;
    streamInFlight = false;

    // A stale tab may have claimed successfully against a newer server state.
    // Bring the in-memory ST chat up to the server's exact generation baseline
    // BEFORE the core Generate() function appends the new user message.
    const claimedSnapshot = incomingSnapshot(claimResult.state.snapshot);
    const currentLocalSnapshot = syncSnapshot(durableSnapshot());
    if (!deepEqual(currentLocalSnapshot, claimedSnapshot)) {
        await applySnapshot(
            claimedSnapshot,
            {
                save: false,
                render: true,
                expectedScope: currentScope,
            },
        );
    }

    startGenerationHeartbeat(scopeEpoch);
    updateGenerationUi();

    // ST emits GENERATION_STARTED before extension interceptors run, so the
    // event listener alone cannot start the server generation. Do it here and
    // await it before returning, which removes the claim/stream race.
    const started = await ensureGenerationStarted();
    if (!started) {
        abort(false);
        try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
        localGeneration = null;
        localGenerationScopeKey = '';
        generationServerReadyId = null;
        stopGenerationHeartbeat();
        await resyncCurrentScope(scopeEpoch);
    }
}

async function onGenerationStarted() {
    // For normal generation ST emits GENERATION_STARTED before the extension
    // interceptor runs, so there is nothing to do yet. The interceptor calls
    // ensureGenerationStarted() after claiming the generation. Group-wrapper
    // starts can reach here after the claim and will be handled idempotently.
    if (!localGeneration || !currentScope) return;
    if (!nativeScopeStable(currentScope)) return;
    await ensureGenerationStarted();
}

function scheduleGenerationStream() {
    if (
        terminalizingGenerationId ||
        streamTimer ||
        streamInFlight ||
        !pendingStream ||
        !localGeneration ||
        !currentScope ||
        generationServerReadyId !== localGeneration.generationId
    ) return;

    const delay = Math.max(0, STREAM_SEND_MS - (Date.now() - lastStreamSentAt));

    streamTimer = setTimeout(async () => {
        streamTimer = null;

        if (terminalizingGenerationId || !pendingStream || !localGeneration || !currentScope) return;
        if (generationServerReadyId !== localGeneration.generationId) return;
        if (!nativeScopeStable(currentScope)) return;

        const payload = pendingStream;
        pendingStream = null;
        streamInFlight = true;
        const generationId = localGeneration.generationId;
        const scopeAtStream = clone(currentScope);

        try {
            const nextSeq = Number(localGeneration.seq || 0) + 1;
            const result = await api('/generation/stream', 'POST', {
                scope: currentScope,
                clientId,
                deviceId,
                generationId: localGeneration.generationId,
                seq: Math.max(Number(payload.seq || 0), nextSeq),
                message: payload.message,
                messageIndex: payload.messageIndex,
            });

            lastStreamSentAt = Date.now();
            if (terminalizingGenerationId !== generationId && localGeneration?.generationId === generationId && scopeKeyValue === makeScopeKey(scopeAtStream)) {
                serverState = result.state;
                localGeneration = clone(result.state.generation);
                generationServerReadyId = localGeneration?.generationId || generationServerReadyId;
                updateGenerationUi();
            }
        } catch (error) {
            if (error?.status === 409 && error?.payload?.error === 'generation_not_started') {
                // Safety net for any remaining ordering race. Re-establish the
                // server phase without interrupting the real LLM request.
                pendingStream = payload;
                const started = await ensureGenerationStarted();
                if (!terminalizingGenerationId && started) {
                    scheduleGenerationStream();
                } else if (!terminalizingGenerationId && localGeneration) {
                    streamTimer = setTimeout(() => {
                        streamTimer = null;
                        ensureGenerationStarted()
                            .then(ok => { if (ok) scheduleGenerationStream(); })
                            .catch(() => { /* terminal path will reconcile */ });
                    }, 150);
                }
                return;
            }

            warn('generation stream failed', error);
            try { ctx?.stopGeneration?.(); } catch { /* ignore */ }
            localGeneration = null;
            localGenerationScopeKey = '';
            generationServerReadyId = null;
            stopGenerationHeartbeat();
            await resyncCurrentScope(scopeEpoch);
        } finally {
            streamInFlight = false;
            if (pendingStream && localGeneration && generationServerReadyId === localGeneration.generationId) {
                scheduleGenerationStream();
            }
        }
    }, delay);
}

function captureLocalStream() {
    if (terminalizingGenerationId || !localGeneration || !ctx?.chat?.length || !currentScope) return;
    if (localGenerationScopeKey !== makeScopeKey(currentScope)) return;
    if (!nativeScopeStable(currentScope)) return;

    const messages = ctx.chat;
    let index = -1;

    for (let i = messages.length - 1; i >= 0; i -= 1) {
        if (!messages[i]?.is_user && !messages[i]?.is_system) {
            index = i;
            break;
        }
    }

    if (index < 0) return;

    ensureMessageIds(messages);
    const message = clone(messages[index]);

    // Keep only the newest full-message image until the next stream request.
    // The server sequence is advanced when the request is acknowledged.
    const seq = pendingStream?.seq ?? (Number(localGeneration.seq || 0) + 1);
    pendingStream = {
        seq,
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
    pendingStream = null;
    if (streamTimer) clearTimeout(streamTimer);
    streamTimer = null;
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

                    if (error.payload?.error === 'generation_not_started') {
                        const started = await ensureGenerationStarted();
                        if (started && attempt < 2) continue;
                    }
                    break;
                }
                if (attempt < 2) await sleep(250 * (attempt + 1));
            }
        }

        if (!succeeded && lastError) {
            warn('generation terminal failed', lastError);
            try {
                await enqueueSnapshot(
                    snapshot,
                    Number(serverState?.revision || 0),
                    baseSnapshot,
                );
            } catch (queueError) {
                warn('generation terminal queue failed', queueError);
            }
        }
    } finally {
        localGeneration = null;
        localGenerationScopeKey = '';
        generationServerReadyId = null;
        generationStartPromise = null;
        generationStartPromiseId = null;
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

async function onGenerationEnded() {
    if (localGeneration) await sendGenerationTerminal('completed');
}

async function onGenerationStopped() {
    if (localGeneration) await sendGenerationTerminal('stopped');
}

function publishAfterLocalEvent() {
    const run = publishChain.then(async () => {
        if (
            applyingRemoteDepth > 0 ||
            !currentScope ||
            !settings.enabled ||
            !settings.syncMessages ||
            localGeneration ||
            terminalizingGenerationId ||
            serverState?.generation
        ) return;

        refreshLiveContext();
        if (!nativeScopeStable(currentScope)) {
            await switchScope('local-event-context-mismatch');
            return;
        }

        try {
            await ensureIdsPersisted();
            await publishLocalSnapshot(syncSnapshot(durableSnapshot()));
        } catch (error) {
            warn('publish after local event failed', error);
        }
    });

    publishChain = run.catch(error => warn('local publish chain failed', error));
    return run;
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

    const types = ctx.eventTypes;
    const es = ctx.eventSource;

    const listen = (eventType, fn) => {
        if (!eventType || !es?.on) return;
        es.on(eventType, fn);
        registeredEventHandlers.push([eventType, fn]);
    };

    listen(types.APP_INITIALIZED, () => switchScope('APP_INITIALIZED'));
    listen(types.APP_READY, () => switchScope('APP_READY'));
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
    activationInProgress = true;
    startupRestoreComplete = false;

    unwireEvents();
    unwireUiGuards();

    bc?.close?.();
    bc = 'BroadcastChannel' in window ? new BroadcastChannel(BC_NAME) : null;

    bc?.addEventListener('message', message => {
        if (message.data?.scopeKey !== scopeKeyValue) return;
        if (message.data?.kind === 'state' && currentScope) {
            resyncCurrentScope().catch(error => log('[MCS] broadcast resync failed', error));
        }
    });

    await mountSettings();

    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

    // Do this before the first scope join. SillyTavern's active-character
    // setting is shared between windows, so a fresh tab can open in the wrong
    // character/chat even though its previous MCS session was elsewhere.
    if (settings.enabled && settings.autoConnect) {
        await maybeRestoreLastNativeScope();
    }
    refreshLiveContext();
    startupRestoreComplete = true;
    activationInProgress = false;

    wireEvents();
    wireUiGuards();
    await switchScope('activate');

    setTimeout(() => {
        switchScope('post-activate').catch(error => warn('post-activate scope check failed', error));
    }, 1000);
}

async function onEnable() {
    settings.enabled = true;
    settings.autoConnect = true;
    saveSettings();

    ++scopeEpoch;
    wireEvents();
    wireUiGuards();
    globalThis.multiClientSyncGenerateInterceptor = coordinatedGenerateInterceptor;

    refreshLiveContext();
    currentScope = scopeFromContext();
    scopeKeyValue = makeScopeKey(currentScope);
    if (currentScope) writeLastScope(currentScope);

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
    serverState = null;
    baseSnapshot = null;

    try { bc?.close?.(); } catch { /* ignore */ }
    bc = null;
    statusText('Disabled');
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

            if (settings.enabled && settings.autoConnect) {
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
