/**
 * Multi-Client Chat Synchronization Extension for SillyTavern
 *
 * Synchronizes chat state, messages, edits, deletions, generation, and streaming
 * across multiple browser tabs/devices connected to the same SillyTavern instance.
 *
 * Client-side responsibilities implemented here:
 * - chat/session scoping
 * - ordered server-event application with gap detection/recovery
 * - BroadcastChannel + SSE duplicate suppression
 * - message identity/revision handling
 * - stable insertion anchors for concurrent message inserts
 * - ordered/deduplicated streaming
 * - generation conflict handling using server sequence order
 * - remote generation-stop requests through the existing event relay
 * - safer reconnect/chat-switch invalidation
 * - debounced normal SillyTavern persistence for remote changes
 *
 * Server-side responsibilities that cannot be implemented here:
 * - authorization / access control
 * - assigning authoritative server sequence numbers
 * - authoritative snapshot storage/serving
 * - heartbeat expiry policy
 * - persistent generation ownership leases across all server workers
 */

import { eventSource, event_types, getRequestHeaders } from '../../script.js';
import { getContext } from '../../st-context.js';
import { extension_settings } from '../extensions.js';
import { getCurrentUserHandle } from '../../user.js';
import { t } from '../../i18n.js';

const EXTENSION_NAME = 'multi-client-sync';
const LOG_PREFIX = '[MCS]';
const BROADCAST_CHANNEL_NAME = 'mcs_sync';
const DEVICE_STORAGE_KEY = 'mcs_device_id';

const MAX_PROCESSED_EVENT_IDS = 5000;
const PROCESSED_EVENT_PRUNE_COUNT = 1000;

const HEARTBEAT_INTERVAL_MS = 10000;
const INITIAL_RECONNECT_DELAY_MS = 1000;
const MAX_RECONNECT_DELAY_MS = 30000;
const INITIAL_JOIN_DELAY_MS = 1500;
const CHAT_SWITCH_JOIN_DELAY_MS = 250;

const MESSAGE_SAVE_DEBOUNCE_MS = 350;
const STREAM_SAVE_DEBOUNCE_MS = 1200;
const STREAM_RENDER_DEBOUNCE_MS = 40;

// ---------------------------------------------------------------------------
// Settings
// ---------------------------------------------------------------------------

const defaultSettings = {
    enabled: true,
    debugLogging: false,
    showStatusIndicator: true,
};

function getSettings() {
    if (!extension_settings[EXTENSION_NAME]) {
        extension_settings[EXTENSION_NAME] = { ...defaultSettings };
    } else {
        extension_settings[EXTENSION_NAME] = {
            ...defaultSettings,
            ...extension_settings[EXTENSION_NAME],
        };
    }

    return extension_settings[EXTENSION_NAME];
}

function log(...args) {
    if (getSettings().debugLogging) {
        console.log(LOG_PREFIX, ...args);
    }
}

function warn(...args) {
    console.warn(LOG_PREFIX, ...args);
}

function error(...args) {
    console.error(LOG_PREFIX, ...args);
}

function safeClone(value) {
    if (value === undefined) return undefined;

    try {
        if (typeof structuredClone === 'function') {
            return structuredClone(value);
        }
    } catch (e) {
        log('structuredClone failed; using JSON clone', e);
    }

    try {
        return JSON.parse(JSON.stringify(value));
    } catch (e) {
        return value;
    }
}

function escapeHtml(value) {
    return String(value ?? '')
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;');
}

// ---------------------------------------------------------------------------
// Identity
// ---------------------------------------------------------------------------

const CLIENT_ID =
    `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 9)}`;

const DEVICE_ID = (() => {
    try {
        const stored = localStorage.getItem(DEVICE_STORAGE_KEY);

        if (stored) {
            return stored;
        }

        const id =
            `${Math.random().toString(36).slice(2, 10)}-${Date.now().toString(36).slice(-4)}`;

        localStorage.setItem(DEVICE_STORAGE_KEY, id);
        return id;
    } catch {
        return 'unknown';
    }
})();

function getUserId() {
    try {
        return getCurrentUserHandle() ?? '';
    } catch {
        return '';
    }
}

function getClientIdentity() {
    return {
        clientId: CLIENT_ID,
        deviceId: DEVICE_ID,
        userId: getUserId(),
    };
}

// ---------------------------------------------------------------------------
// Connection / synchronization state
// ---------------------------------------------------------------------------

/** @type {string|null} */
let currentChatKey = null;

/** @type {number} */
let lastSequence = 0;

/** @type {number} */
let knownServerHeadSequence = 0;

/** @type {EventSource|null} */
let sseConnection = null;

/** @type {boolean} */
let isApplyingRemote = false;

/** @type {boolean} */
let isReconcilingChat = false;

/** @type {boolean} */
let isConnected = false;

/** @type {Set<string>} */
const processedEventIds = new Set();

/**
 * @type {Map<number, {event:any, source:string, alreadyApplied:boolean}>}
 */
const pendingSequenceEvents = new Map();

/** @type {Map<string, number>} */
const messageRevisions = new Map();

/** @type {Map<string, number>} */
const messageTombstones = new Map();

/**
 * @type {Map<string, {nextExpected:number, pending:Map<number, any>}>}
 */
const streamStates = new Map();

/** @type {Map<string, {timer:number, messageKey:string|null}>} */
const streamRenderTimers = new Map();

let heartbeatTimer = null;
let reconnectTimer = null;
let reconnectDelay = INITIAL_RECONNECT_DELAY_MS;
let reconnectChatKey = null;

let connectionGeneration = 0;
let chatChangeGeneration = 0;

let recoveryPromise = null;
let recoveryTargetSequence = 0;

/** @type {object|null} */
let activeGeneration = null;

/** @type {boolean} */
let isGenerationOwner = false;

let generationRequestTime = 0;

const generationPublishChains = new Map();
const pendingGenerationConflicts = new Map();

/** @type {object|null} */
let pendingRemoteGenerationAfterLocalStop = null;

const finishedGenerationIds = new Set();
const suppressedGenerationStopPublishes = new Set();

let bcChannel = null;

let chatSaveTimer = null;
let chatSaveDelay = MESSAGE_SAVE_DEBOUNCE_MS;
let chatSaveChain = Promise.resolve();

// ---------------------------------------------------------------------------
// Chat Identity
// ---------------------------------------------------------------------------

function getChatIdentity() {
    const ctx = getContext();

    return {
        characterId: String(ctx.characterId ?? ''),
        groupId: String(ctx.groupId ?? ''),
        chatId: String(ctx.chatId ?? ''),
    };
}

function buildChatKey(ident) {
    const scope = ident.groupId
        ? `g:${ident.groupId}`
        : `c:${ident.characterId}`;

    return `${scope}::${ident.chatId}`;
}

function getCurrentDesiredChatKey() {
    const ident = getChatIdentity();

    return ident.chatId
        ? buildChatKey(ident)
        : null;
}

function isCurrentChatKey(chatKey) {
    if (!chatKey || chatKey !== currentChatKey) {
        return false;
    }

    return getCurrentDesiredChatKey() === chatKey;
}

// ---------------------------------------------------------------------------
// API Helpers
// ---------------------------------------------------------------------------

async function apiPost(path, body, options = {}) {
    const res = await fetch(`/api/multi-client-sync${path}`, {
        method: 'POST',
        headers: {
            ...getRequestHeaders(),
            'Content-Type': 'application/json',
        },
        body: JSON.stringify(body),
        ...options,
    });

    if (!res.ok) {
        const text = await res.text().catch(() => '');
        throw new Error(`HTTP ${res.status}: ${text}`);
    }

    const text = await res.text();

    if (!text) {
        return {};
    }

    try {
        return JSON.parse(text);
    } catch {
        return {
            success: true,
            raw: text,
        };
    }
}

function getEventSequence(event) {
    const sequence = Number(event?.sequence);

    return Number.isSafeInteger(sequence) && sequence > 0
        ? sequence
        : null;
}

// ---------------------------------------------------------------------------
// BroadcastChannel
// ---------------------------------------------------------------------------

function initBroadcastChannel() {
    if (typeof BroadcastChannel === 'undefined') {
        return;
    }

    try {
        bcChannel = new BroadcastChannel(BROADCAST_CHANNEL_NAME);

        bcChannel.onmessage = (messageEvent) => {
            try {
                const msg = messageEvent.data;

                if (!msg || msg.type !== 'EVENT') {
                    return;
                }

                if (msg.sourceClientId === CLIENT_ID) {
                    return;
                }

                if (!isCurrentChatKey(msg.chatKey)) {
                    return;
                }

                if (
                    msg.userId &&
                    getUserId() &&
                    msg.userId !== getUserId()
                ) {
                    return;
                }

                handleRemoteEvent(msg.event, true, msg.chatKey);
            } catch (e) {
                warn('BroadcastChannel handler failed', e);
            }
        };
    } catch (e) {
        warn('BroadcastChannel init failed', e);
        bcChannel = null;
    }
}

function bcBroadcast(event, chatKey = currentChatKey) {
    if (!bcChannel || !event || !chatKey) {
        return;
    }

    try {
        bcChannel.postMessage({
            type: 'EVENT',
            sourceClientId: CLIENT_ID,
            userId: getUserId(),
            chatKey,
            event,
        });
    } catch (e) {
        log('BroadcastChannel send failed', e);
    }
}

// ---------------------------------------------------------------------------
// Persistence
// ---------------------------------------------------------------------------

function scheduleChatSave(delay = MESSAGE_SAVE_DEBOUNCE_MS) {
    if (!getSettings().enabled || !currentChatKey) {
        return;
    }

    chatSaveDelay = Math.min(chatSaveDelay, delay);

    if (chatSaveTimer !== null) {
        return;
    }

    const targetChatKey = currentChatKey;

    chatSaveTimer = window.setTimeout(() => {
        chatSaveTimer = null;

        const requestedDelay = chatSaveDelay;
        chatSaveDelay = MESSAGE_SAVE_DEBOUNCE_MS;

        void requestedDelay;

        if (!isCurrentChatKey(targetChatKey)) {
            return;
        }

        const ctx = getContext();

        if (typeof ctx.saveChat !== 'function') {
            return;
        }

        chatSaveChain = chatSaveChain
            .catch(() => {})
            .then(async () => {
                if (!isCurrentChatKey(targetChatKey)) {
                    return;
                }

                try {
                    await ctx.saveChat();
                    log('chat persisted', targetChatKey);
                } catch (e) {
                    warn('chat save failed', e);
                }
            });
    }, delay);
}

function clearChatSaveTimer() {
    if (chatSaveTimer !== null) {
        clearTimeout(chatSaveTimer);
        chatSaveTimer = null;
    }

    chatSaveDelay = MESSAGE_SAVE_DEBOUNCE_MS;
}

// ---------------------------------------------------------------------------
// Message identity / revisions
// ---------------------------------------------------------------------------

function getMessageKey(message, fallbackIndex = null) {
    if (!message) {
        return null;
    }

    const explicit =
        message.mcs_message_id ??
        message.extra?.mcs_message_id;

    if (
        explicit !== undefined &&
        explicit !== null &&
        explicit !== ''
    ) {
        return `id:${String(explicit)}`;
    }

    if (
        message.send_date !== undefined &&
        message.send_date !== null &&
        message.send_date !== ''
    ) {
        return `date:${String(message.send_date)}`;
    }

    if (fallbackIndex !== null && fallbackIndex !== undefined) {
        return `idx:${Number(fallbackIndex)}`;
    }

    return null;
}

function findMessageIndexByKey(key) {
    if (!key) {
        return -1;
    }

    const ctx = getContext();

    for (let i = 0; i < ctx.chat.length; i++) {
        if (getMessageKey(ctx.chat[i], i) === key) {
            return i;
        }
    }

    return -1;
}

function findMessageIndex(payload = {}) {
    const byKey = findMessageIndexByKey(payload.messageKey);

    if (byKey >= 0) {
        return byKey;
    }

    if (Number.isInteger(payload.messageId)) {
        const ctx = getContext();

        if (
            payload.messageId >= 0 &&
            payload.messageId < ctx.chat.length
        ) {
            return payload.messageId;
        }
    }

    return -1;
}

function getRevisionKeyForPayload(payload) {
    return payload?.messageKey ??
        (
            Number.isInteger(payload?.messageId)
                ? `idx:${payload.messageId}`
                : null
        );
}

function isStaleMessageMutation(payload, sequence) {
    const key = getRevisionKeyForPayload(payload);

    if (!key || !sequence) {
        return false;
    }

    const lastRevision =
        messageRevisions.get(key) ?? 0;

    const tombstoneRevision =
        messageTombstones.get(key) ?? 0;

    return sequence <= Math.max(
        lastRevision,
        tombstoneRevision,
    );
}

function recordMessageRevision(payload, sequence) {
    const key = getRevisionKeyForPayload(payload);

    if (!key || !sequence) {
        return;
    }

    messageRevisions.set(
        key,
        Math.max(
            messageRevisions.get(key) ?? 0,
            sequence,
        ),
    );
}

function recordMessageTombstone(key, sequence) {
    if (!key || !sequence) {
        return;
    }

    messageTombstones.set(
        key,
        Math.max(
            messageTombstones.get(key) ?? 0,
            sequence,
        ),
    );

    messageRevisions.set(
        key,
        Math.max(
            messageRevisions.get(key) ?? 0,
            sequence,
        ),
    );
}

// ---------------------------------------------------------------------------
// Sequence ordering / recovery
// ---------------------------------------------------------------------------

function pruneProcessedEventIds() {
    if (processedEventIds.size <= MAX_PROCESSED_EVENT_IDS) {
        return;
    }

    const iterator = processedEventIds.values();

    for (
        let i = 0;
        i < PROCESSED_EVENT_PRUNE_COUNT;
        i++
    ) {
        const next = iterator.next();

        if (next.done) {
            break;
        }

        processedEventIds.delete(next.value);
    }
}

function applyEventNow(
    event,
    source,
    alreadyApplied = false,
) {
    const sequence = getEventSequence(event);

    if (!sequence) {
        return;
    }

    processedEventIds.add(event.eventId);
    pruneProcessedEventIds();

    lastSequence = sequence;
    knownServerHeadSequence =
        Math.max(knownServerHeadSequence, sequence);

    log(
        'applying event',
        event.type,
        'seq',
        sequence,
        'from',
        event.clientId,
        'source',
        source,
        alreadyApplied ? '(already local)' : '',
    );

    isApplyingRemote = true;

    try {
        switch (event.type) {
            case 'MESSAGE_SENT':
            case 'MESSAGE_RECEIVED':
                applyRemoteMessageInserted(event);
                break;

            case 'MESSAGE_EDITED':
                applyRemoteMessageEdited(event);
                break;

            case 'MESSAGE_DELETED':
                applyRemoteMessageDeleted(event);
                break;

            case 'MESSAGE_SWIPED':
                applyRemoteMessageSwiped(event);
                break;

            case 'CHAT_CHANGED':
                break;

            case 'GENERATION_STARTED':
                applyRemoteGenerationStarted(event);
                break;

            case 'GENERATION_STREAM':
                applyRemoteGenerationStream(event);
                break;

            case 'GENERATION_STOP_REQUESTED':
                applyRemoteGenerationStopRequested(event);
                break;

            case 'GENERATION_STOPPED':
                applyRemoteGenerationStopped(event);
                break;

            case 'GENERATION_COMPLETED':
                applyRemoteGenerationCompleted(event);
                break;

            case 'GENERATION_FAILED':
                applyRemoteGenerationFailed(event);
                break;

            case 'GENERATION_OWNER_RELEASED':
                applyRemoteOwnerReleased(event);
                break;

            case 'CHAT_RELOADED':
                applyRemoteChatReloaded(event.payload);
                break;

            default:
                log('unhandled event type', event.type);
        }
    } catch (e) {
        error(
            'event application failed',
            event.type,
            e,
        );
    } finally {
        isApplyingRemote = false;
    }
}

function drainSequenceQueue() {
    while (
        pendingSequenceEvents.has(lastSequence + 1)
    ) {
        const item =
            pendingSequenceEvents.get(lastSequence + 1);

        pendingSequenceEvents.delete(
            lastSequence + 1,
        );

        if (
            processedEventIds.has(
                item.event.eventId,
            )
        ) {
            lastSequence =
                getEventSequence(item.event);
            continue;
        }

        applyEventNow(
            item.event,
            item.source,
            item.alreadyApplied,
        );
    }
}

function acceptSequencedEvent(
    event,
    source = 'server',
    alreadyApplied = false,
    allowRecovery = true,
) {
    if (
        !event ||
        typeof event !== 'object' ||
        !event.eventId
    ) {
        return;
    }

    const eventChatKey =
        event.chatKey || currentChatKey;

    if (!isCurrentChatKey(eventChatKey)) {
        return;
    }

    if (
        event.userId &&
        getUserId() &&
        event.userId !== getUserId()
    ) {
        return;
    }

    const sequence =
        getEventSequence(event);

    if (!sequence) {
        warn(
            'Ignoring event without valid server sequence',
            event,
        );
        return;
    }

    knownServerHeadSequence =
        Math.max(
            knownServerHeadSequence,
            sequence,
        );

    if (sequence <= lastSequence) {
        pendingSequenceEvents.delete(sequence);
        processedEventIds.add(event.eventId);
        pruneProcessedEventIds();
        return;
    }

    const expected = lastSequence + 1;

    if (sequence > expected) {
        const existing =
            pendingSequenceEvents.get(sequence);

        if (!existing) {
            pendingSequenceEvents.set(
                sequence,
                {
                    event,
                    source,
                    alreadyApplied,
                },
            );
        }

        warn(
            'Sequence gap detected',
            {
                expected,
                received: sequence,
                chatKey: currentChatKey,
            },
        );

        if (allowRecovery) {
            requestSequenceRecovery(sequence)
                .catch((e) =>
                    warn(
                        'sequence recovery failed',
                        e,
                    ),
                );
        }

        return;
    }

    if (processedEventIds.has(event.eventId)) {
        return;
    }

    pendingSequenceEvents.delete(sequence);

    applyEventNow(
        event,
        source,
        alreadyApplied,
    );

    drainSequenceQueue();
}

function handleRemoteEvent(
    event,
    fromBroadcastChannel = false,
    hintedChatKey = null,
) {
    if (
        !event ||
        typeof event !== 'object' ||
        !event.eventId
    ) {
        return;
    }

    const eventChatKey =
        event.chatKey ||
        hintedChatKey ||
        currentChatKey;

    if (!isCurrentChatKey(eventChatKey)) {
        return;
    }

    acceptSequencedEvent(
        event,
        fromBroadcastChannel
            ? 'broadcast'
            : 'sse',
        false,
        true,
    );
}

async function reconcileAuthoritatively(
    reason,
    authoritativeSequence = null,
) {
    const targetChatKey = currentChatKey;

    if (
        !targetChatKey ||
        !isCurrentChatKey(targetChatKey)
    ) {
        return false;
    }

    const ctx = getContext();

    if (
        typeof ctx.reloadCurrentChat !==
        'function'
    ) {
        warn(
            'No reloadCurrentChat API available for recovery',
            reason,
        );
        return false;
    }

    log(
        'authoritative chat reconciliation',
        reason,
        targetChatKey,
        authoritativeSequence,
    );

    isReconcilingChat = true;
    isApplyingRemote = true;

    try {
        await ctx.reloadCurrentChat();

        if (!isCurrentChatKey(targetChatKey)) {
            return false;
        }

        pendingSequenceEvents.clear();

        if (
            Number.isSafeInteger(
                authoritativeSequence,
            ) &&
            authoritativeSequence >= 0
        ) {
            lastSequence =
                authoritativeSequence;

            knownServerHeadSequence =
                Math.max(
                    knownServerHeadSequence,
                    authoritativeSequence,
                );
        }

        messageRevisions.clear();
        messageTombstones.clear();
        processedEventIds.clear();

        return true;
    } catch (e) {
        warn(
            'authoritative chat reload failed',
            e,
        );

        return false;
    } finally {
        isApplyingRemote = false;
        isReconcilingChat = false;
    }
}

async function requestSequenceRecovery(
    targetSequence = 0,
) {
    if (!currentChatKey) {
        return;
    }

    recoveryTargetSequence =
        Math.max(
            recoveryTargetSequence,
            Number(targetSequence) || 0,
        );

    if (recoveryPromise) {
        return recoveryPromise;
    }

    const targetChatKey = currentChatKey;
    const targetChatGeneration =
        connectionGeneration;

    recoveryPromise = (async () => {
        try {
            if (!isCurrentChatKey(targetChatKey)) {
                return;
            }

            if (reconnectTimer) {
                clearTimeout(reconnectTimer);
                reconnectTimer = null;
            }

            if (sseConnection) {
                try {
                    sseConnection.close();
                } catch {
                    // ignore
                }

                sseConnection = null;
            }

            isConnected = false;
            updateStatusUI();

            await syncJoinCurrentChat({
                force: true,
                recovery: true,
                expectedChatKey:
                    targetChatKey,
                expectedGeneration:
                    targetChatGeneration,
            });
        } finally {
            recoveryTargetSequence = 0;
            recoveryPromise = null;
        }
    })();

    return recoveryPromise;
}

// ---------------------------------------------------------------------------
// Join / SSE / heartbeat
// ---------------------------------------------------------------------------

async function processMissedEvents(
    missedEvents,
    serverHeadSequence,
    reason = 'join',
) {
    const events = Array.isArray(missedEvents)
        ? [...missedEvents]
            .filter(Boolean)
            .sort(
                (a, b) =>
                    (getEventSequence(a) ?? 0) -
                    (getEventSequence(b) ?? 0),
            )
        : [];

    if (events.length > 0) {
        for (const event of events) {
            acceptSequencedEvent(
                event,
                'join-replay',
                false,
                false,
            );
        }

        drainSequenceQueue();
    }

    const head =
        Number.isSafeInteger(
            Number(serverHeadSequence),
        )
            ? Number(serverHeadSequence)
            : null;

    if (head !== null) {
        knownServerHeadSequence =
            Math.max(
                knownServerHeadSequence,
                head,
            );
    }

    if (
        head !== null &&
        lastSequence < head
    ) {
        const recovered =
            await reconcileAuthoritatively(
                `${reason}: missed-event gap`,
                head,
            );

        if (!recovered) {
            warn(
                'Unable to reconcile missing event range',
                {
                    lastSequence,
                    serverHeadSequence: head,
                },
            );

            return false;
        }
    } else if (
        head !== null &&
        lastSequence > head
    ) {
        warn(
            'Server sequence is behind local sequence; forcing authoritative reset',
            {
                lastSequence,
                serverHeadSequence: head,
            },
        );

        const recovered =
            await reconcileAuthoritatively(
                `${reason}: sequence regression`,
                head,
            );

        if (!recovered) {
            return false;
        }
    }

    return true;
}

async function joinGroup(
    ident = getChatIdentity(),
    token = connectionGeneration,
    options = {},
) {
    if (!ident.chatId) {
        return false;
    }

    const targetChatKey =
        buildChatKey(ident);

    const previousChatKey =
        currentChatKey;

    try {
        const identity =
            getClientIdentity();

        const result = await apiPost(
            '/join',
            {
                ...identity,
                characterId:
                    ident.characterId,
                groupId:
                    ident.groupId,
                chatId:
                    ident.chatId,
                chatKey:
                    targetChatKey,
                lastSequence,
            },
        );

        if (
            token !== connectionGeneration ||
            getCurrentDesiredChatKey() !==
                targetChatKey
        ) {
            try {
                await apiPost(
                    '/leave',
                    {
                        clientId: CLIENT_ID,
                        userId: getUserId(),
                        chatKey:
                            result.chatKey ||
                            targetChatKey,
                    },
                );
            } catch {
                // stale join cleanup is best effort
            }

            return false;
        }

        if (!result?.success) {
            warn(
                'join failed',
                result?.error || result,
            );

            return false;
        }

        currentChatKey =
            result.chatKey ||
            targetChatKey;

        if (
            !isCurrentChatKey(
                currentChatKey,
            )
        ) {
            try {
                await apiPost(
                    '/leave',
                    {
                        clientId:
                            CLIENT_ID,
                        userId:
                            getUserId(),
                        chatKey:
                            currentChatKey,
                    },
                );
            } catch {
                // ignore
            }

            currentChatKey =
                previousChatKey;

            return false;
        }

        const serverHeadSequence =
            Number.isSafeInteger(
                Number(result.nextSequence),
            )
                ? Number(result.nextSequence) -
                  1
                : null;

        const replayOk =
            await processMissedEvents(
                result.missedEvents,
                serverHeadSequence,
                options.recovery
                    ? 'recovery'
                    : 'join',
            );

        if (!replayOk) {
            return false;
        }

        if (
            result.state &&
            Object.prototype.hasOwnProperty.call(
                result.state,
                'generation',
            )
        ) {
            restoreGenerationState(
                result.state.generation,
            );
        }

        if (
            options.recovery &&
            recoveryTargetSequence > 0 &&
            lastSequence <
                recoveryTargetSequence
        ) {
            await reconcileAuthoritatively(
                'recovery target still not satisfied',
                serverHeadSequence,
            );
        }

        log(
            'joined group',
            currentChatKey,
            'clients:',
            result.clientCount,
            'seq:',
            lastSequence,
        );

        return true;
    } catch (e) {
        warn('join error', e);
        return false;
    }
}

function connectSSE(
    expectedChatKey = currentChatKey,
    expectedGeneration =
        connectionGeneration,
) {
    if (!expectedChatKey) {
        return;
    }

    if (sseConnection) {
        try {
            sseConnection.close();
        } catch {
            // ignore
        }

        sseConnection = null;
    }

    const url =
        `/api/multi-client-sync/events?clientId=${encodeURIComponent(
            CLIENT_ID,
        )}&chatKey=${encodeURIComponent(
            expectedChatKey,
        )}`;

    const es =
        new EventSource(url);

    es.onopen = () => {
        if (
            expectedGeneration !==
                connectionGeneration ||
            !isCurrentChatKey(
                expectedChatKey,
            )
        ) {
            try {
                es.close();
            } catch {
                // ignore
            }

            return;
        }

        isConnected = true;
        reconnectDelay =
            INITIAL_RECONNECT_DELAY_MS;
        reconnectChatKey =
            expectedChatKey;

        updateStatusUI();

        log('SSE connected');
    };

    es.onmessage = (event) => {
        if (
            expectedGeneration !==
                connectionGeneration ||
            !isCurrentChatKey(
                expectedChatKey,
            )
        ) {
            try {
                es.close();
            } catch {
                // ignore
            }

            return;
        }

        try {
            const data =
                JSON.parse(event.data);

            if (
                data.type ===
                'CONNECTED'
            ) {
                const sequence =
                    Number(data.sequence);

                if (
                    Number.isSafeInteger(
                        sequence,
                    ) &&
                    sequence >= 0
                ) {
                    knownServerHeadSequence =
                        Math.max(
                            knownServerHeadSequence,
                            sequence,
                        );

                    if (
                        sequence >
                        lastSequence
                    ) {
                        requestSequenceRecovery(
                            sequence,
                        ).catch((e) =>
                            warn(
                                'CONNECTED recovery failed',
                                e,
                            ),
                        );
                    }
                }

                return;
            }

            if (
                data.chatKey &&
                data.chatKey !==
                    expectedChatKey
            ) {
                return;
            }

            handleRemoteEvent(
                data,
                false,
                expectedChatKey,
            );
        } catch (e) {
            warn(
                'SSE parse error',
                e,
            );
        }
    };

    es.onerror = () => {
        if (
            expectedGeneration !==
                connectionGeneration ||
            !isCurrentChatKey(
                expectedChatKey,
            )
        ) {
            try {
                es.close();
            } catch {
                // ignore
            }

            return;
        }

        isConnected = false;
        updateStatusUI();

        try {
            es.close();
        } catch {
            // ignore
        }

        if (sseConnection === es) {
            sseConnection = null;
        }

        scheduleReconnect(
            expectedChatKey,
            expectedGeneration,
        );
    };

    sseConnection = es;
}

function scheduleReconnect(
    expectedChatKey = currentChatKey,
    expectedGeneration =
        connectionGeneration,
) {
    if (
        !expectedChatKey ||
        reconnectTimer ||
        !getSettings().enabled
    ) {
        return;
    }

    reconnectChatKey =
        expectedChatKey;

    reconnectTimer =
        window.setTimeout(() => {
            reconnectTimer = null;

            if (
                !getSettings().enabled
            ) {
                return;
            }

            if (
                expectedGeneration !==
                connectionGeneration
            ) {
                return;
            }

            if (
                !isCurrentChatKey(
                    expectedChatKey,
                )
            ) {
                return;
            }

            reconnectDelay =
                Math.min(
                    reconnectDelay * 2,
                    MAX_RECONNECT_DELAY_MS,
                );

            void syncJoinCurrentChat({
                expectedChatKey,
                expectedGeneration,
                force: true,
            });
        }, reconnectDelay);
}

async function syncJoinCurrentChat(
    options = {},
) {
    const settings =
        getSettings();

    if (!settings.enabled) {
        return false;
    }

    const ident =
        getChatIdentity();

    if (!ident.chatId) {
        return false;
    }

    const expectedChatKey =
        options.expectedChatKey ||
        buildChatKey(ident);

    if (
        getCurrentDesiredChatKey() !==
        expectedChatKey
    ) {
        return false;
    }

    if (
        !options.force &&
        currentChatKey ===
            expectedChatKey &&
        sseConnection &&
        isConnected
    ) {
        return true;
    }

    const token =
        options.expectedGeneration ??
        ++connectionGeneration;

    if (
        token !== connectionGeneration
    ) {
        return false;
    }

    const ok =
        await joinGroup(
            ident,
            token,
            options,
        );

    if (!ok) {
        if (
            getSettings().enabled &&
            isCurrentChatKey(
                expectedChatKey,
            )
        ) {
            scheduleReconnect(
                expectedChatKey,
                token,
            );
        }

        return false;
    }

    if (
        token !==
            connectionGeneration ||
        !isCurrentChatKey(
            expectedChatKey,
        )
    ) {
        return false;
    }

    connectSSE(
        expectedChatKey,
        token,
    );

    startHeartbeat(
        expectedChatKey,
        token,
    );

    return true;
}

function publishOwnerReleaseBestEffort(
    chatKey,
    generation,
) {
    if (
        !chatKey ||
        !generation?.generationId
    ) {
        return;
    }

    const event = {
        eventId:
            `${CLIENT_ID}-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
        clientId: CLIENT_ID,
        deviceId: DEVICE_ID,
        userId: getUserId(),
        chatKey,
        type: 'GENERATION_OWNER_RELEASED',
        generationId:
            generation.generationId,
        timestamp: Date.now(),
        payload: {
            ownerId: CLIENT_ID,
            ownerDevice: DEVICE_ID,
            reason: 'client-leave',
        },
    };

    try {
        fetch(
            '/api/multi-client-sync/event',
            {
                method: 'POST',
                headers: {
                    ...getRequestHeaders(),
                    'Content-Type':
                        'application/json',
                },
                body: JSON.stringify({
                    clientId:
                        CLIENT_ID,
                    deviceId:
                        DEVICE_ID,
                    userId:
                        getUserId(),
                    chatKey,
                    event,
                }),
                keepalive: true,
            },
        ).catch(() => {});
    } catch {
        // best effort only
    }
}

function leaveGroup() {
    const oldChatKey =
        currentChatKey;

    const oldGeneration =
        activeGeneration;

    connectionGeneration++;
    chatChangeGeneration++;

    if (reconnectTimer) {
        clearTimeout(reconnectTimer);
        reconnectTimer = null;
    }

    reconnectChatKey = null;

    if (heartbeatTimer) {
        clearInterval(heartbeatTimer);
        heartbeatTimer = null;
    }

    clearChatSaveTimer();

    if (
        oldGeneration &&
        isGenerationOwner &&
        oldChatKey
    ) {
        publishOwnerReleaseBestEffort(
            oldChatKey,
            oldGeneration,
        );
    }

    if (sseConnection) {
        try {
            sseConnection.close();
        } catch {
            // ignore
        }

        sseConnection = null;
    }

    if (oldChatKey) {
        apiPost(
            '/leave',
            {
                clientId:
                    CLIENT_ID,
                userId:
                    getUserId(),
                chatKey:
                    oldChatKey,
            },
        ).catch(() => {});
    }

    currentChatKey = null;
    isConnected = false;
    lastSequence = 0;
    knownServerHeadSequence = 0;

    activeGeneration = null;
    isGenerationOwner = false;

    pendingSequenceEvents.clear();
    pendingGenerationConflicts.clear();
    pendingRemoteGenerationAfterLocalStop =
        null;

    streamStates.clear();

    updateStatusUI();
}

function startHeartbeat(
    expectedChatKey = currentChatKey,
    expectedGeneration =
        connectionGeneration,
) {
    if (heartbeatTimer) {
        clearInterval(heartbeatTimer);
    }

    if (!expectedChatKey) {
        return;
    }

    heartbeatTimer =
        window.setInterval(() => {
            if (
                expectedGeneration !==
                connectionGeneration
            ) {
                return;
            }

            if (
                !isCurrentChatKey(
                    expectedChatKey,
                )
            ) {
                return;
            }

            apiPost(
                '/heartbeat',
                {
                    clientId:
                        CLIENT_ID,
                    userId:
                        getUserId(),
                    chatKey:
                        expectedChatKey,
                },
            ).catch(() => {});
        }, HEARTBEAT_INTERVAL_MS);
}

// ---------------------------------------------------------------------------
// Event Publishing
// ---------------------------------------------------------------------------

async function publishEvent(
    type,
    payload,
    extra = {},
) {
    const settings =
        getSettings();

    if (
        !settings.enabled ||
        !currentChatKey
    ) {
        return null;
    }

    const chatKey =
        currentChatKey;

    const event = {
        eventId:
            `${CLIENT_ID}-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
        clientId:
            CLIENT_ID,
        deviceId:
            DEVICE_ID,
        userId:
            getUserId(),
        chatKey,
        type,
        payload:
            safeClone(payload),
        timestamp:
            Date.now(),
        ...extra,
    };

    try {
        const result =
            await apiPost(
                '/event',
                {
                    clientId:
                        CLIENT_ID,
                    deviceId:
                        DEVICE_ID,
                    userId:
                        getUserId(),
                    chatKey,
                    event,
                },
            );

        if (!result?.success) {
            warn(
                'publish rejected',
                type,
                result?.error ||
                    result,
            );

            return null;
        }

        const acceptedEvent =
            safeClone(
                result.event || event,
            );

        acceptedEvent.clientId ??=
            CLIENT_ID;

        acceptedEvent.deviceId ??=
            DEVICE_ID;

        acceptedEvent.userId ??=
            getUserId();

        acceptedEvent.chatKey ??=
            chatKey;

        acceptedEvent.type ??=
            type;

        acceptedEvent.payload ??=
            safeClone(payload);

        acceptedEvent.timestamp ??=
            event.timestamp;

        if (
            !getEventSequence(
                acceptedEvent,
            ) &&
            Number.isSafeInteger(
                Number(result.sequence),
            )
        ) {
            acceptedEvent.sequence =
                Number(result.sequence);
        }

        const sequence =
            getEventSequence(
                acceptedEvent,
            );

        if (!sequence) {
            warn(
                'Server accepted event without sequence',
                acceptedEvent,
            );

            return null;
        }

        knownServerHeadSequence =
            Math.max(
                knownServerHeadSequence,
                sequence,
            );

        /*
         * Feed our own acknowledged event through
         * the exact same ordering pipeline as remote
         * events. The SillyTavern local action has
         * already happened, so handlers must be
         * idempotent.
         */
        acceptSequencedEvent(
            acceptedEvent,
            'local-ack',
            true,
            true,
        );

        /*
         * Only broadcast once the server has given the
         * event its authoritative sequence.
         */
        bcBroadcast(
            acceptedEvent,
            chatKey,
        );

        return {
            ...result,
            event:
                acceptedEvent,
            sequence,
        };
    } catch (e) {
        warn(
            'publishEvent failed',
            type,
            e,
        );

        return null;
    }
}

// ---------------------------------------------------------------------------
// Remote Message Application
// ---------------------------------------------------------------------------

function getInsertAnchors(
    ctx,
    index,
) {
    return {
        beforeKey:
            index >= 0 &&
            index < ctx.chat.length
                ? getMessageKey(
                    ctx.chat[index],
                    index,
                )
                : null,

        afterKey:
            index > 0 &&
            index - 1 < ctx.chat.length
                ? getMessageKey(
                    ctx.chat[index - 1],
                    index - 1,
                )
                : null,
    };
}

function resolveInsertionIndex(
    ctx,
    payload,
) {
    if (payload?.afterMessageKey) {
        const afterIndex =
            findMessageIndexByKey(
                payload.afterMessageKey,
            );

        if (afterIndex >= 0) {
            return afterIndex + 1;
        }
    }

    if (payload?.beforeMessageKey) {
        const beforeIndex =
            findMessageIndexByKey(
                payload.beforeMessageKey,
            );

        if (beforeIndex >= 0) {
            return beforeIndex;
        }
    }

    if (
        Number.isInteger(
            payload?.insertAt,
        )
    ) {
        return Math.max(
            0,
            Math.min(
                payload.insertAt,
                ctx.chat.length,
            ),
        );
    }

    return ctx.chat.length;
}

function refreshVisibleMessageIds() {
    const nodes =
        Array.from(
            document.querySelectorAll(
                '#chat .mes',
            ),
        );

    if (nodes.length === 0) {
        return;
    }

    let firstId =
        Number(
            nodes[0].getAttribute(
                'mesid',
            ),
        );

    if (!Number.isFinite(firstId)) {
        firstId = 0;
    }

    nodes.forEach(
        (
            node,
            offset,
        ) => {
            const id =
                firstId + offset;

            node.setAttribute(
                'mesid',
                String(id),
            );

            const display =
                node.querySelector(
                    '.mesIDDisplay',
                );

            if (display) {
                display.textContent =
                    `#${id}`;
            }
        },
    );
}

function applyRemoteMessageInserted(
    event,
) {
    const payload =
        event.payload;

    const message =
        payload?.message;

    if (!message) {
        return;
    }

    const ctx =
        getContext();

    const messageKey =
        payload.messageKey ||
        getMessageKey(
            message,
            payload.insertAt,
        );

    const sequence =
        getEventSequence(event);

    if (messageKey) {
        const existingIndex =
            findMessageIndexByKey(
                messageKey,
            );

        const tombstone =
            messageTombstones.get(
                messageKey,
            ) ?? 0;

        if (existingIndex >= 0) {
            return;
        }

        if (
            tombstone > 0 &&
            sequence &&
            sequence <= tombstone
        ) {
            return;
        }
    }

    const insertIndex =
        resolveInsertionIndex(
            ctx,
            payload,
        );

    const clonedMessage =
        safeClone(message);

    ctx.chat.splice(
        insertIndex,
        0,
        clonedMessage,
    );

    if (
        typeof ctx.addOneMessage ===
        'function'
    ) {
        const options = {
            scroll: false,
            forceId:
                insertIndex,
        };

        if (insertIndex > 0) {
            options.insertAfter =
                insertIndex - 1;
        } else if (
            ctx.chat.length > 1
        ) {
            options.insertBefore =
                1;
        }

        ctx.addOneMessage(
            clonedMessage,
            options,
        );
    }

    refreshVisibleMessageIds();

    if (messageKey && sequence) {
        messageRevisions.set(
            messageKey,
            sequence,
        );
    }

    scheduleChatSave();
}

function applyRemoteMessageEdited(
    event,
) {
    const payload =
        event.payload;

    const sequence =
        getEventSequence(event);

    if (
        !payload ||
        sequence === null
    ) {
        return;
    }

    if (
        isStaleMessageMutation(
            payload,
            sequence,
        )
    ) {
        return;
    }

    const messageIndex =
        findMessageIndex(
            payload,
        );

    if (messageIndex < 0) {
        warn(
            'remote edit target not found',
            payload,
        );

        return;
    }

    const ctx =
        getContext();

    const msg =
        ctx.chat[messageIndex];

    if (!msg) {
        return;
    }

    if (
        payload.mes !== undefined
    ) {
        msg.mes =
            payload.mes;
    }

    if (
        payload.swipes !== undefined
    ) {
        msg.swipes =
            safeClone(
                payload.swipes,
            );
    }

    if (
        payload.swipe_id !== undefined
    ) {
        msg.swipe_id =
            payload.swipe_id;
    }

    if (
        payload.extra !== undefined
    ) {
        msg.extra =
            safeClone(
                payload.extra,
            );
    }

    ctx.updateMessageBlock(
        messageIndex,
        msg,
    );

    recordMessageRevision(
        payload,
        sequence,
    );

    scheduleChatSave();
}

function applyRemoteMessageDeleted(
    event,
) {
    const payload =
        event.payload;

    const sequence =
        getEventSequence(event);

    if (
        !payload ||
        sequence === null
    ) {
        return;
    }

    const ctx =
        getContext();

    const indices =
        new Set();

    const keys =
        Array.isArray(
            payload.deletedMessageKeys,
        )
            ? payload.deletedMessageKeys
            : [];

    for (const key of keys) {
        recordMessageTombstone(
            key,
            sequence,
        );

        const idx =
            findMessageIndexByKey(
                key,
            );

        if (idx >= 0) {
            indices.add(idx);
        }
    }

    const ids =
        Array.isArray(
            payload.deletedIds,
        )
            ? payload.deletedIds
            : [];

    for (const id of ids) {
        if (
            Number.isInteger(id) &&
            id >= 0 &&
            id < ctx.chat.length
        ) {
            const key =
                getMessageKey(
                    ctx.chat[id],
                    id,
                );

            if (key) {
                recordMessageTombstone(
                    key,
                    sequence,
                );
            }

            indices.add(id);
        }
    }

    const sorted =
        [...indices].sort(
            (a, b) => b - a,
        );

    for (
        const messageIndex of sorted
    ) {
        try {
            if (!ctx.chat[messageIndex]) {
                continue;
            }

            const node =
                document.querySelector(
                    `#chat .mes[mesid="${messageIndex}"]`,
                );

            if (node) {
                node.remove();
            }

            ctx.chat.splice(
                messageIndex,
                1,
            );
        } catch (e) {
            warn(
                'remote delete failed',
                messageIndex,
                e,
            );
        }
    }

    refreshVisibleMessageIds();
    scheduleChatSave();
}

function applyRemoteMessageSwiped(
    event,
) {
    const payload =
        event.payload;

    const sequence =
        getEventSequence(event);

    if (
        !payload ||
        sequence === null
    ) {
        return;
    }

    if (
        isStaleMessageMutation(
            payload,
            sequence,
        )
    ) {
        return;
    }

    const messageIndex =
        findMessageIndex(
            payload,
        );

    if (messageIndex < 0) {
        warn(
            'remote swipe target not found',
            payload,
        );

        return;
    }

    const ctx =
        getContext();

    const msg =
        ctx.chat[messageIndex];

    if (!msg) {
        return;
    }

    if (
        payload.swipes !== undefined
    ) {
        msg.swipes =
            safeClone(
                payload.swipes,
            );
    }

    if (
        payload.swipe_id !== undefined
    ) {
        msg.swipe_id =
            payload.swipe_id;

        if (
            Array.isArray(msg.swipes) &&
            msg.swipes[
                msg.swipe_id
            ] !== undefined
        ) {
            msg.mes =
                msg.swipes[
                    msg.swipe_id
                ];
        }
    }

    ctx.updateMessageBlock(
        messageIndex,
        msg,
    );

    recordMessageRevision(
        payload,
        sequence,
    );

    scheduleChatSave();
}

// ---------------------------------------------------------------------------
// Generation / streaming helpers
// ---------------------------------------------------------------------------

function getGenerationStreamState(
    generationId,
) {
    if (!generationId) {
        return null;
    }

    let state =
        streamStates.get(
            generationId,
        );

    if (!state) {
        state = {
            nextExpected: 1,
            pending: new Map(),
        };

        streamStates.set(
            generationId,
            state,
        );
    }

    return state;
}

function scheduleStreamRender(
    generationId,
    messageKey,
) {
    const existing =
        streamRenderTimers.get(
            generationId,
        );

    if (existing) {
        return;
    }

    const timer =
        window.setTimeout(
            () => {
                streamRenderTimers.delete(
                    generationId,
                );

                flushStreamRender(
                    generationId,
                    messageKey,
                );
            },
            STREAM_RENDER_DEBOUNCE_MS,
        );

    streamRenderTimers.set(
        generationId,
        {
            timer,
            messageKey:
                messageKey || null,
        },
    );
}

function flushStreamRender(
    generationId,
    messageKey = null,
) {
    const target =
        messageKey ||
        activeGeneration?.messageKey ||
        null;

    const ctx =
        getContext();

    let messageIndex =
        target
            ? findMessageIndexByKey(
                target,
            )
            : -1;

    if (
        messageIndex < 0 &&
        Number.isInteger(
            activeGeneration?.messageIndex,
        )
    ) {
        messageIndex =
            activeGeneration.messageIndex;
    }

    if (messageIndex < 0) {
        for (
            let i =
                ctx.chat.length - 1;
            i >= 0;
            i--
        ) {
            if (
                ctx.chat[i] &&
                !ctx.chat[i].is_user &&
                !ctx.chat[i].is_system
            ) {
                messageIndex = i;
                break;
            }
        }
    }

    if (
        messageIndex < 0 ||
        !ctx.chat[messageIndex]
    ) {
        return;
    }

    ctx.updateMessageBlock(
        messageIndex,
        ctx.chat[messageIndex],
    );
}

function clearStreamRenderTimer(
    generationId,
) {
    const current =
        streamRenderTimers.get(
            generationId,
        );

    if (!current) {
        return;
    }

    clearTimeout(
        current.timer,
    );

    streamRenderTimers.delete(
        generationId,
    );
}

function findGenerationMessageIndex(
    generation,
    payload = {},
) {
    const ctx =
        getContext();

    if (payload.messageKey) {
        const idx =
            findMessageIndexByKey(
                payload.messageKey,
            );

        if (idx >= 0) {
            return idx;
        }
    }

    if (generation?.messageKey) {
        const idx =
            findMessageIndexByKey(
                generation.messageKey,
            );

        if (idx >= 0) {
            return idx;
        }
    }

    if (
        Number.isInteger(
            payload.messageId,
        ) &&
        payload.messageId >= 0 &&
        payload.messageId <
            ctx.chat.length
    ) {
        return payload.messageId;
    }

    if (
        Number.isInteger(
            generation?.messageIndex,
        ) &&
        generation.messageIndex >= 0 &&
        generation.messageIndex <
            ctx.chat.length
    ) {
        return generation.messageIndex;
    }

    for (
        let i =
            ctx.chat.length - 1;
        i >= 0;
        i--
    ) {
        if (
            ctx.chat[i] &&
            !ctx.chat[i].is_user &&
            !ctx.chat[i].is_system
        ) {
            return i;
        }
    }

    return -1;
}

function initializeGenerationMessage(
    event,
    generation,
) {
    const payload =
        event.payload || {};

    const ctx =
        getContext();

    if (payload.message) {
        const messageKey =
            payload.messageKey ||
            getMessageKey(
                payload.message,
                payload.messageId,
            );

        const existingIndex =
            messageKey
                ? findMessageIndexByKey(
                    messageKey,
                )
                : -1;

        if (existingIndex >= 0) {
            generation.messageIndex =
                existingIndex;

            generation.messageKey =
                messageKey;

            return existingIndex;
        }

        const insertAt =
            Number.isInteger(
                payload.insertAt,
            )
                ? Math.max(
                    0,
                    Math.min(
                        payload.insertAt,
                        ctx.chat.length,
                    ),
                )
                : ctx.chat.length;

        ctx.chat.splice(
            insertAt,
            0,
            safeClone(
                payload.message,
            ),
        );

        if (
            typeof ctx.addOneMessage ===
            'function'
        ) {
            const options = {
                scroll: false,
                forceId: insertAt,
            };

            if (insertAt > 0) {
                options.insertAfter =
                    insertAt - 1;
            } else if (
                ctx.chat.length > 1
            ) {
                options.insertBefore =
                    1;
            }

            ctx.addOneMessage(
                ctx.chat[insertAt],
                options,
            );
        }

        refreshVisibleMessageIds();

        generation.messageIndex =
            insertAt;

        generation.messageKey =
            messageKey ||
            getMessageKey(
                ctx.chat[insertAt],
                insertAt,
            );

        scheduleChatSave(
            STREAM_SAVE_DEBOUNCE_MS,
        );

        return insertAt;
    }

    const idx =
        findGenerationMessageIndex(
            generation,
            payload,
        );

    if (idx >= 0) {
        generation.messageIndex =
            idx;

        generation.messageKey =
            generation.messageKey ||
            getMessageKey(
                ctx.chat[idx],
                idx,
            );
    }

    return idx;
}

function restoreGenerationState(
    serverGeneration,
) {
    if (!serverGeneration) {
        if (
            activeGeneration &&
            activeGeneration.status ===
                'active'
        ) {
            log(
                'server reports no active generation; clearing stale local generation',
            );
        }

        activeGeneration = null;
        isGenerationOwner = false;
        updateStatusUI();

        return;
    }

    activeGeneration = {
        ...safeClone(
            serverGeneration,
        ),

        streamSeqApplied:
            Number(
                serverGeneration.streamSeqApplied ??
                serverGeneration.streamSeq ??
                serverGeneration.lastStreamSeq ??
                0,
            ),

        streamSeq:
            Number(
                serverGeneration.streamSeq ??
                serverGeneration.streamSeqApplied ??
                serverGeneration.lastStreamSeq ??
                0,
            ),
    };

    isGenerationOwner =
        activeGeneration.ownerId ===
        CLIENT_ID;

    const streamState =
        getGenerationStreamState(
            activeGeneration.generationId,
        );

    streamState.nextExpected =
        Math.max(
            1,
            activeGeneration.streamSeqApplied +
                1,
        );

    streamState.pending.clear();

    const currentText =
        activeGeneration.currentText ??
        activeGeneration.text;

    if (
        currentText !== undefined
    ) {
        const idx =
            findGenerationMessageIndex(
                activeGeneration,
                {},
            );

        if (idx >= 0) {
            const ctx =
                getContext();

            ctx.chat[idx].mes =
                currentText;

            activeGeneration.messageIndex =
                idx;

            activeGeneration.messageKey =
                activeGeneration.messageKey ||
                getMessageKey(
                    ctx.chat[idx],
                    idx,
                );

            ctx.updateMessageBlock(
                idx,
                ctx.chat[idx],
            );
        }
    }

    updateStatusUI();
}

function resolveGenerationConflict(
    remoteEvent,
) {
    const localGeneration =
        activeGeneration;

    if (
        !localGeneration ||
        !remoteEvent?.generationId
    ) {
        return false;
    }

    if (
        localGeneration.generationId ===
        remoteEvent.generationId
    ) {
        return true;
    }

    const localSequence =
        Number(
            localGeneration.serverSequence,
        );

    const remoteSequence =
        getEventSequence(
            remoteEvent,
        );

    if (
        !Number.isSafeInteger(
            localSequence,
        ) ||
        !Number.isSafeInteger(
            remoteSequence,
        )
    ) {
        pendingGenerationConflicts.set(
            remoteEvent.generationId,
            remoteEvent,
        );

        log(
            'deferring generation conflict until server sequence is known',
        );

        return true;
    }

    if (
        remoteSequence < localSequence
    ) {
        pendingRemoteGenerationAfterLocalStop =
            remoteEvent;

        const localGenerationId =
            localGeneration.generationId;

        suppressedGenerationStopPublishes.delete(
            localGenerationId,
        );

        try {
            const ctx =
                getContext();

            if (
                typeof ctx.stopGeneration ===
                'function'
            ) {
                Promise.resolve(
                    ctx.stopGeneration(),
                ).catch((e) =>
                    warn(
                        'failed to stop losing local generation',
                        e,
                    ),
                );
            }
        } catch (e) {
            warn(
                'failed to stop losing local generation',
                e,
            );
        }

        activeGeneration = null;
        isGenerationOwner = false;

        activateRemoteGeneration(
            remoteEvent,
        );

        return true;
    }

    void requestRemoteStopForGeneration(
        remoteEvent.generationId,
    );

    return true;
}

function activateRemoteGeneration(
    event,
) {
    if (
        activeGeneration?.generationId &&
        activeGeneration.generationId !==
            event.generationId
    ) {
        clearStreamRenderTimer(
            activeGeneration.generationId,
        );
    }

    activeGeneration = {
        generationId:
            event.generationId,

        ownerId:
            event.clientId,

        ownerDevice:
            event.deviceId,

        status:
            'active',

        startedAt:
            event.timestamp ||
            Date.now(),

        serverSequence:
            getEventSequence(event),

        streamSeqApplied:
            0,

        streamSeq:
            0,
    };

    initializeGenerationMessage(
        event,
        activeGeneration,
    );

    isGenerationOwner =
        event.clientId ===
        CLIENT_ID;

    const streamState =
        getGenerationStreamState(
            activeGeneration.generationId,
        );

    streamState.nextExpected = 1;
    streamState.pending.clear();

    updateStatusUI();

    log(
        'generation started by',
        event.clientId,
        event.generationId,
    );
}

function applyRemoteGenerationStarted(
    event,
) {
    if (!event.generationId) {
        return;
    }

    if (
        activeGeneration?.generationId ===
        event.generationId
    ) {
        if (
            Number.isSafeInteger(
                getEventSequence(event),
            )
        ) {
            activeGeneration.serverSequence =
                getEventSequence(event);
        }

        initializeGenerationMessage(
            event,
            activeGeneration,
        );

        return;
    }

    if (
        activeGeneration &&
        activeGeneration.status ===
            'active' &&
        activeGeneration.ownerId ===
            CLIENT_ID
    ) {
        if (
            resolveGenerationConflict(
                event,
            )
        ) {
            return;
        }
    } else if (
        activeGeneration &&
        activeGeneration.status ===
            'active'
    ) {
        const existingSequence =
            Number(
                activeGeneration.serverSequence,
            );

        const remoteSequence =
            getEventSequence(event);

        if (
            Number.isSafeInteger(
                existingSequence,
            ) &&
            Number.isSafeInteger(
                remoteSequence,
            )
        ) {
            if (
                remoteSequence <
                existingSequence
            ) {
                activateRemoteGeneration(
                    event,
                );
            } else if (
                remoteSequence >
                existingSequence
            ) {
                void requestRemoteStopForGeneration(
                    event.generationId,
                );
            }

            return;
        }
    }

    const deferred =
        pendingGenerationConflicts.get(
            event.generationId,
        );

    if (deferred) {
        pendingGenerationConflicts.delete(
            event.generationId,
        );
    }

    activateRemoteGeneration(
        event,
    );
}

function applyRemoteGenerationStream(
    event,
) {
    if (
        !activeGeneration ||
        activeGeneration.generationId !==
            event.generationId
    ) {
        return;
    }

    const streamSeq =
        Number(event.streamSeq);

    if (
        !Number.isSafeInteger(
            streamSeq,
        ) ||
        streamSeq <= 0
    ) {
        warn(
            'Ignoring generation stream event without valid stream sequence',
            event,
        );

        return;
    }

    if (
        streamSeq <=
        Number(
            activeGeneration.streamSeqApplied ||
                0,
        )
    ) {
        return;
    }

    const streamState =
        getGenerationStreamState(
            event.generationId,
        );

    const expected =
        Number(
            activeGeneration.streamSeqApplied ||
                0,
        ) + 1;

    if (streamSeq > expected) {
        if (
            !streamState.pending.has(
                streamSeq,
            )
        ) {
            streamState.pending.set(
                streamSeq,
                event,
            );
        }

        warn(
            'stream sequence gap detected',
            {
                generationId:
                    event.generationId,
                expected,
                received:
                    streamSeq,
            },
        );

        requestSequenceRecovery(
            getEventSequence(event) || 0,
        ).catch((e) =>
            warn(
                'stream recovery failed',
                e,
            ),
        );

        return;
    }

    const applyChunk =
        (streamEvent) => {
            const seq =
                Number(
                    streamEvent.streamSeq,
                );

            if (
                seq <=
                Number(
                    activeGeneration.streamSeqApplied ||
                        0,
                )
            ) {
                return true;
            }

            const payload =
                streamEvent.payload ||
                {};

            const ctx =
                getContext();

            let messageIndex =
                findGenerationMessageIndex(
                    activeGeneration,
                    payload,
                );

            if (
                messageIndex < 0 &&
                payload.message
            ) {
                messageIndex =
                    initializeGenerationMessage(
                        streamEvent,
                        activeGeneration,
                    );
            }

            if (messageIndex < 0) {
                warn(
                    'stream message target not found; waiting for message event',
                    streamEvent,
                );

                return false;
            }

            const message =
                ctx.chat[messageIndex];

            if (!message) {
                return false;
            }

            if (
                payload.messageKey
            ) {
                activeGeneration.messageKey =
                    payload.messageKey;
            }

            activeGeneration.messageIndex =
                messageIndex;

            activeGeneration.streamSeqApplied =
                seq;

            activeGeneration.streamSeq =
                Math.max(
                    Number(
                        activeGeneration.streamSeq ||
                            0,
                    ),
                    seq,
                );

            const chunk =
                String(
                    payload.chunk ??
                        '',
                );

            if (chunk) {
                message.mes =
                    `${message.mes || ''}${chunk}`;

                scheduleStreamRender(
                    event.generationId,
                    activeGeneration.messageKey,
                );

                scheduleChatSave(
                    STREAM_SAVE_DEBOUNCE_MS,
                );
            }

            return true;
        };

    if (!applyChunk(event)) {
        return;
    }

    streamState.nextExpected =
        Number(
            activeGeneration.streamSeqApplied ||
                0,
        ) + 1;

    while (
        streamState.pending.has(
            streamState.nextExpected,
        )
    ) {
        const nextEvent =
            streamState.pending.get(
                streamState.nextExpected,
            );

        streamState.pending.delete(
            streamState.nextExpected,
        );

        if (!applyChunk(nextEvent)) {
            break;
        }

        streamState.nextExpected =
            Number(
                activeGeneration.streamSeqApplied ||
                    0,
            ) + 1;
    }
}

function activatePendingRemoteGenerationAfterLocalStop(
    localGenerationId,
) {
    const pending =
        pendingRemoteGenerationAfterLocalStop;

    if (!pending) {
        return;
    }

    if (
        activeGeneration?.generationId ===
        localGenerationId
    ) {
        return;
    }

    pendingRemoteGenerationAfterLocalStop =
        null;

    activateRemoteGeneration(
        pending,
    );
}

function applyRemoteGenerationStopRequested(
    event,
) {
    if (!activeGeneration) {
        return;
    }

    if (
        activeGeneration.generationId !==
        event.generationId
    ) {
        return;
    }

    if (!isGenerationOwner) {
        return;
    }

    try {
        const ctx =
            getContext();

        if (
            typeof ctx.stopGeneration !==
            'function'
        ) {
            warn(
                'SillyTavern stopGeneration API is unavailable',
            );

            return;
        }

        log(
            'remote stop requested by',
            event.clientId,
        );

        Promise.resolve(
            ctx.stopGeneration(),
        ).catch((e) =>
            warn(
                'remote stop failed',
                e,
            ),
        );
    } catch (e) {
        warn(
            'remote stop request handling failed',
            e,
        );
    }
}

function applyRemoteGenerationStopped(
    event,
) {
    if (
        !activeGeneration ||
        activeGeneration.generationId !==
            event.generationId
    ) {
        return;
    }

    flushStreamRender(
        event.generationId,
        activeGeneration.messageKey,
    );

    clearStreamRenderTimer(
        event.generationId,
    );

    const localGenerationId =
        activeGeneration.generationId;

    activeGeneration.status =
        'stopped';

    activeGeneration.endedAt =
        event.timestamp ||
        Date.now();

    isGenerationOwner = false;

    finishedGenerationIds.add(
        localGenerationId,
    );

    if (
        finishedGenerationIds.size > 1000
    ) {
        const first =
            finishedGenerationIds
                .values()
                .next();

        if (!first.done) {
            finishedGenerationIds.delete(
                first.value,
            );
        }
    }

    scheduleChatSave();
    updateStatusUI();

    if (
        pendingRemoteGenerationAfterLocalStop
            ?.generationId
    ) {
        const pending =
            pendingRemoteGenerationAfterLocalStop;

        pendingRemoteGenerationAfterLocalStop =
            null;

        activateRemoteGeneration(
            pending,
        );
    } else {
        activeGeneration = null;
        isGenerationOwner = false;
    }

    updateStatusUI();

    log(
        'generation stopped',
        localGenerationId,
    );
}

function applyRemoteGenerationCompleted(
    event,
) {
    if (
        !activeGeneration ||
        activeGeneration.generationId !==
            event.generationId
    ) {
        return;
    }

    flushStreamRender(
        event.generationId,
        activeGeneration.messageKey,
    );

    clearStreamRenderTimer(
        event.generationId,
    );

    activeGeneration.status =
        'completed';

    activeGeneration.endedAt =
        event.timestamp ||
        Date.now();

    isGenerationOwner = false;

    finishedGenerationIds.add(
        activeGeneration.generationId,
    );

    scheduleChatSave();
    updateStatusUI();

    activeGeneration = null;
    isGenerationOwner = false;

    updateStatusUI();

    log(
        'generation completed',
        event.generationId,
    );
}

function applyRemoteGenerationFailed(
    event,
) {
    if (
        !activeGeneration ||
        activeGeneration.generationId !==
            event.generationId
    ) {
        return;
    }

    flushStreamRender(
        event.generationId,
        activeGeneration.messageKey,
    );

    clearStreamRenderTimer(
        event.generationId,
    );

    activeGeneration.status =
        'failed';

    activeGeneration.endedAt =
        event.timestamp ||
        Date.now();

    isGenerationOwner = false;

    finishedGenerationIds.add(
        activeGeneration.generationId,
    );

    scheduleChatSave();
    updateStatusUI();

    activeGeneration = null;
    isGenerationOwner = false;

    updateStatusUI();

    log(
        'generation failed',
        event.generationId,
    );
}

function applyRemoteOwnerReleased(
    event,
) {
    if (!activeGeneration) {
        return;
    }

    if (
        activeGeneration.generationId !==
        event.generationId
    ) {
        return;
    }

    if (
        activeGeneration.ownerId !==
        event.payload?.ownerId
    ) {
        return;
    }

    activeGeneration.status =
        'orphaned';

    activeGeneration.orphanedAt =
        event.timestamp ||
        Date.now();

    isGenerationOwner = false;

    updateStatusUI();

    log(
        'generation owner released',
        event.generationId,
    );
}

function applyRemoteChatReloaded(
    payload,
) {
    const ctx =
        getContext();

    if (
        !payload?.chatId ||
        String(payload.chatId) !==
            String(ctx.chatId)
    ) {
        return;
    }

    if (
        typeof ctx.reloadCurrentChat ===
        'function'
    ) {
        isReconcilingChat = true;

        Promise.resolve(
            ctx.reloadCurrentChat(),
        )
            .catch((e) =>
                warn(
                    'CHAT_RELOADED reconciliation failed',
                    e,
                ),
            )
            .finally(() => {
                isReconcilingChat = false;
                updateStatusUI();
            });
    }
}

async function requestRemoteStopForGeneration(
    generationId,
) {
    if (
        !generationId ||
        !currentChatKey
    ) {
        return null;
    }

    return publishEvent(
        'GENERATION_STOP_REQUESTED',
        {
            requestedBy:
                CLIENT_ID,
            requestedAt:
                Date.now(),
        },
        {
            generationId,
        },
    );
}

// ---------------------------------------------------------------------------
// Generation publishing queue
// ---------------------------------------------------------------------------

function enqueueGenerationPublish(
    generationId,
    action,
) {
    const previous =
        generationPublishChains.get(
            generationId,
        ) ||
        Promise.resolve();

    const next =
        previous
            .catch(() => {})
            .then(action);

    generationPublishChains.set(
        generationId,
        next,
    );

    next.finally(() => {
        if (
            generationPublishChains.get(
                generationId,
            ) === next
        ) {
            generationPublishChains.delete(
                generationId,
            );
        }
    }).catch(() => {});

    return next;
}

// ---------------------------------------------------------------------------
// Local Event Hooks
// ---------------------------------------------------------------------------

function onMessageSent(
    messageId,
) {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    const ctx =
        getContext();

    const msg =
        ctx.chat[messageId];

    if (!msg) {
        return;
    }

    const key =
        getMessageKey(
            msg,
            messageId,
        );

    const anchors =
        getInsertAnchors(
            ctx,
            messageId,
        );

    void publishEvent(
        'MESSAGE_SENT',
        {
            message:
                safeClone(msg),

            messageId,

            messageKey:
                key,

            insertAt:
                messageId,

            beforeMessageKey:
                anchors.beforeKey,

            afterMessageKey:
                anchors.afterKey,
        },
    );
}

function onMessageReceived(
    messageId,
) {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    const ctx =
        getContext();

    const msg =
        ctx.chat[messageId];

    if (!msg) {
        return;
    }

    const key =
        getMessageKey(
            msg,
            messageId,
        );

    const anchors =
        getInsertAnchors(
            ctx,
            messageId,
        );

    void publishEvent(
        'MESSAGE_RECEIVED',
        {
            message:
                safeClone(msg),

            messageId,

            messageKey:
                key,

            insertAt:
                messageId,

            beforeMessageKey:
                anchors.beforeKey,

            afterMessageKey:
                anchors.afterKey,
        },
    );
}

function onMessageEdited(
    messageId,
) {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    const ctx =
        getContext();

    const msg =
        ctx.chat[messageId];

    if (!msg) {
        return;
    }

    void publishEvent(
        'MESSAGE_EDITED',
        {
            messageId,

            messageKey:
                getMessageKey(
                    msg,
                    messageId,
                ),

            mes:
                msg.mes,

            swipes:
                safeClone(
                    msg.swipes,
                ),

            swipe_id:
                msg.swipe_id,

            extra:
                safeClone(
                    msg.extra,
                ),
        },
    );
}

function onMessageDeleted(
    arg1,
    arg2,
) {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    const ctx =
        getContext();

    const deletedIds =
        Array.isArray(arg2)
            ? arg2.filter(
                Number.isInteger,
            )
            : (
                Number.isInteger(
                    arg1,
                )
                    ? [arg1]
                    : []
            );

    const deletedMessageKeys =
        [];

    for (
        const id of deletedIds
    ) {
        const msg =
            ctx.chat[id];

        const key =
            getMessageKey(
                msg,
                id,
            );

        if (key) {
            deletedMessageKeys.push(
                key,
            );
        }
    }

    void publishEvent(
        'MESSAGE_DELETED',
        {
            deletedIds,
            deletedMessageKeys,
            newLength:
                Number.isInteger(
                    arg1,
                )
                    ? arg1
                    : ctx.chat.length,
        },
    );
}

function onMessageSwiped(
    messageId,
) {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    const ctx =
        getContext();

    const msg =
        ctx.chat[messageId];

    if (!msg) {
        return;
    }

    void publishEvent(
        'MESSAGE_SWIPED',
        {
            messageId,

            messageKey:
                getMessageKey(
                    msg,
                    messageId,
                ),

            swipe_id:
                msg.swipe_id,

            swipes:
                safeClone(
                    msg.swipes,
                ),
        },
    );
}

function onChatChanged() {
    if (isReconcilingChat) {
        return;
    }

    const generation =
        ++chatChangeGeneration;

    leaveGroup();

    window.setTimeout(
        () => {
            if (
                generation !==
                chatChangeGeneration
            ) {
                return;
            }

            if (
                !getSettings()
                    .enabled
            ) {
                return;
            }

            void syncJoinCurrentChat();
        },
        CHAT_SWITCH_JOIN_DELAY_MS,
    );
}

// ---------------------------------------------------------------------------
// Generation Hooks
// ---------------------------------------------------------------------------

const GENERATION_ID = () =>
    `${CLIENT_ID}-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;

function createLocalGenerationState(
    id,
) {
    return {
        generationId:
            id,

        ownerId:
            CLIENT_ID,

        ownerDevice:
            DEVICE_ID,

        status:
            'active',

        startedAt:
            Date.now(),

        streamSeq:
            0,

        streamSeqApplied:
            0,

        serverSequence:
            null,
    };
}

function resolvePendingGenerationConflictForLocalGeneration(
    generationId,
    publishResult,
) {
    if (
        !activeGeneration ||
        activeGeneration.generationId !==
            generationId
    ) {
        return;
    }

    if (publishResult?.sequence) {
        activeGeneration.serverSequence =
            publishResult.sequence;
    }

    for (
        const [
            remoteId,
            remoteEvent,
        ] of pendingGenerationConflicts
    ) {
        pendingGenerationConflicts.delete(
            remoteId,
        );

        if (
            remoteEvent.generationId ===
            generationId
        ) {
            continue;
        }

        resolveGenerationConflict(
            remoteEvent,
        );
    }
}

function onGenerationStarted() {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    const id =
        GENERATION_ID();

    const generation =
        createLocalGenerationState(
            id,
        );

    activeGeneration =
        generation;

    isGenerationOwner = true;
    generationRequestTime =
        Date.now();

    const ctx =
        getContext();

    const possibleMessageIndex =
        ctx.chat.length - 1;

    if (
        possibleMessageIndex >= 0 &&
        ctx.chat[
            possibleMessageIndex
        ] &&
        !ctx.chat[
            possibleMessageIndex
        ].is_user
    ) {
        generation.messageIndex =
            possibleMessageIndex;

        generation.messageKey =
            getMessageKey(
                ctx.chat[
                    possibleMessageIndex
                ],
                possibleMessageIndex,
            );
    }

    updateStatusUI();

    void enqueueGenerationPublish(
        id,
        async () => {
            const result =
                await publishEvent(
                    'GENERATION_STARTED',
                    {
                        messageIndex:
                            generation.messageIndex,

                        messageKey:
                            generation.messageKey,

                        message:
                            generation.messageIndex !==
                            undefined
                                ? safeClone(
                                    ctx.chat[
                                        generation
                                            .messageIndex
                                    ],
                                )
                                : null,
                    },
                    {
                        generationId:
                            id,
                    },
                );

            if (
                activeGeneration?.generationId ===
                id
            ) {
                activeGeneration.serverSequence =
                    result?.sequence ??
                    null;

                resolvePendingGenerationConflictForLocalGeneration(
                    id,
                    result,
                );
            }
        },
    );
}

async function finalizeLocalGeneration(
    id,
    finalType,
) {
    if (
        finishedGenerationIds.has(id)
    ) {
        return;
    }

    const generation =
        activeGeneration;

    if (
        !generation ||
        generation.generationId !== id
    ) {
        return;
    }

    generation.status =
        finalType ===
            'GENERATION_COMPLETED'
            ? 'completing'
            : 'stopping';

    updateStatusUI();

    await (
        generationPublishChains.get(
            id,
        ) ||
        Promise.resolve()
    ).catch(() => {});

    if (
        !activeGeneration ||
        activeGeneration.generationId !==
            id
    ) {
        return;
    }

    const result =
        await publishEvent(
            finalType,
            {},
            {
                generationId:
                    id,
            },
        );

    if (!result) {
        warn(
            'generation lifecycle event could not be published',
            finalType,
            id,
        );
    }

    finishedGenerationIds.add(
        id,
    );

    clearStreamRenderTimer(
        id,
    );

    flushStreamRender(
        id,
        generation.messageKey,
    );

    scheduleChatSave();

    activeGeneration = null;
    isGenerationOwner = false;

    activatePendingRemoteGenerationAfterLocalStop(
        id,
    );

    updateStatusUI();
}

function onGenerationStopped() {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    if (!activeGeneration) {
        return;
    }

    const id =
        activeGeneration.generationId;

    if (
        finishedGenerationIds.has(id)
    ) {
        activeGeneration = null;
        isGenerationOwner = false;

        activatePendingRemoteGenerationAfterLocalStop(
            id,
        );

        updateStatusUI();

        return;
    }

    void finalizeLocalGeneration(
        id,
        'GENERATION_STOPPED',
    );
}

function onGenerationEnded() {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    if (!activeGeneration) {
        return;
    }

    const id =
        activeGeneration.generationId;

    if (
        finishedGenerationIds.has(id)
    ) {
        activeGeneration = null;
        isGenerationOwner = false;

        activatePendingRemoteGenerationAfterLocalStop(
            id,
        );

        updateStatusUI();

        return;
    }

    void finalizeLocalGeneration(
        id,
        'GENERATION_COMPLETED',
    );
}

function onStreamTokenReceived(
    token,
) {
    if (
        isApplyingRemote ||
        isReconcilingChat
    ) {
        return;
    }

    if (
        !activeGeneration ||
        !isGenerationOwner ||
        activeGeneration.status !==
            'active'
    ) {
        return;
    }

    const generationId =
        activeGeneration.generationId;

    const ctx =
        getContext();

    let messageIndex =
        findGenerationMessageIndex(
            activeGeneration,
            {},
        );

    let message =
        messageIndex >= 0
            ? ctx.chat[messageIndex]
            : null;

    const streamSeq =
        Number(
            activeGeneration.streamSeq ||
                0,
        ) + 1;

    activeGeneration.streamSeq =
        streamSeq;

    activeGeneration.streamSeqApplied =
        streamSeq;

    if (
        messageIndex >= 0 &&
        message
    ) {
        activeGeneration.messageIndex =
            messageIndex;

        activeGeneration.messageKey =
            activeGeneration.messageKey ||
            getMessageKey(
                message,
                messageIndex,
            );
    }

    const payload = {
        chunk:
            String(token ?? ''),

        messageId:
            messageIndex >= 0
                ? messageIndex
                : null,

        messageKey:
            activeGeneration.messageKey ||
            null,

        message:
            messageIndex >= 0 &&
            message
                ? safeClone(
                    message,
                )
                : null,

        insertAt:
            messageIndex >= 0
                ? messageIndex
                : null,
    };

    void enqueueGenerationPublish(
        generationId,
        () =>
            publishEvent(
                'GENERATION_STREAM',
                payload,
                {
                    generationId,
                    streamSeq,
                },
            ),
    );
}

// ---------------------------------------------------------------------------
// Event Source Wiring
// ---------------------------------------------------------------------------

function wireEvents() {
    if (
        event_types.MESSAGE_SENT
    ) {
        eventSource.on(
            event_types.MESSAGE_SENT,
            onMessageSent,
        );
    }

    if (
        event_types.MESSAGE_RECEIVED
    ) {
        eventSource.on(
            event_types.MESSAGE_RECEIVED,
            onMessageReceived,
        );
    }

    if (
        event_types.MESSAGE_EDITED
    ) {
        eventSource.on(
            event_types.MESSAGE_EDITED,
            onMessageEdited,
        );
    }

    if (
        event_types.MESSAGE_DELETED
    ) {
        eventSource.on(
            event_types.MESSAGE_DELETED,
            onMessageDeleted,
        );
    }

    if (
        event_types.MESSAGE_SWIPED
    ) {
        eventSource.on(
            event_types.MESSAGE_SWIPED,
            onMessageSwiped,
        );
    }

    if (
        event_types.CHAT_CHANGED
    ) {
        eventSource.on(
            event_types.CHAT_CHANGED,
            onChatChanged,
        );
    }

    if (
        event_types.GENERATION_STARTED
    ) {
        eventSource.on(
            event_types.GENERATION_STARTED,
            onGenerationStarted,
        );
    }

    if (
        event_types.GENERATION_STOPPED
    ) {
        eventSource.on(
            event_types.GENERATION_STOPPED,
            onGenerationStopped,
        );
    }

    if (
        event_types.GENERATION_ENDED
    ) {
        eventSource.on(
            event_types.GENERATION_ENDED,
            onGenerationEnded,
        );
    }

    if (
        event_types.STREAM_TOKEN_RECEIVED
    ) {
        eventSource.on(
            event_types.STREAM_TOKEN_RECEIVED,
            onStreamTokenReceived,
        );
    }
}

// ---------------------------------------------------------------------------
// UI
// ---------------------------------------------------------------------------

function createStatusUI() {
    const container =
        document.getElementById(
            'top-bar',
        ) ||
        document.getElementById(
            'top-settings-holder',
        ) ||
        document.body;

    if (!container) {
        return;
    }

    const existing =
        document.getElementById(
            'mcs-status',
        );

    if (existing) {
        existing.remove();
    }

    const el =
        document.createElement(
            'div',
        );

    el.id =
        'mcs-status';

    el.className =
        'mcs-status mcs-disconnected';

    el.title =
        'Multi-Client Sync';

    el.tabIndex = 0;

    el.setAttribute(
        'role',
        'button',
    );

    el.setAttribute(
        'aria-label',
        'Multi-Client Sync status',
    );

    el.textContent = '●';

    const stopRemote =
        () => {
            if (
                !activeGeneration ||
                isGenerationOwner
            ) {
                return;
            }

            void requestRemoteStopForGeneration(
                activeGeneration.generationId,
            );
        };

    el.addEventListener(
        'click',
        stopRemote,
    );

    el.addEventListener(
        'keydown',
        (event) => {
            if (
                event.key === 'Enter' ||
                event.key === ' '
            ) {
                event.preventDefault();
                stopRemote();
            }
        },
    );

    container.appendChild(el);

    updateStatusUI();
}

function updateStatusUI() {
    const el =
        document.getElementById(
            'mcs-status',
        );

    if (!el) {
        return;
    }

    const settings =
        getSettings();

    if (
        !settings.showStatusIndicator
    ) {
        el.style.display =
            'none';

        return;
    }

    el.style.display = '';
    el.style.cursor =
        'default';

    let statusClass =
        'mcs-disconnected';

    const text =
        '●';

    let title =
        'Sync: disconnected';

    if (!settings.enabled) {
        statusClass =
            'mcs-disabled';

        title =
            'Sync: disabled';
    } else if (isConnected) {
        if (activeGeneration) {
            if (isGenerationOwner) {
                statusClass =
                    'mcs-owner';

                title =
                    'Sync: generating (owner)';
            } else if (
                activeGeneration.status ===
                'orphaned'
            ) {
                statusClass =
                    'mcs-streaming';

                title =
                    'Sync: generation owner released; click to request stop/cleanup';
            } else {
                statusClass =
                    'mcs-streaming';

                title =
                    'Sync: streaming (remote) — click to stop remote generation';

                el.style.cursor =
                    'pointer';
            }
        } else {
            statusClass =
                'mcs-connected';

            title =
                'Sync: connected';
        }
    }

    el.className =
        `mcs-status ${statusClass}`;

    el.textContent =
        text;

    el.title =
        title;

    el.setAttribute(
        'aria-label',
        title,
    );
}

function createSettingsUI() {
    const settings =
        getSettings();

    const container =
        document.getElementById(
            'extensions_settings',
        );

    if (!container) {
        return;
    }

    const existing =
        container.querySelector(
            `#${EXTENSION_NAME}-settings`,
        );

    if (existing) {
        existing.remove();
    }

    const wrapper =
        document.createElement(
            'div',
        );

    wrapper.id =
        `${EXTENSION_NAME}-settings`;

    wrapper.innerHTML = `
    <div class="mcs-settings">
        <h3>${t('Multi-Client Sync')}</h3>

        <label class="checkbox_label">
            <input
                type="checkbox"
                id="mcs-enabled"
                ${settings.enabled ? 'checked' : ''}
            >
            <span>
                ${t('Enable synchronization')}
            </span>
        </label>

        <label class="checkbox_label">
            <input
                type="checkbox"
                id="mcs-debug"
                ${settings.debugLogging ? 'checked' : ''}
            >
            <span>
                ${t('Debug logging')}
            </span>
        </label>

        <label class="checkbox_label">
            <input
                type="checkbox"
                id="mcs-indicator"
                ${settings.showStatusIndicator ? 'checked' : ''}
            >
            <span>
                ${t('Show status indicator')}
            </span>
        </label>

        <div class="mcs-info">
            <small>
                Client:
                <code>
                    ${escapeHtml(
                        CLIENT_ID.slice(
                            0,
                            12,
                        ),
                    )}…
                </code>

                |
                Device:
                <code>
                    ${escapeHtml(
                        DEVICE_ID,
                    )}
                </code>
            </small>
        </div>
    </div>`;

    container.appendChild(
        wrapper,
    );

    wrapper
        .querySelector(
            '#mcs-enabled',
        )
        ?.addEventListener(
            'change',
            (event) => {
                settings.enabled =
                    event.target.checked;

                if (settings.enabled) {
                    ++connectionGeneration;

                    void syncJoinCurrentChat(
                        {
                            force: true,
                        },
                    );
                } else {
                    leaveGroup();
                }

                updateStatusUI();
            },
        );

    wrapper
        .querySelector(
            '#mcs-debug',
        )
        ?.addEventListener(
            'change',
            (event) => {
                settings.debugLogging =
                    event.target.checked;
            },
        );

    wrapper
        .querySelector(
            '#mcs-indicator',
        )
        ?.addEventListener(
            'change',
            (event) => {
                settings.showStatusIndicator =
                    event.target.checked;

                updateStatusUI();
            },
        );
}

// ---------------------------------------------------------------------------
// Init / lifecycle
// ---------------------------------------------------------------------------

jQuery(() => {
    initBroadcastChannel();
    wireEvents();
    createStatusUI();
    createSettingsUI();

    window.setTimeout(
        () => {
            if (
                getSettings().enabled
            ) {
                void syncJoinCurrentChat(
                    {
                        force: true,
                    },
                );
            }
        },
        INITIAL_JOIN_DELAY_MS,
    );

    window.addEventListener(
        'beforeunload',
        () => {
            /*
             * Best-effort owner release +
             * membership cleanup.
             *
             * The server heartbeat still needs
             * to be the hard fallback for crashes
             * and suspended clients.
             */
            leaveGroup();
        },
    );

    document.addEventListener(
        'visibilitychange',
        () => {
            if (
                document.visibilityState !==
                'visible'
            ) {
                return;
            }

            if (
                !getSettings().enabled
            ) {
                return;
            }

            const desiredChatKey =
                getCurrentDesiredChatKey();

            if (!desiredChatKey) {
                return;
            }

            if (
                !isCurrentChatKey(
                    desiredChatKey,
                ) ||
                !isConnected
            ) {
                ++connectionGeneration;

                void syncJoinCurrentChat(
                    {
                        force: true,
                        expectedChatKey:
                            desiredChatKey,
                    },
                );
            }
        },
    );
});