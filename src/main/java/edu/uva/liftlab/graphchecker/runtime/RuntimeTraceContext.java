package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Trace-local causal context for runtime region discovery.
 *
 * <p>Numeric identifiers produced here are evidence inside one concrete
 * trace; they are deliberately not replay identities.  A {@link SourceRef}
 * is the explicit stable exception: it names a logical node/application and
 * lifecycle epoch.  A local owner partitions node/service-local state, a lane
 * preserves same-thread program order, and a span identifies one root
 * activation.  Soot-inserted call hooks capture parent context at thread/task
 * submission.  RPC hooks add a remote parent without changing the application
 * payload.</p>
 */
final class RuntimeTraceContext {
    private static final Object LOCK = new Object();
    private static final AtomicLong IDS = new AtomicLong(1L);
    private static final IdentityHashMap<Object, Long> OWNERS =
            new IdentityHashMap<>();
    private static final IdentityHashMap<Object, SourceRef> SOURCE_ALIASES =
            new IdentityHashMap<>();
    private static final Map<String, SourceRef> SOURCES_BY_KEY =
            new LinkedHashMap<>();
    private static final Map<String, Long> SOURCE_OWNER_IDS =
            new LinkedHashMap<>();
    private static final IdentityHashMap<Object, Seed> ASYNC_SEEDS =
            new IdentityHashMap<>();
    private static final Map<String, Deque<Seed>> RPC_SENDS =
            new LinkedHashMap<>();
    private static final Map<String, Long> REQUEST_OCCURRENCES =
            new LinkedHashMap<>();
    private static final List<SourceEvent> SOURCE_EVENTS = new ArrayList<>();
    private static final InheritableThreadLocal<State> CURRENT =
            new InheritableThreadLocal<State>() {
                @Override
                protected State initialValue() {
                    return initialState();
                }

                @Override
                protected State childValue(State parent) {
                    return inheritedState(parent);
                }
            };

    private RuntimeTraceContext() {
    }

    static long registerOwner(Object owner, String label) {
        if (owner == null) return 0L;
        synchronized (LOCK) {
            Long existing = OWNERS.get(owner);
            if (existing != null) return existing;
            long id = nextId();
            OWNERS.put(owner, id);
            return id;
        }
    }

    /** Binds a stable node/application source to a runtime anchor object. */
    static SourceRef registerSource(Object anchor, SourceRef source) {
        if (anchor == null || source == null) {
            throw new IllegalArgumentException(
                    "source registration requires anchor and source");
        }
        synchronized (LOCK) {
            SourceRef canonical = canonicalSourceLocked(source);
            requireUnchangedAliasLocked(anchor, canonical);
            bindSourceLocked(anchor, canonical);
            return canonical;
        }
    }

    /** Binds another runtime object to the source already named by anchor. */
    static SourceRef registerSourceAlias(Object alias, Object anchor) {
        if (alias == null || anchor == null) {
            throw new IllegalArgumentException(
                    "source alias registration requires alias and anchor");
        }
        synchronized (LOCK) {
            SourceRef source = SOURCE_ALIASES.get(anchor);
            if (source == null) {
                throw new IllegalArgumentException(
                        "source anchor is not registered");
            }
            requireUnchangedAliasLocked(alias, source);
            bindSourceLocked(alias, source);
            return source;
        }
    }

    static SourceRef sourceFor(Object alias) {
        if (alias == null) return null;
        synchronized (LOCK) {
            return SOURCE_ALIASES.get(alias);
        }
    }

    /** Enters an external request scope using a registered source alias. */
    static long beginRequest(Object sourceAlias) {
        return beginRequest(sourceAlias, "request");
    }

    static long beginRequest(Object sourceAlias, String apiName) {
        SourceRef source = sourceFor(sourceAlias);
        if (source == null) {
            throw new IllegalArgumentException(
                    "request source alias is not registered");
        }
        return beginRequest(source, apiName);
    }

    /** Enters an external request scope using an explicit stable source. */
    static long beginRequest(SourceRef requestedSource) {
        return beginRequest(requestedSource, "request");
    }

    static long beginRequest(SourceRef requestedSource, String apiName) {
        if (requestedSource == null) {
            throw new IllegalArgumentException("request source is required");
        }
        SourceRef source;
        long ownerId;
        synchronized (LOCK) {
            source = canonicalSourceLocked(requestedSource);
            ownerId = sourceOwnerIdLocked(source);
        }
        State state = CURRENT.get();
        long requestId = nextId();
        String normalizedApi = safe(apiName).trim();
        if (normalizedApi.isEmpty()) normalizedApi = "request";
        long requestOccurrence;
        synchronized (LOCK) {
            String requestFamily = source.key() + "\n" + normalizedApi;
            Long prior = REQUEST_OCCURRENCES.get(requestFamily);
            requestOccurrence = prior == null ? 1L : prior + 1L;
            REQUEST_OCCURRENCES.put(requestFamily, requestOccurrence);
        }
        String requestKey = source.key() + "/request/" + normalizedApi
                + "#" + requestOccurrence;
        Frame activeFrame = state.frames.peek();
        state.requests.push(new RequestFrame(requestId, source,
                state.ownerId, state.source, activeFrame,
                activeFrame == null ? 0L : activeFrame.ownerId,
                activeFrame == null ? null : activeFrame.source,
                state.requestId, state.requestKey, state.requestApi));
        state.ownerId = ownerId;
        state.source = source;
        state.requestId = requestId;
        state.requestKey = requestKey;
        state.requestApi = normalizedApi;
        if (activeFrame != null) {
            activeFrame.ownerId = ownerId;
            activeFrame.source = source;
        }
        recordSourceEvent(SourceEventKind.REQUEST_BEGIN, source, null,
                requestId, state.view());
        return requestId;
    }

    /** Exits the matching request scope and restores the caller source. */
    static void endRequest(long requestId) {
        State state = CURRENT.get();
        RequestFrame request = state.requests.peek();
        if (request == null || request.requestId != requestId) {
            throw new IllegalStateException(
                    "request scopes must end in LIFO order");
        }
        recordSourceEvent(SourceEventKind.REQUEST_END, request.source, null,
                requestId, state.view());
        state.requests.pop();
        state.ownerId = request.previousOwnerId;
        state.source = request.previousSource;
        state.requestId = request.previousRequestId;
        state.requestKey = request.previousRequestKey;
        state.requestApi = request.previousRequestApi;
        if (request.activeFrame != null
                && state.frames.peek() == request.activeFrame) {
            request.activeFrame.ownerId = request.previousFrameOwnerId;
            request.activeFrame.source = request.previousFrameSource;
        }
    }

    /** Advances one logical source to a new lifecycle epoch. */
    static SourceRef restartSource(Object anchor, SourceRef nextSource) {
        if (anchor == null || nextSource == null) {
            throw new IllegalArgumentException(
                    "source restart requires anchor and next source");
        }
        SourceRef previous;
        SourceRef next;
        synchronized (LOCK) {
            previous = SOURCE_ALIASES.get(anchor);
            if (previous == null) {
                throw new IllegalArgumentException(
                        "source anchor is not registered");
            }
            if (!previous.kind().equals(nextSource.kind())
                    || !previous.role().equals(nextSource.role())
                    || !previous.id().equals(nextSource.id())
                    || nextSource.epoch() <= previous.epoch()) {
                throw new IllegalArgumentException(
                        "restart must advance the same logical source");
            }
            next = canonicalSourceLocked(nextSource);
            bindSourceLocked(anchor, next);
        }
        recordSourceEvent(SourceEventKind.RESTART, previous, next, 0L,
                CURRENT.get().view());
        return next;
    }

    /** Captures the current owner/span for a Thread, Runnable, or Callable. */
    static void captureAsync(Object carrier) {
        if (carrier == null) return;
        State state = CURRENT.get();
        View view = state.view();
        synchronized (LOCK) {
            ASYNC_SEEDS.put(carrier, new Seed(view.ownerId, view.spanId,
                    view.source, view.requestId, view.requestKey,
                    view.requestApi));
        }
    }

    /** Starts one root activation; nested methods reuse its span. */
    static View enterRoot(Object receiver) {
        State state = CURRENT.get();
        Seed seed = takeSeed(Thread.currentThread());
        if (seed == null) seed = takeSeed(receiver);

        SourceRef source = seed == null ? null : seed.source;
        if (source == null) source = sourceFor(receiver);
        if (source == null) source = state.pendingRemoteSource;
        if (source == null) source = state.source;

        long ownerId = seed == null ? state.ownerId : seed.ownerId;
        long requestId = seed == null ? state.requestId : seed.requestId;
        String requestKey = seed == null ? state.requestKey : seed.requestKey;
        String requestApi = seed == null ? state.requestApi : seed.requestApi;
        if (source != null) {
            synchronized (LOCK) {
                ownerId = sourceOwnerIdLocked(source);
            }
        }
        long parentSpanId = seed == null ? state.currentSpan() : seed.parentSpanId;
        if (source == null && receiver != null && seed == null
                && (ownerId == 0L || ownerId == state.fallbackOwnerId)) {
            ownerId = registerOwner(receiver, receiver.getClass().getName());
        }
        if (ownerId == 0L) {
            ownerId = state.fallbackOwnerId;
        }
        if (seed != null || state.laneId == 0L) {
            state.laneId = nextId();
        }
        long spanId = nextId();
        // A receive scope belongs to the server lane until the next receive
        // replaces it.  Do not let an adapter/parser root consume it before
        // the actual handler root starts.
        long remoteParentSpanId = state.pendingRemoteParentSpanId;
        Frame frame = new Frame(spanId, parentSpanId, remoteParentSpanId,
                state.ownerId, ownerId, state.source, source,
                state.requestId, state.requestKey, state.requestApi);
        state.ownerId = ownerId;
        state.source = source;
        state.requestId = requestId;
        state.requestKey = requestKey;
        state.requestApi = requestApi;
        state.frames.push(frame);
        return state.view();
    }

    static void exitRoot(long spanId) {
        State state = CURRENT.get();
        Frame frame = state.frames.peek();
        if (frame == null || frame.spanId != spanId) return;
        state.frames.pop();
        state.ownerId = frame.previousOwnerId;
        state.source = frame.previousSource;
        state.requestId = frame.previousRequestId;
        state.requestKey = frame.previousRequestKey;
        state.requestApi = frame.previousRequestApi;
    }

    static View current() {
        return CURRENT.get().view();
    }

    static SourceRef currentSource() {
        return CURRENT.get().view().source;
    }

    /**
     * Registers an RPC endpoint.  SEND stores the caller span; RECEIVE binds
     * the matching caller as remote parent and may establish the local owner.
     */
    static View rpc(String direction, String transport, String correlationId,
                    Object localOwner) {
        State state = CURRENT.get();
        SourceRef localSource = sourceFor(localOwner);
        if (localOwner != null) {
            if (localSource == null) {
                state.ownerId = registerOwner(localOwner,
                        localOwner.getClass().getName());
            } else {
                synchronized (LOCK) {
                    state.ownerId = sourceOwnerIdLocked(localSource);
                }
            }
            state.source = localSource;
            Frame frame = state.frames.peek();
            if (frame != null) {
                frame.ownerId = state.ownerId;
                frame.source = localSource;
            }
        }
        String key = safe(transport) + "\n" + safe(correlationId);
        if ("SEND".equalsIgnoreCase(safe(direction))) {
            View view = state.view();
            synchronized (LOCK) {
                RPC_SENDS.computeIfAbsent(key, ignored -> new ArrayDeque<>())
                        .addLast(new Seed(view.ownerId, view.spanId,
                                view.source, view.requestId,
                                view.requestKey, view.requestApi));
            }
            return view;
        }
        if ("RECEIVE".equalsIgnoreCase(safe(direction))) {
            state.pendingRemoteSource = localSource;
            Seed remote = null;
            synchronized (LOCK) {
                Deque<Seed> parents = RPC_SENDS.get(key);
                if (parents != null) {
                    remote = parents.pollFirst();
                    if (parents.isEmpty()) RPC_SENDS.remove(key);
                }
            }
            if (remote != null) {
                state.pendingRemoteParentSpanId = remote.parentSpanId;
                state.requestId = remote.requestId;
                state.requestKey = remote.requestKey;
                state.requestApi = remote.requestApi;
                Frame frame = state.frames.peek();
                if (frame != null) {
                    frame.remoteParentSpanId = remote.parentSpanId;
                }
            }
        }
        return state.view();
    }

    static void resetForTests() {
        synchronized (LOCK) {
            OWNERS.clear();
            SOURCE_ALIASES.clear();
            SOURCES_BY_KEY.clear();
            SOURCE_OWNER_IDS.clear();
            ASYNC_SEEDS.clear();
            RPC_SENDS.clear();
            REQUEST_OCCURRENCES.clear();
            SOURCE_EVENTS.clear();
        }
        CURRENT.remove();
        IDS.set(1L);
    }

    static List<SourceEvent> sourceEventsForTests() {
        synchronized (LOCK) {
            return new ArrayList<>(SOURCE_EVENTS);
        }
    }

    private static Seed takeSeed(Object carrier) {
        if (carrier == null) return null;
        synchronized (LOCK) {
            return ASYNC_SEEDS.remove(carrier);
        }
    }

    private static SourceRef canonicalSourceLocked(SourceRef source) {
        SourceRef existing = SOURCES_BY_KEY.get(source.key());
        if (existing != null && !existing.equals(source)) {
            throw new IllegalArgumentException(
                    "source key has conflicting kind or role: "
                            + source.key());
        }
        if (existing != null) return existing;
        SOURCES_BY_KEY.put(source.key(), source);
        return source;
    }

    private static void bindSourceLocked(Object alias, SourceRef source) {
        SOURCE_ALIASES.put(alias, source);
        OWNERS.put(alias, sourceOwnerIdLocked(source));
    }

    private static void requireUnchangedAliasLocked(Object alias,
                                                    SourceRef source) {
        SourceRef existing = SOURCE_ALIASES.get(alias);
        if (existing != null && !existing.equals(source)) {
            throw new IllegalArgumentException(
                    "source alias is already bound to " + existing.key());
        }
    }

    private static long sourceOwnerIdLocked(SourceRef source) {
        Long existing = SOURCE_OWNER_IDS.get(source.key());
        if (existing != null) return existing;
        long ownerId = nextId();
        SOURCE_OWNER_IDS.put(source.key(), ownerId);
        return ownerId;
    }

    private static void recordSourceEvent(SourceEventKind kind,
                                          SourceRef source,
                                          SourceRef relatedSource,
                                          long requestId,
                                          View view) {
        SourceEvent event = new SourceEvent(nextId(), kind, source,
                relatedSource, requestId, view.laneId, view.spanId);
        synchronized (LOCK) {
            SOURCE_EVENTS.add(event);
        }
    }

    private static State initialState() {
        long laneId = nextId();
        return new State(laneId, nextId());
    }

    private static State inheritedState(State parent) {
        State child = initialState();
        if (parent == null) return child;
        View inherited = parent.view();
        child.ownerId = inherited.ownerId;
        child.source = inherited.source;
        child.requestId = inherited.requestId;
        child.requestKey = inherited.requestKey;
        child.requestApi = inherited.requestApi;
        return child;
    }

    private static long nextId() {
        return IDS.getAndIncrement();
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    static final class View {
        final long ownerId;
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;
        final SourceRef source;
        final long requestId;
        final String requestKey;
        final String requestApi;

        private View(long ownerId, long laneId, long spanId,
                     long parentSpanId, long remoteParentSpanId,
                     SourceRef source, long requestId,
                     String requestKey, String requestApi) {
            this.ownerId = ownerId;
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.requestId = requestId;
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
        }
    }

    private static final class State {
        private long laneId;
        private final long fallbackOwnerId;
        private long ownerId;
        private SourceRef source;
        private SourceRef pendingRemoteSource;
        private long pendingRemoteParentSpanId;
        private long requestId;
        private String requestKey = "";
        private String requestApi = "";
        private final Deque<Frame> frames = new ArrayDeque<>();
        private final Deque<RequestFrame> requests = new ArrayDeque<>();

        private State(long laneId, long fallbackOwnerId) {
            this.laneId = laneId;
            this.fallbackOwnerId = fallbackOwnerId;
            this.ownerId = fallbackOwnerId;
        }

        private long currentSpan() {
            Frame frame = frames.peek();
            return frame == null ? 0L : frame.spanId;
        }

        private View view() {
            Frame frame = frames.peek();
            return new View(frame == null ? ownerId : frame.ownerId,
                    laneId, frame == null ? 0L : frame.spanId,
                    frame == null ? 0L : frame.parentSpanId,
                    frame == null ? pendingRemoteParentSpanId
                            : frame.remoteParentSpanId,
                    frame == null ? source : frame.source,
                    requestId, requestKey, requestApi);
        }
    }

    private static final class Frame {
        private final long spanId;
        private final long parentSpanId;
        private long remoteParentSpanId;
        private final long previousOwnerId;
        private long ownerId;
        private final SourceRef previousSource;
        private SourceRef source;
        private final long previousRequestId;
        private final String previousRequestKey;
        private final String previousRequestApi;

        private Frame(long spanId, long parentSpanId,
                      long remoteParentSpanId, long previousOwnerId,
                      long ownerId, SourceRef previousSource,
                      SourceRef source, long previousRequestId,
                      String previousRequestKey, String previousRequestApi) {
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.previousOwnerId = previousOwnerId;
            this.ownerId = ownerId;
            this.previousSource = previousSource;
            this.source = source;
            this.previousRequestId = previousRequestId;
            this.previousRequestKey = safe(previousRequestKey);
            this.previousRequestApi = safe(previousRequestApi);
        }
    }

    private static final class Seed {
        private final long ownerId;
        private final long parentSpanId;
        private final SourceRef source;
        private final long requestId;
        private final String requestKey;
        private final String requestApi;

        private Seed(long ownerId, long parentSpanId, SourceRef source,
                     long requestId, String requestKey, String requestApi) {
            this.ownerId = ownerId;
            this.parentSpanId = parentSpanId;
            this.source = source;
            this.requestId = requestId;
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
        }
    }

    private static final class RequestFrame {
        private final long requestId;
        private final SourceRef source;
        private final long previousOwnerId;
        private final SourceRef previousSource;
        private final Frame activeFrame;
        private final long previousFrameOwnerId;
        private final SourceRef previousFrameSource;
        private final long previousRequestId;
        private final String previousRequestKey;
        private final String previousRequestApi;

        private RequestFrame(long requestId, SourceRef source,
                             long previousOwnerId,
                             SourceRef previousSource, Frame activeFrame,
                             long previousFrameOwnerId,
                             SourceRef previousFrameSource,
                             long previousRequestId,
                             String previousRequestKey,
                             String previousRequestApi) {
            this.requestId = requestId;
            this.source = source;
            this.previousOwnerId = previousOwnerId;
            this.previousSource = previousSource;
            this.activeFrame = activeFrame;
            this.previousFrameOwnerId = previousFrameOwnerId;
            this.previousFrameSource = previousFrameSource;
            this.previousRequestId = previousRequestId;
            this.previousRequestKey = safe(previousRequestKey);
            this.previousRequestApi = safe(previousRequestApi);
        }
    }

    enum SourceEventKind {
        REQUEST_BEGIN,
        REQUEST_END,
        RESTART
    }

    static final class SourceEvent {
        final long eventId;
        final SourceEventKind kind;
        final SourceRef source;
        final SourceRef relatedSource;
        final long requestId;
        final long laneId;
        final long spanId;

        private SourceEvent(long eventId, SourceEventKind kind,
                            SourceRef source, SourceRef relatedSource,
                            long requestId, long laneId, long spanId) {
            this.eventId = eventId;
            this.kind = kind;
            this.source = source;
            this.relatedSource = relatedSource;
            this.requestId = requestId;
            this.laneId = laneId;
            this.spanId = spanId;
        }
    }
}
