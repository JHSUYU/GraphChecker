package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Trace-local causal context for runtime region discovery.
 *
 * <p>Soot-inserted call hooks capture parent context at thread/task
 * submission.</p>
 */
final class RuntimeTraceContext {
    private static final Object LOCK = new Object();
    private static final AtomicLong IDS = new AtomicLong(1L);
    private static final IdentityHashMap<Object, SourceRef> SOURCE_ALIASES =
            new IdentityHashMap<>();
    private static final Map<String, SourceRef> SOURCES_BY_KEY =
            new LinkedHashMap<>();
    private static final IdentityHashMap<Object, Seed> ASYNC_SEEDS =
            new IdentityHashMap<>();
    private static final Map<String, Seed> RPC_SENDS =
            new LinkedHashMap<>();
    private static final Map<String, Long> REQUEST_OCCURRENCES =
            new LinkedHashMap<>();
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

    static long beginRequest(Object sourceAlias, String apiName) {
        SourceRef source = sourceFor(sourceAlias);
        if (source == null) {
            throw new IllegalArgumentException(
                    "request source alias is not registered");
        }
        return beginRequest(source, apiName);
    }

    static long beginRequest(SourceRef requestedSource, String apiName) {
        if (requestedSource == null) {
            throw new IllegalArgumentException("request source is required");
        }
        SourceRef source;
        synchronized (LOCK) {
            source = canonicalSourceLocked(requestedSource);
        }
        State state = CURRENT.get();
        long requestId = nextId();
        String normalizedApi = MapFields.safe(apiName).trim();
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
        state.requests.push(new RequestFrame(requestId,
                state.source, activeFrame,
                activeFrame == null ? null : activeFrame.source,
                state.requestId, state.requestKey, state.requestApi));
        state.source = source;
        state.requestId = requestId;
        state.requestKey = requestKey;
        state.requestApi = normalizedApi;
        if (activeFrame != null) {
            activeFrame.source = source;
        }
        publishCausalSource(state);
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
        state.requests.pop();
        state.source = request.previousSource;
        state.requestId = request.previousRequestId;
        state.requestKey = request.previousRequestKey;
        state.requestApi = request.previousRequestApi;
        if (request.activeFrame != null
                && state.frames.peek() == request.activeFrame) {
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
        return next;
    }

    /** Captures the current source/span for a Thread, Runnable, or Callable. */
    static void captureAsync(Object carrier) {
        if (carrier == null) return;
        State state = CURRENT.get();
        View view = state.view();
        synchronized (LOCK) {
            ASYNC_SEEDS.put(carrier, new Seed(view.spanId,
                    view.source, view.requestId, view.requestKey,
                    view.requestApi));
        }
    }

    /** Starts one root activation; nested methods reuse its span. */
    static View enterRoot(Object receiver) {
        State state = CURRENT.get();
        Seed seed = takeSeed(Thread.currentThread());
        if (seed == null) seed = takeSeed(receiver);

        // The receiver's own registration first, and only then anything
        // ambient.
        SourceRef source = sourceFor(receiver);
        // Which authority answered: the receiver's own registration, or the
        // context this thread inherited.  Replay can reproduce the first by
        // object identity and the second only by thread context, so the
        // activation has to say which one named it.
        boolean receiverAttributed = source != null;
        if (source == null && seed != null) source = seed.source;
        if (source == null) source = state.pendingRemoteSource;
        if (source == null) source = state.source;
        // A receiver that named no source of its own keeps the ambient stamp,
        // which is the only answer available while the trace is being written.
        long requestId = seed == null ? state.requestId : seed.requestId;
        String requestKey = seed == null ? state.requestKey : seed.requestKey;
        String requestApi = seed == null ? state.requestApi : seed.requestApi;
        long parentSpanId = seed == null ? state.currentSpan() : seed.parentSpanId;
        if (seed != null || state.laneId == 0L) {
            state.laneId = nextId();
        }
        long spanId = nextId();
        // A receive scope belongs to the server lane until the next receive
        // replaces it.
        long remoteParentSpanId = state.pendingRemoteParentSpanId;
        Frame frame = new Frame(spanId, parentSpanId, remoteParentSpanId,
                state.source, source, receiverAttributed,
                state.requestId, state.requestKey, state.requestApi);
        state.source = source;
        state.requestId = requestId;
        state.requestKey = requestKey;
        state.requestApi = requestApi;
        state.frames.push(frame);
        publishCausalSource(state);
        return state.view();
    }

    static void exitRoot(long spanId) {
        State state = CURRENT.get();
        Frame frame = state.frames.peek();
        if (frame == null || frame.spanId != spanId) return;
        state.frames.pop();
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

    /** Registers an RPC endpoint. */
    static View rpc(String direction, String transport, String correlationId,
                    String half, Object localOwner) {
        State state = CURRENT.get();
        SourceRef localSource = sourceFor(localOwner);
        // A short-lived transport object is commonly unregistered.
        if (localSource != null) {
            state.source = localSource;
            Frame frame = state.frames.peek();
            if (frame != null) {
                frame.source = localSource;
            }
        }
        String key = MapFields.safe(transport) + "\n" + MapFields.safe(correlationId) + "\n"
                + MapFields.safe(half);
        if ("SEND".equalsIgnoreCase(MapFields.safe(direction))) {
            View view = state.view();
            synchronized (LOCK) {
                RPC_SENDS.put(key, new Seed(view.spanId,
                        view.source, view.requestId,
                        view.requestKey, view.requestApi));
            }
            // The exact local endpoint is also the source of the active
            // producer occurrence.
            publishCausalSource(state);
            return view;
        }
        if ("RECEIVE".equalsIgnoreCase(MapFields.safe(direction))) {
            state.pendingRemoteSource = localSource;
            Seed remote = null;
            synchronized (LOCK) {
                remote = RPC_SENDS.remove(key);
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
        publishCausalSource(state);
        return state.view();
    }

    /**
     * Hands the thread's freshly established source to the occurrence running
     * on it.
     */
    private static void publishCausalSource(State state) {
        View view = state.view();
        ConcolicRegionRuntime.observeCausalSource(
                view.source == null ? "" : view.source.key());
    }

    static void resetForTests() {
        synchronized (LOCK) {
            SOURCE_ALIASES.clear();
            SOURCES_BY_KEY.clear();
            ASYNC_SEEDS.clear();
            RPC_SENDS.clear();
            REQUEST_OCCURRENCES.clear();
        }
        CURRENT.remove();
        IDS.set(1L);
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
    }

    /**
     * Whether this run registered the same logical source as {@code
     * sourceKey}.
     */
    static boolean sourceIdentityRegistered(String sourceKey) {
        if (sourceKey == null || sourceKey.isEmpty()) return false;
        synchronized (LOCK) {
            for (String registered : SOURCES_BY_KEY.keySet()) {
                if (sameSourceIdentity(sourceKey, registered)) return true;
            }
            return false;
        }
    }

    /** Same logical source across independently minted replay epochs. */
    static boolean sameSourceIdentity(String left, String right) {
        String leftIdentity = sourceIdentity(left);
        return !leftIdentity.isEmpty()
                && leftIdentity.equals(sourceIdentity(right));
    }

    private static String sourceIdentity(String sourceKey) {
        String value = sourceKey == null ? "" : sourceKey.trim();
        int marker = value.lastIndexOf("#epoch");
        if (marker <= 0 || marker + 6 >= value.length()) return value;
        for (int i = marker + 6; i < value.length(); i++) {
            if (!Character.isDigit(value.charAt(i))) return value;
        }
        return value.substring(0, marker);
    }

    private static void requireUnchangedAliasLocked(Object alias,
                                                    SourceRef source) {
        SourceRef existing = SOURCE_ALIASES.get(alias);
        if (existing != null && !existing.equals(source)) {
            throw new IllegalArgumentException(
                    "source alias is already bound to " + existing.key());
        }
    }

    private static State initialState() {
        return new State(nextId());
    }

    private static State inheritedState(State parent) {
        State child = initialState();
        if (parent == null) return child;
        View inherited = parent.view();
        child.source = inherited.source;
        child.requestId = inherited.requestId;
        child.requestKey = inherited.requestKey;
        child.requestApi = inherited.requestApi;
        return child;
    }

    private static long nextId() {
        return IDS.getAndIncrement();
    }


    static final class View {
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;
        final SourceRef source;
        /** Whether {@link #source} is the root receiver's own registration
         *  rather than the context this thread inherited. */
        final boolean receiverAttributed;
        final long requestId;
        final String requestKey;
        final String requestApi;

        private View(long laneId, long spanId,
                     long parentSpanId, long remoteParentSpanId,
                     SourceRef source, boolean receiverAttributed,
                     long requestId,
                     String requestKey, String requestApi) {
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.receiverAttributed = receiverAttributed;
            this.requestId = requestId;
            this.requestKey = MapFields.safe(requestKey);
            this.requestApi = MapFields.safe(requestApi);
        }
    }

    private static final class State {
        private long laneId;
        private SourceRef source;
        private SourceRef pendingRemoteSource;
        private long pendingRemoteParentSpanId;
        private long requestId;
        private String requestKey = "";
        private String requestApi = "";
        private final Deque<Frame> frames = new ArrayDeque<>();
        private final Deque<RequestFrame> requests = new ArrayDeque<>();

        private State(long laneId) {
            this.laneId = laneId;
        }

        private long currentSpan() {
            Frame frame = frames.peek();
            return frame == null ? 0L : frame.spanId;
        }

        private View view() {
            Frame frame = frames.peek();
            return new View(
                    laneId, frame == null ? 0L : frame.spanId,
                    frame == null ? 0L : frame.parentSpanId,
                    frame == null ? pendingRemoteParentSpanId
                            : frame.remoteParentSpanId,
                    frame == null ? source : frame.source,
                    frame != null && frame.receiverAttributed,
                    requestId, requestKey, requestApi);
        }
    }

    private static final class Frame {
        private final long spanId;
        private final long parentSpanId;
        private long remoteParentSpanId;
        private final SourceRef previousSource;
        private SourceRef source;
        private final boolean receiverAttributed;
        private final long previousRequestId;
        private final String previousRequestKey;
        private final String previousRequestApi;

        private Frame(long spanId, long parentSpanId,
                      long remoteParentSpanId, SourceRef previousSource,
                      SourceRef source, boolean receiverAttributed,
                      long previousRequestId,
                      String previousRequestKey, String previousRequestApi) {
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.previousSource = previousSource;
            this.source = source;
            this.receiverAttributed = receiverAttributed;
            this.previousRequestId = previousRequestId;
            this.previousRequestKey = MapFields.safe(previousRequestKey);
            this.previousRequestApi = MapFields.safe(previousRequestApi);
        }
    }

    private static final class Seed {
        private final long parentSpanId;
        private final SourceRef source;
        private final long requestId;
        private final String requestKey;
        private final String requestApi;

        private Seed(long parentSpanId, SourceRef source,
                     long requestId, String requestKey, String requestApi) {
            this.parentSpanId = parentSpanId;
            this.source = source;
            this.requestId = requestId;
            this.requestKey = MapFields.safe(requestKey);
            this.requestApi = MapFields.safe(requestApi);
        }
    }

    private static final class RequestFrame {
        private final long requestId;
        private final SourceRef previousSource;
        private final Frame activeFrame;
        private final SourceRef previousFrameSource;
        private final long previousRequestId;
        private final String previousRequestKey;
        private final String previousRequestApi;

        private RequestFrame(long requestId,
                             SourceRef previousSource, Frame activeFrame,
                             SourceRef previousFrameSource,
                             long previousRequestId,
                             String previousRequestKey,
                             String previousRequestApi) {
            this.requestId = requestId;
            this.previousSource = previousSource;
            this.activeFrame = activeFrame;
            this.previousFrameSource = previousFrameSource;
            this.previousRequestId = previousRequestId;
            this.previousRequestKey = MapFields.safe(previousRequestKey);
            this.previousRequestApi = MapFields.safe(previousRequestApi);
        }
    }

}
