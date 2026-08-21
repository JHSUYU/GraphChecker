package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Trace-local causal context for runtime region discovery.
 *
 * <p>Numeric identifiers produced here are evidence inside one concrete
 * trace; they are deliberately not replay identities.  A {@link SourceRef}
 * is the explicit stable exception: it names a logical node/application and
 * lifecycle epoch.  Node/service-local state is partitioned by that source
 * alone; a lane preserves same-thread program order, and a span identifies
 * one root activation.  Soot-inserted call hooks capture parent context at
 * thread/task submission.  RPC hooks add a remote parent without changing the
 * application payload.</p>
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
        synchronized (LOCK) {
            source = canonicalSourceLocked(requestedSource);
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
        recordSourceEvent(SourceEventKind.REQUEST_BEGIN, source, null,
                requestId, state.view());
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
        recordSourceEvent(SourceEventKind.REQUEST_END, request.source, null,
                requestId, state.view());
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
        recordSourceEvent(SourceEventKind.RESTART, previous, next, 0L,
                CURRENT.get().view());
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
        // ambient.  A node binds its receivers to itself at start-up
        // (registerSource/registerSourceAlias), so this is the application
        // stating which logical source the activation belongs to.  The async
        // seed below it is the source of whoever *submitted* the thread, and
        // an in-process cluster submits every node's threads from the driver
        // - so preferring the seed attributed every DataNode activation to
        // the driver, which is what made a producer and its target land on
        // different owners and epochs and left the delivery of one exchange
        // recorded by two occurrences of one source.  Nothing here searches:
        // an alias is an identity binding the application made, and a
        // receiver bound to two sources is already refused at registration
        // by requireUnchangedAliasLocked rather than resolved by choosing.
        SourceRef source = sourceFor(receiver);
        boolean receiverAttributed = source != null;
        if (source == null && seed != null) source = seed.source;
        if (source == null) source = state.pendingRemoteSource;
        if (source == null) source = state.source;
        // A receiver that named no source of its own keeps the ambient
        // stamp, which is the only answer available while the trace is being
        // written.  Whether that stamp survives is decided after the trace is
        // read: the receiver's own registration, wherever in the run it
        // arrives, carries the recorded object identity and re-attributes
        // these frames to it.
        long requestId = seed == null ? state.requestId : seed.requestId;
        String requestKey = seed == null ? state.requestKey : seed.requestKey;
        String requestApi = seed == null ? state.requestApi : seed.requestApi;
        long parentSpanId = seed == null ? state.currentSpan() : seed.parentSpanId;
        if (seed != null || state.laneId == 0L) {
            state.laneId = nextId();
        }
        long spanId = nextId();
        // A receive scope belongs to the server lane until the next receive
        // replaces it.  Do not let an adapter/parser root consume it before
        // the actual handler root starts.
        long remoteParentSpanId = state.pendingRemoteParentSpanId;
        Frame frame = new Frame(spanId, parentSpanId, remoteParentSpanId,
                state.source, source,
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

    /**
     * Registers an RPC endpoint.  SEND stores the caller span; RECEIVE binds
     * the matching caller as remote parent and may establish the local source.
     *
     * <p>The application supplies an exchange id and half, so one key names
     * one transport leg.  The seed is consequently an exact one-shot mapping,
     * not a FIFO guessed from payload equality or arrival order.</p>
     */
    static View rpc(String direction, String transport, String correlationId,
                    String half, Object localOwner) {
        State state = CURRENT.get();
        SourceRef localSource = sourceFor(localOwner);
        // A short-lived transport object is commonly unregistered.  It says
        // nothing about ownership and must not erase the source already
        // established by the enclosing request/receiver.  Only an explicit
        // application registration is authority to replace that context.
        if (localSource != null) {
            state.source = localSource;
            Frame frame = state.frames.peek();
            if (frame != null) {
                frame.source = localSource;
            }
        }
        String key = safe(transport) + "\n" + safe(correlationId) + "\n"
                + safe(half);
        if ("SEND".equalsIgnoreCase(safe(direction))) {
            View view = state.view();
            synchronized (LOCK) {
                RPC_SENDS.put(key, new Seed(view.spanId,
                        view.source, view.requestId,
                        view.requestKey, view.requestApi));
            }
            // The exact local endpoint is also the source of the active
            // producer occurrence.  RECEIVE publishes this below, but SEND
            // used to return first: a root whose receiver is a short-lived
            // transport object could then export every demanded value and
            // still be rejected as source-unattributed.  Publish the source
            // resolved from the real local owner before returning; this is
            // attribution only and does not pair or move an expression.
            publishCausalSource(state);
            return view;
        }
        if ("RECEIVE".equalsIgnoreCase(safe(direction))) {
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
     *
     * <p>The source is the stable half of a replay address, and an
     * application establishes it inside its own entry method - a thread-entry
     * root is entered before its source exists.  A replay therefore cannot
     * read it at the region entry hook and has to be told when it appears.
     * A service that never opens a scope on these threads is attributed from
     * its receiver's registration instead.</p>
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
    }

    /**
     * Whether this run registered the same logical source as {@code sourceKey}.
     *
     * <p>The epoch is a lifecycle number minted independently by each fresh
     * replay.  It remains useful within one trace, but comparing its numeric
     * value with the seed would reject the same NameNode/DataNode role merely
     * because startup order changed.</p>
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

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    static final class View {
        final long laneId;
        final long spanId;
        final long parentSpanId;
        final long remoteParentSpanId;
        final SourceRef source;
        final long requestId;
        final String requestKey;
        final String requestApi;

        private View(long laneId, long spanId,
                     long parentSpanId, long remoteParentSpanId,
                     SourceRef source, long requestId,
                     String requestKey, String requestApi) {
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
                    requestId, requestKey, requestApi);
        }
    }

    private static final class Frame {
        private final long spanId;
        private final long parentSpanId;
        private long remoteParentSpanId;
        private final SourceRef previousSource;
        private SourceRef source;
        private final long previousRequestId;
        private final String previousRequestKey;
        private final String previousRequestApi;

        private Frame(long spanId, long parentSpanId,
                      long remoteParentSpanId, SourceRef previousSource,
                      SourceRef source, long previousRequestId,
                      String previousRequestKey, String previousRequestApi) {
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.previousSource = previousSource;
            this.source = source;
            this.previousRequestId = previousRequestId;
            this.previousRequestKey = safe(previousRequestKey);
            this.previousRequestApi = safe(previousRequestApi);
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
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
        }
    }

    private static final class RequestFrame {
        private final long requestId;
        private final SourceRef source;
        private final SourceRef previousSource;
        private final Frame activeFrame;
        private final SourceRef previousFrameSource;
        private final long previousRequestId;
        private final String previousRequestKey;
        private final String previousRequestApi;

        private RequestFrame(long requestId, SourceRef source,
                             SourceRef previousSource, Frame activeFrame,
                             SourceRef previousFrameSource,
                             long previousRequestId,
                             String previousRequestKey,
                             String previousRequestApi) {
            this.requestId = requestId;
            this.source = source;
            this.previousSource = previousSource;
            this.activeFrame = activeFrame;
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
