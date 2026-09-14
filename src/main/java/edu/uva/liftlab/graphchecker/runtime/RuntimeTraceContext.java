package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
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
            SourceRef source = resolveNamedAnchorLocked(anchor);
            if (source == null) {
                throw new IllegalArgumentException(
                        "source anchor is not registered: "
                                + describeAnchor(anchor));
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
        SourceRef source;
        synchronized (LOCK) {
            source = resolveNamedAnchorLocked(sourceAlias);
        }
        if (source == null) {
            throw new IllegalArgumentException(
                    "request source alias is not registered: "
                            + describeAnchor(sourceAlias) + " for request "
                            + MapFields.safe(apiName));
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
        state.scopes.push(new ScopeFrame(requestId, state, activeFrame));
        state.source = source;
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
        restoreScope(requestId);
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
            previous = resolveNamedAnchorLocked(anchor);
            if (previous == null) {
                throw new IllegalArgumentException(
                        "source anchor is not registered: "
                                + describeAnchor(anchor));
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
                    view.source, view.requestKey, view.requestApi,
                    view.exchangeTransport, view.exchangeCorrelationId,
                    view.exchangeAttemptId, view.exchangeHalf));
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
        if (source == null) source = state.source;
        // A receiver that named no source of its own keeps the ambient stamp,
        // which is the only answer available while the trace is being written.
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
                state.requestKey, state.requestApi,
                state.exchangeTransport, state.exchangeCorrelationId,
                state.exchangeAttemptId, state.exchangeHalf);
        state.source = source;
        state.requestKey = requestKey;
        state.requestApi = requestApi;
        if (seed != null) {
            state.exchangeTransport = seed.exchangeTransport;
            state.exchangeCorrelationId = seed.exchangeCorrelationId;
            state.exchangeAttemptId = seed.exchangeAttemptId;
            state.exchangeHalf = seed.exchangeHalf;
        }
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
        state.requestKey = frame.previousRequestKey;
        state.requestApi = frame.previousRequestApi;
        state.exchangeTransport = frame.previousExchangeTransport;
        state.exchangeCorrelationId = frame.previousExchangeCorrelationId;
        state.exchangeAttemptId = frame.previousExchangeAttemptId;
        state.exchangeHalf = frame.previousExchangeHalf;
    }

    static View current() {
        return CURRENT.get().view();
    }

    static SourceRef currentSource() {
        return CURRENT.get().view().source;
    }

    /** Encodes the current node and request flow for the next message. */
    static String outboundHeader(Object localOwner) {
        State state = CURRENT.get();
        bindLocalOwner(state, localOwner);
        View view = state.view();
        if (view.source == null || view.requestKey.isEmpty()
                || view.requestApi.isEmpty()) {
            throw new IllegalStateException(
                    "outbound message requires source and request flow");
        }
        SourceRef source = view.source;
        return "1|" + view.spanId + "|" + source.epoch()
                + "|" + encoded(source.kind())
                + "|" + encoded(source.role())
                + "|" + encoded(source.id())
                + "|" + encoded(view.requestKey)
                + "|" + encoded(view.requestApi);
    }

    /** Installs one received message and its exact transport exchange. */
    static long enterInbound(String header, String transport,
                             String correlationId, String attemptId,
                             String half, Object localOwner) {
        MessageContext remote = MessageContext.parse(header);
        State state = CURRENT.get();
        Frame activeFrame = state.frames.peek();
        long token = nextId();
        state.scopes.push(new ScopeFrame(token, state, activeFrame));
        SourceRef localSource = sourceFor(localOwner);
        state.source = localSource != null ? localSource
                : state.source != null ? state.source : remote.source;
        state.requestKey = remote.requestKey;
        state.requestApi = remote.requestApi;
        state.pendingRemoteParentSpanId = remote.parentSpanId;
        state.exchangeTransport = normalizedUpper(transport);
        state.exchangeCorrelationId = normalized(correlationId);
        state.exchangeAttemptId = normalized(attemptId);
        state.exchangeHalf = normalizedUpper(half);
        if (activeFrame != null) {
            activeFrame.source = state.source;
            activeFrame.remoteParentSpanId = remote.parentSpanId;
        }
        publishCausalSource(state);
        return token;
    }

    static void exitInbound(long token) {
        restoreScope(token);
    }

    /** Attributes a local exchange leg without inferring any remote state. */
    static View exchange(Object localOwner) {
        State state = CURRENT.get();
        bindLocalOwner(state, localOwner);
        publishCausalSource(state);
        return state.view();
    }

    private static void bindLocalOwner(State state, Object localOwner) {
        SourceRef source = sourceFor(localOwner);
        if (source == null) return;
        state.source = source;
        Frame frame = state.frames.peek();
        if (frame != null) frame.source = source;
    }

    private static void restoreScope(long token) {
        State state = CURRENT.get();
        ScopeFrame scope = state.scopes.peek();
        if (scope == null || scope.token != token) {
            throw new IllegalStateException(
                    "context scopes must end in LIFO order");
        }
        state.scopes.pop();
        state.source = scope.source;
        state.requestKey = scope.requestKey;
        state.requestApi = scope.requestApi;
        state.pendingRemoteParentSpanId = scope.remoteParentSpanId;
        state.exchangeTransport = scope.exchangeTransport;
        state.exchangeCorrelationId = scope.exchangeCorrelationId;
        state.exchangeAttemptId = scope.exchangeAttemptId;
        state.exchangeHalf = scope.exchangeHalf;
        if (scope.activeFrame != null
                && state.frames.peek() == scope.activeFrame) {
            scope.activeFrame.source = scope.frameSource;
            scope.activeFrame.remoteParentSpanId = scope.frameRemoteParentSpanId;
        }
        publishCausalSource(state);
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
     * Resolves an anchor the workload named explicitly in an API call.
     *
     * <p>Registration is by object identity because identity is the only
     * attribution a replay can reproduce.  The application is still free to
     * replace the object it handed over with a value-equal successor:
     * HDFS swaps {@code DataNode.id} for a fresh {@code DatanodeRegistration}
     * on every DataNode re-registration, so the anchor a workload registered
     * before a block-report lease expired is no longer the anchor it passes
     * afterwards.  Refusing the successor throws out of instrumentation into
     * the workload and ends the run; every region downstream of that source
     * is then skipped as anchor-unmatched, and the campaign fails stages
     * later with no trace of why.
     *
     * <p>Only an explicitly named anchor is resolved this way.  Root
     * attribution keeps using {@link #sourceFor} and stays identity-exact: a
     * receiver that registered nothing must go on inheriting its ambient
     * source rather than being matched by value against unrelated objects.
     */
    private static SourceRef resolveNamedAnchorLocked(Object anchor) {
        SourceRef registered = SOURCE_ALIASES.get(anchor);
        if (registered != null) return registered;
        SourceRef replaced = replacedAnchorLocked(anchor);
        // The successor is the identity every later call will carry, so bind
        // it once instead of rescanning on each request.
        if (replaced != null) bindSourceLocked(anchor, replaced);
        return replaced;
    }

    /**
     * The source a value-equal predecessor of {@code anchor} registered.
     *
     * <p>The successor names the same logical source only when both objects
     * declare value equality, agree in both directions, and no second
     * registered anchor answering to it names a different source.  Anything
     * else stays unresolved: a guessed source is a wrong causal chain.
     */
    private static SourceRef replacedAnchorLocked(Object anchor) {
        if (!declaresValueEquality(anchor)) return null;
        SourceRef match = null;
        for (Map.Entry<Object, SourceRef> entry : SOURCE_ALIASES.entrySet()) {
            Object candidate = entry.getKey();
            if (candidate == anchor
                    || !declaresValueEquality(candidate)
                    || !anchor.equals(candidate)
                    || !candidate.equals(anchor)) {
                continue;
            }
            if (match != null && !match.equals(entry.getValue())) return null;
            match = entry.getValue();
        }
        return match;
    }

    /** Whether this object answers by value rather than only by identity. */
    private static boolean declaresValueEquality(Object value) {
        if (value == null) return false;
        try {
            return Object.class != value.getClass()
                    .getMethod("equals", Object.class).getDeclaringClass();
        } catch (NoSuchMethodException unreachable) {
            return false;
        }
    }

    /** Names an anchor a caller passed, without calling its toString(). */
    private static String describeAnchor(Object anchor) {
        if (anchor == null) return "null";
        return anchor.getClass().getName() + "@"
                + Integer.toHexString(System.identityHashCode(anchor));
    }

    /**
     * Whether the recording window has opened in this run.
     *
     * <p>A workload starts its cluster, then names its sources, then does
     * the thing being recorded.  Everything the process did before the first
     * source was registered is outside the window: the recording never saw
     * it, so the plan counted none of it, and a replay that counts it is
     * numbering a different population than the plan numbered.</p>
     *
     * <p>The first registration is the moment, and it is the same moment in
     * every replay of one recording because it is the workload that makes
     * it, not the engine.</p>
     */
    static boolean recordingWindowOpen() {
        synchronized (LOCK) {
            return !SOURCES_BY_KEY.isEmpty();
        }
    }

    /**
     * Whether this run registered exactly {@code sourceKey}, epoch included.
     *
     * <p>{@link #sourceIdentityRegistered} answers about the node and
     * deliberately ignores the epoch, so that a region addressed at one epoch
     * can be matched in a run that reached it.  For deciding whether an
     * activation <em>is</em> a given epoch that is too weak: a workload
     * declares its epochs literally ({@code registerSource(..., 0)} at start,
     * {@code restartSource(..., 1)} across a restart), so the same label means
     * the same lifecycle in every run of it, and a run that never registered
     * {@code ...#epoch1} never had an epoch-1 activation to address.</p>
     */
    static boolean sourceKeyRegistered(String sourceKey) {
        if (sourceKey == null || sourceKey.isEmpty()) return false;
        synchronized (LOCK) {
            return SOURCES_BY_KEY.containsKey(sourceKey);
        }
    }

    /** The keys this run registered for {@code sourceKey}'s node. */
    static String registeredEpochsOf(String sourceKey) {
        List<String> keys = new ArrayList<>();
        synchronized (LOCK) {
            for (String registered : SOURCES_BY_KEY.keySet()) {
                if (sameSourceIdentity(sourceKey, registered)) {
                    keys.add(registered);
                }
            }
        }
        Collections.sort(keys);
        return keys.toString();
    }

    /** Whether {@code sourceKey} names an epoch of its node at all. */
    static boolean declaresEpoch(String sourceKey) {
        String value = sourceKey == null ? "" : sourceKey.trim();
        return !value.isEmpty() && !sourceIdentity(value).equals(value);
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
        child.requestKey = inherited.requestKey;
        child.requestApi = inherited.requestApi;
        child.exchangeTransport = inherited.exchangeTransport;
        child.exchangeCorrelationId = inherited.exchangeCorrelationId;
        child.exchangeAttemptId = inherited.exchangeAttemptId;
        child.exchangeHalf = inherited.exchangeHalf;
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
        final String requestKey;
        final String requestApi;
        final String exchangeTransport;
        final String exchangeCorrelationId;
        final String exchangeAttemptId;
        final String exchangeHalf;

        private View(long laneId, long spanId,
                     long parentSpanId, long remoteParentSpanId,
                     SourceRef source, boolean receiverAttributed,
                     String requestKey, String requestApi,
                     String exchangeTransport, String exchangeCorrelationId,
                     String exchangeAttemptId, String exchangeHalf) {
            this.laneId = laneId;
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.receiverAttributed = receiverAttributed;
            this.requestKey = MapFields.safe(requestKey);
            this.requestApi = MapFields.safe(requestApi);
            this.exchangeTransport = normalizedUpper(exchangeTransport);
            this.exchangeCorrelationId = normalized(exchangeCorrelationId);
            this.exchangeAttemptId = normalized(exchangeAttemptId);
            this.exchangeHalf = normalizedUpper(exchangeHalf);
        }
    }

    private static final class State {
        private long laneId;
        private SourceRef source;
        private long pendingRemoteParentSpanId;
        private String requestKey = "";
        private String requestApi = "";
        private String exchangeTransport = "";
        private String exchangeCorrelationId = "";
        private String exchangeAttemptId = "";
        private String exchangeHalf = "";
        private final Deque<Frame> frames = new ArrayDeque<>();
        private final Deque<ScopeFrame> scopes = new ArrayDeque<>();

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
                    requestKey, requestApi, exchangeTransport,
                    exchangeCorrelationId, exchangeAttemptId, exchangeHalf);
        }
    }

    private static final class Frame {
        private final long spanId;
        private final long parentSpanId;
        private long remoteParentSpanId;
        private final SourceRef previousSource;
        private SourceRef source;
        private final boolean receiverAttributed;
        private final String previousRequestKey;
        private final String previousRequestApi;
        private final String previousExchangeTransport;
        private final String previousExchangeCorrelationId;
        private final String previousExchangeAttemptId;
        private final String previousExchangeHalf;

        private Frame(long spanId, long parentSpanId,
                      long remoteParentSpanId, SourceRef previousSource,
                      SourceRef source, boolean receiverAttributed,
                      String previousRequestKey, String previousRequestApi,
                      String previousExchangeTransport,
                      String previousExchangeCorrelationId,
                      String previousExchangeAttemptId,
                      String previousExchangeHalf) {
            this.spanId = spanId;
            this.parentSpanId = parentSpanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.previousSource = previousSource;
            this.source = source;
            this.receiverAttributed = receiverAttributed;
            this.previousRequestKey = MapFields.safe(previousRequestKey);
            this.previousRequestApi = MapFields.safe(previousRequestApi);
            this.previousExchangeTransport = normalizedUpper(
                    previousExchangeTransport);
            this.previousExchangeCorrelationId = normalized(
                    previousExchangeCorrelationId);
            this.previousExchangeAttemptId = normalized(
                    previousExchangeAttemptId);
            this.previousExchangeHalf = normalizedUpper(previousExchangeHalf);
        }
    }

    private static final class Seed {
        private final long parentSpanId;
        private final SourceRef source;
        private final String requestKey;
        private final String requestApi;
        private final String exchangeTransport;
        private final String exchangeCorrelationId;
        private final String exchangeAttemptId;
        private final String exchangeHalf;

        private Seed(long parentSpanId, SourceRef source,
                     String requestKey, String requestApi,
                     String exchangeTransport, String exchangeCorrelationId,
                     String exchangeAttemptId, String exchangeHalf) {
            this.parentSpanId = parentSpanId;
            this.source = source;
            this.requestKey = MapFields.safe(requestKey);
            this.requestApi = MapFields.safe(requestApi);
            this.exchangeTransport = normalizedUpper(exchangeTransport);
            this.exchangeCorrelationId = normalized(exchangeCorrelationId);
            this.exchangeAttemptId = normalized(exchangeAttemptId);
            this.exchangeHalf = normalizedUpper(exchangeHalf);
        }
    }

    private static final class ScopeFrame {
        private final long token;
        private final SourceRef source;
        private final Frame activeFrame;
        private final SourceRef frameSource;
        private final long frameRemoteParentSpanId;
        private final long remoteParentSpanId;
        private final String requestKey;
        private final String requestApi;
        private final String exchangeTransport;
        private final String exchangeCorrelationId;
        private final String exchangeAttemptId;
        private final String exchangeHalf;

        private ScopeFrame(long token, State state, Frame activeFrame) {
            this.token = token;
            this.source = state.source;
            this.activeFrame = activeFrame;
            this.frameSource = activeFrame == null ? null : activeFrame.source;
            this.frameRemoteParentSpanId = activeFrame == null ? 0L
                    : activeFrame.remoteParentSpanId;
            this.remoteParentSpanId = state.pendingRemoteParentSpanId;
            this.requestKey = state.requestKey;
            this.requestApi = state.requestApi;
            this.exchangeTransport = state.exchangeTransport;
            this.exchangeCorrelationId = state.exchangeCorrelationId;
            this.exchangeAttemptId = state.exchangeAttemptId;
            this.exchangeHalf = state.exchangeHalf;
        }
    }

    private static String normalized(String value) {
        return MapFields.safe(value).trim();
    }

    private static String normalizedUpper(String value) {
        return normalized(value).toUpperCase(Locale.ROOT);
    }

    private static String encoded(String value) {
        return Base64.getUrlEncoder().withoutPadding().encodeToString(
                value.getBytes(StandardCharsets.UTF_8));
    }

    private static String decoded(String value) {
        try {
            String decoded = new String(Base64.getUrlDecoder().decode(value),
                    StandardCharsets.UTF_8);
            if (!encoded(decoded).equals(value)) throw new IllegalArgumentException();
            return decoded;
        } catch (IllegalArgumentException malformed) {
            throw new IllegalArgumentException("malformed trace context header");
        }
    }

    private static final class MessageContext {
        private final long parentSpanId;
        private final SourceRef source;
        private final String requestKey;
        private final String requestApi;

        private MessageContext(long parentSpanId, SourceRef source,
                               String requestKey, String requestApi) {
            this.parentSpanId = parentSpanId;
            this.source = source;
            this.requestKey = requestKey;
            this.requestApi = requestApi;
        }

        private static MessageContext parse(String header) {
            String[] parts = MapFields.safe(header).split("\\|", -1);
            try {
                if (parts.length != 8 || !"1".equals(parts[0])) {
                    throw new IllegalArgumentException();
                }
                long parentSpan = Long.parseLong(parts[1]);
                long epoch = Long.parseLong(parts[2]);
                if (parentSpan < 0L || epoch < 0L) {
                    throw new IllegalArgumentException();
                }
                SourceRef source = new SourceRef(decoded(parts[3]),
                        decoded(parts[4]), decoded(parts[5]), epoch);
                String requestKey = decoded(parts[6]);
                String requestApi = decoded(parts[7]);
                if (requestKey.isEmpty() || requestApi.isEmpty()) {
                    throw new IllegalArgumentException();
                }
                return new MessageContext(parentSpan, source,
                        requestKey, requestApi);
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        "malformed trace context header");
            }
        }
    }

}
