package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.runtime.Lineage;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Base64;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
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
        Frame activeFrame = state.frames.peek();
        ScopeFrame scope = new ScopeFrame(requestId, state, activeFrame);
        // The workload's own action is the root of this lineage: every
        // activation under it states which action it descends from, and
        // which k-th one, instead of only which request key was in force.
        scope.lineageToken = Lineage.push(source.key(), Role.CLIENT,
                normalizedApi);
        // The key's ordinal is that lineage's k -- one counter -- and it
        // addresses nothing: the trace and the wire header carry it as text.
        String requestKey = source.key() + "/request/" + normalizedApi
                + "#" + Lineage.rootWindowIndex();
        // A root the thread opens for itself: the index of what runs inside
        // begins at the request, and a start frame standing above it is the
        // frame of the ROOT that carried this thread here, not of the
        // request (Identity.Hop.SCOPE_ROOT).
        scope.scopeBaseBefore = edu.uva.liftlab.graphchecker.runtime.Identity.scopeStart(
                edu.uva.liftlab.graphchecker.runtime.Identity.Hop
                        .SCOPE_ROOT);
        scope.opened = source;
        state.scopes.push(scope);
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
        if (carrier instanceof java.util.Collection) {
            // A batch submission is one submission per task: two subtasks
            // of one invokeAll run under two endpoints, which is the only
            // thing that tells their activations apart.
            for (Object element : (java.util.Collection<?>) carrier) {
                captureAsync(element);
            }
            return;
        }
        State state = CURRENT.get();
        View view = state.view();
        // The lineage travels with the work, exactly as the request scope
        // does: a pool thread created before the scope existed inherits
        // neither, and both are facts about the work rather than the thread.
        // The node it carries EXPLICITLY is the starter's explicit scope and
        // nothing weaker: a node the starter only resolved by its frames or
        // its own starter is what the work's reference already states
        // (Attribution, rule 3), and made explicit here it would outrank the
        // work's own frames.
        String nodeKey = view.source == null ? "" : view.source.key();
        Object lineage = Lineage.capture(nodeKey);
        synchronized (LOCK) {
            ASYNC_SEEDS.put(carrier, new Seed(
                    explicitSource(), view.requestKey, view.requestApi,
                    view.exchangeTransport, view.exchangeCorrelationId,
                    view.exchangeAttemptId, view.exchangeHalf, lineage));
        }
    }

    /**
     * Enters, on the claiming thread, the scope a start carried.
     *
     * <p>The CLAIM half of every handoff ({@code Identity}'s claim of a
     * start), in both passes: the scope the starter stood in -- its explicit
     * node, its request flow, its lineage -- comes with the work to whatever
     * pool thread takes it, and is left when the work's start level goes
     * ({@link #releaseCarried}).  This is what replaced the carried scopes
     * hand-woven into each Hadoop tree's pool tasks.</p>
     *
     * <p>No scope START here: the index of the work begins at its start
     * frame, which is what tells two siblings started from one site apart.
     * </p>
     */
    static void claimCarried(Object carrier) {
        Seed seed = takeSeed(carrier);
        if (seed == null) return;
        boolean flow = !seed.requestKey.isEmpty() && !seed.requestApi.isEmpty();
        boolean lineage = seed.lineage instanceof Lineage.Carried
                && ((Lineage.Carried) seed.lineage).names();
        if (seed.source == null && !flow && !lineage) return;
        releaseCarried();
        State state = CURRENT.get();
        Frame activeFrame = state.frames.peek();
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state, activeFrame);
        scope.opened = seed.source;
        scope.lineageToken = Lineage.restore(seed.lineage,
                seed.source == null ? "" : seed.source.key(),
                Role.EXECUTOR_TASK, "");
        state.scopes.push(scope);
        if (seed.source != null) state.source = seed.source;
        state.requestKey = seed.requestKey;
        state.requestApi = seed.requestApi;
        state.exchangeTransport = seed.exchangeTransport;
        state.exchangeCorrelationId = seed.exchangeCorrelationId;
        state.exchangeAttemptId = seed.exchangeAttemptId;
        state.exchangeHalf = seed.exchangeHalf;
        CARRIED.set(token);
        publishCausalSource(state);
    }

    /** Leaves the scope the last claim on this thread entered, if any. */
    static void releaseCarried() {
        Long token = CARRIED.get();
        if (token == null) return;
        CARRIED.remove();
        restoreScope(token);
    }

    /** The token of the carried scope this thread's claimed work runs in. */
    private static final ThreadLocal<Long> CARRIED = new ThreadLocal<Long>();

    /**
     * Rule 1 of the attribution rule: the innermost explicit scope's node,
     * or null.
     */
    static SourceRef explicitSource() {
        State state = CURRENT.get();
        for (ScopeFrame scope : state.scopes) {
            if (scope.opened != null) return scope.opened;
        }
        return null;
    }

    /**
     * The explicit scope this thread's CREATOR stood in when it constructed
     * it, or null ({@link Attribution}, rule 3).
     */
    static SourceRef inheritedSource() {
        return CURRENT.get().inheritedSource;
    }

    /** The first of these objects that is registered, by identity. */
    static SourceRef firstRegistered(java.util.List<Object> objects) {
        if (objects == null || objects.isEmpty()) return null;
        synchronized (LOCK) {
            for (Object object : objects) {
                if (object == null) continue;
                SourceRef source = SOURCE_ALIASES.get(object);
                if (source != null) return source;
            }
        }
        return null;
    }

    /**
     * Starts one root activation; nested methods reuse its span.
     *
     * <p>Opens no execution-index SCOPE.  This method is reached from the
     * trace recorder's method hook and from nowhere else, so a scope opened
     * here would exist in the recording and not in any replay, and the
     * index of every occurrence under it would start at a different frame in
     * the two passes -- which is a second identity.  A scope is opened where
     * the workload says one begins (a request, a daemon tick, a carried
     * scope, an inbound exchange), and those calls are the same code in both
     * passes.  What this arm used to protect against -- a pool thread
     * carrying the frames of whatever created it -- is answered by the start
     * frame instead: {@link Identity#startWork} files the frame of the start
     * that created the work, and {@link Identity} drops a finished task's
     * start frame before the next one (REPORT-P2H).</p>
     */
    static View enterRoot(Object receiver) {
        State state = CURRENT.get();
        // A start's scope is taken back where the work CLAIMS it
        // (#claimCarried), in both passes; this hook is the recording's alone.
        SourceRef registered = sourceFor(receiver);
        // Which authority answered: the receiver's own registration, or the
        // context this thread inherited.  Replay can reproduce the first by
        // object identity and the second only by thread context, so the
        // activation has to say which one named it.
        boolean receiverAttributed = registered != null;
        // THE attribution rule, the one the replay evaluates at the same
        // entry (Attribution).
        SourceRef source = Attribution.resolve(receiver);
        // A receiver that named no source of its own keeps the ambient stamp,
        // which is the only answer available while the trace is being written.
        if (state.laneId == 0L) {
            state.laneId = nextId();
        }
        long spanId = nextId();
        // A receive scope belongs to the server lane until the next receive
        // replaces it.
        long remoteParentSpanId = state.pendingRemoteParentSpanId;
        Frame frame = new Frame(spanId, remoteParentSpanId,
                state.source, source, receiverAttributed,
                state.requestKey, state.requestApi,
                state.exchangeTransport, state.exchangeCorrelationId,
                state.exchangeAttemptId, state.exchangeHalf);
        state.source = source;
        state.frames.push(frame);
        publishCausalSource(state);
        return state.view();
    }

    static void exitRoot(long spanId) {
        State state = CURRENT.get();
        Frame frame = state.frames.peek();
        if (frame == null || frame.spanId != spanId) return;
        state.frames.pop();
        if (frame.lineageToken > 0L) Lineage.release(frame.lineageToken);
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

    /**
     * The request scope of the thread that is calling, as a value.
     *
     * <p>A request scope belongs to the work, not to the thread: Hadoop's
     * {@code Client} builds a {@code Call} on the caller's thread and writes
     * it from a sender thread of its own pool, created once when the
     * connection was set up.  This state is an
     * {@link InheritableThreadLocal}, so it reaches a thread created inside
     * a scope and never one created before it -- and which of the two the
     * sender is, is an accident of when the connection happened to be
     * opened.  Captured here at the moment the work is created and carried
     * with it, the scope is the same in a recording and in a replay whatever
     * the pool does.</p>
     */
    static Object captureScope() {
        View view = CURRENT.get().view();
        String nodeKey = view.source == null ? "" : view.source.key();
        return new RequestScope(view.source, view.requestKey,
                view.requestApi, Lineage.capture(nodeKey));
    }

    /**
     * Enters a scope captured where the work was created.
     *
     * <p>The dequeue half of a queue that outlives its enqueueing thread.
     * Hadoop's IPC {@code Server.Call} is built on a reader thread and run
     * on a handler thread of a pool created once at connection setup: an
     * {@link InheritableThreadLocal} reaches a handler only if the handler
     * happened to be created inside a scope, which is why on hdfs-17899
     * bug3 two handlers of one pool carried the caller's scope and a third
     * did not, varying run to run.  Carried at enqueue and restored here,
     * the scope is the same in a recording and in a replay whatever the
     * pool does.</p>
     *
     * @return the token that leaves the scope again, or 0 when the carried
     *         value names none and nothing was entered
     */
    static long enterCarriedScope(Object carriedScope, String roleName,
                                  String apiName) {
        if (!(carriedScope instanceof RequestScope)) return 0L;
        RequestScope scope = (RequestScope) carriedScope;
        if (!scope.names()) return 0L;
        State state = CURRENT.get();
        Frame activeFrame = state.frames.peek();
        long token = nextId();
        ScopeFrame frame = new ScopeFrame(token, state, activeFrame);
        frame.opened = scope.source;
        state.scopes.push(frame);
        state.source = scope.source;
        state.requestKey = scope.requestKey;
        state.requestApi = scope.requestApi;
        if (activeFrame != null) activeFrame.source = scope.source;
        String api = MapFields.safe(apiName).isEmpty()
                ? scope.requestApi : MapFields.safe(apiName);
        frame.lineageToken = Lineage.restore(scope.lineage,
                scope.source.key(), Role.of(roleName), api);
        // The same root: the carried scope is the work's, and the pool
        // thread that dequeued it is not (Identity.Hop.SCOPE_ROOT).
        frame.scopeBaseBefore = edu.uva.liftlab.graphchecker.runtime.Identity.scopeStart(
                edu.uva.liftlab.graphchecker.runtime.Identity.Hop
                        .SCOPE_ROOT);
        publishCausalSource(state);
        return token;
    }

    /** Leaves the scope {@link #enterCarriedScope} entered. */
    static void exitCarriedScope(long token) {
        if (token > 0L) restoreScope(token);
    }

    /**
     * Opens one daemon tick as a lineage root.
     *
     * <p>A timer thread is created by no request and serves none, so it has
     * no scope to repair: {@code HeartbeatManager$Monitor}, {@code
     * BPServiceActor} and the key-manager updater measured 0% scoped on
     * every run.  The tick is its own root -- role plus a window-local k --
     * which is what makes the NameNode's key rotation an addressable
     * occurrence instead of a family-less one (REPORT-NNCHAIN §5).  It
     * touches no request scope: v1 addresses are exactly what they were.</p>
     *
     * @return the token that closes the tick
     */
    static long beginTick(Object owner, String roleName) {
        State state = CURRENT.get();
        // The tick's OWNER is an explicit scope when it is registered
        // (Attribution, rule 1); otherwise the tick is the thread's.
        SourceRef owned = sourceFor(owner);
        SourceRef source = owned != null ? owned : Attribution.resolve(null);
        // A root that IS the started work, so its index begins at the start
        // frame the work claimed: the tick's own beginning
        // (Identity.Hop.STARTED_ROOT).
        int scopeBaseBefore = edu.uva.liftlab.graphchecker.runtime.Identity.scopeStart(
                edu.uva.liftlab.graphchecker.runtime.Identity.Hop
                        .STARTED_ROOT);
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state, state.frames.peek());
        scope.scopeBaseBefore = scopeBaseBefore;
        scope.opened = owned;
        // A ROOT hop, whatever this thread already stands in: a tick is
        // started by no message and serves none, so it descends from
        // nothing (Lineage#pushRoot).  A nested hop made
        // KeyManager$BlockKeyUpdater's tick render the balance-block
        // request's own Root:CLIENT#1.
        scope.lineageToken = Lineage.pushRoot(
                source == null ? "" : source.key(), Role.of(roleName), "");
        state.scopes.push(scope);
        // A tick is the special case of a service-loop turn (TimedWaits):
        // what it sends is a request of its node's, so it carries a request
        // flow the way a turn does, and a heartbeat sent inside it reaches
        // its server anchored rather than Lost.  Put back when it closes.
        if (source != null
                && !UNREGISTERED_SOURCE.key().equals(source.key())) {
            String api = MapFields.safe(roleName).trim();
            if (api.isEmpty()) api = "tick";
            state.source = source;
            state.requestKey = source.key() + "/tick/" + api + "#"
                    + Lineage.rootWindowIndex();
            state.requestApi = api;
        }
        return token;
    }

    /** Closes the tick {@link #beginTick} opened. */
    static void endTick(long token) {
        restoreScope(token);
    }

    /**
     * Opens one turn of a service loop as a root scope ({@code TimedWaits}).
     *
     * <p>A root, like a tick: started by no message, descending from nothing
     * ({@link Lineage#pushRoot}), its k the k-th turn of this loop on this node
     * in the window.  Unlike a tick it carries a request flow -- source, key,
     * api -- because what a turn sends is a request of that node's, and a
     * message without one reaches its server as a {@code Lost} context.  The
     * index of what runs inside begins here ({@code Identity.Hop.SCOPE_ROOT}).
     * </p>
     *
     * @return the token that closes the turn, or 0 when the thread belongs to
     *         no node the run can name and nothing was opened
     */
    static long beginWake(String api) {
        // A timed wait inside a request, a carried scope or a served message
        // is a pause WITHIN that work -- a workload polling for its own
        // result, a handler backing off -- and not the next turn of a
        // daemon: the work it pauses stays the work that runs after it.
        State current = CURRENT.get();
        for (ScopeFrame standing : current.scopes) {
            if (!standing.turn) return 0L;
        }
        SourceRef source = activationSource(null);
        if (source == null
                || UNREGISTERED_SOURCE.key().equals(source.key())) {
            return 0L;
        }
        String normalizedApi = MapFields.safe(api).trim();
        if (normalizedApi.isEmpty()) normalizedApi = "wake";
        State state = CURRENT.get();
        long token = nextId();
        Frame activeFrame = state.frames.peek();
        ScopeFrame scope = new ScopeFrame(token, state, activeFrame);
        scope.opened = source;
        scope.turn = true;
        scope.lineageToken = Lineage.pushRoot(source.key(), Role.of("WAKE"),
                normalizedApi);
        scope.scopeBaseBefore = edu.uva.liftlab.graphchecker.runtime.Identity.scopeStart(
                edu.uva.liftlab.graphchecker.runtime.Identity.Hop.SCOPE_ROOT);
        state.scopes.push(scope);
        state.source = source;
        state.requestKey = source.key() + "/wake/" + normalizedApi + "#"
                + Lineage.rootWindowIndex();
        state.requestApi = normalizedApi;
        if (activeFrame != null) activeFrame.source = source;
        publishCausalSource(state);
        return token;
    }

    /**
     * Closes the turn {@code token} opened when it is the innermost scope, and
     * says whether it did.
     *
     * <p>Only then: a scope opened inside the turn and still standing belongs
     * to whoever opened it, and closing the turn under it would break the LIFO
     * order every scope's own close relies on.</p>
     */
    static boolean endWakeIfInnermost(long token) {
        State state = CURRENT.get();
        boolean standing = false;
        for (ScopeFrame open : state.scopes) {
            if (open.token == token) {
                standing = true;
                break;
            }
        }
        // Closed already, by an outer scope's close: nothing left to do.
        if (!standing) return true;
        ScopeFrame innermost = state.scopes.peek();
        if (innermost == null || innermost.token != token) return false;
        restoreScope(token);
        return true;
    }

    /** One captured request scope; opaque to its carrier. */
    static final class RequestScope {
        private final SourceRef source;
        private final String requestKey;
        private final String requestApi;
        /** The lineage the work was created inside, as a value. */
        private final Object lineage;

        private RequestScope(SourceRef source, String requestKey,
                             String requestApi, Object lineage) {
            this.source = source;
            this.requestKey = requestKey == null ? "" : requestKey;
            this.requestApi = requestApi == null ? "" : requestApi;
            this.lineage = lineage;
        }

        boolean names() {
            return source != null && !requestKey.isEmpty()
                    && !requestApi.isEmpty();
        }

    }

    /** Encodes the current node and request flow for the next message. */
    static String outboundHeader(Object localOwner) {
        return outboundHeader(localOwner, null);
    }

    /**
     * The same header, for work whose scope was captured where it was made.
     *
     * <p>The carried scope decides when it names one: the thread doing the
     * write may be a pool thread that never saw the request.  Without one --
     * every caller before this and every send the workload makes inline --
     * the thread's own scope answers exactly as before.</p>
     */
    static String outboundHeader(Object localOwner, Object carriedScope) {
        State state = CURRENT.get();
        View view = scoped(owned(state.view(), localOwner), carriedScope);
        if (view.source == null || view.requestKey.isEmpty()
                || view.requestApi.isEmpty()) {
            // Named, because the refusal decides whether the workload's own
            // fault marker runs: bug2 guards it with causynth.active(), and
            // an envelope refused here is an empty Outbound, so the marker
            // behind that guard is never called and mints nothing.  "It
            // refused" is not a finding a reader can act on; which of the
            // three was missing is.
            //
            // Both halves, separately: the carried scope is the scope of
            // the send, and the thread's is only what answers when no scope
            // was carried.  One combined list could not tell "the work
            // carried nothing" from "the work carried a node and no
            // request", and those have different owners -- the first is the
            // carry, the second is where the work was created.
            // The thread is not named: the refusal is published as a row,
            // and a row a reader compares across replays cannot be keyed
            // by which pool thread happened to perform the write -- that
            // accident is the whole reason a scope is carried at all.
            throw new IllegalStateException(
                    "outbound message requires source and request flow;"
                            + " the call carried " + describe(carriedScope)
                            + " and the thread it is sent on carries no"
                            + missing(owned(state.view(), localOwner)));
        }
        return header(view.source, view.requestKey, view.requestApi,
                view.spanId);
    }

    /** One wire header; the same eight fields whatever named the scope. */
    private static String header(SourceRef source, String requestKey,
                                 String requestApi, long spanId) {
        return "1|" + spanId + "|" + source.epoch()
                + "|" + encoded(source.kind())
                + "|" + encoded(source.role())
                + "|" + encoded(source.id())
                + "|" + encoded(requestKey)
                + "|" + encoded(requestApi);
    }

    /** Installs one received message and its exact transport exchange. */
    static long enterInbound(String header, String transport,
                             String correlationId, String attemptId,
                             String half, Object localOwner) {
        MessageContext remote = MessageContext.parse(header);
        State state = CURRENT.get();
        Frame activeFrame = state.frames.peek();
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state, activeFrame);
        state.scopes.push(scope);
        // Execution context is set by execution-scope events only: a node's
        // registration of its instances, or an async seed from a registered
        // source.  A value arriving over the wire is provenance, and the
        // propagated expression already carries it.
        //
        // The third arm of this used to be the SENDER's source, parsed out of
        // the message header, and it wrote that node into the RECEIVING
        // thread's ambient context whenever the local owner was unregistered
        // and the thread had no source yet.  At record time a DataNode thread
        // already carries the DN, so the arm never fired; at replay the
        // thread may be fresh, so it did -- and on hdfs-17899 bug3 that is
        // "matching root inherited hdfs-17899/nn0#epoch0 instead of
        // hdfs-17899/target-dn#epoch0", an activation addressed to the node
        // whose value it received rather than the node it ran on.  Same
        // function on both sides, over inputs only the replay mutated.
        SourceRef localSource = sourceFor(localOwner);
        // A registered local owner is this scope's EXPLICIT node
        // (Attribution, rule 1), for exactly as long as the scope stands.
        scope.opened = localSource;
        if (localSource != null) {
            state.source = localSource;
        }
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
        // The hop a served message opens: which role served it, for which
        // remote family, and the k-th time this node served that family.
        // The api is the remote family rather than the bare api because two
        // callers of one api are two populations -- the v1 family suffix,
        // stated as the hop it always was.
        // The role a served message opens its scope under is the transport
        // the WORKLOAD named at the exchange -- one string, carried.  A
        // table here mapped IPC/RPC to one Hadoop role and
        // SASL/DATA_TRANSFER/XCEIVER to another, which is a deployment's
        // vocabulary in engine code and a guess for every transport it did
        // not list.
        scope.lineageToken = Lineage.push(
                state.source == null ? "" : state.source.key(),
                Role.of(state.exchangeTransport),
                inboundFamily(remote.requestKey, remote.requestApi));
        // An anchored request: the index of what serves it begins at the
        // inbound scope, and the frames above it -- the pooled handler's
        // start frame, Server$Handler.run, RpcCall.run -- are the carrier
        // thread's (Identity.Hop.ANCHOR).  Which handler serves a request
        // is scheduling; the anchor below already identifies it.
        scope.scopeBaseBefore = edu.uva.liftlab.graphchecker.runtime.Identity.scopeStart(
                edu.uva.liftlab.graphchecker.runtime.Identity.Hop.ANCHOR);
        // The message that opened this scope names its producer; that
        // endpoint IS this occurrence's causal context (IDENTITY-V3).
        Lineage.anchor(edu.uva.liftlab.graphchecker.runtime.Interactions
                        .sender(state.exchangeTransport,
                                state.exchangeCorrelationId,
                                state.exchangeHalf),
                // The api is the LAST path segment, which is how a case's
                // selector is matched against it (ComposeMain.apiOf).
                normalizedUpper(transport) + "/"
                        + MapFields.safe(remote.requestApi));
        publishCausalSource(state);
        return token;
    }

    /**
     * Who the served message belongs to: {@code <source>/<api>} of the
     * request in force, else the bare api.
     *
     * <p>Not the whole request key: its trailing ordinal counts requests in
     * the recording window, which is the one part a replay cannot be held
     * to.  Not a request FAMILY either, in the deleted sense -- nothing is
     * addressed by it.  It is the hop's api, and it carries the caller
     * because two callers of one api are two populations and their hops
     * must not share a k.</p>
     */
    private static String inboundFamily(String requestKey, String requestApi) {
        String key = MapFields.safe(requestKey).trim();
        int marker = key.lastIndexOf("/request/");
        if (marker <= 0) return MapFields.safe(requestApi).trim();
        String source = key.substring(0, marker);
        String api = key.substring(marker + "/request/".length());
        int ordinal = api.lastIndexOf('#');
        if (ordinal > 0) api = api.substring(0, ordinal);
        return source.isEmpty() || api.isEmpty()
                ? MapFields.safe(requestApi).trim() : source + "/" + api;
    }

    static void exitInbound(long token) {
        restoreScope(token);
    }

    /**
     * The same leg, for work carrying the scope it was made in.
     *
     * <p>The node the send is filed under is the node the carried scope
     * names, so the recorded row and the wire header agree and neither
     * depends on which thread performed the write.</p>
     */
    static View exchange(Object localOwner, Object carriedScope) {
        State state = CURRENT.get();
        View view = scoped(owned(state.view(), localOwner), carriedScope);
        publishCausalSource(view);
        return view;
    }

    /** The view this work speaks with: its carried scope when it names one. */
    /** Which of the three a view is missing, as " a b c" or "thing". */
    private static String missing(View view) {
        StringBuilder absent = new StringBuilder();
        if (view.source == null) absent.append(" source");
        if (view.requestKey.isEmpty()) absent.append(" requestKey");
        if (view.requestApi.isEmpty()) absent.append(" requestApi");
        return absent.length() == 0 ? "thing" : absent.toString();
    }

    /** What a carried scope holds, for a refusal that has to be actionable. */
    private static String describe(Object carriedScope) {
        if (carriedScope == null) return "no scope at all";
        if (!(carriedScope instanceof RequestScope)) {
            return "a scope this runtime did not mint";
        }
        RequestScope scope = (RequestScope) carriedScope;
        if (scope.names()) return "a complete scope";
        StringBuilder held = new StringBuilder();
        if (scope.source != null) {
            held.append(" source=").append(scope.source.key());
        }
        if (!scope.requestKey.isEmpty()) {
            held.append(" requestKey=").append(scope.requestKey);
        }
        if (!scope.requestApi.isEmpty()) {
            held.append(" requestApi=").append(scope.requestApi);
        }
        return held.length() == 0 ? "an empty scope"
                : "a partial scope holding only" + held;
    }

    private static View scoped(View view, Object carriedScope) {
        RequestScope scope = carriedScope instanceof RequestScope
                ? (RequestScope) carriedScope : null;
        if (scope == null || !scope.names()) return view;
        return view.withScope(scope.source, scope.requestKey,
                scope.requestApi);
    }

    /**
     * The view of one exchange leg made on behalf of a registered local
     * owner: that owner's node, for this leg only.
     *
     * <p>A local owner used to be BOUND -- written into the thread's ambient
     * source, where it stayed after the leg and named every later event of
     * the thread.  It is a frame now: the leg speaks for the owner, and
     * nothing it names outlives the leg.</p>
     */
    static View owned(View view, Object localOwner) {
        SourceRef source = sourceFor(localOwner);
        if (source == null) return view;
        return view.withScope(source, view.requestKey, view.requestApi);
    }

    /** The node a leg made on behalf of {@code localOwner} belongs to. */
    static SourceRef ownedSource(Object localOwner) {
        SourceRef owned = sourceFor(localOwner);
        if (owned != null) return owned;
        return activationSource(null);
    }

    private static void restoreScope(long token) {
        State state = CURRENT.get();
        boolean standing = false;
        for (ScopeFrame open : state.scopes) {
            if (open.token == token) {
                standing = true;
                break;
            }
        }
        // A scope that is not standing was already closed -- by an outer
        // scope's close, which takes every scope opened inside it along --
        // and closing it again is nothing.  A hook never throws into the
        // workload for it.
        if (!standing) return;
        while (state.scopes.peek() != null
                && state.scopes.peek().token != token) {
            ScopeFrame inner = state.scopes.peek();
            restoreOne(state, inner);
        }
        restoreOne(state, state.scopes.peek());
        publishCausalSource(state);
    }

    /** Closes the innermost scope and puts back what it replaced. */
    private static void restoreOne(State state, ScopeFrame scope) {
        state.scopes.pop();
        if (scope.lineageToken > 0L) Lineage.release(scope.lineageToken);
        if (scope.scopeBaseBefore >= 0) {
            edu.uva.liftlab.graphchecker.runtime.Identity.scopeRestore(
                    scope.scopeBaseBefore);
        }
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
        if (CARRIED.get() != null && CARRIED.get() == scope.token) {
            CARRIED.remove();
        }
    }

    /**
     * Hands the thread's freshly established source to the occurrence running
     * on it.
     */
    private static void publishCausalSource(State state) {
        publishCausalSource(state.view());
    }

    private static void publishCausalSource(View view) {
        ConcolicRegionRuntime.observeCausalSource(
                view.source == null ? "" : view.source.key());
    }

    static void resetForTests() {
        Lineage.resetForTests();
        synchronized (LOCK) {
            SOURCE_ALIASES.clear();
            SOURCES_BY_KEY.clear();
            ASYNC_SEEDS.clear();
        }
        CURRENT.remove();
        IDS.set(1L);
        // A fixture models a run that is recording: the workload under test
        // has opened its window.  A test about the window itself says
        // otherwise for itself.
        RecordingWindow.reset();
        RecordingWindow.open();
    }

    private static Seed takeSeed(Object carrier) {
        if (carrier == null) return null;
        synchronized (LOCK) {
            return ASYNC_SEEDS.remove(carrier);
        }
    }

    /**
     * The source one root activation is attributed to, or {@code null}.
     *
     * <p>The receiver's own registration, then the async seed the thread or
     * the receiver carries, then this thread's ambient execution context --
     * and nothing else.  Every arm is execution scope: a node's registration
     * of its own instances, and the context a registered node's thread
     * carries.  Since a value arriving over the wire no longer writes the
     * ambient context, the answer is where the activation RAN.</p>
     *
     * <p>It is one function because the recorder stamps every {@code
     * METHOD_ENTER} with it ({@link #enterRoot}), the planner names and
     * counts the occurrence by that stamp ({@code
     * RuntimeRegionPlanner.activationSource}), and the replay has to ask the
     * same question of the same inputs.  When the replay asked its own
     * version -- the registration, else the ambient context only when it
     * already named the planned node, else the plan's own key -- every
     * activation of one region in a JVM running three nodes fell into the
     * planned node's bucket, and on hdfs-17899 bug3 the planned first
     * activation of {@code REGION.16ba41cf} on target-dn was answered by
     * "invocation 2 instead of 1" while the NameNode's own activation of it,
     * counted as target-dn's first, was published as source-dn's.</p>
     */
    static SourceRef activationSource(Object receiver) {
        return activationSource(receiver,
                Collections.<SourceRef>emptyList());
    }

    /**
     * The planner's own attribution rule, evaluated by the replay.
     *
     * <p>{@code RuntimeRegionPlanner.activationSource} reads an activation's
     * own {@code METHOD_ENTER} stamp, and when there is none takes the
     * <em>unique</em> stamp among the activation's own frames, and when there
     * is not exactly one of those attributes the activation to the
     * unregistered source.  This is that function, with the stamp computed
     * live rather than read out of a trace, so the two ends cannot answer
     * differently.</p>
     *
     * <p>The third arm used to be the replay's own: the PLANNED node.  That
     * is what let an activation nothing had stamped count in the planned
     * node's bucket -- on hdfs-17899 bug2 the DataNode heartbeats that run
     * before the workload registers {@code dn.getDatanodeId()} carry no node
     * at all, and each one's {@code PBHelper.convert} took a k in
     * target-dn's count ahead of the heartbeat the plan addresses, which is
     * "occurrence is activation 2, not 1" on a region whose own activation
     * was there all along.  The planner never counted them there, because
     * the planner puts them in the unregistered source's own population.</p>
     *
     * @param frameStamps the sources the activation's own frames carry, in
     *                    recorded order; empty at a root entry, where no
     *                    frame of the activation has run yet
     */
    static SourceRef activationSource(Object receiver,
                                      Collection<SourceRef> frameStamps) {
        return attributedActivationSource(Attribution.resolve(receiver),
                frameStamps);
    }

    /**
     * One activation's source: its own stamp, else the unique stamp among
     * its frames, else the unregistered source.  Never null.
     *
     * <p>The second arm is a refusal when it is not unique: two frames of
     * one activation that name two components say the run cannot attribute
     * the activation, and it goes to the unregistered population rather
     * than to the first of the two.  That was already the answer and it was
     * silent, so nothing downstream could tell it from an activation nothing
     * had stamped at all -- and the two are different facts: one is missing
     * evidence, the other is contradictory evidence about where an
     * occurrence ran.  The class is every activation whose frames disagree,
     * on either pass, since this is the one rule both evaluate.</p>
     */
    static SourceRef attributedActivationSource(
            SourceRef stamp, Collection<SourceRef> frameStamps) {
        if (stamp != null) return stamp;
        SourceRef unique = null;
        if (frameStamps != null) {
            for (SourceRef frame : frameStamps) {
                if (frame == null) continue;
                if (unique == null) {
                    unique = frame;
                } else if (!unique.key().equals(frame.key())) {
                    RowRuntime.gap(edu.uva.liftlab.graphchecker.contract
                                    .GapKind.LINEAGE_LOST,
                            edu.uva.liftlab.graphchecker.contract
                                    .GapClass.DIAGNOSTIC,
                            unique.key() + " vs " + frame.key(),
                            "two frames of one activation name two"
                                    + " components, so the run attributes it"
                                    + " to no node and counts it in the"
                                    + " unregistered population");
                    return UNREGISTERED_SOURCE;
                }
            }
        }
        return unique == null ? UNREGISTERED_SOURCE : unique;
    }

    /**
     * The node the running thread belongs to right now, by the attribution
     * rule every activation is stamped with ({@link #activationSource}).
     */
    static String nodeHere() {
        SourceRef source = activationSource(null);
        return source == null ? "" : source.key();
    }

    /** The source an activation nothing attributed belongs to: the
     *  planner's own constant, so the two ends name one population. */
    static final SourceRef UNREGISTERED_SOURCE =
            RuntimeRegionPlanner.UNREGISTERED_SOURCE;

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
     * The source an anchor the workload named explicitly is registered as.
     *
     * <p>Object identity, and nothing else: identity is the only attribution
     * a replay can reproduce.  A value-equal successor used to be matched
     * here too -- HDFS swaps {@code DataNode.id} for a fresh {@code
     * DatanodeRegistration} on every re-registration -- but matching an
     * object the workload never registered against the ones it did is a
     * tolerance for a second spelling of the source, and which predecessor
     * it lands on is decided by an equals() the engine does not own.  A
     * workload that replaces the object it handed over registers the
     * successor explicitly -- {@code registerSource} for the same logical
     * source, {@code restartSource} when the replacement IS a new lifecycle
     * epoch -- which is a statement rather than a guess.</p>
     */
    private static SourceRef resolveNamedAnchorLocked(Object anchor) {
        return SOURCE_ALIASES.get(anchor);
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
     * <p>A workload starts its cluster, names its sources, and then opens
     * the window over the thing being recorded.  Everything the process did
     * before the window is outside it: the recording never wrote a line for
     * it, so the plan counted none of it, and a replay that counts it is
     * numbering a different population than the plan numbered.</p>
     *
     * <p>{@code startRecording()} is that moment, and it is the same moment
     * in every replay of one recording because it is the workload that makes
     * it, not the engine.  "A source has been registered" was a second
     * implementation of the same notion: it coincided until a workload put a
     * cluster restart between its first registration and its
     * {@code startRecording()} -- hdfs-11741 does -- and then the replay
     * counted a whole NameNode generation the recording never saw.
     * Registration before the window is state, not the window.</p>
     */
    static boolean recordingWindowOpen() {
        return RecordingWindow.opened();
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
        // The explicit scope the creator stood in, read off its state (no
        // thread-local may be touched while a thread is being constructed).
        SourceRef creatorExplicit = null;
        for (ScopeFrame scope : parent.scopes) {
            if (scope.opened != null) {
                creatorExplicit = scope.opened;
                break;
            }
        }
        child.inheritedSource = creatorExplicit != null ? creatorExplicit
                : parent.inheritedSource;
        View inherited = parent.rawView();
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
                     long remoteParentSpanId,
                     SourceRef source, boolean receiverAttributed,
                     String requestKey, String requestApi,
                     String exchangeTransport, String exchangeCorrelationId,
                     String exchangeAttemptId, String exchangeHalf) {
            this.laneId = laneId;
            this.spanId = spanId;
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

        /** The same view speaking for a carried request scope. */
        private View withScope(SourceRef scopeSource, String scopeKey,
                               String scopeApi) {
            return new View(laneId, spanId, remoteParentSpanId,
                    scopeSource, receiverAttributed, scopeKey, scopeApi,
                    exchangeTransport, exchangeCorrelationId,
                    exchangeAttemptId, exchangeHalf);
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
        /** The explicit node this thread's creator stood in, or null. */
        private SourceRef inheritedSource;

        private State(long laneId) {
            this.laneId = laneId;
        }

        /**
         * The thread's view, its source by THE attribution rule, resolved
         * now ({@link Attribution}).
         */
        private View view() {
            Frame frame = frames.peek();
            return new View(
                    laneId, frame == null ? 0L : frame.spanId,
                    frame == null ? pendingRemoteParentSpanId
                            : frame.remoteParentSpanId,
                    Attribution.resolve(null),
                    frame != null && frame.receiverAttributed,
                    requestKey, requestApi, exchangeTransport,
                    exchangeCorrelationId, exchangeAttemptId, exchangeHalf);
        }

        /** The same view with no resolution: for a thread's construction. */
        private View rawView() {
            Frame frame = frames.peek();
            return new View(
                    laneId, frame == null ? 0L : frame.spanId,
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
        /** The lineage hop this root opened, or 0 when it opened none. */
        private long lineageToken;
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

        private Frame(long spanId,
                      long remoteParentSpanId, SourceRef previousSource,
                      SourceRef source, boolean receiverAttributed,
                      String previousRequestKey, String previousRequestApi,
                      String previousExchangeTransport,
                      String previousExchangeCorrelationId,
                      String previousExchangeAttemptId,
                      String previousExchangeHalf) {
            this.spanId = spanId;
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
        private final SourceRef source;
        private final String requestKey;
        private final String requestApi;
        private final String exchangeTransport;
        private final String exchangeCorrelationId;
        private final String exchangeAttemptId;
        private final String exchangeHalf;
        /** The lineage the submitting thread was inside, as a value. */
        private final Object lineage;

        private Seed(SourceRef source,
                     String requestKey, String requestApi,
                     String exchangeTransport, String exchangeCorrelationId,
                     String exchangeAttemptId, String exchangeHalf,
                     Object lineage) {
            this.lineage = lineage;
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
        /** The scope root this hop replaced, put back when it ends; -1 when it opened none. */
        private int scopeBaseBefore = -1;
        /** The lineage hop this scope opened, or 0 when it opened none. */
        private long lineageToken;
        /**
         * The node this scope names EXPLICITLY, or null: a request's source,
         * a carried scope's, a registered local owner's, a tick owner's, a
         * service-loop turn's ({@link Attribution}, rule 1).
         */
        private SourceRef opened;
        /** Whether this scope is a service-loop turn ({@link #beginWake}). */
        private boolean turn;
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

    /**
     * What one message states about the exchange it belongs to.
     *
     * <p>The header also names the SENDER's source, and it is deliberately
     * not kept: that is where the value came from, and execution context is
     * set by execution-scope events only.  It is still parsed, because a
     * header that cannot state it is malformed.</p>
     */
    private static final class MessageContext {
        private final long parentSpanId;
        private final String requestKey;
        private final String requestApi;

        private MessageContext(long parentSpanId, String requestKey,
                               String requestApi) {
            this.parentSpanId = parentSpanId;
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
                // Constructed to validate the header, not retained.
                new SourceRef(decoded(parts[3]), decoded(parts[4]),
                        decoded(parts[5]), epoch);
                String requestKey = decoded(parts[6]);
                String requestApi = decoded(parts[7]);
                if (requestKey.isEmpty() || requestApi.isEmpty()) {
                    throw new IllegalArgumentException();
                }
                return new MessageContext(parentSpan, requestKey,
                        requestApi);
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        "malformed trace context header");
            }
        }
    }

}
