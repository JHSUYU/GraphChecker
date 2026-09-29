package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.RuntimeRegionPlanner.UNREGISTERED_SOURCE;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Base64;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

/**
 * The running thread's causal context: the registered sources, the node the
 * thread works for ({@link Attribution}), and the request flow and exchange
 * leg it stands in, each set by a scope that puts back what it replaced.
 *
 * <p>Work queued for another thread carries its scope as a value
 * ({@link #captureAsync}, {@link #captureScope}): an
 * {@link InheritableThreadLocal} misses pool threads created earlier.</p>
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
            SOURCE_ALIASES.put(anchor, canonical);
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
                        "source anchor is not registered: "
                                + describeAnchor(anchor));
            }
            requireUnchangedAliasLocked(alias, source);
            SOURCE_ALIASES.put(alias, source);
            return source;
        }
    }

    /**
     * The source an explicitly named anchor is registered as, by object
     * identity only: the only attribution a replay reproduces.  A workload
     * that replaces the object registers the successor itself
     * ({@code registerSource} / {@code restartSource}).
     */
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
                    "request source alias is not registered: "
                            + describeAnchor(sourceAlias) + " for request "
                            + MapFields.safe(apiName));
        }
        return beginRequest(source, apiName);
    }

    static long beginRequest(SourceRef requestedSource, String apiName) {
        return beginRequest(requestedSource, apiName, false);
    }

    /**
     * @param ownRoot the request is a root of its own even inside another
     *                ({@link Lineage#pushCallRoot}); otherwise it roots the
     *                lineage only where none stands
     */
    static long beginRequest(SourceRef requestedSource, String apiName,
                             boolean ownRoot) {
        if (requestedSource == null) {
            throw new IllegalArgumentException("request source is required");
        }
        SourceRef source;
        synchronized (LOCK) {
            source = canonicalSourceLocked(requestedSource);
        }
        State state = CURRENT.get();
        long requestId = nextId();
        String normalizedApi = Text.safe(apiName);
        if (normalizedApi.isEmpty()) normalizedApi = "request";
        ScopeFrame scope = new ScopeFrame(requestId, state);
        // The workload's action roots this lineage.
        scope.lineageToken = ownRoot
                ? Lineage.pushCallRoot(source.key(), Role.CLIENT, normalizedApi)
                : Lineage.push(source.key(), Role.CLIENT, normalizedApi);
        // The key's ordinal is the lineage's k; it addresses nothing.
        String requestKey = source.key() + "/request/" + normalizedApi
                + "#" + Lineage.rootWindowIndex();
        // The index begins at the request; a start frame above it belongs
        // to the root that carried the thread here (Identity.Hop.SCOPE_ROOT).
        scope.scopeBaseBefore = Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        standIn(state, scope, source, requestKey, normalizedApi);
        publishCausalSource(state);
        return requestId;
    }

    /**
     * Stands the thread and its active frame in {@code scope}, which names
     * {@code source} and the request {@code key}/{@code api} explicitly.
     */
    private static void standIn(State state, ScopeFrame scope,
                                SourceRef source, String key, String api) {
        scope.opened = source;
        state.scopes.push(scope);
        state.source = source;
        state.flow = state.flow.withRequest(key, api);
        if (scope.activeFrame != null) scope.activeFrame.source = source;
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
            previous = SOURCE_ALIASES.get(anchor);
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
            SOURCE_ALIASES.put(anchor, next);
        }
        return next;
    }

    /** Captures the current source/span for a Thread, Runnable, or Callable. */
    static void captureAsync(Object carrier) {
        if (carrier == null) return;
        if (carrier instanceof Collection) {
            // A batch is one submission per task, so siblings stay distinct.
            for (Object element : (Collection<?>) carrier) {
                captureAsync(element);
            }
            return;
        }
        State state = CURRENT.get();
        View view = state.view();
        // Lineage and flow travel with the work, not the thread.  Only the
        // starter's EXPLICIT node is carried: a weaker one made explicit here
        // would outrank the work's own frames (Attribution, rule 3).
        Lineage.Carried lineage = Lineage.capture();
        synchronized (LOCK) {
            ASYNC_SEEDS.put(carrier, new Seed(
                    explicitSource(), view.flow, lineage));
        }
    }

    /**
     * Enters, on the claiming thread, the scope a start carried: the CLAIM
     * half of every handoff, in both passes; left by {@link #releaseCarried}.
     *
     * <p>No scope START here: the work's index begins at its start frame,
     * which tells siblings from one site apart.</p>
     */
    static void claimCarried(Object carrier) {
        Seed seed = takeSeed(carrier);
        if (seed == null) return;
        boolean flow = !seed.flow.requestKey.isEmpty()
                && !seed.flow.requestApi.isEmpty();
        if (seed.source == null && !flow && !seed.lineage.names()) return;
        releaseCarried();
        State state = CURRENT.get();
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        scope.opened = seed.source;
        scope.lineageToken = Lineage.restore(seed.lineage,
                seed.source == null ? "" : seed.source.key(),
                Role.EXECUTOR_TASK, "");
        state.scopes.push(scope);
        if (seed.source != null) state.source = seed.source;
        state.flow = seed.flow;
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

    /** Attribution rule 1: the innermost explicit scope's node, or null. */
    static SourceRef explicitSource() {
        return explicitIn(CURRENT.get());
    }

    /** Rule 1 read off one state, with no thread-local touched. */
    private static SourceRef explicitIn(State state) {
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
    static SourceRef firstRegistered(List<Object> objects) {
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
     * <p>Opens no execution-index SCOPE: this is the recorder's hook alone,
     * so a scope here would exist in the recording and not the replay.
     * Scopes open only where the workload says one begins; pool threads are
     * handled by {@link Identity#startWork}'s start frame.</p>
     */
    static View enterRoot(Object receiver) {
        State state = CURRENT.get();
        SourceRef registered = sourceFor(receiver);
        // Which authority named it: replay reproduces a registration by
        // identity, an inherited context only by thread context.
        boolean receiverAttributed = registered != null;
        // The same rule the replay evaluates at this entry.
        SourceRef source = Attribution.resolve(receiver);
        if (state.laneId == 0L) {
            state.laneId = nextId();
        }
        long spanId = nextId();
        long remoteParentSpanId = state.pendingRemoteParentSpanId;
        Frame frame = new Frame(spanId, remoteParentSpanId,
                state.source, source, receiverAttributed, state.flow);
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
        state.source = frame.previousSource;
        state.flow = frame.previousFlow;
    }

    static View current() {
        return CURRENT.get().view();
    }

    static SourceRef currentSource() {
        return CURRENT.get().view().source;
    }

    /**
     * The calling thread's request scope, as a value to carry with work: a
     * scope belongs to the work, not the thread.
     */
    static Object captureScope() {
        View view = CURRENT.get().view();
        return new RequestScope(view.source, view.requestKey,
                view.requestApi, Lineage.capture());
    }

    /**
     * Enters a scope captured where the work was created: the dequeue half
     * of a queue that outlives its enqueueing thread ({@link #captureScope}).
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
        long token = nextId();
        ScopeFrame frame = new ScopeFrame(token, state);
        standIn(state, frame, scope.source, scope.requestKey,
                scope.requestApi);
        String api = MapFields.safe(apiName).isEmpty()
                ? scope.requestApi : MapFields.safe(apiName);
        frame.lineageToken = Lineage.restore(scope.lineage,
                scope.source.key(), Role.of(roleName), api);
        // The carried scope is the work's, not the pool thread's.
        frame.scopeBaseBefore = Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        publishCausalSource(state);
        return token;
    }

    /** Leaves the scope {@link #enterCarriedScope} entered. */
    static void exitCarriedScope(long token) {
        if (token > 0L) restoreScope(token);
    }

    /**
     * Opens one daemon tick as a lineage root (role plus a window-local k):
     * a timer thread serves no request, so the tick is its own root.
     *
     * @return the token that closes the tick
     */
    static long beginTick(Object owner, String roleName) {
        State state = CURRENT.get();
        // A registered owner is an explicit scope (Attribution, rule 1).
        SourceRef owned = sourceFor(owner);
        SourceRef source = owned != null ? owned : Attribution.resolve(null);
        // The tick IS the started work: index begins at its start frame.
        int scopeBaseBefore = Identity.scopeStart(Identity.Hop.STARTED_ROOT);
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        scope.scopeBaseBefore = scopeBaseBefore;
        scope.opened = owned;
        // Always a ROOT hop: a nested one would inherit whatever request
        // the thread stands in (Lineage#pushRoot).
        scope.lineageToken = Lineage.pushRoot(
                source == null ? "" : source.key(), Role.of(roleName), "");
        state.scopes.push(scope);
        // Like a service-loop turn it carries a request flow, so what it
        // sends reaches its server anchored rather than Lost.
        if (source != null
                && !UNREGISTERED_SOURCE.key().equals(source.key())) {
            String api = Text.safe(roleName);
            if (api.isEmpty()) api = "tick";
            state.source = source;
            state.flow = state.flow.withRequest(source.key() + "/tick/"
                    + api + "#" + Lineage.rootWindowIndex(), api);
        }
        // A tick is a WAKE.  Only a turn whose WAKE was written states its
        // END, so no END is left without a WAKE across the window opening.
        String site = "tick." + MapFields.safe(roleName);
        if (ScheduleLog.observe(ScheduleEvent.Kind.WAKE, site)) {
            scope.tickSite = site;
        }
        return token;
    }

    /**
     * Closes the tick {@link #beginTick} opened and states its END, which
     * orders the turn's writes before their readers
     * ({@code ScheduleEvent.Kind.END}).
     */
    static void endTick(long token) {
        State state = CURRENT.get();
        ScopeFrame tick = standing(state, token);
        if (tick != null && tick.tickSite != null) {
            // Inner scopes close first, so END stands in the turn's context.
            closeInside(state, tick);
            ScheduleLog.observe(ScheduleEvent.Kind.END, tick.tickSite);
        }
        restoreScope(token);
    }

    /**
     * Opens one turn of a service loop as a root scope ({@code WakeScopes},
     * {@link Lineage#pushRoot}); k is the turn's ordinal on this node in the
     * window.  It carries a request flow so what it sends is not
     * {@code Lost}.
     *
     * @return the token that closes the turn, or 0 when the thread belongs to
     *         no node the run can name and nothing was opened
     */
    static long beginWake(String api) {
        // A timed wait inside non-turn work is a pause within it, not a
        // daemon's next turn.
        State state = CURRENT.get();
        for (ScopeFrame open : state.scopes) {
            if (!open.turn) return 0L;
        }
        SourceRef source = activationSource(null);
        if (UNREGISTERED_SOURCE.key().equals(source.key())) {
            return 0L;
        }
        String normalizedApi = Text.safe(api);
        if (normalizedApi.isEmpty()) normalizedApi = "wake";
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        scope.turn = true;
        scope.lineageToken = Lineage.pushRoot(source.key(), Role.of("WAKE"),
                normalizedApi);
        scope.scopeBaseBefore = Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        standIn(state, scope, source, source.key() + "/wake/"
                + normalizedApi + "#" + Lineage.rootWindowIndex(),
                normalizedApi);
        publishCausalSource(state);
        return token;
    }

    /**
     * Closes the turn {@code token} opened only when it is innermost (scope
     * closes are LIFO), and says whether it did.
     */
    static boolean endWakeIfInnermost(long token) {
        State state = CURRENT.get();
        ScopeFrame turn = standing(state, token);
        if (turn == null) return true;
        if (state.scopes.peek() != turn) return false;
        restoreScope(token);
        return true;
    }

    /** One captured request scope; opaque to its carrier. */
    static final class RequestScope {
        private final SourceRef source;
        private final String requestKey;
        private final String requestApi;
        /** The lineage the work was created inside, as a value. */
        private final Lineage.Carried lineage;

        private RequestScope(SourceRef source, String requestKey,
                             String requestApi, Lineage.Carried lineage) {
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

    /**
     * Encodes the current node and request flow for the next message; a
     * carried scope wins when it names one, else the thread's answers.
     */
    static String outboundHeader(Object localOwner, Object carriedScope) {
        View view = leg(localOwner, carriedScope);
        if (view.source == null || view.requestKey.isEmpty()
                || view.requestApi.isEmpty()) {
            // Name what was missing, carried scope and thread separately:
            // they have different owners.  Never name the thread; the row
            // must compare across replays.
            throw new IllegalStateException(
                    "outbound message requires source and request flow;"
                            + " the call carried " + describe(carriedScope)
                            + " and the thread it is sent on carries no"
                            + missing(owned(current(), localOwner)));
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
    /**
     * @param via the receiving side's own name for where the message arrived
     *            (a store notification's watcher), "" for none: part of the
     *            context the work it opens is addressed by, never of the
     *            pairing with its sender
     */
    static long enterInbound(String header, String transport,
                             String correlationId, String attemptId,
                             String half, Object localOwner, String via) {
        MessageContext remote = MessageContext.parse(header);
        State state = CURRENT.get();
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        Frame activeFrame = scope.activeFrame;
        state.scopes.push(scope);
        // Execution context comes from execution-scope events only; the
        // SENDER's source is provenance and must not become the receiver's
        // context (it would differ between record and replay).  A registered
        // local owner is this scope's explicit node (Attribution, rule 1).
        SourceRef localSource = sourceFor(localOwner);
        scope.opened = localSource;
        if (localSource != null) {
            state.source = localSource;
        }
        state.pendingRemoteParentSpanId = remote.parentSpanId;
        state.flow = new Flow(remote.requestKey, remote.requestApi,
                transport, correlationId, attemptId, half);
        if (activeFrame != null) {
            activeFrame.source = state.source;
            activeFrame.remoteParentSpanId = remote.parentSpanId;
        }
        // The served hop: role = the transport the workload named (no
        // engine-side role table), api = the remote family, so two callers
        // of one api count separately.
        scope.lineageToken = Lineage.push(
                state.source == null ? "" : state.source.key(),
                Role.of(state.flow.exchangeTransport),
                inboundFamily(remote.requestKey, remote.requestApi));
        // The index begins at the inbound scope; the handler frames above
        // it are scheduling (Identity.Hop.ANCHOR).
        scope.scopeBaseBefore = Identity.scopeStart(Identity.Hop.ANCHOR);
        // The producer endpoint IS the causal context (IDENTITY-V3).
        Lineage.anchor(Interactions.sender(state.flow.exchangeTransport,
                                state.flow.exchangeCorrelationId,
                                state.flow.exchangeHalf),
                // Api is the last segment (ComposeMain.apiOf).
                normalizedUpper(transport)
                        + (Text.safe(via).isEmpty() ? ""
                        : "." + normalizedUpper(via)) + "/"
                        + MapFields.safe(remote.requestApi));
        publishCausalSource(state);
        return token;
    }

    /**
     * The served hop's api: {@code <source>/<api>} of the request in force,
     * else the bare api.  The request key's ordinal is dropped: a replay
     * cannot be held to it.
     */
    private static String inboundFamily(String requestKey, String requestApi) {
        String key = Text.safe(requestKey);
        int marker = key.lastIndexOf("/request/");
        if (marker <= 0) return Text.safe(requestApi);
        String source = key.substring(0, marker);
        String api = key.substring(marker + "/request/".length());
        int ordinal = api.lastIndexOf('#');
        if (ordinal > 0) api = api.substring(0, ordinal);
        return source.isEmpty() || api.isEmpty()
                ? Text.safe(requestApi) : source + "/" + api;
    }

    static void exitInbound(long token) {
        restoreScope(token);
    }

    /** The exchange leg's view ({@link #leg}), handed to the occurrence. */
    static View exchange(Object localOwner, Object carriedScope) {
        View view = leg(localOwner, carriedScope);
        publishCausalSource(view);
        return view;
    }

    /**
     * The view of one exchange leg: under the carried scope when it names
     * one, so row and wire header agree whatever thread writes.
     */
    private static View leg(Object localOwner, Object carriedScope) {
        View view = owned(current(), localOwner);
        if (!(carriedScope instanceof RequestScope)
                || !((RequestScope) carriedScope).names()) {
            return view;
        }
        RequestScope scope = (RequestScope) carriedScope;
        return view.withScope(scope.source, scope.requestKey,
                scope.requestApi);
    }

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

    /**
     * The view of one exchange leg made on behalf of a registered local
     * owner: that owner's node, for this leg only; never bound to the thread.
     */
    private static View owned(View view, Object localOwner) {
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
        ScopeFrame scope = standing(state, token);
        // Already closed by an outer close: a no-op, never a throw.
        if (scope == null) return;
        closeInside(state, scope);
        restoreOne(state, scope);
        publishCausalSource(state);
    }

    /** The scope {@code token} opened, while it stands; else null. */
    private static ScopeFrame standing(State state, long token) {
        for (ScopeFrame open : state.scopes) {
            if (open.token == token) return open;
        }
        return null;
    }

    /** Closes every scope inside {@code scope}, innermost first. */
    private static void closeInside(State state, ScopeFrame scope) {
        while (state.scopes.peek() != null && state.scopes.peek() != scope) {
            restoreOne(state, state.scopes.peek());
        }
    }

    /** Closes the innermost scope and puts back what it replaced. */
    private static void restoreOne(State state, ScopeFrame scope) {
        state.scopes.pop();
        if (scope.lineageToken > 0L) Lineage.release(scope.lineageToken);
        if (scope.scopeBaseBefore >= 0) {
            Identity.scopeRestore(scope.scopeBaseBefore);
        }
        state.source = scope.source;
        state.flow = scope.flow;
        state.pendingRemoteParentSpanId = scope.remoteParentSpanId;
        if (scope.activeFrame != null
                && state.frames.peek() == scope.activeFrame) {
            scope.activeFrame.source = scope.frameSource;
            scope.activeFrame.remoteParentSpanId = scope.frameRemoteParentSpanId;
        }
        if (CARRIED.get() != null && CARRIED.get() == scope.token) {
            CARRIED.remove();
        }
    }

    /** Hands the thread's new source to the occurrence running on it. */
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
        // A fixture models an open recording window.
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
     * The source one root activation is attributed to: where it RAN, by
     * execution scope only.  Never null.
     *
     * <p>The planner's rule ({@link #attributedActivationSource}) with the
     * stamp computed live and no frame stamps yet, as at a root entry; one
     * function for recorder, planner and replay, since a replay-only variant
     * miscounts occurrences per node.  Trap: never fall back to the PLANNED
     * node; unstamped activations belong to the unregistered
     * population.</p>
     */
    static SourceRef activationSource(Object receiver) {
        return attributedActivationSource(Attribution.resolve(receiver),
                Collections.<SourceRef>emptyList());
    }

    /**
     * One activation's source: its own stamp, else the unique stamp among
     * its frames (in recorded order), else the unregistered source.  Never
     * null.  Disagreeing frames are a named gap (contradictory, not missing,
     * evidence).
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
                    RowRuntime.gap(GapKind.LINEAGE_LOST,
                            GapClass.DIAGNOSTIC,
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
        return activationSource(null).key();
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

    /** Names an anchor a caller passed, without calling its toString(). */
    private static String describeAnchor(Object anchor) {
        if (anchor == null) return "null";
        return anchor.getClass().getName() + "@"
                + Integer.toHexString(System.identityHashCode(anchor));
    }

    /** Whether {@code sourceKey} names an epoch of its node at all. */
    static boolean declaresEpoch(String sourceKey) {
        String value = Text.safe(sourceKey);
        return !value.isEmpty() && !sourceIdentity(value).equals(value);
    }

    /** Whether this run registered the same logical source as {@code sourceKey}. */
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
        String value = Text.safe(sourceKey);
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
        // Read off parent state: no thread-local during construction.
        SourceRef creatorExplicit = explicitIn(parent);
        child.inheritedSource = creatorExplicit != null ? creatorExplicit
                : parent.inheritedSource;
        // Unresolved: resolving would touch the child's thread-locals.
        Frame frame = parent.frames.peek();
        child.source = frame == null ? parent.source : frame.source;
        // A pool's worker works for its node, in no request of its own.
        if (!PoolWorkers.constructing()) child.flow = parent.flow;
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
        /** Whether {@link #source} is the receiver's own registration. */
        final boolean receiverAttributed;
        final String requestKey;
        final String requestApi;
        final String exchangeCorrelationId;
        final String exchangeAttemptId;
        /** The request flow this view states. */
        private final Flow flow;

        private View(long laneId, long spanId,
                     long remoteParentSpanId,
                     SourceRef source, boolean receiverAttributed,
                     Flow flow) {
            this.laneId = laneId;
            this.spanId = spanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.source = source;
            this.receiverAttributed = receiverAttributed;
            this.flow = flow;
            this.requestKey = flow.requestKey;
            this.requestApi = flow.requestApi;
            this.exchangeCorrelationId = flow.exchangeCorrelationId;
            this.exchangeAttemptId = flow.exchangeAttemptId;
        }

        /** The same view speaking for a carried request scope. */
        private View withScope(SourceRef scopeSource, String scopeKey,
                               String scopeApi) {
            return new View(laneId, spanId, remoteParentSpanId,
                    scopeSource, receiverAttributed,
                    flow.withRequest(scopeKey, scopeApi));
        }
    }

    private static final class State {
        private long laneId;
        private SourceRef source;
        private long pendingRemoteParentSpanId;
        private Flow flow = Flow.NONE;
        private final Deque<Frame> frames = new ArrayDeque<>();
        private final Deque<ScopeFrame> scopes = new ArrayDeque<>();
        /** The explicit node this thread's creator stood in, or null. */
        private SourceRef inheritedSource;

        private State(long laneId) {
            this.laneId = laneId;
        }

        /** The thread's view, source resolved now ({@link Attribution}). */
        private View view() {
            Frame frame = frames.peek();
            return new View(
                    laneId, frame == null ? 0L : frame.spanId,
                    frame == null ? pendingRemoteParentSpanId
                            : frame.remoteParentSpanId,
                    Attribution.resolve(null),
                    frame != null && frame.receiverAttributed, flow);
        }
    }

    private static final class Frame {
        private final long spanId;
        private long remoteParentSpanId;
        private final SourceRef previousSource;
        private SourceRef source;
        private final boolean receiverAttributed;
        private final Flow previousFlow;

        private Frame(long spanId,
                      long remoteParentSpanId, SourceRef previousSource,
                      SourceRef source, boolean receiverAttributed,
                      Flow previousFlow) {
            this.spanId = spanId;
            this.remoteParentSpanId = remoteParentSpanId;
            this.previousSource = previousSource;
            this.source = source;
            this.receiverAttributed = receiverAttributed;
            this.previousFlow = previousFlow;
        }
    }

    private static final class Seed {
        private final SourceRef source;
        private final Flow flow;
        /** The lineage the submitting thread was inside, as a value. */
        private final Lineage.Carried lineage;

        private Seed(SourceRef source, Flow flow, Lineage.Carried lineage) {
            this.lineage = lineage;
            this.source = source;
            this.flow = flow;
        }
    }

    /**
     * The request flow a thread carries (request key/api plus the inbound
     * exchange), normalized once and saved/restored as one value.
     */
    private static final class Flow {
        static final Flow NONE = new Flow("", "", "", "", "", "");
        private final String requestKey;
        private final String requestApi;
        private final String exchangeTransport;
        private final String exchangeCorrelationId;
        private final String exchangeAttemptId;
        private final String exchangeHalf;

        private Flow(String requestKey, String requestApi,
                     String exchangeTransport, String exchangeCorrelationId,
                     String exchangeAttemptId, String exchangeHalf) {
            this.requestKey = MapFields.safe(requestKey);
            this.requestApi = MapFields.safe(requestApi);
            this.exchangeTransport = normalizedUpper(exchangeTransport);
            this.exchangeCorrelationId = Text.safe(exchangeCorrelationId);
            this.exchangeAttemptId = Text.safe(exchangeAttemptId);
            this.exchangeHalf = normalizedUpper(exchangeHalf);
        }

        /** The same exchange under another request. */
        private Flow withRequest(String key, String api) {
            return new Flow(key, api, exchangeTransport,
                    exchangeCorrelationId, exchangeAttemptId, exchangeHalf);
        }
    }

    private static final class ScopeFrame {
        private final long token;
        /** The scope root this hop replaced, put back when it ends; -1 when it opened none. */
        private int scopeBaseBefore = -1;
        /** The lineage hop this scope opened, or 0 when it opened none. */
        private long lineageToken;
        /** The node this scope names EXPLICITLY, or null ({@link Attribution}, rule 1). */
        private SourceRef opened;
        /** Whether this scope is a service-loop turn ({@link #beginWake}). */
        private boolean turn;
        /** The tick's site when its WAKE was written, else null. */
        private String tickSite;
        private final SourceRef source;
        private final Frame activeFrame;
        private final SourceRef frameSource;
        private final long frameRemoteParentSpanId;
        private final long remoteParentSpanId;
        /** The request flow this scope replaced, put back when it ends. */
        private final Flow flow;

        /** Opens over {@code state} as it stands, active frame included. */
        private ScopeFrame(long token, State state) {
            this.token = token;
            this.source = state.source;
            Frame activeFrame = state.frames.peek();
            this.activeFrame = activeFrame;
            this.frameSource = activeFrame == null ? null : activeFrame.source;
            this.frameRemoteParentSpanId = activeFrame == null ? 0L
                    : activeFrame.remoteParentSpanId;
            this.remoteParentSpanId = state.pendingRemoteParentSpanId;
            this.flow = state.flow;
        }
    }

    private static String normalizedUpper(String value) {
        return Text.safe(value).toUpperCase(Locale.ROOT);
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
     * What one message states about its exchange.  The sender's source is
     * validated but not kept: it is provenance, not execution context.
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
