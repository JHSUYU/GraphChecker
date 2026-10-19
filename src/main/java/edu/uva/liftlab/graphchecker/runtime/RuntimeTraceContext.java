package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.RuntimeRegionPlanner.UNREGISTERED_SOURCE;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Base64;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

final class RuntimeTraceContext {
    private static final Object LOCK = new Object();
    private static final AtomicLong IDS = new AtomicLong(1L);
    private static final WeakIdentityMap<SourceRef> SOURCE_ALIASES =
            new WeakIdentityMap<>();
    private static final Map<String, SourceRef> SOURCES_BY_KEY =
            new LinkedHashMap<>();
    private static final WeakIdentityMap<Seed> ASYNC_SEEDS =
            new WeakIdentityMap<>();
    private static final InheritableThreadLocal<State> CURRENT =
            new InheritedState<State>() {
                @Override
                protected State initialValue() {
                    return initialState();
                }

                @Override
                protected State inherit(State parent) {
                    return inheritedState(parent);
                }
            };

    private RuntimeTraceContext() {
    }

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
                            + nonNull(apiName));
        }
        return beginRequest(source, apiName);
    }

    static long beginRequest(SourceRef requestedSource, String apiName) {
        return beginRequest(requestedSource, apiName, false);
    }

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
        String normalizedApi = trimmed(apiName);
        if (normalizedApi.isEmpty()) normalizedApi = "request";
        ScopeFrame scope = new ScopeFrame(requestId, state);
        scope.lineageToken = ownRoot
                ? Lineage.pushCallRoot(source.key(), Role.CLIENT, normalizedApi)
                : Lineage.push(source.key(), Role.CLIENT, normalizedApi);
        String requestKey = source.key() + "/request/" + normalizedApi
                + "#" + Lineage.rootWindowIndex();
        scope.scopeBaseBefore = Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        standIn(state, scope, source, requestKey, normalizedApi);
        scope.request = state.flow;
        Identity.hopOpened(scope.lineageToken);
        publishCausalSource(state);
        return requestId;
    }

    private static void standIn(State state, ScopeFrame scope,
                                SourceRef source, String key, String api) {
        scope.opened = source;
        state.scopes.push(scope);
        state.source = source;
        state.flow = state.flow.withRequest(key, api);
        if (scope.activeFrame != null) scope.activeFrame.source = source;
    }

    static void endRequest(long requestId) {
        restoreScope(requestId);
    }

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

    static void captureAsync(Object carrier) {
        if (carrier == null) return;
        if (carrier instanceof Collection) {
            for (Object element : (Collection<?>) carrier) {
                captureAsync(element);
            }
            return;
        }
        State state = CURRENT.get();
        View view = state.view();
        Lineage.Carried lineage = Lineage.capture();
        synchronized (LOCK) {
            ASYNC_SEEDS.put(carrier, new Seed(
                    carriedIn(state), view.flow, lineage));
        }
    }

    static void claimCarried(Object carrier) {
        Seed seed = takeSeed(carrier);
        boolean flow = seed != null && !seed.flow.requestKey.isEmpty()
                && !seed.flow.requestApi.isEmpty();
        if (seed == null
                || seed.source == null && !flow && !seed.lineage.names()) {
            CARRIED.get().push(0L);
            return;
        }
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
        CARRIED.get().push(token);
        Identity.hopOpened(scope.lineageToken);
        publishCausalSource(state);
    }

    static void releaseCarried() {
        Deque<Long> carried = CARRIED.get();
        if (carried.isEmpty()) return;
        long token = carried.pop();
        if (token != 0L) restoreScope(token);
    }

    private static final ThreadLocal<Deque<Long>> CARRIED =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<Long>();
                }
            };

    static Set<String> clientNodes() {
        Set<String> clients = new TreeSet<String>();
        synchronized (LOCK) {
            for (SourceRef source : SOURCES_BY_KEY.values()) {
                if (CausynthTraceRecorder.WORKLOAD_KIND.equals(
                        source.kind())) {
                    clients.add(source.key());
                }
            }
        }
        return clients;
    }

    static SourceRef explicitSource() {
        return explicitIn(CURRENT.get());
    }

    private static SourceRef explicitIn(State state) {
        for (ScopeFrame scope : state.scopes) {
            if (scope.opened != null) return scope.opened;
        }
        return null;
    }

    private static SourceRef carriedIn(State state) {
        for (ScopeFrame scope : state.scopes) {
            if (scope.startup != null) return scope.startup;
            if (scope.opened != null) return scope.opened;
        }
        return null;
    }

    static SourceRef carriedNode() {
        return carriedIn(CURRENT.get());
    }

    static SourceRef inheritedSource() {
        return CURRENT.get().inheritedSource;
    }

    static long beginNodeStartup(SourceRef node) {
        if (node == null) return 0L;
        State state = CURRENT.get();
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        SourceRef canonical;
        synchronized (LOCK) {
            for (SourceRef registered : SOURCES_BY_KEY.values()) {
                if (registered.id().equals(node.id())
                        && registered.epoch() > node.epoch()) {
                    throw new IllegalArgumentException("a node startup names "
                            + node.key() + ", but " + registered.key()
                            + " is registered: a restarted node's startup"
                            + " is its live epoch's");
                }
            }
            canonical = canonicalSourceLocked(node);
        }
        scope.startup = canonical;
        scope.opened = canonical;
        state.scopes.push(scope);
        state.source = canonical;
        if (scope.activeFrame != null) scope.activeFrame.source = canonical;
        publishCausalSource(state);
        return token;
    }

    static void endNodeStartup(long token) {
        if (token > 0L) restoreScope(token);
    }

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

    static View enterRoot(Object receiver) {
        State state = CURRENT.get();
        SourceRef registered = sourceFor(receiver);
        boolean receiverAttributed = registered != null;
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
        Deque<ScopeFrame> outliving = new ArrayDeque<ScopeFrame>();
        for (ScopeFrame scope : state.scopes) {
            if (scope.request != null && scope.activeFrame == frame) {
                outliving.push(scope);
            }
        }
        if (outliving.isEmpty()) return;
        outliving.peek().outlive(frame.previousSource, frame.previousFlow);
        Frame parent = state.frames.peek();
        for (ScopeFrame scope : outliving) {
            scope.reframe(parent);
            state.source = scope.opened;
            state.flow = scope.request;
            if (parent != null) parent.source = scope.opened;
        }
    }

    static View current() {
        return CURRENT.get().view();
    }

    static SourceRef currentSource() {
        return CURRENT.get().view().source;
    }

    static Object captureScope() {
        View view = CURRENT.get().view();
        return new RequestScope(view.source, view.requestKey,
                view.requestApi, Lineage.capture());
    }

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
        String api = nonNull(apiName).isEmpty()
                ? scope.requestApi : nonNull(apiName);
        frame.lineageToken = Lineage.restore(scope.lineage,
                scope.source.key(), Role.of(roleName), api);
        frame.scopeBaseBefore = Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        Identity.hopOpened(frame.lineageToken);
        publishCausalSource(state);
        return token;
    }

    static void exitCarriedScope(long token) {
        if (token > 0L) restoreScope(token);
    }

    static long beginTick(Object owner, String roleName) {
        State state = CURRENT.get();
        SourceRef owned = sourceFor(owner);
        SourceRef source = owned != null ? owned : Attribution.resolve(null);
        int scopeBaseBefore = Identity.scopeStart(Identity.Hop.STARTED_ROOT);
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        scope.scopeBaseBefore = scopeBaseBefore;
        scope.opened = owned;
        scope.lineageToken = Lineage.pushRoot(
                source == null ? "" : source.key(), Role.of(roleName), "");
        state.scopes.push(scope);
        if (source != null
                && !UNREGISTERED_SOURCE.key().equals(source.key())) {
            String api = trimmed(roleName);
            if (api.isEmpty()) api = "tick";
            state.source = source;
            state.flow = state.flow.withRequest(source.key() + "/tick/"
                    + api + "#" + Lineage.quietly(Lineage::rootWindowIndex),
                    api);
        }
        final long hop = scope.lineageToken;
        final String site = "tick." + nonNull(roleName);
        scope.tick = Lineage.quietly(() -> ScheduleLog.turnBegun(site, hop));
        Identity.hopOpened(scope.lineageToken);
        return token;
    }

    static boolean vacantTick(long token) {
        ScopeFrame tick = standing(CURRENT.get(), token);
        return tick != null && ScheduleLog.vacant(tick.tick);
    }

    static void endTick(long token) {
        State state = CURRENT.get();
        ScopeFrame tick = standing(state, token);
        if (tick != null && ScheduleLog.turnEnded(tick.tick)) {
            closeInside(state, tick);
            ScheduleLog.observe(ScheduleEvent.Kind.END, tick.tick.site());
        }
        restoreScope(token);
    }

    static long beginWake(String api) {
        State state = CURRENT.get();
        for (ScopeFrame open : state.scopes) {
            if (!open.turn) return 0L;
        }
        SourceRef source = activationSource(null);
        if (UNREGISTERED_SOURCE.key().equals(source.key())) {
            return 0L;
        }
        String normalizedApi = trimmed(api);
        if (normalizedApi.isEmpty()) normalizedApi = "wake";
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        scope.turn = true;
        scope.lineageToken = Lineage.pushRoot(source.key(), Role.WAKE,
                normalizedApi);
        scope.scopeBaseBefore = Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        standIn(state, scope, source, source.key() + "/wake/"
                + normalizedApi + "#" + Lineage.quietly(
                        Lineage::rootWindowIndex), normalizedApi);
        Identity.hopOpened(scope.lineageToken);
        publishCausalSource(state);
        return token;
    }

    static boolean endWakeIfInnermost(long token) {
        State state = CURRENT.get();
        ScopeFrame turn = standing(state, token);
        if (turn == null) return true;
        if (state.scopes.peek() != turn) return false;
        restoreScope(token);
        return true;
    }

    static final class RequestScope {
        private final SourceRef source;
        private final String requestKey;
        private final String requestApi;
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

    static String outboundHeader(Object localOwner, Object carriedScope) {
        View view = leg(localOwner, carriedScope);
        if (view.source == null || view.requestKey.isEmpty()
                || view.requestApi.isEmpty()) {
            throw new IllegalStateException(
                    "outbound message requires source and request flow;"
                            + " the call carried " + describe(carriedScope)
                            + " and the thread it is sent on carries no"
                            + missing(owned(current(), localOwner)));
        }
        return header(view.source, view.requestKey, view.requestApi,
                view.spanId);
    }

    private static String header(SourceRef source, String requestKey,
                                 String requestApi, long spanId) {
        return "1|" + spanId + "|" + source.epoch()
                + "|" + encoded(source.kind())
                + "|" + encoded(source.role())
                + "|" + encoded(source.id())
                + "|" + encoded(requestKey)
                + "|" + encoded(requestApi);
    }

    static long enterInbound(String header, String transport,
                             String correlationId, String attemptId,
                             String half, Object localOwner, String via) {
        MessageContext remote = MessageContext.parse(header);
        State state = CURRENT.get();
        long token = nextId();
        ScopeFrame scope = new ScopeFrame(token, state);
        Frame activeFrame = scope.activeFrame;
        state.scopes.push(scope);
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
        scope.lineageToken = Lineage.push(
                state.source == null ? "" : state.source.key(),
                Role.of(state.flow.exchangeTransport),
                inboundFamily(remote.requestKey, remote.requestApi));
        scope.scopeBaseBefore = Identity.scopeStart(Identity.Hop.ANCHOR);
        String sender = Interactions.sender(state.flow.exchangeTransport,
                state.flow.exchangeCorrelationId, state.flow.exchangeHalf);
        String rpcSite = normalizedUpper(transport)
                + (trimmed(via).isEmpty() ? ""
                : "." + normalizedUpper(via)) + "/"
                + nonNull(remote.requestApi);
        Lineage.anchor(sender, rpcSite);
        if (sender.isEmpty()) unanchored(state, rpcSite);
        Identity.hopOpened(scope.lineageToken);
        publishCausalSource(state);
        return token;
    }

    private static void unanchored(State state, String rpcSite) {
        OccurrenceAddress here = RowRuntime.occurrenceHere(
                state.source == null ? "" : state.source.key(), rpcSite);
        RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                here == null ? rpcSite : here.render(),
                "the " + state.flow.exchangeTransport + " "
                        + state.flow.exchangeHalf + " received at " + rpcSite
                        + " names no sender this run holds ("
                        + Interactions.sendersEvicted() + " sent messages"
                        + " were evicted past the " + Interactions.LIMIT
                        + "-entry bound, or its sender filed none: work no"
                        + " hop named sends unanchored), so the"
                        + " work it opens is addressed under this thread's"
                        + " own context instead of an anchor");
    }

    private static String inboundFamily(String requestKey, String requestApi) {
        String key = trimmed(requestKey);
        int marker = key.lastIndexOf("/request/");
        if (marker <= 0) return trimmed(requestApi);
        String source = key.substring(0, marker);
        String api = key.substring(marker + "/request/".length());
        int ordinal = api.lastIndexOf('#');
        if (ordinal > 0) api = api.substring(0, ordinal);
        return source.isEmpty() || api.isEmpty()
                ? trimmed(requestApi) : source + "/" + api;
    }

    static void exitInbound(long token) {
        restoreScope(token);
    }

    static View exchange(Object localOwner, Object carriedScope) {
        View view = leg(localOwner, carriedScope);
        publishCausalSource(view);
        return view;
    }

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

    private static String missing(View view) {
        StringBuilder absent = new StringBuilder();
        if (view.source == null) absent.append(" source");
        if (view.requestKey.isEmpty()) absent.append(" requestKey");
        if (view.requestApi.isEmpty()) absent.append(" requestApi");
        return absent.length() == 0 ? "thing" : absent.toString();
    }

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

    private static View owned(View view, Object localOwner) {
        SourceRef source = sourceFor(localOwner);
        if (source == null) return view;
        return view.withScope(source, view.requestKey, view.requestApi);
    }

    static SourceRef ownedSource(Object localOwner) {
        SourceRef owned = sourceFor(localOwner);
        if (owned != null) return owned;
        return activationSource(null);
    }

    private static void restoreScope(long token) {
        State state = CURRENT.get();
        ScopeFrame scope = standing(state, token);
        if (scope == null) return;
        closeInside(state, scope);
        restoreOne(state, scope);
        publishCausalSource(state);
    }

    private static ScopeFrame standing(State state, long token) {
        for (ScopeFrame open : state.scopes) {
            if (open.token == token) return open;
        }
        return null;
    }

    private static void closeInside(State state, ScopeFrame scope) {
        while (state.scopes.peek() != null && state.scopes.peek() != scope) {
            restoreOne(state, state.scopes.peek());
        }
    }

    private static void restoreOne(State state, ScopeFrame scope) {
        state.scopes.pop();
        Identity.hopClosed(scope.lineageToken);
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
    }

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
        CARRIED.remove();
        IDS.set(1L);
        RecordingWindow.reset();
        RecordingWindow.open();
    }

    private static Seed takeSeed(Object carrier) {
        if (carrier == null) return null;
        synchronized (LOCK) {
            return ASYNC_SEEDS.remove(carrier);
        }
    }

    static SourceRef activationSource(Object receiver) {
        SourceRef source = Attribution.resolve(receiver);
        return source == null ? UNREGISTERED_SOURCE : source;
    }

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

    private static String describeAnchor(Object anchor) {
        if (anchor == null) return "null";
        return anchor.getClass().getName() + "@"
                + Integer.toHexString(System.identityHashCode(anchor));
    }

    static boolean declaresEpoch(String sourceKey) {
        String value = trimmed(sourceKey);
        return !value.isEmpty() && !sourceIdentity(value).equals(value);
    }

    static boolean sourceIdentityRegistered(String sourceKey) {
        if (sourceKey == null || sourceKey.isEmpty()) return false;
        synchronized (LOCK) {
            for (String registered : SOURCES_BY_KEY.keySet()) {
                if (sameSourceIdentity(sourceKey, registered)) return true;
            }
            return false;
        }
    }

    static boolean sameSourceIdentity(String left, String right) {
        String leftIdentity = sourceIdentity(left);
        return !leftIdentity.isEmpty()
                && leftIdentity.equals(sourceIdentity(right));
    }

    private static String sourceIdentity(String sourceKey) {
        String value = trimmed(sourceKey);
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
        SourceRef creator = carriedIn(parent);
        child.inheritedSource = creator != null ? creator
                : parent.inheritedSource;
        Frame frame = parent.frames.peek();
        child.source = frame == null ? parent.source : frame.source;
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
        final boolean receiverAttributed;
        final String requestKey;
        final String requestApi;
        final String exchangeAttemptId;
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
            this.exchangeAttemptId = flow.exchangeAttemptId;
        }

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
        private SourceRef inheritedSource;

        private State(long laneId) {
            this.laneId = laneId;
        }

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
        private final Lineage.Carried lineage;

        private Seed(SourceRef source, Flow flow, Lineage.Carried lineage) {
            this.lineage = lineage;
            this.source = source;
            this.flow = flow;
        }
    }

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
            this.requestKey = nonNull(requestKey);
            this.requestApi = nonNull(requestApi);
            this.exchangeTransport = normalizedUpper(exchangeTransport);
            this.exchangeCorrelationId = trimmed(exchangeCorrelationId);
            this.exchangeAttemptId = trimmed(exchangeAttemptId);
            this.exchangeHalf = normalizedUpper(exchangeHalf);
        }

        private Flow withRequest(String key, String api) {
            return new Flow(key, api, exchangeTransport,
                    exchangeCorrelationId, exchangeAttemptId, exchangeHalf);
        }
    }

    private static final class ScopeFrame {
        private final long token;
        private int scopeBaseBefore = -1;
        private long lineageToken;
        private SourceRef opened;
        private SourceRef startup;
        private boolean turn;
        private Flow request;
        private ScheduleLog.TurnWake tick;
        private SourceRef source;
        private Frame activeFrame;
        private SourceRef frameSource;
        private long frameRemoteParentSpanId;
        private final long remoteParentSpanId;
        private Flow flow;

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

        private void reframe(Frame parent) {
            activeFrame = parent;
            frameSource = parent == null ? null : parent.source;
            frameRemoteParentSpanId = parent == null ? 0L
                    : parent.remoteParentSpanId;
        }

        private void outlive(SourceRef before, Flow beforeFlow) {
            source = before;
            flow = beforeFlow;
        }
    }

    private static String normalizedUpper(String value) {
        return trimmed(value).toUpperCase(Locale.ROOT);
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
        private final String requestKey;
        private final String requestApi;

        private MessageContext(long parentSpanId, String requestKey,
                               String requestApi) {
            this.parentSpanId = parentSpanId;
            this.requestKey = requestKey;
            this.requestApi = requestApi;
        }

        private static MessageContext parse(String header) {
            String[] parts = nonNull(header).split("\\|", -1);
            try {
                if (parts.length != 8 || !"1".equals(parts[0])) {
                    throw new IllegalArgumentException();
                }
                long parentSpan = Long.parseLong(parts[1]);
                long epoch = Long.parseLong(parts[2]);
                if (parentSpan < 0L || epoch < 0L) {
                    throw new IllegalArgumentException();
                }
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
