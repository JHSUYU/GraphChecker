package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.LibraryCatalog;
import edu.uva.liftlab.graphchecker.contract.ActivationRow.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.lang.ref.WeakReference;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.LinkedTransferQueue;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class Identity {
    private static final ThreadLocal<State> CURRENT =
            new InheritedState<State>() {
                @Override
                protected State initialValue() {
                    return new State();
                }

                @Override
                protected State inherit(State parent) {
                    return parent == null || PoolWorkers.constructing()
                            ? new State() : parent.copy();
                }
            };

    private static final AtomicLong TOKENS = new AtomicLong(1L);

    private static final Set<String> SERVING = ConcurrentHashMap.newKeySet();

    private Identity() {
    }

    private static final class State {
        private final List<Level> levels = new ArrayList<Level>();
        private boolean claimed;
        private int scopeBase;
        private final Deque<Claim> starts = new ArrayDeque<Claim>();
        private long claimSerial;
        private final Deque<ClaimScope> claimScopes =
                new ArrayDeque<ClaimScope>();
        private boolean unnamedThread;
        private int unnamedAt = -1;
        private final List<Region> regions = new ArrayList<Region>();
        private Attribution.Reference starter;
        private boolean adopted;
        private Object work;
        private String requestVerb = "";

        private State() {
            levels.add(new Level(null, 0L, null));
        }

        private int depth() {
            return levels.size() - 1;
        }

        private Frame frame(int index) {
            return levels.get(index + 1).frame;
        }

        private Frame addressedFrame(int index) {
            return levels.get(index + 1).addressed();
        }

        private Level top() {
            return levels.get(levels.size() - 1);
        }

        private State copy() {
            State child = new State();
            for (int index = 1; index < levels.size(); index++) {
                child.levels.add(new Level(levels.get(index).frame,
                        levels.get(index).token,
                        levels.get(index).receiver,
                        levels.get(index).window));
            }
            child.scopeBase = scopeBase;
            child.starter = Attribution.Reference.of(receiversOf(this),
                    starter);
            for (Region region : regions) {
                child.regions.add(new Region(region.base));
            }
            return child;
        }

        private void openStart(Start start, boolean own, boolean ranHere,
                               ClaimKind kind) {
            boolean consumed = !own && !ranHere;
            if (consumed && start.thread.get() != Thread.currentThread()) {
                serves();
            }
            Claim held = starts.peek();
            if (held != null && held.scope == claimScope()
                    && onlyStartsFrom(held.depth)) {
                while (depth() > held.depth) levels.remove(depth());
                closeStartsFrom(held.depth);
            }
            starts.push(new Claim(depth(), start.key, own, consumed,
                    own ? ClaimKind.NONE : kind, claimScope(), claimSerial++));
            for (Frame frame : own || ranHere
                    ? Collections.singletonList(start.frame())
                    : start.frames) {
                levels.add(new Level(frame, 0L, null, start.window));
            }
        }

        private long claimScope() {
            return claimScopes.isEmpty() ? 0L : claimScopes.peek().id;
        }

        private boolean onlyStartsFrom(int from) {
            for (int index = from; index < depth(); index++) {
                if (levels.get(index + 1).token != 0L) return false;
            }
            return true;
        }

        private int ownStart() {
            for (Claim claim : starts) {
                if (claim.own) return claim.depth;
            }
            return -1;
        }

        private int consumedStart() {
            int outermost = -1;
            for (Claim claim : starts) {
                if (claim.consumed) outermost = claim.depth;
            }
            return outermost;
        }

        private int innermostStart() {
            return starts.isEmpty() ? -1 : starts.peek().depth;
        }

        private void serves() {
            for (Claim standing : starts) {
                if (standing.kind == ClaimKind.HANDOFF_TASK) {
                    SERVING.add(standing.start);
                }
            }
        }

        private void standApart() {
            scopeBase = starts.peek().depth;
            Region apart = new Region(scopeBase);
            apart.apart = true;
            regions.add(apart);
        }

        private void claimUnnamed(boolean thread) {
            if (thread) {
                unnamedThread = true;
            } else {
                unnamedAt = depth();
            }
        }

        private void endUnnamedWork() {
            if (unnamedAt >= 0 && onlyStartsFrom(unnamedAt)) unnamedAt = -1;
        }

        private boolean unnamed() {
            return (unnamedThread || unnamedAt >= 0) && !Lineage.named();
        }

        private void closeStartsFrom(int depth) {
            while (!starts.isEmpty() && starts.peek().depth >= depth) {
                starts.pop();
                RuntimeTraceContext.releaseCarried();
            }
        }

        private int regionBase() {
            return regions.isEmpty() ? scopeBase
                    : regions.get(regions.size() - 1).base;
        }

        private Region region() {
            return regions.isEmpty() ? null
                    : regions.get(regions.size() - 1);
        }

        private Region activeRegion() {
            for (int index = regions.size() - 1; index >= 0; index--) {
                Region open = regions.get(index);
                if (open.occurrence != null) return open;
                if (open.apart) return null;
            }
            return null;
        }

        private void journal() {
            boolean journalled = false;
            for (int index = 0; index < regions.size(); index++) {
                if (regions.get(index).journal != null) journalled = true;
            }
            if (!journalled) return;
            long now = CLOCK.now();
            if (now < 0L) return;
            for (int index = 0; index < regions.size(); index++) {
                Region region = regions.get(index);
                if (region.journal == null) continue;
                region.journal.note(now, snapshot(region.base));
            }
        }

        private Frame[] snapshot(int base) {
            int start = Math.max(0, Math.min(base, depth()));
            Frame[] standing = new Frame[depth() - start];
            for (int index = start; index < depth(); index++) {
                standing[index - start] = addressedFrame(index);
            }
            return standing;
        }

        private int nextSiteEvent(String site) {
            return nextSiteEvent(site, RecordingWindow.index());
        }

        private int nextSiteEvent(String site, int window) {
            return next(top().events(countingRoot(), window), site);
        }

        private Frame requestFrame(String site, int attempt, int window) {
            if (attempt <= 0) {
                return Frame.of(site, nextSiteEvent(site, window));
            }
            String retry = site + "#retry" + attempt;
            Integer made = top().events(countingRoot(), window).get(site);
            return made == null ? Frame.of(retry, nextSiteEvent(retry, window))
                    : Frame.of(retry, made - 1);
        }

        private long countingRoot() {
            Region running = activeRegion();
            return running != null ? running.root : Lineage.rootToken();
        }

        private int nextStartEvent(String site, int window) {
            return next(top().startEvents(Lineage.contextToken(), window),
                    site);
        }

        private static int next(Map<String, Integer> events, String site) {
            Integer made = events.get(site);
            int iteration = made == null ? 0 : made;
            events.put(site, iteration + 1);
            return iteration;
        }

        private ExecutionIndex from(int base) {
            return ExecutionIndex.of(Arrays.asList(snapshot(base)));
        }
    }

    private static final class Level {
        private final Frame frame;
        private final long token;
        private final Object receiver;
        private final List<Counters> counters = new ArrayList<Counters>();
        private final List<Counters> startCounters = new ArrayList<Counters>();

        private final int window;

        private Level(Frame frame, long token, Object receiver) {
            this(frame, token, receiver, RecordingWindow.index());
        }

        private Level(Frame frame, long token, Object receiver, int window) {
            this.frame = frame;
            this.token = token;
            this.receiver = receiver;
            this.window = window;
        }

        private Frame addressed() {
            if (frame == null || window == RecordingWindow.index()
                    || frame.iteration() == 0) {
                return frame;
            }
            return Frame.of(frame.callSite(), 0);
        }

        private Map<String, Integer> events(long rootToken, int window) {
            return counts(counters, rootToken, window);
        }

        private Map<String, Integer> startEvents(long hop, int window) {
            return counts(startCounters, hop, window);
        }

        private static Map<String, Integer> counts(List<Counters> filedHops,
                                                   long hop, int window) {
            for (int index = filedHops.size() - 1; index >= 0; index--) {
                Counters filed = filedHops.get(index);
                if (filed.rootToken == hop) {
                    while (filedHops.size() > index + 1) {
                        filedHops.remove(filedHops.size() - 1);
                    }
                    if (filed.window != window) {
                        filed = filed.reopened(window);
                        filedHops.set(index, filed);
                    }
                    return filed.events;
                }
                if (Lineage.isOpen(filed.rootToken)) break;
                filedHops.remove(index);
            }
            Counters opened = new Counters(hop, window);
            filedHops.add(opened);
            return opened.events;
        }
    }

    private static final class Counters {
        private final long rootToken;
        private final int window;
        private final Map<String, Integer> events =
                new HashMap<String, Integer>();

        private Counters(long rootToken, int window) {
            this.rootToken = rootToken;
            this.window = window;
        }

        private Counters reopened(int window) {
            Counters counted = new Counters(rootToken, window);
            for (String site : events.keySet()) {
                counted.events.put(site, 1);
            }
            return counted;
        }
    }

    private static final WeakIdentityMap<Start> STARTS =
            new WeakIdentityMap<Start>();

    private static final WeakIdentityMap<WeakIdentityMap<Filed>> QUEUED =
            new WeakIdentityMap<WeakIdentityMap<Filed>>();

    private static final int FILED_PER_ITEM = 256;

    private static final class Filed {
        private final boolean fifo;
        private final ArrayDeque<Start> starts = new ArrayDeque<Start>();

        private Filed(boolean fifo) {
            this.fifo = fifo;
        }

        private synchronized void file(Start start) {
            if (!fifo) {
                if (start == Start.UNNAMED && !starts.isEmpty()) return;
                starts.clear();
            } else if (starts.size() >= FILED_PER_ITEM) {
                starts.pollFirst();
            }
            starts.addLast(start);
        }

        private synchronized Start take() {
            return starts.pollFirst();
        }
    }

    private static final class Start {
        private static final Start UNNAMED = new Start(
                Collections.<Frame>emptyList(), null, "", null, null, 0, 0,
                false);
        private final List<Frame> frames;
        private final Attribution.Reference starter;
        private final String key;
        private final int window;
        private final WeakReference<Thread> thread;
        private final WeakReference<Level> level;
        private final int depth;
        private final boolean handoff;
        private final AtomicBoolean adopted = new AtomicBoolean();

        private Start(List<Frame> frames, Attribution.Reference starter,
                      String key, Thread thread, Level level, int depth,
                      int window, boolean handoff) {
            this.frames = frames;
            this.starter = starter;
            this.key = key;
            this.thread = new WeakReference<Thread>(thread);
            this.level = new WeakReference<Level>(level);
            this.depth = depth;
            this.window = window;
            this.handoff = handoff;
        }

        private Frame frame() {
            return frames.get(frames.size() - 1);
        }

        private boolean adopt() {
            return this == UNNAMED || adopted.compareAndSet(false, true);
        }

        private boolean ranHere(State state) {
            Level standing = level.get();
            return thread.get() == Thread.currentThread() && standing != null
                    && depth <= state.depth()
                    && state.levels.get(depth) == standing;
        }
    }

    private static final class Claim {
        private final int depth;
        private final String start;
        private final boolean own;
        private final boolean consumed;
        private final ClaimKind kind;
        private final long scope;
        private final long serial;

        private Claim(int depth, String start, boolean own, boolean consumed,
                      ClaimKind kind, long scope, long serial) {
            this.depth = depth;
            this.start = start;
            this.own = own;
            this.consumed = consumed;
            this.kind = kind;
            this.scope = scope;
            this.serial = serial;
        }
    }

    private static final class ClaimScope {
        private final long id = TOKENS.getAndIncrement();
        private final long serial;
        private final Object work;
        private final Attribution.Reference starter;
        private final boolean adopted;
        private final int unnamedAt;
        private final boolean continuation;
        private final int regions;
        private final int scopeBase;
        private final String requestVerb;
        private MessageDoors.Inbound inbound;
        private boolean aside;
        private boolean apart;

        private ClaimScope(State state, boolean continuation) {
            this.serial = state.claimSerial;
            this.work = state.work;
            this.starter = state.starter;
            this.adopted = state.adopted;
            this.unnamedAt = state.unnamedAt;
            this.continuation = continuation;
            this.regions = state.regions.size();
            this.scopeBase = state.scopeBase;
            this.requestVerb = state.requestVerb;
        }
    }

    private static State state() {
        State state = CURRENT.get();
        if (!state.claimed) {
            state.claimed = true;
            adopt(state, Thread.currentThread(), null, false, false);
        }
        return state;
    }

    private static Start taken(Object carrier, Object queue) {
        if (carrier == null) return null;
        WeakIdentityMap<Filed> byItem = queue == null || QUEUED.isEmpty()
                ? null : QUEUED.get(queue);
        Filed filed = byItem == null ? null : byItem.get(carrier);
        Start start = null;
        if (filed != null) {
            do {
                start = filed.take();
            } while (start != null && !start.adopt());
        }
        if (start != null) {
            STARTS.remove(carrier, start);
            return start;
        }
        start = STARTS.isEmpty() ? null : STARTS.remove(carrier);
        return start == null || start.adopt() ? start : null;
    }

    private static Filed filed(Object queue, Object item) {
        WeakIdentityMap<Filed> byItem = QUEUED.get(queue);
        if (byItem == null) {
            WeakIdentityMap<Filed> fresh = new WeakIdentityMap<Filed>();
            byItem = QUEUED.putIfAbsent(queue, fresh);
            if (byItem == null) byItem = fresh;
        }
        Filed filed = byItem.get(item);
        if (filed == null) {
            Filed fresh = new Filed(fifo(queue));
            filed = byItem.putIfAbsent(item, fresh);
            if (filed == null) filed = fresh;
        }
        return filed;
    }

    private static boolean fifo(Object queue) {
        return queue instanceof LinkedBlockingQueue
                || queue instanceof ArrayBlockingQueue
                || queue instanceof LinkedTransferQueue
                || queue instanceof SynchronousQueue;
    }

    private static void adopt(State state, Object carrier, Object queue,
                              boolean item, boolean continuation) {
        Start start = taken(carrier, queue);
        if (item && (start == null || start == Start.UNNAMED)) state.serves();
        if (start == null) return;
        boolean own = carrier == Thread.currentThread();
        if (start == Start.UNNAMED) {
            state.claimUnnamed(own);
            return;
        }
        boolean ranHere = !own && !continuation && start.ranHere(state);
        ClaimKind kind = item ? ClaimKind.ITEM
                : start.handoff && !ranHere ? ClaimKind.HANDOFF_TASK
                : ClaimKind.QUEUED_TASK;
        state.openStart(start, own, ranHere, kind);
        if (continuation || !own && kind == ClaimKind.HANDOFF_TASK) {
            state.standApart();
            if (!state.claimScopes.isEmpty()) {
                state.claimScopes.peek().apart = true;
            }
        }
        state.starter = start.starter;
        state.adopted = true;
        RuntimeTraceContext.claimCarried(carrier);
        if (!own && kind == ClaimKind.HANDOFF_TASK
                && Confirmation.ordering()) {
            Confirmation.entering(Confirmation.claim(start.key));
        }
        ScheduleLog.observe(ScheduleEvent.Kind.CLAIM,
                start.frame().callSite());
    }

    public static void startWork(String startSiteId, Object carrier,
                                 Object submittedTo) {
        String stable = JvmNames.stable(trimmed(startSiteId));
        if (stable.isEmpty() || carrier == null) return;
        Object queue = submittedTo instanceof BlockingQueue
                ? submittedTo : null;
        if (!Lineage.named()) {
            STARTS.putIfAbsent(carrier, Start.UNNAMED);
            if (queue != null) filed(queue, carrier).file(Start.UNNAMED);
            return;
        }
        State state = state();
        boolean continuation = carrier instanceof Continuations.Carrier;
        String named = continuation ? Continuations.registrant()
                : state.requestVerb;
        String site = named.isEmpty() ? stable : stable + ":" + named;
        int window = RecordingWindow.index();
        int iteration = state.nextStartEvent(site, window);
        List<Frame> frames = new ArrayList<Frame>(
                Arrays.asList(state.snapshot(state.scopeBase)));
        frames.add(Frame.of(site, iteration));
        RuntimeTraceContext.captureAsync(carrier);
        Start start = new Start(frames, Attribution.capture(),
                RuntimeTraceContext.nodeHere() + "|"
                        + contextHere().render() + "|"
                        + ExecutionIndex.of(frames).render(),
                Thread.currentThread(), state.top(), state.depth(),
                window, handsOff(submittedTo));
        STARTS.put(carrier, start);
        if (queue != null) filed(queue, carrier).file(start);
        if (!continuation) {
            ScheduleLog.observe(ScheduleEvent.Kind.START, site);
        }
    }

    private static boolean handsOff(Object executor) {
        if (!(executor instanceof ThreadPoolExecutor)) return false;
        try {
            return ((ThreadPoolExecutor) executor).getQueue()
                    instanceof SynchronousQueue;
        } catch (RuntimeException unstated) {
            return false;
        }
    }

    static void requestInHand(String verb) {
        CURRENT.get().requestVerb = Endpoint.verb(verb);
    }

    static long requestStarting(String site, String verb, int attempt) {
        requestInHand(verb);
        if (CURRENT.get().requestVerb.isEmpty()) return 0L;
        State state = state();
        int window = RecordingWindow.index();
        return enter(state, state.requestFrame(JvmNames.stable(site),
                attempt, window), null, window);
    }

    static void requestEnded(long token) {
        if (token <= 0L) return;
        exitFrame(token);
        requestInHand("");
    }

    static void doorFaulted(String marker) {
        if (LibraryCatalog.exchangeMarker(marker)) requestInHand("");
    }

    static Attribution.Reference starter() {
        return state().starter;
    }

    static String claimedStart() {
        State state = state();
        return state.starts.isEmpty() || state.starts.peek().own ? null
                : state.starts.peek().start;
    }

    static Set<String> servingTasks() {
        return Collections.unmodifiableSet(new TreeSet<String>(SERVING));
    }

    static ClaimKind claimKind() {
        State state = state();
        return state.starts.isEmpty() ? ClaimKind.NONE
                : state.starts.peek().kind;
    }

    static boolean adoptedStarter() {
        return state().adopted;
    }

    static List<Object> receivers() {
        return receiversOf(state());
    }

    private static List<Object> receiversOf(State state) {
        List<Object> receivers = new ArrayList<Object>();
        for (int index = state.levels.size() - 1; index >= 1; index--) {
            Object receiver = state.levels.get(index).receiver;
            if (receiver != null) receivers.add(receiver);
        }
        if (state.work != null) receivers.add(state.work);
        return receivers;
    }

    public static long claimStart(Object carrier) {
        return claimStart(carrier, false);
    }

    static long claimStart(Object carrier, boolean continuation) {
        if (carrier == null) return 0L;
        State state = state();
        ClaimScope scope = new ClaimScope(state, continuation);
        state.claimScopes.push(scope);
        try {
            claim(state, carrier, null, false, continuation);
            if (continuation) {
                scope.inbound = MessageDoors.setAside();
                scope.aside = true;
                state.requestVerb = "";
            }
        } catch (RuntimeException | Error failed) {
            endClaim(scope.id);
            throw failed;
        }
        return scope.id;
    }

    public static void endClaim(long id) {
        if (id <= 0L) return;
        State state = state();
        ClaimScope scope = null;
        for (ClaimScope open : state.claimScopes) {
            if (open.id == id) {
                scope = open;
                break;
            }
        }
        if (scope == null) return;
        while (state.claimScopes.pop() != scope) {
        }
        int from = -1;
        while (!state.starts.isEmpty()
                && state.starts.peek().serial >= scope.serial) {
            from = state.starts.pop().depth;
            RuntimeTraceContext.releaseCarried();
        }
        if (from >= 0) {
            while (state.depth() > from
                    && state.levels.get(state.depth()).token == 0L) {
                state.levels.remove(state.depth());
            }
        }
        state.work = scope.work;
        state.starter = scope.starter;
        state.adopted = scope.adopted;
        state.unnamedAt = scope.unnamedAt;
        if (scope.continuation || scope.apart) {
            while (state.regions.size() > scope.regions) {
                state.regions.remove(state.regions.size() - 1);
            }
            state.scopeBase = scope.scopeBase;
        }
        if (scope.continuation) {
            state.requestVerb = scope.requestVerb;
            if (scope.aside) MessageDoors.putBack(scope.inbound);
        }
        if (state.scopeBase > state.depth()) state.scopeBase = state.depth();
        state.journal();
    }

    static void claimItem(Object item, Object queue) {
        if (item == null) return;
        claim(state(), item, queue, true, false);
    }

    private static void claim(State state, Object carrier, Object queue,
                              boolean item, boolean continuation) {
        state.work = carrier;
        state.endUnnamedWork();
        adopt(state, carrier, queue, item, continuation);
    }

    public static long enterFrame(String callSiteId, Object receiver) {
        State state = state();
        String site = JvmNames.stable(trimmed(callSiteId));
        int window = RecordingWindow.index();
        return enter(state, Frame.of(site, state.nextSiteEvent(site,
                window)), receiver, window);
    }

    private static long enter(State state, Frame frame, Object receiver,
                              int window) {
        long token = TOKENS.getAndIncrement();
        state.levels.add(new Level(frame, token, receiver, window));
        state.journal();
        if (Confirmation.ordering()) {
            String activation = activation(state, state.depth());
            if (activation != null) Confirmation.entering(activation);
        }
        return token;
    }

    private static String activation(State state, int top) {
        Region running = state.activeRegion();
        if (running == null || running.occurrence == null) return null;
        int from = Math.max(0, Math.min(state.regionBase(), top));
        Frame[] frames = new Frame[top - from];
        for (int index = from; index < top; index++) {
            frames[index - from] = state.addressedFrame(index);
        }
        return Confirmation.activation(running.occurrence,
                ExecutionIndex.of(Arrays.asList(frames)));
    }

    public static void exitFrame(long token) {
        if (token <= 0L) return;
        State state = state();
        for (int index = state.levels.size() - 1; index >= 1; index--) {
            if (state.levels.get(index).token != token) continue;
            if (Confirmation.ordering()) {
                for (int level = state.depth(); level >= index; level--) {
                    String activation = activation(state, level);
                    if (activation != null) Confirmation.exited(activation);
                }
            }
            while (state.levels.size() > index) {
                state.levels.remove(state.levels.size() - 1);
            }
            state.closeStartsFrom(state.depth());
            if (state.depth() < state.unnamedAt) state.unnamedAt = -1;
            if (state.scopeBase > state.depth()) {
                state.scopeBase = state.depth();
            }
            state.journal();
            return;
        }
    }

    public enum Hop {
        ANCHOR,
        SCOPE_ROOT,
        STARTED_ROOT
    }

    public static int scopeStart(Hop hop) {
        State state = state();
        int before = state.scopeBase;
        state.scopeBase = hop == Hop.STARTED_ROOT && state.innermostStart() >= 0
                ? Math.min(state.innermostStart(), state.depth())
                : state.depth();
        return before;
    }

    public static void scopeRestore(int before) {
        State state = state();
        state.scopeBase = Math.max(0, Math.min(before, state.depth()));
    }

    public static ExecutionIndex atScope() {
        State state = state();
        return state.from(state.scopeBase);
    }

    public static ExecutionIndex regionEnter() {
        State state = state();
        ExecutionIndex index = state.from(state.scopeBase);
        state.regions.add(new Region(state.depth()));
        return index;
    }

    public static void regionKey(long vmRegionEnterEventId) {
        State state = state();
        Region region = state.activeRegion();
        if (region == null || vmRegionEnterEventId <= 0L) return;
        region.journal = FrameJournal.open(vmRegionEnterEventId,
                state.snapshot(region.base));
    }

    public static void regionExit(Throwable thrown) {
        State state = state();
        if (state.regions.isEmpty()) return;
        int innermost = state.regions.size() - 1;
        Region exiting = state.regions.get(innermost);
        if (exiting.before != null) {
            RowRuntime.regionUnnamed(innermost, exiting.namedBy, thrown);
        }
        Region closed = state.regions.remove(innermost);
        int claimed = -1;
        for (Claim start : state.starts) {
            if (start.depth >= closed.entered) claimed = start.depth;
        }
        if (claimed >= 0) {
            while (state.depth() > claimed) {
                state.levels.remove(state.levels.size() - 1);
            }
            state.closeStartsFrom(claimed);
            state.journal();
        }
        if (closed.occurrence != null) {
            ScheduleLog.closed(closed.occurrence.id());
            if (Confirmation.ordering()) {
                Confirmation.exited(Confirmation.activation(
                        closed.occurrence, ExecutionIndex.empty()));
                Confirmation.regionClosed(closed.occurrence);
            }
        }
    }

    public static int nextBranchOrdinal(String site) {
        State state = state();
        Region running = state.activeRegion();
        if (running == null) return 0;
        String key = trimmed(site);
        if (running.window != RecordingWindow.index()) {
            running.branchOrdinals.clear();
            running.window = RecordingWindow.index();
        }
        Integer previous = running.branchOrdinals.get(key);
        int ordinal = previous == null ? 1 : previous + 1;
        running.branchOrdinals.put(key, ordinal);
        return ordinal;
    }

    public static ExecutionIndex siteIndex() {
        State state = state();
        return state.from(state.regionBase());
    }

    public static int depth() {
        return state().depth();
    }

    public static long frameToken() {
        State state = state();
        return state.levels.get(state.depth()).token;
    }

    static String callerFrame() {
        State state = state();
        for (int depth = state.depth() - 2; depth >= 0; depth--) {
            String caller = state.frame(depth).callSite();
            if (!JvmNames.syntheticHop(caller)) return caller;
        }
        return "";
    }

    public static String innermostFrame() {
        State state = state();
        return state.depth() == 0 ? ""
                : state.frame(state.depth() - 1).callSite();
    }

    public static int regionDepth() {
        return state().regions.size();
    }

    public static CausalContext contextHere() {
        return here(Lineage.role());
    }

    public static String handoffs() {
        State state = state();
        int own = state.ownStart();
        StringBuilder chain = new StringBuilder();
        for (int index = Math.max(0, Math.max(state.scopeBase,
                state.consumedStart())); index < state.depth(); index++) {
            Level level = state.levels.get(index + 1);
            if (level.frame == null || level.token != 0L && index >= own) {
                continue;
            }
            Frame frame = state.addressedFrame(index);
            if (chain.length() > 0) chain.append('>');
            chain.append(frame.callSite());
            if (level.token == 0L) chain.append('@').append(frame.iteration());
        }
        return chain.toString();
    }

    public static String innermostRegionId() {
        Region running = state().activeRegion();
        return running == null ? "" : running.occurrence.id();
    }

    public static String innermostRegion() {
        Region running = state().activeRegion();
        return running == null ? "" : running.occurrence.render();
    }

    public static OccurrenceAddress occurrence(String nodeKey, String regionId,
                                               boolean open) {
        String node = trimmed(nodeKey);
        String region = trimmed(regionId);
        if (node.isEmpty() || region.isEmpty()) {
            return null;
        }
        if (open) {
            OccurrenceAddress enclosing = fold();
            if (enclosing != null) return enclosing;
            State state = state();
            if (state.unnamed()) {
                Region marker = new Region(state.regionBase());
                marker.entered = state.depth();
                marker.unnamed = true;
                marker.of(region, state.top().receiver);
                state.regions.add(marker);
                RowRuntime.unnamedEntry(node, region);
                return null;
            }
        }
        ExecutionIndex index = open ? regionEnter() : atScope();
        OccurrenceAddress address = OccurrenceAddress.of(
                NodeId.parse(node), region, here(Lineage.rootRole()), index);
        if (open) {
            State state = state();
            Region entered = state.region();
            if (entered != null) {
                entered.occurrence = address;
                entered.root = Lineage.rootToken();
                entered.of(region, state.top().receiver);
            }
            ScheduleLog.mark(address.id());
            if (Confirmation.ordering()) {
                Confirmation.entering(Confirmation.activation(address,
                        ExecutionIndex.empty()));
            }
            MessageDoors.regionOpened(address);
        }
        return address;
    }

    public static OccurrenceAddress answer(OccurrenceAddress declared) {
        Region entered = state().region();
        if (declared == null || entered == null
                || entered.occurrence == null) {
            return null;
        }
        OccurrenceAddress ran = entered.occurrence;
        entered.occurrence = declared;
        ScheduleLog.mark(declared.id());
        if (Confirmation.ordering()) {
            Confirmation.entering(Confirmation.activation(declared,
                    ExecutionIndex.empty()));
        }
        return ran;
    }

    private static OccurrenceAddress fold() {
        State state = state();
        Region running = state.activeRegion();
        if (running == null) return null;
        Region marker = new Region(running.base);
        marker.entered = state.depth();
        state.regions.add(marker);
        return running.occurrence;
    }

    public static boolean inOccurrence() {
        return state().activeRegion() != null;
    }

    public static List<String> standingOccurrences() {
        List<Region> regions = state().regions;
        List<String> standing = new ArrayList<String>();
        for (int index = regions.size() - 1; index >= 0; index--) {
            OccurrenceAddress occurrence = regions.get(index).occurrence;
            if (occurrence != null) standing.add(occurrence.render());
        }
        return standing;
    }

    public static boolean openedNone() {
        State state = state();
        Region innermost = state.region();
        return innermost != null && innermost.occurrence == null
                && (innermost.unnamed || state.activeRegion() != null);
    }

    public static void hopOpened(long hop) {
        State state = state();
        int index = nameless(state);
        if (index < 0) return;
        CausalContext context = here(Lineage.rootRole());
        if (context.isLost()) return;
        Region region = state.regions.get(index);
        OccurrenceAddress address = OccurrenceAddress.of(NodeId.parse(
                RuntimeTraceContext.activationSource(region.receiver).key()),
                region.regionId, context, state.from(state.scopeBase));
        region.name(hop, address);
        ScheduleLog.mark(address.id());
        if (Confirmation.ordering()) {
            Confirmation.entering(Confirmation.activation(address,
                    ExecutionIndex.empty()));
        }
        RowRuntime.regionNamed(index, address, region.receiver, hop);
    }

    public static void hopClosed(long hop) {
        if (hop <= 0L) return;
        State state = state();
        for (int index = 0; index < state.regions.size(); index++) {
            Region region = state.regions.get(index);
            if (region.before == null || region.namedBy != hop) continue;
            RowRuntime.regionUnnamed(index, hop, null);
            ScheduleLog.closed(region.occurrence.id());
            if (Confirmation.ordering()) {
                Confirmation.exited(Confirmation.activation(
                        region.occurrence, ExecutionIndex.empty()));
                Confirmation.regionClosed(region.occurrence);
            }
            region.unname();
            return;
        }
    }

    private static int nameless(State state) {
        int from = 0;
        for (int index = 0; index < state.regions.size(); index++) {
            if (state.regions.get(index).apart) from = index + 1;
        }
        for (int index = from; index < state.regions.size(); index++) {
            Region region = state.regions.get(index);
            if (region.occurrence != null) {
                return region.occurrence.lineageLost() ? index : -1;
            }
            if (region.unnamed) return index;
        }
        return -1;
    }

    public static OccurrenceAddress currentOccurrence(String nodeKey) {
        Region running = state().activeRegion();
        return running != null ? running.occurrence
                : roleOccurrence(nodeKey, Lineage.role());
    }

    public static Endpoint endpointAt(OccurrenceAddress occurrence,
                                      String site, int attempt) {
        if (occurrence == null) return null;
        String stable = JvmNames.stable(trimmed(site));
        return Endpoint.of(occurrence, stable, eventSiteIndex(stable),
                attempt);
    }

    private static ExecutionIndex eventSiteIndex(String site) {
        State state = state();
        if (site.isEmpty()) return state.from(state.regionBase());
        int iteration = state.nextSiteEvent(site);
        List<Frame> frames = new ArrayList<Frame>(
                Arrays.asList(state.snapshot(state.regionBase())));
        frames.add(Frame.of(site, iteration));
        return ExecutionIndex.of(frames);
    }

    public static Endpoint responseEndpoint(String nodeKey, String transport,
                                            String half) {
        OccurrenceAddress at = roleOccurrence(nodeKey, Lineage.role());
        if (at == null) return null;
        String site = JvmNames.stable(trimmed(transport) + "#"
                + trimmed(half));
        return Endpoint.of(at, site, ExecutionIndex.of(Arrays.asList(
                Frame.of(site, 0))), 0);
    }

    public static Endpoint messageSent(String nodeKey, String transport,
                                       String correlationId, String half,
                                       String site, Endpoint minted) {
        if (minted == null && !Lineage.named()) return null;
        Endpoint producer = minted != null ? minted
                : endpointAt(currentOccurrence(nodeKey), site, 0);
        if (producer == null) return null;
        Interactions.sent(trimmed(transport), trimmed(correlationId),
                trimmed(half), producer);
        if (producer.occurrence().role()) {
            RowRuntime.ambientActivation(producer.occurrence());
        }
        return producer;
    }

    public static OccurrenceAddress roleOccurrence(String nodeKey, Role role) {
        String node = trimmed(nodeKey);
        if (node.isEmpty()) return null;
        Role kind = role == null ? Role.UNKNOWN : role;
        return OccurrenceAddress.of(NodeId.parse(node),
                OccurrenceAddress.ROLE_REGION + kind.name(), here(kind),
                atScope());
    }

    private static CausalContext here(Role role) {
        Lineage.Here at = Lineage.here();
        return context(at.anchor, at.rpcSite, at.rootRole, at.rootApi,
                at.rootWindowIndex, role);
    }

    public static CausalContext context(String anchorEndpointId,
                                        String rpcSite, Role role,
                                        String api, int windowIndex) {
        return context(anchorEndpointId, rpcSite, role, api, windowIndex,
                role);
    }

    private static CausalContext context(String anchorEndpointId,
                                         String rpcSite, Role role,
                                         String api, int windowIndex,
                                         Role unattributed) {
        if (!trimmed(anchorEndpointId).isEmpty()) {
            return CausalContext.of(anchorEndpointId, trimmed(rpcSite));
        }
        if (role != null && !Role.UNKNOWN.equals(role)
                && windowIndex > 0) {
            return CausalContext.of(role, api, windowIndex);
        }
        return CausalContext.of(unattributed == null
                ? Role.UNKNOWN : unattributed);
    }

    public static void clock(FrameJournal.Clock source) {
        CLOCK = source == null ? UNAVAILABLE : source;
    }

    private static final FrameJournal.Clock UNAVAILABLE =
            new FrameJournal.Clock() {
                @Override
                public long now() {
                    return -1L;
                }
            };

    private static volatile FrameJournal.Clock CLOCK = UNAVAILABLE;

    static long afterLastEvent() {
        long now = CLOCK.now();
        return now < 0L ? 0L : now + 1L;
    }

    static RowOrder.Position enginePosition() {
        synchronized (ENGINE_TIES) {
            long seq = afterLastEvent();
            if (seq <= 0L) return new RowOrder.Position(0L, 0);
            if (seq != ENGINE_TIES[0]) {
                ENGINE_TIES[0] = seq;
                ENGINE_TIES[1] = 0L;
            }
            return new RowOrder.Position(seq, (int) ++ENGINE_TIES[1]);
        }
    }

    private static final long[] ENGINE_TIES = {0L, 0L};

    private static final class Region {
        private final int base;
        private int entered;
        private FrameJournal journal;
        private OccurrenceAddress occurrence;
        private boolean unnamed;
        private Map<String, Integer> branchOrdinals =
                new HashMap<String, Integer>();
        private int window = RecordingWindow.index();
        private String regionId = "";
        private Object receiver;
        private Region before;
        private long namedBy;
        private long root;
        private boolean apart;

        private Region(int base) {
            this.base = base;
            this.entered = base;
        }

        private void of(String regionId, Object receiver) {
            this.regionId = regionId;
            this.receiver = receiver;
        }

        private void name(long hop, OccurrenceAddress address) {
            Region was = new Region(base);
            was.occurrence = occurrence;
            was.unnamed = unnamed;
            was.branchOrdinals = branchOrdinals;
            was.window = window;
            was.root = root;
            before = was;
            namedBy = hop;
            occurrence = address;
            unnamed = false;
            branchOrdinals = new HashMap<String, Integer>();
            window = RecordingWindow.index();
            root = Lineage.rootToken();
        }

        private void unname() {
            occurrence = before.occurrence;
            unnamed = before.unnamed;
            branchOrdinals = before.branchOrdinals;
            window = before.window;
            root = before.root;
            before = null;
            namedBy = 0L;
        }
    }
}
