package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * The execution index of the running thread: one stack, O(1) per event
 * (IDENTITY-IMPL §B).
 *
 * <p>Every instrumented call site pushes a frame carrying its iteration in
 * the enclosing level; an occurrence is indexed from its scope root and an
 * event from its region entry.  A flat ordinal ("the k-th activation") is
 * forbidden: a branch flip inserts invocations earlier in the run and moves
 * it, while an execution index does not.</p>
 */
public final class Identity {
    private static final ThreadLocal<State> CURRENT =
            new InheritableThreadLocal<State>() {
                @Override
                protected State initialValue() {
                    return new State();
                }

                @Override
                protected State childValue(State parent) {
                    // A thread starts where it was created; the explicit
                    // carry is for a pool thread created before the work.
                    return parent == null ? new State() : parent.copy();
                }
            };

    /** Frame-level tokens: one per entered level, never reused. */
    private static final AtomicLong TOKENS = new AtomicLong(1L);

    private Identity() {
    }

    /**
     * One thread's index levels: the thread root and one level per frame.
     *
     * <p>A count belongs to the level it was taken in and dies with it
     * (IDENTITY-V3 §1, PEPID): the k of an event is the k-th event at its
     * site in the enclosing level under the current root hop ({@link
     * State#nextSiteEvent}).  Never a per-thread counter: that is a
     * run-length ordinal, which a polling loop elsewhere shifts.</p>
     */
    private static final class State {
        /** The thread root, then one level per open frame, outermost last. */
        private final List<Level> levels = new ArrayList<Level>();
        /** Whether this thread has looked for the start that created it. */
        private boolean claimed;
        private int scopeBase;
        /** Depth of the claimed start frame, or -1 when none. */
        private int startDepth = -1;
        /** The region activations open on this thread, innermost last. */
        private final List<Region> regions = new ArrayList<Region>();
        /**
         * Where this thread's work was started ({@link Attribution}, rule
         * 3): the claimed start's, else the thread's creator's.
         */
        private Attribution.Reference starter;
        /** Whether {@link #starter} is a claimed start, not the creator. */
        private boolean adopted;
        /**
         * The work this thread runs: the receiver of its last work entry
         * ({@link #claimStart}).  Attribution's outermost receiver, so a
         * daemon whose class weaves no frames (lineage-only text) is still
         * its registered object's.
         */
        private Object work;

        private State() {
            levels.add(new Level(null, 0L, null));
        }

        /** How many frames are standing. */
        private int depth() {
            return levels.size() - 1;
        }

        /** The frame at depth {@code index}, counted from the thread root. */
        private Frame frame(int index) {
            return levels.get(index + 1).frame;
        }

        /**
         * The frame as an address states it: one entered before the
         * recording window stands at iteration 0 ({@link RecordingWindow}).
         * Otherwise start-up history -- e.g. which DataNode the random block
         * placement made the k-th -- leaks into every inherited address.
         */
        private Frame addressedFrame(int index) {
            return levels.get(index + 1).addressed();
        }

        /** The level events minted right now are counted in. */
        private Level top() {
            return levels.get(levels.size() - 1);
        }

        private State copy() {
            State child = new State();
            // Frames carry over; counts do not: the child's events are not
            // events of the parent's levels.
            for (int index = 1; index < levels.size(); index++) {
                child.levels.add(new Level(levels.get(index).frame,
                        levels.get(index).token,
                        levels.get(index).receiver,
                        levels.get(index).window));
            }
            child.scopeBase = scopeBase;
            // The child claims its own start frame; until it does, its
            // creator started it.  Read this state directly: no thread-local
            // may be touched during the child's construction.
            child.starter = Attribution.Reference.of(receiversOf(this),
                    starter);
            for (Region region : regions) {
                // Depth carries over, the journal does not: a journal has
                // one writer thread.
                child.regions.add(new Region(region.base));
            }
            return child;
        }

        /**
         * Opens the frame of the start this thread's work runs under
         * (IDENTITY-V3 §1, scope transfer): two siblings started from one
         * site in one loop differ by this frame alone.  Its level has no
         * token, so no frame exit closes it.
         */
        private void openStart(Frame frame, int startedIn) {
            // A pool thread drops its finished task's start frame (and the
            // scope it carried) before taking the next; a nested start nests.
            if (startDepth >= 0 && startDepth == depth() - 1) {
                levels.remove(startDepth + 1);
                RuntimeTraceContext.releaseCarried();
            }
            startDepth = depth();
            // The frame belongs to the window the start was counted in.
            levels.add(new Level(frame, 0L, null, startedIn));
        }

        /**
         * The depth an endpoint's site index is measured from: the
         * innermost region's, else the scope root's.  Never the thread
         * base: that leaks pool-handler and queue ordinals into message
         * ids (IDENTITY-V3 §1).
         */
        private int regionBase() {
            return regions.isEmpty() ? scopeBase
                    : regions.get(regions.size() - 1).base;
        }

        private Region region() {
            return regions.isEmpty() ? null
                    : regions.get(regions.size() - 1);
        }

        /**
         * The occurrence running on this thread, or null: the fold rule's
         * test ({@link #occurrence}).  A child thread inherits region depth
         * but no occurrence ({@link #copy}), so it opens its own -- an
         * occurrence ends at a thread boundary (paper §3.1.2).
         */
        private Region activeRegion() {
            for (int index = regions.size() - 1; index >= 0; index--) {
                Region open = regions.get(index);
                if (open.occurrence != null) return open;
            }
            return null;
        }

        /**
         * Journals the standing frames into every open region's journal,
         * not only the innermost: an enclosing journal must be current when
         * a nested region returns.  One clock reading serves all.
         */
        private void journal() {
            boolean journalled = false;
            for (int index = 0; index < regions.size(); index++) {
                if (regions.get(index).journal != null) journalled = true;
            }
            // The clock is a VM call: skip it when nothing journals.
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

        /**
         * THE counter: the k of one event at {@code site} in the top level
         * under the current root hop.  Sends, region entries, work starts
         * and frame entries count here; VM-logged reads and writes by the
         * same rule at read-out ({@code LoggedEventSites#siteIndex}).
         *
         * <p>Keyed by (level, root hop, site) only.  Trap: keying also by
         * the live causal context moves the key whenever the thread's anchor
         * moves, and sibling sends collapse to one endpoint.  Two
         * activations of one region count apart through their own
         * levels.</p>
         */
        private int nextSiteEvent(String site) {
            Map<String, Integer> events = top().events(Lineage.rootToken());
            Integer made = events.get(site);
            int iteration = made == null ? 0 : made;
            events.put(site, iteration + 1);
            return iteration;
        }

        private ExecutionIndex from(int base) {
            return ExecutionIndex.of(Arrays.asList(snapshot(base)));
        }
    }

    /** One level of the index: an entered frame and the events under it. */
    private static final class Level {
        /** The frame this level was entered with, or null on the root. */
        private final Frame frame;
        /** The token the frame exit closes this level by, or 0. */
        private final long token;
        /** The activation's receiver, or null ({@link Attribution}, rule 2). */
        private final Object receiver;
        /**
         * Site counts, one map per root hop this level was innermost under,
         * outermost hop first.
         *
         * <p>Counts live for the level's lifetime within one root hop, so
         * the thread base level restarts k at each new root (IDENTITY-V3
         * §1).  One map per hop, not one cleared map: a hop opened inside
         * this level (a daemon tick inside a request) must hand the
         * enclosing hop's counts back untouched.  Trap: keying by scope
         * token instead restarts counts at every request sent.</p>
         */
        private final List<Counters> counters = new ArrayList<Counters>();

        /** The window {@link #frame} was entered in ({@link RecordingWindow}). */
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

        /** The frame as an address states it in the current window. */
        private Frame addressed() {
            if (frame == null || window == RecordingWindow.index()
                    || frame.iteration() == 0) {
                return frame;
            }
            return Frame.of(frame.callSite(), 0);
        }

        /**
         * This level's counts under the root hop {@code rootToken}.  Counts
         * of closed hops are dropped here (hop tokens are never reused), so
         * a long-lived pool level holds no map per past task.
         */
        private Map<String, Integer> events(long rootToken) {
            for (int index = counters.size() - 1; index >= 0; index--) {
                Counters filed = counters.get(index);
                if (filed.rootToken == rootToken) {
                    // Hops filed above this one were nested and have closed.
                    while (counters.size() > index + 1) {
                        counters.remove(counters.size() - 1);
                    }
                    // Counted before the window opened: count again.
                    if (filed.window != RecordingWindow.index()) {
                        filed = new Counters(rootToken);
                        counters.set(index, filed);
                    }
                    return filed.events;
                }
                // An open hop encloses this one: its counts stand.
                if (Lineage.isOpenRoot(filed.rootToken)) break;
                counters.remove(index);
            }
            Counters opened = new Counters(rootToken);
            counters.add(opened);
            return opened.events;
        }
    }

    /** One level's site counts under one root hop. */
    private static final class Counters {
        private final long rootToken;
        /** The window these counts were taken in ({@link RecordingWindow}). */
        private final int window = RecordingWindow.index();
        private final Map<String, Integer> events =
                new HashMap<String, Integer>();

        private Counters(long rootToken) {
            this.rootToken = rootToken;
        }
    }

    /**
     * The frames filed at a start site, by the object that carries the work.
     * A start is an event of the STARTER; it is filed here and taken by the
     * work when it runs, since a thread inherits its creator's state at
     * construction, before the start.
     */
    private static final Map<Carrier, Start> STARTS =
            new ConcurrentHashMap<Carrier, Start>();

    /**
     * One filed start: its frame and its starter.  A thread whose frames
     * name no component belongs to the one that started it.
     */
    private static final class Start {
        private final Frame frame;
        private final Attribution.Reference starter;
        /** The window the start was counted in ({@link Level#window}). */
        private final int window = RecordingWindow.index();

        private Start(Frame frame, Attribution.Reference starter) {
            this.frame = frame;
            this.starter = starter;
        }
    }

    private static final ReferenceQueue<Object> COLLECTED =
            new ReferenceQueue<Object>();

    /**
     * One pending start's carrier: weak, so an unrun submission is
     * collected; by identity, because two equal tasks are two submissions.
     */
    private static final class Carrier extends WeakReference<Object> {
        private final int identity;

        private Carrier(Object value, ReferenceQueue<Object> queue) {
            super(value, queue);
            this.identity = System.identityHashCode(value);
        }

        @Override
        public int hashCode() {
            return identity;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof Carrier)) return false;
            Object held = get();
            return held != null && held == ((Carrier) other).get();
        }
    }

    /**
     * This thread's state, having claimed the start filed for the THREAD
     * once.
     *
     * <p>The claim rule: started work claims its start frame at its FIRST
     * identity event, and every such event passes through here first, so
     * no address is computed without it.  Work carried by a task object
     * claims at its functional method's entry instead ({@link
     * #claimStart}); claiming only at region entry lets a pool task send
     * before claiming and share an endpoint with its sibling.</p>
     */
    private static State state() {
        State state = CURRENT.get();
        if (!state.claimed) {
            state.claimed = true;
            adopt(state, Thread.currentThread());
        }
        return state;
    }

    private static void adopt(State state, Object carrier) {
        if (carrier == null || STARTS.isEmpty()) return;
        Start start = STARTS.remove(new Carrier(carrier, null));
        if (start == null) return;
        state.openStart(start.frame, start.window);
        state.starter = start.starter;
        state.adopted = true;
        // The starter's scope comes with the work; it closes when the start
        // level goes (#exitFrame, State#openStart).
        RuntimeTraceContext.claimCarried(carrier);
        // The CLAIM half of the handoff, at the site the START named.
        ScheduleLog.observe(ScheduleEvent.Kind.CLAIM,
                start.frame.callSite());
    }

    /**
     * Files the frame of one {@code Thread.start} or work submission.
     *
     * <p>The iteration is the k-th start at this site in the level making
     * it ({@link State#nextSiteEvent}), so siblings from one loop differ by
     * it alone (IDENTITY-V3 §1) -- never a thread id or session ordinal.
     * Starts the index cannot separate share an endpoint id and are refused
     * at the mint, never renumbered here.</p>
     */
    public static void startWork(String startSiteId, Object carrier) {
        String site = JvmNames.stable(Text.safe(startSiteId));
        if (site.isEmpty() || carrier == null) return;
        // A thread with no identity files no frame: under no root hop (a
        // connection acceptor) its k would count arrivals, which nothing
        // schedules.  ScheduleLog.pending refuses such events likewise.
        if (contextHere().isLost()) return;
        State state = state();
        int iteration = state.nextSiteEvent(site);
        sweep();
        // The start's scope travels with the work
        // (RuntimeTraceContext#claimCarried takes it back).
        RuntimeTraceContext.captureAsync(carrier);
        STARTS.put(new Carrier(carrier, COLLECTED),
                new Start(Frame.of(site, iteration), Attribution.capture()));
        ScheduleLog.observe(ScheduleEvent.Kind.START, site);
    }

    /**
     * Where the work this thread runs was started ({@link Attribution},
     * rule 3), or null on a thread nothing started.
     */
    static Attribution.Reference starter() {
        return state().starter;
    }

    /** Whether that reference is a claimed start, not the thread's creator. */
    static boolean adoptedStarter() {
        return state().adopted;
    }

    /**
     * The receivers of this thread's standing frames, innermost first
     * ({@link Attribution}, rule 2).
     */
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

    /**
     * Takes the start frame filed for task {@code carrier}, if any: the
     * task half of the claim rule ({@link #state}), woven at the functional
     * method's entry by {@code CausynthPipeline.claimWorkEntry} in both
     * passes.  An unfiled thread claims nothing; its inseparable events are
     * refused at the mint, not given an invented frame.
     */
    public static void claimStart(Object carrier) {
        if (carrier == null) return;
        State state = state();
        state.work = carrier;
        if (!STARTS.isEmpty()) adopt(state, carrier);
    }

    /** Drops the entries of carriers nothing runs any more. */
    private static void sweep() {
        for (Reference<?> dead = COLLECTED.poll(); dead != null;
                dead = COLLECTED.poll()) {
            STARTS.remove(dead);
        }
    }

    /**
     * Enters the frame of one application-scope method activation.
     *
     * <p>THE frame rule: every application-scope method opens a level at
     * entry and closes it at every exit, in both passes ({@code
     * CausynthPipeline.instrumentApplicationScope}), so an event's calling
     * context is the application methods it is inside (IDENTITY-V3 §1).
     * The iteration is the k-th entry of this site in the enclosing level
     * ({@link State#nextSiteEvent}); callers outside the weave count in the
     * thread base level.</p>
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterFrame(String callSiteId, Object receiver) {
        State state = state();
        String site = JvmNames.stable(Text.safe(callSiteId));
        int iteration = state.nextSiteEvent(site);
        long token = TOKENS.getAndIncrement();
        state.levels.add(new Level(Frame.of(site, iteration), token,
                receiver));
        state.journal();
        if (Confirmation.ordering()) {
            String activation = activation(state, state.depth());
            if (activation != null) Confirmation.entering(activation);
        }
        return token;
    }

    /**
     * The key of the method activation at level {@code top} of the running
     * occurrence ({@link Endpoint#activation}), or null outside one: what a
     * CONFIRM order gate holds.
     */
    private static String activation(State state, int top) {
        Region running = state.activeRegion();
        if (running == null || running.occurrence == null) return null;
        int from = Math.max(0, Math.min(state.regionBase(), top));
        Frame[] frames = new Frame[top - from];
        for (int index = from; index < top; index++) {
            frames[index - from] = state.addressedFrame(index);
        }
        return Endpoint.activation(running.occurrence,
                ExecutionIndex.of(Arrays.asList(frames)));
    }

    /**
     * Leaves the level {@code token} opened and every level a non-local
     * exit left inside it.  The token is per activation, so recursion
     * closes its own entry; a start frame (token 0) is never closed here.
     */
    public static void exitFrame(long token) {
        if (token <= 0L) return;
        State state = state();
        for (int index = state.levels.size() - 1; index >= 1; index--) {
            if (state.levels.get(index).token != token) continue;
            if (Confirmation.ordering()) {
                // A non-local exit leaves every level inside it too.
                for (int level = state.depth(); level >= index; level--) {
                    String activation = activation(state, level);
                    if (activation != null) Confirmation.exited(activation);
                }
            }
            while (state.levels.size() > index) {
                state.levels.remove(state.levels.size() - 1);
            }
            if (state.startDepth >= state.depth()) {
                // The start frame closed with this level: its work and
                // carried scope are over.
                state.startDepth = -1;
                RuntimeTraceContext.releaseCarried();
            }
            // Clamp the scope root to the deepest level still shared: a
            // scope opened inside a returning call (inbound propagation)
            // would otherwise index from a gone level and collide.  This
            // also lands an ANCHOR hop's base on the handler's own level.
            if (state.scopeBase > state.depth()) {
                state.scopeBase = state.depth();
            }
            state.journal();
            return;
        }
    }

    /**
     * What opened a causal context: the key of the one scope-base rule
     * ({@link #scopeStart}).  Every door states its kind, so nothing is
     * inferred from the stack.
     */
    public enum Hop {
        /**
         * An inbound request ({@code RuntimeTraceContext.enterInbound}).
         * The origin is the inbound scope: which pooled handler serves it
         * is scheduling, not identity.
         */
        ANCHOR,
        /**
         * A scope the thread opens for itself ({@code beginRequest}, {@code
         * enterCarriedScope}).  The origin is the scope start; a claimed
         * start frame above it belongs to the root, not the request.
         */
        SCOPE_ROOT,
        /**
         * A root that IS the started work: a daemon tick ({@code
         * beginTick}).  The origin is the claimed start frame, else a
         * pooled tick's addresses lose the frame that separates tasks;
         * with no claimed start it begins where opened.
         */
        STARTED_ROOT
    }

    /**
     * Opens a scope: THE scope-base rule.  An index is relative to its
     * causal context's origin -- a {@link Hop#STARTED_ROOT}'s claimed start
     * frame, else the point the scope is opened at.  Trap: applying the
     * start-frame base to every hop puts the serving pool handler into a
     * request's address.
     */
    public static int scopeStart(Hop hop) {
        State state = state();
        int before = state.scopeBase;
        state.scopeBase = hop == Hop.STARTED_ROOT && state.startDepth >= 0
                ? Math.min(state.startDepth, state.depth())
                : state.depth();
        return before;
    }

    /**
     * Puts back the scope root a hop replaced: a hop's scope root lasts as
     * long as the hop.  Left in place, the exit clamp lifts it to the
     * thread base and later occurrences lose their claimed start frame.
     */
    public static void scopeRestore(int before) {
        State state = state();
        state.scopeBase = Math.max(0, Math.min(before, state.depth()));
    }

    /** The index from the scope root to here: an occurrence's own index. */
    public static ExecutionIndex atScope() {
        State state = state();
        return state.from(state.scopeBase);
    }

    /**
     * Opens a region: every endpoint inside it is indexed from here.
     *
     * @return the index from the scope root to this region entry
     */
    public static ExecutionIndex regionEnter() {
        State state = state();
        ExecutionIndex index = state.from(state.scopeBase);
        state.regions.add(new Region(state.depth()));
        return index;
    }

    /**
     * Files the innermost open region's journal under the VM's region-enter
     * event id, so VM events join their frames by the VM's statement.  A
     * folded entry keys its own journal, measured from the base of the
     * occurrence it folded into ({@link #fold}).
     */
    public static void regionKey(long vmRegionEnterEventId) {
        State state = state();
        Region region = state.region();
        if (region == null || vmRegionEnterEventId <= 0L) return;
        region.journal = FrameJournal.open(vmRegionEnterEventId,
                state.snapshot(region.base));
    }

    /**
     * Closes the innermost open region entry: one pop per entry, folded or
     * not, so a folded exit pops its marker and cannot close the occurrence
     * it folded into ({@link #fold}).  Regions hold no counts; nothing to
     * clean.
     */
    public static void regionExit() {
        State state = state();
        if (state.regions.isEmpty()) return;
        Region closed = state.regions.remove(state.regions.size() - 1);
        // A closed occurrence makes no further event (ScheduleLog).
        if (closed.occurrence != null) {
            ScheduleLog.closed(closed.occurrence.id());
            if (Confirmation.ordering()) {
                Confirmation.exited(Endpoint.activation(closed.occurrence,
                        ExecutionIndex.empty()));
            }
        }
    }

    /**
     * The 1-based ordinal of one decision at {@code site} in the occurrence
     * running here, or {@code 0} when none runs.
     *
     * <p>I3: ordinals belong to the performer.  Counted on the occurrence
     * (folded entries included), not per activation -- else two
     * activations folded into one occurrence collide at (occurrence, site,
     * ordinal), the key an obligation's flip is addressed by.</p>
     */
    public static int nextBranchOrdinal(String site) {
        State state = state();
        Region running = state.activeRegion();
        if (running == null) return 0;
        String key = Text.safe(site);
        // The window rule ({@link RecordingWindow}): renumber from the
        // window's opening.
        if (running.window != RecordingWindow.index()) {
            running.branchOrdinals.clear();
            running.window = RecordingWindow.index();
        }
        Integer previous = running.branchOrdinals.get(key);
        int ordinal = previous == null ? 1 : previous + 1;
        running.branchOrdinals.put(key, ordinal);
        return ordinal;
    }

    /** The site-local index of one event inside the region. */
    public static ExecutionIndex siteIndex() {
        State state = state();
        return state.from(state.regionBase());
    }

    /** How many index frames this thread stands on. */
    public static int depth() {
        return state().depth();
    }

    /** The innermost frame's call site, for a report, or {@code ""}. */
    public static String innermostFrame() {
        State state = state();
        return state.depth() == 0 ? ""
                : state.frame(state.depth() - 1).callSite();
    }

    /**
     * How many regions this thread has open: the second stack to balance.
     * It decides an event's occurrence and site-index base, so an
     * activation closing at another region depth must be refused, as an
     * unbalanced frame is.
     */
    public static int regionDepth() {
        return state().regions.size();
    }

    /**
     * The causal context the running thread is in ({@link #here(Role)}):
     * a schedule event's {@code c}.
     */
    public static CausalContext contextHere() {
        return here(Lineage.role());
    }

    /**
     * The start frames from the scope root, outermost first, as {@code
     * site@k>site@k}, or {@code ""}: the thread handoffs inside the scope,
     * the rest of the causal context.  Keyed by scope alone, a schedule
     * event's k would count across threads started under it, which an
     * event identity may never do ({@link ScheduleLog}).
     */
    public static String handoffs() {
        State state = state();
        StringBuilder chain = new StringBuilder();
        for (int index = Math.max(0, state.scopeBase);
             index < state.depth(); index++) {
            Level level = state.levels.get(index + 1);
            if (level.token != 0L || level.frame == null) continue;
            Frame frame = state.addressedFrame(index);
            if (chain.length() > 0) chain.append('>');
            chain.append(frame.callSite()).append('@')
                    .append(frame.iteration());
        }
        return chain.toString();
    }

    /**
     * The id of the occurrence running on this thread, or {@code ""}: where
     * a task's prefix is cut.
     */
    public static String innermostRegionId() {
        Region running = state().activeRegion();
        return running == null ? "" : running.occurrence.id();
    }

    /** The innermost open region's occurrence, for a report, or {@code ""}. */
    public static String innermostRegion() {
        Region running = state().activeRegion();
        return running == null ? "" : running.occurrence.render();
    }

    /**
     * THE one computation of an occurrence address (IDENTITY-IMPL §A).
     * Recording and replay both call it over the same stack, so their
     * addresses match by construction; offline passes read what the
     * recording stated, never re-derive it.  {@code null} when no node can
     * be named: a guessed node is a wrong causal chain.
     *
     * @param open whether this is a region ENTRY (opens an occurrence, or
     *             folds into the running one, {@link #fold}) or only a read,
     *             which must not move the base of an open region
     */
    public static OccurrenceAddress occurrence(String nodeKey, String regionId,
                                               boolean open) {
        String node = Text.safe(nodeKey);
        String region = Text.safe(regionId);
        if (node.isEmpty() || region.isEmpty()) {
            return null;
        }
        if (open) {
            OccurrenceAddress enclosing = fold();
            if (enclosing != null) return enclosing;
        }
        ExecutionIndex index = open ? regionEnter() : atScope();
        OccurrenceAddress address = OccurrenceAddress.of(
                NodeId.parse(node), region, here(Lineage.rootRole()), index);
        if (open) {
            Region entered = state().region();
            if (entered != null) entered.occurrence = address;
            // Where a prefix focusing this occurrence is cut.
            ScheduleLog.mark(address.id());
            if (Confirmation.ordering()) {
                Confirmation.entering(Endpoint.activation(address,
                        ExecutionIndex.empty()));
            }
        }
        return address;
    }

    /**
     * THE FOLD RULE (paper §3.1.2): a declared region entered synchronously
     * inside a running occurrence opens none; everything below it is an
     * event of the running occurrence.  Decided by the call stack only, so
     * recording and replay fold at the same entries.
     *
     * <p>The folded entry still pushes a marker region with the enclosing
     * base and no occurrence, so its exit closes nothing and the two stacks
     * stay balanced ({@code ConcolicRegionRuntime#closeRegionEntry}).</p>
     *
     * @return the occurrence this entry folded into, or null when this
     *         thread runs none and the entry opens its own
     */
    private static OccurrenceAddress fold() {
        State state = state();
        Region running = state.activeRegion();
        if (running == null) return null;
        state.regions.add(new Region(running.base));
        return running.occurrence;
    }

    /**
     * Whether the innermost region entry was FOLDED (F1): it is a call
     * inside the running occurrence, so neither pass records an activation
     * for it.  Asked at the entry, where the marker is innermost.
     */
    public static boolean foldedEntry() {
        State state = state();
        Region innermost = state.region();
        return innermost != null && innermost.occurrence == null
                && state.activeRegion() != null;
    }

    /**
     * The occurrence an event on this thread belongs to: the innermost open
     * region's, else the degraded role occurrence (INTERACTION-ID R-I1).
     */
    public static OccurrenceAddress currentOccurrence(String nodeKey) {
        Region running = state().activeRegion();
        return running != null ? running.occurrence
                : roleOccurrence(nodeKey, Lineage.role());
    }

    /**
     * THE endpoint of one event in {@code occurrence} (IDENTITY-IMPL §A):
     * (occurrence, site, site-local index, attempt), one computation for
     * both passes so the contexts downstream of a message match.  The site
     * is stabilised once ({@link JvmNames#stable}) and the index is taken
     * over that string.
     */
    public static Endpoint endpointAt(OccurrenceAddress occurrence,
                                      String site, int attempt) {
        if (occurrence == null) return null;
        String stable = JvmNames.stable(Text.safe(site));
        return Endpoint.of(occurrence, stable, eventSiteIndex(stable),
                attempt);
    }

    /**
     * The site-local index of the event minting an endpoint here, with the
     * event itself as the innermost frame (IDENTITY-V3 §1).  Without that
     * frame two events of one occurrence at one site share an endpoint id.
     * Its k is the enclosing level's ({@link State#nextSiteEvent}).
     */
    private static ExecutionIndex eventSiteIndex(String site) {
        State state = state();
        if (site.isEmpty()) return state.from(state.regionBase());
        int iteration = state.nextSiteEvent(site);
        List<Frame> frames = new ArrayList<Frame>(
                Arrays.asList(state.snapshot(state.regionBase())));
        frames.add(Frame.of(site, iteration));
        return ExecutionIndex.of(frames);
    }

    /** The producer endpoint a message sent here now would carry. */
    public static Endpoint messageEndpoint(String nodeKey, String transport,
                                           String half) {
        return endpointAt(currentOccurrence(nodeKey),
                Text.safe(transport) + "#" + Text.safe(half), 0);
    }

    /**
     * Files the producer endpoint of one whole message, for the anchor its
     * receiver states (IDENTITY-IMPL §C): {@code minted} when the message
     * was given its endpoint elsewhere (a response, at its request's
     * receipt), else the one sent here now.  Returns the endpoint, not its
     * digest, so rows and refusals spell out what the anchor digests.
     *
     * @return the endpoint filed, or {@code null}
     */
    public static Endpoint messageSent(String nodeKey, String transport,
                                       String correlationId, String half,
                                       Endpoint minted) {
        Endpoint producer = minted != null ? minted
                : messageEndpoint(nodeKey, transport, half);
        if (producer == null) return null;
        Interactions.sent(Text.safe(transport), Text.safe(correlationId),
                Text.safe(half), producer);
        return producer;
    }

    /**
     * The address of work under no selected region: its role, node and
     * index from the scope root ({@link #scopeStart}), never from the
     * thread's first frame (that leaks the pool handler's iteration).
     * The region slot is {@code ROLE.<role>}; the
     * context is still exact.
     */
    public static OccurrenceAddress roleOccurrence(String nodeKey, Role role) {
        String node = Text.safe(nodeKey);
        if (node.isEmpty()) return null;
        Role kind = role == null ? Role.UNKNOWN : role;
        return OccurrenceAddress.of(NodeId.parse(node),
                "ROLE." + kind.name(), here(kind), atScope());
    }

    /**
     * The context the running thread is in, by the one rule.  {@code role}
     * is the fallback when nothing is attributable ({@link
     * CausalContext.Lost}).  A ROOT context takes role, api and k from the
     * innermost root hop, which are one fact ({@code Lineage.push}).
     */
    private static CausalContext here(Role role) {
        Lineage.Here at = Lineage.here();
        return context(at.anchor, at.rpcSite, at.rootRole, at.rootApi,
                at.rootWindowIndex, role);
    }

    /** The context an occurrence entered under, from its scope frame. */
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
        if (!Text.safe(anchorEndpointId).isEmpty()) {
            return CausalContext.of(anchorEndpointId, Text.safe(rpcSite));
        }
        // No "started by a submission" arm: started work runs in its
        // starter's scope, and siblings differ by the start FRAME
        // (#startWork).  Trap: such an arm fires only in the recording, so
        // one occurrence gets two contexts.
        if (role != null && !Role.UNKNOWN.equals(role)
                && windowIndex > 0) {
            return CausalContext.of(role, api, windowIndex);
        }
        return CausalContext.of(unattributed == null
                ? Role.UNKNOWN : unattributed);
    }

    /**
     * Installs the VM's session event clock the frame journal samples.  No
     * clock, no journal: readings are never invented.
     */
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

    /** A position after every VM event so far, or 0 with no clock: where a
     *  decision the VM gave no event of its own stands. */
    static long afterLastEvent() {
        long now = CLOCK.now();
        return now < 0L ? 0L : now + 1L;
    }

    /**
     * One open region entry: where its endpoints are indexed from.  An
     * opening entry carries its occurrence; a folded one ({@link #fold})
     * carries none and is a pure ownership marker.
     */
    private static final class Region {
        private final int base;
        private FrameJournal journal;
        /** The occurrence this entry opened, or null when folded. */
        private OccurrenceAddress occurrence;
        /**
         * Decisions per site on this OCCURRENCE ({@link #nextBranchOrdinal});
         * empty on a folded entry.
         */
        private final Map<String, Integer> branchOrdinals =
                new HashMap<String, Integer>();
        /** The window {@link #branchOrdinals} were counted in. */
        private int window = RecordingWindow.index();

        private Region(int base) {
            this.base = base;
        }
    }

    public static void resetForTests() {
        CURRENT.remove();
        STARTS.clear();
        CLOCK = UNAVAILABLE;
        FrameJournal.resetForTests();
    }
}
