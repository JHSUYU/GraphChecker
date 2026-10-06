package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.LibraryCatalog;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
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
import java.util.concurrent.atomic.AtomicLong;

/**
 * The execution index of the running thread: one stack, O(1) per event
 * (IDENTITY §3).
 *
 * <p>Every instrumented call site pushes a frame carrying its iteration in
 * the enclosing level; an occurrence is indexed from its scope root and an
 * event from its region entry.  A flat ordinal ("the k-th activation") is
 * forbidden: a branch flip inserts invocations earlier in the run and moves
 * it, while an execution index does not.</p>
 */
public final class Identity {
    private static final ThreadLocal<State> CURRENT =
            new InheritedState<State>() {
                @Override
                protected State initialValue() {
                    return new State();
                }

                @Override
                protected State inherit(State parent) {
                    // A thread starts where it was created, but for a pool's
                    // worker: every task carries its own start explicitly.
                    return parent == null || PoolWorkers.constructing()
                            ? new State() : parent.copy();
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
     * (IDENTITY §3): the k of an event is the k-th event at its
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
        /**
         * The claimed starts, innermost first: a task a task runs (a
         * FutureTask inside an executor's wrapper) nests.
         */
        private final Deque<Claim> starts = new ArrayDeque<Claim>();
        /** The serial the next claim on this thread takes. */
        private long claimSerial;
        /** The work entries standing that claimed work ({@link
         *  Identity#claimStart}), innermost first. */
        private final Deque<ClaimScope> claimScopes =
                new ArrayDeque<ClaimScope>();
        /**
         * Whether this thread's own start was UNNAMED ({@link #startWork}
         * where no hop names the starter): for the thread's life.
         */
        private boolean unnamedThread;
        /**
         * The depth at which this thread claimed a task's UNNAMED start, or
         * -1: until the next claim finds that work over, or a level below
         * it exits ({@link #endUnnamedWork}, {@link Identity#exitFrame}).
         */
        private int unnamedAt = -1;
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
        /**
         * The verb of the request this thread has in hand: its last outbound
         * named it and neither a receipt nor a message door's fault came
         * since ({@link #requestInHand}, {@link #doorFaulted}); a start it
         * makes meanwhile hands that request off ({@link #startWork}).  Its
         * own: a child thread starts with none.
         */
        private String requestVerb = "";
        /**
         * The received message this thread is handing to a worker queue
         * ({@link #handoffStarting}), {@code ""} when none: a start it makes
         * meanwhile is that message's.
         */
        private String handedMessage = "";

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
         * Opens the frames of the start this thread's work runs under
         * (IDENTITY §3, start frames): the starter's index from its scope
         * root, then the start's own frame, so two starts from one site
         * differ by the frames they were made under or by that frame's k.
         * Work that already stands on its starter's frames -- a started
         * thread ({@link #copy}), or work its starter runs itself ({@link
         * Start#ranHere}) -- opens the start's own frame alone.  Their
         * levels have no token, so no frame exit closes them; a work
         * entry's claim ends when the entry returns ({@link
         * Identity#endClaim}).
         *
         * @param own whether this is the thread's own start, which is no
         *            claimed work: the thread orders it
         */
        private void openStart(Start start, boolean own, boolean ranHere) {
            // A claim takes the place of the finished one made in the same
            // work before it (a consumer loop's previous item, and the scope
            // that item carried); any other stands under it: the work that
            // runs it, or the thread's own start.
            Claim held = starts.peek();
            if (held != null && held.scope == claimScope()
                    && onlyStartsFrom(held.depth)) {
                while (depth() > held.depth) levels.remove(depth());
                closeStartsFrom(held.depth);
            }
            starts.push(new Claim(depth(), start.key, own, !own && !ranHere,
                    claimScope(), claimSerial++));
            // The frames belong to the window the start was counted in.
            for (Frame frame : own || ranHere
                    ? Collections.singletonList(start.frame())
                    : start.frames) {
                levels.add(new Level(frame, 0L, null, start.window));
            }
        }

        /** The innermost work entry's claim scope, or 0 under none. */
        private long claimScope() {
            return claimScopes.isEmpty() ? 0L : claimScopes.peek().id;
        }

        /** Whether no entered frame stands at depth {@code from} or above:
         *  only claimed starts' levels, whose work is over. */
        private boolean onlyStartsFrom(int from) {
            for (int index = from; index < depth(); index++) {
                if (levels.get(index + 1).token != 0L) return false;
            }
            return true;
        }

        /**
         * The depth of this thread's own start frame, or -1 when it claimed
         * none: every level below it is a frame of its starter's it stands
         * on ({@link #copy}).
         */
        private int ownStart() {
            for (Claim claim : starts) {
                if (claim.own) return claim.depth;
            }
            return -1;
        }

        /**
         * The depth of the outermost claim a consumer made, or -1: a queue
         * item or a task carries its putter's scope (IDENTITY §3), so which
         * consumer took it -- an IPC server's handler or reader, its own
         * start and the frames it inherited -- is the queue's scheduling,
         * stated by no context of the work (hdfs-adhoc-46: which handler
         * claimed a call moved the CLAIM's context).
         */
        private int consumedStart() {
            int outermost = -1;
            for (Claim claim : starts) {
                if (claim.consumed) outermost = claim.depth;
            }
            return outermost;
        }

        /** The depth of the innermost claimed start frame, or -1. */
        private int innermostStart() {
            return starts.isEmpty() ? -1 : starts.peek().depth;
        }

        /** Claims an UNNAMED start: the thread's own, or a task's here. */
        private void claimUnnamed(boolean thread) {
            if (thread) {
                unnamedThread = true;
            } else {
                unnamedAt = depth();
            }
        }

        /**
         * Ends a task's unnamed claim whose work is over -- no entered frame
         * stands at its depth or above -- before the next claim on this
         * thread: a pool's thread takes its next task.
         */
        private void endUnnamedWork() {
            if (unnamedAt >= 0 && onlyStartsFrom(unnamedAt)) unnamedAt = -1;
        }

        /**
         * Whether this thread runs unnamed work that no hop names yet: what
         * it enters is no occurrence ({@link Identity#occurrence}).
         */
        private boolean unnamed() {
            return (unnamedThread || unnamedAt >= 0) && !Lineage.named();
        }

        /**
         * Closes every claimed start at depth {@code depth} or deeper, whose
         * level is gone: its work and the scope it carried are over, one
         * carried scope per start.
         */
        private void closeStartsFrom(int depth) {
            while (!starts.isEmpty() && starts.peek().depth >= depth) {
                starts.pop();
                RuntimeTraceContext.releaseCarried();
            }
        }

        /**
         * The depth an endpoint's site index is measured from: the
         * innermost region's, else the scope root's.  Never the thread
         * base: that leaks pool-handler and queue ordinals into message
         * ids (IDENTITY §4).
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
         * under the root hop that owns the count ({@link #countingRoot}).
         * Sends, region entries, work starts and frame entries count here;
         * VM-logged reads and writes by the same rule at read-out ({@code
         * LoggedEventSites#siteIndex}).
         *
         * <p>Keyed by (level, root hop, site) only.  Trap: keying also by
         * the live causal context moves the key whenever the thread's anchor
         * moves, and sibling sends collapse to one endpoint.  Two
         * activations of one region count apart through their own
         * levels.</p>
         */
        private int nextSiteEvent(String site) {
            return nextSiteEvent(site, RecordingWindow.index());
        }

        /** {@link #nextSiteEvent} in {@code window}: an entry reads the
         *  window once, for its count and its level alike. */
        private int nextSiteEvent(String site, int window) {
            return next(top().events(countingRoot(), window), site);
        }

        /**
         * THE request's level (IDENTITY §3): the k-th request at its message
         * site (which names its verb) in the enclosing level under the root
         * hop that owns the count ({@link #nextSiteEvent}), as a start made
         * with a request in hand is counted per verb: a request of another
         * verb -- a heartbeat a replay inserted, a call a fault added --
         * renames no later one (hdfs-adhoc-52 SL1-3: the test's every
         * {@code Client.call@k} counted all its RPCs).  A retry (attempt
         * {@code a}) is its original's k at {@code <site>#retry<a>}; one
         * whose original this level did not count (a retry on another
         * thread) is counted at that site, never a silent 0.
         */
        private Frame requestFrame(String site, int attempt, int window) {
            if (attempt <= 0) {
                return Frame.of(site, nextSiteEvent(site, window));
            }
            String retry = site + "#retry" + attempt;
            Integer made = top().events(countingRoot(), window).get(site);
            return made == null ? Frame.of(retry, nextSiteEvent(retry, window))
                    : Frame.of(retry, made - 1);
        }

        /**
         * The root hop an event's count is kept under: the one the
         * occurrence running here was opened or named under ({@link
         * Region#root}), else the current root hop.  An occurrence's address
         * is its frame path within it, and names no root hop opened inside
         * it: one restarting the counts would give two of its events one
         * index (round HG5A, hdfs-adhoc-21: a DataNode actor's {@code run()}
         * occurrence, entered in the startup window under the test's
         * request, sent each turn's heartbeat at {@code
         * offerService@0/sendHeartBeat@0}, one producer endpoint for three
         * turns, so the NameNode served all three under one anchor).
         */
        private long countingRoot() {
            Region running = activeRegion();
            return running != null ? running.root : Lineage.rootToken();
        }

        /**
         * THE start counter: the k of one start at {@code site} in the top
         * level under the hop that gives the context (IDENTITY §3), not the
         * whole root hop: under a test's one request every poll and node
         * start before it moved the k of a shell command's thread
         * (hdfs-adhoc-35: @317 recorded, @404 replayed).  No two works can
         * share an address by it: each carries that hop's context.
         */
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
         * the thread base level restarts k at each new root where no
         * occurrence runs (IDENTITY §3, {@link State#countingRoot}).  One map per hop, not one cleared map: a hop opened inside
         * this level (a daemon tick inside a request) must hand the
         * enclosing hop's counts back untouched.  Trap: keying by scope
         * token instead restarts counts at every request sent.</p>
         */
        private final List<Counters> counters = new ArrayList<Counters>();
        /** Start counts, one map per context hop ({@link #nextStartEvent}). */
        private final List<Counters> startCounters = new ArrayList<Counters>();

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
        private Map<String, Integer> events(long rootToken, int window) {
            return counts(counters, rootToken, window);
        }

        /** This level's start counts under the context hop {@code hop}. */
        private Map<String, Integer> startEvents(long hop, int window) {
            return counts(startCounters, hop, window);
        }

        private static Map<String, Integer> counts(List<Counters> filedHops,
                                                   long hop, int window) {
            for (int index = filedHops.size() - 1; index >= 0; index--) {
                Counters filed = filedHops.get(index);
                if (filed.rootToken == hop) {
                    // Hops filed above this one were nested and have closed.
                    while (filedHops.size() > index + 1) {
                        filedHops.remove(filedHops.size() - 1);
                    }
                    // Counted before the window opened: count again.
                    if (filed.window != window) {
                        filed = filed.reopened(window);
                        filedHops.set(index, filed);
                    }
                    return filed.events;
                }
                // An open hop encloses this one: its counts stand.
                if (Lineage.isOpen(filed.rootToken)) break;
                filedHops.remove(index);
            }
            Counters opened = new Counters(hop, window);
            filedHops.add(opened);
            return opened.events;
        }
    }

    /** One level's site counts under one root hop. */
    private static final class Counters {
        private final long rootToken;
        /** The window these counts were taken in ({@link RecordingWindow}). */
        private final int window;
        private final Map<String, Integer> events =
                new HashMap<String, Integer>();

        private Counters(long rootToken, int window) {
            this.rootToken = rootToken;
            this.window = window;
        }

        /**
         * These counts, counted again from the opening of {@code window}: a
         * site this level reached before it starts at 1.  Its m entries then
         * all stand at 0 ({@link Level#addressed}), one perhaps still
         * running, so the window's first entry is the next one: with m
         * entries before the window, in-window entry j is {@code @(j + [m >
         * 0])}.  Restarted at 0 it took the standing entry's address (round
         * SL1, hdfs-adhoc-39: the NameNode's blockReport handler serving a
         * DataNode's report queued two storage reports through {@code
         * runBlockOp}, the first entered before the window, both lambdas at
         * {@code runBlockOp@0}).  Two passes agree where their m are equal,
         * or 0 and 1 (the window opened before, or during, one call); not 1
         * and 2, nor 0 and m >= 1 where the earlier entries are set-up
         * noise (IDENTITY §3).
         */
        private Counters reopened(int window) {
            Counters counted = new Counters(rootToken, window);
            for (String site : events.keySet()) {
                counted.events.put(site, 1);
            }
            return counted;
        }
    }

    /**
     * The frames filed at a start site, by the object that carries the work.
     * A start is an event of the STARTER; it is filed here and taken by the
     * work when it runs, since a thread inherits its creator's state at
     * construction, before the start.  By identity, because two equal tasks
     * are two submissions; weakly, so an unrun submission is collected.
     */
    private static final WeakIdentityMap<Start> STARTS =
            new WeakIdentityMap<Start>();

    /**
     * One filed start: its frames and its starter.  A thread whose frames
     * name no component belongs to the one that started it.  An UNNAMED
     * start ({@link #startWork} where no hop names the starter) has
     * neither: it states only that the work has no identity of its own.
     */
    private static final class Start {
        private static final Start UNNAMED = new Start(
                Collections.<Frame>emptyList(), null, "", null, null, 0, 0);
        /** The starter's frames from its scope root, then the start's. */
        private final List<Frame> frames;
        private final Attribution.Reference starter;
        /**
         * What tells this start apart from every other of the run, as its
         * START event does: the starter's node and context, then {@link
         * #frames} ({@link #claimedStart}).
         */
        private final String key;
        /** The window the start was counted in ({@link Level#window}). */
        private final int window;
        /**
         * The thread that made the start, and its innermost level then,
         * held weakly: a level holds its activation's receiver, which may be
         * the carrier this start is filed under (a task resubmitting
         * itself), and a value holding its own key would keep the weak
         * entry forever.  Gone, neither can be standing ({@link #ranHere}).
         */
        private final WeakReference<Thread> thread;
        private final WeakReference<Level> level;
        private final int depth;

        private Start(List<Frame> frames, Attribution.Reference starter,
                      String key, Thread thread, Level level, int depth,
                      int window) {
            this.frames = frames;
            this.starter = starter;
            this.key = key;
            this.thread = new WeakReference<Thread>(thread);
            this.level = new WeakReference<Level>(level);
            this.depth = depth;
            this.window = window;
        }

        /** The start's own frame: its site and k. */
        private Frame frame() {
            return frames.get(frames.size() - 1);
        }

        /**
         * Whether {@code state}'s thread is the starter and still stands on
         * the level it started from: the starter runs the work itself (an
         * executor that runs a task on the calling thread, HBase's
         * {@code IPCUtil#execute} on its own event loop).  The work stands on
         * the starter's frames already; opened again on top of them, every
         * such run doubled the stack.
         */
        private boolean ranHere(State state) {
            Level standing = level.get();
            return thread.get() == Thread.currentThread() && standing != null
                    && depth <= state.depth()
                    && state.levels.get(depth) == standing;
        }
    }

    /**
     * One claimed start standing on a thread: where its levels open, its
     * start's {@link Start#key}, the claim scope that made it, and its
     * serial on the thread.
     */
    private static final class Claim {
        private final int depth;
        private final String start;
        /** Whether this is the thread's own start, which is no claimed work. */
        private final boolean own;
        /**
         * Whether a consumer claimed it: a queue item or a task taken on
         * another thread than its starter's, whose context is its putter's
         * ({@link #handoffs}).
         */
        private final boolean consumed;
        private final long scope;
        private final long serial;

        private Claim(int depth, String start, boolean own, boolean consumed,
                      long scope, long serial) {
            this.depth = depth;
            this.start = start;
            this.own = own;
            this.consumed = consumed;
            this.scope = scope;
            this.serial = serial;
        }
    }

    /**
     * One work entry's claim scope: what it found on the thread, which it
     * puts back when the work returns ({@link #endClaim}).
     */
    private static final class ClaimScope {
        private final long id = TOKENS.getAndIncrement();
        /** The serial of the first claim this activation may make. */
        private final long serial;
        private final Object work;
        private final Attribution.Reference starter;
        private final boolean adopted;
        private final int unnamedAt;

        private ClaimScope(State state) {
            this.serial = state.claimSerial;
            this.work = state.work;
            this.starter = state.starter;
            this.adopted = state.adopted;
            this.unnamedAt = state.unnamedAt;
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
        Start start = STARTS.remove(carrier);
        if (start == null) return;
        // The thread a start created claims it itself, standing on the
        // frames it inherited; a task is claimed on a pool's thread.
        boolean own = carrier == Thread.currentThread();
        if (start == Start.UNNAMED) {
            // Work no hop started: nothing to open, nothing carried, no
            // CLAIM (its START was never an event).
            state.claimUnnamed(own);
            return;
        }
        state.openStart(start, own, !own && start.ranHere(state));
        state.starter = start.starter;
        state.adopted = true;
        // The starter's scope comes with the work; it closes when the start
        // levels go (#exitFrame, State#openStart).
        RuntimeTraceContext.claimCarried(carrier);
        // The CLAIM half of the handoff, at the site the START named.
        ScheduleLog.observe(ScheduleEvent.Kind.CLAIM,
                start.frame().callSite());
    }

    /**
     * Files the frames of one {@code Thread.start} or work submission: the
     * starter's index from its scope root, then the start's own frame.
     *
     * <p>The iteration is the k-th start at this site in the level making
     * it ({@link State#nextSiteEvent}), so siblings from one loop differ by
     * it (IDENTITY §3) -- never a thread id or session ordinal.  Starts from
     * one site in two calls of the method holding it are both its first:
     * the frames above tell them apart (hdfs-11741 r3: the balancer's two
     * {@code executePendingMove} tasks shared one address once a pool's
     * worker stopped inheriting its creator's frames).  Starts the index
     * cannot separate share an endpoint id and are refused at the mint,
     * never renumbered here.</p>
     *
     * <p>A starter no hop names files no frame: under no hop (a connection
     * acceptor) its k would count arrivals, which nothing schedules ({@code
     * ScheduleLog.pending} refuses such events likewise).  It files an
     * UNNAMED start instead: siblings started so differ by nothing an
     * address names, so the work opens no occurrence until a hop names it
     * ({@link #occurrence}).  One test decides both: {@link Lineage#named}.</p>
     */
    public static void startWork(String startSiteId, Object carrier) {
        String stable = JvmNames.stable(Text.safe(startSiteId));
        if (stable.isEmpty() || carrier == null) return;
        if (!Lineage.named()) {
            // Never in place of a named start of the same carrier.
            STARTS.putIfAbsent(carrier, Start.UNNAMED);
            return;
        }
        State state = state();
        // A received message handed to a worker queue is that message's
        // (#handoffStarting); a start made with a request in hand hands that
        // request off: it is that operation's, its k counted per verb
        // (IDENTITY §3).
        String named = state.handedMessage.isEmpty() ? state.requestVerb
                : state.handedMessage;
        String site = named.isEmpty() ? stable : stable + ":" + named;
        // One reading of the window, for the count and the filed start.
        int window = RecordingWindow.index();
        int iteration = state.nextStartEvent(site, window);
        List<Frame> frames = new ArrayList<Frame>(
                Arrays.asList(state.snapshot(state.scopeBase)));
        frames.add(Frame.of(site, iteration));
        // The start's scope travels with the work
        // (RuntimeTraceContext#claimCarried takes it back).
        RuntimeTraceContext.captureAsync(carrier);
        STARTS.put(carrier, new Start(frames, Attribution.capture(),
                        RuntimeTraceContext.nodeHere() + "|"
                                + contextHere().render() + "|"
                                + ExecutionIndex.of(frames).render(),
                        Thread.currentThread(), state.top(), state.depth(),
                        window));
        ScheduleLog.observe(ScheduleEvent.Kind.START, site);
    }

    /**
     * Sets the request this thread has in hand: every outbound states its
     * verb ({@code ""} for a message whose door names none, and for a
     * response), every receipt and every message door's fault clears it
     * ({@link #doorFaulted}).  The Hadoop IPC caller sends its
     * request, hands it to the connection's sender (a queue offer, the
     * start {@link #startWork} names), waits and receives the response: a
     * DataNode turn's heartbeat hand-off no longer takes its block report's
     * START and CLAIM (hdfs-adhoc-15).
     */
    static void requestInHand(String verb) {
        // Not state(): a door is no identity event, and claims no start.
        CURRENT.get().requestVerb = Endpoint.verb(verb);
    }

    /**
     * A request of {@code verb} starts on this thread, attempt {@code
     * attempt} of it ({@code MessageDoors#requestStarting}): it is in hand
     * from here ({@link #requestInHand}) and opens a level of its own at
     * {@code site}, its message site ({@link State#requestFrame}), whatever
     * of the client the case's scope frames.  A request naming no verb is
     * only in hand.
     *
     * @return the token {@link #requestEnded} closes its level by, or 0
     */
    static long requestStarting(String site, String verb, int attempt) {
        requestInHand(verb);
        if (CURRENT.get().requestVerb.isEmpty()) return 0L;
        State state = state();
        int window = RecordingWindow.index();
        return enter(state, state.requestFrame(JvmNames.stable(site),
                attempt, window), null, window);
    }

    /**
     * The request {@link #requestStarting} opened is over, answered or
     * failed: its level closes and it is in hand no more, so a call that
     * failed before its send (a connection refused) names no later start
     * (the hdfs-17899-bug2 class, {@link #doorFaulted}).
     */
    static void requestEnded(long token) {
        if (token <= 0L) return;
        exitFrame(token);
        requestInHand("");
    }

    /**
     * This thread hands a received message to a worker queue ({@code
     * MessageDoors#handingOff}), until {@link #handoffEnded}: every start it
     * makes meanwhile is that message's, named by {@code message} (its
     * sender's endpoint) and standing on none of the thread's own frames, so
     * no other message the thread handed off before renames it (IDENTITY §3).
     * An IPC server's Reader counted its calls per connection: one call the
     * replay did not make renamed every later call of that connection, and
     * each one stood its watchdog out (hdfs-adhoc-21, round TM13: 14 of its
     * 17 stalls).
     *
     * @return what {@link #handoffEnded} takes; null for a message that
     *         names no sender, whose hand-off is a plain start
     */
    static Object handoffStarting(String message) {
        if (Text.safe(message).isEmpty()) return null;
        State state = state();
        Handoff handoff = new Handoff(state.scopeBase, state.handedMessage);
        state.scopeBase = state.depth();
        state.handedMessage = message;
        return handoff;
    }

    /** The hand-off {@link #handoffStarting} began is over. */
    static void handoffEnded(Object token) {
        if (!(token instanceof Handoff)) return;
        Handoff handoff = (Handoff) token;
        State state = state();
        state.handedMessage = handoff.message;
        state.scopeBase = Math.max(0, Math.min(handoff.scopeBase,
                state.depth()));
    }

    /** What a hand-off replaced: the scope root and the message before it. */
    private static final class Handoff {
        final int scopeBase;
        final String message;

        Handoff(int scopeBase, String message) {
            this.scopeBase = scopeBase;
            this.message = message;
        }
    }

    /**
     * A fault marker answered true on this thread, where a run decides one
     * (a replay's mint, {@link RootMint}; a native reproduction's plant,
     * {@link RecordingPlant#marker}): a message door's fault ends the
     * exchange the thread had in hand, in failure, as a receipt ends it, so
     * no later start hands that request off.  Left in hand, it named every
     * later start of the thread (hdfs-17899-bug2: once the SPS key
     * manager's {@code getBlockKeys} request faulted, the test thread
     * started the SPS daemon as {@code
     * Daemon.start()#u5:NamenodeProtocol.getBlockKeys}, an address no plan
     * instrumented, and the key id's producer went unattested).  A demanded
     * door's fault (a local file operation) ends no exchange.
     */
    static void doorFaulted(String marker) {
        if (LibraryCatalog.exchangeMarker(marker)) requestInHand("");
    }

    /**
     * Where the work this thread runs was started ({@link Attribution},
     * rule 3), or null on a thread nothing started.
     */
    static Attribution.Reference starter() {
        return state().starter;
    }

    /**
     * The key of the innermost start this thread's work was claimed from (a
     * task, a queue item), or null under none or under the thread's own
     * start: what an activation is program-ordered by ({@code
     * RowRuntime#threadKey}).
     * Work claimed one item after another on one consumer thread runs in the
     * order its items arrived, which their starters decide, not the thread.
     */
    static String claimedStart() {
        State state = state();
        return state.starts.isEmpty() || state.starts.peek().own ? null
                : state.starts.peek().start;
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
     * passes, before the method's level.  An unfiled thread claims nothing;
     * its inseparable events are refused at the mint, not given an invented
     * frame.
     *
     * @return what ends the claim when the work returns ({@link #endClaim})
     */
    public static long claimStart(Object carrier) {
        if (carrier == null) return 0L;
        State state = state();
        ClaimScope scope = new ClaimScope(state);
        state.claimScopes.push(scope);
        claim(state, carrier);
        return scope.id;
    }

    /**
     * Ends the claim {@link #claimStart} made at a work entry, woven at the
     * entry's every exit after its own level: the claims made since -- the
     * work's own and any a queue take inside it made -- end with it, their
     * start levels and the scopes they carried, and the work, starter and
     * unnamed state they replaced come back.  Left standing, an event
     * loop's callbacks ran on its last task's frames and scope, and each
     * send they made nested under the one before (HBA1: 3777 frames on one
     * HBase client event loop).  A claim a non-local exit left inside it
     * ends with it.
     */
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
            // a claim a non-local exit left inside it
        }
        int from = -1;
        while (!state.starts.isEmpty()
                && state.starts.peek().serial >= scope.serial) {
            from = state.starts.pop().depth;
            RuntimeTraceContext.releaseCarried();
        }
        if (from >= 0) {
            // The claims' levels; a frame entered above them has exited.
            while (state.depth() > from
                    && state.levels.get(state.depth()).token == 0L) {
                state.levels.remove(state.depth());
            }
        }
        state.work = scope.work;
        state.starter = scope.starter;
        state.adopted = scope.adopted;
        state.unnamedAt = scope.unnamedAt;
        if (state.scopeBase > state.depth()) state.scopeBase = state.depth();
        state.journal();
    }

    /**
     * Takes the start filed for an item taken off a queue (woven after the
     * take in both passes), which lasts until the consumer takes its next
     * item or the work it runs in ends.  Whoever put the item there, its
     * scope comes with it: one consumer may serve the work of every node of
     * the JVM (Hadoop IPC's RpcRequestSender, one per connection, sends each
     * in-JVM DataNode's calls).
     */
    static void claimItem(Object item) {
        if (item == null) return;
        claim(state(), item);
    }

    private static void claim(State state, Object carrier) {
        state.work = carrier;
        // A task claimed here takes the place of a finished unnamed one.
        state.endUnnamedWork();
        if (!STARTS.isEmpty()) adopt(state, carrier);
    }

    /**
     * Enters the frame of one application-scope method activation.
     *
     * <p>THE frame rule: every application-scope method opens a level at
     * entry and closes it at every exit, in both passes ({@code
     * CausynthPipeline.instrumentApplicationScope}), so an event's calling
     * context is the application methods it is inside (IDENTITY §3).
     * The iteration is the k-th entry of this site in the enclosing level
     * ({@link State#nextSiteEvent}); callers outside the weave count in the
     * thread base level.</p>
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterFrame(String callSiteId, Object receiver) {
        State state = state();
        String site = JvmNames.stable(Text.safe(callSiteId));
        // One reading of the window, for the count and the level alike: an
        // entry racing the window's opening counted under one and filed
        // under the other would keep a set-up count inside the window.
        int window = RecordingWindow.index();
        return enter(state, Frame.of(site, state.nextSiteEvent(site,
                window)), receiver, window);
    }

    /** Opens one level at {@code frame}, counted in {@code window},
     *  journalled and, under CONFIRM's order gate, entered. */
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

    /**
     * The key of the method activation at level {@code top} of the running
     * occurrence ({@link Confirmation#activation}), or null outside one: what a
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
        return Confirmation.activation(running.occurrence,
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
            // A start frame closed with this level: its work is over.
            state.closeStartsFrom(state.depth());
            if (state.depth() < state.unnamedAt) state.unnamedAt = -1;
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
        state.scopeBase = hop == Hop.STARTED_ROOT && state.innermostStart() >= 0
                ? Math.min(state.innermostStart(), state.depth())
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
     * Files the journal of the region the running occurrence is under the
     * VM's region-enter event id, so VM events join their frames by the VM's
     * statement, measured from that region's entry.  Not the innermost
     * entry's: a folded entry's marker, or unnamed work's inside a region a
     * hop named ({@link #hopOpened}), closes before the activation does, and
     * the frames of every event after it would be unplaced.
     */
    public static void regionKey(long vmRegionEnterEventId) {
        State state = state();
        Region region = state.activeRegion();
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
        regionExit(null);
    }

    /**
     * {@link #regionExit()}, by a throw when {@code thrown} is not null: an
     * occurrence a hop named ends with its region's entry, whichever comes
     * first ({@link #hopOpened}), and states how.
     */
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
            if (start.depth >= closed.base) claimed = start.depth;
        }
        if (closed.occurrence != null && claimed >= 0) {
            // Work the occurrence claimed ends with it: its start levels and
            // the scopes they carried close here, not at the next claim.  A
            // region that drains a queue (BlockManager's processQueue) would
            // otherwise close a level deeper than it opened.  A folded entry's
            // marker shares its occurrence's base and closes nothing.
            while (state.depth() > claimed) {
                state.levels.remove(state.levels.size() - 1);
            }
            state.closeStartsFrom(claimed);
            state.journal();
        }
        // A closed occurrence makes no further event (ScheduleLog).
        if (closed.occurrence != null) {
            ScheduleLog.closed(closed.occurrence.id());
            if (Confirmation.ordering()) {
                Confirmation.exited(Confirmation.activation(
                        closed.occurrence, ExecutionIndex.empty()));
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

    /**
     * The token of the innermost level, unique to one method activation (0
     * at the thread root): what a loop budget is counted in.
     */
    public static long frameToken() {
        State state = state();
        return state.levels.get(state.depth()).token;
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
     * The claimed starts' frames from the scope root, outermost first, as
     * {@code site@k>site@k}, or {@code ""}: the thread handoffs inside the
     * scope, each the frames it was made under and its own, the rest of the
     * causal context.  Keyed by scope alone, a schedule
     * event's k would count across threads started under it, which an
     * event identity may never do ({@link ScheduleLog}).
     *
     * <p>A task claimed on a pool's thread stands on its starter's frames as
     * levels of the claim; a started thread stands on the frames it
     * inherited from its creator ({@link State#copy}) and adds its start
     * frame alone, so those inherited frames are its starter's frames here.
     * Without them two threads started through one utility (Hadoop's {@code
     * Daemon.start}, each call a level of its own, so both starts are its
     * 0th) after one RPC returned shared one context: hdfs-adhoc-02's
     * LeaseRenewer took the DataStreamer's addBlock slot and every later
     * send of either was the other's.</p>
     */
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
            // An inherited frame by its site alone: its k counts how often
            // the creator came there (the k-th call of a poll re-creating an
            // idle connection), which one thread's events must not depend
            // on; a claim level's k is the start's own.
            if (level.token == 0L) chain.append('@').append(frame.iteration());
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
     * THE one computation of an occurrence address (IDENTITY §1).
     * Recording and replay both call it over the same stack, so their
     * addresses match by construction; offline passes read what the
     * recording stated, never re-derive it.  {@code null} when no node can
     * be named: a guessed node is a wrong causal chain.
     *
     * <p>UNNAMED WORK opens none: work started under no context ({@link
     * #startWork}) differs from its siblings by nothing an address names --
     * a DataNode's connections, each run before its first message by a
     * thread its acceptor started under no root, would share one address.
     * Until a hop names it, a region it enters is a marker like a fold's,
     * and its events are its role's ({@link #currentOccurrence}).</p>
     *
     * @param open whether this is a region ENTRY (opens an occurrence, or
     *             folds into the running one, {@link #fold}) or only a read,
     *             which must not move the base of an open region
     * @return the address, or null when no node can be named or an entry
     *         of unnamed work opened none
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
            State state = state();
            if (state.unnamed()) {
                Region marker = new Region(state.regionBase());
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
            // Where a prefix focusing this occurrence is cut.
            ScheduleLog.mark(address.id());
            if (Confirmation.ordering()) {
                Confirmation.entering(Confirmation.activation(address,
                        ExecutionIndex.empty()));
            }
        }
        return address;
    }

    /**
     * Gives the occurrence the innermost region entry opened the address
     * {@code declared}, a planned occurrence it answers by its shape
     * (IDENTITY §9, {@code ConcolicTaskPlan#select}): from here its rows,
     * endpoints, decision ordinals, schedule mark and close state the
     * planned address, as the recording's did, and so does every endpoint
     * minted under it.
     *
     * @return the address this run computed for it, or null when the entry
     *         opened no occurrence of its own (a fold, unnamed work)
     */
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
     * <p>An occurrence that opened Lost folds what is entered while the
     * thread is still Lost; the hop that gives the thread a context names
     * its region ({@link #hopOpened}), so no two contexts share the Lost
     * address (owner, 2026-09-27).</p>
     *
     * @return the occurrence this entry folded into, or null when the entry
     *         opens its own
     */
    private static OccurrenceAddress fold() {
        State state = state();
        Region running = state.activeRegion();
        if (running == null) return null;
        state.regions.add(new Region(running.base));
        return running.occurrence;
    }

    /**
     * Whether the innermost region entry opened no occurrence (IDENTITY §1):
     * it FOLDED into the running one, or unnamed work entered it ({@link
     * #occurrence}), so neither pass records an activation for it.  Asked at
     * the entry, where its marker is innermost.
     */
    public static boolean openedNone() {
        State state = state();
        Region innermost = state.region();
        return innermost != null && innermost.occurrence == null
                && (innermost.unnamed || state.activeRegion() != null);
    }

    /**
     * THE NAMING RULE (IDENTITY §1, unnamed work): a hop that gives this
     * thread a context of its own names the region its work stands in when
     * that region's entry has none -- unnamed work entered it, or it opened
     * {@code Lost} (a turn begun before the window).  The region opens an
     * occurrence under the hop, indexed from the hop's scope base, until the
     * hop ends or the region's entry exits, whichever comes first; what it
     * enters meanwhile folds into it, and its decisions take that
     * occurrence's ordinals.  Called by every hop opener in both passes
     * ({@code RuntimeTraceContext}), so both name the same regions at the
     * same events.
     *
     * <p>The outermost such region: what it entered before the hop is its
     * work (the fold rule, "the enclosing occurrence wins").  A named
     * occurrence standing below it would have taken its entries, so none
     * stands.  A daemon started before the window or under no root
     * (DataNodeDiskMetrics' detector) runs its service loop in a region
     * whose one entry opened none; each WAKE turn now names one of its
     * iterations.</p>
     *
     * @param hop the lineage token of the hop just opened
     */
    public static void hopOpened(long hop) {
        State state = state();
        // Only a region with no name reads the hop's context: a turn that
        // names nothing stays unnamed (Lineage#pop).
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

    /**
     * Ends the occurrence the hop {@code hop} named, if its region still
     * stands: the region is nameless again ({@link #hopOpened}).
     */
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
            }
            region.unname();
            return;
        }
    }

    /**
     * The position of the outermost standing region whose entry has no name
     * ({@link #hopOpened}), or -1: none stands, or a named occurrence stands
     * below it.  A fold's marker, and a region a child thread inherited
     * ({@link State#copy}), is no entry of this thread's work.
     */
    private static int nameless(State state) {
        for (int index = 0; index < state.regions.size(); index++) {
            Region region = state.regions.get(index);
            if (region.occurrence != null) {
                return region.occurrence.lineageLost() ? index : -1;
            }
            if (region.unnamed) return index;
        }
        return -1;
    }

    /**
     * The occurrence an event on this thread belongs to: the innermost open
     * region's, else the degraded role occurrence (IDENTITY §1).
     */
    public static OccurrenceAddress currentOccurrence(String nodeKey) {
        Region running = state().activeRegion();
        return running != null ? running.occurrence
                : roleOccurrence(nodeKey, Lineage.role());
    }

    /**
     * THE endpoint of one event in {@code occurrence} (IDENTITY §4):
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
     * event itself as the innermost frame (IDENTITY §4).  Without that
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

    /**
     * The producer endpoint of the response to the request received here
     * now: the request's scope, whose context names the request's own
     * anchor, and the response site alone.  Not the region this receipt runs
     * in -- one a pool handler opened before the request came (the
     * NameNode's {@code doAs}), whose index counts the calls that handler
     * took -- nor this thread's frames or site counts: which handler took
     * the call would rename the response, and two handlers' first calls
     * would share one.
     */
    public static Endpoint responseEndpoint(String nodeKey, String transport,
                                            String half) {
        OccurrenceAddress at = roleOccurrence(nodeKey, Lineage.role());
        if (at == null) return null;
        String site = JvmNames.stable(Text.safe(transport) + "#"
                + Text.safe(half));
        return Endpoint.of(at, site, ExecutionIndex.of(Arrays.asList(
                Frame.of(site, 0))), 0);
    }

    /**
     * Files the producer endpoint of one whole message, for the anchor its
     * receiver states (IDENTITY §4): {@code minted} when the message
     * was given its endpoint elsewhere (a response, at its request's
     * receipt), else the one sent here now at {@code site} ({@code
     * Endpoint#messageSite}).  Returns the endpoint, not its digest, so rows
     * and refusals spell out what the anchor digests.
     *
     * <p>A message unnamed work sends here (no hop names the thread, §1)
     * files none, as an unnamed start files no frame (§3): its index would
     * count what sibling threads did, and two handlers' sends would share
     * one anchor.  Its receipt is unanchored and named ({@code
     * RuntimeTraceContext#unanchored}).</p>
     *
     * @return the endpoint filed, or {@code null}
     */
    public static Endpoint messageSent(String nodeKey, String transport,
                                       String correlationId, String half,
                                       String site, Endpoint minted) {
        if (minted == null && !Lineage.named()) return null;
        Endpoint producer = minted != null ? minted
                : endpointAt(currentOccurrence(nodeKey), site, 0);
        if (producer == null) return null;
        Interactions.sent(Text.safe(transport), Text.safe(correlationId),
                Text.safe(half), producer);
        // A role occurrence (a response minted at its request's scope, a
        // send under no region) has no activation of its own; stated here,
        // the chain of whatever runs under this message goes on through the
        // sender its own anchor names (Arms.concurrent).
        if (producer.occurrence().role()) {
            RowRuntime.ambientActivation(producer.occurrence());
        }
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
                OccurrenceAddress.ROLE_REGION + kind.name(), here(kind),
                atScope());
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
     * opening entry carries its occurrence; a folded one ({@link #fold}) or
     * unnamed work's ({@link #occurrence}) carries none and is a marker that
     * keeps the region stack balanced.
     */
    private static final class Region {
        private final int base;
        private FrameJournal journal;
        /** The occurrence this entry opened, or null when it opened none. */
        private OccurrenceAddress occurrence;
        /** Whether unnamed work entered it, opening none ({@link #occurrence}). */
        private boolean unnamed;
        /**
         * Decisions per site on this OCCURRENCE ({@link #nextBranchOrdinal});
         * empty on a folded entry.
         */
        private Map<String, Integer> branchOrdinals =
                new HashMap<String, Integer>();
        /** The window {@link #branchOrdinals} were counted in. */
        private int window = RecordingWindow.index();
        /** The region this entry is of, "" on a fold's marker. */
        private String regionId = "";
        /** Its root activation's receiver: the node a hop's name states. */
        private Object receiver;
        /**
         * While a hop names this entry ({@link #hopOpened}), what it was
         * before, put back when the hop ends; null otherwise.
         */
        private Region before;
        /** The lineage token of the hop naming it. */
        private long namedBy;
        /**
         * The root hop this entry's occurrence was opened or named under:
         * its events count under it, whatever root hop opens inside it
         * ({@link State#countingRoot}).
         */
        private long root;

        private Region(int base) {
            this.base = base;
        }

        /** States which region's entry this is, and its root's receiver. */
        private void of(String regionId, Object receiver) {
            this.regionId = regionId;
            this.receiver = receiver;
        }

        /** Opens {@code address} under the hop {@code hop}: a new
         *  occurrence, so its decisions count from 1. */
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

        /** The hop ended: the entry is what it was before it. */
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

    public static void resetForTests() {
        CURRENT.remove();
        STARTS.clear();
        CLOCK = UNAVAILABLE;
        FrameJournal.resetForTests();
    }
}
