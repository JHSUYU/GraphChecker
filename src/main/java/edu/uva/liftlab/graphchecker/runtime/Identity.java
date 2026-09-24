package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The execution index of the running thread: one stack, O(1) per event.
 *
 * <p>IDENTITY-IMPL §B.  Every instrumented call site pushes a frame carrying
 * the iteration of the innermost loop enclosing it; a region entry reads the
 * frames from its scope root, and every event inside the region reads the
 * frames from the region entry.  The prefix hashes are folded incrementally
 * on push, so an id is constant-size and two replays compare by equality
 * rather than by walking two lists.</p>
 *
 * <p>What this replaces: "the k-th activation", "the k-th attach".  A flat
 * ordinal moves when an unrelated invocation is inserted anywhere earlier in
 * the run, which is precisely what a branch flip does; the point of an
 * execution index is that it does not.</p>
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
                    // A thread starts where it was created, as the scope
                    // does; the explicit carry is for a pool thread that was
                    // created before the work existed.
                    return parent == null ? new State() : parent.copy();
                }
            };

    /** Frame-level tokens: one per entered level, never reused. */
    private static final java.util.concurrent.atomic.AtomicLong TOKENS =
            new java.util.concurrent.atomic.AtomicLong(1L);

    private Identity() {
    }

    /**
     * One thread's index levels: the thread root and one level per frame.
     *
     * <p>A LEVEL is one entered frame and the events minted while it was the
     * innermost one.  IDENTITY-V3 §1 asks for a PEPID index -- a calling
     * context plus per-call-site iteration counts -- so a count belongs to
     * the level it was taken in and dies with it: the k of an event is the
     * k-th event at {@code site} in the enclosing LEVEL, under the root hop
     * that level is running in, and at nothing else ({@link
     * State#nextSiteEvent}).  A polling loop's extra calls are frames of
     * their own and cannot move a sibling's k.</p>
     *
     * <p>What this replaces: one counter map per THREAD, keyed by the
     * occurrence alone.  With frames only at region roots and work starts,
     * the balancer's {@code main} addressed every event it made outside a
     * region as ONE degraded occurrence {@code
     * balancer#epoch0/ROLE.CLIENT/Root:CLIENT#1/idx:} for the whole
     * process, so its {@code HADOOP_IPC#REQUEST} count was a run-length
     * ordinal over the process: the recording's {@code balance-block}
     * request was the 19th such send (@18) and the replay's the 23rd (@22),
     * because the replay's {@code main} polled {@code
     * MiniDFSCluster.waitActive} four more times first.  IDENTITY-V3 §1
     * forbids a run-length ordinal, and the frames of the whole
     * application scope are what replace it.</p>
     */
    private static final class State {
        /** The thread root, then one level per open frame, outermost last. */
        private final List<Level> levels = new ArrayList<Level>();
        /** Whether this thread has looked for the start that created it. */
        private boolean claimed;
        private int scopeBase;
        /**
         * Where the frame of the start this thread's work runs under sits,
         * or -1 on a thread that runs its own work.
         */
        private int startDepth = -1;
        /** The region activations open on this thread, innermost last. */
        private final List<Region> regions = new ArrayList<Region>();
        /**
         * Where the work this thread runs was started, as a reference the
         * attribution rule resolves when it is asked ({@link Attribution},
         * rule 3): the claimed start's, else the thread's creator's.
         */
        private Attribution.Reference starter;
        /** Whether {@link #starter} is a claimed start rather than the
         *  creator the thread inherited at construction. */
        private boolean adopted;

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
         * The same frame as an ADDRESS states it: a frame entered before the
         * recording window stands at iteration 0.
         *
         * <p>The window rule for frames, as {@link RecordingWindow} is for
         * counts and {@link RecordingWindow} for root k: an iteration
         * counted before the window is set-up history neither run controls.
         * hdfs-17899-bug1 is why: every DataXceiver thread inherits the main
         * thread's frames from DataNode start-up, {@code
         * instantiateDataNode} among them at the k-th DataNode started, and
         * which started DataNode plays the case's target is the cluster's
         * random block placement -- so the target's SASL response had the
         * producer endpoint {@code instantiateDataNode@0} in the recording
         * and {@code @1} in the replay, and the balancer's receive of it was
         * a different anchor in every run.</p>
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
            // The frames carry over -- a child thread's index continues its
            // parent's -- but not the counts: an event of the child is not
            // an event the frame the parent took its own counts in made.
            for (int index = 1; index < levels.size(); index++) {
                child.levels.add(new Level(levels.get(index).frame,
                        levels.get(index).token,
                        levels.get(index).receiver,
                        levels.get(index).window));
            }
            child.scopeBase = scopeBase;
            // The start frame of the work THIS thread runs is not the start
            // frame of the work the child will run: the child claims its
            // own, at the site that started it.
            child.claimed = false;
            child.startDepth = -1;
            // The thread was created HERE, by this thread's work: until it
            // claims a start of its own, that is what started it.  Read off
            // this state directly -- this runs inside the child's
            // construction, where no thread-local may be touched.
            child.starter = Attribution.Reference.of(receiversOf(this),
                    starter);
            child.adopted = false;
            for (Region region : regions) {
                // The depth carries over -- a child thread's frames continue
                // its parent's -- but not the journal: a journal is one
                // thread's clock readings in order, and a second writer would
                // interleave two threads' events into one sequence.
                child.regions.add(new Region(region.base));
            }
            return child;
        }

        /**
         * Opens the frame of the start this thread's work runs under.
         *
         * <p>The inherited stack GAINS one frame -- the start site and the
         * iteration of that start inside the starter's activation -- so two
         * siblings started from one site in one loop differ by it and by
         * nothing else (IDENTITY-V3 SS1, scope transfer).  It sits at the
         * boundary between the frames the starter stood on and the frames
         * the work itself pushes, which is where the start happened.</p>
         *
         * <p>Its level carries no token: nothing the work returns from
         * opened it, so no frame exit may close it.</p>
         */
        private void openStart(Frame frame, int startedIn) {
            // A pool thread that finished its last task drops that task's
            // start frame before it takes the next: the work that frame
            // named is over, and the next task was started elsewhere.  A
            // task started from inside another one nests instead.
            if (startDepth >= 0 && startDepth == depth() - 1) {
                levels.remove(startDepth + 1);
                // ...and the scope that task carried goes with its frame.
                RuntimeTraceContext.releaseCarried();
            }
            startDepth = depth();
            // The start was COUNTED where it was made, so its frame belongs
            // to that window, whenever the work claims it.
            levels.add(new Level(frame, 0L, null, startedIn));
        }

        /**
         * The frame depth an endpoint's site index is measured from: the
         * innermost region's, else the scope root's.
         *
         * <p>An occurrence with no region open -- a role occurrence, the
         * transport's own send and receive -- used to measure from the
         * thread base, so its endpoint ids carried the whole thread's
         * history: which pool handler served the message ({@code
         * Server.start#u31@k}) and how many calls the reader had queued
         * before it ({@code CallQueueManager.put#u7@k}), ordinals of the
         * thread and of the server, never of the message (IDENTITY-V3 §1).
         * hdfs-17960's recordings carried them in every response id and
         * matched by luck until the daemons took part; then a response's id
         * differed from the recording's with the same causal context, and
         * the client's every later message id cascaded after it.  The
         * scope root is where the message's own work begins ({@link
         * Identity#scopeStart}), and {@link Identity#atScope} already
         * measures the occurrence's index from it.</p>
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
         * The occurrence running on this thread right now, or null.
         *
         * <p>THE test the fold rule asks ({@link #occurrence}): an entry
         * opens an occurrence only when there is none.  A region entry
         * inherited across a thread boundary carries its DEPTH and not its
         * occurrence ({@link #copy}), so a child thread answers null here
         * and the first declared region it enters opens its own -- which is
         * what "an occurrence ends when execution crosses a thread or
         * process boundary" means (paper SS3.1.2).</p>
         */
        private Region activeRegion() {
            for (int index = regions.size() - 1; index >= 0; index--) {
                Region open = regions.get(index);
                if (open.occurrence != null) return open;
            }
            return null;
        }

        /**
         * Journals the frames now standing, for the VM's logged events.
         *
         * <p>Every open region, not only the innermost: an enclosing
         * activation's journal has to be current when a nested one returns
         * and its events start being stamped with the enclosing entry
         * again.  One clock reading serves them all -- it is the same
         * instant -- and each journal measures from its own entry.</p>
         */
        private void journal() {
            boolean journalled = false;
            for (int index = 0; index < regions.size(); index++) {
                if (regions.get(index).journal != null) journalled = true;
            }
            // Reading the clock costs a call into the VM, so a thread with no
            // journal of its own -- a child that inherited only the depth,
            // any thread outside a selected region -- never pays for it.
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
         * The k of one event at {@code site}: how many this level has
         * already made there, under the root hop it is running in.
         *
         * <p>THE counter.  A send, a read, a write, a region entry, a work
         * start and a frame entry are all events of the level they are made
         * in, and one of them is the k-th at its site or two of them share an
         * address.  Every caller comes through here so that the number the
         * recording states and the number a replay computes are the same
         * number for the same event.</p>
         *
         * <p>Keyed by (level, root hop, site) and by nothing else.  What this
         * replaces: a key that also carried the BUCKET the event was minted
         * in -- the open region's serial, else the degraded occurrence's
         * (node, role, causal context).  A causal context is read live from
         * {@link Lineage}, so the key of a count moved whenever the thread's
         * innermost anchor moved, and a frame entered under one anchor was
         * counted apart from the same site entered under another: hdfs-17960
         * verification #6 sent six {@code create-snapshots} RPCs from {@code
         * main} in one request and minted ONE producer endpoint for all six
         * ({@code 98ad5650d0490b91}, 46 sends over 28 ids, 158 downstream
         * {@code OCCURRENCE_ADDRESS_SHARED} rows), because the client's
         * response install leaves an anchored hop standing until the next
         * request is written, so every {@code Client.call} frame was counted
         * under the PREVIOUS response's anchor and its iteration restarted
         * at 0 while the endpoint was published under the request's own
         * {@code Root:CLIENT/create-snapshots#1}.  A counter keyed by what
         * the index is FOR cannot count the index.</p>
         *
         * <p>Two events of two occurrences at one site in one level are
         * still two events: they take k 0 and 1, and their occurrences
         * differ, so no two endpoints collide.  What the bucket was for --
         * two activations of one region counting apart -- is what the levels
         * already give, since every application-scope method opens one
         * (G11).</p>
         */
        private int nextSiteEvent(String site) {
            Map<String, Integer> events = top().events(Lineage.rootToken());
            Integer made = events.get(site);
            int iteration = made == null ? 0 : made;
            events.put(site, iteration + 1);
            return iteration;
        }

        private ExecutionIndex from(int base) {
            int start = Math.max(0, Math.min(base, depth()));
            if (start >= depth()) return ExecutionIndex.empty();
            List<Frame> standing = new ArrayList<Frame>(depth() - start);
            for (int index = start; index < depth(); index++) {
                standing.add(addressedFrame(index));
            }
            return ExecutionIndex.of(standing);
        }
    }

    /** One level of the index: an entered frame and the events under it. */
    private static final class Level {
        /** The frame this level was entered with, or null on the root. */
        private final Frame frame;
        /** The token the frame exit closes this level by, or 0. */
        private final long token;
        /**
         * The receiver of the activation this level is, or null: what the
         * attribution rule asks is registered ({@link Attribution}, rule 2).
         */
        private final Object receiver;
        /**
         * This level's site counts, one map per root hop it has been the
         * innermost level under, outermost hop first.
         *
         * <p>THE lifetime rule: a level's counters live for the level's
         * lifetime WITHIN one root hop.  A woven frame's exit drops its
         * level and its counts with it; the thread base level has no frame
         * to close it, so the root hop is what ends its counts -- the next
         * request is a new root occurrence and its k starts again.  Without
         * that, main's base level would count for the whole thread and the
         * k of a send would be a run-length ordinal over the process, which
         * IDENTITY-V3 SS1 forbids.</p>
         *
         * <p>One map per hop rather than one map cleared on each: a root hop
         * opened INSIDE this level -- hdfs-11741's {@code KEY_MANAGER_TICK}
         * rotations, opened on the balancer's {@code main} inside {@code
         * balance-block#1} -- must not move the enclosing hop's counts, and
         * hands them back untouched when it closes.  That is what separated
         * this from the scope TOKEN a former implementation keyed on: a
         * scope token changes every time a scope is entered and left, which
         * on that {@code main} is at every request it sends, so the
         * enclosing level's count restarted mid-run and two {@code
         * Balancer.runOneIteration} calls of one request both stood at
         * iteration 0.  A ROOT hop does not move while the occurrence does
         * not.</p>
         */
        private final List<Counters> counters = new ArrayList<Counters>();

        /**
         * The window {@link #frame} was entered in ({@link RecordingWindow}).
         * A frame entered before the window stands in no in-window address
         * with the iteration it was counted at ({@link State#from}).
         */
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
         * This level's counts under the root hop {@code rootToken}.
         *
         * <p>What is filed for a hop that has CLOSED goes with it, here,
         * where the level is next read: a level that outlives a hop does not
         * outlive that hop's counts, and nothing filed for a closed hop can
         * be reached again because a hop token is never reused.  Dropping it
         * on the spot is also what keeps a level that outlives thousands of
         * hops -- a pool thread's start level -- from holding one map per
         * task it ever ran.</p>
         */
        private Map<String, Integer> events(long rootToken) {
            for (int index = counters.size() - 1; index >= 0; index--) {
                Counters filed = counters.get(index);
                if (filed.rootToken == rootToken) {
                    // Every hop filed above this one was opened inside it
                    // and has closed, so its counts go with it.
                    while (counters.size() > index + 1) {
                        counters.remove(counters.size() - 1);
                    }
                    // Counted before the recording window opened: what the
                    // hop made there is nothing either run states
                    // ({@link RecordingWindow}), so it counts again from here.
                    if (filed.window != RecordingWindow.index()) {
                        filed = new Counters(rootToken);
                        counters.set(index, filed);
                    }
                    return filed.events;
                }
                // A hop still open is an ENCLOSING one, and its counts stand:
                // the turns of a tick opened inside a request cannot move the
                // request's k, nor the request's the tick's.
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
     *
     * <p>A start is not an event of the thread that runs the work: it is an
     * event of the STARTER, at the starter's call site and inside the
     * starter's activation.  The frame is computed there, filed under the
     * Thread or the task the start named, and taken by the work when it
     * runs -- which is the only way a child can carry it, since a thread
     * inherits its creator's state when it is CONSTRUCTED and the start
     * happens afterwards.</p>
     */
    private static final Map<Carrier, Start> STARTS =
            new ConcurrentHashMap<Carrier, Start>();

    /**
     * One filed start: where it was made, and on which node.
     *
     * <p>The node travels with the frame because it is the same fact about
     * the same event.  A thread whose own frames name no component belongs
     * to the component that STARTED it -- the DataNode whose
     * BPServiceActor this is -- and that is a statement of the recording
     * and of every replay alike, not an inference over the graph.</p>
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
     * One pending start's carrier, held weakly and keyed by identity.
     *
     * <p>Weakly, so a submission nothing ever runs is collected rather than
     * retained for the run; by identity, because two equal task objects are
     * two submissions and the frame of one is not the frame of the
     * other.</p>
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
     * This thread's state, having claimed the start that created it once.
     *
     * <p>THE claim rule, one half of it: a started work claims its start
     * frame at its FIRST identity event on that thread -- a region entry, a
     * message send, a read or write endpoint, another work start, whatever
     * comes first.  Every one of them reaches this method before it answers
     * anything ({@link #currentOccurrence}, {@link #occurrence}, {@link
     * #endpointAt}, {@link #enterFrame}, {@link #startWork}), so the frame is
     * standing before the first address that would otherwise be computed
     * without it.  The claim is lazy for exactly that reason: the start is
     * filed after this thread's state was inherited (at construction) and
     * before the thread runs anything.</p>
     *
     * <p>This half takes the start filed for the THREAD -- a {@code
     * Thread.start}, where the thread is the work.  The other half is {@link
     * #claimStart}, for work whose carrier is a task object the thread never
     * sees through an event of its own: that claim is woven at the entry of
     * the functional method the start named, which is the work's own first
     * instruction.  Before this, the task claim happened only at a region
     * entry, and hdfs-11741's mover pool threads send the balancer's
     * HDFS_SASL request before entering any region -- so two mover tasks
     * stood on one empty index under one degraded {@code ROLE.HDFS_SASL}
     * occurrence, each counted its site events from 0 in its own state, and
     * the two sends carried ONE producer endpoint id.</p>
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
        // The scope the starter was in comes with the work, whatever thread
        // the pool hands it to: installed here, closed when the work's start
        // level goes (#exitFrame, State#openStart).
        RuntimeTraceContext.claimCarried(carrier);
    }

    /**
     * Files the frame of one {@code Thread.start} or work submission.
     *
     * <p>The iteration is the k-th start AT THIS SITE in the level that
     * makes it -- the one counter every other event is counted by ({@link
     * State#nextSiteEvent}) -- so two siblings started from one site in one
     * loop differ by it and by nothing else (IDENTITY-V3 SS1: "two siblings
     * started from one site in one loop differ by the loop iteration of the
     * start site").  It is a structural count of starts, never a thread id,
     * an address or a session ordinal.</p>
     *
     * <p>Two starts made at one site from two activations of a CALLER are
     * two levels, because every method of the application scope enters one
     * (G11).  A caller outside that scope shares the thread base level with
     * its siblings, and two starts it makes at one site inside one root hop
     * are the 0th and the 1st there.  Two under DIFFERENT root hops are
     * both the 0th -- their root occurrences differ, so their addresses do
     * -- and two the index cannot separate at all are a shared endpoint id
     * and a named refusal at the mint, never a renumbering here.</p>
     */
    public static void startWork(String startSiteId, Object carrier) {
        String site = JvmNames.stable(Text.safe(startSiteId));
        if (site.isEmpty() || carrier == null) return;
        // A START MADE BY A THREAD WITH NO IDENTITY FILES NO FRAME.  The k
        // of a start is the k-th start of that site in the level that makes
        // it, within one root hop; a thread under no root hop -- a
        // DataNode's connection acceptor, created at start-up and never
        // ticked -- has one level for its whole life, so its k is the count
        // of connections it has accepted, an ordinal of arrivals nothing
        // schedules.  hdfs-11741 v30: the balance-block's DataXceiver on dn1
        // was Daemon.start#u5@1 in the recording and @0 in the replay, on
        // which mover's connection the acceptor met first.  Its identity is
        // its own turn (Root:DATA_XCEIVER#k) and the message its handshake
        // serves, as it was before the acceptor's start was woven.
        if (contextHere().isLost()) return;
        State state = state();
        int iteration = state.nextSiteEvent(site);
        sweep();
        // The scope this start was made in travels with the work
        // (RuntimeTraceContext#claimCarried takes it back at the claim).
        RuntimeTraceContext.captureAsync(carrier);
        STARTS.put(new Carrier(carrier, COLLECTED),
                new Start(Frame.of(site, iteration), Attribution.capture()));
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
        return receivers;
    }

    /**
     * Takes the start frame filed for {@code carrier}, if there is one.
     *
     * <p>The other half of {@link #startWork}: a thread claims the start
     * filed for ITSELF the first time it does anything ({@link #state}), and
     * work whose carrier is a task object claims the start filed for that
     * task at its own first instruction -- the entry of the functional
     * method the start named, woven by {@code
     * CausynthPipeline.claimWorkEntry} in BOTH passes over the same
     * {@code WorkStartSites} list the filing half reads.</p>
     *
     * <p>One claim point per notion.  It used to be the region entry as
     * well, which is neither first nor reached at all on a pool thread whose
     * task enters no selected region.</p>
     *
     * <p>A thread nobody filed a start for -- started before the recording
     * began, or from JDK code the weave cannot touch -- claims nothing and
     * keeps the role occurrence it has today.  Two of its events that the
     * index cannot separate then share one endpoint id, which is a named
     * refusal at the mint (LINEAGE_LOST, DIAGNOSTIC: {@code
     * CausynthTraceRecorder.refuseSharedProducer} for a message, {@code
     * RowRuntime.distinct} for a read or write) and not a frame invented
     * here.</p>
     */
    public static void claimStart(Object carrier) {
        if (carrier == null || STARTS.isEmpty()) return;
        adopt(state(), carrier);
    }

    /** Drops the entries of carriers nothing runs any more. */
    private static void sweep() {
        for (Reference<?> dead = COLLECTED.poll(); dead != null;
                dead = COLLECTED.poll()) {
            STARTS.remove(dead);
        }
    }

    /**
     * Enters the index frame of ONE application-scope method activation.
     *
     * <p>THE frame rule, and there is no second one: every method of the
     * application scope opens a level at its entry and closes it at every
     * exit, in BOTH passes, from the one weave walk
     * ({@code CausynthPipeline.instrumentApplicationScope}).  The calling
     * context of an event is then the frames of the application methods it
     * is inside, which is what IDENTITY-V3 §1 asks a LocalExecutionIndex to
     * be (Execution Indexing / PEPID) and what the region-root-only frame
     * rule could not give: a thread outside every region had an EMPTY
     * calling context, so its site counts were run-length ordinals over the
     * process.</p>
     *
     * <p>The frame's iteration is the k-th entry of THIS site in the level
     * that ENCLOSES it: a method entry is an event of that level, counted
     * by the one counter every other event is counted by ({@link
     * State#nextSiteEvent}).  A loop body re-entering the same call site is
     * that site at iteration 1, 2, 3 -- which is what the innermost
     * enclosing loop's iteration count means -- and one rule computes it in
     * the recording and in the replay alike.  A caller the weave does not
     * reach (a test method, JDK code) opens no level, so its calls are
     * counted in the thread base level and advance {@code @0, @1, @2}
     * there: that is what separates the six {@code create-snapshots} RPCs
     * hdfs-17960's {@code main} sends at one transport site.</p>
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
        return token;
    }

    /**
     * Leaves the level {@code token} opened, and every level opened inside
     * it that a non-local exit left behind.
     *
     * <p>The token is a local of the woven frame, so recursion holds a
     * different one at every depth and the exit closes the entry that token
     * owns rather than whatever the runtime finds innermost.  A level the
     * token does not name -- the start frame of the work this thread runs,
     * which no call of that work pushed -- is never closed here.</p>
     */
    public static void exitFrame(long token) {
        if (token <= 0L) return;
        State state = state();
        for (int index = state.levels.size() - 1; index >= 1; index--) {
            if (state.levels.get(index).token != token) continue;
            while (state.levels.size() > index) {
                state.levels.remove(state.levels.size() - 1);
            }
            if (state.startDepth >= state.depth()) {
                // The start frame was inside the level that just closed, so
                // the work it named is over with it -- and so is the scope it
                // carried.
                state.startDepth = -1;
                RuntimeTraceContext.releaseCarried();
            }
            // The scope root is the deepest level the scope start and this
            // point still SHARE.  A scope is opened inside a call that
            // returns -- CausynthMessagePropagation.inbound opens the scope
            // of a served message and hands control back to the handler --
            // and an index measured from a level that has gone is empty:
            // on hdfs-11741 the four PBHelper.convert activations of one
            // refresh answered one address, which is the collision the
            // index exists to prevent.  It is also what puts an ANCHOR
            // hop's base on the handler's own level: the inbound scope is
            // opened one level down, inside the propagation call, and this
            // brings it back to the level the served api is entered at.
            if (state.scopeBase > state.depth()) {
                state.scopeBase = state.depth();
            }
            state.journal();
            return;
        }
    }

    /**
     * What opened the causal context whose index begins at a scope start.
     *
     * <p>THE key of the one scope-base rule ({@link #scopeStart}).  An
     * occurrence's execution index is relative to its causal context's own
     * ORIGIN, and which point on the thread that is depends on what opened
     * the context -- so every door states its kind and there is nothing
     * left for the rule to infer from the stack.</p>
     */
    public enum Hop {
        /**
         * An inbound request, paired to its producer endpoint by
         * {@code RuntimeTraceContext.enterInbound}.
         *
         * <p>The origin is the inbound scope itself.  The frames ABOVE it
         * are the carrier thread's -- the pooled handler's start frame,
         * {@code Server$Handler.run}, {@code RpcCall.run}, an executor's
         * frames -- and which pooled handler serves a request is
         * scheduling, not identity: hdfs-17960 planned every activation
         * under {@code Anchor:...@HADOOP_IPC/checkpoint-namespace} from
         * {@code <org.apache.hadoop.ipc.Server: void start()>#u31@3}, ran
         * it on handler 0 and refused 14 tasks at frame 0.  The anchor
         * already identifies the request; the carrier does not enter into
         * it.</p>
         */
        ANCHOR,
        /**
         * A scope the running thread opens for itself: the workload's own
         * request ({@code beginRequest}) or the scope carried to the
         * thread that runs the work ({@code enterCarriedScope}).
         *
         * <p>The origin is that scope's start.  A claimed start frame
         * standing above it is the ROOT's -- the frame that tells two
         * started siblings apart -- and not the request's, so it stays out
         * of the request's index exactly as a handler's does.</p>
         */
        SCOPE_ROOT,
        /**
         * A root that IS the started work: a daemon tick
         * ({@code beginTick}).
         *
         * <p>The origin is the start frame the work claimed, because that
         * frame is the tick's own beginning rather than some carrier's:
         * hdfs-11741's {@code KeyManager$BlockKeyUpdater} claims it at its
         * entry and a base below it drops the start site and its iteration
         * from every address the tick publishes, so two pooled tasks would
         * be one occurrence (G10/G11).  A tick on a thread nobody filed a
         * start for -- the balancer's {@code main}, which drives its own
         * {@code KEY_MANAGER_TICK} rotations -- has no such frame and
         * begins where it was opened; two of its turns are told apart by
         * the window index of the root hop, which is what a {@code Root}
         * context states.</p>
         */
        STARTED_ROOT
    }

    /**
     * Opens a scope: the execution index of what runs inside starts here.
     *
     * <p>THE scope-base rule, and there is no second one: the execution
     * index of an occurrence is relative to its causal context's own
     * origin.  A {@link Hop#STARTED_ROOT}'s origin is the start frame its
     * work claimed; every other context's origin is the point the scope
     * was opened at, and the frames above that point belong to the thread
     * that carried the work there rather than to the work.</p>
     *
     * <p>What this replaces: "never above the start frame this thread's
     * work already claimed", which was written for the tick and applied to
     * every hop, so the pooled handler that happened to serve a request
     * became part of the request's address (hdfs-17960 verification #5,
     * 14 REPLAY refusals at {@code <org.apache.hadoop.ipc.Server: void
     * start()>#u31}, planned at iteration 3 and run at 0).  One rule keyed
     * on the hop, called through the same doors by the recording and by
     * the replay ({@code RuntimeTraceContext}).</p>
     */
    public static int scopeStart(Hop hop) {
        if (hop == null) {
            throw new IllegalArgumentException(
                    "a scope start states which hop opens it");
        }
        State state = state();
        int before = state.scopeBase;
        state.scopeBase = hop == Hop.STARTED_ROOT && state.startDepth >= 0
                ? Math.min(state.startDepth, state.depth())
                : state.depth();
        return before;
    }

    /**
     * Puts back the scope root a hop replaced, when the hop ends.
     *
     * <p>A HOP'S SCOPE ROOT LASTS AS LONG AS THE HOP.  A served message's
     * root was set and never put back: once the message's scope had ended
     * the root stayed where the message had opened it, the frame exit's
     * clamp then moved it up to the thread's base, and every later
     * occurrence of that thread lost the frames that name the thread -- its
     * claimed start above all.  hdfs-17899 bug2's three SPS-node threads
     * each carried their start frame on their first RPC and none after, so
     * their k-th calls shared one address (PLAN OCCURRENCE_ADDRESS_SHARED,
     * six of them).</p>
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
     * Files the innermost open region's journal under the VM's own key.
     *
     * <p>The key is the region-enter event id the VM stamps on every version
     * and every read it logs from inside this activation, so an event and the
     * frames it stood on are joined by the VM's statement rather than by the
     * runtime guessing which activation was live.</p>
     *
     * <p>A FOLDED entry keys a journal of its own -- the VM numbers its
     * region entry whether or not this class opens an occurrence for it --
     * and that journal measures from the base of the occurrence the entry
     * folded into, which is the occurrence that performed the events it
     * holds ({@link #fold}).</p>
     */
    public static void regionKey(long vmRegionEnterEventId) {
        State state = state();
        Region region = state.region();
        if (region == null || vmRegionEnterEventId <= 0L) return;
        region.journal = FrameJournal.open(vmRegionEnterEventId,
                state.snapshot(region.base));
    }

    /**
     * Closes the innermost open region entry.
     *
     * <p>One pop per entry, folded or not: a folded entry pushed a marker
     * ({@link #fold}) and this pops that marker, so the exit hook of a region
     * that was folded cannot close the occurrence it folded into.  Only the
     * entry that opened an occurrence pops the region that carries it.</p>
     *
     * <p>No counter cleanup, and nothing here to clean: counts live in the
     * levels, keyed by (level, root hop, site), and a region holds none.
     * Two activations of one region count apart because each entered its
     * region root's own level (G11), and the level drops its counts when
     * the frame that opened it exits.  What this replaces: deleting the
     * closing occurrence's counter bucket from a thread-wide map, which had
     * to run at exactly the right region depth or it renumbered the
     * enclosing occurrence's events
     * (ConcolicRegionRuntime#popActiveRegion).</p>
     */
    public static void regionExit() {
        State state = state();
        if (state.regions.isEmpty()) return;
        state.regions.remove(state.regions.size() - 1);
    }

    /**
     * The ordinal of one decision at {@code site} in the occurrence running
     * here, or {@code 0} when this thread is running none.
     *
     * <p>I3 -- ROWS AND ORDINALS BELONG TO THE PERFORMER.  A decision row is
     * addressed by the occurrence that performed the branch, so its site
     * ordinal is counted on THAT occurrence: the count lives beside the
     * address, on the region entry that opened it, and every entry folded
     * into it ({@link #fold}) goes on counting there.  Counted per
     * ACTIVATION instead, two selected activations that fold into one
     * occurrence each start at 1 and two rows collide at (occurrence, site,
     * ordinal) -- which is the pair an obligation's flip is addressed
     * by.</p>
     *
     * <p>1-based, because an obligation's {@code ordinal} is: the first
     * decision of a site in an occurrence is its first.</p>
     */
    public static int nextBranchOrdinal(String site) {
        State state = state();
        Region running = state.activeRegion();
        if (running == null) return 0;
        String key = Text.safe(site);
        // The same window rule as every other count ({@link RecordingWindow}): an
        // activation that straddles the window's opening numbers its
        // decisions from there.
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
     * How many regions this thread has open: the other stack to balance.
     *
     * <p>{@link #depth} counts frames and {@link #regionExit} pops regions,
     * so a region popped without a push leaves the frame count right and
     * this one wrong -- and it is this stack that decides which occurrence
     * an event belongs to ({@link #currentOccurrence}) and which frame the
     * site index of its endpoints is measured from ({@link #siteIndex}).
     * An activation that closes at a region depth other than the one it
     * opened at must be refused, exactly as an unbalanced frame is.</p>
     */
    public static int regionDepth() {
        return state().regions.size();
    }

    /**
     * The causal context the running thread is in right now, by the one
     * rule ({@link #here(Role)}).
     */
    public static CausalContext contextHere() {
        return here(Lineage.named() ? Lineage.role() : Role.UNKNOWN);
    }

    /**
     * The id of the occurrence running on this thread, or {@code ""}: where a
     * message door stands ({@code contract.DoorRow}).
     */
    public static String innermostRegionId() {
        State state = state();
        Region running = state.activeRegion();
        return running == null || running.occurrence == null ? ""
                : running.occurrence.id();
    }

    /** The innermost open region's occurrence, for a report, or {@code ""}. */
    public static String innermostRegion() {
        State state = state();
        for (int index = state.regions.size() - 1; index >= 0; index--) {
            OccurrenceAddress occurrence = state.regions.get(index).occurrence;
            if (occurrence != null) return occurrence.render();
        }
        return "";
    }

    /**
     * The address of the activation entering here (IDENTITY-IMPL A).
     *
     * <p>THE one computation of an occurrence address, and there is no
     * second one.  The recording calls it on the stock JDK from the trace
     * recorder's own method hook, and the replay calls it on the custom VM
     * from the region hook; both read the frame stack and the scope this
     * class maintains, so the address the SEED trace carries and the address
     * a replay computes for the same occurrence are the same string by
     * construction rather than by reconciliation.  An offline pass over
     * trace rows never re-derives it: it reads what the recording
     * stated.</p>
     *
     * <p>{@code null} when this run can name no node to put the occurrence
     * on -- a guessed node is a wrong causal chain.</p>
     *
     * @param open whether this is a region ENTRY -- which opens an occurrence
     *             when the thread runs none and is folded into the running
     *             one when it does ({@link #fold}) -- or only a read (the
     *             recording and admission, which must not move the base the
     *             endpoints of an already-open region are indexed from)
     */
    public static OccurrenceAddress occurrence(String nodeKey, String regionId,
                                               boolean open) {
        String node = Text.safe(nodeKey);
        if (node.isEmpty() || Text.safe(regionId).isEmpty()) {
            return null;
        }
        if (open) {
            OccurrenceAddress enclosing = fold();
            if (enclosing != null) return enclosing;
        }
        ExecutionIndex index = open ? regionEnter() : atScope();
        OccurrenceAddress address = OccurrenceAddress.of(
                NodeId.parse(Text.safe(nodeKey)), Text.safe(regionId),
                here(Lineage.rootRole()), index);
        if (open) {
            State state = state();
            Region region = state.region();
            if (region != null) region.occurrence = address;
        }
        return address;
    }

    /**
     * Folds one declared region entry into the occurrence already running.
     *
     * <p>THE FOLD RULE (paper SS3.1.2: sites connected by synchronous calls
     * are one region, and an occurrence ends only when execution crosses a
     * thread or process boundary).  A declared region method called
     * synchronously inside another region's occurrence opens NO occurrence
     * of its own: its entry is folded, and every site executed below it --
     * decisions, reads, writes, exports, attaches, hook mints -- is an event
     * of the occurrence that was already running.  A declared region opens
     * its own occurrence only on a thread where none is.</p>
     *
     * <p>Decided by the CALL STACK and by nothing else: which obligation a
     * replay focuses, which task a plan named, what a region is called -- all
     * out.  So the recording and the replay fold at the same entries, which
     * they must, because the plan names the occurrences the replay is asked
     * to open ({@code CausynthTraceRecorder#enterMethod} and {@code
     * ConcolicRegionRuntime#enterRegionEntry} both reach this one function).
     * Before this, dn1's {@code addKeys} (REGION.ba3902cd) calling {@code
     * removeExpiredKeys} (REGION.094a8e3d) opened a NESTED occurrence
     * {@code 845fa3841a35af67} inside one synchronous call.</p>
     *
     * <p>OWNERSHIP is the pushed marker.  A folded entry still pushes a
     * region -- with the enclosing occurrence's base and no occurrence of its
     * own -- so the one exit hook that pairs with this entry pops the marker
     * and cannot close the occurrence it folded into.  An entry that OPENS
     * an occurrence is the only entry whose exit closes one, and the two
     * stacks stay balanced for the check {@code
     * ConcolicRegionRuntime#closeRegionEntry} makes.</p>
     *
     * <p>The folded region's base is the enclosing entry's, so the site
     * index of an event below it -- and the frames its journal hands the VM's
     * logged events -- are measured from the occurrence that performed it
     * (IDENTITY-IMPL SSA).  The enclosing occurrence's own address does not
     * move: nothing is pushed above its base and its address was minted when
     * it was entered.</p>
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
     * Whether the region entry standing on this thread was FOLDED.
     *
     * <p>F1 -- A FOLDED ENTRY IS NOT AN ENTRY OF AN OCCURRENCE, it is a
     * method call inside the one already running, so neither pass records an
     * activation for it: the recording states no occurrence address on its
     * trace row ({@code CausynthTraceRecorder#enterMethod}) and the replay
     * starts no ActiveRegion at it ({@code
     * ConcolicRegionRuntime#enterRegionFrame}).  What remains is the marker
     * this class pushed, so the two index stacks balance and the fold's own
     * exit closes nothing ({@link #fold}).</p>
     *
     * <p>Asked at the entry, where the marker is innermost -- both hooks sit
     * at one Java entry and the region entry hook runs first.  It stays true
     * for everything executed below that entry, which is the same statement:
     * no activation is started while the innermost entry on this thread is a
     * fold, so one occurrence has one activation.</p>
     */
    public static boolean foldedEntry() {
        State state = state();
        Region innermost = state.region();
        return innermost != null && innermost.occurrence == null
                && state.activeRegion() != null;
    }

    /**
     * The occurrence an event on this thread belongs to.
     *
     * <p>The innermost region activation open here, whose address was filed
     * when it was entered by {@link #occurrence} -- in the recording and in
     * a replay alike, because both open their regions through that one
     * call.  Outside every region it is the degraded role occurrence, which
     * is still an occurrence an endpoint can be keyed by (INTERACTION-ID
     * R-I1).</p>
     */
    public static OccurrenceAddress currentOccurrence(String nodeKey) {
        State state = state();
        for (int index = state.regions.size() - 1; index >= 0; index--) {
            OccurrenceAddress occurrence = state.regions.get(index).occurrence;
            if (occurrence != null) return occurrence;
        }
        return roleOccurrence(nodeKey,
                Lineage.named() ? Lineage.role() : Role.UNKNOWN);
    }

    /**
     * THE endpoint of one event: where it happened, in which occurrence.
     *
     * <p>IDENTITY-IMPL §A: (occurrence, site, site-local execution index,
     * attempt).  One computation for both passes, as the occurrence address
     * is: a producer endpoint the recording mints and a producer endpoint a
     * replay mints are the same string for the same event, which is what
     * lets the causal context of everything downstream of a message be the
     * SAME context in the two passes.  Before this, the recording minted
     * its senders from a degraded role occurrence (or, behind a session
     * guard, not at all) and the replay from its live activation, so the
     * anchor of every occurrence a message started drifted -- hdfs-17960's
     * two FSImageSaver activations were planned at {@code
     * Anchor:...@THREAD_START} and ran at {@code
     * Anchor:...@HADOOP_IPC/checkpoint-namespace}.</p>
     */
    public static Endpoint endpoint(String nodeKey, String site, int attempt) {
        return endpointAt(currentOccurrence(nodeKey), site, attempt);
    }

    /**
     * The same endpoint, for an occurrence the caller already holds.
     *
     * <p>The site is put in its stable spelling ONCE, here, and the index
     * is taken over that same string: a class the JVM minted per run is not
     * an identity ({@link JvmNames#stable}), and the site of an endpoint
     * and the innermost frame of its index are the same site.</p>
     */
    public static Endpoint endpointAt(OccurrenceAddress occurrence,
                                      String site, int attempt) {
        if (occurrence == null) return null;
        String stable = JvmNames.stable(Text.safe(site));
        return Endpoint.of(occurrence, stable,
                eventSiteIndex(occurrence, stable), attempt);
    }

    /**
     * The site-local index of the event minting an endpoint HERE, with the
     * event itself as the innermost frame.
     *
     * <p>IDENTITY-V3 §1: an Endpoint is (occurrence, site, site-local
     * execution index, attempt), and two events of one occurrence at one
     * site are two points of its control structure.  Without the innermost
     * frame they share one endpoint id -- which is what RowInvariants:337
     * states as "invariant 4 site index missing ... 2 events of this site in
     * one occurrence share one endpoint id" and says is the identity's to
     * fix with no ordinal and no counter of the session's.  The count is
     * the enclosing LEVEL's ({@link State#nextSiteEvent}), keyed by (level,
     * root hop, site): it starts at zero in that calling context under that
     * root and is therefore the same number in the recording and in a
     * replay of it, whatever else the thread it ran on did.  Two sends made
     * inside ONE activation of the transport site's caller advance k there;
     * two sends made from two activations differ by that caller's own frame
     * iteration instead, which is the same count taken one level up.</p>
     */
    private static ExecutionIndex eventSiteIndex(OccurrenceAddress occurrence,
                                                 String site) {
        State state = state();
        String key = JvmNames.stable(Text.safe(site));
        if (key.isEmpty()) return state.from(state.regionBase());
        int iteration = state.nextSiteEvent(key);
        List<Frame> frames = new ArrayList<Frame>(
                state.from(state.regionBase()).frames());
        frames.add(Frame.of(key, iteration));
        return ExecutionIndex.of(frames);
    }

    /**
     * Files the producer endpoint of one whole message, for the anchor its
     * receiver states (IDENTITY-IMPL §C).
     *
     * <p>The endpoint itself comes back, not its digest: the caller states
     * the four components this mint was given -- which occurrence sent the
     * message, at which transport site, the k-th event of that occurrence
     * there, and the attempt -- so the trace row and a refusal spell out
     * what the anchor is a digest OF.</p>
     *
     * @return the endpoint filed, or {@code null}
     */
    public static Endpoint messageSent(String nodeKey, String transport,
                                       String correlationId, String half) {
        Endpoint producer = endpoint(nodeKey,
                Text.safe(transport) + "#" + Text.safe(half), 0);
        if (producer == null) return null;
        Interactions.sent(Text.safe(transport), Text.safe(correlationId),
                Text.safe(half), producer);
        return producer;
    }

    /**
     * The address of work that ran under no region this plan selected: its
     * role, on its node, at its index from the scope root -- the one
     * scope-base rule ({@link #scopeStart}), as a region's is.  Measured
     * from the thread's first frame instead, a response the pooled handler
     * sent outside every region carried that handler's start iteration
     * ({@code Server.start()#u31@N}), and hdfs-17960's replay -- one
     * heartbeat shifting the handler rotation -- anchored the client's
     * next request on an endpoint the recording never minted.
     *
     * <p>REPORT-ENTRY §4: the region slot carries a role id rather than a
     * plan region, so a reader tells an ambient occurrence from a planned
     * one by the visible {@code ROLE.} prefix.  An activation no PLAN
     * selected is not an activation with no CONTEXT: the message that opened
     * its scope, or the root it descends from, is known exactly as it is for
     * a selected one.</p>
     */
    public static OccurrenceAddress roleOccurrence(String nodeKey, Role role) {
        if (Text.safe(nodeKey).isEmpty()) return null;
        Role kind = role == null ? Role.UNKNOWN : role;
        return OccurrenceAddress.of(NodeId.parse(Text.safe(nodeKey)),
                "ROLE." + kind.name(), here(kind), atScope());
    }

    /**
     * The context the running thread is in, by the one rule.
     *
     * <p>{@code role} is what the thread degrades to when nothing can be
     * attributed at all ({@link CausalContext.Lost}).  A ROOT context takes
     * its role, its api and its k from the root hop itself -- the innermost
     * one, so a daemon tick opened inside a request descends from the tick
     * -- because those three are one fact: {@code Lineage.push} counts the
     * k per (node, role, api).</p>
     */
    private static CausalContext here(Role role) {
        return context(Lineage.anchor(), Lineage.rpcSite(),
                Lineage.rootRole(), Lineage.rootApi(),
                Lineage.rootWindowIndex(), role);
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
        // No arm for "started by a submission".  A thread start is not a
        // message: the work runs inside the scope its starter was in, whose
        // anchor is the arm above, and two siblings started from one site
        // are told apart by the start-site FRAME in the index (#startWork,
        // REPORT-P2H) rather than by a second context form.  The arm that
        // used to stand here fired only in the recording -- the replay
        // always had the scope's anchor by then -- so one occurrence
        // carried two contexts.
        if (role != null && !Role.UNKNOWN.equals(role)
                && windowIndex > 0) {
            return CausalContext.of(role, api, windowIndex);
        }
        return CausalContext.of(unattributed == null
                ? Role.UNKNOWN : unattributed);
    }

    /**
     * The VM's session event clock, which the frame journal samples.
     *
     * <p>Installed by the runtime that owns the VM bindings: this package
     * states identity and holds no reflective view of the engine, and a run
     * with no such clock journals nothing rather than inventing readings.</p>
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

    /**
     * One open region entry: where its endpoints are indexed from.
     *
     * <p>Two kinds, one stack.  An entry that OPENED an occurrence carries
     * it; an entry that was FOLDED into the occurrence already running
     * ({@link #fold}) carries none and inherits the opener's base, so it is
     * a pure ownership marker: its exit pops it and closes nothing.</p>
     */
    private static final class Region {
        private final int base;
        private FrameJournal journal;
        /**
         * The occurrence this entry opened, or null when it was folded into
         * the one already running on this thread.
         */
        private OccurrenceAddress occurrence;
        /**
         * How many decisions this OCCURRENCE has taken at each site, for the
         * ordinal its rows carry ({@link #nextBranchOrdinal}).  Empty on a
         * folded entry: it counts on the occurrence it folded into.
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
