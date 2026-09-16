package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
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
     * the frame it was taken in and dies with it: the k of an event is the
     * k-th event at (enclosing occurrence, site) INSIDE its enclosing
     * frame.  A polling loop's extra calls are frames of their own and
     * cannot move a sibling's k.</p>
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
        /** How many regions have been opened on this thread. */
        private int regionsOpened;
        /**
         * The node of the frame that started the work this thread runs, or
         * {@code ""}: the component an occurrence belongs to when its own
         * frames name none.
         */
        private String startNode = "";

        private State() {
            levels.add(new Level(null, 0L));
        }

        /** How many frames are standing. */
        private int depth() {
            return levels.size() - 1;
        }

        /** The frame at depth {@code index}, counted from the thread root. */
        private Frame frame(int index) {
            return levels.get(index + 1).frame;
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
                        levels.get(index).token));
            }
            child.scopeBase = scopeBase;
            // The start frame of the work THIS thread runs is not the start
            // frame of the work the child will run: the child claims its
            // own, at the site that started it.
            child.claimed = false;
            child.startDepth = -1;
            child.startNode = "";
            for (Region region : regions) {
                // The depth carries over -- a child thread's frames continue
                // its parent's -- but not the journal: a journal is one
                // thread's clock readings in order, and a second writer would
                // interleave two threads' events into one sequence.
                child.regions.add(new Region(region.base, region.key));
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
        private void openStart(Frame frame) {
            // A pool thread that finished its last task drops that task's
            // start frame before it takes the next: the work that frame
            // named is over, and the next task was started elsewhere.  A
            // task started from inside another one nests instead.
            if (startDepth >= 0 && startDepth == depth() - 1) {
                levels.remove(startDepth + 1);
            }
            startDepth = depth();
            levels.add(new Level(frame, 0L));
        }

        /** The frame depth an endpoint inside the innermost region is from. */
        private int regionBase() {
            return regions.isEmpty() ? 0
                    : regions.get(regions.size() - 1).base;
        }

        private Region region() {
            return regions.isEmpty() ? null
                    : regions.get(regions.size() - 1);
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
                standing[index - start] = frame(index);
            }
            return standing;
        }

        /**
         * The bucket an event is counted in: the occurrence it belongs to.
         *
         * <p>The innermost region activation open on this thread, by the
         * serial it was opened with, else the degraded occurrence's own
         * identity.  A serial rather than the address: an address costs one
         * digest per frame on the path ({@code ExecutionIndex.of}), which
         * is where hdfs-11741's seed replay spent its 980 seconds before
         * {@code OccurrenceAddress#id} was memoized.  The key is
         * thread-local bookkeeping and is published nowhere.</p>
         */
        private String bucket(OccurrenceAddress occurrence) {
            for (int index = regions.size() - 1; index >= 0; index--) {
                Region region = regions.get(index);
                if (region.occurrence == occurrence) return region.key;
            }
            return degraded(occurrence.node().render(),
                    occurrence.regionId(), occurrence.context());
        }

        /**
         * The iteration of a FRAME entered at {@code site}: how many times
         * this level has entered that site.
         *
         * <p>Control flow, and nothing else -- IDENTITY-V3 §1's "the
         * innermost enclosing loop's iteration count at that frame".  The
         * loop that re-enters a site is often in code outside the
         * application scope (hdfs-11741's balancer iterations are
         * {@code TestBalancer.runBalancer}'s own {@code for}), so the count
         * of entries at this level is the only thing that separates two
         * turns of it, and it must not be reset by anything that is not
         * control flow.</p>
         *
         * <p>What this replaces: counting a frame entry as an EVENT of the
         * enclosing occurrence.  A thread's ambient occurrence changes
         * whenever its scope does -- an IPC client carries the inbound
         * scope of the last response until it builds the next request
         * ({@code Client.java:1237}) -- so the two {@code
         * Balancer.runOneIteration} entries of one workload request landed
         * in two buckets, both at iteration 0, and the two {@code
         * balance-block} requests they sent carried ONE producer endpoint
         * id ({@code d21d5bc6e61357f1}).  Which occurrence a frame ENTRY
         * belongs to is not part of where that frame sits in the control
         * structure.</p>
         */
        private int nextCall(String site) {
            Map<String, Integer> calls = top().calls;
            Integer made = calls.get(site);
            int iteration = made == null ? 0 : made;
            calls.put(site, iteration + 1);
            return iteration;
        }

        /**
         * The k of one EVENT of the bucket {@code occurrence} at
         * {@code site}: how many it has already made there AT THIS LEVEL.
         *
         * <p>THE event counter.  A send, a read, a write and an attach are
         * events OF an occurrence, and one of them is the k-th of that
         * occurrence at its site or two of them share an endpoint id
         * (RowInvariants invariant 4).  Keyed by the occurrence, because
         * that is what the count means; taken at this level, because a
         * count belongs to the calling context it was taken in.  Every
         * caller comes through here so that the number the recording
         * states and the number a replay computes are the same number for
         * the same event.</p>
         */
        private int nextSiteEvent(String occurrence, String site) {
            Map<String, Integer> events = top().events;
            String key = occurrence + '\n' + site;
            Integer made = events.get(key);
            int iteration = made == null ? 0 : made;
            events.put(key, iteration + 1);
            return iteration;
        }

        private ExecutionIndex from(int base) {
            int start = Math.max(0, Math.min(base, depth()));
            if (start >= depth()) return ExecutionIndex.empty();
            List<Frame> standing = new ArrayList<Frame>(depth() - start);
            for (int index = start; index < depth(); index++) {
                standing.add(frame(index));
            }
            return ExecutionIndex.of(standing);
        }

        /**
         * The bucket of one degraded occurrence: what its id is made of,
         * minus the index its level already fixes.
         *
         * <p>(node, role, causal context) is the whole of a degraded
         * occurrence's identity at a given level, so two events of it at
         * one site count in one bucket and two events of DIFFERENT
         * occurrences never do: a daemon tick opened inside a request has
         * its own context ({@code Root:KEY_MANAGER_TICK#k}) and its events
         * are not a continuation of the request's counts.</p>
         *
         * <p>What this replaces: the innermost scope frame's TOKEN, which
         * changes whenever a scope is entered and left and therefore
         * restarted an occurrence's counts while the occurrence itself had
         * not changed.  The context does not move while the occurrence does
         * not.  It DOES move when the thread's ambient scope does, which is
         * why no FRAME is counted by it ({@link State#nextCall}): where a
         * frame sits in the control structure is not a fact about the
         * occurrence that happened to be current when it was entered.</p>
         */
        private static String degraded(String node, String regionId,
                                       CausalContext context) {
            return "d" + node + '\n' + regionId + '\n' + context.render();
        }
    }

    /** One level of the index: an entered frame and what happened under it. */
    private static final class Level {
        /** The frame this level was entered with, or null on the root. */
        private final Frame frame;
        /** The token the frame exit closes this level by, or 0. */
        private final long token;
        /** How often this level has entered each call site. */
        private final Map<String, Integer> calls =
                new HashMap<String, Integer>();
        /** How often each (occurrence, site) has minted an event here. */
        private final Map<String, Integer> events =
                new HashMap<String, Integer>();

        private Level(Frame frame, long token) {
            this.frame = frame;
            this.token = token;
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
        private final String nodeKey;

        private Start(Frame frame, String nodeKey) {
            this.frame = frame;
            this.nodeKey = nodeKey;
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
        state.openStart(start.frame);
        if (!start.nodeKey.isEmpty()) state.startNode = start.nodeKey;
    }

    /**
     * Files the frame of one {@code Thread.start} or work submission.
     *
     * <p>The iteration is the k-th start AT THIS SITE of the occurrence that
     * makes it -- the one counter every other event of an occurrence is
     * counted by ({@link State#nextSiteEvent}) -- so two siblings started
     * from one site in one loop differ by it and by nothing else
     * (IDENTITY-V3 SS1: "two siblings started from one site in one loop
     * differ by the loop iteration of the start site").  It is a structural
     * count of starts, never a thread id, an address or a session
     * ordinal.</p>
     *
     * <p>The count is taken in the level the start was made in: two starts
     * made at one site by one occurrence from two activations of a CALLER
     * are two levels, because every method of the application scope enters
     * one (G11).  A caller outside that scope has no level of its own, and
     * two starts it makes at one site stand at one iteration -- which is a
     * shared endpoint id and a named refusal at the mint, never a
     * renumbering here.</p>
     */
    public static void startWork(String startSiteId, Object carrier,
                                 String starterNodeKey) {
        String site = Text.safe(startSiteId);
        if (site.isEmpty() || carrier == null) return;
        State state = state();
        // The start-site frame is a frame of the work that was started, so
        // its iteration is control flow like any other: the k-th start at
        // this site in this level.  Two starts one level makes at one site
        // are two siblings, whatever the starter's ambient scope did
        // between them.
        int iteration = state.nextCall(site);
        sweep();
        STARTS.put(new Carrier(carrier, COLLECTED),
                new Start(Frame.of(site, iteration),
                        attributable(starterNodeKey)
                                ? Text.safe(starterNodeKey)
                                : node()));
    }

    /** Whether a node key names a component rather than the degraded one. */
    private static boolean attributable(String nodeKey) {
        String key = Text.safe(nodeKey);
        return !key.isEmpty()
                && !OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(key);
    }

    /**
     * The node this thread belongs to when nothing else names one: the node
     * of the start that created the work it is running.
     *
     * <p>Transitive by construction -- a thread that inherited a node hands
     * it to what it starts -- so a component's own worker tree stays its
     * own however deep it goes.</p>
     */
    public static String node() {
        return state().startNode;
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
     * <p>The frame's iteration is the k-th entry of THIS site inside the
     * occurrence that ENCLOSES it, counted in the level of the enclosing
     * frame: a method entry is an event of the enclosing occurrence,
     * counted by the one counter every other event of an occurrence is
     * counted by ({@link State#nextSiteEvent}).  A loop body re-entering
     * the same call site is that site at iteration 1, 2, 3 -- which is what
     * the innermost enclosing loop's iteration count means -- and one rule
     * computes it in the recording and in the replay alike.</p>
     *
     * <p>No node: a level is a point of the component's control structure
     * and the node is a property of the OCCURRENCE an event belongs to,
     * which {@link #occurrence} and {@link #endpointAt} name for
     * themselves.  Reading it here would also cost a lock
     * ({@code RuntimeTraceContext.activationSource}) at every application
     * call.</p>
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterFrame(String callSiteId) {
        State state = state();
        String site = Text.safe(callSiteId);
        int iteration = state.nextCall(site);
        long token = TOKENS.getAndIncrement();
        state.levels.add(new Level(Frame.of(site, iteration), token));
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
                // the work it named is over with it.
                state.startDepth = -1;
            }
            // The scope root is the deepest level the scope start and this
            // point still SHARE.  A scope is opened inside a call that
            // returns -- CausynthMessagePropagation.inbound opens the scope
            // of a served message and hands control back to the handler --
            // and an index measured from a level that has gone is empty:
            // on hdfs-11741 the four PBHelper.convert activations of one
            // refresh answered one address, which is the collision the
            // index exists to prevent.
            if (state.scopeBase > state.depth()) {
                state.scopeBase = state.depth();
            }
            state.journal();
            return;
        }
    }

    /**
     * Opens a scope: the execution index of what runs inside starts here.
     *
     * <p>Never above the start frame this thread's work already claimed: the
     * start site and its iteration are what tell two siblings apart
     * (IDENTITY-V3 §1, scope transfer), and a scope base above them drops
     * them from every address the work publishes.  hdfs-11741's
     * {@code KeyManager$BlockKeyUpdater} claimed its start frame at its
     * entry and {@code beginTick} then based the tick's scope above it.</p>
     */
    public static void scopeStart() {
        State state = state();
        state.scopeBase = state.startDepth >= 0
                ? Math.min(state.startDepth, state.depth())
                : state.depth();
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
        state.regions.add(new Region(state.depth(),
                "r" + (++state.regionsOpened)));
        return index;
    }

    /**
     * Files the innermost open region's journal under the VM's own key.
     *
     * <p>The key is the region-enter event id the VM stamps on every version
     * and every read it logs from inside this activation, so an event and the
     * frames it stood on are joined by the VM's statement rather than by the
     * runtime guessing which activation was live.</p>
     */
    public static void regionKey(long vmRegionEnterEventId) {
        State state = state();
        Region region = state.region();
        if (region == null || vmRegionEnterEventId <= 0L) return;
        region.journal = FrameJournal.open(vmRegionEnterEventId,
                state.snapshot(region.base));
    }

    /**
     * Closes the innermost open region.
     *
     * <p>No counter cleanup: a region's serial is never reused, so the
     * counts of an activation that closed can be reached by nothing, and
     * the level they live in drops them when the frame that opened it
     * exits.  What this replaces: deleting the closing occurrence's bucket
     * from a thread-wide map, which had to run at exactly the right region
     * depth or it renumbered the enclosing occurrence's events
     * (ConcolicRegionRuntime#popActiveRegion).</p>
     */
    public static void regionExit() {
        State state = state();
        if (state.regions.isEmpty()) return;
        state.regions.remove(state.regions.size() - 1);
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
     * an event belongs to ({@link #currentOccurrence}) and which bucket
     * counts its site ({@link State#nextSiteEvent}).  An activation that
     * closes at a region depth other than the one it opened at must be
     * refused, exactly as an unbalanced frame is.</p>
     */
    public static int regionDepth() {
        return state().regions.size();
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

    /** The whole path this thread is at, for a degraded address. */
    public static ExecutionIndex here() {
        State state = state();
        return state.from(0);
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
     * @param open whether the region is opened here (the replay: every
     *             endpoint inside is indexed from this entry) or only read
     *             (the recording and admission, which must not move the base
     *             the endpoints of an already-open region are indexed from)
     */
    public static OccurrenceAddress occurrence(String nodeKey, String regionId,
                                               boolean open) {
        String node = attributable(nodeKey) || !attributable(node())
                ? Text.safe(nodeKey) : node();
        if (node.isEmpty() || Text.safe(regionId).isEmpty()) {
            return null;
        }
        nodeKey = node;
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

    /** The same endpoint, for an occurrence the caller already holds. */
    public static Endpoint endpointAt(OccurrenceAddress occurrence,
                                      String site, int attempt) {
        return occurrence == null ? null
                : Endpoint.of(occurrence, Text.safe(site),
                        eventSiteIndex(occurrence, site), attempt);
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
     * the occurrence's own ({@link State#nextSiteEvent}), keyed by the
     * occurrence this endpoint is under and taken in the level the event
     * was minted in: it starts at zero for that occurrence in that calling
     * context and is therefore the same number in the recording and in a
     * replay of it, whatever else the thread it ran on did.
     * It is also what separates the five {@code record-ordered-deletes}
     * messages one client occurrence sends at one transport site, whose
     * consumers would otherwise share one causal context and one
     * address.</p>
     */
    private static ExecutionIndex eventSiteIndex(OccurrenceAddress occurrence,
                                                 String site) {
        State state = state();
        String key = Text.safe(site);
        if (key.isEmpty()) return state.from(state.regionBase());
        int iteration = state.nextSiteEvent(state.bucket(occurrence), key);
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
     * The endpoint of one work submission, for the row that names the
     * thread-start edge (R-I7.1).
     *
     * @return the endpoint id, or {@code ""}
     */
    public static String workSubmitted(String nodeKey) {
        Endpoint submission = endpoint(nodeKey, "SUBMIT", 0);
        return submission == null ? "" : submission.id();
    }

    /**
     * The address of work that ran under no region this plan selected: its
     * role, on its node, at the path the thread stood on.
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
                "ROLE." + kind.name(), here(kind), here());
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

    /** One open region activation: where its endpoints are indexed from. */
    private static final class Region {
        private final int base;
        /** The bucket the events of this activation are counted in. */
        private final String key;
        private FrameJournal journal;
        /** The occurrence this activation is, for the endpoints inside it. */
        private OccurrenceAddress occurrence;

        private Region(int base, String key) {
            this.base = base;
            this.key = key;
        }
    }

    public static void resetForTests() {
        CURRENT.remove();
        STARTS.clear();
        CLOCK = UNAVAILABLE;
        FrameJournal.resetForTests();
    }
}
