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

    private Identity() {
    }

    /** One thread's frame stack, its prefix hashes and its loop counters. */
    private static final class State {
        private final List<Frame> frames =
                new ArrayList<Frame>();
        /** Per frame, how often each child call site has been entered. */
        private final List<Map<String, Integer>> entries =
                new ArrayList<Map<String, Integer>>();
        private final Map<String, Integer> roots =
                new HashMap<String, Integer>();

        /** The counters of the frame a new child is entered under. */
        private Map<String, Integer> children() {
            return entries.isEmpty() ? roots
                    : entries.get(entries.size() - 1);
        }
        /** loop id -> iterations charged inside the innermost frame. */
        private final Map<String, Integer> loops =
                new HashMap<String, Integer>();
        private String loop = "";
        private int scopeBase;
        /** Whether this thread has looked for the start that created it. */
        private boolean claimed;
        /**
         * Where the frame of the start this thread's work runs under sits,
         * or -1 on a thread that runs its own work.
         */
        private int startDepth = -1;
        /** The region activations open on this thread, innermost last. */
        private final List<Region> regions = new ArrayList<Region>();
        /**
         * The node of the frame that started the work this thread runs, or
         * {@code ""}: the component an occurrence belongs to when its own
         * frames name none.
         */
        private String startNode = "";

        private State copy() {
            State child = new State();
            child.frames.addAll(frames);
            for (Map<String, Integer> frame : entries) {
                child.entries.add(new HashMap<String, Integer>(frame));
            }
            child.roots.putAll(roots);
            child.loops.putAll(loops);
            child.loop = loop;
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
         */
        private void openStart(Frame frame) {
            // A pool thread that finished its last task drops that task's
            // start frame before it takes the next: the work that frame
            // named is over, and the next task was started elsewhere.  A
            // task started from inside another one nests instead.
            if (startDepth >= 0 && startDepth == frames.size() - 1) {
                frames.remove(startDepth);
                if (!entries.isEmpty()) entries.remove(entries.size() - 1);
            }
            startDepth = frames.size();
            frames.add(frame);
            entries.add(new HashMap<String, Integer>());
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
            int start = Math.max(0, Math.min(base, frames.size()));
            Frame[] standing = new Frame[frames.size() - start];
            for (int index = start; index < frames.size(); index++) {
                standing[index - start] = frames.get(index);
            }
            return standing;
        }

        private ExecutionIndex from(int base) {
            int start = Math.max(0, Math.min(base, frames.size()));
            return start >= frames.size() ? ExecutionIndex.empty()
                    : ExecutionIndex.of(new ArrayList<Frame>(
                            frames.subList(start, frames.size())));
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
     * <p>The claim is lazy because the start is filed after the thread's
     * state was inherited (at construction) and before the thread runs
     * anything: its first frame, its first region, its first event -- all
     * go through here.</p>
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
     * <p>The iteration is the number of starts already made AT THIS SITE
     * inside the starter's current activation: the count lives in that
     * frame's own counters and is gone when the frame pops, exactly as a
     * loop iteration is (IDENTITY-V3 SS1: "two siblings started from one
     * site in one loop differ by the loop iteration of the start site").
     * It is a structural count of starts, never a thread id, an address or
     * a session ordinal.</p>
     */
    public static void startWork(String startSiteId, Object carrier,
                                 String starterNodeKey) {
        String site = Text.safe(startSiteId);
        if (site.isEmpty() || carrier == null) return;
        State state = state();
        Map<String, Integer> starts = state.children();
        String key = STARTED + site;
        Integer made = starts.get(key);
        int iteration = made == null ? 0 : made;
        starts.put(key, iteration + 1);
        sweep();
        STARTS.put(new Carrier(carrier, COLLECTED),
                new Start(Frame.of(site, iteration),
                        attributable(starterNodeKey)
                                ? Text.safe(starterNodeKey)
                                : node()));
    }

    /**
     * The site-local index of one export, with the export itself as its
     * innermost frame.
     *
     * <p>IDENTITY-V3 §1: an Endpoint's ordinal is replaced by a site-local
     * execution index, and two exports of one occurrence at one site are
     * two points of its control structure -- the k-th turn of whatever
     * loop or sequence made them, counted in the frame they stand in
     * exactly as a start site's iteration is (#startWork).  Without that
     * frame the five {@code record-ordered-deletes} calls one client
     * occurrence makes at one site are one producer endpoint, so the five
     * NameNode occurrences they start share one causal context and one
     * address; with it they are five.  It is a structural count inside a
     * frame that dies with the frame, never a session ordinal.</p>
     */
    private static ExecutionIndex exportIndex(String site) {
        State state = state();
        Map<String, Integer> exports = state.children();
        String key = EXPORTED + site;
        Integer made = exports.get(key);
        int iteration = made == null ? 0 : made;
        exports.put(key, iteration + 1);
        List<Frame> frames = new ArrayList<Frame>(
                state.from(state.regionBase()).frames());
        frames.add(Frame.of(site, iteration));
        return ExecutionIndex.of(frames);
    }

    private static final String EXPORTED = "export\u0000";

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
     * filed for ITSELF the first time it does anything, and a pool thread
     * that was created before the work claims the start filed for the task
     * it is running -- the task object the region was entered on.</p>
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

    private static final String STARTED = "start\u0000";

    /**
     * Enters one instrumented call site.
     *
     * <p>The frame's iteration is the k-th entry of THIS call site under
     * the frame that encloses it, counted since that frame was entered.  A
     * loop body re-entering the same site is the same site at iteration
     * 1, 2, 3 -- which is what the innermost enclosing loop's iteration
     * count means -- and one rule computes it in the recording and in the
     * replay alike, because the recording weaves no loop-backedge hook and
     * an index that differed between the two passes would name two
     * different points for one execution point.</p>
     */
    public static void enterCall(String callSiteId) {
        State state = state();
        String site = Text.safe(callSiteId);
        Map<String, Integer> siblings = state.children();
        Integer seen = siblings.get(site);
        int iteration = seen == null ? 0 : seen;
        siblings.put(site, iteration + 1);
        state.frames.add(Frame.of(site, iteration));
        state.entries.add(new HashMap<String, Integer>());
        state.journal();
    }

    /** Leaves the innermost call site. */
    public static void exitCall() {
        State state = state();
        int depth = state.frames.size();
        if (depth == 0) return;
        // The frame of the start this thread's work runs under was pushed by
        // no call of that work, so no return of it may pop it: an unbalanced
        // exit would otherwise take the one frame that tells two siblings
        // apart.
        if (depth - 1 <= state.startDepth) return;
        state.frames.remove(depth - 1);
        // The frame's own children are gone with it; the counters of the
        // frame it returns to stay, which is what makes the next turn of a
        // loop the next iteration.
        if (!state.entries.isEmpty()) {
            state.entries.remove(state.entries.size() - 1);
        }
        state.journal();
    }

    /** Charges one iteration of {@code loopId} to the current frame. */
    public static void loopIteration(String loopId) {
        String loop = Text.safe(loopId);
        if (loop.isEmpty()) return;
        State state = state();
        state.loop = loop;
        Integer charged = state.loops.get(loop);
        state.loops.put(loop, charged == null ? 1 : charged + 1);
    }

    /** Opens a scope: the execution index of what runs inside starts here. */
    public static void scopeStart() {
        State state = state();
        state.scopeBase = state.frames.size();
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
        state.regions.add(new Region(state.frames.size()));
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

    /** Closes the innermost open region. */
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
                : Endpoint.of(occurrence, Text.safe(site), siteIndex(),
                        attempt);
    }

    /**
     * Files the producer endpoint of one whole message, for the anchor its
     * receiver states (IDENTITY-IMPL §C).
     *
     * @return the endpoint id filed, or {@code ""}
     */
    public static String messageSent(String nodeKey, String transport,
                                     String correlationId, String half) {
        OccurrenceAddress occurrence = currentOccurrence(nodeKey);
        String site = Text.safe(transport) + "#" + Text.safe(half);
        Endpoint producer = occurrence == null ? null
                : Endpoint.of(occurrence, site, exportIndex(site), 0);
        if (producer == null) return "";
        Interactions.sent(Text.safe(transport), Text.safe(correlationId),
                Text.safe(half), producer.id());
        return producer.id();
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

    /** The context the running thread is in, by the one rule. */
    private static CausalContext here(Role role) {
        return context(Lineage.anchor(), Lineage.rpcSite(), role,
                Lineage.rootWindowIndex());
    }

    /** The context an occurrence entered under, from its scope frame. */
    public static CausalContext context(String anchorEndpointId,
                                        String rpcSite, Role role,
                                        int windowIndex) {
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
        if (role != null && role != Role.UNKNOWN && windowIndex > 0) {
            return CausalContext.of(role, windowIndex);
        }
        return CausalContext.of(role == null ? Role.UNKNOWN : role);
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
        private FrameJournal journal;
        /** The occurrence this activation is, for the endpoints inside it. */
        private OccurrenceAddress occurrence;

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
