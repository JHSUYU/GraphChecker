package edu.uva.liftlab.graphchecker.runtime.d3;

import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.Frame;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
        /** The region activations open on this thread, innermost last. */
        private final List<Region> regions = new ArrayList<Region>();

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
            for (Region region : regions) {
                // The depth carries over -- a child thread's frames continue
                // its parent's -- but not the journal: a journal is one
                // thread's clock readings in order, and a second writer would
                // interleave two threads' events into one sequence.
                child.regions.add(new Region(region.base));
            }
            return child;
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
        State state = CURRENT.get();
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
        State state = CURRENT.get();
        int depth = state.frames.size();
        if (depth == 0) return;
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
        State state = CURRENT.get();
        state.loop = loop;
        Integer charged = state.loops.get(loop);
        state.loops.put(loop, charged == null ? 1 : charged + 1);
    }

    /** Opens a scope: the execution index of what runs inside starts here. */
    public static void scopeStart() {
        State state = CURRENT.get();
        state.scopeBase = state.frames.size();
    }

    /** The index from the scope root to here: an occurrence's own index. */
    public static ExecutionIndex atScope() {
        State state = CURRENT.get();
        return state.from(state.scopeBase);
    }

    /**
     * Opens a region: every endpoint inside it is indexed from here.
     *
     * @return the index from the scope root to this region entry
     */
    public static ExecutionIndex regionEnter() {
        State state = CURRENT.get();
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
        State state = CURRENT.get();
        Region region = state.region();
        if (region == null || vmRegionEnterEventId <= 0L) return;
        region.journal = FrameJournal.open(vmRegionEnterEventId,
                state.snapshot(region.base));
    }

    /** Closes the innermost open region. */
    public static void regionExit() {
        State state = CURRENT.get();
        if (state.regions.isEmpty()) return;
        state.regions.remove(state.regions.size() - 1);
    }

    /** The site-local index of one event inside the region. */
    public static ExecutionIndex siteIndex() {
        State state = CURRENT.get();
        return state.from(state.regionBase());
    }

    /** The whole path this thread is at, for a degraded address. */
    public static ExecutionIndex here() {
        State state = CURRENT.get();
        return state.from(0);
    }

    /** The context an occurrence entered under, from its scope frame. */
    public static CausalContext context(String anchorEndpointId,
                                        String rpcSite, Role role,
                                        int windowIndex) {
        if (!Text.safe(anchorEndpointId).isEmpty()) {
            return CausalContext.of(anchorEndpointId, Text.safe(rpcSite));
        }
        // A thread started by a submission ran because of that submission:
        // its endpoint is the anchor, exactly as a message's producer is.
        // Two sibling threads doing the same work under one request -- the
        // two FSImageSaver threads on hdfs-17960 -- share a role, a window
        // index and a call path, and are told apart by nothing else.
        String started = Lineage.startedBy();
        if (!started.isEmpty()) {
            return CausalContext.of(started, "THREAD_START");
        }
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

        private Region(int base) {
            this.base = base;
        }
    }

    public static void resetForTests() {
        CURRENT.remove();
        CLOCK = UNAVAILABLE;
        FrameJournal.resetForTests();
    }
}
