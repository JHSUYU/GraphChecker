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
        /** loop id -> iterations charged inside the innermost frame. */
        private final Map<String, Integer> loops =
                new HashMap<String, Integer>();
        private String loop = "";
        private int scopeBase;
        private int regionBase;

        private State copy() {
            State child = new State();
            child.frames.addAll(frames);
            child.loops.putAll(loops);
            child.loop = loop;
            child.scopeBase = scopeBase;
            child.regionBase = regionBase;
            return child;
        }

        private ExecutionIndex from(int base) {
            int start = Math.max(0, Math.min(base, frames.size()));
            return start >= frames.size() ? ExecutionIndex.empty()
                    : ExecutionIndex.of(new ArrayList<Frame>(
                            frames.subList(start, frames.size())));
        }
    }

    /** Enters one instrumented call site. */
    public static void enterCall(String callSiteId) {
        State state = CURRENT.get();
        int iteration = state.loop.isEmpty() ? 0
                : state.loops.containsKey(state.loop)
                        ? state.loops.get(state.loop) : 0;
        state.frames.add(Frame.of(callSiteId, iteration));
    }

    /** Leaves the innermost call site. */
    public static void exitCall() {
        State state = CURRENT.get();
        int depth = state.frames.size();
        if (depth == 0) return;
        state.frames.remove(depth - 1);
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
        state.regionBase = state.frames.size();
        return index;
    }

    /** The site-local index of one event inside the region. */
    public static ExecutionIndex siteIndex() {
        State state = CURRENT.get();
        return state.from(state.regionBase);
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
        if (role != null && role != Role.UNKNOWN && windowIndex > 0) {
            return CausalContext.of(role, windowIndex);
        }
        return CausalContext.of(role == null ? Role.UNKNOWN : role);
    }

    public static void resetForTests() {
        CURRENT.remove();
    }
}
