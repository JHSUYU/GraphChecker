package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

/**
 * The heap as the recording saw objects hold one another: an edge from a
 * holder to what it held -- a field access's receiver to its value, the
 * receiver of a call at a store site that mutates through the call to each
 * object it was handed ({@link TracedRows} traces those rows), an accessor
 * call's receiver to what it returned -- and the objects static fields held,
 * which every reader can reach.  Built once by the trace aggregation
 * ({@code runtime.RuntimeRegionPlanner#recordedHeap}); the demand walk asks
 * it what a reader that never touched a demanded field in the recording
 * could have reached, and whether an object was seen held at all
 * ({@code RuntimeSelectedRegionFinalizer}'s {@code DemandWalk
 * #holdsOthersOnly}).
 *
 * <p>An object named by content ({@code CausynthTraceRecorder
 * #nameObservedObjectsFromContent}) may stand for several: their edges are
 * one object's, which only widens what is reachable.</p>
 */
public final class RecordedHeap {
    /** Holders, ascending; {@link #start} and {@link #held} their edges. */
    private final int[] holders;
    private final int[] start;
    private final int[] held;
    /** Every object some recorded holder held, ascending. */
    private final int[] heldAtAll;
    /** Every object a static field held, ascending. */
    private final int[] roots;

    private RecordedHeap(int[] holders, int[] start, int[] held,
                         int[] heldAtAll, int[] roots) {
        this.holders = holders;
        this.start = start;
        this.held = held;
        this.heldAtAll = heldAtAll;
        this.roots = roots;
    }

    /** Whether the recording saw anything hold {@code object}. */
    public boolean held(int object) {
        return Arrays.binarySearch(heldAtAll, object) >= 0;
    }

    /**
     * Every object reachable from {@code named} or a static field's object
     * over the recorded edges, those included.
     */
    public Set<Integer> reachable(int[] named) {
        Set<Integer> seen = new HashSet<>();
        Deque<Integer> work = new ArrayDeque<>();
        for (int object : named) {
            if (seen.add(object)) work.add(object);
        }
        for (int object : roots) {
            if (seen.add(object)) work.add(object);
        }
        while (!work.isEmpty()) {
            int at = Arrays.binarySearch(holders, work.removeFirst());
            if (at < 0) continue;
            for (int edge = start[at]; edge < start[at + 1]; edge++) {
                if (seen.add(held[edge])) work.add(held[edge]);
            }
        }
        return seen.isEmpty() ? Collections.<Integer>emptySet() : seen;
    }

    /** Collects the edges, then sorts them once. */
    public static final class Builder {
        private long[] edges = new long[1024];
        private int size;
        private final Set<Integer> roots = new HashSet<>();

        /** {@code holder} held {@code object}; 0 is no object. */
        public void edge(int holder, int object) {
            if (holder == 0 || object == 0 || holder == object) return;
            if (size == edges.length) {
                edges = Arrays.copyOf(edges, edges.length * 2);
            }
            edges[size++] = ((long) holder << 32) | (object & 0xffffffffL);
        }

        /** A static field held {@code object}. */
        public void root(int object) {
            if (object != 0) roots.add(object);
        }

        public RecordedHeap build() {
            long[] sorted = Arrays.copyOf(edges, size);
            Arrays.sort(sorted);
            int unique = 0;
            for (int index = 0; index < sorted.length; index++) {
                if (index == 0 || sorted[index] != sorted[index - 1]) {
                    sorted[unique++] = sorted[index];
                }
            }
            int holderCount = 0;
            for (int index = 0; index < unique; index++) {
                if (index == 0 || (int) (sorted[index] >> 32)
                        != (int) (sorted[index - 1] >> 32)) {
                    holderCount++;
                }
            }
            int[] holders = new int[holderCount];
            int[] start = new int[holderCount + 1];
            int[] held = new int[unique];
            int at = -1;
            for (int index = 0; index < unique; index++) {
                int holder = (int) (sorted[index] >> 32);
                if (at < 0 || holders[at] != holder) {
                    holders[++at] = holder;
                    start[at] = index;
                }
                held[index] = (int) sorted[index];
            }
            start[holderCount] = unique;
            int[] heldAtAll = Arrays.copyOf(held, held.length);
            Arrays.sort(heldAtAll);
            int distinct = 0;
            for (int index = 0; index < heldAtAll.length; index++) {
                if (index == 0 || heldAtAll[index] != heldAtAll[index - 1]) {
                    heldAtAll[distinct++] = heldAtAll[index];
                }
            }
            int[] rootIds = new int[roots.size()];
            int next = 0;
            for (int root : roots) rootIds[next++] = root;
            Arrays.sort(rootIds);
            return new RecordedHeap(holders, start, held,
                    Arrays.copyOf(heldAtAll, distinct), rootIds);
        }
    }
}
