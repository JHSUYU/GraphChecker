package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
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
 * could have reached, and where an object it could not was confined
 * ({@code RuntimeSelectedRegionFinalizer}'s {@code DemandWalk
 * #holdsOthersOnly}).
 *
 * <p>And the CAUSAL CONTEXT each object was mentioned under -- as a
 * receiver, an argument, a return, a field's holder or value: the {@code c}
 * of an occurrence's {@code (r,c,i)} (IDENTITY.md), one tick, one served
 * request, one client root, which work it starts carries on whatever thread
 * runs it; and each occurrence's.  {@link #confinement} reads them over an
 * object and every recorded holder above it.</p>
 *
 * <p>PARTIAL: only what the trace records is here -- field events of the
 * trace methods, call rows at the sites {@link TracedRows} names, method
 * entries.  Untraced code (unwoven, or woven outside the trace methods, a
 * lambda's body included) holds, hands over and mentions objects unseen --
 * an unwoven cache shared by two requests among them --, so an object
 * confined here may have escaped there: every writer the walk drops on it
 * is published ({@code CLOSURE_CONFINED}).  An object named by content
 * ({@code CausynthTraceRecorder#nameObservedObjectsFromContent}) may stand
 * for several: their edges are one object's, which only widens what is
 * reachable, and their mentions one object's, which only narrows what is
 * confined.</p>
 */
public final class RecordedHeap {
    /** Holders, ascending; {@link #start} and {@link #held} their edges. */
    private final int[] holders;
    private final int[] start;
    private final int[] held;
    /** Held objects, ascending; {@link #heldStart} and {@link #holdersOf}
     *  the edges into them. */
    private final int[] heldObjects;
    private final int[] heldStart;
    private final int[] holdersOf;
    /** Every object a static field held, ascending. */
    private final int[] roots;
    /** Object -> the one causal context every event mentioning it ran
     *  under, or {@link #NOWHERE}. */
    private final Map<Integer, Long> contexts;
    /** An occurrence's root call -> its causal context. */
    private final Map<Long, Long> rootContexts;
    /** {@link #confinement}, once asked. */
    private final Map<Integer, Long> confinements = new HashMap<>();

    /** Mentioned under more than one context, or under none. */
    public static final long NOWHERE = Long.MIN_VALUE;

    private RecordedHeap(int[][] forward, int[][] backward, int[] roots,
                         Map<Integer, Long> contexts,
                         Map<Long, Long> rootContexts) {
        this.holders = forward[0];
        this.start = forward[1];
        this.held = forward[2];
        this.heldObjects = backward[0];
        this.heldStart = backward[1];
        this.holdersOf = backward[2];
        this.roots = roots;
        this.contexts = contexts;
        this.rootContexts = rootContexts;
    }

    /** The causal context of the occurrence rooted at {@code rootCall}, or
     *  {@link #NOWHERE}. */
    public long contextOfRoot(long rootCall) {
        Long context = rootContexts.get(rootCall);
        return context == null ? NOWHERE : context;
    }

    /**
     * The one causal context every event mentioning {@code object}, or any
     * object the recording saw hold it or hold those, ran under; {@link
     * #NOWHERE} when they ran under two or under none.  A holder is how an
     * object is handed on, so it is confined only as far as its holders are;
     * an object no event mentions is confined nowhere.
     */
    public long confinement(int object) {
        Long known = confinements.get(object);
        if (known != null) return known;
        long context = scope(object);
        Set<Integer> seen = new HashSet<>();
        Deque<Integer> work = new ArrayDeque<>();
        seen.add(object);
        work.add(object);
        while (!work.isEmpty() && context != NOWHERE) {
            int at = work.removeFirst();
            if (scope(at) != context) {
                context = NOWHERE;
                break;
            }
            int index = Arrays.binarySearch(heldObjects, at);
            if (index < 0) continue;
            for (int edge = heldStart[index]; edge < heldStart[index + 1];
                 edge++) {
                if (seen.add(holdersOf[edge])) work.add(holdersOf[edge]);
            }
        }
        confinements.put(object, context);
        return context;
    }

    private long scope(int object) {
        Long context = contexts.get(object);
        return context == null ? NOWHERE : context;
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

    /** Collects the occurrences, mentions and edges; sorts the edges
     *  once. */
    public static final class Builder {
        private long[] edges = new long[1024];
        private int size;
        private final Set<Integer> roots = new HashSet<>();
        private final Map<String, Long> ids = new HashMap<>();
        private final Map<Integer, Long> contexts = new HashMap<>();
        private final Map<Long, Long> rootContexts = new HashMap<>();

        /** The id of one causal context ({@code ""}: none). */
        private long context(String key) {
            if (key == null || key.isEmpty()) return NOWHERE;
            return ids.computeIfAbsent(key, ignored -> (long) ids.size());
        }

        /** The occurrence rooted at {@code rootCall} ran under {@code
         *  context}. */
        public void occurrence(long rootCall, String context) {
            long id = context(context);
            if (id != NOWHERE) rootContexts.put(rootCall, id);
        }

        /** An event under {@code context} ({@code ""}: none known)
         *  mentioned {@code object}; 0 is no object. */
        public void mention(int object, String context) {
            if (object == 0) return;
            long id = context(context);
            Long before = contexts.putIfAbsent(object, id);
            if (before != null && before != id) contexts.put(object, NOWHERE);
        }

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
            long[] forward = Arrays.copyOf(edges, size);
            long[] backward = new long[size];
            for (int index = 0; index < size; index++) {
                long edge = forward[index];
                backward[index] = (edge << 32) | (edge >>> 32);
            }
            int[] rootIds = new int[roots.size()];
            int next = 0;
            for (int root : roots) rootIds[next++] = root;
            Arrays.sort(rootIds);
            return new RecordedHeap(adjacency(forward), adjacency(backward),
                    rootIds, contexts, rootContexts);
        }

        /** {from, start, to}: the distinct edges {@code from << 32 | to}
         *  grouped by their ascending {@code from}. */
        private static int[][] adjacency(long[] edges) {
            Arrays.sort(edges);
            int unique = 0;
            for (int index = 0; index < edges.length; index++) {
                if (index == 0 || edges[index] != edges[index - 1]) {
                    edges[unique++] = edges[index];
                }
            }
            int fromCount = 0;
            for (int index = 0; index < unique; index++) {
                if (index == 0 || (int) (edges[index] >> 32)
                        != (int) (edges[index - 1] >> 32)) {
                    fromCount++;
                }
            }
            int[] from = new int[fromCount];
            int[] start = new int[fromCount + 1];
            int[] to = new int[unique];
            int at = -1;
            for (int index = 0; index < unique; index++) {
                int source = (int) (edges[index] >> 32);
                if (at < 0 || from[at] != source) {
                    from[++at] = source;
                    start[at] = index;
                }
                to[index] = (int) edges[index];
            }
            start[fromCount] = unique;
            return new int[][] {from, start, to};
        }
    }
}
