package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class RecordedHeap {
    private final int[] holders;
    private final int[] start;
    private final int[] held;
    private final int[] heldObjects;
    private final int[] heldStart;
    private final int[] holdersOf;
    private final int[] roots;
    private final Map<Integer, Long> contexts;
    private final Map<Long, Long> rootContexts;
    private final Map<Integer, Long> confinements = new HashMap<>();

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

    public long contextOfRoot(long rootCall) {
        Long context = rootContexts.get(rootCall);
        return context == null ? NOWHERE : context;
    }

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

    public static final class Builder {
        private long[] edges = new long[1024];
        private int size;
        private final Set<Integer> roots = new HashSet<>();
        private final Map<String, Long> ids = new HashMap<>();
        private final Map<Integer, Long> contexts = new HashMap<>();
        private final Map<Long, Long> rootContexts = new HashMap<>();

        private long context(String key) {
            if (key == null || key.isEmpty()) return NOWHERE;
            return ids.computeIfAbsent(key, ignored -> (long) ids.size());
        }

        public void occurrence(long rootCall, String context) {
            long id = context(context);
            if (id != NOWHERE) rootContexts.put(rootCall, id);
        }

        public void mention(int object, String context) {
            if (object == 0) return;
            long id = context(context);
            Long before = contexts.putIfAbsent(object, id);
            if (before != null && before != id) contexts.put(object, NOWHERE);
        }

        public void edge(int holder, int object) {
            if (holder == 0 || object == 0 || holder == object) return;
            if (size == edges.length) {
                edges = Arrays.copyOf(edges, edges.length * 2);
            }
            edges[size++] = ((long) holder << 32) | (object & 0xffffffffL);
        }

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
