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
 * <p>And where each object was mentioned -- as a receiver, an argument, a
 * return, a field's holder or value: the one occurrence whose events alone
 * name it, the one occurrence tree (an occurrence and those it encloses)
 * and the one thread, or none; with the occurrences' own nesting and
 * threads.  {@link #confinement} reads them over an object and every
 * recorded holder above it.</p>
 *
 * <p>PARTIAL: only what the trace records is here -- field events of the
 * trace methods, call rows at the sites {@link TracedRows} names, method
 * entries.  Untraced code (unwoven, or woven outside the trace methods, a
 * lambda's body included) holds, hands over and mentions objects unseen,
 * so an object confined here may have escaped there: every writer the walk
 * drops on it is published ({@code CLOSURE_CONFINED}).  An object named by
 * content ({@code CausynthTraceRecorder#nameObservedObjectsFromContent})
 * may stand for several: their edges are one object's, which only widens
 * what is reachable, and their mentions one object's, which only narrows
 * what is confined.</p>
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
    /** Object -> the root call of the one occurrence whose events alone
     *  mention it, or {@link #NOWHERE}. */
    private final Map<Integer, Long> occurrences;
    /** Object -> the root call of the outermost occurrence of the one tree
     *  every event mentioning it ran in, or {@link #NOWHERE}. */
    private final Map<Integer, Long> trees;
    /** Object -> the one thread every event mentioning it ran on, or
     *  {@link #NOWHERE}. */
    private final Map<Integer, Long> threads;
    /** An occurrence's root call -> the thread it ran on. */
    private final Map<Long, Long> rootThreads;
    /** An occurrence's root call -> that of the occurrence enclosing it
     *  nearest; none for an outermost one. */
    private final Map<Long, Long> enclosing;
    /** {@link #confinement}, once asked. */
    private final Map<Integer, Confinement> confinements = new HashMap<>();

    /** Mentioned in more than one scope, or in none. */
    public static final long NOWHERE = Long.MIN_VALUE;

    /**
     * Where an object and every recorded holder above it were mentioned:
     * the one occurrence, the one occurrence tree (its outermost root call)
     * and the one thread all of them were, each {@link #NOWHERE} when they
     * were in more than one or in none.
     */
    public static final class Confinement {
        public final long occurrence;
        public final long tree;
        public final long thread;

        Confinement(long occurrence, long tree, long thread) {
            this.occurrence = occurrence;
            this.tree = tree;
            this.thread = thread;
        }
    }

    private RecordedHeap(int[][] forward, int[][] backward, int[] roots,
                         Map<Integer, Long> occurrences,
                         Map<Integer, Long> trees,
                         Map<Integer, Long> threads,
                         Map<Long, Long> rootThreads,
                         Map<Long, Long> enclosing) {
        this.holders = forward[0];
        this.start = forward[1];
        this.held = forward[2];
        this.heldObjects = backward[0];
        this.heldStart = backward[1];
        this.holdersOf = backward[2];
        this.roots = roots;
        this.occurrences = occurrences;
        this.trees = trees;
        this.threads = threads;
        this.rootThreads = rootThreads;
        this.enclosing = enclosing;
    }

    /** The thread the occurrence rooted at {@code rootCall} ran on, or
     *  {@link #NOWHERE}. */
    public long threadOfRoot(long rootCall) {
        Long thread = rootThreads.get(rootCall);
        return thread == null ? NOWHERE : thread;
    }

    /** Whether the occurrence rooted at {@code rootCall} is the one rooted
     *  at {@code outer} or ran inside it. */
    public boolean within(long rootCall, long outer) {
        Set<Long> seen = new HashSet<>();
        for (Long at = rootCall; at != null && seen.add(at);
             at = enclosing.get(at)) {
            if (at == outer) return true;
        }
        return false;
    }

    /**
     * Where {@code object} and every object the recording saw hold it, and
     * hold those, were mentioned ({@link Confinement}): a holder is how an
     * object is handed on, so it is confined only as far as its holders
     * are.  An object no event mentions is confined nowhere.
     */
    public Confinement confinement(int object) {
        Confinement known = confinements.get(object);
        if (known != null) return known;
        long occurrence = NOWHERE;
        long tree = NOWHERE;
        long thread = NOWHERE;
        boolean first = true;
        Set<Integer> seen = new HashSet<>();
        Deque<Integer> work = new ArrayDeque<>();
        seen.add(object);
        work.add(object);
        while (!work.isEmpty()) {
            int at = work.removeFirst();
            long atOccurrence = scope(occurrences, at);
            long atTree = scope(trees, at);
            long atThread = scope(threads, at);
            occurrence = first || occurrence == atOccurrence
                    ? atOccurrence : NOWHERE;
            tree = first || tree == atTree ? atTree : NOWHERE;
            thread = first || thread == atThread ? atThread : NOWHERE;
            first = false;
            if (thread == NOWHERE) {
                // On two threads, or none known: confined nowhere.
                occurrence = NOWHERE;
                tree = NOWHERE;
                break;
            }
            int index = Arrays.binarySearch(heldObjects, at);
            if (index < 0) continue;
            for (int edge = heldStart[index]; edge < heldStart[index + 1];
                 edge++) {
                if (seen.add(holdersOf[edge])) work.add(holdersOf[edge]);
            }
        }
        Confinement found = new Confinement(occurrence, tree, thread);
        confinements.put(object, found);
        return found;
    }

    private static long scope(Map<Integer, Long> scopes, int object) {
        Long scope = scopes.get(object);
        return scope == null ? NOWHERE : scope;
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

    /** Collects the occurrences, then the mentions and edges; sorts the
     *  edges once. */
    public static final class Builder {
        private long[] edges = new long[1024];
        private int size;
        private final Set<Integer> roots = new HashSet<>();
        private final Map<Integer, Long> occurrences = new HashMap<>();
        private final Map<Integer, Long> trees = new HashMap<>();
        private final Map<Integer, Long> threads = new HashMap<>();
        private final Map<Long, Long> rootThreads = new HashMap<>();
        private final Map<Long, Long> enclosing = new HashMap<>();
        /** Root call -> its outermost enclosing root call, once asked. */
        private final Map<Long, Long> outermost = new HashMap<>();

        /** The occurrence rooted at {@code rootCall} ran on {@code thread},
         *  inside the one rooted at {@code enclosingRoot} ({@link #NOWHERE}:
         *  inside none).  Every occurrence is stated before any mention. */
        public void occurrence(long rootCall, long thread,
                               long enclosingRoot) {
            if (thread != NOWHERE) rootThreads.put(rootCall, thread);
            if (enclosingRoot != NOWHERE) {
                enclosing.put(rootCall, enclosingRoot);
            }
        }

        /** An event of the occurrence rooted at {@code owner}, on {@code
         *  thread} ({@link #NOWHERE}: of none, on none known), mentioned
         *  {@code object}; 0 is no object. */
        public void mention(int object, long owner, long thread) {
            if (object == 0) return;
            once(occurrences, object, owner);
            once(trees, object, owner == NOWHERE ? NOWHERE
                    : outermost(owner));
            once(threads, object, thread);
        }

        private long outermost(long rootCall) {
            Long known = outermost.get(rootCall);
            if (known != null) return known;
            long at = rootCall;
            Set<Long> seen = new HashSet<>();
            for (Long outer = enclosing.get(at); outer != null
                    && seen.add(outer); outer = enclosing.get(at)) {
                at = outer;
            }
            outermost.put(rootCall, at);
            return at;
        }

        private static void once(Map<Integer, Long> scopes, int object,
                                 long scope) {
            Long before = scopes.putIfAbsent(object, scope);
            if (before != null && before != scope) {
                scopes.put(object, NOWHERE);
            }
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
                    rootIds, occurrences, trees, threads, rootThreads,
                    enclosing);
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
