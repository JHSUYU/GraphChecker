package edu.uva.liftlab.graphchecker.causynth;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Every access of a cell the recording states, per cell in seq order, each
 * with the call it ran in and whether it stored: the trace's field reads and
 * stores, the calls at a store site that mutates through a call ({@link
 * RuntimeSelectedRegionFinalizer#storingCalls}) and those at a site that
 * returns a field ({@link RuntimeSelectedRegionFinalizer
 * #fieldAccessingCalls}).  Built once by the trace aggregation ({@code
 * runtime.RuntimeRegionPlanner#recordedAccesses}); the demand walk asks it
 * whether an occurrence stored a demanded cell, and whether anyone else
 * touched one between two equivalent deciders ({@link
 * RuntimeSelectedRegionFinalizer#DECIDER_CLASS}).
 */
public final class RecordedAccesses {
    /** No access recorded. */
    public static final RecordedAccesses NONE = new Builder().build();

    /** Cell -> its accesses' seqs, ascending; at the same positions the
     *  calls they ran in, and whether each stored. */
    private final Map<String, long[]> seqs;
    private final Map<String, long[]> calls;
    private final Map<String, boolean[]> stores;

    private RecordedAccesses(Map<String, long[]> seqs,
                             Map<String, long[]> calls,
                             Map<String, boolean[]> stores) {
        this.seqs = seqs;
        this.calls = calls;
        this.stores = stores;
    }

    /**
     * Whether a call outside {@code own} accessed one of {@code cells} at a
     * seq in {@code [from, to]}.
     */
    boolean touched(Collection<String> cells, long from, long to,
                    Set<Long> own) {
        return any(cells, from, to, own, false);
    }

    /**
     * Whether a call in {@code own} stored one of {@code cells} at a seq in
     * {@code [from, to]}.
     */
    boolean stored(Collection<String> cells, long from, long to,
                   Set<Long> own) {
        return any(cells, from, to, own, true);
    }

    private boolean any(Collection<String> cells, long from, long to,
                        Set<Long> own, boolean storedByOwn) {
        for (String cell : cells) {
            long[] at = seqs.get(cell);
            if (at == null) continue;
            long[] by = calls.get(cell);
            boolean[] store = stores.get(cell);
            int index = Arrays.binarySearch(at, from);
            if (index < 0) {
                index = -index - 1;
            } else {
                while (index > 0 && at[index - 1] == from) index--;
            }
            for (; index < at.length && at[index] <= to; index++) {
                if (storedByOwn ? store[index] && own.contains(by[index])
                        : !own.contains(by[index])) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Collects accesses in any order; {@link #build} sorts each cell's. */
    public static final class Builder {
        /** Cell -> (seq, call, stored 0/1) triples, as added. */
        private final Map<String, long[]> added = new HashMap<>();
        private final Map<String, Integer> sizes = new HashMap<>();

        public Builder add(String cell, long seq, long callId,
                           boolean store) {
            int size = sizes.getOrDefault(cell, 0);
            long[] held = added.get(cell);
            if (held == null || held.length < 3 * size + 3) {
                held = Arrays.copyOf(held == null ? new long[0] : held,
                        Math.max(12, 6 * size + 6));
                added.put(cell, held);
            }
            held[3 * size] = seq;
            held[3 * size + 1] = callId;
            held[3 * size + 2] = store ? 1L : 0L;
            sizes.put(cell, size + 1);
            return this;
        }

        public RecordedAccesses build() {
            Map<String, long[]> seqs = new HashMap<>();
            Map<String, long[]> calls = new HashMap<>();
            Map<String, boolean[]> stores = new HashMap<>();
            for (Map.Entry<String, long[]> entry : added.entrySet()) {
                int size = sizes.get(entry.getKey());
                long[] held = entry.getValue();
                Integer[] order = new Integer[size];
                for (int index = 0; index < size; index++) order[index] = index;
                Arrays.sort(order, (one, other) -> Long.compare(
                        held[3 * one], held[3 * other]));
                long[] at = new long[size];
                long[] by = new long[size];
                boolean[] store = new boolean[size];
                for (int index = 0; index < size; index++) {
                    at[index] = held[3 * order[index]];
                    by[index] = held[3 * order[index] + 1];
                    store[index] = held[3 * order[index] + 2] != 0L;
                }
                seqs.put(entry.getKey(), at);
                calls.put(entry.getKey(), by);
                stores.put(entry.getKey(), store);
            }
            return new RecordedAccesses(seqs, calls, stores);
        }
    }
}
