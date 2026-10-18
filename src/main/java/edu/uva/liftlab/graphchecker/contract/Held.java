package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Indexes built by adding and then held for good: each list's array cut to
 * its size.  An {@code ArrayList} takes ten slots at its first add, and a
 * session's indexes by location and occurrence are mostly of one row
 * (SGF8-adhoc-05 round 5's planner: 3.1 M arrays, 202 MB, for 2.6 M lists).
 */
public final class Held {
    private Held() {
    }

    /** Every list of {@code index} cut to its size. */
    public static <K, T> void trimmed(Map<K, List<T>> index) {
        for (List<T> list : index.values()) {
            if (list instanceof ArrayList) ((ArrayList<T>) list).trimToSize();
        }
    }
}
