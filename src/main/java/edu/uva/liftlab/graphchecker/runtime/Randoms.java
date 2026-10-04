package edu.uva.liftlab.graphchecker.runtime;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;

/**
 * THE unseeded randomness of the application scope, seeded by where it is
 * drawn.  The weave replaces {@code new Random()}, {@code Math.random()},
 * {@code Collections.shuffle(List)} and {@code UUID.randomUUID()} with these
 * in BOTH passes, so a replay draws what the recording drew: a Solr client
 * shuffles the live nodes it sends an admin request to, and a replay that
 * sent it to another node than the recording did held no order past it.
 *
 * <p>Inside the window a draw in an occurrence with a context (a Root or an
 * Anchor) is seeded by its endpoint: the occurrence, its site and its count
 * there -- the same function of the same inputs in both passes.  A Lost
 * context names no work of its own: siblings share its address (unnamed
 * work, a turn begun before the window), so a draw there is seeded as one
 * before the window, where no occurrence stands: by its site and its count
 * at that site in this window.  hdfs-adhoc-01 (round HS1): a cluster started
 * inside the window while no hop stood drew one UUID for every DataNode, and
 * their registrations refused each other for the rest of the run.  Such a
 * count follows the run's own arrival order (the work is unscheduled), so
 * two runs may hand two such draws each other's values: distinct is what is
 * guaranteed, not equal.</p>
 */
public final class Randoms {
    /** Per window and site, the draws seeded by their count so far. */
    private static final Map<String, AtomicLong> COUNTS =
            new ConcurrentHashMap<String, AtomicLong>();

    private Randoms() {
    }

    /** What the draw at {@code site} here is keyed by (class comment). */
    static String key(String site) {
        if (RecordingWindow.opened()) {
            OccurrenceAddress occurrence = Identity.currentOccurrence(
                    RuntimeTraceContext.nodeHere());
            if (occurrence != null && !occurrence.lineageLost()) {
                return Identity.endpointAt(occurrence, "random#" + site, 0)
                        .id();
            }
        }
        String counted = RecordingWindow.index() + "#" + site;
        return counted + "#" + COUNTS.computeIfAbsent(counted,
                ignored -> new AtomicLong()).getAndIncrement();
    }

    /** A key as a seed, its bits mixed (two neighbouring keys of one site
     *  would otherwise start two generators nearly alike). */
    static long seed(String key) {
        long seed = 1125899906842597L;
        for (int i = 0; i < key.length(); i++) {
            seed = 31 * seed + key.charAt(i);
        }
        seed = (seed ^ (seed >>> 33)) * 0xff51afd7ed558ccdL;
        seed = (seed ^ (seed >>> 33)) * 0xc4ceb9fe1a85ec53L;
        return seed ^ (seed >>> 33);
    }

    /** Test seam: a fresh run's counts. */
    static void resetForTests() {
        COUNTS.clear();
    }

    /** {@code new Random()}'s seed. */
    public static long constructed(String site) {
        return seed(key(site));
    }

    /** {@code Math.random()}. */
    public static double random(String site) {
        return new Random(seed(key(site))).nextDouble();
    }

    /** {@code Collections.shuffle(list)}. */
    public static void shuffle(List<?> list, String site) {
        Collections.shuffle(list, new Random(seed(key(site))));
    }

    /** {@code UUID.randomUUID()}: a version-4 UUID from the seeded draw. */
    public static UUID randomUUID(String site) {
        Random draw = new Random(seed(key(site)));
        long most = (draw.nextLong() & ~0xF000L) | 0x4000L;
        long least = (draw.nextLong() & ~(0xC000000000000000L))
                | 0x8000000000000000L;
        return new UUID(most, least);
    }
}
