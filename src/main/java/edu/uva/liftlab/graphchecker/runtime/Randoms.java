package edu.uva.liftlab.graphchecker.runtime;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * THE randomness of the application scope, keyed by where it is drawn.
 * The weave makes every draw on a Random receiver (Random, ThreadLocalRandom,
 * SecureRandom) a draw on {@link #at}, whatever seed the Random was built
 * with, a Random handed to a JDK method {@link #at} at that call, and {@code Math.random()}, {@code
 * Collections.shuffle(List)} and {@code UUID.randomUUID()} these stand-ins,
 * in BOTH passes, so a replay draws what the recording drew, never a
 * stream's next value whatever was drawn from it before: a Solr client
 * shuffles the live nodes it sends an admin request to, and a replay that
 * sent it to another node than the recording did held no order past it.
 *
 * <p>A draw is keyed by what no weave moves: inside the window, its schedule
 * context ({@link ScheduleLog#contextOf}: node, causal context and the
 * starts it was handed on through), its site, and its count under that key;
 * before the window, where no context is ordered, its node and handoffs in
 * place of the context.  Never an occurrence or an endpoint: a GROW weaves
 * new regions, whose occurrences and endpoints are new ids (IDENTITY §9),
 * so a draw keyed by its endpoint drew another value in every replay after
 * the GROW, and a block placement another pipeline (hdfs-adhoc-01/42).  The
 * counts restart at each window.  A key one thread alone draws under counts
 * in that thread's program order, the same in both passes; threads that
 * share one (unnamed work of one node, started under no hop: round HS1's
 * DataNodes, which drew one UUID before draws were counted and refused each
 * other's registrations) take its counts in the run's arrival order,
 * so two runs may hand them each other's values: distinct is what is
 * guaranteed there, not equal.</p>
 */
public final class Randoms {
    /** Per window, context (or node and handoffs) and site, the draws
     *  keyed by their count so far. */
    private static final Map<String, AtomicLong> COUNTS =
            new ConcurrentHashMap<String, AtomicLong>();

    private Randoms() {
    }

    /** What the draw at {@code site} here is keyed by (class comment). */
    static String key(String site) {
        String scope = RecordingWindow.opened()
                ? ScheduleLog.contextOf(Identity.contextHere())
                : RuntimeTraceContext.nodeHere() + "|" + Identity.handoffs();
        String counted = RecordingWindow.index() + "#" + scope + "#" + site;
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

    /**
     * The Random one draw at {@code site} draws from, seeded by its key: a
     * fresh one per draw, so the draw is a function of where it is drawn
     * alone (a bounded draw only ThreadLocalRandom declares goes through the
     * helpers below).
     */
    public static Random at(String site) {
        return new Random(seed(key(site)));
    }

    /** {@code ThreadLocalRandom#nextInt(int, int)} on {@code random}: the
     *  bounded draws below are Random's own bounded streams, one long. */
    public static int nextInt(Random random, int origin, int bound) {
        return random.ints(1L, origin, bound).iterator().nextInt();
    }

    /** {@code ThreadLocalRandom#nextLong(long)} on {@code random}. */
    public static long nextLong(Random random, long bound) {
        return nextLong(random, 0L, bound);
    }

    /** {@code ThreadLocalRandom#nextLong(long, long)} on {@code random}. */
    public static long nextLong(Random random, long origin, long bound) {
        return random.longs(1L, origin, bound).iterator().nextLong();
    }

    /** {@code ThreadLocalRandom#nextDouble(double)} on {@code random}. */
    public static double nextDouble(Random random, double bound) {
        return nextDouble(random, 0.0, bound);
    }

    /** {@code ThreadLocalRandom#nextDouble(double, double)} on {@code
     *  random}. */
    public static double nextDouble(Random random, double origin,
                                    double bound) {
        return random.doubles(1L, origin, bound).iterator().nextDouble();
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
