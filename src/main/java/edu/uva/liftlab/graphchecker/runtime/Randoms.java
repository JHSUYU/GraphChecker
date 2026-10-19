package edu.uva.liftlab.graphchecker.runtime;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

public final class Randoms {
    private static final Map<String, AtomicLong> COUNTS =
            new ConcurrentHashMap<String, AtomicLong>();

    private Randoms() {
    }

    static String key(String site) {
        String scope = RecordingWindow.opened()
                ? ScheduleLog.contextOf(Identity.contextHere())
                : RuntimeTraceContext.nodeHere() + "|" + Identity.handoffs();
        String counted = RecordingWindow.index() + "#" + scope + "#" + site;
        return counted + "#" + COUNTS.computeIfAbsent(counted,
                ignored -> new AtomicLong()).getAndIncrement();
    }

    static long seed(String key) {
        long seed = 1125899906842597L;
        for (int i = 0; i < key.length(); i++) {
            seed = 31 * seed + key.charAt(i);
        }
        seed = (seed ^ (seed >>> 33)) * 0xff51afd7ed558ccdL;
        seed = (seed ^ (seed >>> 33)) * 0xc4ceb9fe1a85ec53L;
        return seed ^ (seed >>> 33);
    }

    public static Random at(String site) {
        return new Random(seed(key(site)));
    }

    public static int nextInt(Random random, int origin, int bound) {
        return random.ints(1L, origin, bound).iterator().nextInt();
    }

    public static long nextLong(Random random, long bound) {
        return nextLong(random, 0L, bound);
    }

    public static long nextLong(Random random, long origin, long bound) {
        return random.longs(1L, origin, bound).iterator().nextLong();
    }

    public static double nextDouble(Random random, double bound) {
        return nextDouble(random, 0.0, bound);
    }

    public static double nextDouble(Random random, double origin,
                                    double bound) {
        return random.doubles(1L, origin, bound).iterator().nextDouble();
    }

    public static double random(String site) {
        return new Random(seed(key(site))).nextDouble();
    }

    public static void shuffle(List<?> list, String site) {
        Collections.shuffle(list, new Random(seed(key(site))));
    }

    public static UUID randomUUID(String site) {
        Random draw = new Random(seed(key(site)));
        long most = (draw.nextLong() & ~0xF000L) | 0x4000L;
        long least = (draw.nextLong() & ~(0xC000000000000000L))
                | 0x8000000000000000L;
        return new UUID(most, least);
    }
}
