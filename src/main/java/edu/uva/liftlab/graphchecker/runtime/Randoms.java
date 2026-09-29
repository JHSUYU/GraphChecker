package edu.uva.liftlab.graphchecker.runtime;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;

/**
 * THE unseeded randomness of the application scope, seeded by where it is
 * drawn.  The weave replaces {@code new Random()}, {@code Math.random()},
 * {@code Collections.shuffle(List)} and {@code UUID.randomUUID()} with these
 * in BOTH passes, so a replay draws what the recording drew: a Solr client
 * shuffles the live nodes it sends an admin request to, and a replay that
 * sent it to another node than the recording did held no order past it.
 *
 * <p>Inside the window a draw is seeded by its endpoint: the occurrence it
 * runs in, its site and its count there -- the same function of the same
 * inputs in both passes.  Before the window no occurrence stands, and a draw
 * is seeded by its site and its count at that site.</p>
 */
public final class Randoms {
    private static final Map<String, AtomicLong> BEFORE_WINDOW =
            new ConcurrentHashMap<String, AtomicLong>();

    private Randoms() {
    }

    /** The seed of the draw at {@code site} here. */
    static long seed(String site) {
        String key;
        if (RecordingWindow.opened()) {
            SourceRef source = RuntimeTraceContext.ownedSource(null);
            OccurrenceAddress occurrence = Identity.currentOccurrence(
                    source == null ? "" : source.key());
            Endpoint at = Identity.endpointAt(occurrence, "random#" + site, 0);
            key = at == null ? site : at.id();
        } else {
            key = site + "#" + BEFORE_WINDOW.computeIfAbsent(site,
                    ignored -> new AtomicLong()).getAndIncrement();
        }
        long seed = 1125899906842597L;
        for (int i = 0; i < key.length(); i++) {
            seed = 31 * seed + key.charAt(i);
        }
        return seed;
    }

    /** {@code new Random()}'s seed. */
    public static long constructed(String site) {
        return seed(site);
    }

    /** {@code Math.random()}. */
    public static double random(String site) {
        return new Random(seed(site)).nextDouble();
    }

    /** {@code Collections.shuffle(list)}. */
    public static void shuffle(List<?> list, String site) {
        Collections.shuffle(list, new Random(seed(site)));
    }

    /** {@code UUID.randomUUID()}: a version-4 UUID from the seeded draw. */
    public static UUID randomUUID(String site) {
        Random draw = new Random(seed(site));
        long most = (draw.nextLong() & ~0xF000L) | 0x4000L;
        long least = (draw.nextLong() & ~(0xC000000000000000L))
                | 0x8000000000000000L;
        return new UUID(most, least);
    }
}
