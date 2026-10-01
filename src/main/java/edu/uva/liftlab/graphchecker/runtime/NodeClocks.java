package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Clock;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The clocks of the nodes one replay runs.  A declared clock reading reads
 * its node's clock: the host's reading moved by the skew of the jump before
 * it.  A plant is a jump: the planted reading reads its plant, and its clock
 * runs on from there, so a later reading nothing asks a skew of reads the
 * host plus that skew.  Read off the host alone it fell back behind the
 * plant, and no clock runs so (SOLR-18406 wave 0: a commit's delete() of G
 * read the hour it was skewed by, its delete() of the older commit a moment
 * later the host's clock, and COMPOSE's clock order refuted the path).
 *
 * <p>"Before" is the RECORDING's order.  A reading's place is the event the
 * recording observed it at ({@code SymbolizeAction#eventSeq}, the seq its
 * mint row states), and it runs on from the jump on its clock latest at or
 * before that place -- never by this replay's order, in which two threads of
 * one node may plant either way round.  COMPOSE orders a node's cells by
 * the same seq ({@code Composer#clocks}) and the claim names the same jumps
 * ({@code ClaimPolicy#runsOn}).  One clock is what COMPOSE orders as one
 * ({@link Clock#same}: one JVM clock at one tick): the wall clock and a
 * monotonic one of a node, both in milliseconds, are two.  A reading whose
 * clock states no source is on no clock's order: it reads the host, and a
 * plant there moves it alone.</p>
 */
final class NodeClocks {
    /** One plant: its clock, its place, the skew. */
    private static final class Jump {
        private final Clock clock;
        private final long place;
        private final long skew;

        private Jump(Clock clock, long place, long skew) {
            this.clock = clock;
            this.place = place;
            this.skew = skew;
        }
    }

    /** Node -> its jumps, in the order this replay planted them. */
    private static final Map<String, List<Jump>> JUMPS =
            new ConcurrentHashMap<String, List<Jump>>();

    private NodeClocks() {
    }

    static void reset() {
        JUMPS.clear();
    }

    /**
     * The skew one reading of a node's clock runs at: that of the jump on
     * its clock latest at or before its place (of two at one place, the one
     * planted last), 0 when there is none.  A reading with no place (the
     * recording states no event for it, {@code place <= 0}) is on no clock's
     * order and reads the host.
     */
    static long skew(String node, Clock clock, long place) {
        List<Jump> jumps = JUMPS.get(node);
        if (jumps == null || place <= 0L) return 0L;
        synchronized (jumps) {
            Jump latest = null;
            for (Jump jump : jumps) {
                if (jump.place > place || !jump.clock.same(clock)) {
                    continue;
                }
                if (latest == null || jump.place >= latest.place) {
                    latest = jump;
                }
            }
            return latest == null ? 0L : latest.skew;
        }
    }

    /**
     * Files one plant as a jump of its node's clock; false for a reading
     * with no place or a clock stating no source, which the plant moves
     * alone.
     */
    static boolean jump(String node, Clock clock, long place, long skew) {
        if (place <= 0L || clock.source().isEmpty()) return false;
        List<Jump> jumps = JUMPS.computeIfAbsent(node,
                key -> new ArrayList<Jump>());
        synchronized (jumps) {
            jumps.add(new Jump(clock, place, skew));
        }
        return true;
    }
}
