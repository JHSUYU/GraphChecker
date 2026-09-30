package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

/**
 * A node's clock runs on from its jumps in the RECORDING's order, one clock
 * at a time ({@link NodeClocks}).
 */
public class NodeClocksTest {
    private static final long MS = 1_000_000L;
    /** A wall-clock instant and a monotonic one, both in milliseconds. */
    private static final long WALL = 1_790_775_785_501L;
    private static final long MONO = 183_934_881L;

    @Before
    public void reset() {
        NodeClocks.reset();
    }

    @Test
    public void aReadingRunsOnFromTheJumpBeforeItInTheRecordingsOrder() {
        // Planted in THIS order: the later place first, as two threads may.
        NodeClocks.jump("nn0", MS, 200L, WALL + 10, 3_600_000L);
        NodeClocks.jump("nn0", MS, 100L, WALL, 60_000L);
        assertEquals("a plant the recording states no event for moves its "
                + "reading alone", false, NodeClocks.jump("dn1", MS, 0L,
                WALL, 60_000L));
        Object[][] readings = {
                // node, tick, place, host reading, skew it runs at, why
                {"nn0", MS, 50L, WALL - 5, 0L, "before every jump: the host"},
                {"nn0", MS, 100L, WALL, 60_000L, "the jump's own cell"},
                {"nn0", MS, 150L, WALL + 5, 60_000L,
                        "between: the earlier jump, whichever was planted "
                                + "last here"},
                {"nn0", MS, 300L, WALL + 20, 3_600_000L,
                        "after both: the later jump"},
                {"nn0", MS, 300L, MONO, 0L,
                        "the node's monotonic clock is another clock"},
                {"nn0", 1L, 300L, WALL + 20, 0L, "another tick, another clock"},
                {"dn1", MS, 300L, WALL + 20, 0L, "another node's clock"},
                {"nn0", MS, 0L, WALL + 20, 0L,
                        "a reading the recording states no event for is on "
                                + "no clock's order"},
        };
        for (Object[] reading : readings) {
            assertEquals((String) reading[5], ((Long) reading[4]).longValue(),
                    NodeClocks.skew((String) reading[0], (Long) reading[1],
                            (Long) reading[2], (Long) reading[3]));
        }
    }
}
