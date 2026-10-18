package edu.uva.liftlab.graphchecker.contract;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/** An engine JVM is out of heap when it only collects with its old
 *  generation full ({@link HeapWatch}): {collecting, full, out of heap};
 *  it holds its next read while its live set at its highest and a third of
 *  the files it reads now stay under 90 % of its old generation. */
public class HeapWatchTest {
    @Test
    public void aJvmThatOnlyCollectsOverAFullOldGenerationIsOutOfHeap() {
        double[][] rows = {
            {0.51, 0.99, 1},   // SGF7-adhoc-10's planner
            {0.51, 0.70, 0},   // collecting, but its sweeps free the heap
            {0.05, 0.99, 0},   // full, but computing
        };
        for (double[] row : rows) {
            assertEquals(row[0] + "/" + row[1], row[2] == 1,
                    HeapWatch.outOfHeap(row[0], row[1]));
        }
    }

    /** {peak live MB, old generation MB, MB of files to read, holds}. */
    @Test
    public void aJvmHoldsItsNextReadWhileItsLiveSetLeavesTheRoom() {
        long[][] rows = {
            // SGF8-adhoc-05 round 6: ~14.5 GB live of a 21.5 GB heap (old
            // generation 17203 MB), ~1 GB of new sessions: asked.
            {14500, 17203, 1000, 1},
            // A round of 312 new sessions (13.5 GB) beside it: not.
            {14500, 17203, 13574, 0},
            // 40 planning-7: 9.3 GB live, then past the heap in the frontier
            // -- the peak of the round before is what is carried.
            {17600, 17203, 0, 0},
            {0, 17203, 40000, 1},
            {0, 17203, 50000, 0},
            // Nothing measured yet: it holds it.
            {0, 0, 1 << 20, 1},
        };
        for (long[] row : rows) {
            String past = HeapWatch.outgrown("the planner", row[0] << 20,
                    row[1] << 20, row[2] << 20);
            assertEquals(java.util.Arrays.toString(row) + ": " + past,
                    row[3] == 1, past == null);
            if (past != null) {
                assertTrue(past, past.startsWith("the planner needs ~")
                        && past.contains(row[0] + " MB live at its highest"));
            }
        }
    }
}
