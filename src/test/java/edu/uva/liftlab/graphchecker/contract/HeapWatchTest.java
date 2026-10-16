package edu.uva.liftlab.graphchecker.contract;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/** An engine JVM is out of heap when it only collects with its old
 *  generation full ({@link HeapWatch}): {collecting, full, out of heap}. */
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
}
