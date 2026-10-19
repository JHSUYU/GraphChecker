package edu.uva.liftlab.graphchecker.contract;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class HeapWatchTest {
    @Test
    public void aJvmThatOnlyCollectsOverAFullOldGenerationIsOutOfHeap() {
        double[][] rows = {
            {0.51, 0.99, 1},
            {0.51, 0.70, 0},
            {0.05, 0.99, 0},
        };
        for (double[] row : rows) {
            assertEquals(row[0] + "/" + row[1], row[2] == 1,
                    HeapWatch.outOfHeap(row[0], row[1]));
        }
    }

    @Test
    public void aJvmHoldsItsNextReadWhileItsLiveSetLeavesTheRoom() {
        long[][] rows = {
            {14500, 17203, 1000, 1},
            {14500, 17203, 13574, 0},
            {17600, 17203, 0, 0},
            {0, 17203, 40000, 1},
            {0, 17203, 50000, 0},
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
