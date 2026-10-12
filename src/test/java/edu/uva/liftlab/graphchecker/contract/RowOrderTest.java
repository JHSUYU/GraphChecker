package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

/** The one order of a session's rows ({@link RowOrder}). */
public class RowOrderTest {
    @Test
    public void rowsStandBySeqThenEngineTiesThenTheVmEventOfTheSeq() {
        Object[][] rows = {
                // seq, tie, other seq, other tie, before?
                {41L, 0, 42L, 1, true},   // a VM event, then the engine's row
                {42L, 1, 42L, 0, true},   // the engine's row, then VM event 42
                {42L, 0, 42L, 1, false},
                {42L, 1, 42L, 2, true},   // a decode, then the read of it
                {42L, 2, 42L, 1, false},  // the read, then a newer decode
                {42L, 1, 42L, 1, false},
                {42L, 0, 42L, 0, false},
                {0L, 0, 42L, 1, false},   // no clock orders nothing
                {42L, 1, 0L, 0, false},
                {43L, 1, 42L, 5, false},
        };
        for (Object[] row : rows) {
            assertEquals(java.util.Arrays.toString(row), row[4],
                    RowOrder.before((Long) row[0], (Integer) row[1],
                            (Long) row[2], (Integer) row[3]));
        }
        Object[][] cutoffs = {
                // seq, tie, the VM event, before it?
                {41L, 0, 42L, true},
                {42L, 1, 42L, true},   // the guard's read, then its branch
                {42L, 0, 42L, false},
                {43L, 1, 42L, false},
                {0L, 0, 42L, true},    // no clock: as seq < event
        };
        for (Object[] row : cutoffs) {
            assertEquals(java.util.Arrays.toString(row), row[3],
                    RowOrder.beforeEvent((Long) row[0], (Integer) row[1],
                            (Long) row[2]));
        }
    }
}
