package edu.uva.liftlab.graphchecker.smt;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/** A z3 carries its own hard timeout, whole seconds ten past its budget. */
public class Z3Test {
    @Test
    public void aZ3StopsItselfTenSecondsPastItsBudget() {
        long[][] table = {
                // budget ms, -T seconds
                {1L, 11L},
                {1_000L, 11L},
                {1_500L, 12L},
                {20_000L, 30L},
                {1_800_000L, 1_810L},
        };
        for (long[] row : table) {
            assertEquals("budget " + row[0] + " ms", "-T:" + row[1],
                    Z3.hardTimeout(row[0]));
        }
    }
}
