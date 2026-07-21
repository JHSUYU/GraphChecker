package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class MixedTypeThreeThreadRpcWorkloadTest {
    @Test
    public void safeSeedAndMixedTypeBugWitnessUseRealThreads()
            throws Exception {
        MixedTypeThreeThreadRpcWorkload.RunResult safe =
                MixedTypeThreeThreadRpcWorkload.execute(false, false,
                        0, 0L, 0.5d, "plain");
        assertEquals(-5, safe.getA());
        assertEquals(11, safe.getB());
        assertFalse(safe.isBugReached());

        MixedTypeThreeThreadRpcWorkload.RunResult bug =
                MixedTypeThreeThreadRpcWorkload.execute(true, false,
                        1, 101L, 1.5d, "has-needle");
        assertEquals(12, bug.getA());
        assertEquals(11, bug.getB());
        assertTrue(bug.isBugReached());
    }

    @Test
    public void loopIsClampedToThreeIterations() {
        MixedTypeThreeThreadRpcWorkload.MixedProducer producer =
                new MixedTypeThreeThreadRpcWorkload.MixedProducer();
        assertEquals(14, producer.compute(true, 100, 101L,
                1.5d, "needle"));
        assertEquals(11, producer.compute(true, -1, 101L,
                1.5d, "needle"));
    }
}
