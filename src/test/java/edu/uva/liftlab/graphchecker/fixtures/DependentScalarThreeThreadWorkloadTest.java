package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/** Concrete sanity check for the maintained dependent-scalar workload. */
public class DependentScalarThreeThreadWorkloadTest {
    @Test
    public void bothProducerRelationsAreRequired() throws Exception {
        DependentScalarThreeThreadWorkload.RunResult safe =
                DependentScalarThreeThreadWorkload.execute(true, 4,
                        "plain");
        assertFalse(safe.isBugReached());
        assertNull(safe.getFailure());

        DependentScalarThreeThreadWorkload.RunResult bug =
                DependentScalarThreeThreadWorkload.execute(true, 4,
                        "ready");
        assertTrue(bug.isBugReached());
        assertEquals(DependentScalarThreeThreadWorkload.CONSUMER_THREAD,
                bug.getFailureThread());
    }
}
