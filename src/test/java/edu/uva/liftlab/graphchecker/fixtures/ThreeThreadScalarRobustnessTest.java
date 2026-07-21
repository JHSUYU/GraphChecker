package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/** Small concrete sanity checks for the three scalar fixture shapes. */
public class ThreeThreadScalarRobustnessTest {
    @Test
    public void stringPredicatesHaveSafeAndBugExecutions()
            throws Exception {
        StringPredicateThreeThreadWorkload.RunResult safe =
                StringPredicateThreeThreadWorkload.execute(true,
                        "pre-plain-end", false);
        assertFalse(safe.isBugReached());
        assertNull(safe.getFailure());

        StringPredicateThreeThreadWorkload.RunResult bug =
                StringPredicateThreeThreadWorkload.execute(true,
                        "pre-needle-end", false);
        assertTrue(bug.isBugReached());
        assertEquals(StringPredicateThreeThreadWorkload.CONSUMER_THREAD,
                bug.getFailureThread());
    }

    @Test
    public void numericLoopHasSafeAndBugExecutions() throws Exception {
        NumericLoopThreeThreadWorkload.RunResult safe =
                NumericLoopThreeThreadWorkload.execute(false, false,
                        0, 0L, 0.5d);
        assertFalse(safe.isBugReached());
        assertNull(safe.getFailure());

        NumericLoopThreeThreadWorkload.RunResult bug =
                NumericLoopThreeThreadWorkload.execute(true, false,
                        2, 101L, 1.5d);
        assertTrue(bug.isBugReached());
        assertEquals(NumericLoopThreeThreadWorkload.CONSUMER_THREAD,
                bug.getFailureThread());
    }

    @Test
    public void dependentScalarsNeedBothProducerRelations()
            throws Exception {
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
