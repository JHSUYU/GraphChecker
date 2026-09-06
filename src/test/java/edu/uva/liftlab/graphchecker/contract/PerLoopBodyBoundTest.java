package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;

/**
 * README section 5's {@code K_L} is per loop, and the executor limit is
 * derived from the declarations rather than fixed beside them.
 *
 * <pre>
 * Every loop L retained by an accepted model must declare K_L, the maximum
 * number of loop-body executions.  GraphChecker translates it to the
 * executor's internal backedge limit and rejects an observed count above K_L.
 * </pre>
 *
 * <p>The one property these cases exist for is the direction the bounded
 * semantics may not fail in: the backedge limit the executor is instrumented
 * with is never below a bound the model states.  A limit below it would cut a
 * replay before the prefix the model holds and produce a relation for a
 * prefix the run never completed.</p>
 */
public class PerLoopBodyBoundTest {

    private static final String LOOKUP =
            "<example.DataNode: java.lang.Object lookup(int)>#u12";
    private static final String ROTATION =
            "<example.NameNode: void rotate()>#u3";

    // ------------------------------------------------------------------
    // The declaration
    // ------------------------------------------------------------------

                    // ------------------------------------------------------------------
    // The translation to the executor
    // ------------------------------------------------------------------

            /** Each loop's own {@code K_L} is what the instrumenter can narrow to. */
    @Test
    public void eachLoopAnswersWithItsOwnBound() {
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(LOOKUP, Integer.valueOf(60));
        LoopBoundPolicy policy = LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared);

        assertEquals(60, policy.maxBackedgeTraversals(LOOKUP));
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals(ROTATION));
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals(null));
    }

        // ------------------------------------------------------------------
    // The encoded contract
    // ------------------------------------------------------------------

                    }
