package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * README section 5: "GraphChecker translates it to the executor's internal
 * backedge limit."
 *
 * <p>The scheduler is where that translation happens.  Every scheduled task
 * carries one {@code loopBound} contract, the instrumenter reads its limit,
 * and the runtime refuses a hook stamped under any other - so the limit has
 * to be derived from the {@code K_L} the planned body instances were minted
 * under rather than fixed beside them.</p>
 */
public class ScheduledLoopBoundTest {

    private static final int INHERITED =
            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
    private static final String LOOKUP =
            "<example.DataNode: java.lang.Object lookup(int)>#u12";
    private static final String ROTATION =
            "<example.NameNode: void rotate()>#u3";

    /** A plan that retains no loop keeps the contract it always had. */
    @Test
    public void aPlanWithNoRetainedLoopKeepsTheInheritedContract() {
        LoopBoundPolicy policy = ConcolicScheduler.declaredLoopBounds(
                INHERITED, Arrays.asList(nonLoopRow(), nonLoopRow()));

        assertEquals(INHERITED, policy.maxBackedgeTraversals());
        assertTrue(policy.declaredBounds().isEmpty());
        assertEquals(LoopBoundPolicy.cfgBackedges(INHERITED).identity(),
                policy.identity());
    }

    /**
     * A declared bound reaches the executor limit of every scheduled task.
     *
     * <p>Without this the model would hold {@code K_L} slots the replay is
     * cut before reaching, which is the one direction the bounded semantics
     * may not fail in.</p>
     */
    @Test
    public void aDeclaredBoundRaisesTheExecutorLimit() {
        LoopBoundPolicy policy = ConcolicScheduler.declaredLoopBounds(
                INHERITED, Arrays.asList(
                        loopRow(LOOKUP, 0, 60),
                        loopRow(LOOKUP, 1, 60),
                        loopRow(ROTATION, 0, 4)));

        assertEquals(60, policy.maxBackedgeTraversals());
        assertEquals(60, policy.maxBackedgeTraversals(LOOKUP));
        assertEquals(4, policy.maxBackedgeTraversals(ROTATION));
        assertEquals(2, policy.declaredBounds().size());
    }

    /**
     * A loop minted under the inherited bound declares nothing of its own.
     *
     * <p>Recording it would resolve to the same {@code K_L} and move the
     * contract identity of every campaign that declares nothing, so a run
     * that retains an ordinary loop keeps the artifacts it already had.</p>
     */
    @Test
    public void anInheritedBoundIsNotRecordedAsADeclaration() {
        LoopBoundPolicy policy = ConcolicScheduler.declaredLoopBounds(
                INHERITED, Collections.singletonList(
                        loopRow(ROTATION, 0, INHERITED)));

        assertEquals(INHERITED, policy.maxBackedgeTraversals());
        assertTrue(policy.declaredBounds().isEmpty());
    }

    /** One loop has one prefix, so two bounds for it are refused by name. */
    @Test
    public void twoBoundsForOneLoopAreRefusedByName() {
        List<JsonObject> rows = new ArrayList<>();
        rows.add(loopRow(LOOKUP, 0, 60));
        rows.add(loopRow(LOOKUP, 1, 32));
        try {
            ConcolicScheduler.declaredLoopBounds(INHERITED, rows);
            fail("expected a refusal for two bounds of one loop");
        } catch (IllegalStateException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES));
        }
    }

    /** A bound above the per-loop ceiling never becomes an executor limit. */
    @Test
    public void aBoundAboveTheCeilingIsRefused() {
        try {
            ConcolicScheduler.declaredLoopBounds(INHERITED,
                    Collections.singletonList(loopRow(LOOKUP, 0,
                            LoopBoundPolicy
                                    .MAX_DECLARED_LOOP_BODY_ITERATIONS + 1)));
            fail("expected a refusal above the ceiling");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    LoopBoundPolicy.DECLARED_BOUND_OUT_OF_RANGE));
        }
    }

    private static JsonObject nonLoopRow() {
        JsonObject row = new JsonObject();
        row.addProperty("occurrenceId", "cluster/nn#epoch0/region/R#1");
        return row;
    }

    private static JsonObject loopRow(String loopSiteId, int iterationIndex,
                                      int bodyBound) {
        JsonObject row = nonLoopRow();
        JsonObject loop = new JsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, bodyBound);
        com.google.gson.JsonArray loops = new com.google.gson.JsonArray();
        loops.add(loop);
        row.add(BoundedLoopComposition.PLAN_FIELD, loops);
        return row;
    }
}
