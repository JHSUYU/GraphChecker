package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Test;

/**
 * The end of a run: its settle gives up only on a grace in which nothing
 * moved, and an activation stranded there is settled in one step, its own
 * terminal still finding it.
 */
public class EndOfRunTest {
    private static final long TOKEN = 990001L;

    @After
    public void clear() {
        ConcolicRegionRuntime.ACTIVE.remove(TOKEN);
        ConcolicRegionRuntime.STRANDED.remove(TOKEN);
    }

    @Test
    public void theGraceRestartsOnEveryMoveAndIsSpentOnlyWhenNothingMoved() {
        ConcolicResultPublisher.Grace grace = new ConcolicResultPublisher
                .Grace(100L, 0L, new long[] {1L, 0L});
        long[][] table = {
                // now, progress..., remaining
                {0L, 1L, 0L, 100L},
                {60L, 1L, 0L, 40L},
                {70L, 1L, 5L, 100L},
                {150L, 1L, 5L, 20L},
                {180L, 1L, 5L, -10L},
        };
        for (long[] row : table) {
            assertEquals("at " + row[0], row[3], grace.remaining(row[0],
                    new long[] {row[1], row[2]}));
        }
    }

    @Test
    public void aStrandIsOneStepAndTheOwnersTerminalStillTakesIt()
            throws Exception {
        ActiveRegion active = live();
        assertTrue(ConcolicRegionRuntime.strand(active));
        assertTrue(active.finished.get() && active.abandoned);
        assertFalse("out of the run", ConcolicRegionRuntime.ACTIVE
                .containsKey(TOKEN));
        assertSame(active, ConcolicRegionRuntime.STRANDED.get(TOKEN));
        assertFalse("once", ConcolicRegionRuntime.strand(active));
        try {
            // Its own terminal, on its own thread: it closes the VM region,
            // which this JVM has no VM to do.
            ConcolicRegionRuntime.finish(TOKEN, "NORMAL", "", null);
        } catch (RuntimeException noVm) {
            // The region it tried to close is the VM's.
        }
        assertFalse("its terminal took it", ConcolicRegionRuntime.STRANDED
                .containsKey(TOKEN));
    }

    @Test
    public void aTerminalThatWinsLeavesNothingToStrand() {
        ActiveRegion active = live();
        assertTrue(active.finished.compareAndSet(false, true));
        assertFalse(ConcolicRegionRuntime.strand(active));
        assertTrue("still the run's to close", ConcolicRegionRuntime.ACTIVE
                .containsKey(TOKEN));
        assertFalse(ConcolicRegionRuntime.STRANDED.containsKey(TOKEN));
    }

    /** One live activation of this thread. */
    private static ActiveRegion live() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "hdfs/nn0#epoch0");
        encoded.addProperty("occurrenceId",
                "hdfs/nn0#epoch0/region/REGION.1#1");
        encoded.addProperty("rootMethod", "<a.B: void run()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", "<a.B: void run()>");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "hdfs/nn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branchMethods", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("defaultBackedgeTraversals", 8);
        encoded.add("loopBound", loopBound);
        ActiveRegion active = new ActiveRegion(TOKEN,
                new ConcolicTaskPlan.RuntimeTask(
                        ExecutionTask.decode(encoded)),
                null, Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(TOKEN, active);
        return active;
    }
}
