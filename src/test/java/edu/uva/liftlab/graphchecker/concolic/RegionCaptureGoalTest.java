package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RegionCaptureGoalTest {
    @Test
    public void captureGoalIsARequestAndNotARegionCategory() {
        JsonObject row = new JsonObject();
        row.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());

        RegionCaptureGoal goal = RegionCaptureGoal.from(row);

        assertTrue(goal.isOutputClosure());
        assertEquals("BOUNDED_OUTPUT_RELEVANT_PATHS",
                goal.toJson().get("scope").getAsString());
    }

    @Test
    public void legacyModeIsRejected() {
        JsonObject row = new JsonObject();
        row.addProperty("summaryMode", "RELATIONAL_PRODUCER");

        try {
            RegionCaptureGoal.from(row);
            fail("legacy capture mode was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("captureGoal"));
        }
    }

    @Test
    public void transitionDiscoveryUsesOutputCaptureButIsQuarantined() {
        JsonObject row = new JsonObject();
        row.add("captureGoal", RegionCaptureGoal.transitionDiscovery()
                .toJson());

        RegionCaptureGoal goal = RegionCaptureGoal.from(row);

        assertTrue(goal.isOutputClosure());
        assertTrue(goal.isTransitionDiscovery());
        assertEquals(RegionCaptureGoal.TRANSITION_DISCOVERY,
                goal.purpose());
        assertEquals("QUARANTINED_UNTIL_SAME_EXECUTION_RUNTIME_EDGE",
                goal.toJson().get("cacheAdmission").getAsString());
    }
}
