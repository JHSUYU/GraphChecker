package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RegionCaptureGoalTest {
    @Test
    public void captureGoalIsARequestAndNotARegionCategory() {
        JsonObject row = new JsonObject();
        row.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());

        RegionCaptureGoal goal = RegionCaptureGoal.from(row);

        assertTrue(goal.isOutputClosure());
        assertFalse(goal.cameFromLegacySchema());
        assertEquals("BOUNDED_OUTPUT_RELEVANT_PATHS",
                goal.toJson().get("scope").getAsString());
    }

    @Test
    public void legacyModeIsTranslatedOnlyAtSchemaBoundary() {
        JsonObject row = new JsonObject();
        row.addProperty("summaryMode", "RELATIONAL_PRODUCER");

        RegionCaptureGoal goal = RegionCaptureGoal.from(row);

        assertTrue(goal.isOutputClosure());
        assertTrue(goal.cameFromLegacySchema());
        assertEquals(RegionCaptureGoal.OUTPUT_CLOSURE, goal.kind());
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
