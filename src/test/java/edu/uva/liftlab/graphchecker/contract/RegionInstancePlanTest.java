package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RegionInstancePlanTest {
    @Test
    public void decodesOneGoalOwnedByOneSkeletonOccurrence() {
        RegionInstancePlan plan = RegionInstancePlan.decode(
                plan("OCC.1", targetGoal("GOAL.1")));

        assertEquals("nn0#epoch1", plan.sourceKey());
        assertEquals("OCC.1", plan.occurrenceId());
        assertEquals("REL.1", plan.relationKey());
        assertEquals("HASH.1", plan.relationContractHash());
        assertEquals("REGION.1", plan.regionId());
        assertTrue(plan.containsOccurrence("OCC.1"));
        assertFalse(plan.containsOccurrence("OCC.2"));
        assertEquals(1, plan.goals().size());
        assertEquals("GOAL.1", plan.goals().get(0).goalId());
        assertEquals(ClosureGoalKind.TARGET_REACH_CLOSURE,
                plan.goals().get(0).kind());
    }

    @Test
    public void sameRelationMayHaveIndependentOccurrences() {
        RegionInstancePlan first = RegionInstancePlan.decode(
                plan("OCC.1", targetGoal("GOAL.1")));
        RegionInstancePlan second = RegionInstancePlan.decode(
                plan("OCC.2", targetGoal("GOAL.2")));

        assertEquals(first.relationKey(), second.relationKey());
        assertEquals(first.relationContractHash(),
                second.relationContractHash());
        assertFalse(first.occurrenceId().equals(second.occurrenceId()));
    }

    @Test
    public void outputClosureMustMatchReusableRelationIdentity() {
        RegionInstancePlan decoded = RegionInstancePlan.decode(
                plan("OCC.1", outputGoal("GOAL.1")));
        OutputClosureContract closure = decoded.goals().get(0)
                .outputClosure();
        assertEquals("REL.1", closure.producer().relationKey());
        assertEquals("HASH.1", closure.producer().contractHash());

        JsonObject mismatched = plan("OCC.1", outputGoal("GOAL.1"));
        mismatched.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .getAsJsonObject(OutputClosureContract.FIELD)
                .getAsJsonObject("producer")
                .addProperty("contractHash", "HASH.other");
        expectFailure(() -> RegionInstancePlan.decode(mismatched),
                "conflicts with relation");
    }

    @Test
    public void legacyExpandedPlanFailsInsteadOfBeingCompacted() {
        for (String retired : new String[] {
                "regionInstanceId", "rootCallId", "logicalRegionId",
                "logicalInstanceCount", "summaryReuseKey", "occurrences",
                "occurrenceInstantiationCatalog"}) {
            JsonObject legacy = plan("OCC.1", targetGoal("GOAL.1"));
            legacy.addProperty(retired, "old");
            expectFailure(() -> RegionInstancePlan.decode(legacy),
                    "retired field " + retired);
        }
    }

    @Test
    public void goalCannotRedirectExecutionToAnotherOccurrence() {
        JsonObject redirect = targetGoal("GOAL.1");
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrenceId", "OCC.2");
        redirect.add("executionOccurrence", occurrence);
        expectFailure(() -> RegionInstancePlan.decode(
                plan("OCC.1", redirect)),
                "retired field executionOccurrence");
    }

    @Test
    public void duplicateGoalIdsFailWithinOccurrence() {
        JsonObject encoded = plan("OCC.1", targetGoal("GOAL.1"));
        encoded.getAsJsonArray("closureGoals").add(
                targetGoal("GOAL.1"));
        expectFailure(() -> RegionInstancePlan.decode(encoded),
                "goal ids must be unique");
    }

    private static JsonObject plan(String occurrenceId, JsonObject goal) {
        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", 4);
        plan.addProperty("kind", "CONCOLIC_REGION_PLAN");
        plan.addProperty("sourceKey", "nn0#epoch1");
        plan.addProperty("occurrenceId", occurrenceId);
        plan.addProperty("relationKey", "REL.1");
        plan.addProperty("relationContractHash", "HASH.1");
        plan.addProperty("regionId", "REGION.1");
        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        return plan;
    }

    private static JsonObject targetGoal(String goalId) {
        JsonObject goal = baseGoal(goalId, "TARGET_REACH_CLOSURE");
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());
        goal.add("edgeBindings", new JsonArray());
        return goal;
    }

    private static JsonObject outputGoal(String goalId) {
        JsonObject goal = baseGoal(goalId, "OUTPUT_RELATION_CLOSURE");
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());
        goal.add("edgeBindings", new JsonArray());
        goal.add(OutputClosureContract.FIELD, closure().toJson());
        return goal;
    }

    private static JsonObject baseGoal(String id, String kind) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", id);
        goal.addProperty("kind", kind);
        goal.add("runtimeDefinitionMethods", strings("<P: void run()>"));
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);
        return goal;
    }

    private static OutputClosureContract closure() {
        String port = "REGION.1.out.value";
        String cell = "<P: int value>";
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings("REGION.1.in.0"));
        slice.add("sites", strings("<P: void run()>#u1"));
        slice.add("staticSites", new JsonArray());
        slice.add("methods", strings("<P: void run()>"));
        slice.add("causalEdgeIds", strings("EDGE.1"));
        slice.add("captureBindingIssues", new JsonArray());
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.1");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        capture.add("fieldPath", strings("value"));
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", "REGION.1.in.0");
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        return OutputClosureCodec.singleton("REL.1", "REGION.1",
                "HASH.1", port, cell, "HEAP_STATE", "int", slice);
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static void expectFailure(Runnable action, String text) {
        try {
            action.run();
            fail("expected IllegalArgumentException containing " + text);
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains(text));
        }
    }
}
