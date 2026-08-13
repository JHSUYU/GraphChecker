package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RuntimeWorkflowDiscoveryTest {
    private static final String SOURCE = "cluster0/nn0#epoch0";
    private static final String TARGET = SOURCE + "/region/REGION.T#1";
    private static final String PRODUCER = SOURCE + "/region/REGION.P#1";

    @Test
    public void ranksOneExactProducerBeforeItsTarget() throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        targetPlan(), producerPlan()));

        assertEquals(2, workflow.selections().size());
        assertEquals(TARGET, workflow.selections().get(0).occurrenceId);
        assertEquals(PRODUCER, workflow.selections().get(1).occurrenceId);
        assertEquals("REL.P", workflow.producerGroups().get(0).relationKey);
        assertEquals(PRODUCER,
                workflow.producerGroups().get(0).occurrenceId);
        assertEquals(2, workflow.scheduledTaskCount());
    }

    @Test
    public void duplicateOccurrenceIdFailsClosed() throws Exception {
        JsonObject duplicate = targetPlan();
        try {
            RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                    duplicate, duplicate.deepCopy()));
            fail("duplicate occurrence must be rejected");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("duplicate occurrenceId"));
        }
    }

    @Test
    public void baselineReadUsesLatestObservedWriter() throws Exception {
        JsonObject early = edge("EDGE.EARLY", 10);
        JsonObject late = edge("EDGE.LATE", 15);
        JsonObject target = targetPlan();
        target.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .add("edgeBindings", edges(early, late));
        JsonObject producer = producerPlan();
        producer.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .add("edgeBindings", edges(early, late));

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(
                        Arrays.asList(target, producer));

        assertEquals(Collections.singleton("EDGE.LATE"),
                workflow.selections().get(0).targetEdgeIds);
        assertEquals(Collections.singleton("EDGE.LATE"),
                workflow.selections().get(1).producerProjection.edgeIds());
    }

    private static JsonObject targetPlan() {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.T.in.value");
        action.addProperty("cell", "<T: int value>");
        action.addProperty("location", "RECEIVER_FIELD");
        action.addProperty("javaType", "int");
        action.addProperty("observed", true);
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        JsonArray symbolize = new JsonArray();
        symbolize.add(action);

        JsonObject goal = goal("GOAL.T", false);
        goal.addProperty("kind", ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        goal.add("symbolize", symbolize);
        goal.add("edgeBindings", array(edge()));
        return plan("REGION.T", TARGET, "REL.T", "HASH.T", goal);
    }

    private static JsonObject producerPlan() {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.P.out.value");
        slice.addProperty("outputCell", "<P: int value>");
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", strings("EDGE.1"));
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.P", "REGION.P", "HASH.P", "REGION.P.out.value",
                "<P: int value>", "REGION_OUTPUT", "int", slice);

        JsonObject goal = goal("GOAL.P", true);
        goal.addProperty("kind",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE.name());
        OutputClosureCodec.writeTo(goal, closure);
        goal.add("edgeBindings", array(edge()));
        return plan("REGION.P", PRODUCER, "REL.P", "HASH.P", goal);
    }

    private static JsonObject goal(String id, boolean producer) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", id);
        goal.addProperty("pathSeedKey", "PATH.1");
        goal.add("runtimeDefinitionMethods", new JsonArray());
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());
        goal.add("edgeBindings", new JsonArray());
        return goal;
    }

    private static JsonObject plan(String region, String occurrence,
                                   String relation, String hash,
                                   JsonObject goal) {
        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", 3);
        plan.addProperty("kind", "CONCOLIC_REGION_PLAN");
        plan.addProperty("sourceKey", SOURCE);
        plan.addProperty("occurrenceId", occurrence);
        plan.addProperty("relationKey", relation);
        plan.addProperty("relationContractHash", hash);
        plan.addProperty("regionId", region);
        plan.add("closureGoals", array(goal));
        return plan;
    }

    private static JsonObject edge() {
        return edge("EDGE.1", 10);
    }

    private static JsonObject edge(String id, long writerEventSeq) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("edgeId", id);
        edge.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.addProperty("fromRegion", "REGION.P");
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("fromOccurrenceId", PRODUCER);
        edge.addProperty("toOccurrenceId", TARGET);
        edge.addProperty("fromOutputPort", "REGION.P.out.value");
        edge.addProperty("toInputPort", "REGION.T.in.value");
        edge.addProperty("receiverObjectId", 7);
        edge.addProperty("writerLaneId", "lane.p");
        edge.addProperty("readerLaneId", "lane.t");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("writerEventSeq", writerEventSeq);
        edge.addProperty("readerEventSeq", 20);
        return edge;
    }

    private static JsonArray edges(JsonObject... values) {
        JsonArray result = new JsonArray();
        for (JsonObject value : values) result.add(value.deepCopy());
        return result;
    }

    private static JsonArray array(JsonObject value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray strings(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }
}
