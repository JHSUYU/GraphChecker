package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class TopologyDeltaConfiguredSourcePhaseTest {
    private static final Gson GSON = new Gson();
    private static final String OCCURRENCE =
            "test/nn0#epoch0/region/REGION.TARGET#1";

    @Test
    public void exactPhaseSequenceIsLocalCaseButMissingPhaseIsDivergence() {
        ExecutionTask task = ExecutionTask.decode(task());
        String phaseId = task.json().getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD).get(1)
                .getAsJsonObject().get("phaseId").getAsString();

        TopologyDelta exact = new TopologyDelta("iteration-1",
                TopologyDelta.planDigest(Collections.singletonList(task)));
        JsonObject exactRaw = raw();
        JsonObject observation = new JsonObject();
        observation.addProperty("exactMatch", true);
        observation.addProperty("selectedPhase", false);
        observation.addProperty("matchedPhaseId", task.json()
                .getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .get(0).getAsJsonObject().get("phaseId").getAsString());
        observation.addProperty("phaseKind", "PUBLISH");
        observation.addProperty("sourceId", "TARGET.LOCAL");
        observation.addProperty("siteId", "<Target: void run()>#u3");
        observation.addProperty("replayOrdinal", 1);
        JsonArray observations = new JsonArray();
        observations.add(observation);
        observation = new JsonObject();
        observation.addProperty("exactMatch", true);
        observation.addProperty("selectedPhase", true);
        observation.addProperty("matchedPhaseId", phaseId);
        observation.addProperty("phaseKind", "PUBLISH");
        observation.addProperty("sourceId", "TARGET.LOCAL");
        observation.addProperty("siteId", "<Target: void run()>#u3");
        observation.addProperty("replayOrdinal", 1);
        observations.add(observation);
        exactRaw.add("configuredSourcePhaseObservations", observations);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = new JsonObject();
        exact.classify(task, exactRaw, 0, admitted);
        assertEquals(TopologyDelta.NEW_OCCURRENCE,
                exact.rows().get(0).get("deltaKind").getAsString());

        TopologyDelta missing = new TopologyDelta("iteration-1",
                TopologyDelta.planDigest(Collections.singletonList(task)));
        JsonObject missingRaw = raw();
        missingRaw.add("configuredSourcePhaseObservations",
                new JsonArray());
        TopologyDelta.Observation refused =
                TopologyDelta.Observation.refused(
                        "CONFIGURED_SOURCE_PHASE_MISSING");
        missing.classify(task, missingRaw, 0, refused);
        JsonObject divergence = missing.rows().get(0);
        assertEquals(TopologyDelta.TOPOLOGY_DIVERGENCE,
                divergence.get("deltaKind").getAsString());
        assertTrue(divergence.getAsJsonArray("divergences").toString(),
                divergence.getAsJsonArray("divergences").toString()
                        .contains("configuredSourcePhases"));
    }

    @Test
    public void selectedPublishWithoutMaterializationBindingIsRejected() {
        JsonObject malformed = task();
        malformed.remove(SymbolicSourceEvidence.TASK_FIELD);
        try {
            ExecutionTask.decode(malformed);
            fail("selected PUBLISH without symbolicSourceFields must fail");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("do not match exact PUBLISH/CONSUME"));
        }
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.TARGET");
        task.addProperty("goalId", "GOAL.TARGET");
        task.addProperty("regionId", "REGION.TARGET");
        task.addProperty("sourceKey", "test/nn0#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "test/nn0/REGION.TARGET");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);

        Map<String, Object> declaration =
                ConfiguredSourcePhaseContract.declaration(
                        ConfiguredSourcePhaseContract.Phase.PUBLISH,
                        "TARGET.LOCAL", "<Target: long local>",
                        "<Target: void run()>", 3);
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        Collections.singletonList(declaration)).get(0);
        Map<String, Object> first =
                ConfiguredSourcePhaseContract.occurrence(decoded,
                        OCCURRENCE, 1, 10L, 20L, 30L,
                        "<Target: void run()>",
                        Collections.singletonList(20L));
        Map<String, Object> phase =
                ConfiguredSourcePhaseContract.occurrence(decoded,
                        OCCURRENCE, 2, 11L, 20L, 31L,
                        "<Target: void run()>",
                        Collections.singletonList(20L));
        JsonArray phases = new JsonArray();
        phases.add(GSON.toJsonTree(first));
        phases.add(GSON.toJsonTree(phase));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonArray selected = new JsonArray();
        selected.add(String.valueOf(phase.get("phaseId")));
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                selected);
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourcePhaseId",
                String.valueOf(phase.get("phaseId")));
        source.addProperty("sourceId", "TARGET.LOCAL");
        source.addProperty("fieldSignature", "<Target: long local>");
        source.addProperty("sourceRole", "TARGET_REACH");
        source.addProperty("requiredTargetInputPort", "TARGET.local");
        JsonArray sources = new JsonArray();
        sources.add(source);
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        return task;
    }

    private static JsonObject raw() {
        JsonObject raw = new JsonObject();
        raw.addProperty("taskId", "TASK.TARGET");
        JsonObject binding = new JsonObject();
        binding.addProperty("occurrenceId", OCCURRENCE);
        raw.add("regionFrameBinding", binding);
        return raw;
    }
}
