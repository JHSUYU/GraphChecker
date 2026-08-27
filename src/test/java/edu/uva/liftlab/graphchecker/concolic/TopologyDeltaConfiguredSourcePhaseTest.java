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

/**
 * The frozen schema is the catalog of mint SITES.  Executing any of them is a
 * local case -- every occurrence of a declared site is its own symbol, so
 * nothing predicts which of them one replay runs -- while a mint at a site
 * the plan never declared is still a topology divergence.
 */
public class TopologyDeltaConfiguredSourcePhaseTest {
    private static final Gson GSON = new Gson();
    private static final String OCCURRENCE =
            "test/nn0#epoch0/region/REGION.TARGET#1";

    @Test
    public void anyDeclaredMintSiteExecutionIsALocalCase() {
        ExecutionTask task = ExecutionTask.decode(task());
        TopologyDelta exact = new TopologyDelta("iteration-1",
                Collections.singletonList(task));
        JsonObject raw = raw();
        JsonArray observations = new JsonArray();
        for (int index = 0; index < 2; index++) {
            observations.add(observation(task.json().getAsJsonArray(
                    ConfiguredSourcePhaseContract.PLAN_FIELD).get(index)
                    .getAsJsonObject().get("phaseId").getAsString()));
        }
        raw.add("configuredSourcePhaseObservations", observations);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = new JsonObject();
        exact.classify(task,
                new ConcolicSummaryImporter.ResultRow(raw, 0), admitted);
        assertEquals(TopologyDelta.NEW_OCCURRENCE,
                exact.rows().get(0).get("deltaKind").getAsString());
    }

    @Test
    public void mintObservedAtAnUndeclaredSiteIsADivergence() {
        ExecutionTask task = ExecutionTask.decode(task());
        TopologyDelta unknown = new TopologyDelta("iteration-1",
                Collections.singletonList(task));
        JsonObject raw = raw();
        JsonArray observations = new JsonArray();
        observations.add(observation("SOURCE_PHASE.not-in-plan"));
        raw.add("configuredSourcePhaseObservations", observations);
        TopologyDelta.Observation refused =
                TopologyDelta.Observation.refused(
                        "CONFIGURED_SOURCE_PHASE_MISSING");
        unknown.classify(task,
                new ConcolicSummaryImporter.ResultRow(raw, 0), refused);
        JsonObject divergence = unknown.rows().get(0);
        assertEquals(TopologyDelta.TOPOLOGY_DIVERGENCE,
                divergence.get("deltaKind").getAsString());
        assertTrue(divergence.getAsJsonArray("divergences").toString(),
                divergence.getAsJsonArray("divergences").toString()
                        .contains("configuredSourcePhases"));
    }

    /** The observation names the catalog row it matched; every other member
     * it could carry restates that row and is not written. */
    private static JsonObject observation(String matchedPhaseId) {
        JsonObject observation = new JsonObject();
        observation.addProperty("matchedPhaseId", matchedPhaseId);
        return observation;
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

        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "TARGET.LOCAL", "<Target: long local>",
                "<Target: void run()>", 3));
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0);
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(decoded,
                OCCURRENCE, 1, 10L, 20L, 30L, "<Target: void run()>",
                Collections.singletonList(20L)));
        phases.add(ConfiguredSourcePhaseContract.occurrence(decoded,
                OCCURRENCE, 2, 11L, 20L, 31L, "<Target: void run()>",
                Collections.singletonList(20L)));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        return task;
    }

    /** An RPC value handed to this occurrence over an edge the frozen plan
     * declared is a local case; one from an occurrence or port the plan never
     * declared is the topology change that re-plans. */
    @Test
    public void handoffFromAnUndeclaredExchangeIsADivergence() {
        ExecutionTask task = ExecutionTask.decode(task());
        TopologyDelta unknown = new TopologyDelta("iteration-1",
                Collections.singletonList(task));
        JsonObject raw = raw();
        JsonArray handoffs = new JsonArray();
        JsonObject handoff = new JsonObject();
        handoff.addProperty("producerOccurrenceId",
                "test/dn9#epoch0/region/REGION.UNKNOWN#1");
        handoff.addProperty("portId", "XCH.unknown.resp");
        handoffs.add(handoff);
        raw.add("vmHandoffEvents", handoffs);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = new JsonObject();
        unknown.classify(task,
                new ConcolicSummaryImporter.ResultRow(raw, 0), admitted);
        JsonObject divergence = unknown.rows().get(0);
        assertEquals(TopologyDelta.TOPOLOGY_DIVERGENCE,
                divergence.get("deltaKind").getAsString());
        assertTrue(divergence.getAsJsonArray("divergences").toString(),
                divergence.getAsJsonArray("divergences").toString()
                        .contains("exchangeSchema"));
    }

    private static JsonObject raw() {
        JsonObject raw = new JsonObject();
        raw.addProperty("taskId", "TASK.TARGET");
        return raw;
    }
}
