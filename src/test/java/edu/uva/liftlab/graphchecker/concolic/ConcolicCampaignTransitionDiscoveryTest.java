package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;
import java.util.Arrays;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicCampaignTransitionDiscoveryTest {
    @Test
    public void promotesOnlyWhenExactOutputConsumerAndEdgeShareExecution() {
        JsonObject task = task();
        JsonObject summary = summary();
        JsonObject consumer = consumer();
        JsonObject edge = edge(true);
        ConcolicCampaignRunner.ExecutionOutcome outcome = outcome(summary,
                consumer, edge);

        JsonObject admitted = ConcolicCampaignRunner
                .transitionPromotionAdmission(task, outcome,
                        ConcolicCampaignRunner.RuntimeDiscoveryMode
                                .SAME_EXECUTION_REQUIRED);
        assertTrue(admitted.toString(), admitted.get("valid").getAsBoolean());

        JsonObject noEdge = ConcolicCampaignRunner
                .transitionPromotionAdmission(task, outcome(summary,
                        consumer, edge(false)),
                        ConcolicCampaignRunner.RuntimeDiscoveryMode
                                .SAME_EXECUTION_REQUIRED);
        assertFalse(noEdge.get("valid").getAsBoolean());

        JsonObject exceptional = summary();
        exceptional.addProperty("normalExit", false);
        JsonObject noOutput = ConcolicCampaignRunner
                .transitionPromotionAdmission(task, outcome(exceptional,
                        consumer, edge),
                        ConcolicCampaignRunner.RuntimeDiscoveryMode
                                .SAME_EXECUTION_REQUIRED);
        assertFalse(noOutput.get("valid").getAsBoolean());

        JsonObject noConsumer = ConcolicCampaignRunner
                .transitionPromotionAdmission(task,
                        new ConcolicCampaignRunner.ExecutionOutcome(
                                "SUCCEEDED", new JsonObject(), summary,
                                "EXEC.fresh",
                                Collections.singletonList(source()),
                                Collections.singletonList(edge)),
                        ConcolicCampaignRunner.RuntimeDiscoveryMode
                                .SAME_EXECUTION_REQUIRED);
        assertFalse(noConsumer.get("valid").getAsBoolean());
    }

    @Test
    public void fixedGraphModeCanNeverPromoteDiscovery() {
        JsonObject admitted = ConcolicCampaignRunner
                .transitionPromotionAdmission(task(), outcome(summary(),
                        consumer(), edge(true)),
                        ConcolicCampaignRunner.RuntimeDiscoveryMode
                                .FIXED_VALIDATED_GRAPH);
        assertFalse(admitted.get("valid").getAsBoolean());
    }

    private static ConcolicCampaignRunner.ExecutionOutcome outcome(
            JsonObject summary, JsonObject consumer, JsonObject edge) {
        return new ConcolicCampaignRunner.ExecutionOutcome("SUCCEEDED",
                new JsonObject(), summary, "EXEC.fresh",
                Arrays.asList(source(), consumer),
                Collections.singletonList(edge));
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.add("captureGoal", RegionCaptureGoal.transitionDiscovery()
                .toJson());
        JsonObject discovery = new JsonObject();
        discovery.addProperty("candidateEdgeId", "EDGE.P.C");
        discovery.addProperty("fromRegion", "REGION.P");
        discovery.addProperty("sourceActivationId", "ACT.P.1");
        discovery.addProperty("sourceRegionInstanceId", "REGION.P#call1");
        discovery.addProperty("runtimeFromPort", "LOCAL.PAYLOAD");
        discovery.addProperty("fromOutputPort", "REGION.P.out.0");
        discovery.addProperty("toRegion", "REGION.C");
        discovery.addProperty("toPort", "REGION.C.in.0");
        task.add("transitionDiscovery", discovery);
        return task;
    }

    private static JsonObject summary() {
        JsonObject summary = new JsonObject();
        summary.addProperty("valid", true);
        summary.addProperty("normalExit", true);
        summary.addProperty("relationallyComplete", true);
        summary.addProperty("activationId", "ACT.P.1");
        summary.addProperty("regionId", "REGION.P");
        summary.addProperty("regionInstanceId", "REGION.P#call1");
        summary.add("captureGoal", RegionCaptureGoal.transitionDiscovery()
                .toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        summary.add("requestedOutput", requested);
        JsonObject outputs = new JsonObject();
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_exp", "REGION.P.in.0");
        outputs.add("REGION.P.out.0", expression);
        summary.add("outputExpressions", outputs);
        return summary;
    }

    private static JsonObject consumer() {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.C.1");
        activation.addProperty("regionId", "REGION.C");
        activation.addProperty("regionInstanceId", "REGION.C#call2");
        return activation;
    }

    private static JsonObject source() {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.P.1");
        activation.addProperty("regionId", "REGION.P");
        activation.addProperty("regionInstanceId", "REGION.P#call1");
        return activation;
    }

    private static JsonObject edge(boolean composable) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.P.C");
        edge.addProperty("fromRegion", "REGION.P");
        edge.addProperty("fromPort", "LOCAL.PAYLOAD");
        edge.addProperty("toRegion", "REGION.C");
        edge.addProperty("toPort", "REGION.C.in.0");
        edge.addProperty("candidateRelation", "EQUALITY");
        edge.addProperty("validatedRelation", composable ? "EQUALITY" : "");
        edge.addProperty("composable", composable);
        edge.addProperty("eligibleForAutomaticDerivation", composable);
        edge.addProperty("eligibleForAutomaticSmt", composable);
        edge.addProperty("status", composable
                ? "CONFIRMED_RUNTIME_VALUE_EQUALITY" : "UNOBSERVED");
        edge.addProperty("valueEqualityObserved", composable);
        edge.addProperty("confirmedValueEqualityPairCount",
                composable ? 1 : 0);
        edge.addProperty("valueEqualityAuthority",
                composable ? "RUNTIME_COMPLETE_VALUE_FINGERPRINT" : "");
        JsonObject binding = new JsonObject();
        binding.addProperty("fromRegionInstance", "REGION.P#call1");
        binding.addProperty("toRegionInstance", "REGION.C#call2");
        binding.addProperty("valueEqualityObserved", composable);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        return edge;
    }
}
