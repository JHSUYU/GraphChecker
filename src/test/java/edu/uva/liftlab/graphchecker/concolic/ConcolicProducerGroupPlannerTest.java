package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicProducerGroupPlannerTest {
    @Test
    public void campaignScopeRejectsSameConcreteEvidenceFromAnotherAttempt()
            throws Exception {
        JsonObject target = new JsonObject();
        target.addProperty("postDiscoveryTargetExecutionId", "EXEC.A");
        target.addProperty("regionInstanceId", "EXEC.A::TARGET");

        try {
            ConcolicProducerGroupPlanner.validateExecutionBindingsForTests(
                    target, Arrays.asList(edge("EDGE.A", "EXEC.A"),
                            edge("EDGE.B", "EXEC.B")), "artifact-sha");
            fail("campaign attempts must not join by test/seq/fingerprint");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "CROSS_OR_MISSING_DISCOVERED_EXECUTION"));
        }
    }

    @Test
    public void immutableBaselineScopeIncludesArtifactHashAndTest()
            throws Exception {
        JsonObject target = new JsonObject();
        target.addProperty("regionInstanceId", "TARGET");
        JsonObject edge = edge("EDGE.BASELINE", "");
        List<String> identities = ConcolicProducerGroupPlanner
                .validateExecutionBindingsForTests(target,
                        Collections.singletonList(edge), "sha-immutable");

        assertEquals(Collections.singletonList(
                "BASELINE:sha-immutable:ExampleTest#test"), identities);
    }

    private static JsonObject edge(String id, String execution) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", id);
        if (!execution.isEmpty()) {
            edge.addProperty("discoveredExecutionId", execution);
            JsonArray executions = new JsonArray();
            executions.add(execution);
            edge.add("discoveredExecutionIds", executions);
        }
        JsonObject binding = new JsonObject();
        binding.addProperty("test", "ExampleTest#test");
        binding.addProperty("fromRegionInstance", execution.isEmpty()
                ? "SOURCE" : execution + "::SOURCE");
        binding.addProperty("toRegionInstance", execution.isEmpty()
                ? "TARGET" : execution + "::TARGET");
        // Deliberately identical across attempts: none of these concrete
        // fields is an execution namespace.
        binding.addProperty("fromEndpointSeq", 20);
        binding.addProperty("toEndpointSeq", 30);
        binding.addProperty("valueFingerprint", "sha256:same");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        return edge;
    }
}
