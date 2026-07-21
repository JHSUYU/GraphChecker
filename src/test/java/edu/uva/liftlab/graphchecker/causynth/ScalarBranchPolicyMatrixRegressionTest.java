package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Regression matrix for output-causal scalar guards.
 *
 * <p>The static analyzer has a separate Soot-level regression for creating a
 * same-local {@code path_guard_dependency}. This class fixes the downstream
 * planner contract: once that exact control-dependence edge exists, policy is
 * based on scalar provenance, not on a workload or variable name.</p>
 */
public class ScalarBranchPolicyMatrixRegressionTest {
    @Test
    public void scalarGuardsAcrossTypesAndSourceShapesAreExplored() {
        String method = "<fixture.ScalarMatrix: int compute(boolean,int,int,"
                + "long,double,java.lang.String)>";
        String output = method + ".return";
        List<String> inputs = Arrays.asList(
                method + ".param0:boolean",
                method + ".param1:int",
                method + ".param2:int",
                method + ".param3:long",
                method + ".param4:double",
                method + ".param5:java.lang.String");
        List<Map<String, Object>> edges = new ArrayList<>();
        List<String> labels = Arrays.asList("boolean", "first-int",
                "second-int", "long", "double", "string-contains");
        for (int index = 0; index < inputs.size(); index++) {
            String local = method + "::" + labels.get(index);
            int guardUnit = 2 + index * 3;
            edges.add(edge(method, "IDENTITY_BINDING", "local_def_use",
                    inputs.get(index), local, guardUnit - 1));
            edges.add(pathGuard(method, local, guardUnit,
                    guardUnit + 1, index % 2 == 0));
            edges.add(edge(method, "VALUE_PASS", "local_def_use", local,
                    output, guardUnit + 2));
        }

        // A constant-bounded for loop still has a scalar loop-count frontier.
        // Repeated runtime occurrences are handled by RegionPathWorklist.
        String loopLocal = method + "::bounded-loop-count";
        edges.add(edge(method, "IDENTITY_BINDING", "local_def_use",
                inputs.get(1), loopLocal, 30));
        edges.add(pathGuard(method, loopLocal, 31, 32, true));
        edges.add(edge(method, "VALUE_PASS", "local_def_use", loopLocal,
                output, 33));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, Collections.singletonList(
                        plan(method, inputs, Collections.singletonList(
                                output)))), method);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) region.get("branchPolicies");

        assertEquals(7, policies.size());
        for (int unit : new int[]{2, 5, 8, 11, 14, 17, 31}) {
            Map<String, Object> policy = policyAt(policies, unit);
            assertEquals("EXPLORE", policy.get("policy"));
            assertTrue(policy.get("requiredOutcome") instanceof Boolean);
        }
        assertTrue(String.valueOf(region.get("symbolicInputs")),
                ((List<?>) region.get("symbolicInputs")).size() >= 6);
    }

    @Test
    public void controlFlowFormsExploreWithoutOutputIndependenceProof() {
        String method = "<fixture.ControlMatrix: int compute(boolean,int,"
                + "java.lang.String,java.lang.Object)>";
        String output = method + ".return";
        List<String> inputs = Arrays.asList(
                method + ".param0:boolean",
                method + ".param1:int",
                method + ".param2:java.lang.String",
                method + ".param3:java.lang.Object");
        List<Map<String, Object>> edges = new ArrayList<>();

        edges.add(controlGuard(method, inputs.get(0), output, 2,
                "if flag == 0 goto falseCase", false));
        edges.add(controlGuard(method, inputs.get(1), output, 5,
                "if value >= 10 goto largeCase", true));
        edges.add(controlGuard(method, inputs.get(3), output, 8,
                "if object == null goto nullCase", true));

        String containsResult = method + "::containsResult";
        edges.add(edge(method, "FUNCTION_RETURN", "call_return",
                inputs.get(2), containsResult, 10));
        edges.add(controlGuard(method, containsResult, output, 11,
                "if containsResult == 0 goto absentCase", false));

        Map<String, Object> switchGuard = controlGuard(method,
                inputs.get(1), output, 14,
                "tableswitch(value) { case 0: case0; default: other; }",
                null);
        switchGuard.put("reachingSuccessorIndices",
                Collections.singletonList(0));
        edges.add(switchGuard);

        edges.add(controlGuard(method, inputs.get(1), output, 17,
                "if index >= bound goto loopExit", false));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, Collections.singletonList(
                        plan(method, inputs, Collections.singletonList(
                                output)))), method);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) region.get("branchPolicies");

        assertEquals(6, policies.size());
        for (int unit : new int[]{2, 5, 8, 11, 14, 17}) {
            Map<String, Object> policy = policyAt(policies, unit);
            assertEquals("EXPLORE", policy.get("policy"));
            assertEquals("STATIC_OUTPUT_CONTROL_DEPENDENCE_REQUIRES_"
                            + "EXPLORATION_V1",
                    policy.get("policyAuthority"));
            assertEquals("OUTPUT_OR_PATH_INFLUENCE_PRESENT_OR_NOT_PROVEN_"
                            + "ABSENT",
                    policy.get("explorationReason"));
        }
        assertEquals(Collections.singletonList(0),
                policyAt(policies, 14).get("requiredSuccessorIndices"));
        assertEquals(null, policyAt(policies, 14).get("requiredOutcome"));
    }

    @Test
    public void pathAssumptionRequiresAuditableOutputIndependenceProof() {
        String method = "<fixture.ControlMatrix: int compute(boolean)>";
        String input = method + ".param0:boolean";
        String output = method + ".return";
        Map<String, Object> guard = edge(method, "GUARD",
                "guard_dependency", input, method + "#u2", 2);
        guard.put("unit", "if debugEnabled == 0 goto continue");
        ControlDependenceEdgeSupport.annotateOutputIndependentGuard(guard,
                Collections.singletonList(output),
                "both successors reach the same output definition and value");

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(Collections.singletonList(guard),
                        Collections.singletonList(plan(method,
                                Collections.singletonList(input),
                                Collections.singletonList(output)))),
                method);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) region.get("branchPolicies");
        Map<String, Object> policy = policyAt(policies, 2);
        assertEquals("PATH_ASSUMPTION", policy.get("policy"));
        assertEquals("SOOT_CFG_BOTH_SIDES_EQUIVALENT_FOR_ALL_REGION_"
                        + "OUTPUTS_V1", policy.get("policyAuthority"));
        assertTrue(policy.get("pathAssumptionProof") instanceof Map);

        String secondOutput = method + "::secondaryOutput";
        Map<String, Object> partialRegion = regionForRoot(
                SymbolicRegionPlanner.plan(Collections.singletonList(guard),
                        Collections.singletonList(plan(method,
                                Collections.singletonList(input),
                                Arrays.asList(output, secondOutput)))),
                method);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> partialPolicies =
                (List<Map<String, Object>>) partialRegion.get(
                        "branchPolicies");
        assertEquals("EXPLORE", policyAt(partialPolicies, 2).get("policy"));
    }

    private static Map<String, Object> pathGuard(String method, String local,
                                                  int guardUnit,
                                                  int definitionUnit,
                                                  boolean requiredOutcome) {
        Map<String, Object> guard = edge(method, "GUARD",
                "path_guard_dependency", local, local, guardUnit);
        guard.put("requiredOutcome", requiredOutcome);
        guard.put("sameCellRedefinition", true);
        guard.put("guardSiteId", method + "#u" + guardUnit);
        guard.put("controlledDefinitionSiteId",
                method + "#u" + definitionUnit);
        guard.put("controlledDefinitionUnitIndex", definitionUnit);
        guard.put("controlDependenceAuthority",
                "SOOT_CFG_REQUIRED_OUTCOME_TO_EXACT_RELEVANT_DEFINITION_V1");
        return guard;
    }

    private static Map<String, Object> controlGuard(
            String method, String from, String to, int unit, String text,
            Boolean requiredOutcome) {
        Map<String, Object> guard = edge(method, "GUARD",
                "path_guard_dependency", from, to, unit);
        guard.put("unit", text);
        if (requiredOutcome != null) {
            guard.put("requiredOutcome", requiredOutcome);
        }
        guard.put("guardSiteId", method + "#u" + unit);
        guard.put("controlledDefinitionSiteId", method + "#u" + (unit + 1));
        guard.put("controlDependenceAuthority", requiredOutcome == null
                ? "SOOT_CFG_REQUIRED_SUCCESSORS_TO_EXACT_RELEVANT_"
                + "DEFINITION_V1"
                : "SOOT_CFG_REQUIRED_OUTCOME_TO_EXACT_RELEVANT_"
                + "DEFINITION_V1");
        return guard;
    }

    private static Map<String, Object> policyAt(
            List<Map<String, Object>> policies, int unit) {
        for (Map<String, Object> policy : policies) {
            if (Integer.valueOf(unit).equals(policy.get("unitIndex"))) {
                return policy;
            }
        }
        throw new AssertionError("missing policy at unit " + unit + ": "
                + policies);
    }

    private static Map<String, Object> regionForRoot(
            SymbolicRegionPlanner.Result result, String root) {
        for (Map<String, Object> region : result.regions) {
            if (root.equals(region.get("rootMethod"))) return region;
        }
        throw new AssertionError("missing region rooted at " + root);
    }

    private static Map<String, Object> plan(String method,
                                            List<String> inputs,
                                            List<String> outputs) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("method", method);
        row.put("classification", "SYMBOLIC_EXECUTION");
        row.put("symbolicInputs", inputs);
        row.put("outputs", outputs);
        row.put("requiredModels", Collections.emptyList());
        row.put("siteIds", Collections.singletonList(method + "#u0:test"));
        row.put("guards", Collections.emptyList());
        return row;
    }

    private static Map<String, Object> edge(String method, String transfer,
                                            String kind, String from,
                                            String to, int unit) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("method", method);
        row.put("transferKind", transfer);
        row.put("kind", kind);
        row.put("fromCell", from);
        row.put("toCell", to);
        row.put("unitIndex", unit);
        row.put("siteId", method + "#u" + unit + ":" + kind);
        row.put("id", "DF.SCALAR." + Integer.toHexString((method + "\n"
                + transfer + "\n" + kind + "\n" + from + "\n" + to
                + "\n" + unit).hashCode()));
        return row;
    }
}
