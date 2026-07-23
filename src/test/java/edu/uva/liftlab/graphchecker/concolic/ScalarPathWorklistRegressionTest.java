package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** End-to-end unit boundary from normalized branch paths to Z3 models. */
public class ScalarPathWorklistRegressionTest {
    @Test
    public void booleanAndSameIntSequentialBranchesYieldSatAndUnsatFlips()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String bool = raw("Z", 0, "java/lang/Boolean");
        String integer = raw("I", 1, "java/lang/Integer");
        List<JsonObject> conditions = Arrays.asList(
                binary(symbol("Z", bool), "!=", constant("Z", "0")),
                binary(symbol("I", integer), "==", constant("I", "0")),
                binary(symbol("I", integer), "<", constant("I", "10")));
        JsonObject summary = summary("ACT.SEQUENTIAL", conditions,
                Arrays.asList(true, true, true));
        JsonObject activation = activation("ACT.SEQUENTIAL", 2);

        RegionPathWorklist.Result worklist = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(3, worklist.tasks.size());
        JsonObject redundantFlip = taskAt(worklist.tasks, 2);
        ConcolicConstraintSolver.Result unsat =
                ConcolicConstraintSolver.solve(redundantFlip, activation,
                        Paths.get("z3"), 10_000L);
        assertEquals("UNSAT", unsat.record.get("status").getAsString());
        assertTrue(unsat.smtLib.contains("(= "));
        assertTrue(unsat.smtLib.contains("(>= "));

        JsonObject sameLocalFlip = taskAt(worklist.tasks, 1);
        ConcolicConstraintSolver.Result sat =
                ConcolicConstraintSolver.solve(sameLocalFlip, activation,
                        Paths.get("z3"), 10_000L);
        assertEquals(sat.record.toString(), "SAT_MODEL_READY",
                sat.record.get("status").getAsString());
        assertEquals(2, sat.record.get("controlledSymbolCount").getAsInt());
        // The exact prefix is solver-controlled too.  Both its Boolean input
        // and the selected integer frontier must therefore be materialized;
        // otherwise a later replay can silently fall back to an unrelated
        // concrete seed and violate the prefix before reaching the flip.
        assertEquals(2, sat.modelAssignments.size());
        Set<String> assigned = new LinkedHashSet<>();
        for (JsonElement assignment : sat.modelAssignments) {
            assigned.add(assignment.getAsJsonObject().get("inputSymbol")
                    .getAsString());
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                "REGION.9.in.0", "REGION.9.in.1")), assigned);
    }

    @Test
    public void nestedMixedScalarFlipProducesTypedModelsForEveryInput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject condition = andAll(Arrays.asList(
                binary(symbol("Z", raw("Z", 0, "java/lang/Boolean")),
                        "!=", constant("Z", "0")),
                binary(symbol("I", raw("I", 1, "java/lang/Integer")),
                        "<", symbol("I", raw("I", 2,
                                "java/lang/Integer"))),
                binary(symbol("J", raw("J", 3, "java/lang/Long")),
                        ">", constant("J", "100")),
                binary(symbol("D", raw("D", 4, "java/lang/Double")),
                        ">=", constant("D", "1.5")),
                stringOperation("contains", false,
                        symbol("java/lang/String", raw("L'String'", 5,
                                "java/lang/String")),
                        concreteString("needle"))));
        JsonObject summary = summary("ACT.MIXED",
                Collections.singletonList(condition),
                Collections.singletonList(true));
        JsonObject activation = activation("ACT.MIXED", 6);
        RegionPathWorklist.Result worklist = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(1, worklist.tasks.size());
        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(worklist.tasks.get(0),
                        activation, Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(6, result.record.get("controlledSymbolCount").getAsInt());
        assertEquals(6, result.modelAssignments.size());
        Set<String> valueTypes = new LinkedHashSet<>();
        for (JsonElement element : result.modelAssignments) {
            valueTypes.add(element.getAsJsonObject().get("valueType")
                    .getAsString());
        }
        assertTrue(valueTypes.toString(), valueTypes.contains("BOOL"));
        assertTrue(valueTypes.toString(), valueTypes.contains("INT"));
        assertTrue(valueTypes.toString(), valueTypes.contains("REAL"));
        assertTrue(valueTypes.toString(), valueTypes.contains("STRING"));
        assertTrue(result.smtLib.contains("(str.contains "));
        assertTrue(result.smtLib.contains("(_ FloatingPoint 11 53)"));
        assertTrue(result.smtLib.contains(" String)"));
    }

    @Test
    public void boundedLoopOccurrencesStayDistinctAndBoundsFailClosed() {
        String bound = raw("I", 0, "java/lang/Integer");
        List<JsonObject> conditions = Arrays.asList(
                binary(symbol("I", bound), ">", constant("I", "0")),
                binary(symbol("I", bound), ">", constant("I", "1")),
                binary(symbol("I", bound), ">", constant("I", "2")),
                binary(symbol("I", bound), "<=", constant("I", "3")));
        JsonObject summary = summary("ACT.LOOP", conditions,
                Arrays.asList(true, true, true, false));
        JsonArray mappings = summary.getAsJsonArray("branchMappings");
        JsonArray repeatedMappings = new JsonArray();
        for (int index = 0; index < mappings.size(); index++) {
            SummaryBranchMapping mapping = SummaryBranchMapping.fromJson(
                    mappings.get(index).getAsJsonObject());
            BranchWitness source = mapping.witness();
            JsonObject metadata = new JsonObject();
            metadata.addProperty("predicateNormalization",
                    source.predicateNormalization());
            BranchWitness repeated = BranchWitness.vmPc(
                    "SITE.LOOP.HEADER", source.method(),
                    source.unitIndex(), index + 1,
                    source.sourceTakenOutcome(),
                    source.sourceSatisfiedPredicate(), source.vmPcIndex(),
                    metadata);
            repeatedMappings.add(SummaryBranchMapping.witnessed(repeated,
                    mapping.summaryPcIndex(), mapping.policy()).toJson());
        }
        summary.add("branchMappings", repeatedMappings);
        JsonObject activation = activation("ACT.LOOP", 1);

        RegionPathWorklist.Result full = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(4, full.tasks.size());
        Set<Integer> occurrences = new LinkedHashSet<>();
        for (JsonObject task : full.tasks) {
            occurrences.add(replayContract(task).source().occurrence());
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(1, 2, 3, 4)),
                occurrences);

        RegionPathWorklist.Result bounded = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 2, 256, 30_000L));
        assertEquals(2, bounded.tasks.size());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                bounded.manifest.get("state").getAsString());
        assertTrue(bounded.manifest.getAsJsonArray("gaps").toString()
                .contains("MAX_FLIPS_PER_PATH"));
    }

    @Test
    public void unsupportedStringOperationIsAnExplicitIncompleteFrontier()
            throws Exception {
        JsonObject unsupported = stringOperation("regionMatches", false,
                symbol("java/lang/String", raw("L'String'", 0,
                        "java/lang/String")), concreteString("x"));
        JsonObject summary = summary("ACT.UNSUPPORTED",
                Collections.singletonList(unsupported),
                Collections.singletonList(true));
        JsonObject activation = activation("ACT.UNSUPPORTED", 1);
        RegionPathWorklist.Result initial = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(1, initial.tasks.size());
        ConcolicConstraintSolver.Result solve =
                ConcolicConstraintSolver.solve(initial.tasks.get(0),
                        activation, Paths.get("z3"), 10_000L);
        assertEquals("UNSUPPORTED", solve.record.get("status").getAsString());

        RegionPathWorklist.Result replanned = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.singletonList(solve.record),
                RegionPathWorklist.Bounds.defaults());
        assertTrue(replanned.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                replanned.manifest.get("state").getAsString());
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("UNSUPPORTED_EXPRESSION_IR"));
    }

    private static JsonObject taskAt(List<JsonObject> tasks,
                                     int conditionIndex) {
        for (JsonObject task : tasks) {
            if (replayContract(task).orderedPrefix().size()
                    == conditionIndex) {
                return task;
            }
        }
        throw new AssertionError("missing task for condition "
                + conditionIndex);
    }

    private static JsonObject summary(String activationId,
                                      List<JsonObject> conditions,
                                      List<Boolean> outcomes) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + activationId);
        summary.addProperty("activationId", activationId);
        summary.addProperty("regionId", "REGION.9");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.9.out.0");
        summary.add("requestedOutput", output);
        JsonArray path = new JsonArray();
        JsonArray mappings = new JsonArray();
        for (int index = 0; index < conditions.size(); index++) {
            path.add(conditions.get(index));
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", "SITE." + index);
            mapping.addProperty("conditionIndex", index);
            mapping.addProperty("occurrence", 1);
            mapping.addProperty("outcome", outcomes.get(index));
            mapping.addProperty("policy", "EXPLORE");
            mappings.add(mapping);
        }
        summary.add("pathCondition", path);
        summary.add("branchMappings", mappings);
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapEffects", new JsonArray());
        authorizeVmPcMappings(summary);
        return summary;
    }

    private static void authorizeVmPcMappings(JsonObject summary) {
        JsonArray conditions = summary.getAsJsonArray("pathCondition");
        JsonArray mappings = summary.getAsJsonArray("branchMappings");
        JsonArray canonical = new JsonArray();
        for (JsonElement element : mappings) {
            JsonObject mapping = element.getAsJsonObject();
            int conditionIndex = mapping.get("conditionIndex").getAsInt();
            JsonObject event = new JsonObject();
            event.addProperty("eventId", conditionIndex + 1L);
            event.addProperty("contextId", 1L);
            BranchWitness witness = BranchWitness.vmPc(
                    mapping.get("siteId").getAsString(),
                    "<test.Scalar: void run()>", conditionIndex,
                    mapping.get("occurrence").getAsInt(),
                    mapping.get("outcome").getAsBoolean(),
                    conditions.get(conditionIndex), conditionIndex, event);
            canonical.add(SummaryBranchMapping.witnessed(witness,
                    conditionIndex, SummaryBranchMapping.Policy.EXPLORE)
                    .toJson());
        }
        summary.add("branchMappings", canonical);
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        return BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract"));
    }

    private static JsonObject activation(String id, int inputCount) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", id);
        activation.addProperty("regionId", "REGION.9");
        activation.add("captureGoal", RegionCaptureGoal.outputClosure()
                .toJson());
        JsonArray materializations = new JsonArray();
        for (int index = 0; index < inputCount; index++) {
            JsonObject action = new JsonObject();
            action.addProperty("symbol", "REGION.9.in." + index);
            action.addProperty("location", "ARGUMENT");
            action.addProperty("bindingMode", "ROOT_ENTRY");
            action.addProperty("index", index);
            materializations.add(action);
        }
        activation.add("materializations", materializations);
        return activation;
    }

    private static String raw(String descriptor, int input,
                              String owner) {
        return "M_" + descriptor + "_field_REGION.9.in." + input + "_"
                + owner;
    }

    private static JsonObject symbol(String javaType, String raw) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject constant(String javaType, String value) {
        JsonObject result = symbol(javaType, "Y_" + javaType + "_" + value);
        result.addProperty("_type", "ConstExpr");
        return result;
    }

    private static JsonObject concreteString(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConStringSymbolExp");
        result.addProperty("_java_type", "java/lang/String");
        result.addProperty("_exp", "Y_L'String'_" + value);
        return result;
    }

    private static JsonObject binary(JsonElement left, String operator,
                                     JsonElement right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static JsonObject andAll(List<JsonObject> expressions) {
        if (expressions.isEmpty()) throw new IllegalArgumentException();
        JsonObject result = expressions.get(0);
        for (int index = 1; index < expressions.size(); index++) {
            result = binary(result, "&&", expressions.get(index));
        }
        return result;
    }

    private static JsonObject stringOperation(String operation,
                                              boolean negated,
                                              JsonElement... parameters) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "OpStrExpression");
        result.addProperty("_name", operation);
        result.addProperty("_is_not", negated);
        JsonArray values = new JsonArray();
        for (JsonElement parameter : parameters) values.add(parameter);
        result.add("_param_list", values);
        return result;
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }
}
