package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicConstraintSolverTest {

    /**
     * Java integral arithmetic wraps at the exact two's complement boundary
     * and non-finite floating point literals keep exact IEEE semantics; both
     * are the same contract, that the lowering is Java's own and not the
     * solver's unbounded arithmetic.
     */
    @Test
    public void exactJavaIntegralAndIeeeFloatingPointSemantics()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String intRaw = "M_I_field_REGION.3.in.0_example/Input";
        JsonObject intInput = intSymbol(intRaw);
        JsonObject wrappedInt = binaryExpression(
                intConstant(10), "+", intInput.deepCopy());
        ConcolicConstraintSolver.Result intResult =
                solveForTest(task(binaryExpression(intInput.deepCopy(),
                                ">=", intConstant(0)),
                                binaryExpression(wrappedInt, "<",
                                        intConstant(0))),
                        activation(), Paths.get("z3"), 10_000L);

        assertEquals(intResult.record.toString(), "SAT_MODEL_READY",
                intResult.record.get("status").getAsString());
        assertTrue(intResult.smtLib, intResult.smtLib.contains(
                "(java_int_wrap (+ 10 sym__"));
        int intWitness = intResult.modelAssignments.get(0)
                .getAsJsonObject().get("value").getAsInt();
        assertTrue(Integer.toString(intWitness),
                intWitness >= Integer.MAX_VALUE - 9);

        String longRaw = "M_J_field_REGION.3.in.0_example/Input";
        JsonObject longInput = numericSymbol(longRaw, "J");
        JsonObject longEqualsMax = binaryExpression(longInput.deepCopy(),
                "==", numericConstant("J", "9223372036854775807"));
        JsonObject wrappedLongEqualsMin = binaryExpression(
                binaryExpression(longInput.deepCopy(), "+",
                        numericConstant("J", "1")), "==",
                numericConstant("J", "-9223372036854775808"));
        JsonObject longTask = task(wrappedLongEqualsMin);
        JsonArray longConstraints = new JsonArray();
        longConstraints.add(longEqualsMax);
        longConstraints.add(wrappedLongEqualsMin);
        longTask.add("constraints", longConstraints);

        ConcolicConstraintSolver.Result longResult =
                solveForTest(longTask, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(longResult.record.toString(), "SAT_MODEL_READY",
                longResult.record.get("status").getAsString());
        assertTrue(longResult.smtLib, longResult.smtLib.contains(
                "(java_long_wrap (+ sym__"));
        assertEquals(Long.MAX_VALUE, longResult.modelAssignments.get(0)
                .getAsJsonObject().get("value").getAsLong());

        // Folded from nonFiniteFloatingLiteralsHaveExactIeeeSemantics.
        for (String value : new String[]{"nan", "inf"}) {
            JsonObject condition = numericBinary(
                    "M_D_field_REGION.3.in.0_example/Input", "D", ">",
                    "D", value);
            ConcolicConstraintSolver.Result result =
                    solveForTest(task(condition),
                            activation(), Paths.get("z3"), 10_000L);

            assertEquals(result.record.toString(), "UNSAT",
                    result.record.get("status").getAsString());
            assertEquals(0, result.record.getAsJsonArray("unsupported")
                    .size());
            assertTrue(result.smtLib, result.smtLib.contains("#x7ff"));
        }

        JsonObject greaterThanNegativeInfinity = numericBinary(
                "M_D_field_REGION.3.in.0_example/Input", "D", ">",
                "D", "-inf");
        ConcolicConstraintSolver.Result satisfiable =
                solveForTest(
                        task(greaterThanNegativeInfinity), activation(),
                        Paths.get("z3"), 10_000L);
        assertEquals(satisfiable.record.toString(), "SAT_MODEL_READY",
                satisfiable.record.get("status").getAsString());
        JsonObject assignment = satisfiable.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REAL", assignment.get("valueType").getAsString());
    }

    @Test
    public void modelProjectsAllFiveConfiguredSourcesAcrossPrefixAndTarget()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String occurrence = "test/node#epoch0/region/REGION.five#1";
        String[] sourceIds = {
                "SOURCE.A", "SOURCE.B", "SOURCE.C", "SOURCE.D", "SOURCE.E"
        };
        JsonObject activation = configuredSourcesActivation(
                occurrence, sourceIds);
        JsonObject[] symbols = new JsonObject[sourceIds.length];
        for (int index = 0; index < sourceIds.length; index++) {
            String raw = "M_J_field_"
                    + SymbolicSourceEvidence.engineLabelForPhase(
                    sourcePhaseId(occurrence, sourceIds[index]),
                    sourceIds[index]) + "_example/Source";
            symbols[index] = numericSymbol(raw, "J");
        }
        JsonObject prefixC = binaryExpression(symbols[2].deepCopy(), ">",
                numericConstant("J", "30"));
        JsonObject prefixD = binaryExpression(symbols[3].deepCopy(), ">",
                numericConstant("J", "40"));
        JsonObject prefixE = binaryExpression(symbols[4].deepCopy(), ">",
                numericConstant("J", "50"));
        JsonObject targetAB = binaryExpression(symbols[0].deepCopy(), ">",
                symbols[1].deepCopy());

        ConcolicConstraintSolver.Result result = solveForTest(
                task(prefixC, prefixD, prefixE, targetAB), activation,
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 5,
                result.modelAssignments.size());
        Set<String> projectedSources = new LinkedHashSet<>();
        for (JsonElement element : result.modelAssignments) {
            JsonObject assignment = element.getAsJsonObject();
            projectedSources.add(assignment.get("configuredSourceId")
                    .getAsString());
        }
        assertEquals(new LinkedHashSet<>(java.util.Arrays.asList(sourceIds)),
                projectedSources);
    }

    @Test
    public void dynamicMapReadUsesItsAccessOrdinalWithoutProjectingTheKey()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String mapPort = "REGION.3.in.map";
        JsonObject stateIdentity = numericSymbol(mapPort,
                "java/util/HashMap");
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("_java_type", "L");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.add("receiver", stateIdentity);
        state.add("arguments", new JsonArray());

        JsonObject dynamicKey = numericSymbol(
                "UNMATERIALIZABLE_DYNAMIC_KEY", "I");
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ContainerRelation");
        read.addProperty("_java_type", "L");
        read.addProperty("shape", "ASSOCIATIVE");
        read.addProperty("operation", "READ");
        read.add("receiver", state);
        JsonArray arguments = new JsonArray();
        arguments.add(dynamicKey);
        read.add("arguments", arguments);
        JsonObject isNull = binaryExpression(read, "==",
                numericSymbol("N", ""));

        JsonObject activation = new JsonObject();
        JsonObject action = materialization(mapPort, 0);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("javaType", "java.util.Map");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        JsonArray actions = new JsonArray();
        actions.add(action);
        activation.add("inputActions", actions);

        ConcolicConstraintSolver.Result result = solveForTest(task(isNull),
                activation, Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertFalse(result.smtLib,
                result.smtLib.contains("UNMATERIALIZABLE_DYNAMIC_KEY"));
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(mapPort,
                assignment.get("inputSymbol").getAsString());
        assertEquals("NULL", assignment.get("valueType").getAsString());
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals("ASSOCIATIVE", target.get("shape").getAsString());
        assertEquals("ACCESS_ORDINAL",
                target.get("selectorKind").getAsString());
        assertEquals(1, target.get("accessOrdinal").getAsInt());
        assertFalse(target.has("keyValue"));
    }

    private static JsonObject activation() {
        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        JsonObject action = materialization("REGION.3.in.0", 0);
        action.addProperty("mode", "SYMBOLIC");
        materializations.add(action);
        activation.add("inputActions", materializations);
        return activation;
    }

    private static JsonObject configuredSourcesActivation(
            String occurrence, String... sourceIds) {
        JsonObject activation = new JsonObject();
        activation.addProperty("occurrenceId", occurrence);
        activation.add("inputActions", new JsonArray());
        for (int index = 0; index < sourceIds.length; index++) {
            addMintSite(activation, occurrence, sourceIds[index],
                    "<example.Source: long value" + index + ">", index + 1);
        }
        return activation;
    }

    /** The task's catalog of declared mint SITES: what a VM source root
     * resolves against now that no selection row predicts it. */
    private static void addMintSite(JsonObject activation, String occurrence,
                                    String sourceId, String fieldSignature,
                                    int ordinal) {
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                sourceId, fieldSignature, mintMethod(sourceId), 1));
        JsonObject row = ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0),
                occurrence, 1, ordinal, 10L, 100L + ordinal,
                "<example.Hook: boolean symbolize(java.lang.String,"
                        + "java.lang.Object,java.lang.String)>",
                Collections.singletonList(10L));
        JsonArray phases = activation.has(
                ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? activation.getAsJsonArray(
                        ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        phases.add(row);
        activation.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static String mintMethod(String sourceId) {
        return "<example.Source: void mint"
                + sourceId.replaceAll("[^A-Za-z0-9]", "_") + "()>";
    }

    private static String sourcePhaseId(
            String occurrence, String sourceId) {
        return ConfiguredSourcePhaseContract.phaseId(occurrence,
                ConfiguredSourcePhaseContract.siteId(
                        mintMethod(sourceId), 1),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static JsonObject materialization(String symbol, int index) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", index);
        action.addProperty("javaType", "int");
        return action;
    }

    /** Adapts expression-focused unit fixtures to the production protocol. */
    private static ConcolicConstraintSolver.Result solveForTest(
            JsonObject predicateFixture, JsonObject activation,
            java.nio.file.Path z3, long timeoutMillis) throws Exception {
        return solveForTest(predicateFixture, activation, z3,
                timeoutMillis, new JsonObject[0]);
    }

    private static ConcolicConstraintSolver.Result solveForTest(
            JsonObject predicateFixture, JsonObject activation,
            java.nio.file.Path z3, long timeoutMillis,
            JsonObject... contextConstraints) throws Exception {
        JsonObject task = predicateFixture.deepCopy();
        JsonArray constraints = task.getAsJsonArray("constraints");
        if (constraints == null || constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "solver fixture requires at least one predicate");
        }
        for (JsonElement element
                : activation.getAsJsonArray("inputActions")) {
            JsonObject action = element.getAsJsonObject();
            String javaType = regionInputJavaType(constraints,
                    action.get("symbol").getAsString());
            if (!javaType.isEmpty()) {
                action.addProperty("javaType", javaType);
            }
        }
        java.util.List<BranchWitness> prefix = new java.util.ArrayList<>();
        for (int index = 0; index + 1 < constraints.size(); index++) {
            JsonObject event = new JsonObject();
            event.addProperty("eventId", index + 1L);
            event.addProperty("contextId", 1L);
            prefix.add(BranchWitness.vmPc("TEST#u" + index,
                    "<test.Solver: void run()>", index, 1, true,
                    constraints.get(index), index, event));
        }
        int targetIndex = constraints.size() - 1;
        JsonObject sourceEvent = new JsonObject();
        sourceEvent.addProperty("eventId", targetIndex + 1L);
        sourceEvent.addProperty("contextId", 1L);
        BranchWitness source = BranchWitness.vmPc(
                "TEST#u" + targetIndex, "<test.Solver: void run()>",
                targetIndex, 1, false, BranchPredicateAlgebra.complement(
                constraints.get(targetIndex)), targetIndex, sourceEvent);
        task.add("replayContract", BranchReplayContract.flip(prefix,
                source).toJson());
        task.addProperty("schemaVersion", 3);
        task.addProperty("kind", "REGION_PATH_FLIP");
        JsonObject context = SolverPathContext.empty().toJson();
        JsonArray rows = new JsonArray();
        for (int index = 0; index < contextConstraints.length; index++) {
            JsonObject row = new JsonObject();
            row.addProperty("summaryPcIndex", index);
            row.add("expression", contextConstraints[index]);
            rows.add(row);
        }
        context.add("constraints", rows);
        task.add("solverPathContext", context);
        task.remove("constraints");
        return ConcolicConstraintSolver.solve(task, activation, z3,
                timeoutMillis);
    }

    private static String regionInputJavaType(
            JsonElement element, String inputSymbol) {
        if (element == null || element.isJsonNull()) return "";
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                String found = regionInputJavaType(child, inputSymbol);
                if (!found.isEmpty()) return found;
            }
            return "";
        }
        if (!element.isJsonObject()) return "";
        JsonObject object = element.getAsJsonObject();
        if ("SymbolExpression".equals(object.has("_type")
                ? object.get("_type").getAsString() : "")
                && object.has("_exp")
                && object.get("_exp").getAsString().contains(inputSymbol)) {
            return object.has("_java_type")
                    ? object.get("_java_type").getAsString() : "";
        }
        for (java.util.Map.Entry<String, JsonElement> entry
                : object.entrySet()) {
            String found = regionInputJavaType(
                    entry.getValue(), inputSymbol);
            if (!found.isEmpty()) return found;
        }
        return "";
    }

    private static JsonObject task(JsonObject... conditions) {
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", CanonicalJson.sha256("QUERY.0"));
        task.addProperty("regionId", "REGION.3");
        JsonArray constraints = new JsonArray();
        for (JsonObject condition : conditions) constraints.add(condition);
        task.add("constraints", constraints);
        return task;
    }

    private static JsonObject intSymbol(String raw) {
        return numericSymbol(raw, "I");
    }

    private static JsonObject numericSymbol(String raw, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject intConstant(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject numericConstant(String javaType, String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", "Y_" + javaType + "_" + value);
        return result;
    }

    private static JsonObject binaryExpression(
            JsonElement left, String operator, JsonElement right) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }

    private static JsonObject numericBinary(String raw, String symbolType,
                                            String operator,
                                            String constantType,
                                            String value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", symbolType);
        left.addProperty("_exp", raw);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", constantType);
        right.addProperty("_exp", "Y_" + constantType + "_" + value);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
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
