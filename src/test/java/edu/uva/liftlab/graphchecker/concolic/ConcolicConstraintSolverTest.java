package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicConstraintSolverTest {
    @Test
    public void z3ModelIsMappedToARealInputMaterialization() throws Exception {
        Assume.assumeTrue(z3Available());
        ConcolicConstraintSolver.Result result =
                solveForTest(task(binary(">", 3)),
                        activation(), Paths.get("z3"), 10_000L);

        assertEquals("SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.0",
                assignment.get("inputSymbol").getAsString());
        assertEquals("Z3_PATH_FLIP_MODEL",
                assignment.get("authority").getAsString());
    }

    @Test
    public void contradictoryPrefixAndFlipAreUnsat() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject task = task(binary(">", 3));
        task.getAsJsonArray("constraints").add(binary("<", 0));

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("UNSAT", result.record.get("status").getAsString());
        assertEquals(0, result.modelAssignments.size());
    }

    @Test
    public void javaIntAndLongOverflowUseExactTwosComplementModels()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String intRaw = "M_I_field_REGION.3.in.0_example/Input";
        JsonObject intInput = intSymbol(intRaw);
        JsonObject wrappedInt = binaryExpression(
                intConstant(10), "+", intInput.deepCopy());
        ConcolicConstraintSolver.Result intResult =
                solveForTest(task(binaryExpression(
                                wrappedInt, "<", intConstant(0))),
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
    }

    @Test
    public void nonFiniteFloatingLiteralsHaveExactIeeeSemantics()
            throws Exception {
        Assume.assumeTrue(z3Available());
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
        for (String retired : new String[]{"floatingPointFormat",
                "modelNaNSymbol", "modelIsNaN", "nanReplayAuthority",
                "modelBitSymbol", "modelIeeeBits"}) {
            assertFalse(retired, assignment.has(retired));
        }
    }

    @Test
    public void unsupportedExpressionNeverInventsDiagnosticSmtMeaning()
            throws Exception {
        JsonObject division = binaryExpression(
                intSymbol("M_I_field_REGION.3.in.0_example/Input"),
                "/", intConstant(2));
        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(division, ">", intConstant(0))),
                activation(), Paths.get("/does/not/exist/z3"), 10_000L);

        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray("unsupported").size() > 0);
        assertFalse(result.smtLib.contains("unsupported_division"));
        assertFalse(result.smtLib.contains("declare-fun uf__"));
    }

    @Test
    public void runtimeTypedStringSymbolMapsToExactRegionInput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "java/lang/String");
        input.addProperty("_exp",
                "M_L'String'_REGION.3.in.0_example/Input");
        JsonObject needle = new JsonObject();
        needle.addProperty("_type", "ConStringSymbolExp");
        needle.addProperty("_java_type", "java/lang/String");
        needle.addProperty("_exp", "Y_L'String'_needle");
        JsonArray parameters = new JsonArray();
        parameters.add(input);
        parameters.add(needle);
        JsonObject contains = new JsonObject();
        contains.addProperty("_type", "OpStrExpression");
        contains.addProperty("_name", "contains");
        contains.add("_param_list", parameters);
        JsonObject condition = binaryExpression(contains, "==",
                numericConstant("Z", "0"));

        ConcolicConstraintSolver.Result result = solveForTest(
                task(condition), activation(), Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals("REGION.3.in.0", result.modelAssignments.get(0)
                .getAsJsonObject().get("inputSymbol").getAsString());
    }

    private static JsonObject activation() {
        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        activation.add("materializations", materializations);
        return activation;
    }

    private static JsonObject materialization(String symbol, int index) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", index);
        return action;
    }

    /** Adapts expression-focused unit fixtures to the production protocol. */
    private static ConcolicConstraintSolver.Result solveForTest(
            JsonObject legacyExpressionFixture, JsonObject activation,
            java.nio.file.Path z3, long timeoutMillis) throws Exception {
        JsonObject task = legacyExpressionFixture.deepCopy();
        JsonArray constraints = task.getAsJsonArray("constraints");
        if (constraints == null || constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "solver fixture requires at least one predicate");
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
        task.add("solverPathContext", SolverPathContext.empty().toJson());
        task.remove("constraints");
        return ConcolicConstraintSolver.solve(task, activation, z3,
                timeoutMillis);
    }

    private static JsonObject task(JsonObject condition) {
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", "QUERY.0");
        task.addProperty("regionId", "REGION.3");
        JsonArray constraints = new JsonArray();
        constraints.add(condition);
        task.add("constraints", constraints);
        return task;
    }

    private static JsonObject binary(String operator, int constant) {
        return binarySymbol(
                "M_I_field_REGION.3.in.0_java/lang/Integer",
                operator, constant);
    }

    private static JsonObject binarySymbol(String raw, String operator,
                                           int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", raw);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
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
