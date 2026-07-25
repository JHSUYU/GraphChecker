package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Paths;
import java.security.MessageDigest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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
        assertEquals("D", satisfiable.modelAssignments.get(0)
                .getAsJsonObject().get("floatingPointFormat").getAsString());
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

    private static JsonObject containerActivation() {
        JsonObject activation = activation();
        JsonObject container = new JsonObject();
        container.addProperty("symbol", "REGION.3.in.array");
        container.addProperty("cell", "<example.Keys: example.Key[] keys>");
        container.addProperty("location", "HEAP_OBJECT_FIELD");
        container.addProperty("bindingMode", "FIELD_ACCESS");
        activation.getAsJsonArray("materializations").add(container);
        return activation;
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

    private static JsonObject stringContains(String raw, String needle,
                                             boolean negated) {
        return stringOperation("contains", negated, stringSymbol(raw),
                stringConstant(needle));
    }

    private static JsonObject stringOperation(String operation,
                                              boolean negated,
                                              JsonElement... parameters) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "OpStrExpression");
        expression.addProperty("_name", operation);
        expression.addProperty("_is_not", negated);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : parameters) {
            arguments.add(parameter);
        }
        expression.add("_param_list", arguments);
        return expression;
    }

    private static JsonObject stringSymbol(String raw) {
        JsonObject receiver = new JsonObject();
        receiver.addProperty("_type", "SymbolExpression");
        receiver.addProperty("_java_type", "java/lang/String");
        receiver.addProperty("_exp", raw);
        return receiver;
    }

    private static JsonObject intSymbol(String raw) {
        return numericSymbol(raw, "I");
    }

    private static JsonObject referenceSymbol(String raw, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject numericSymbol(String raw, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject stringConstant(String value) {
        JsonObject argument = new JsonObject();
        argument.addProperty("_type", "ConStringSymbolExp");
        argument.addProperty("_java_type", "java/lang/String");
        argument.addProperty("_exp", "Y_L'String'_" + value);
        return argument;
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

    private static JsonObject cast(JsonElement source, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "TypeCastExpression");
        result.addProperty("_java_type", javaType);
        result.add("_exp", source);
        return result;
    }

    private static JsonObject explicitCast(JsonElement source,
                                           String sourceJavaType,
                                           String targetJavaType) {
        JsonObject result = cast(source, targetJavaType);
        result.addProperty("sourceJavaType", sourceJavaType);
        result.addProperty("targetJavaType", targetJavaType);
        return result;
    }

    private static JsonObject unaryNegation(JsonElement operand) {
        return binaryExpression(JsonNull.INSTANCE, "-", operand);
    }

    private static JsonObject method(String name, JsonElement resultValue,
                                     JsonElement... parameters) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "MethodExpression");
        result.addProperty("_name", name);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : parameters) arguments.add(parameter);
        result.add("_param_list", arguments);
        result.add("_res_exp", resultValue);
        return result;
    }

    private static JsonObject nullReference() {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "Ljava/lang/Object;");
        result.addProperty("_exp", "N");
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

    private static JsonObject currentTimePlaceholder(int count) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "PlaceholderExpression");
        result.addProperty("_place_holder_func", "currentTimeMills");
        result.addProperty("_count", count);
        return result;
    }

    private static JsonObject dynamicBinding(String base, String site,
                                             int occurrence, String key)
            throws Exception {
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature", "<Key: long expiry>");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        binding.add("fieldPath", fieldPath);
        binding.addProperty("leafOwnerObjectToken", "OBJECT.old-run");
        binding.addProperty("entryReadObservationId", "ENTRY.READ."
                + occurrence);
        JsonObject keyExpression = new JsonObject();
        keyExpression.addProperty("_type", "ConstExpr");
        keyExpression.addProperty("_java_type", "Ljava/lang/String;");
        keyExpression.addProperty("_exp", key);
        binding.add("keyExpression", keyExpression);
        binding.addProperty("keyExpressionAuthority",
                "RUNTIME_MAP_ENTRY_READ_KEY_EXPRESSION");
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject containerBinding(String base, String site,
                                               int index, int occurrence)
            throws Exception {
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature", "<example.Key: int id>");
        JsonArray path = new JsonArray();
        path.add("id");
        binding.add("fieldPath", path);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.ARRAY.1");
        selector.addProperty("containerInputPort", "REGION.3.in.array");
        selector.addProperty("containerInputCell",
                "<example.Keys: example.Key[] keys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", index);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "int");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.SOURCE");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_ACTIVATION_"
                        + "LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        binding.add("containerSelector", selector);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.SOURCE");
        binding.addProperty("complete", true);
        return binding;
    }

    private static String sha256(String value) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] bytes = digest.digest(value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte current : bytes) {
            result.append(String.format("%02x", current & 0xff));
        }
        return result.toString();
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }

    private static void assertZ3Parses(String smt) throws Exception {
        Process process = new ProcessBuilder("z3", "-in")
                .redirectErrorStream(true).start();
        try (OutputStream input = process.getOutputStream()) {
            input.write(smt.getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = process.getInputStream().read(buffer)) >= 0) {
            output.write(buffer, 0, count);
        }
        int exit = process.waitFor();
        String text = new String(output.toByteArray(),
                StandardCharsets.UTF_8);
        assertEquals(text, 0, exit);
        assertFalse(text, text.contains("(error"));
    }
}
