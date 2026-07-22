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
        assertFalse(result.record.get("branchOverrideAllowed")
                .getAsBoolean());
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
    public void unsupportedExpressionIsAnExplicitGap() throws Exception {
        JsonObject unsupported = new JsonObject();
        unsupported.addProperty("_type", "UNSUPPORTED_TEST_NODE");

        ConcolicConstraintSolver.Result result =
                solveForTest(task(unsupported), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertEquals("UNSUPPORTED_EXPRESSION_IR",
                result.record.get("reason").getAsString());
    }

    @Test
    public void capturedStringContainsPathsProduceExactReplayModels()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L'String'_field_REGION.3.in.0_example/Input";
        JsonObject positive = stringContains(raw,
                "needle_with_underscore", false);
        JsonObject negative = stringContains(raw, "absent", true);
        JsonObject task = task(negative);
        JsonArray constraints = new JsonArray();
        constraints.add(positive);
        constraints.add(negative);
        task.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(0, result.record.getAsJsonArray("unsupported").size());
        assertTrue(result.smtLib.contains("(str.contains "));
        assertTrue(result.smtLib.contains("\"needle_with_underscore\""));
        assertTrue(result.smtLib.contains("(not (str.contains "));
        assertEquals(1, result.modelAssignments.size());
        assertEquals("STRING", result.modelAssignments.get(0)
                .getAsJsonObject().get("valueType").getAsString());
        String value = result.modelAssignments.get(0).getAsJsonObject()
                .get("value").getAsString();
        assertTrue(value, value.contains("needle_with_underscore"));
        assertFalse(value, value.contains("absent"));
    }

    @Test
    public void nullableJavaStringGuardsProjectNullnessAndContentModels()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L'String'_field_REGION.3.in.0_example/Input";
        JsonObject symbol = stringSymbol(raw);
        JsonObject nonNull = binaryExpression(symbol.deepCopy(), "!=",
                nullReference());
        JsonObject symmetricNonNull = binaryExpression(nullReference(),
                "!=", symbol.deepCopy());
        JsonObject positiveTask = task(nonNull);
        JsonArray positiveConstraints = new JsonArray();
        positiveConstraints.add(nonNull);
        positiveConstraints.add(symmetricNonNull);
        positiveTask.add("constraints", positiveConstraints);

        ConcolicConstraintSolver.Result positive =
                solveForTest(positiveTask, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(positive.record.toString(), "SAT_MODEL_READY",
                positive.record.get("status").getAsString());
        assertEquals(0, positive.record.getAsJsonArray("unsupported").size());
        assertTrue(positive.record.get("nullableJavaStringModeled")
                .getAsBoolean());
        assertEquals("JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1",
                positive.record.get("nullableStringEncodingAuthority")
                        .getAsString());
        assertTrue(positive.smtLib,
                positive.smtLib.contains("sym__string_is_null__"));
        assertTrue(positive.smtLib,
                positive.smtLib.contains("(not sym__string_is_null__"));
        assertEquals(1, positive.modelAssignments.size());
        JsonObject positiveAssignment = positive.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("STRING", positiveAssignment.get("valueType")
                .getAsString());
        assertFalse(positiveAssignment.get("modelIsNull").getAsBoolean());
        assertEquals("JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1",
                positiveAssignment.get("nullableStringEncodingAuthority")
                        .getAsString());

        JsonObject isNull = binaryExpression(symbol.deepCopy(), "==",
                nullReference());
        JsonObject symmetricNull = binaryExpression(nullReference(), "==",
                symbol.deepCopy());
        JsonObject nullTask = task(isNull);
        JsonArray nullConstraints = new JsonArray();
        nullConstraints.add(isNull);
        nullConstraints.add(symmetricNull);
        nullTask.add("constraints", nullConstraints);
        ConcolicConstraintSolver.Result nullable =
                solveForTest(nullTask, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(nullable.record.toString(), "SAT_MODEL_READY",
                nullable.record.get("status").getAsString());
        assertEquals(0,
                nullable.record.getAsJsonArray("unsupported").size());
        assertEquals(1, nullable.modelAssignments.size());
        JsonObject nullAssignment = nullable.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("NULL", nullAssignment.get("valueType").getAsString());
        assertEquals("null", nullAssignment.get("value").getAsString());
        assertTrue(nullAssignment.get("modelIsNull").getAsBoolean());
    }

    @Test
    public void genericReferenceNullTargetProducesAnExactNullAssignment()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L_field_REGION.3.in.0_example/Input";
        JsonObject isNull = binaryExpression(referenceSymbol(raw,
                        "Ljava/lang/Boolean;"), "==", nullReference());
        JsonObject query = task(isNull);
        query.add("negatedCondition", isNull.deepCopy());

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertTrue(result.record.get("nullableJavaReferenceModeled")
                .getAsBoolean());
        assertTrue(result.smtLib, result.smtLib.contains(
                "sym__reference_is_null__"));
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.0",
                assignment.get("inputSymbol").getAsString());
        assertEquals("NULL", assignment.get("valueType").getAsString());
        assertEquals("null", assignment.get("value").getAsString());
        assertTrue(assignment.get("modelIsNull").getAsBoolean());
        assertEquals("JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1",
                assignment.get("referenceNullnessEncodingAuthority")
                        .getAsString());
    }

    @Test
    public void classNameContainingStringRemainsAnOrdinaryReference()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L_field_REGION.3.in.0_example/StringHolder";
        JsonObject isNull = binaryExpression(referenceSymbol(raw,
                        "Lexample/StringHolder;"), "==", nullReference());
        JsonObject query = task(isNull);
        query.add("negatedCondition", isNull.deepCopy());

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "sym__reference_is_null__"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "sym__string_is_null__"));
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("NULL", assignment.get("valueType").getAsString());
        assertEquals("JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1",
                assignment.get("referenceNullnessEncodingAuthority")
                        .getAsString());
    }

    @Test
    public void genericReferenceNonNullTargetFailsClosedWithoutAnObjectModel()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L_field_REGION.3.in.0_example/Input";
        JsonObject nonNull = binaryExpression(referenceSymbol(raw,
                        "Ljava/lang/Boolean;"), "!=", nullReference());
        JsonObject query = task(nonNull);
        query.add("negatedCondition", nonNull.deepCopy());

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("NOT_ALL_PATH_INPUT_SYMBOLS_HAVE_"
                        + "MATERIALIZATION_TARGETS",
                result.record.get("reason").getAsString());
        assertEquals(0, result.modelAssignments.size());
        assertTrue(result.record.getAsJsonArray("unmappedInputSymbols")
                .toString().contains(raw));
    }

    @Test
    public void nonTargetReferencePrefixRetainsItsConcreteReplayObject()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String prefixRaw = "M_L_field_REGION.3.in.0_example/Input";
        String targetRaw = "M_I_field_REGION.3.in.1_java/lang/Integer";
        JsonObject prefix = binaryExpression(referenceSymbol(prefixRaw,
                        "Ljava/lang/Boolean;"), "!=", nullReference());
        JsonObject target = binarySymbol(targetRaw, ">", 3);
        JsonObject query = task(target);
        JsonArray constraints = new JsonArray();
        constraints.add(prefix);
        constraints.add(target);
        query.add("constraints", constraints);
        query.add("negatedCondition", target.deepCopy());

        JsonObject replay = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        materializations.add(materialization("REGION.3.in.1", 1));
        replay.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, replay,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.record.get(
                "unforcedPrefixReferenceSymbolCount").getAsInt());
        assertTrue(result.record.getAsJsonArray(
                "unforcedPrefixReferenceSymbols").toString().contains(
                prefixRaw));
        assertTrue(result.record.get(
                "requiresUnforcedEnvironmentValidation").getAsBoolean());
        assertEquals(1, result.modelAssignments.size());
        assertEquals("REGION.3.in.1", result.modelAssignments.get(0)
                .getAsJsonObject().get("inputSymbol").getAsString());
    }

    @Test
    public void nullReferencePrefixIsMaterializedForALaterScalarFlip()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String prefixRaw = "M_L_field_REGION.3.in.0_example/Input";
        String targetRaw = "M_I_field_REGION.3.in.1_java/lang/Integer";
        JsonObject prefix = binaryExpression(referenceSymbol(prefixRaw,
                        "Ljava/lang/Boolean;"), "==", nullReference());
        JsonObject target = binarySymbol(targetRaw, ">", 3);
        JsonObject query = task(target);
        JsonArray constraints = new JsonArray();
        constraints.add(prefix);
        constraints.add(target);
        query.add("constraints", constraints);
        query.add("negatedCondition", target.deepCopy());

        JsonObject replay = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        materializations.add(materialization("REGION.3.in.1", 1));
        replay.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, replay,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(0, result.record.get(
                "unforcedPrefixReferenceSymbolCount").getAsInt());
        assertEquals(1, result.record.get(
                "materializedNullPrefixReferenceSymbolCount").getAsInt());
        assertTrue(result.record.getAsJsonArray(
                "materializedNullPrefixReferenceSymbols").toString()
                .contains(prefixRaw));
        assertEquals(2, result.modelAssignments.size());
        JsonObject nullAssignment = null;
        for (JsonElement element : result.modelAssignments) {
            JsonObject assignment = element.getAsJsonObject();
            if ("REGION.3.in.0".equals(assignment.get("inputSymbol")
                    .getAsString())) {
                nullAssignment = assignment;
            }
        }
        assertTrue(result.modelAssignments.toString(),
                nullAssignment != null);
        assertEquals("NULL", nullAssignment.get("valueType").getAsString());
        assertEquals("null", nullAssignment.get("value").getAsString());
        assertTrue(nullAssignment.get("modelIsNull").getAsBoolean());
    }

    @Test
    public void nullStringCannotSatisfyAnEvaluatedContentPredicate()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L'String'_field_REGION.3.in.0_example/Input";
        JsonObject symbol = stringSymbol(raw);
        JsonObject isNull = binaryExpression(symbol.deepCopy(), "==",
                nullReference());
        JsonObject contains = stringOperation("contains", false,
                symbol.deepCopy(), stringConstant("needle"));
        JsonObject task = task(contains);
        JsonArray constraints = new JsonArray();
        constraints.add(isNull);
        constraints.add(contains);
        task.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "UNSAT",
                result.record.get("status").getAsString());
        assertEquals(0, result.record.getAsJsonArray("unsupported").size());
        assertTrue(result.smtLib,
                result.smtLib.contains("(not sym__string_is_null__"));
    }

    @Test
    public void arbitraryReferenceAndStringEqualityStillFailsClosed()
            throws Exception {
        JsonObject reference = new JsonObject();
        reference.addProperty("_type", "SymbolExpression");
        reference.addProperty("_java_type", "Ljava/lang/Object;");
        reference.addProperty("_exp",
                "M_L_field_REGION.3.in.1_example/Input");
        JsonObject equality = binaryExpression(stringSymbol(
                "M_L'String'_field_REGION.3.in.0_example/Input"), "==",
                reference);

        ConcolicConstraintSolver.Result result =
                solveForTest(task(equality), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray("unsupported").toString(),
                result.record.getAsJsonArray("unsupported").toString()
                        .contains("SORT_MISMATCH:STRING:REF"));

        String firstRaw =
                "M_L'String'_field_REGION.3.in.0_example/Input";
        String secondRaw =
                "M_L'String'_field_REGION.3.in.1_example/Input";
        ConcolicConstraintSolver.Result distinctStrings =
                solveForTest(task(binaryExpression(
                                stringSymbol(firstRaw), "==",
                                stringSymbol(secondRaw))), activation(),
                        Paths.get("z3"), 10_000L);
        assertEquals(distinctStrings.record.toString(), "UNSUPPORTED",
                distinctStrings.record.get("status").getAsString());
        assertTrue(distinctStrings.record.getAsJsonArray("unsupported")
                        .toString(), distinctStrings.record
                        .getAsJsonArray("unsupported").toString().contains(
                        "JAVA_STRING_REFERENCE_IDENTITY_"
                                + "MATERIALIZATION_UNMODELED"));

        Assume.assumeTrue(z3Available());
        JsonObject self = binaryExpression(stringSymbol(firstRaw), "==",
                stringSymbol(firstRaw));
        ConcolicConstraintSolver.Result selfComparison =
                solveForTest(task(self), activation(),
                        Paths.get("z3"), 10_000L);
        assertEquals(selfComparison.record.toString(), "SAT_MODEL_READY",
                selfComparison.record.get("status").getAsString());
    }

    @Test
    public void coreStringOperationsLowerExactlyWithBothPredicatePolarities()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_L'String'_field_REGION.3.in.0_example/Input";
        JsonObject receiver = stringSymbol(raw);
        JsonArray constraints = new JsonArray();
        constraints.add(stringOperation("equals", false,
                receiver.deepCopy(), stringConstant("prefix_tail")));
        constraints.add(stringOperation("equals", true,
                receiver.deepCopy(), stringConstant("other")));
        constraints.add(stringOperation("startsWith", false,
                receiver.deepCopy(), stringConstant("prefix")));
        constraints.add(stringOperation("startsWith", true,
                receiver.deepCopy(), stringConstant("tail")));
        constraints.add(stringOperation("endsWith", false,
                receiver.deepCopy(), stringConstant("tail")));
        constraints.add(stringOperation("isEmpty", false,
                stringConstant("")));
        constraints.add(stringOperation("isEmpty", true,
                receiver.deepCopy()));
        constraints.add(binaryExpression(stringOperation("length", false,
                        receiver.deepCopy()), "==", intConstant(11)));
        constraints.add(stringOperation("equals", false,
                stringOperation("concat", false, stringConstant("prefix"),
                        stringConstant("_tail")),
                stringConstant("prefix_tail")));
        JsonObject target = stringOperation("endsWith", true,
                receiver.deepCopy(), stringConstant("prefix"));
        constraints.add(target);
        JsonObject task = task(target);
        task.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(0, result.record.getAsJsonArray("unsupported").size());
        assertTrue(result.smtLib.contains("(= sym__"));
        assertTrue(result.smtLib.contains("(not (= sym__"));
        assertTrue(result.smtLib.contains(
                "(str.prefixof \"prefix\" sym__"));
        assertTrue(result.smtLib.contains(
                "(not (str.prefixof \"tail\" sym__"));
        assertTrue(result.smtLib.contains(
                "(str.suffixof \"tail\" sym__"));
        assertTrue(result.smtLib.contains(
                "(not (str.suffixof \"prefix\" sym__"));
        assertTrue(result.smtLib.contains("(= (str.len \"\") 0)"));
        assertTrue(result.smtLib.contains("(not (= (str.len sym__"));
        assertTrue(result.smtLib.contains("(= (str.len sym__"));
        assertTrue(result.smtLib.contains(") 11)"));
        assertTrue(result.smtLib.contains(
                "(str.++ \"prefix\" \"_tail\")"));
    }

    @Test
    public void inexactStringVariantsAndNonStringOperandsFailClosed()
            throws Exception {
        JsonObject receiver = stringSymbol(
                "M_L'String'_field_REGION.3.in.0_example/Input");
        JsonObject offsetStartsWith = stringOperation("startsWith", false,
                receiver.deepCopy(), stringConstant("prefix"),
                intConstant(1));
        JsonObject equalsIgnoreCase = stringOperation("equalsIgnoreCase",
                false, receiver.deepCopy(), stringConstant("PREFIX_TAIL"));
        JsonObject matches = stringOperation("matches", false,
                receiver.deepCopy(), stringConstant("prefix.*"));
        JsonObject nonStringReceiver = stringOperation("equals", false,
                intSymbol("M_I_field_REGION.3.in.1_example/Input"),
                stringConstant("1"));
        JsonObject task = task(matches);
        JsonArray constraints = new JsonArray();
        constraints.add(offsetStartsWith);
        constraints.add(equalsIgnoreCase);
        constraints.add(matches);
        constraints.add(nonStringReceiver);
        task.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);
        String unsupported = result.record.getAsJsonArray("unsupported")
                .toString();

        assertEquals(result.record.toString(), "UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(unsupported, unsupported.contains(
                "STRING_STARTSWITH_ARITY:3"));
        assertTrue(unsupported, unsupported.contains(
                "OP_STRING_OPERATOR:equalsIgnoreCase"));
        assertTrue(unsupported, unsupported.contains(
                "OP_STRING_OPERATOR:matches"));
        assertTrue(unsupported, unsupported.contains(
                "STRING_EQUALS_SORT_MISMATCH:0:INT"));
    }

    @Test
    public void finiteExponentAndLongMinLiteralsAreExactZ3Input()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String longRaw = "M_J_field_REGION.3.in.0_example/Input";
        String realRaw = "M_D_field_REGION.3.in.1_example/Input";
        String intRaw = "M_I_field_REGION.3.in.2_example/Input";
        JsonObject longFloor = numericBinary(longRaw, "J", ">=", "J",
                "-9223372036854775808");
        JsonObject longCeiling = numericBinary(longRaw, "J", "<=", "J",
                "9223372036854775807");
        JsonObject floatFloor = numericBinary(realRaw, "D", ">", "F",
                "1.250000000e-03");
        JsonObject intCeiling = numericBinary(intRaw, "I", "<=", "I",
                "2147483647");
        JsonObject doubleCeiling = numericBinary(realRaw, "D", "<", "D",
                "1.25000000000000000e+02");
        JsonObject task = task(doubleCeiling);
        JsonArray constraints = new JsonArray();
        constraints.add(longFloor);
        constraints.add(longCeiling);
        constraints.add(floatFloor);
        constraints.add(intCeiling);
        constraints.add(doubleCeiling);
        task.add("constraints", constraints);
        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        materializations.add(materialization("REGION.3.in.1", 1));
        materializations.add(materialization("REGION.3.in.2", 2));
        activation.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertTrue(result.smtLib.contains("(- 9223372036854775808)"));
        assertTrue(result.smtLib.contains("9223372036854775807"));
        assertTrue(result.smtLib.contains("(- 2147483648)"));
        assertTrue(result.smtLib.contains("2147483647"));
        assertTrue(result.smtLib.contains("((_ to_fp 8 24) #x3aa3d70a)"));
        assertTrue(result.smtLib.contains(
                "((_ to_fp 11 53) #x405f400000000000)"));
        assertFalse(result.smtLib.contains("e-03"));
        assertFalse(result.smtLib.contains("e+02"));
        assertEquals(2, result.record.get(
                "integralInputRangeConstraintCount").getAsInt());
        assertTrue(result.record.get("javaIntegralOverflowModeled")
                .getAsBoolean());
        assertTrue(result.record.get("ieee754FloatingPointModeled")
                .getAsBoolean());
        JsonObject realAssignment = null;
        for (JsonElement assignment : result.modelAssignments) {
            JsonObject candidate = assignment.getAsJsonObject();
            if ("REGION.3.in.1".equals(candidate.get("inputSymbol")
                    .getAsString())) {
                realAssignment = candidate;
                break;
            }
        }
        assertTrue(result.modelAssignments.toString(),
                realAssignment != null);
        assertEquals("REAL", realAssignment.get("valueType").getAsString());
        assertEquals("D", realAssignment.get("floatingPointFormat")
                .getAsString());
        assertTrue(realAssignment.get("modelIeeeBits").getAsString()
                .matches("#x[0-9a-f]{16}"));
    }

    @Test
    public void javaIntAndLongInputsCannotEscapeTheirRuntimeDomains()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject intOverflow = numericBinary(
                "M_I_field_REGION.3.in.0_example/Input", "I", ">", "J",
                "2147483647");
        JsonObject longUnderflow = numericBinary(
                "M_J_field_REGION.3.in.1_example/Input", "J", "<", "J",
                "-9223372036854775808");
        JsonObject task = task(longUnderflow);
        JsonArray constraints = new JsonArray();
        constraints.add(intOverflow);
        constraints.add(longUnderflow);
        task.add("constraints", constraints);
        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        materializations.add(materialization("REGION.3.in.1", 1));
        activation.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "UNSAT",
                result.record.get("status").getAsString());
        assertEquals(2, result.record.get(
                "integralInputRangeConstraintCount").getAsInt());
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

    @Test
    public void nanModelsUseExplicitDiscriminatorInsteadOfUnspecifiedBits()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_D_field_REGION.3.in.0_example/Input";
        JsonObject input = numericSymbol(raw, "D");
        JsonObject isNaN = binaryExpression(input.deepCopy(), "!=",
                input.deepCopy());

        ConcolicConstraintSolver.Result result =
                solveForTest(task(isNaN), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("NaN", assignment.get("value").getAsString());
        assertTrue(assignment.get("modelIsNaN").getAsBoolean());
        assertTrue(assignment.has("modelNaNSymbol"));
        assertFalse(assignment.has("modelIeeeBits"));
        assertFalse(assignment.has("modelBitSymbol"));
        assertEquals("SMT_FP_IS_NAN_TO_JAVA_CANONICAL_NAN_V1",
                assignment.get("nanReplayAuthority").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "() Bool (fp.isNaN sym__"));
    }

    @Test
    public void jvmCompareResultsPreserveNanVariantAndLongTrichotomy()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_D_field_REGION.3.in.0_example/Input";
        JsonObject input = numericSymbol(raw, "D");
        JsonObject isNaN = binaryExpression(input.deepCopy(), "!=",
                input.deepCopy());
        JsonObject dcmpl = binaryExpression(binaryExpression(
                input.deepCopy(), "--l", numericConstant("D", "0.0")),
                "==", numericConstant("I", "-1"));
        JsonObject dcmpg = binaryExpression(binaryExpression(
                input.deepCopy(), "--g", numericConstant("D", "0.0")),
                "==", numericConstant("I", "1"));
        JsonObject lcmp = binaryExpression(binaryExpression(
                numericConstant("J", "1"), "--",
                numericConstant("J", "2")), "==",
                numericConstant("I", "-1"));
        JsonObject query = task(dcmpg);
        JsonArray constraints = new JsonArray();
        constraints.add(isNaN);
        constraints.add(dcmpl);
        constraints.add(lcmp);
        constraints.add(dcmpg);
        query.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(0, result.record.getAsJsonArray("unsupported").size());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(ite (or (fp.isNaN "));
        assertTrue(result.smtLib, result.smtLib.contains(
                ") (- 1) (ite (fp.lt "));
        assertTrue(result.smtLib, result.smtLib.contains(
                ") 1 (ite (fp.lt "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(ite (< 1 2) (- 1) (ite (> 1 2) 1 0))"));
    }

    @Test
    public void wideningRealDivisionAndUnaryNegationLowerExactly()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject input = intSymbol(
                "M_I_field_REGION.3.in.0_example/Input");
        JsonObject widening = binaryExpression(cast(input.deepCopy(), "L"),
                ">=", numericConstant("J", "-2147483648"));
        JsonObject realDivision = binaryExpression(binaryExpression(
                numericConstant("D", "-7.5"), "@",
                numericConstant("D", "2.5")), "==",
                numericConstant("D", "-3.0"));
        JsonObject unaryNegation = binaryExpression(
                unaryNegation(input.deepCopy()), "<=",
                numericConstant("I", "2147483647"));
        JsonObject query = task(unaryNegation);
        JsonArray constraints = new JsonArray();
        constraints.add(widening);
        constraints.add(realDivision);
        constraints.add(unaryNegation);
        query.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(0, result.record.getAsJsonArray("unsupported").size());
        assertTrue(result.smtLib, result.smtLib.contains("(fp.div RNE "));
        assertTrue(result.smtLib, result.smtLib.contains("(- sym__"));
        assertFalse(result.smtLib, result.smtLib.contains("(div "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(define-fun java_int_wrap"));
        assertZ3Parses(result.smtLib);
    }

    @Test
    public void primitiveCastsPreserveJavaBoundarySemanticsInPathSolving()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonArray constraints = new JsonArray();
        constraints.add(binaryExpression(explicitCast(
                numericConstant("J", "4294967297"), "J", "I"), "==",
                numericConstant("I", "1")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("I", "257"), "I", "B"), "==",
                numericConstant("B", "1")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("I", "65535"), "I", "S"), "==",
                numericConstant("S", "-1")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("I", "-1"), "I", "C"), "==",
                numericConstant("C", "65535")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("I", "-1"), "I", "J"), "==",
                numericConstant("J", "-1")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("J", "4294967297"), "J", "D"), "==",
                numericConstant("D", "4294967297.0")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("F", "1.5"), "F", "D"), "==",
                numericConstant("D", "1.5")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("D", "1.5"), "D", "F"), "==",
                numericConstant("F", "1.5")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("D", "NaN"), "D", "I"), "==",
                numericConstant("I", "0")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("D", "Infinity"), "D", "I"), "==",
                numericConstant("I", "2147483647")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("D", "-Infinity"), "D", "I"), "==",
                numericConstant("I", "-2147483648")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("D", "-2.9"), "D", "I"), "==",
                numericConstant("I", "-2")));
        constraints.add(binaryExpression(explicitCast(
                numericConstant("F", "Infinity"), "F", "J"), "==",
                numericConstant("J", "9223372036854775807")));
        // Legacy VM JSON has no explicit source/target pair.
        constraints.add(binaryExpression(cast(
                numericConstant("I", "257"), "B"), "==",
                numericConstant("B", "1")));
        JsonObject query = task(constraints.get(0).getAsJsonObject());
        query.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "sat",
                result.record.get("solverStatus").getAsString());
        assertEquals(result.record.toString(), 0,
                result.record.getAsJsonArray("unsupported").size());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(java_int_wrap 4294967297)"));
        assertTrue(result.smtLib, result.smtLib.contains("(fp.isNaN "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "((_ fp.to_sbv 32) RTZ "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "((_ fp.to_sbv 64) RTZ "));
    }

    @Test
    public void unknownMethodsCastsAndNonNumericOperatorsFailClosed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonArray constraints = new JsonArray();
        constraints.add(method("example/Codec mystery",
                numericConstant("I", "0"), numericConstant("I", "1")));
        constraints.add(method("example/Codec mystery",
                stringConstant("result"), stringConstant("argument")));
        constraints.add(binaryExpression(cast(
                numericConstant("I", "257"), "B"), "==",
                numericConstant("I", "1")));
        constraints.add(binaryExpression(cast(
                numericConstant("I", "1"), "D"), "==",
                numericConstant("D", "1.0")));
        constraints.add(binaryExpression(cast(stringConstant("payload"),
                "Ljava/lang/Object;"), "==", nullReference()));
        constraints.add(binaryExpression(stringConstant("a"), "<",
                stringConstant("b")));
        constraints.add(binaryExpression(stringConstant("a"), "+",
                stringConstant("b")));
        JsonObject query = task(constraints.get(0).getAsJsonObject());
        query.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);
        String unsupported = result.record.getAsJsonArray("unsupported")
                .toString();

        assertEquals(result.record.toString(), "UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(unsupported, unsupported.contains(
                "METHOD_SEMANTICS_MISSING:example/Codec mystery"));
        assertFalse(unsupported, unsupported.contains(
                "UNSUPPORTED_JAVA_CAST:I->B"));
        assertFalse(unsupported, unsupported.contains(
                "UNSUPPORTED_JAVA_CAST:I->D"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "((_ to_fp 11 53) RNE (to_real 1))"));
        assertTrue(unsupported, unsupported.contains(
                "UNSUPPORTED_JAVA_CAST:java/lang/String->"
                        + "Ljava/lang/Object;"));
        assertTrue(unsupported, unsupported.contains(
                "NON_NUMERIC_COMPARISON"));
        assertTrue(unsupported, unsupported.contains(
                "NON_NUMERIC_ARITHMETIC"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-fun uf__example_Codec_mystery"));
        assertZ3Parses(result.smtLib);
    }

    @Test
    public void javaIntegralDivisionAndRemainderNeverUseSmtEuclideanOps()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject division = binaryExpression(binaryExpression(
                numericConstant("I", "-7"), "@",
                numericConstant("I", "2")), "==",
                numericConstant("I", "-3"));
        JsonObject remainder = binaryExpression(binaryExpression(
                numericConstant("I", "-7"), "%",
                numericConstant("I", "2")), "==",
                numericConstant("I", "-1"));
        JsonObject query = task(remainder);
        JsonArray constraints = new JsonArray();
        constraints.add(division);
        constraints.add(remainder);
        query.add("constraints", constraints);

        ConcolicConstraintSolver.Result result =
                solveForTest(query, activation(),
                        Paths.get("z3"), 10_000L);
        String unsupported = result.record.getAsJsonArray("unsupported")
                .toString();

        assertEquals(result.record.toString(), "UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(unsupported, unsupported.contains(
                "JAVA_INTEGRAL_DIVISION_UNMODELED"));
        assertTrue(unsupported, unsupported.contains(
                "JAVA_INTEGRAL_REMAINDER_UNMODELED"));
        assertFalse(result.smtLib, result.smtLib.contains("(div "));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(mod (- 7) 2)"));
        assertZ3Parses(result.smtLib);
    }

    @Test
    public void vmClockPlaceholderIsUncontrolledAndNeverProjected()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject condition = binary("<", 0);
        condition.add("_right", currentTimePlaceholder(1));

        ConcolicConstraintSolver.Result result =
                solveForTest(task(condition), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.record.get(
                "uncontrolledEnvironmentTermCount").getAsInt());
        assertEquals(0, result.record.get(
                "environmentModelAssignmentCount").getAsInt());
        assertTrue(result.record.get(
                "requiresUnforcedEnvironmentValidation").getAsBoolean());
        assertTrue(result.record.getAsJsonArray(
                "uncontrolledEnvironmentTerms").toString().contains(
                "currentTimeMills#1"));
        assertEquals(1, result.modelAssignments.size());
        assertEquals("REGION.3.in.0", result.modelAssignments.get(0)
                .getAsJsonObject().get("inputSymbol").getAsString());
        assertFalse(result.smtLib.contains(
                "get-value (environment__currentTimeMills"));
    }

    @Test
    public void replayProjectsEveryControlledInputNeededByExactPrefix()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String prefixRaw =
                "M_I_field_REGION.3.in.0_java/lang/Integer";
        String targetRaw =
                "M_I_field_REGION.3.in.1_java/lang/Integer";
        JsonObject prefix = binarySymbol(prefixRaw, ">", 0);
        JsonObject target = binarySymbol(targetRaw, "<", 0);
        JsonObject task = task(target);
        JsonArray constraints = new JsonArray();
        constraints.add(prefix);
        constraints.add(target);
        task.add("constraints", constraints);
        task.add("negatedCondition", target.deepCopy());

        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        materializations.add(materialization("REGION.3.in.1", 1));
        activation.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals("FULL_PATH_MATERIALIZABLE_INPUTS_PLUS_MODEL_"
                        + "PARTITIONED_PREFIX_REFERENCES_V4",
                result.record.get("modelProjectionPolicy").getAsString());
        assertEquals(2, result.record.get("controlledSymbolCount").getAsInt());
        assertEquals(1, result.record.get(
                "targetControlledSymbolCount").getAsInt());
        assertEquals(1, result.record.get(
                "materializedPrefixControlledSymbolCount").getAsInt());
        assertEquals(2, result.modelAssignments.size());
        JsonArray assignedInputs = new JsonArray();
        for (JsonElement assignment : result.modelAssignments) {
            assignedInputs.add(assignment.getAsJsonObject().get(
                    "inputSymbol").getAsString());
        }
        assertTrue(assignedInputs.toString(), assignedInputs.toString()
                .contains("REGION.3.in.0"));
        assertTrue(assignedInputs.toString(), assignedInputs.toString()
                .contains("REGION.3.in.1"));
        assertTrue(result.record.getAsJsonArray(
                "materializedPrefixControlledSymbols").toString().contains(
                prefixRaw));
    }

    @Test
    public void directFieldModelRetainsRuntimeMaterializationPath()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String raw = "M_I_field_REGION.3.in.2_example/Owner";
        JsonObject activation = new JsonObject();
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.3.in.2");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        JsonArray path = new JsonArray();
        path.add("var");
        action.add("fieldPath", path.deepCopy());
        JsonArray materializations = new JsonArray();
        materializations.add(action);
        activation.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                solveForTest(task(binarySymbol(raw,
                                ">=", 10)), activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        assertEquals(path, result.modelAssignments.get(0).getAsJsonObject()
                .get("materializationPath"));
    }

    @Test
    public void unverifiedPlaceholderKindIsAnExplicitIrGap()
            throws Exception {
        JsonObject condition = binary("<", 0);
        JsonObject placeholder = currentTimePlaceholder(1);
        placeholder.addProperty("_place_holder_func", "nanoTime");
        condition.add("_right", placeholder);

        ConcolicConstraintSolver.Result result =
                solveForTest(task(condition), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray("unsupported").toString()
                .contains("UNVERIFIED_PLACEHOLDER_EXPRESSION:nanoTime#1"));
        assertEquals(0, result.record.get(
                "environmentModelAssignmentCount").getAsInt());
    }

    @Test
    public void unmappedFlipDependencyIsRejectedBeforeSolverExecution()
            throws Exception {
        JsonObject condition = binary(">", 3);
        condition.getAsJsonObject("_left").addProperty("_exp",
                "A[_2.length");

        ConcolicConstraintSolver.Result result =
                solveForTest(task(condition), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS",
                result.record.get("reason").getAsString());
        assertFalse(result.record.get("solverInvoked").getAsBoolean());
        assertTrue(result.record.getAsJsonArray(
                "unmaterializableFlipSymbols").toString()
                .contains("A[_2.length"));
    }

    @Test
    public void exactOccurrenceTwoDynamicBindingDefersKeyToFreshReplay()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject first = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one");
        JsonObject second = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 2, "key-two");
        String dynamic = second.get("dynamicFieldSymbol").getAsString();
        JsonObject task = task(binarySymbol(dynamic, ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(dynamic,
                assignment.get("dynamicFieldSymbol").getAsString());
        assertEquals(2, assignment.get("materializationOccurrence")
                .getAsInt());
        assertEquals("REGION.3.in.0",
                assignment.get("baseInputSymbol").getAsString());
        assertFalse(assignment.has("expectedEntryKey"));
        assertFalse(assignment.has("keyExpression"));
        assertFalse(assignment.has("entryReadObservationId"));
        assertFalse(assignment.get("sourceEntrySelectorRetained")
                .getAsBoolean());
        assertEquals("EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                        + "FRESH_ENTRY_REBIND_V1",
                assignment.get("dynamicReplayRebindingAuthority")
                        .getAsString());
    }

    @Test
    public void exactArrayElementBindingProducesRuntimeContainerSelector()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject binding = containerBinding("REGION.3.in.0",
                "ENTRY.FIELD#id", 2, 1);
        String dynamic = binding.get("dynamicFieldSymbol").getAsString();
        JsonObject task = task(binarySymbol(dynamic, ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, containerActivation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertFalse(assignment.has("expectedEntryKey"));
        JsonObject selector = assignment.getAsJsonObject(
                "containerSelector");
        assertEquals("BIND.ARRAY.1",
                selector.get("bindingId").getAsString());
        assertEquals("REGION.3.in.array",
                selector.get("containerInputPort").getAsString());
        assertEquals(2, selector.get("elementIndex").getAsInt());
        assertEquals(1, selector.get("elementOccurrence").getAsInt());
        assertEquals("EXACT_ARRAY_INDEX",
                selector.get("selectorAuthority").getAsString());
        assertEquals("example.Key", selector.get(
                "declaredFieldOwnerClass").getAsString());
        assertEquals("int",
                selector.get("declaredFieldType").getAsString());
        assertFalse(selector.has("containerObjectToken"));
        assertFalse(selector.has("objectTokenScope"));
        assertFalse(selector.has("complete"));
        assertEquals("EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1",
                assignment.get("containerReplayRebindingAuthority")
                        .getAsString());
        assertFalse(assignment.get("sourceContainerObjectTokensRetained")
                .getAsBoolean());
    }

    @Test
    public void selectorOnlySnapshotLeafUsesUniqueDeclaredAction()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String site = "<example.Producer: int compute()>#u3";
        JsonObject binding = containerBinding("REGION.3.in.8", site,
                0, 1);
        binding.addProperty("fieldSignature",
                "<example.BooleanLeaf: boolean enabled>");
        JsonArray path = new JsonArray();
        path.add("state");
        path.add("guard");
        path.add("enabled");
        binding.add("fieldPath", path);
        JsonObject selector = binding.getAsJsonObject("containerSelector");
        selector.addProperty("declaredFieldOwnerClass",
                "example.BooleanLeaf");
        selector.addProperty("declaredFieldType", "boolean");
        String dynamic = binding.get("dynamicFieldSymbol").getAsString();
        String engine = "M_Z_field_" + dynamic
                + "_example/BooleanLeaf";
        JsonObject condition = binarySymbol(engine, "!=", 0);
        condition.getAsJsonObject("_left").addProperty("_java_type", "Z");
        JsonObject task = task(condition);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        task.add("dynamicFieldBindings", bindings);

        JsonObject activation = new JsonObject();
        JsonObject container = new JsonObject();
        container.addProperty("symbol", "REGION.3.in.array");
        container.addProperty("cell",
                "<example.Keys: example.Key[] keys>");
        container.addProperty("location", "HEAP_OBJECT_FIELD");
        container.addProperty("bindingMode",
                "CONTAINER_INPUT_OBSERVATION");
        JsonArray materializations = new JsonArray();
        materializations.add(container);
        activation.add("materializations", materializations);
        JsonObject leaf = new JsonObject();
        leaf.addProperty("symbol", "REGION.3.in.8");
        leaf.addProperty("cell", "<example.State: example.Guard state>"
                + "#field:guard#field:enabled");
        leaf.addProperty("field",
                "<example.BooleanLeaf: boolean enabled>");
        leaf.addProperty("leafFieldSignature",
                "<example.BooleanLeaf: boolean enabled>");
        leaf.addProperty("leafOwnerClass", "example.BooleanLeaf");
        leaf.addProperty("leafField", "enabled");
        leaf.addProperty("accessSiteId", site);
        leaf.addProperty("bindingMode", "FIELD_ACCESS");
        leaf.addProperty("location", "HEAP_OBJECT_FIELD");
        leaf.addProperty("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        leaf.add("fieldPath", path.deepCopy());
        JsonArray declared = new JsonArray();
        declared.add(leaf);
        activation.add("symbolize", declared);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.8",
                assignment.get("inputSymbol").getAsString());
        assertEquals(path, assignment.get("materializationPath"));
        assertEquals("REGION.3.in.array", assignment.getAsJsonObject(
                "containerSelector").get("containerInputPort")
                .getAsString());
        assertEquals("REGION.3.in.8", assignment.getAsJsonObject(
                "target").get("symbol").getAsString());
    }

    @Test
    public void missingOrDiscoveryArraySelectorIsInvalidRegistry()
            throws Exception {
        JsonObject missing = containerBinding("REGION.3.in.0",
                "ENTRY.FIELD#id", 0, 1);
        missing.remove("containerSelector");
        JsonObject discovery = containerBinding("REGION.3.in.0",
                "ENTRY.FIELD#id", 0, 1);
        discovery.getAsJsonObject("containerSelector").addProperty(
                "selectorAuthority", "DISCOVER_UNIQUE_IDENTITY_INDEX");
        for (JsonObject binding : new JsonObject[]{missing, discovery}) {
            JsonObject task = task(binarySymbol(binding.get(
                    "dynamicFieldSymbol").getAsString(), ">", 3));
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            task.add("dynamicFieldBindings", bindings);
            ConcolicConstraintSolver.Result result =
                    solveForTest(task,
                            containerActivation(), Paths.get("z3"),
                            10_000L);
            assertEquals("MATERIALIZATION_GAP",
                    result.record.get("status").getAsString());
            assertEquals("INVALID_DYNAMIC_FIELD_BINDING_REGISTRY",
                    result.record.get("reason").getAsString());
            assertFalse(result.record.get("solverInvoked").getAsBoolean());
        }
    }

    @Test
    public void realVmFieldWrapperAndOwnerSuffixResolveExactDynamicBinding()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject first = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one");
        JsonObject second = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 2, "key-two");
        String dynamic = second.get("dynamicFieldSymbol").getAsString();
        String engine = "M_J_field_" + dynamic
                + "_org/apache/hadoop/hdfs/security/token/block/BlockKey";
        JsonObject task = task(binarySymbol(engine, ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(engine, assignment.get("engineSymbol").getAsString());
        assertEquals(dynamic,
                assignment.get("dynamicFieldSymbol").getAsString());
        assertEquals(2, assignment.get("materializationOccurrence")
                .getAsInt());
    }

    @Test
    public void malformedSuffixAndDynamicPrefixCollisionAreNotAssociated()
            throws Exception {
        JsonObject binding = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one");
        String dynamic = binding.get("dynamicFieldSymbol").getAsString();
        JsonArray bindings = new JsonArray();
        bindings.add(binding);

        String[] rejected = {
                "M_J_field_" + dynamic + "0_java/lang/Long",
                "M_J_field_" + dynamic + "_java.lang.Long",
                "M_Q_field_" + dynamic + "_java/lang/Long"
        };
        for (String engine : rejected) {
            JsonObject task = task(binarySymbol(engine, ">", 3));
            task.add("dynamicFieldBindings", bindings.deepCopy());
            ConcolicConstraintSolver.Result result =
                    solveForTest(task, activation(),
                            Paths.get("z3"), 10_000L);
            assertEquals(engine + ": " + result.record,
                    "MATERIALIZATION_GAP",
                    result.record.get("status").getAsString());
            assertFalse(result.record.get("solverInvoked").getAsBoolean());
            assertTrue(result.record.getAsJsonArray(
                    "dynamicBindingResolutionGaps").toString().contains(
                    "ENGINE_SYMBOL_NOT_EXACT_DYNAMIC_BINDING"));
        }
    }

    @Test
    public void oneEntryBaseOnlyDynamicModelIsStillRejected()
            throws Exception {
        JsonObject task = task(binarySymbol("REGION.3.in.0", ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one"));
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray(
                "dynamicBindingResolutionGaps").toString().contains(
                "BASE_ONLY_DYNAMIC_INPUT_PROHIBITED"));
    }

    @Test
    public void twoDynamicEntriesNeverBroadcastABaseOnlyModel()
            throws Exception {
        JsonObject task = task(binarySymbol("REGION.3.in.0", ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one"));
        bindings.add(dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 2, "key-two"));
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                solveForTest(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertFalse(result.record.get("solverInvoked").getAsBoolean());
        assertTrue(result.record.getAsJsonArray(
                "dynamicBindingResolutionGaps").toString().contains(
                "AMBIGUOUS_DYNAMIC_BASE_INPUT"));
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
        String[] retired = new String[]{"constraints", "prefix",
                "negatedCondition", "flipSite", "flipOccurrence",
                "conditionIndex", "desiredOutcome",
                "expectedBranchPrefix", "pathReplayConstraints",
                "pathReplayNegatedCondition",
                "pathReplayTargetConditionIndex"};
        for (String field : retired) task.remove(field);
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
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject numericConstant(String javaType, String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
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
        binding.addProperty("schemaVersion", 2);
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
