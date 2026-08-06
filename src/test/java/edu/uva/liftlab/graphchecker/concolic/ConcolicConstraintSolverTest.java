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
        assertFalse(assignment.has("authority"));
        assertFalse(assignment.has("solverSymbol"));
        assertFalse(assignment.has("target"));
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
    public void replayFrontierMaterializesPrefixAndTargetReferences()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String prefixRaw = "M_L_field_REGION.3.in.1_example/Input";
        JsonObject prefixReferenceIsNull = binaryExpression(
                referenceSymbol(prefixRaw), "==", referenceSymbol("N"));
        JsonObject primitiveTarget = task(binary(">", 3));
        JsonArray orderedConstraints = new JsonArray();
        orderedConstraints.add(prefixReferenceIsNull);
        orderedConstraints.add(primitiveTarget
                .getAsJsonArray("constraints").get(0));
        primitiveTarget.add("constraints", orderedConstraints);
        JsonObject twoInputs = activation();
        JsonObject prefixAction = materialization("REGION.3.in.1", 1);
        prefixAction.addProperty("javaType", "java.lang.Object");
        prefixAction.addProperty("mode", "SYMBOLIC");
        twoInputs.getAsJsonArray("inputActions").add(prefixAction);

        ConcolicConstraintSolver.Result prefixResult = solveForTest(
                primitiveTarget, twoInputs, Paths.get("z3"), 10_000L);

        assertEquals(prefixResult.record.toString(), "SAT_MODEL_READY",
                prefixResult.record.get("status").getAsString());
        assertEquals(2, prefixResult.modelAssignments.size());
        java.util.Set<String> prefixInputs = new java.util.LinkedHashSet<>();
        for (JsonElement element : prefixResult.modelAssignments) {
            prefixInputs.add(element.getAsJsonObject()
                    .get("inputSymbol").getAsString());
        }
        assertTrue(prefixInputs.contains("REGION.3.in.0"));
        assertTrue(prefixInputs.contains("REGION.3.in.1"));

        JsonObject referenceTarget = task(binaryExpression(
                referenceSymbol(prefixRaw), "==", referenceSymbol("N")));
        JsonObject referenceActivation = new JsonObject();
        JsonArray actions = new JsonArray();
        prefixAction = materialization("REGION.3.in.1", 1);
        prefixAction.addProperty("javaType", "java.lang.Object");
        prefixAction.addProperty("mode", "SYMBOLIC");
        actions.add(prefixAction);
        referenceActivation.add("inputActions", actions);

        ConcolicConstraintSolver.Result targetResult = solveForTest(
                referenceTarget, referenceActivation, Paths.get("z3"),
                10_000L);

        assertEquals(targetResult.record.toString(), "SAT_MODEL_READY",
                targetResult.record.get("status").getAsString());
        assertEquals(1, targetResult.modelAssignments.size());
        JsonObject assignment = targetResult.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.1",
                assignment.get("inputSymbol").getAsString());
        assertEquals("NULL", assignment.get("valueType").getAsString());
    }

    @Test
    public void nullComparisonWidensOnlyItsOwnReferenceDomain()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String leftRaw = "M_L_field_REGION.3.in.1_example/Owner";
        String rightRaw = "M_L_field_REGION.3.in.2_example/Owner";
        String nullableRaw = "M_L_field_REGION.3.in.3_example/Owner";
        JsonObject query = task(
                binaryExpression(referenceSymbol(leftRaw), "==",
                        referenceSymbol(rightRaw)),
                binaryExpression(referenceSymbol(nullableRaw), "==",
                        referenceSymbol("N")));
        JsonObject left = referenceFieldAction(
                "REGION.3.in.1", "example.Ref", "left", 41L, 71L);
        JsonObject right = referenceFieldAction(
                "REGION.3.in.2", "example.Ref", "right", 41L, 72L);
        JsonObject nullable = referenceFieldAction(
                "REGION.3.in.3", "example.Ref", "nullable", 41L, 73L);

        ConcolicConstraintSolver.Result result = solveForTest(
                query, containerActivation(left, right, nullable),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        java.util.Map<String, String> types = new java.util.LinkedHashMap<>();
        for (JsonElement element : result.modelAssignments) {
            JsonObject assignment = element.getAsJsonObject();
            types.put(assignment.get("inputSymbol").getAsString(),
                    assignment.get("valueType").getAsString());
        }
        assertFalse(types.get("REGION.3.in.1"),
                "NULL".equals(types.get("REGION.3.in.1")));
        assertFalse(types.get("REGION.3.in.2"),
                "NULL".equals(types.get("REGION.3.in.2")));
        assertEquals("NULL", types.get("REGION.3.in.3"));
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
    public void untypedSymbolIsRejectedInsteadOfBecomingAFreeReference()
            throws Exception {
        JsonObject untyped = new JsonObject();
        untyped.addProperty("_type", "SymbolExpression");
        untyped.addProperty("_exp",
                "M_L'Object'_REGION.3.in.0_example/Input");
        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(untyped, "==",
                        intSymbol("N"))),
                activation(), Paths.get("/does/not/exist/z3"), 10_000L);

        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray("unsupported").toString(),
                result.record.getAsJsonArray("unsupported").toString()
                        .contains("UNSUPPORTED_SYMBOL_TYPE:MISSING"));
        assertFalse(result.smtLib.contains("sym__M_L_Object"));

        JsonObject untypedConstant = new JsonObject();
        untypedConstant.addProperty("_type", "ConstExpr");
        untypedConstant.addProperty("_exp", "Y_UNKNOWN_payload");
        result = solveForTest(task(binaryExpression(untypedConstant, "==",
                        intSymbol("N"))),
                activation(), Paths.get("/does/not/exist/z3"), 10_000L);
        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray("unsupported").toString(),
                result.record.getAsJsonArray("unsupported").toString()
                        .contains("UNSUPPORTED_CONSTANT_TYPE:MISSING"));
        assertFalse(result.smtLib.contains("const__"));
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

    @Test
    public void directInitialIndexedReadsReplaySparseElements()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String stateSymbol = "M_L_field_REGION.3.in.4";
        JsonObject observedTwo = binaryExpression(
                indexedRead(stateSymbol, intConstant(2), "I"),
                "==", intConstant(-1));
        JsonObject observedZero = binaryExpression(
                indexedRead(stateSymbol, intConstant(0), "I"),
                "==", intConstant(0));
        JsonObject inBounds = binaryExpression(intConstant(2), "<",
                indexedStateSize(stateSymbol));
        JsonObject action = indexedInputAction("REGION.3.in.4");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(indexedRead(stateSymbol,
                                intConstant(0), "I"),
                                ">", intConstant(1)),
                        binaryExpression(indexedRead(stateSymbol,
                                intConstant(2), "I"),
                                ">", intConstant(5))),
                containerActivation(action), Paths.get("z3"), 10_000L,
                observedZero, observedTwo, inBounds);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 2,
                result.modelAssignments.size());
        for (JsonElement element : result.modelAssignments) {
            JsonObject assignment = element.getAsJsonObject();
            assertEquals("REGION.3.in.4",
                    assignment.get("inputSymbol").getAsString());
            assertFalse(assignment.has("target"));
            JsonObject target = assignment.getAsJsonObject(
                    "containerTarget");
            assertEquals("INDEXED", target.get("shape").getAsString());
            int index = target.get("index").getAsInt();
            assertTrue(assignment.toString(), index == 0 || index == 2);
            assertTrue(assignment.toString(),
                    assignment.get("value").getAsInt()
                            > (index == 0 ? 1 : 5));
        }
        assertTrue(result.smtLib, result.smtLib.contains(
                "(define-fun container_boundary__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(indexed_size "));
        assertTrue(result.smtLib, result.smtLib.contains("2147483647"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= (valueInt (indexed_read "
                        + "container__M_L_field_REGION_3_in_4"));
    }

    @Test
    public void indexedBoundaryRequiresOneRefActionAndConcreteIndex()
            throws Exception {
        String stateSymbol = "M_L_field_REGION.3.in.4";
        JsonObject condition = binaryExpression(
                indexedRead(stateSymbol, intConstant(1), "I"),
                ">", intConstant(5));

        ConcolicConstraintSolver.Result missing = solveForTest(
                task(condition), containerActivation(),
                Paths.get("/does/not/exist/z3"), 10_000L);
        assertEquals(missing.record.toString(), "MATERIALIZATION_GAP",
                missing.record.get("status").getAsString());
        assertEquals("SPARSE_CONTAINER_BOUNDARY_IS_NOT_MATERIALIZABLE",
                missing.record.get("reason").getAsString());

        ConcolicConstraintSolver.Result ambiguous = solveForTest(
                task(condition), containerActivation(
                        indexedInputAction("REGION.3.in.4"),
                        indexedInputAction("REGION.3.in.4")),
                Paths.get("/does/not/exist/z3"), 10_000L);
        assertEquals(ambiguous.record.toString(), "MATERIALIZATION_GAP",
                ambiguous.record.get("status").getAsString());

        JsonObject symbolicIndex = intSymbol(
                "M_I_field_REGION.3.in.5_index");
        ConcolicConstraintSolver.Result nonConcrete = solveForTest(
                task(binaryExpression(indexedRead(stateSymbol,
                                symbolicIndex, "I"),
                        ">", intConstant(5))),
                containerActivation(indexedInputAction("REGION.3.in.4")),
                Paths.get("/does/not/exist/z3"), 10_000L);
        assertEquals(nonConcrete.record.toString(), "MATERIALIZATION_GAP",
                nonConcrete.record.get("status").getAsString());
        assertTrue(nonConcrete.record
                .getAsJsonArray("unresolvedContainerBoundaries").toString(),
                nonConcrete.record
                        .getAsJsonArray("unresolvedContainerBoundaries")
                        .toString().contains("NON_CONCRETE_SELECTOR"));
    }

    @Test
    public void associativeBoundaryReplaysOneConcretePrimitiveKey()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String state = "M_L_field_REGION.3.in.4";
        JsonObject read = associativeRead(state, intConstant(7), "I");
        JsonObject action = containerInputAction(
                "REGION.3.in.4", "java.util.Map");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(read.deepCopy(), ">",
                        intConstant(10))),
                containerActivation(action), Paths.get("z3"), 10_000L,
                binaryExpression(read, "==", intConstant(3)));

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals("ASSOCIATIVE",
                target.get("shape").getAsString());
        assertEquals("I", target.get("keyJavaType").getAsString());
        assertEquals("7", target.get("keyValue").getAsString());
        assertTrue(assignment.get("value").getAsInt() > 10);
    }

    @Test
    public void orderedAssociativeCursorIsAReplayableSparseBoundary()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String state = "M_L_field_REGION.3.in.4";
        JsonObject selected = associativeNext(
                state, "KEY_VIEW", intConstant(0), "I");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(selected.deepCopy(), ">",
                        intConstant(0))),
                containerActivation(containerInputAction(
                        "REGION.3.in.4", "java.util.Set")),
                Paths.get("z3"), 10_000L,
                binaryExpression(selected, "==", intConstant(-7)));

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals("ASSOCIATIVE",
                target.get("shape").getAsString());
        assertEquals("ITERATION_INDEX",
                target.get("selectorKind").getAsString());
        assertEquals("KEY", target.get("projection").getAsString());
        assertEquals(0, target.get("index").getAsInt());
        assertTrue(assignment.get("value").getAsInt() > 0);
    }

    @Test
    public void associativeReadProjectsRemoveWithoutIteratorState()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String stateSymbol = "M_L_field_REGION.3.in.4";
        JsonObject state = associativeState(stateSymbol);
        JsonObject removed = associativeOperation("REMOVE", state,
                intConstant(3));
        JsonObject before = associativeRead(state.deepCopy(),
                intConstant(7), "I");
        JsonObject after = associativeRead(removed,
                intConstant(7), "I");
        JsonObject query = task(binaryExpression(after, ">",
                intConstant(10)));
        JsonArray constraints = new JsonArray();
        constraints.add(binaryExpression(before, "==", intConstant(3)));
        constraints.add(query.getAsJsonArray("constraints").get(0));
        query.add("constraints", constraints);

        ConcolicConstraintSolver.Result result = solveForTest(
                query, containerActivation(containerInputAction(
                        "REGION.3.in.4", "java.util.Map")),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "UNSAT",
                result.record.get("status").getAsString());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assoc_remove container__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(ite (= (VInt 7) (VInt 3))"));
    }

    @Test
    public void boxedIntegralContainerValuesKeepTheirJavaTypeTags()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject cleared = associativeOperation("CLEAR",
                associativeState("M_L_field_REGION.3.in.4"));
        JsonObject withByte = associativeOperation("PUT", cleared,
                numericConstant("B", "7"),
                numericConstant("B", "9"));
        JsonObject containsByte = associativeOperation("CONTAINS",
                withByte.deepCopy(), numericConstant("B", "7"));
        JsonObject containsInteger = associativeOperation("CONTAINS",
                withByte.deepCopy(), numericConstant("I", "7"));
        JsonObject readByte = associativeRead(withByte,
                numericConstant("B", "7"), "B");
        JsonObject taggedContainerCondition = binaryExpression(
                binaryExpression(containsByte, "!=",
                        containsInteger), "&&",
                binaryExpression(readByte, "==",
                        numericConstant("B", "9")));
        JsonObject condition = binaryExpression(
                taggedContainerCondition, "&&",
                binary(">", 0));

        ConcolicConstraintSolver.Result result = solveForTest(
                task(condition), activation(), Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains("(VByte 7)"));
        assertTrue(result.smtLib, result.smtLib.contains("(VInt 7)"));
        assertTrue(result.smtLib, result.smtLib.contains("(valueByte "));
        for (String tag : new String[]{"Byte", "Char", "Short", "Int",
                "Long"}) {
            assertTrue(result.smtLib,
                    result.smtLib.contains("(V" + tag + " (value"
                            + tag + " Int))"));
        }
    }

    @Test
    public void indexedReferenceEqualityReplaysAsAnExistingElementAlias()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String state = "M_L_field_REGION.3.in.4";
        JsonObject first = indexedRead(state, intConstant(0), "L");
        JsonObject second = indexedRead(state, intConstant(1), "L");
        JsonObject action = containerInputAction(
                "REGION.3.in.4", "java.util.List");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(first, "==", second)),
                containerActivation(action), Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("CONTAINER_REFERENCE_ALIAS",
                assignment.get("valueType").getAsString());
        assertEquals("REGION.3.in.4",
                assignment.get("referenceSourceInputSymbol").getAsString());
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals(1, target.get("index").getAsInt());
        assertEquals("INDEXED", target.get("sourceShape").getAsString());
        assertEquals(0, target.get("sourceIndex").getAsInt());
    }

    @Test
    public void indexedReferenceAliasCanUseAnotherContainerInput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject left = indexedRead("M_L_field_REGION.3.in.4",
                intConstant(0), "L");
        JsonObject right = indexedRead("M_L_field_REGION.3.in.5",
                intConstant(1), "L");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(left, "==", right)),
                containerActivation(
                        containerInputAction("REGION.3.in.4",
                                "java.util.List"),
                        containerInputAction("REGION.3.in.5",
                                "java.util.List")),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.5",
                assignment.get("inputSymbol").getAsString());
        assertEquals("REGION.3.in.4",
                assignment.get("referenceSourceInputSymbol").getAsString());
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals(1, target.get("index").getAsInt());
        assertEquals("INDEXED", target.get("sourceShape").getAsString());
        assertEquals(0, target.get("sourceIndex").getAsInt());
    }

    @Test
    public void indexedReferenceAliasCanUseOrdinaryReferenceInput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject element = indexedRead("M_L_field_REGION.3.in.4",
                intConstant(0), "L");
        String ordinaryRaw =
                "M_L_field_REGION.3.in.1_example/Owner";
        JsonObject ordinary = numericSymbol(ordinaryRaw, "example.Node");
        JsonObject ordinaryAction = referenceFieldAction(
                "REGION.3.in.1", "example.Node", "node", 41L, 73L);

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(element, "==", ordinary)),
                containerActivation(
                        containerInputAction("REGION.3.in.4",
                                "java.util.List"),
                        ordinaryAction),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.4",
                assignment.get("inputSymbol").getAsString());
        assertEquals("REGION.3.in.1",
                assignment.get("referenceSourceInputSymbol").getAsString());
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals(0, target.get("index").getAsInt());
        assertFalse(target.has("sourceShape"));
    }

    @Test
    public void nonNullSparseReferenceWithoutSourceIsUnresolved()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject element = indexedRead("M_L_field_REGION.3.in.4",
                intConstant(0), "L");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(element, "!=",
                        referenceSymbol("N"))),
                containerActivation(containerInputAction(
                        "REGION.3.in.4", "java.util.List")),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("REPLAY_CONTROL_FRONTIER_MODEL_IS_NOT_MATERIALIZABLE",
                result.record.get("reason").getAsString());
        assertTrue(result.record.toString(),
                result.record.getAsJsonArray(
                        "unresolvedReplayControlSymbols").size() == 1);
    }

    @Test
    public void sparseReferenceCanReplayNull() throws Exception {
        Assume.assumeTrue(z3Available());
        String port = "REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838"
                + ".in.fc915256-5ad9-3272-977b-2ccd8a7699a9";
        JsonObject element = associativeRead(
                "M_L_field_" + port, intConstant(7), "L");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(element, "==",
                        referenceSymbol("N"))),
                containerActivation(containerInputAction(
                        port, "java.util.Map")),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(port, assignment.get("inputSymbol").getAsString());
        assertEquals("NULL", assignment.get("valueType").getAsString());
        JsonObject target = assignment.getAsJsonObject("containerTarget");
        assertEquals("ACCESS_ORDINAL",
                target.get("selectorKind").getAsString());
        assertEquals(1, target.get("accessOrdinal").getAsInt());
        assertFalse(target.has("keyValue"));
    }

    @Test
    public void associativeElementLongFieldLowersJvmLcmpWithoutTypeGap()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String port = "REGION.3.in.map";
        String state = "M_L_field_" + port;
        JsonObject entryView = associativeOperation("ENTRY_VIEW",
                associativeState(state));
        JsonObject iterator = associativeOperation("ITERATOR", entryView);
        JsonObject next = associativeOperation("NEXT", iterator,
                intConstant(0));
        JsonObject value = associativeOperation("VALUE", next);
        JsonObject expiry = new JsonObject();
        expiry.addProperty("_type", "FieldAccessExpression");
        expiry.addProperty("_java_type", "J");
        expiry.addProperty("ownerClass", "example/Key");
        expiry.addProperty("fieldOffset", 24);
        expiry.add("owner", value);
        JsonObject now = new JsonObject();
        now.addProperty("_type", "PlaceholderExpression");
        now.addProperty("_place_holder_func", "currentTimeMills");
        now.addProperty("_count", 1);
        JsonObject lcmp = binaryExpression(expiry, "--", now);
        lcmp.addProperty("_java_type", "I");

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(lcmp, "<", intConstant(0))),
                containerActivation(containerInputAction(port,
                        "java.util.Map")), Paths.get("z3"), 10_000L);

        assertFalse(result.record.toString(), "UNSUPPORTED".equals(
                result.record.get("status").getAsString()));
        assertFalse(result.record.toString(), result.record
                .getAsJsonArray("unsupported").toString()
                .contains("MALFORMED_JVM_LCMP_OPERANDS"));
        assertTrue(result.smtLib, result.smtLib.contains("(ite (> "));
    }

    @Test
    public void observedReferenceIdentityIsIndependentOfDeclaredType()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String baseRaw = "M_L_field_REGION.3.in.1_example/Owner";
        String derivedRaw = "M_L_field_REGION.3.in.2_example/Owner";
        JsonObject base = numericSymbol(baseRaw, "example.Base");
        JsonObject derived = numericSymbol(derivedRaw, "example.Derived");
        JsonObject baseAction = referenceFieldAction(
                "REGION.3.in.1", "example.Base", "base", 41L, 73L);
        JsonObject derivedAction = referenceFieldAction(
                "REGION.3.in.2", "example.Derived", "derived", 41L, 73L);

        ConcolicConstraintSolver.Result result = solveForTest(
                task(binaryExpression(base, "!=", derived)),
                containerActivation(baseAction, derivedAction),
                Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "UNSAT",
                result.record.get("status").getAsString());
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

    private static JsonObject materialization(String symbol, int index) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", index);
        action.addProperty("javaType", "int");
        return action;
    }

    private static JsonObject containerActivation(JsonObject... actions) {
        JsonObject activation = new JsonObject();
        JsonArray inputActions = new JsonArray();
        for (JsonObject action : actions) inputActions.add(action);
        activation.add("inputActions", inputActions);
        return activation;
    }

    private static JsonObject indexedInputAction(String symbol) {
        return containerInputAction(symbol, "int[]");
    }

    private static JsonObject containerInputAction(
            String symbol, String javaType) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("sourceKind", "SHARED_HEAP");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("javaType", javaType);
        action.addProperty("mode", "SYMBOLIC");
        return action;
    }

    private static JsonObject referenceFieldAction(
            String symbol, String javaType, String field,
            long receiverObjectId, long valueObjectId) {
        JsonObject action = containerInputAction(symbol, javaType);
        JsonArray path = new JsonArray();
        path.add(field);
        action.add("fieldPath", path);
        action.addProperty("fieldReceiverObjectId", receiverObjectId);
        action.addProperty("valueObjectId", valueObjectId);
        return action;
    }

    private static JsonObject indexedState(String stateSymbol) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "[");
        identity.addProperty("_exp", stateSymbol);

        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "INDEXED");
        state.addProperty("operation", "STATE");
        state.addProperty("_java_type", "L");
        state.add("receiver", identity);
        state.add("arguments", new JsonArray());
        return state;
    }

    private static JsonObject indexedRead(String stateSymbol,
                                          JsonElement index,
                                          String javaType) {
        JsonArray arguments = new JsonArray();
        arguments.add(index);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ContainerRelation");
        read.addProperty("shape", "INDEXED");
        read.addProperty("operation", "READ");
        read.addProperty("_java_type", javaType);
        read.add("receiver", indexedState(stateSymbol));
        read.add("arguments", arguments);
        return read;
    }

    private static JsonObject indexedStateSize(String stateSymbol) {
        JsonObject size = new JsonObject();
        size.addProperty("_type", "ContainerRelation");
        size.addProperty("shape", "INDEXED");
        size.addProperty("operation", "SIZE");
        size.addProperty("_java_type", "I");
        size.add("receiver", indexedState(stateSymbol));
        size.add("arguments", new JsonArray());
        return size;
    }

    private static JsonObject indexedSize(String codePosition) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "[");
        identity.addProperty("_exp", "M_[_field_REGION.3.container");

        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "INDEXED");
        state.addProperty("operation", "STATE");
        state.addProperty("_java_type", "L");
        state.add("receiver", identity);
        state.add("arguments", new JsonArray());

        JsonObject size = new JsonObject();
        size.addProperty("_code_position", codePosition);
        size.addProperty("_type", "ContainerRelation");
        size.addProperty("shape", "INDEXED");
        size.addProperty("operation", "SIZE");
        size.addProperty("_java_type", "I");
        size.add("receiver", state);
        size.add("arguments", new JsonArray());
        return size;
    }

    private static JsonObject associativeRead(
            String stateSymbol, JsonElement key, String javaType) {
        return associativeRead(associativeState(stateSymbol), key, javaType);
    }

    private static JsonObject associativeState(String stateSymbol) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "L");
        identity.addProperty("_exp", stateSymbol);

        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.addProperty("_java_type", "L");
        state.add("receiver", identity);
        state.add("arguments", new JsonArray());
        return state;
    }

    private static JsonObject associativeRead(
            JsonElement receiver, JsonElement key, String javaType) {
        JsonArray arguments = new JsonArray();
        arguments.add(key);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ContainerRelation");
        read.addProperty("shape", "ASSOCIATIVE");
        read.addProperty("operation", "READ");
        read.addProperty("_java_type", javaType);
        read.add("receiver", receiver);
        read.add("arguments", arguments);
        return read;
    }

    private static JsonObject associativeNext(
            String stateSymbol, String viewKind, JsonElement cursor,
            String javaType) {
        JsonObject view = associativeOperation(
                viewKind, associativeState(stateSymbol));
        JsonArray arguments = new JsonArray();
        arguments.add(cursor);
        JsonObject next = new JsonObject();
        next.addProperty("_type", "ContainerRelation");
        next.addProperty("shape", "ASSOCIATIVE");
        next.addProperty("operation", "NEXT");
        next.addProperty("_java_type", javaType);
        next.add("receiver", view);
        next.add("arguments", arguments);
        return next;
    }

    private static JsonObject associativeOperation(
            String operation, JsonElement receiver,
            JsonElement... arguments) {
        JsonArray values = new JsonArray();
        for (JsonElement argument : arguments) values.add(argument);
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", "ContainerRelation");
        relation.addProperty("shape", "ASSOCIATIVE");
        relation.addProperty("operation", operation);
        relation.addProperty("_java_type", "L");
        relation.add("receiver", receiver);
        relation.add("arguments", values);
        return relation;
    }

    /** Adapts expression-focused unit fixtures to the production protocol. */
    private static ConcolicConstraintSolver.Result solveForTest(
            JsonObject legacyExpressionFixture, JsonObject activation,
            java.nio.file.Path z3, long timeoutMillis) throws Exception {
        return solveForTest(legacyExpressionFixture, activation, z3,
                timeoutMillis, new JsonObject[0]);
    }

    private static ConcolicConstraintSolver.Result solveForTest(
            JsonObject legacyExpressionFixture, JsonObject activation,
            java.nio.file.Path z3, long timeoutMillis,
            JsonObject... contextConstraints) throws Exception {
        JsonObject task = legacyExpressionFixture.deepCopy();
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

    private static JsonObject referenceSymbol(String raw) {
        return numericSymbol(raw, "L");
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
