package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import org.junit.Assume;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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
    public void exactJavaBitwiseAndShiftSemantics() throws Exception {
        Assume.assumeTrue(z3Available());

        JsonObject input = intSymbol(
                "M_I_field_REGION.3.in.0_example/Input");
        JsonObject masked = binaryExpression(input.deepCopy(), "&",
                intConstant(992));
        JsonObject shifted = binaryExpression(masked, ">>", intConstant(5));
        JsonObject condition = binaryExpression(shifted, "==",
                intConstant(31));

        ConcolicConstraintSolver.Result result = solveForTest(
                task(condition), activation(), Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(set-option :smt.arith.solver 2)"));
        assertTrue(result.smtLib, result.smtLib.contains("(mod "));
        assertTrue(result.smtLib, result.smtLib.contains("(div "));
        assertFalse(result.record.toString(),
                result.record.getAsJsonArray("unsupported").size() > 0);
    }

    @Test
    public void configuredSourceFieldIsAReplayMaterializationBoundary()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String occurrence = "test/node#epoch0/region/REGION.source#1";
        String sourceId = "SOURCE.COMPLEX.VALUE";
        String field = "<example.Source: long value>";
        String phaseId = sourcePhaseId(occurrence, sourceId);
        String raw = "M_J_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                phaseId, sourceId) + "_example/Source";
        JsonObject predicate = binaryExpression(
                numericSymbol(raw, "J"), ">",
                numericConstant("J", "100"));
        JsonObject activation = configuredSourceActivation(
                occurrence, sourceId, field);

        ConcolicConstraintSolver.Result result = solveForTest(
                task(predicate), activation, Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(raw, assignment.get("engineSymbol").getAsString());
        assertEquals("SOURCE_PHASE:" + phaseId,
                assignment.get("inputSymbol").getAsString());
        assertEquals(sourceId,
                assignment.get("configuredSourceId").getAsString());
        assertEquals(phaseId,
                assignment.get("configuredSourcePhaseId").getAsString());
        assertEquals(field, assignment.get(
                "configuredSourceFieldSignature").getAsString());
        assertTrue(assignment.get("value").getAsLong() > 100L);

        JsonObject wrongOccurrence = configuredSourceActivation(
                occurrence + ".other", sourceId, field);
        ConcolicConstraintSolver.Result refused = solveForTest(
                task(predicate), wrongOccurrence, Paths.get("z3"),
                10_000L);
        assertEquals(refused.record.toString(), "MATERIALIZATION_GAP",
                refused.record.get("status").getAsString());
        assertEquals("FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS",
                refused.record.get("reason").getAsString());
    }

    @Test
    public void modelProjectsWritableConfiguredSourceFromPrefixAndTargetRoot()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String occurrence = "test/node#epoch0/region/REGION.source#1";
        String sourceId = "SOURCE.PREFIX.VALUE";
        String field = "<example.Source: long prefixValue>";
        String prefixRaw = "M_J_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                sourcePhaseId(occurrence, sourceId), sourceId)
                + "_example/Source";
        String targetRaw = "M_I_field_REGION.3.in.0_example/Input";
        JsonObject prefix = binaryExpression(
                numericSymbol(prefixRaw, "J"), ">",
                numericConstant("J", "100"));
        JsonObject target = binaryExpression(
                numericSymbol(targetRaw, "I"), ">", intConstant(0));
        JsonObject activation = configuredSourceActivation(
                occurrence, sourceId, field);
        JsonObject targetAction = materialization("REGION.3.in.0", 0);
        targetAction.addProperty("mode", "SYMBOLIC");
        activation.getAsJsonArray("inputActions").add(targetAction);

        ConcolicConstraintSolver.Result result = solveForTest(
                task(prefix, target), activation, Paths.get("z3"),
                10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 2,
                result.modelAssignments.size());
        JsonObject sourceAssignment = null;
        JsonObject targetAssignment = null;
        for (JsonElement element : result.modelAssignments) {
            JsonObject assignment = element.getAsJsonObject();
            if (prefixRaw.equals(
                    assignment.get("engineSymbol").getAsString())) {
                sourceAssignment = assignment;
            } else if (targetRaw.equals(
                    assignment.get("engineSymbol").getAsString())) {
                targetAssignment = assignment;
            }
        }
        assertTrue(result.modelAssignments.toString(),
                sourceAssignment != null);
        assertTrue(result.modelAssignments.toString(),
                targetAssignment != null);
        assertEquals(sourceId, sourceAssignment.get(
                "configuredSourceId").getAsString());
        assertEquals(field, sourceAssignment.get(
                "configuredSourceFieldSignature").getAsString());
        assertTrue(sourceAssignment.get("value").getAsLong() > 100L);
        assertEquals("REGION.3.in.0",
                targetAssignment.get("inputSymbol").getAsString());
        assertTrue(targetAssignment.get("value").getAsInt() > 0);
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
    public void freeEnvironmentSupportRefusesReplayBeforeSolverLaunch()
            throws Exception {
        String targetRaw = "M_I_field_REGION.3.in.0_example/Input";
        JsonObject environmentPrefix = binaryExpression(
                currentTimeMillisPlaceholder(1), ">",
                numericConstant("J", "0"));
        JsonObject target = binaryExpression(
                numericSymbol(targetRaw, "I"), ">", intConstant(0));

        ConcolicConstraintSolver.Result result = solveForTest(
                task(environmentPrefix, target), activation(),
                Paths.get("definitely-missing-z3"), 10_000L);

        assertEquals(result.record.toString(), "MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("REPLAY_CONTROL_FRONTIER_IS_NOT_MATERIALIZABLE",
                result.record.get("reason").getAsString());
        assertTrue(result.record.toString(), result.record
                .getAsJsonArray("unresolvedReplaySupportSymbols")
                .contains(new com.google.gson.JsonPrimitive(
                        "ENVIRONMENT_PLACEHOLDER:currentTimeMills#1")));
        assertEquals(0, result.modelAssignments.size());
    }

    @Test
    public void targetPrefixKeepsExactRpcCompanionOutOfAssignments()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String remoteRaw = "M_I_field_REMOTE.RPC.VALUE_example/Reply";
        String localRaw = "M_I_field_REGION.3.in.0_example/Input";
        JsonObject fixture = targetTask(
                binaryExpression(numericSymbol(remoteRaw, "I"), ">",
                        intConstant(0)),
                binaryExpression(numericSymbol(localRaw, "I"), ">",
                        intConstant(5)));
        VmHandoffEvidence.writeTo(fixture,
                java.util.Collections.singletonList(
                        VmHandoffEvidence.event("REGION.3.in.rpc", 11L,
                                numericSymbol(remoteRaw, "I"),
                                "TASK.REMOTE.PRODUCER",
                                "REGION.REMOTE/occurrence-1")));

        ConcolicConstraintSolver.Result result = solveForTest(
                fixture, activation(), Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        assertEquals(localRaw, result.modelAssignments.get(0)
                .getAsJsonObject().get("engineSymbol").getAsString());
    }

    @Test
    public void targetPrefixRequiresUniqueExactRpcCompanion()
            throws Exception {
        String remoteRaw = "M_I_field_REMOTE.RPC.VALUE_example/Reply";
        JsonObject missing = targetTask(
                binaryExpression(numericSymbol(remoteRaw, "I"), ">",
                        intConstant(0)),
                binary(">", 5));
        ConcolicConstraintSolver.Result missingResult = solveForTest(
                missing, activation(), Paths.get("definitely-missing-z3"),
                10_000L);
        assertEquals(missingResult.record.toString(),
                "MATERIALIZATION_GAP",
                missingResult.record.get("status").getAsString());
        assertEquals("TARGET_PREFIX_COMPANION_SUPPORT_MISSING",
                missingResult.record.get("reason").getAsString());

        JsonObject ambiguous = missing.deepCopy();
        java.util.List<JsonObject> events = new java.util.ArrayList<>();
        events.add(VmHandoffEvidence.event("REGION.3.in.rpc", 11L,
                numericSymbol(remoteRaw, "I"), "TASK.PRODUCER.A",
                "REGION.A/occurrence-1"));
        events.add(VmHandoffEvidence.event("REGION.3.in.rpc", 12L,
                numericSymbol(remoteRaw, "I"), "TASK.PRODUCER.B",
                "REGION.B/occurrence-1"));
        VmHandoffEvidence.writeTo(ambiguous, events);
        ConcolicConstraintSolver.Result ambiguousResult = solveForTest(
                ambiguous, activation(), Paths.get("definitely-missing-z3"),
                10_000L);
        assertEquals(ambiguousResult.record.toString(),
                "MATERIALIZATION_GAP",
                ambiguousResult.record.get("status").getAsString());
        assertEquals("TARGET_PREFIX_COMPANION_SUPPORT_AMBIGUOUS",
                ambiguousResult.record.get("reason").getAsString());
    }

    @Test
    public void targetPrefixRejectsPredicateMixingLocalAndCompanion()
            throws Exception {
        String remoteRaw = "M_I_field_REMOTE.RPC.VALUE_example/Reply";
        String localRaw = "M_I_field_REGION.3.in.0_example/Input";
        JsonObject mixed = targetTask(binaryExpression(
                numericSymbol(localRaw, "I"), ">",
                numericSymbol(remoteRaw, "I")));
        VmHandoffEvidence.writeTo(mixed,
                java.util.Collections.singletonList(
                        VmHandoffEvidence.event("REGION.3.in.rpc", 11L,
                                numericSymbol(remoteRaw, "I"),
                                "TASK.REMOTE.PRODUCER",
                                "REGION.REMOTE/occurrence-1")));

        ConcolicConstraintSolver.Result result = solveForTest(
                mixed, activation(), Paths.get("definitely-missing-z3"),
                10_000L);

        assertEquals(result.record.toString(), "MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("TARGET_PREFIX_MIXES_LOCAL_AND_COMPANION_SUPPORT",
                result.record.get("reason").getAsString());
    }

    @Test
    public void targetPrefixAcceptsOneExactSharedCompanion()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String sharedPort = "REGION.3.in.shared";
        String sharedRaw = "M_I_field_" + sharedPort + "_example/Owner";
        JsonObject fixture = targetTask(
                binaryExpression(numericSymbol(sharedRaw, "I"), ">",
                        intConstant(0)),
                binary(">", 5));
        JsonArray bindings = new JsonArray();
        bindings.add(exactSharedBinding(sharedPort));
        fixture.add("edgeBindings", bindings);
        JsonObject source = activation();
        JsonObject sharedAction = materialization(sharedPort, 1);
        sharedAction.addProperty("mode", "CONCRETE");
        source.getAsJsonArray("inputActions").add(sharedAction);

        ConcolicConstraintSolver.Result result = solveForTest(
                fixture, source, Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        assertEquals("REGION.3.in.0", result.modelAssignments.get(0)
                .getAsJsonObject().get("inputSymbol").getAsString());
    }

    @Test
    public void fieldBindingAliasProjectsItsUniqueWritableRepresentative()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String rootRaw = "M_I_field_REGION.3.in.0_example/Input";
        String aliasRaw = "M_I_field_REGION.99.in.0_example/Input";
        JsonObject target = binaryExpression(numericSymbol(aliasRaw, "I"),
                ">", intConstant(0));
        JsonObject rootBinding = fieldBinding(rootRaw);
        JsonObject aliasBinding = fieldBinding(aliasRaw);

        ConcolicConstraintSolver.Result result = solveForTest(
                task(target), activation(), Paths.get("z3"), 10_000L,
                rootBinding, aliasBinding);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(rootRaw,
                assignment.get("engineSymbol").getAsString());
        assertEquals("REGION.3.in.0",
                assignment.get("inputSymbol").getAsString());
        assertTrue(assignment.get("value").getAsInt() > 0);
    }

    @Test
    public void branchAliasWithoutFieldBindingIsNeverGuessedAsAReplayRoot()
            throws Exception {
        String aliasRaw = "M_I_field_REGION.99.in.0_example/Input";
        JsonObject target = binaryExpression(numericSymbol(aliasRaw, "I"),
                ">", intConstant(0));

        ConcolicConstraintSolver.Result result = solveForTest(
                task(target), activation(),
                Paths.get("definitely-missing-z3"), 10_000L);

        assertEquals(result.record.toString(), "MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS",
                result.record.get("reason").getAsString());
        assertTrue(result.record.toString(), result.record
                .getAsJsonArray("unresolvedTargetSymbols")
                .contains(new com.google.gson.JsonPrimitive(aliasRaw)));
        assertEquals(0, result.modelAssignments.size());
    }

    @Test
    public void fieldBindingAliasProjectsConfiguredSourceRepresentative()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String occurrence = "test/node#epoch0/region/REGION.alias#1";
        String sourceId = "SOURCE.ALIAS.VALUE";
        String field = "<example.Source: long value>";
        String sourceRaw = "M_J_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                sourcePhaseId(occurrence, sourceId), sourceId)
                + "_example/Source";
        String aliasRaw = "M_J_field_REGION.99.in.0_example/Source";
        JsonObject target = binaryExpression(numericSymbol(aliasRaw, "J"),
                ">", numericConstant("J", "0"));

        ConcolicConstraintSolver.Result result = solveForTest(
                task(target), configuredSourceActivation(
                        occurrence, sourceId, field), Paths.get("z3"),
                10_000L, fieldBinding(sourceRaw, "J"),
                fieldBinding(aliasRaw, "J"));

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(result.modelAssignments.toString(), 1,
                result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(sourceRaw,
                assignment.get("engineSymbol").getAsString());
        assertEquals(sourceId,
                assignment.get("configuredSourceId").getAsString());
        assertEquals(field, assignment.get(
                "configuredSourceFieldSignature").getAsString());
        assertTrue(assignment.get("value").getAsLong() > 0L);
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

    @Test
    public void aSolvedModelSaysWhichRecordedWriterItSelected()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject fixture = task(binary(">", 3));
        fixture.add(RecordedSessionModel.QUERY_FIELD,
                RecordedSharedStateFixtures.selectedReadCutQuery());

        ConcolicConstraintSolver.Result result = solveForTest(fixture,
                activation(), Paths.get("z3"), 10_000L);

        // The query has to declare the choice before a model can report it.
        assertEquals("SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const rf_selector__21__rf1 Bool)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__11 Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named pc_") && result.smtLib.contains("(get-value ("));

        JsonObject cut = result.record.getAsJsonObject("selectedReadCut");
        assertEquals(SelectedReadCut.KIND, cut.get("kind").getAsString());
        // Exactly one arm, chosen by z3 and read back rather than guessed.
        assertEquals(1, cut.get("selectedReads").getAsInt());
        JsonObject selection = cut.getAsJsonArray("selections").get(0)
                .getAsJsonObject();
        assertEquals(21L, selection.get("readEventId").getAsLong());
        assertTrue(selection.toString(),
                selection.get("selector").getAsString()
                        .startsWith("rf_selector__21__"));
        // A selection that compiled to a gate travels with the replay task;
        // one that did not is a named gate gap instead.
        assertEquals(selection.get("installed").getAsBoolean(),
                cut.getAsJsonArray("gates").size() > 0);
        assertTrue(cut.getAsJsonArray("refusals").size() > 0);
        // Every arm was valued, so nothing was left undetermined: the model
        // really did answer the choice the query declared.
        for (JsonElement refusal : cut.getAsJsonArray("refusals")) {
            assertFalse(refusal.toString(),
                    SelectedReadCut.MODEL_OMITS_READ_SELECTOR.equals(
                            refusal.getAsJsonObject().get("reason")
                                    .getAsString()));
        }
    }

    @Test
    public void aRecordedReadCutNeverTurnsASatisfiableQueryUnsatisfiable()
            throws Exception {
        Assume.assumeTrue(z3Available());
        // Its positions are fresh variables over an acyclic recorded order,
        // and the unknown-writer arm carries no order at all, so the cut
        // cannot remove a model the query had without it.
        JsonObject withCut = task(binary(">", 3));
        withCut.add(RecordedSessionModel.QUERY_FIELD,
                RecordedSharedStateFixtures.selectedReadCutQuery());

        ConcolicConstraintSolver.Result plain = solveForTest(
                task(binary(">", 3)), activation(), Paths.get("z3"),
                10_000L);
        ConcolicConstraintSolver.Result gated = solveForTest(withCut,
                activation(), Paths.get("z3"), 10_000L);

        assertEquals("SAT_MODEL_READY",
                plain.record.get("status").getAsString());
        assertEquals("SAT_MODEL_READY",
                gated.record.get("status").getAsString());
        assertFalse(plain.record.has("selectedReadCut"));
        assertEquals(plain.modelAssignments.size(),
                gated.modelAssignments.size());

        // That harmlessness is a property of a cut this composition admitted.
        // A payload carrying any other authority is refused, never dropped:
        // ignoring it would silently solve a query whose read-from choice
        // nobody had stated.
        JsonObject forged = task(binary(">", 3));
        JsonObject unadmitted = RecordedSharedStateFixtures
                .selectedReadCutQuery().deepCopy();
        unadmitted.addProperty("authority", "FORGED_READ_CUT_AUTHORITY_V1");
        forged.add(RecordedSessionModel.QUERY_FIELD, unadmitted);
        try {
            solveForTest(forged, activation(), Paths.get("z3"), 10_000L);
            fail("an unadmitted recorded read cut must be refused");
        } catch (IOException refused) {
            assertTrue(String.valueOf(refused.getMessage()),
                    String.valueOf(refused.getMessage()).contains(
                            "unadmitted recorded read cut"));
        }
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

    private static JsonObject configuredSourceActivation(
            String occurrence, String sourceId, String fieldSignature) {
        JsonObject activation = new JsonObject();
        activation.addProperty("occurrenceId", occurrence);
        activation.add("inputActions", new JsonArray());
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", sourceId);
        source.addProperty("sourcePhaseId",
                sourcePhaseId(occurrence, sourceId));
        source.addProperty("fieldSignature", fieldSignature);
        source.addProperty("requiredOutputFieldSignature",
                "<example.Source: long output>");
        JsonArray sources = new JsonArray();
        sources.add(source);
        activation.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        return activation;
    }

    private static JsonObject configuredSourcesActivation(
            String occurrence, String... sourceIds) {
        JsonObject activation = new JsonObject();
        activation.addProperty("occurrenceId", occurrence);
        activation.add("inputActions", new JsonArray());
        JsonArray sources = new JsonArray();
        for (int index = 0; index < sourceIds.length; index++) {
            JsonObject source = new JsonObject();
            source.addProperty("authority",
                    SymbolicSourceEvidence.DECLARATION_AUTHORITY);
            source.addProperty("sourceId", sourceIds[index]);
            source.addProperty("sourcePhaseId",
                    sourcePhaseId(occurrence, sourceIds[index]));
            source.addProperty("fieldSignature", "<example.Source: long value"
                    + index + ">");
            source.addProperty("requiredOutputFieldSignature",
                    "<example.Source: long output>");
            sources.add(source);
        }
        activation.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        return activation;
    }

    private static String sourcePhaseId(
            String occurrence, String sourceId) {
        return ConfiguredSourcePhaseContract.phaseId(occurrence, sourceId,
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

    private static JsonObject targetTask(JsonObject... conditions) {
        JsonObject task = task(conditions);
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        return task;
    }

    private static JsonObject exactSharedBinding(String toInputPort) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("edgeId", "EDGE.EXACT.SHARED");
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("fromOccurrenceId",
                "REGION.PRODUCER/occurrence-1");
        binding.addProperty("toOccurrenceId",
                "REGION.3/occurrence-1");
        binding.addProperty("fromOutputPort", "REGION.PRODUCER.out.0");
        binding.addProperty("toInputPort", toInputPort);
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        binding.addProperty("writerEventSeq", 20L);
        binding.addProperty("readerEventSeq", 30L);
        binding.addProperty("receiverObjectId", 7L);
        binding.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        return binding;
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

    private static JsonObject currentTimeMillisPlaceholder(int count) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "PlaceholderExpression");
        result.addProperty("_java_type", "J");
        result.addProperty("_place_holder_func", "currentTimeMills");
        result.addProperty("_count", count);
        return result;
    }

    private static JsonObject fieldBinding(String raw) {
        return fieldBinding(raw, "I");
    }

    private static JsonObject fieldBinding(String raw, String javaType) {
        JsonObject owner = numericSymbol(
                "M_L'example/Owner'_1", "example/Owner");
        JsonObject field = new JsonObject();
        field.addProperty("_type", "FieldAccessExpression");
        field.addProperty("_java_type", javaType);
        field.addProperty("ownerClass", "example/Owner");
        field.addProperty("fieldOffset", 8);
        field.add("owner", owner);
        JsonObject binding = binaryExpression(field, "==",
                numericSymbol(raw, javaType));
        binding.addProperty("_code_position",
                "static void java.lang.System.symbolizeExactField("
                        + "jobject, jobject, jobject, jobject, jobject):-1");
        return binding;
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
