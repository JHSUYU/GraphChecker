package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicSummaryImporterTest {
    @Test
    public void executableActivationRequiresCanonicalMaterializationObjects()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path regions = root.resolve("regions.jsonl");
            JsonObject region = new JsonObject();
            region.addProperty("regionId", "REGION.ACTIVATION.SCHEMA");
            write(regions, region + "\n");

            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("activationId", "ACT.ACTIVATION.SCHEMA");
            raw.addProperty("regionId", "REGION.ACTIVATION.SCHEMA");
            raw.addProperty("exitKind", "NORMAL");
            raw = canonicalRuntimeResultForTest(raw);

            JsonObject base = new JsonObject();
            base.addProperty("activationId", "ACT.ACTIVATION.SCHEMA");
            base.addProperty("regionId", "REGION.ACTIVATION.SCHEMA");
            RegionCaptureGoal.outputClosure().writeTo(base);
            JsonObject[] invalid = new JsonObject[]{
                    base.deepCopy(), base.deepCopy(), base.deepCopy()};
            invalid[1].add("materializations", new JsonObject());
            JsonArray nonObject = new JsonArray();
            nonObject.add("declaration-is-not-an-action");
            invalid[2].add("materializations", nonObject);
            String[] expected = new String[]{
                    "materializations must be present as a JSON object array",
                    "materializations must be a JSON array",
                    "materializations[0] must be a JSON object"};

            for (int index = 0; index < invalid.length; index++) {
                Path caseRoot = root.resolve("activation-case-" + index);
                Files.createDirectories(caseRoot);
                Path activations = caseRoot.resolve("activations.jsonl");
                Path results = caseRoot.resolve("results.jsonl");
                Path output = caseRoot.resolve("summaries.jsonl");
                Path diagnostics = caseRoot.resolve("diagnostics.jsonl");
                // Bypass the canonical fixture writer: malformed scheduler
                // output is the subject of this test.
                writeVerbatim(activations, invalid[index] + "\n");
                writeVerbatim(results, raw + "\n");

                ConcolicSummaryImporter.ImportResult imported =
                        ConcolicSummaryImporter.importSummaries(
                                results, activations, regions, output,
                                diagnostics, caseRoot.resolve("cache"));

                assertEquals(0, imported.validSummaryCount);
                JsonObject diagnostic = JsonParser.parseString(new String(
                        Files.readAllBytes(diagnostics),
                        StandardCharsets.UTF_8).trim()).getAsJsonObject();
                assertEquals("INVALID_EXECUTABLE_ACTIVATION_SCHEMA",
                        diagnostic.get("code").getAsString());
                assertTrue(diagnostic.get("detail").getAsString(),
                        diagnostic.get("detail").getAsString().contains(
                                expected[index]));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void pathRelationClosureUsesOnlyExecutableMaterializations() {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("symbol", "REGION.CLOSURE.in.0");
        declaration.addProperty("lazy", true);
        declaration.addProperty("bindingMode", "ROOT_ENTRY");
        JsonObject activation = new JsonObject();
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        activation.add("symbolize", declarations);

        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", "I");
        constant.addProperty("_exp", "Y_I_7");
        JsonArray pathCondition = new JsonArray();
        pathCondition.add(constant.deepCopy());
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.CLOSURE.out.0", constant.deepCopy());

        activation.add("materializations", new JsonArray());
        assertEquals(null,
                PathRelationInputClosure.proveGuardedConstantUnusedInput(
                        activation, "REGION.CLOSURE.in.0", pathCondition,
                        outputs, true,
                        "EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_"
                                + "PATH_GUARD",
                        true));

        JsonArray executable = new JsonArray();
        executable.add(declaration.deepCopy());
        activation.add("materializations", executable);
        assertTrue(PathRelationInputClosure
                .proveGuardedConstantUnusedInput(activation,
                        "REGION.CLOSURE.in.0", pathCondition, outputs, true,
                        "EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_"
                                + "PATH_GUARD",
                        true) != null);

        JsonObject[] malformed = new JsonObject[]{activation.deepCopy(),
                activation.deepCopy(), activation.deepCopy()};
        malformed[0].remove("materializations");
        malformed[1].addProperty("materializations", "not-an-array");
        JsonArray nonObject = new JsonArray();
        nonObject.add(1);
        malformed[2].add("materializations", nonObject);
        for (JsonObject value : malformed) {
            try {
                PathRelationInputClosure.proveGuardedConstantUnusedInput(
                        value, "REGION.CLOSURE.in.0", pathCondition,
                        outputs, true,
                        "EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_"
                                + "PATH_GUARD",
                        true);
                throw new AssertionError(
                        "malformed executable activation must fail closed");
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage().contains(
                        "materializations"));
            }
        }
    }

    @Test
    public void canonicalRuntimeEnvelopeRejectsMissingOrMismatchedAuthority()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activations.jsonl");
            Path regions = root.resolve("regions.jsonl");

            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.SCHEMA");
            activation.addProperty("regionId", "REGION.SCHEMA");
            write(activations, activation + "\n");
            JsonObject region = new JsonObject();
            region.addProperty("regionId", "REGION.SCHEMA");
            write(regions, region + "\n");

            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("activationId", "ACT.SCHEMA");
            raw.addProperty("regionId", "REGION.SCHEMA");
            raw.addProperty("exitKind", "NORMAL");
            raw = canonicalRuntimeResultForTest(raw);

            JsonObject[] invalid = new JsonObject[15];
            String[] expected = new String[]{
                    "engineSummary must be a JSON object",
                    "engineSummary.engine must be openjdk8-zero-concolic",
                    "engineSummary.regionId must exactly match the result",
                    "engineSummary.activationId must exactly match the result",
                    "activationId must be a nonempty JSON string",
                    "regionId must be a nonempty JSON string",
                    "runtimeHeapEffects is retired and must be absent",
                    "runtimeHeapObservations must be a JSON array",
                    "dynamicFieldBindings must be a JSON array",
                    "pathConditionRecordingPaused must be true",
                    "pathConditionRecordingPaused must be true",
                    "pathConditionPauseDepth must be a positive integer",
                    "pathConditionPauseDepth must be a positive integer",
                    "pathConditionPauseDepth must be a positive integer",
                    "pathConditionPauseDepth must be a positive integer"};
            for (int index = 0; index < invalid.length; index++) {
                invalid[index] = raw.deepCopy();
            }
            invalid[0].remove("engineSummary");
            invalid[1].getAsJsonObject("engineSummary").addProperty(
                    "engine", "unknown-engine");
            invalid[2].getAsJsonObject("engineSummary").addProperty(
                    "regionId", "REGION.OTHER");
            invalid[3].getAsJsonObject("engineSummary").addProperty(
                    "activationId", "ACT.OTHER");
            invalid[4].remove("activationId");
            invalid[5].addProperty("regionId", 7);
            invalid[6].add("runtimeHeapEffects", new JsonArray());
            invalid[7].remove("runtimeHeapObservations");
            invalid[8].remove("dynamicFieldBindings");
            invalid[9].getAsJsonObject("engineSummary").addProperty(
                    "pathConditionRecordingPaused", false);
            invalid[10].getAsJsonObject("engineSummary").remove(
                    "pathConditionRecordingPaused");
            invalid[11].getAsJsonObject("engineSummary").addProperty(
                    "pathConditionPauseDepth", 0);
            invalid[12].getAsJsonObject("engineSummary").addProperty(
                    "pathConditionPauseDepth", -1);
            invalid[13].getAsJsonObject("engineSummary").remove(
                    "pathConditionPauseDepth");
            invalid[14].getAsJsonObject("engineSummary").addProperty(
                    "pathConditionPauseDepth", "2");

            for (int index = 0; index < invalid.length; index++) {
                Path caseRoot = root.resolve("case-" + index);
                Files.createDirectories(caseRoot);
                Path results = caseRoot.resolve("results.jsonl");
                Path output = caseRoot.resolve("summaries.jsonl");
                Path diagnostics = caseRoot.resolve("diagnostics.jsonl");
                writeVerbatim(results, invalid[index] + "\n");
                ConcolicSummaryImporter.ImportResult imported =
                        ConcolicSummaryImporter.importSummaries(
                                results, activations, regions, output,
                                diagnostics, caseRoot.resolve("cache"));
                assertEquals(0, imported.validSummaryCount);
                assertEquals(1, imported.diagnosticCount);
                String diagnostic = new String(Files.readAllBytes(
                        diagnostics), StandardCharsets.UTF_8);
                assertTrue(diagnostic,
                        diagnostic.contains("INVALID_RUNTIME_RESULT_SCHEMA"));
                assertTrue(diagnostic, diagnostic.contains(expected[index]));
                assertEquals(0, Files.size(output));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void tokenValueRefWitnessRequiresExactActivationAndValueToken() {
        JsonObject witness = valueRefWitnessRecord(false);
        assertTrue(ConcolicSummaryImporter.validValueRefWitnessForTests(
                witness, "ACT.P"));

        witness.addProperty("valueExpressionWitnessObjectToken", 104L);
        assertFalse(ConcolicSummaryImporter.validValueRefWitnessForTests(
                witness, "ACT.P"));
        witness.addProperty("valueExpressionWitnessObjectToken", 103L);
        assertFalse(ConcolicSummaryImporter.validValueRefWitnessForTests(
                witness, "ACT.Q"));
    }

    @Test
    public void tokenMapRefWitnessRequiresExactActivationAndMapToken() {
        JsonObject witness = mapRefWitnessRecord();
        assertTrue(ConcolicSummaryImporter.validMapRefWitnessForTests(
                witness, "ACT.P"));

        witness.addProperty("mapExpressionWitnessObjectToken", 102L);
        assertFalse(ConcolicSummaryImporter.validMapRefWitnessForTests(
                witness, "ACT.P"));
        witness.addProperty("mapExpressionWitnessObjectToken", 101L);
        assertFalse(ConcolicSummaryImporter.validMapRefWitnessForTests(
                witness, "ACT.Q"));
    }
    private static JsonObject valueRefWitnessRecord(boolean certified) {
        JsonObject record = new JsonObject();
        record.addProperty("valueExpressionAuthority",
                "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1");
        record.addProperty("objectTokenScope", "ACT.P");
        record.addProperty("valueObjectToken", 103L);
        record.addProperty("valueExpressionWitnessSchemaVersion", 1);
        record.addProperty("valueExpressionWitnessKind",
                "ACTIVATION_LOCAL_REF_SYMBOL_WITNESS");
        record.addProperty("valueExpressionWitnessObjectToken", 103L);
        record.addProperty("valueExpressionWitnessObjectTokenScope", "ACT.P");
        record.addProperty("valueExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "L");
        expression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T103");
        record.add("valueExpression", expression);
        if (certified) {
            record.addProperty("valueExpressionWitnessCertified", true);
            record.addProperty("valueExpressionWitnessCertificationAuthority",
                    "IMPORTER_EXACT_ACTIVATION_TOKEN_AND_"
                            + "DYNAMIC_FIELD_OWNER_JOIN_V1");
            record.addProperty(
                    "valueExpressionWitnessCertifiedObjectToken", 103L);
            record.addProperty(
                    "valueExpressionWitnessCertifiedObjectTokenScope", "ACT.P");
        }
        return record;
    }

    private static JsonObject mapRefWitnessRecord() {
        JsonObject record = new JsonObject();
        record.addProperty("expressionAuthority",
                "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1");
        record.addProperty("objectTokenScope", "ACT.P");
        record.addProperty("backingMapObjectToken", 101L);
        record.addProperty("mapExpressionWitnessSchemaVersion", 1);
        record.addProperty("mapExpressionWitnessKind",
                "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS");
        record.addProperty("mapExpressionWitnessObjectToken", 101L);
        record.addProperty("mapExpressionWitnessObjectTokenScope", "ACT.P");
        record.addProperty("mapExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "L");
        expression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T101");
        record.add("mapExpression", expression);
        return record;
    }

    @Test
    public void admitsOnlyObservedUnforcedDirectedTargetReplay()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");

            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.T");
            activation.addProperty("regionId", "REGION.T");
            activation.addProperty("regionInstanceId",
                    "REGION.T@test#call7");
            activation.addProperty("rootCallId", 7);
            activation.addProperty("targetReplayRequired", true);
            activation.addProperty("executionPhase",
                    "REPLAY_DIRECTED_TARGET");
            activation.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
            JsonObject originalCondition = new JsonObject();
            originalCondition.addProperty("_type", "BinaryExpression");
            originalCondition.addProperty("_op", "!=");
            JsonObject left = new JsonObject();
            left.addProperty("_type", "SymbolExpression");
            left.addProperty("_java_type", "I");
            left.addProperty("_exp", "M_I_field_REGION.T.in.0_example/Target");
            JsonObject right = new JsonObject();
            right.addProperty("_type", "ConstExpr");
            right.addProperty("_java_type", "I");
            right.addProperty("_exp", "Y_I_0");
            originalCondition.add("_left", left);
            originalCondition.add("_right", right);
            JsonObject sourceEvent = new JsonObject();
            sourceEvent.addProperty("eventId", 1);
            sourceEvent.addProperty("contextId", 7);
            BranchWitness sourceWitness = BranchWitness.vmPc(
                    "example.Target#u8", "example.Target", 8, 1, true,
                    originalCondition, 0, sourceEvent);
            BranchReplayContract targetContract = BranchReplayContract.flip(
                    Collections.<BranchWitness>emptyList(), sourceWitness);
            activation.add("replayContract", targetContract.toJson());
            write(activations, activation + "\n");

            JsonObject region = new JsonObject();
            region.addProperty("regionId", "REGION.T");
            JsonObject failure = new JsonObject();
            failure.addProperty("kind", "FAILURE_PREDICATE");
            failure.addProperty("cell",
                    "example.Target#u9#exception:example.Fatal");
            JsonArray outputs = new JsonArray();
            outputs.add(failure);
            region.add("outputs", outputs);
            write(regions, region + "\n");

            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("activationId", "ACT.T");
            raw.addProperty("regionId", "REGION.T");
            raw.addProperty("exitKind", "THROW");
            raw.addProperty("exceptionType", "example.Wrapper");
            raw.addProperty("branchOverrideUsed", false);
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", "example.Target#u8");
            branch.addProperty("occurrence", 1);
            branch.addProperty("outcome", false);
            branch.addProperty("observedOutcome", false);
            branch.addProperty("effectiveOutcome", false);
            branch.addProperty("overrideApplied", false);
            JsonObject replayEvent = new JsonObject();
            replayEvent.addProperty("eventId", 2);
            replayEvent.addProperty("contextId", 7);
            BranchWitness replayWitness = BranchWitness.vmPc(
                    "example.Target#u8", "example.Target", 8, 1, false,
                    targetContract.requiredSatisfiedPredicate(), 0,
                    replayEvent);
            branch.add("witness", replayWitness.toJson());
            JsonArray branches = new JsonArray();
            branches.add(branch);
            raw.add("branchMappings", branches);
            JsonObject cause = new JsonObject();
            cause.addProperty("type", "example.Fatal");
            JsonArray exceptionChain = new JsonArray();
            exceptionChain.add(cause);
            raw.add("exceptionChain", exceptionChain);
            JsonObject engine = new JsonObject();
            engine.addProperty("active", true);
            engine.addProperty("regionId", "REGION.T");
            engine.addProperty("activationId", "ACT.T");
            engine.add("pathCondition", new JsonArray());
            raw.add("engineSummary", engine);
            write(results, raw + "\n");

            ConcolicSummaryImporter.ImportResult accepted =
                    ConcolicSummaryImporter.importSummaries(results,
                            activations, regions, output, diagnostics,
                            root.resolve("cache-ok"));
            assertEquals(1, accepted.validSummaryCount);
            JsonObject acceptedSummary = JsonParser.parseString(new String(
                    Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                    .getAsJsonObject();
            assertFalse(acceptedSummary.has("targetReplayValidated"));
            assertEquals(targetContract.contractId(), acceptedSummary
                    .getAsJsonObject("executionAdmission")
                    .getAsJsonObject("branchReplayObservation")
                    .get("contractId").getAsString());
            assertFalse(acceptedSummary.has("directedTargetQuery"));
            assertEquals("SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION",
                    acceptedSummary.getAsJsonObject("executionAdmission")
                            .get("authority").getAsString());

            branch.addProperty("observedOutcome", true);
            BranchWitness wrongWitness = BranchWitness.vmPc(
                    "example.Target#u8", "example.Target", 8, 1, true,
                    originalCondition, 0, replayEvent);
            branch.add("witness", wrongWitness.toJson());
            write(results, raw + "\n");
            Path rejectedOutput = root.resolve("rejected.jsonl");
            Path rejectedDiagnostics = root.resolve("rejected-diagnostics.jsonl");
            ConcolicSummaryImporter.ImportResult rejected =
                    ConcolicSummaryImporter.importSummaries(results,
                            activations, regions, rejectedOutput,
                            rejectedDiagnostics, root.resolve("cache-bad"));
            assertEquals(0, rejected.validSummaryCount);
            assertTrue(new String(Files.readAllBytes(rejectedDiagnostics),
                    StandardCharsets.UTF_8).contains(
                    "TARGET_OUTCOME_MISMATCH"));

            JsonObject seedActivation = activation.deepCopy();
            seedActivation.addProperty("targetReplayRequired", false);
            seedActivation.addProperty("executionPhase",
                    "CAPTURE_THEN_NEGATE");
            seedActivation.remove("replayContract");
            branch.addProperty("observedOutcome", false);
            branch.addProperty("overrideApplied", false);
            raw.addProperty("branchOverrideUsed", false);
            for (int mode = 0; mode < 3; mode++) {
                JsonObject candidateActivation = seedActivation.deepCopy();
                JsonObject candidateRaw = raw.deepCopy();
                String expectedFailure;
                if (mode == 0) {
                    candidateRaw.addProperty("branchOverrideUsed", true);
                    expectedFailure = "BRANCH_OVERRIDE_USED";
                } else if (mode == 1) {
                    candidateRaw.getAsJsonArray("branchMappings").get(0)
                            .getAsJsonObject().addProperty(
                                    "overrideApplied", true);
                    expectedFailure = "BRANCH_OVERRIDE_USED";
                } else {
                    JsonObject forced = new JsonObject();
                    forced.addProperty("siteId", "example.Target#u8");
                    forced.addProperty("occurrence", 1);
                    forced.addProperty("desiredOutcome", false);
                    JsonArray forcedBranches = new JsonArray();
                    forcedBranches.add(forced);
                    candidateActivation.add("forcedBranches",
                            forcedBranches);
                    expectedFailure =
                            "FORCED_BRANCH_PLAN_OR_RESULT_PRESENT";
                }
                write(activations, candidateActivation + "\n");
                write(results, candidateRaw + "\n");
                Path seedOutput = root.resolve("rejected-seed-" + mode
                        + ".jsonl");
                Path seedDiagnostics = root.resolve(
                        "rejected-seed-diagnostics-" + mode + ".jsonl");
                ConcolicSummaryImporter.ImportResult rejectedSeed =
                        ConcolicSummaryImporter.importSummaries(results,
                                activations, regions, seedOutput,
                                seedDiagnostics, root.resolve(
                                        "cache-rejected-seed-" + mode));
                assertEquals(0, rejectedSeed.validSummaryCount);
                assertTrue(new String(Files.readAllBytes(seedDiagnostics),
                        StandardCharsets.UTF_8).contains(expectedFailure));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void validatesRegionSummaryWithNestedPathConditionPause()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            Path cache = root.resolve("cache");
            String method = "<example.Handler: void handle()>";
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + method + "\","
                    + "\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson() + ","
                    + "\"receiverType\":\"Handler\","
                    + "\"symbolize\":[{\"symbol\":\"REGION.0.in.0\"}],"
                    + "\"materializations\":[],"
                    + "\"outputs\":[{\"symbol\":\"REGION.0.out.0\","
                    + "\"location\":\"THROW_OR_BRANCH\"}]}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"rootMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + method + "\"]}\n");
            // The observation boundary and finish-time bookkeeping each hold
            // a pause, so a real custom-Zero result can legitimately report 2.
            write(results, "{\"event\":\"CONCOLIC_REGION_RESULT\","
                    + "\"activationId\":\"ACT.0\",\"regionId\":\"REGION.0\","
                    + "\"exitKind\":\"THROW\",\"exceptionType\":\"InvalidToken\","
                    + "\"unresolvedInputs\":[],"
                    + "\"rootOutputExpression\":{\"kind\":\"SYMBOLIC_OBJECT\"},"
                    + "\"engineSummary\":{\"active\":true,"
                    + "\"engine\":\"openjdk8-zero-concolic\","
                    + "\"regionId\":\"REGION.0\",\"activationId\":\"ACT.0\","
                    + "\"pathConditionRecordingPaused\":true,"
                    + "\"pathConditionPauseDepth\":2,"
                    + "\"pathCondition\":[{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"==\",\"_code_position\":"
                    + "\"virtual void example.Handler.handle():12\"}]}}\n");

            ConcolicSummaryImporter.ImportResult imported =
                    ConcolicSummaryImporter.importSummaries(results, activations,
                            regions, output, diagnostics, cache);

            assertEquals(1, imported.rawResultCount);
            assertEquals(1, imported.validSummaryCount);
            String summary = new String(Files.readAllBytes(output),
                    StandardCharsets.UTF_8);
            assertTrue(summary.contains("RUNTIME_CONCOLIC"));
            assertTrue(summary.contains("InvalidToken"));
            JsonObject importedSummary = JsonParser.parseString(
                    summary.trim()).getAsJsonObject();
            assertEquals(0, importedSummary.getAsJsonArray(
                    "symbolicInputs").size());
            assertEquals(1, Files.list(cache).count());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsRuntimeBookkeepingRemainingAfterNormalization()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            Path cache = root.resolve("cache");
            String method = "<example.Handler: void handle()>";
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + method + "\",\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson() + "}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"rootMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + method + "\"]}\n");

            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("activationId", "ACT.0");
            raw.addProperty("regionId", "REGION.0");
            raw.addProperty("exitKind", "NORMAL");
            raw.addProperty("pathConditionIsolationPolicy",
                    ConcolicSummaryImporter.PATH_CONDITION_ISOLATION_POLICY);
            JsonObject engine = new JsonObject();
            engine.addProperty("active", true);
            engine.addProperty("regionId", "REGION.0");
            engine.addProperty("activationId", "ACT.0");
            JsonArray path = new JsonArray();
            JsonObject direct = new JsonObject();
            direct.addProperty("_type", "BinaryExpression");
            direct.addProperty("_code_position", "static jobject "
                    + "edu.uva.liftlab.graphchecker.runtime."
                    + "ConcolicRegionRuntime.safe(jobject):1513");
            path.add(direct);
            JsonObject nested = new JsonObject();
            nested.addProperty("_type", "BinaryExpression");
            nested.addProperty("_code_position",
                    "virtual void example.Handler.handle():12");
            JsonObject operand = new JsonObject();
            operand.addProperty("_type", "MethodExpression");
            operand.addProperty("_code_position", "static jobject "
                    + "edu/uva/liftlab/graphchecker/runtime/"
                    + "ConcolicRegionRuntime.safe(jobject):1514");
            nested.add("_left", operand);
            path.add(nested);
            engine.add("pathCondition", path);
            raw.add("engineSummary", engine);
            write(results, raw + "\n");

            ConcolicSummaryImporter.ImportResult imported =
                    ConcolicSummaryImporter.importSummaries(results,
                            activations, regions, output, diagnostics, cache);

            assertEquals(1, imported.rawResultCount);
            assertEquals(0, imported.validSummaryCount);
            assertEquals("", new String(Files.readAllBytes(output),
                    StandardCharsets.UTF_8));
            assertFalse(Files.exists(cache));
            JsonObject diagnostic = JsonParser.parseString(new String(
                    Files.readAllBytes(diagnostics), StandardCharsets.UTF_8)
                    .trim()).getAsJsonObject();
            assertEquals("RUNTIME_BOOKKEEPING_PATH_CONDITION",
                    diagnostic.get("code").getAsString());
            JsonObject detail = JsonParser.parseString(
                    diagnostic.get("detail").getAsString())
                    .getAsJsonObject();
            assertEquals(1, detail.getAsJsonArray(
                    "contaminatedConditionIndexes").size());
            assertEquals(1, detail.getAsJsonArray(
                    "runtimeCodePositions").size());
            assertEquals("REJECT_GRAPH_CHECKER_RUNTIME_CODE_POSITIONS",
                    detail.get("policy").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void preservesMappedDuplicateConditionOccurrence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\","
                    + "\"rootMethod\":\"<example.Handler: void handle()>\","
                    + "\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson() + ","
                    + "\"symbolize\":[]}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"methods\":[\"<example.Handler: void handle()>\"]}\n");
            String condition = "{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"!=\",\"_code_position\":"
                    + "\"virtual void example.Handler.handle():12\"}";
            write(results, "{\"event\":\"CONCOLIC_REGION_RESULT\","
                    + "\"activationId\":\"ACT.0\",\"regionId\":\"REGION.0\","
                    + "\"exitKind\":\"NORMAL\","
                    + "\"branchMappings\":["
                    + "{\"siteId\":\"example.Handler#u1\","
                    + "\"occurrence\":1,\"conditionIndex\":0,"
                    + "\"pathConditionSize\":1,"
                    + "\"pathConditionBaseline\":0},"
                    + "{\"siteId\":\"example.Handler#u1\","
                    + "\"occurrence\":2,\"conditionIndex\":1,"
                    + "\"pathConditionSize\":2,"
                    + "\"pathConditionBaseline\":1},"
                    + "{\"siteId\":\"example.Handler#u1\","
                    + "\"occurrence\":3,\"conditionIndex\":2,"
                    + "\"pathConditionSize\":3,"
                    + "\"pathConditionBaseline\":2}],"
                    + "\"engineSummary\":{\"active\":true,"
                    + "\"pathCondition\":[" + condition + ","
                    + condition + "," + condition + "]}}\n");

            ConcolicSummaryImporter.importSummaries(results, activations,
                    regions, output, diagnostics, root.resolve("cache"));

            JsonObject summary = JsonParser.parseString(new String(
                    Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                    .getAsJsonObject();
            assertEquals(3, summary.getAsJsonArray("pathCondition").size());
            JsonArray mappings = summary.getAsJsonArray("branchMappings");
            for (int index = 0; index < mappings.size(); index++) {
                JsonObject mapping = mappings.get(index).getAsJsonObject();
                assertEquals(index,
                        mapping.get("conditionIndex").getAsInt());
                assertEquals(index,
                        mapping.get("engineConditionIndex").getAsInt());
            }
            assertEquals(0, summary.getAsJsonObject(
                    "pathConditionNormalization")
                    .get("consecutiveDuplicatesRemoved").getAsInt());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void substitutesJimplePredicateForJvmCompareTrichotomyWitness()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            String method = "<example.Handler: void handle()>";
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + method + "\",\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson()
                    + ",\"symbolize\":[]}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"methods\":[\"" + method + "\"]}\n");

            JsonObject rawCondition = JsonParser.parseString("{"
                    + "\"_type\":\"BinaryExpression\","
                    + "\"_left\":{\"_type\":\"SymbolExpression\","
                    + "\"_exp\":\"expiry\"},"
                    + "\"_op\":\">\","
                    + "\"_right\":{\"_type\":\"SymbolExpression\","
                    + "\"_exp\":\"now\"},"
                    + "\"_code_position\":\"virtual void "
                    + "example.Handler.handle():12\"}").getAsJsonObject();
            JsonObject semanticCondition = rawCondition.deepCopy();
            semanticCondition.addProperty("_op", ">=");
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", method + "#u4");
            mapping.addProperty("occurrence", 1);
            mapping.addProperty("outcome", true);
            mapping.addProperty("rawConditionIndex", 0);
            mapping.addProperty("rawPathConditionSize", 1);
            mapping.addProperty("conditionNormalization",
                    "JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE");
            mapping.add("rawCondition", rawCondition.deepCopy());
            mapping.add("condition", semanticCondition.deepCopy());
            JsonArray mappings = new JsonArray();
            mappings.add(mapping);
            JsonArray path = new JsonArray();
            path.add(rawCondition.deepCopy());
            JsonObject engine = new JsonObject();
            engine.addProperty("active", true);
            engine.add("pathCondition", path);
            JsonObject result = new JsonObject();
            result.addProperty("event", "CONCOLIC_REGION_RESULT");
            result.addProperty("activationId", "ACT.0");
            result.addProperty("regionId", "REGION.0");
            result.addProperty("exitKind", "NORMAL");
            result.add("branchMappings", mappings);
            result.add("engineSummary", engine);
            write(results, result + "\n");

            ConcolicSummaryImporter.importSummaries(results, activations,
                    regions, output, diagnostics, root.resolve("cache"));

            JsonObject summary = JsonParser.parseString(new String(
                    Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                    .getAsJsonObject();
            JsonObject importedCondition = summary.getAsJsonArray(
                    "pathCondition").get(0).getAsJsonObject();
            assertEquals(">=", importedCondition.get("_op").getAsString());
            JsonObject importedMapping = summary.getAsJsonArray(
                    "branchMappings").get(0).getAsJsonObject();
            assertEquals(">", importedMapping.getAsJsonObject(
                    "rawCondition").get("_op").getAsString());
            assertEquals(">=", importedMapping.getAsJsonObject(
                    "condition").get("_op").getAsString());
            assertEquals(1, summary.getAsJsonObject(
                    "pathConditionNormalization").get(
                    "semanticBranchConditionSubstitutionCount").getAsInt());
            assertEquals("<", BranchPredicateAlgebra.complement(
                    importedCondition)
                    .getAsJsonObject().get("_op").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void filtersBookkeepingAndPreservesRawAndNormalizedIndices()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            String method = "<example.Target: java.lang.Object lookup(int)>";
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + method + "\",\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson()
                    + ",\"symbolize\":[]}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"methods\":[\"" + method + "\"]}\n");
            String producer = "{\"_type\":\"MethodExpression\","
                    + "\"_code_position\":\"virtual jobject "
                    + "example.Target.lookup(jint):40\"}";
            String bookkeeping = "{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"!=\",\"_code_position\":\"static jobject "
                    + "edu.uva.liftlab.graphchecker.runtime."
                    + "ConcolicRegionRuntime.safe(jobject):840\"}";
            String target = "{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"!=\",\"_code_position\":\"virtual jobject "
                    + "example.Target.lookup(jint):41\"}";
            write(results, "{\"event\":\"CONCOLIC_REGION_RESULT\","
                    + "\"activationId\":\"ACT.0\",\"regionId\":\"REGION.0\","
                    + "\"exitKind\":\"NORMAL\","
                    + "\"branchMappings\":[{\"conditionIndex\":2,"
                    + "\"pathConditionSize\":3,\"pathConditionBaseline\":0,"
                    + "\"condition\":" + target + "}],"
                    + "\"engineSummary\":{\"active\":true,"
                    + "\"pathCondition\":[" + producer + ","
                    + bookkeeping + "," + target + "]}}\n");

            ConcolicSummaryImporter.ImportResult imported =
                    ConcolicSummaryImporter.importSummaries(results, activations,
                            regions, output, diagnostics, root.resolve("cache"));

            assertEquals(1, imported.validSummaryCount);
            JsonObject summary = JsonParser.parseString(new String(
                    Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                    .getAsJsonObject();
            assertEquals(2, summary.getAsJsonArray("pathCondition").size());
            JsonObject mapping = summary.getAsJsonArray("branchMappings")
                    .get(0).getAsJsonObject();
            assertEquals(2, mapping.get("rawConditionIndex").getAsInt());
            assertEquals(1, mapping.get("normalizedConditionIndex").getAsInt());
            assertEquals(1, mapping.get("conditionIndex").getAsInt());
            assertEquals(2, mapping.get("pathConditionSize").getAsInt());
            assertTrue(mapping.has("rawCondition"));

            JsonObject normalization = summary.getAsJsonObject(
                    "pathConditionNormalization");
            assertEquals(1, normalization.get("filteredConditionCount").getAsInt());
            assertEquals(2, normalization.get("semanticConditionCount").getAsInt());
            JsonObject filteredIndex = normalization
                    .getAsJsonArray("conditionIndexMap").get(1).getAsJsonObject();
            assertEquals(-1, filteredIndex.get("normalizedConditionIndex").getAsInt());
            assertEquals("FILTERED", filteredIndex.get("status").getAsString());
            String diagnosticRows = new String(Files.readAllBytes(diagnostics),
                    StandardCharsets.UTF_8);
            assertTrue(diagnosticRows.contains(
                    "FILTERED_NON_SEMANTIC_PATH_CONDITIONS"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void treatsAvailableBranchMappingsAsAuthorityForBinaryConditions()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            String method = "<example.Target: java.lang.Object lookup(int)>";
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + method + "\",\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson()
                    + ",\"symbolize\":[]}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"methods\":[\"" + method + "\"]}\n");
            String semanticEvent = "{\"_type\":\"MethodExpression\","
                    + "\"_code_position\":\"virtual jobject "
                    + "example.Target.lookup(jint):40\"}";
            String unmapped = "{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"==\",\"_code_position\":"
                    + "\"virtual jobject example.Target.lookup(jint):41\"}";
            String mapped = "{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"!=\",\"_code_position\":"
                    + "\"virtual jobject example.Target.lookup(jint):42\"}";
            write(results, "{\"event\":\"CONCOLIC_REGION_RESULT\","
                    + "\"activationId\":\"ACT.0\",\"regionId\":\"REGION.0\","
                    + "\"exitKind\":\"NORMAL\","
                    + "\"branchMappings\":[{\"conditionIndex\":2,"
                    + "\"condition\":" + mapped + "}],"
                    + "\"engineSummary\":{\"active\":true,"
                    + "\"pathCondition\":[" + semanticEvent + ","
                    + unmapped + "," + mapped + "]}}\n");

            ConcolicSummaryImporter.importSummaries(results, activations,
                    regions, output, diagnostics, root.resolve("cache"));

            JsonObject summary = JsonParser.parseString(new String(
                    Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                    .getAsJsonObject();
            assertEquals(2, summary.getAsJsonArray("pathCondition").size());
            JsonObject mapping = summary.getAsJsonArray("branchMappings")
                    .get(0).getAsJsonObject();
            assertEquals(1, mapping.get("conditionIndex").getAsInt());
            JsonObject filtered = summary.getAsJsonObject(
                    "pathConditionNormalization").getAsJsonArray(
                    "conditionIndexMap").get(1).getAsJsonObject();
            assertEquals("FILTERED", filtered.get("status").getAsString());
            assertEquals("BINARY_CONDITION_WITHOUT_INSTRUMENTED_BRANCH_MAPPING",
                    filtered.get("reason").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void outputClosureFailsClosedWithoutAnyBinaryBranchMapping()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(binaryCondition(
                    "virtual void example.Store.update():18", "!=",
                    map, constant("Y_L_NULL", "L")));
            path.add(methodExpression("java/util/HashMap put", 19,
                    symbolCopy(map), symbol("key", "I"),
                    symbol("value", "example/Value")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);

            assertTrue("the modeled heap effect remains complete",
                    imported.summary.getAsJsonObject("heapEffectModel")
                            .get("complete").getAsBoolean());
            assertFalse("an output relation cannot omit a symbolic branch",
                    imported.summary.get("relationallyComplete")
                            .getAsBoolean());
            JsonObject filtered = imported.summary.getAsJsonObject(
                    "pathConditionNormalization").getAsJsonArray(
                    "filteredConditions").get(0).getAsJsonObject();
            assertEquals(
                    "BINARY_CONDITION_WITHOUT_INSTRUMENTED_BRANCH_MAPPING",
                    filtered.get("reason").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsMapMutationsAsVersionedHeapEffects() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonObject key1 = symbol("key1", "I");
            JsonObject value1 = symbol("value1", "example/Value");
            JsonObject key2 = symbol("key2", "I");
            JsonObject source = symbol("sourceMap", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/Map put", 10,
                    symbolCopy(map), key1, value1));
            path.add(methodExpression("java/util/TreeMap remove", 11,
                    symbolCopy(map), key2));
            path.add(methodExpression(
                    "java/util/concurrent/ConcurrentHashMap clear", 12,
                    symbolCopy(map)));
            path.add(methodExpression("java/util/LinkedHashMap putAll", 13,
                    symbolCopy(map), source));

            Path root = folder.getRoot().toPath();
            MapFixture imported = importMapFixture(root, path);
            assertEquals("OUTPUT_CLOSURE", imported.summary
                    .getAsJsonObject("captureGoal").get("kind")
                    .getAsString());
            assertEquals("REGION.P.out.0", imported.summary.getAsJsonObject(
                    "requestedOutput").get("portId").getAsString());
            assertEquals("REGION.P@fixture#call10", imported.summary.get(
                    "regionInstanceId").getAsString());
            assertFalse(imported.summary.has(
                    "requestedOutputSliceComplete"));
            assertTrue(imported.summary.getAsJsonObject(
                    "requestedOutputSlice").get("complete").getAsBoolean());
            assertEquals("REGION.P.out.0", imported.summary.getAsJsonObject(
                    "requestedOutputSlice").get("outputPort").getAsString());
            assertEquals(1, imported.summary.getAsJsonArray(
                    "edgeBindings").size());
            JsonArray effects = imported.summary.getAsJsonArray("heapEffects");
            assertEquals(4, effects.size());
            assertEquals("MAP_PUT", effect(effects, 0, "kind"));
            assertEquals("MAP_REMOVE", effect(effects, 1, "kind"));
            assertEquals("MAP_CLEAR", effect(effects, 2, "kind"));
            assertEquals("MAP_PUT_ALL", effect(effects, 3, "kind"));

            JsonObject put = effects.get(0).getAsJsonObject();
            JsonObject remove = effects.get(1).getAsJsonObject();
            JsonObject clear = effects.get(2).getAsJsonObject();
            JsonObject putAll = effects.get(3).getAsJsonObject();
            assertEquals("REGION.P.in.0", put.get("inputPort").getAsString());
            assertEquals(put.get("outputPort").getAsString(),
                    remove.get("inputPort").getAsString());
            assertEquals(remove.get("outputPort").getAsString(),
                    clear.get("inputPort").getAsString());
            assertEquals(clear.get("outputPort").getAsString(),
                    putAll.get("inputPort").getAsString());
            assertEquals("REGION.P.out.0",
                    putAll.get("outputPort").getAsString());

            for (int index = 0; index < effects.size(); index++) {
                JsonObject item = effects.get(index).getAsJsonObject();
                assertEquals(index, item.get("rawConditionIndex").getAsInt());
                assertEquals(index,
                        item.get("normalizedConditionIndex").getAsInt());
                assertEquals(index,
                        item.get("stateOrdinalBefore").getAsInt());
                assertEquals(index + 1,
                        item.get("stateOrdinalAfter").getAsInt());
                assertEquals(1, item.get("occurrence").getAsInt());
                assertTrue(item.get("siteId").getAsString().contains(
                        "example.Store.update"));
                assertTrue(item.has("mapExpression"));
                assertTrue(item.has("resultExpression"));
            }
            assertEquals("key1", put.getAsJsonObject("keyExpression")
                    .get("_exp").getAsString());
            assertEquals("value1", put.getAsJsonObject("valueExpression")
                    .get("_exp").getAsString());
            assertEquals("key2", remove.getAsJsonObject("keyExpression")
                    .get("_exp").getAsString());
            assertEquals("sourceMap", putAll.getAsJsonObject("sourceExpression")
                    .get("_exp").getAsString());

            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(4, model.get("effectCount").getAsInt());
            assertEquals(1, model.get("mapStateFamilyCount").getAsInt());
            assertTrue(model.get("complete").getAsBoolean());
            assertTrue(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
            JsonObject output = imported.summary
                    .getAsJsonObject("outputExpressions")
                    .getAsJsonObject("REGION.P.out.0");
            assertEquals("HEAP_STATE_VERSION", output.get("kind").getAsString());
            assertEquals(putAll.get("postState").getAsString(),
                    output.get("stateId").getAsString());

            JsonObject incompleteActivation = JsonParser.parseString(new String(
                    Files.readAllBytes(root.resolve("activation.jsonl")),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            // A stale outer claim cannot override an incomplete inner slice.
            incompleteActivation.addProperty("requestedOutputSliceComplete",
                    true);
            incompleteActivation.getAsJsonObject("requestedOutputSlice")
                    .addProperty("complete", false);
            JsonObject fallback = new JsonObject();
            fallback.addProperty("symbol", "REGION.P.in.0");
            fallback.addProperty("bindingMode", "CONCRETE_PASSTHROUGH");
            fallback.addProperty("concreteFallback", true);
            JsonArray fallbacks = new JsonArray();
            fallbacks.add(fallback);
            incompleteActivation.add("concreteFallbacks", fallbacks);
            write(root.resolve("activation.jsonl"), incompleteActivation
                    + "\n");

            JsonObject incompleteRaw = JsonParser.parseString(new String(
                    Files.readAllBytes(root.resolve("results.jsonl")),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            incompleteRaw.add("symbolizedInputs", new JsonArray());
            JsonArray unresolved = new JsonArray();
            unresolved.add("REGION.P.in.0:concrete passthrough");
            incompleteRaw.add("unresolvedInputs", unresolved);
            write(root.resolve("results.jsonl"), incompleteRaw + "\n");

            Path incompleteOutput = root.resolve("incomplete-summaries.jsonl");
            Path incompleteDiagnostics = root.resolve(
                    "incomplete-diagnostics.jsonl");
            ConcolicSummaryImporter.importSummaries(
                    root.resolve("results.jsonl"),
                    root.resolve("activation.jsonl"), root.resolve(
                            "regions.jsonl"), incompleteOutput,
                    incompleteDiagnostics, root.resolve("incomplete-cache"));
            JsonObject incompleteSummary = JsonParser.parseString(new String(
                    Files.readAllBytes(incompleteOutput),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            assertFalse(incompleteSummary.has(
                    "requestedOutputSliceComplete"));
            assertFalse(incompleteSummary.getAsJsonObject(
                    "requestedOutputSlice").get("complete").getAsBoolean());
            assertFalse(incompleteSummary.get("relationallyComplete")
                    .getAsBoolean());

            incompleteActivation.remove("requestedOutputSlice");
            write(root.resolve("activation.jsonl"), incompleteActivation
                    + "\n");
            Path missingSliceOutput = root.resolve(
                    "missing-slice-summaries.jsonl");
            ConcolicSummaryImporter.importSummaries(
                    root.resolve("results.jsonl"),
                    root.resolve("activation.jsonl"), root.resolve(
                            "regions.jsonl"), missingSliceOutput,
                    root.resolve("missing-slice-diagnostics.jsonl"),
                    root.resolve("missing-slice-cache"));
            JsonObject missingSliceSummary = JsonParser.parseString(
                    new String(Files.readAllBytes(missingSliceOutput),
                            StandardCharsets.UTF_8).trim()).getAsJsonObject();
            assertFalse(missingSliceSummary.has(
                    "requestedOutputSliceComplete"));
            assertTrue(missingSliceSummary.getAsJsonObject(
                    "requestedOutputSlice").entrySet().isEmpty());
            assertFalse(missingSliceSummary.get("relationallyComplete")
                    .getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void iteratorRemoveCannotUseUniqueLibraryEffectFallback()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol("M_L'java/util/HashMap'_25",
                    "java/util/HashMap");
            JsonObject nativeRemove = methodExpression(
                    "java/util/HashMap remove", 42,
                    map, constant("Y_I_7", "I"),
                    symbol("key", "java/lang/Integer"),
                    constant("Y_Z_0", "Z"), constant("Y_Z_0", "Z"));
            MapFixture imported = importObservedMapMutationFixture(
                    folder.getRoot().toPath(), nativeRemove,
                    "<java.util.Iterator: void remove()>", false);

            JsonArray effects = imported.summary.getAsJsonArray("heapEffects");
            assertEquals(1, effects.size());
            JsonObject remove = effects.get(0).getAsJsonObject();
            assertEquals("MAP_REMOVE", remove.get("kind").getAsString());
            assertEquals("key", remove.getAsJsonObject("keyExpression")
                    .get("_exp").getAsString());
            assertEquals("JDK_HASHMAP_REMOVENODE_MATCH_VALUE_FALSE",
                    remove.get("parameterNormalization").getAsString());
            assertFalse(remove.has("valueExpression"));
            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(1, model.get("candidateMutationCount").getAsInt());
            assertEquals(0, model.get("unsupportedMutationCount").getAsInt());
            assertFalse(model.get("complete").getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "INCOMPLETE_ITERATOR_REMOVE_APPLICATION_PROVENANCE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void doesNotAdmitUnboundLibraryMapMutation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonArray path = new JsonArray();
            path.add(methodExpressionAt("java/util/HashMap put",
                    "java.util.HashMap.putVal()", 18,
                    symbol("foreignMap", "java/util/HashMap"),
                    symbol("key", "I"),
                    symbol("value", "example/Value")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);

            assertEquals(0, imported.summary.getAsJsonArray(
                    "pathCondition").size());
            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapEffects").size());
            JsonObject normalization = imported.summary.getAsJsonObject(
                    "pathConditionNormalization");
            assertEquals(1, normalization.get("filteredConditionCount")
                    .getAsInt());
            assertEquals("OUTSIDE_REGION_SEMANTIC_METHOD_BOUNDARY",
                    normalization.getAsJsonArray("conditionIndexMap").get(0)
                            .getAsJsonObject().get("reason").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void directMapRemoveRetainsExactLibraryTransformerCoverage()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol("M_L'java/util/HashMap'_25",
                    "java/util/HashMap");
            JsonObject key = symbol("expiredKey", "java/lang/Integer");
            JsonObject directRemove = methodExpression(
                    "java/util/HashMap remove", 42, map, key);
            MapFixture imported = importObservedMapMutationFixture(
                    folder.getRoot().toPath(), directRemove,
                    "<java.util.Map: java.lang.Object remove("
                            + "java.lang.Object)>", false);

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
            assertEquals("MAP_REMOVE", imported.summary.getAsJsonArray(
                    "heapEffects").get(0).getAsJsonObject().get("kind")
                    .getAsString());
            JsonObject coverage = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals(1, coverage.get(
                    "statePortMatchedTransformerCount").getAsInt());
            assertTrue(coverage.get("complete").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactLibraryFallbackRequiresUniqueNonemptyInvoke()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject directRemove = methodExpression(
                    "java/util/HashMap remove", 42,
                    symbol("M_L'java/util/HashMap'_25",
                            "java/util/HashMap"),
                    symbol("expiredKey", "java/lang/Integer"));
            MapFixture missing = importObservedMapMutationFixture(
                    folder.getRoot().toPath().resolve("missing"),
                    directRemove, null, false);
            MapFixture duplicate = importObservedMapMutationFixture(
                    folder.getRoot().toPath().resolve("duplicate"),
                    directRemove,
                    "<java.util.Map: java.lang.Object remove("
                            + "java.lang.Object)>", true);

            for (MapFixture imported : new MapFixture[]{missing, duplicate}) {
                assertFalse(imported.summary.get("relationallyComplete")
                        .getAsBoolean());
                assertTrue(imported.diagnostics,
                        imported.diagnostics.contains(
                                "UNRESOLVED_REQUESTED_HEAP_EFFECT_PROVENANCE"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactContractDoesNotPromotePathOnlyHeapEffectToEvidence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            ExactTransformerFixture fixture = exactTransformerFixture(
                    new JsonArray());
            JsonObject mapBinding = transformerInputBinding(
                    "REGION.P.in.0", fixture.outputCell,
                    strings(fixture.updateSite, fixture.pruneSite),
                    new JsonArray());
            // A mutable heap prestate is globally required.  It is observed in
            // this fixture, so it must not be classified path-inactive.
            mapBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            fixture.sliceMetadata.add("inputBindings",
                    stringsAsObjects(mapBinding));
            addHeapEffectCaptureDischarge(fixture.sliceMetadata,
                    fixture.outputCell, "REGION.P.in.0");

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), fixture.path, true,
                    new JsonArray(), fixture.methods, fixture.causalEdges,
                    null, new JsonArray(), fixture.branchMappings,
                    null, null, fixture.sliceMetadata, new JsonArray());

            JsonObject coverage = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals("EXACT_REQUESTED_STATE_TRANSFORMER_"
                            + "RUNTIME_PATH_COVERAGE_V5",
                    coverage.get("policy").getAsString());
            assertTrue(coverage.get(
                    "exactRequestedStateTransformerContract").getAsBoolean());
            assertTrue(coverage.get(
                    "requestedStateTransformerContractValid").getAsBoolean());
            assertEquals(2, coverage.get("declaredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("coveredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("uncoveredWriteSiteCount").getAsInt());
            assertEquals(0, coverage.get("edgeFreeVoidMethodCount").getAsInt());
            assertEquals(1, coverage.get("guardExcludedWriteSiteCount")
                    .getAsInt());
            assertEquals(0, coverage.get("statePortMatchedTransformerCount")
                    .getAsInt());
            assertFalse(coverage.get("complete").getAsBoolean());
            assertEquals("HEAP_EFFECT_STATE_TRANSFORMER",
                    imported.summary.getAsJsonObject(
                            "requestedOutputSlice").get(
                            "captureDischargeAuthority").getAsString());
            assertFalse(coverage.toString().contains("DF.WRITE.OTHER"));
            assertFalse(coverage.toString().contains(fixture.wrapper));
            assertTrue(coverage.toString().contains(
                    fixture.outerGuardSite));
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNOBSERVED_DECLARED_HEAP_WRITE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactContractRequiresOrderedFourPutBijection()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture valid = importOrderedPutFixture(
                    folder.getRoot().toPath().resolve("valid"), "VALID");
            assertTrue(valid.diagnostics,
                    valid.summary.get("relationallyComplete").getAsBoolean());
            assertEquals(0, valid.diagnostics.trim().length());
            JsonObject coverage = valid.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals(4, coverage.get("declaredWriteSiteCount")
                    .getAsInt());
            assertEquals(4, coverage.get("coveredWriteSiteCount")
                    .getAsInt());
            assertEquals(0, coverage.get("uncoveredWriteSiteCount")
                    .getAsInt());
            assertEquals(4, coverage.get(
                    "statePortMatchedTransformerCount").getAsInt());
            int orderedMatches = 0;
            for (JsonElement element : coverage.getAsJsonArray("matches")) {
                if ("RUNTIME_ORDERED_MAP_PUT_TO_EXACT_STATIC_WRITE_AND_"
                        .concat("CONTAINER_ELEMENT_FIELD_V1").equals(
                                element.getAsJsonObject().get("authority")
                                        .getAsString())) {
                    orderedMatches++;
                }
            }
            assertEquals(4, orderedMatches);

            String[] failures = new String[]{"CARDINALITY", "ORDER", "KEY",
                    "LOAD", "PORT", "TOKEN"};
            for (String failure : failures) {
                MapFixture rejected = importOrderedPutFixture(
                        folder.getRoot().toPath().resolve(
                                failure.toLowerCase(java.util.Locale.ROOT)),
                        failure);
                assertFalse(failure + ": " + rejected.diagnostics,
                        rejected.summary.get("relationallyComplete")
                                .getAsBoolean());
                assertTrue(failure + ": " + rejected.diagnostics,
                        rejected.diagnostics.contains(
                                "EXACT_ORDERED_MAP_PUT_BIJECTION_FAILED"));
                JsonObject rejectedCoverage = rejected.summary
                        .getAsJsonObject("heapEffectModel").getAsJsonObject(
                                "staticTransformerCoverage");
                assertEquals(failure, 0, rejectedCoverage.get(
                        "statePortMatchedTransformerCount").getAsInt());
                assertEquals(failure, 4, rejectedCoverage.get(
                        "uncoveredWriteSiteCount").getAsInt());
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void heapEffectCaptureDischargeRequiresExactSameCellBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            ExactTransformerFixture fixture = exactTransformerFixture(
                    new JsonArray());
            JsonObject mapBinding = transformerInputBinding(
                    "REGION.P.in.0", fixture.outputCell,
                    strings(fixture.updateSite, fixture.pruneSite),
                    new JsonArray());
            mapBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            fixture.sliceMetadata.add("inputBindings",
                    stringsAsObjects(mapBinding));
            addHeapEffectCaptureDischarge(fixture.sliceMetadata,
                    fixture.outputCell, "REGION.P.in.missing");

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), fixture.path, true,
                    new JsonArray(), fixture.methods, fixture.causalEdges,
                    null, new JsonArray(), fixture.branchMappings,
                    null, null, fixture.sliceMetadata, new JsonArray());

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "INVALID_HEAP_EFFECT_CAPTURE_DISCHARGE"));
            assertTrue(imported.diagnostics.contains(
                    "EXACT_SAME_CELL_HEAP_STATE_BINDING_COUNT=0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void heapEffectCaptureDischargeRejectsNonMapStateCell()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            ExactTransformerFixture fixture = exactTransformerFixture(
                    new JsonArray());
            String listCell = "<example.Store: java.util.List data>";
            JsonArray obligations = fixture.sliceMetadata.getAsJsonArray(
                    "requestedStateTransformerObligations");
            for (JsonElement element : obligations) {
                element.getAsJsonObject().addProperty("targetCell",
                        listCell);
            }
            fixture.sliceMetadata.addProperty(
                    "requestedStateTransformerContractOutputCell",
                    listCell);
            JsonObject listBinding = transformerInputBinding(
                    "REGION.P.in.0", listCell,
                    strings(fixture.updateSite, fixture.pruneSite),
                    new JsonArray());
            listBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            fixture.sliceMetadata.add("inputBindings",
                    stringsAsObjects(listBinding));
            addHeapEffectCaptureDischarge(fixture.sliceMetadata,
                    listCell, "REGION.P.in.0");

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), fixture.path, true,
                    new JsonArray(), fixture.methods, fixture.causalEdges,
                    null, new JsonArray(), fixture.branchMappings,
                    null, null, fixture.sliceMetadata, new JsonArray());

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "INVALID_HEAP_EFFECT_CAPTURE_DISCHARGE"));
            assertTrue(imported.diagnostics.contains(
                    "MALFORMED_HEAP_EFFECT_CAPTURE_DISCHARGE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void heapEffectCaptureDischargeDoesNotMaskUnsupportedEffect()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            ExactTransformerFixture fixture = exactTransformerFixture(
                    new JsonArray());
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            fixture.path.add(methodExpression(
                    "java/util/HashMap putIfAbsent", 20,
                    symbolCopy(map), symbol("unsupportedKey", "I"),
                    symbol("unsupportedValue", "example/Value")));
            JsonObject mapBinding = transformerInputBinding(
                    "REGION.P.in.0", fixture.outputCell,
                    strings(fixture.updateSite, fixture.pruneSite),
                    new JsonArray());
            mapBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            fixture.sliceMetadata.add("inputBindings",
                    stringsAsObjects(mapBinding));
            addHeapEffectCaptureDischarge(fixture.sliceMetadata,
                    fixture.outputCell, "REGION.P.in.0");

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), fixture.path, true,
                    new JsonArray(), fixture.methods, fixture.causalEdges,
                    null, new JsonArray(), fixture.branchMappings,
                    null, null, fixture.sliceMetadata, new JsonArray());

            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(1, model.get("unsupportedMutationCount")
                    .getAsInt());
            assertFalse(model.get("complete").getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNSUPPORTED_MAP_MUTATION_OPERATION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactGuardCoverageFailsClosedWhenMissingOrOverridden()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            ExactTransformerFixture missing = exactTransformerFixture(
                    new JsonArray());
            JsonObject mapBinding = transformerInputBinding(
                    "REGION.P.in.0", missing.outputCell,
                    strings(missing.updateSite, missing.pruneSite),
                    new JsonArray());
            mapBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            missing.sliceMetadata.add("inputBindings",
                    stringsAsObjects(mapBinding));
            addHeapEffectCaptureDischarge(missing.sliceMetadata,
                    missing.outputCell, "REGION.P.in.0");
            MapFixture missingGuard = importMapFixture(
                    folder.getRoot().toPath().resolve("missing"),
                    missing.path, true, new JsonArray(), missing.methods,
                    missing.causalEdges, null, new JsonArray(),
                    new JsonArray(), null, null, missing.sliceMetadata,
                    new JsonArray());
            JsonObject missingCoverage = missingGuard.summary
                    .getAsJsonObject("heapEffectModel").getAsJsonObject(
                            "staticTransformerCoverage");
            assertEquals(0, missingCoverage.get(
                    "guardExcludedWriteSiteCount").getAsInt());
            assertFalse(missingCoverage.get("complete").getAsBoolean());
            assertFalse(missingGuard.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(missingGuard.diagnostics.contains(
                    "UNOBSERVED_DECLARED_HEAP_WRITE"));

            ExactTransformerFixture overridden = exactTransformerFixture(
                    new JsonArray());
            JsonObject overriddenBinding = transformerInputBinding(
                    "REGION.P.in.0", overridden.outputCell,
                    strings(overridden.updateSite, overridden.pruneSite),
                    new JsonArray());
            overriddenBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            overridden.sliceMetadata.add("inputBindings",
                    stringsAsObjects(overriddenBinding));
            overridden.branchMappings.get(0).getAsJsonObject().addProperty(
                    "overrideApplied", true);
            MapFixture forced = importMapFixture(
                    folder.getRoot().toPath().resolve("overridden"),
                    overridden.path, true, new JsonArray(),
                    overridden.methods, overridden.causalEdges, null,
                    new JsonArray(), overridden.branchMappings, null, null,
                    overridden.sliceMetadata, new JsonArray());
            assertEquals(0, forced.summary.size());
            assertTrue(forced.diagnostics.contains("BRANCH_OVERRIDE_USED"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void deactivatesOnlyMissingInputWhoseCompleteSinksAreExcluded()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            ExactTransformerFixture fixture = exactTransformerFixture(
                    new JsonArray());
            String keyPort = "REGION.12.in.26";
            String expiryPort = "REGION.12.in.27";
            JsonArray bindings = new JsonArray();
            JsonObject mapBinding = transformerInputBinding(
                    "REGION.P.in.0", fixture.outputCell,
                    strings(fixture.updateSite, fixture.pruneSite),
                    new JsonArray());
            mapBinding.addProperty(
                    "requestedStateTransformerSinkExclusive", false);
            bindings.add(mapBinding);
            bindings.add(transformerInputBinding(keyPort,
                    "<example.Key: int keyId>",
                    strings(fixture.updateSite), new JsonArray()));
            bindings.add(transformerInputBinding(expiryPort,
                    "<example.Key: long expiry>",
                    strings(fixture.pruneSite),
                    strings(fixture.innerGuardSite)));
            fixture.sliceMetadata.add("inputBindings", bindings);

            JsonArray additional = new JsonArray();
            additional.add(fieldAccessAction(keyPort, "keyId"));
            additional.add(fieldAccessAction(expiryPort, "expiry"));
            MapFixture inactiveExpiry = importMapFixture(
                    folder.getRoot().toPath().resolve("expiry-inactive"),
                    fixture.path, true, new JsonArray(), fixture.methods,
                    fixture.causalEdges, null, additional,
                    fixture.branchMappings, null, null,
                    fixture.sliceMetadata, strings(expiryPort));

            JsonObject admission = inactiveExpiry.summary.getAsJsonObject(
                    "inputMaterializationAdmission");
            assertTrue(admission.get("complete").getAsBoolean());
            assertTrue(containsString(admission.getAsJsonArray(
                    "globalSliceInputs"), expiryPort));
            assertFalse(containsString(admission.getAsJsonArray(
                    "requiredSliceInputs"), expiryPort));
            assertTrue(containsString(admission.getAsJsonArray(
                    "pathInactiveSliceInputs"), expiryPort));
            assertEquals(1, admission.getAsJsonArray("pathInactiveProofs")
                    .size());
            JsonObject proof = admission.getAsJsonArray(
                    "pathInactiveProofs").get(0).getAsJsonObject();
            assertEquals(expiryPort, proof.get("inputPort").getAsString());
            assertTrue(proof.toString().contains(fixture.pruneSite));
            assertTrue(proof.toString().contains(fixture.outerGuardSite));
            assertTrue(proof.toString().contains(fixture.innerGuardSite));
            assertFalse(inactiveExpiry.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(inactiveExpiry.diagnostics.contains(
                    "UNOBSERVED_DECLARED_HEAP_WRITE"));

            MapFixture missingKey = importMapFixture(
                    folder.getRoot().toPath().resolve("key-required"),
                    fixture.path, true, new JsonArray(), fixture.methods,
                    fixture.causalEdges, null, additional,
                    fixture.branchMappings, null, null,
                    fixture.sliceMetadata, strings(keyPort, expiryPort));
            JsonObject keyAdmission = missingKey.summary.getAsJsonObject(
                    "inputMaterializationAdmission");
            assertFalse(keyAdmission.get("complete").getAsBoolean());
            assertTrue(containsString(keyAdmission.getAsJsonArray(
                    "requiredSliceInputs"), keyPort));
            assertTrue(containsString(keyAdmission.getAsJsonArray(
                    "pathInactiveSliceInputs"), expiryPort));
            assertFalse(missingKey.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(missingKey.diagnostics.contains(
                    "SLICE_INPUT_NOT_SYMBOLIZED:" + keyPort));
            assertFalse(missingKey.diagnostics.contains(
                    "SLICE_INPUT_NOT_SYMBOLIZED:" + expiryPort));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void coversUnobservedWriteWhenDominatingGuardIsAlwaysOpposite()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 19,
                    symbolCopy(map), symbol("putKey", "I"),
                    symbol("putValue", "example/Value")));
            String update = "<example.Store: void update()>";
            String prune = "<example.Store: void prune()>";
            JsonArray methods = new JsonArray();
            methods.add(update);
            methods.add(prune);
            JsonArray causalEdges = new JsonArray();
            causalEdges.add(causalEdge("DF.WRITE.1", update,
                    update + "#u1", "HEAP_WRITE", "field_mutation"));
            causalEdges.add(causalEdge("DF.WRITE.2", prune,
                    prune + "#u5", "HEAP_WRITE", "field_mutation"));
            causalEdges.add(guardedMutationEdge("DF.GUARD.2", prune,
                    4, 5, false));
            JsonArray branchMappings = new JsonArray();
            branchMappings.add(branchMapping(prune, 4, 1, true,
                    symbol("M_J_field_REGION.P.in.1_expiry", "J")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, true, new JsonArray(),
                    methods, causalEdges, new JsonArray(),
                    branchMappings, null);

            JsonObject coverage = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals(2, coverage.get("declaredWriteSiteCount").getAsInt());
            assertEquals(2, coverage.get("coveredWriteSiteCount").getAsInt());
            assertEquals(0, coverage.get("uncoveredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("guardExcludedWriteSiteCount")
                    .getAsInt());
            JsonObject guardMatch = coverage.getAsJsonArray("matches").get(0)
                    .getAsJsonObject();
            assertEquals("RUNTIME_OBSERVED_DOMINATING_GUARD_EXCLUDES_WRITE",
                    guardMatch.get("authority").getAsString());
            assertEquals(prune + "#u4",
                    guardMatch.get("guardSiteId").getAsString());
            assertFalse(guardMatch.get("requiredOutcome").getAsBoolean());
            assertTrue(guardMatch.get("observedOutcome").getAsBoolean());
            assertTrue(coverage.get("complete").getAsBoolean());
            assertTrue(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void doesNotExcludeWriteWhenRequiredGuardOutcomeWasObserved()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 19,
                    symbolCopy(map), symbol("putKey", "I"),
                    symbol("putValue", "example/Value")));
            String update = "<example.Store: void update()>";
            String prune = "<example.Store: void prune()>";
            JsonArray methods = new JsonArray();
            methods.add(update);
            methods.add(prune);
            JsonArray causalEdges = new JsonArray();
            causalEdges.add(causalEdge("DF.WRITE.1", update,
                    update + "#u1", "HEAP_WRITE", "field_mutation"));
            causalEdges.add(causalEdge("DF.WRITE.2", prune,
                    prune + "#u5", "HEAP_WRITE", "field_mutation"));
            causalEdges.add(guardedMutationEdge("DF.GUARD.2", prune,
                    4, 5, false));
            JsonArray branchMappings = new JsonArray();
            branchMappings.add(branchMapping(prune, 4, 1, false,
                    symbol("M_J_field_REGION.P.in.1_expiry", "J")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, true, new JsonArray(),
                    methods, causalEdges, new JsonArray(),
                    branchMappings, null);

            JsonObject coverage = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals(0, coverage.get("guardExcludedWriteSiteCount")
                    .getAsInt());
            assertEquals(1, coverage.get("uncoveredWriteSiteCount").getAsInt());
            assertFalse(coverage.get("complete").getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNOBSERVED_DECLARED_HEAP_WRITE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void doesNotExcludeWriteWithoutRuntimeGuardObservation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 19,
                    symbolCopy(map), symbol("putKey", "I"),
                    symbol("putValue", "example/Value")));
            String update = "<example.Store: void update()>";
            String prune = "<example.Store: void prune()>";
            JsonArray methods = new JsonArray();
            methods.add(update);
            methods.add(prune);
            JsonArray causalEdges = new JsonArray();
            causalEdges.add(causalEdge("DF.WRITE.1", update,
                    update + "#u1", "HEAP_WRITE", "field_mutation"));
            causalEdges.add(causalEdge("DF.WRITE.2", prune,
                    prune + "#u5", "HEAP_WRITE", "field_mutation"));
            causalEdges.add(guardedMutationEdge("DF.GUARD.2", prune,
                    4, 5, false));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, true, new JsonArray(),
                    methods, causalEdges, new JsonArray(),
                    new JsonArray(), null);

            JsonObject coverage = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals(0, coverage.get("guardExcludedWriteSiteCount")
                    .getAsInt());
            assertEquals(1, coverage.get("uncoveredWriteSiteCount").getAsInt());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNOBSERVED_DECLARED_HEAP_WRITE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void validHashMapRemoveNodeRetainsExactLibraryCoverage()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol("M_L'java/util/HashMap'_25",
                    "java/util/HashMap");
            JsonObject key = symbol("expiredKey", "java/lang/Integer");
            JsonObject nativeRemove = methodExpression(
                    "java/util/HashMap remove",
                    42, map, constant("Y_I_7", "I"), key,
                    constant("Y_Z_0", "Z"),
                    constant("Y_Z_0", "Z"));
            MapFixture imported = importObservedMapMutationFixture(
                    folder.getRoot().toPath(), nativeRemove,
                    "<java.util.HashMap: java.lang.Object removeNode(int,"
                            + "java.lang.Object,java.lang.Object,boolean,"
                            + "boolean)>", false);

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
            JsonObject effect = imported.summary.getAsJsonArray(
                    "heapEffects").get(0).getAsJsonObject();
            assertEquals("MAP_REMOVE", effect.get("kind").getAsString());
            assertEquals("JDK_HASHMAP_REMOVENODE_MATCH_VALUE_FALSE",
                    effect.get("parameterNormalization").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsConditionalOrUnknownHashMapRemoveShapes()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpressionAt("java/util/HashMap remove",
                    "java.util.HashMap$HashIterator.remove()", 15,
                    symbolCopy(map), constant("Y_I_1", "I"),
                    symbol("key1", "java/lang/Integer"),
                    constant("Y_Z_1", "Z"), constant("Y_Z_0", "Z")));
            path.add(methodExpressionAt("java/util/HashMap remove",
                    "java.util.HashMap$HashIterator.remove()", 16,
                    symbolCopy(map), constant("Y_I_2", "I"),
                    symbol("key2", "java/lang/Integer"),
                    symbol("M_Z_matchValue", "Z"),
                    constant("Y_Z_0", "Z")));
            // Public Map.remove(key, value) remains conditional and must not
            // be confused with the five-parameter removeNode export.
            path.add(methodExpression("java/util/HashMap remove", 17,
                    symbolCopy(map), symbol("key3", "I"),
                    symbol("value3", "example/Value")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);

            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapEffects").size());
            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(3, model.get("candidateMutationCount").getAsInt());
            assertEquals(3, model.get("unsupportedMutationCount").getAsInt());
            assertEquals(0, model.get("malformedMutationCount").getAsInt());
            assertFalse(model.get("complete").getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNSUPPORTED_MAP_MUTATION_OPERATION"));
            assertTrue(imported.diagnostics.contains(
                    "conditional-internal-removeNode"));
            assertTrue(imported.diagnostics.contains(
                    "java/util/HashMap remove/conditional"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void preservesRepeatedMutationEventsAcrossPathDeduplication()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject mutation = methodExpression("java/util/HashMap put", 10,
                    symbol("M_L_field_REGION.P.in.0_example/Store", "L"),
                    symbol("key", "I"), symbol("value", "example/Value"));
            JsonArray path = new JsonArray();
            path.add(mutation);
            path.add(mutation.deepCopy());

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);
            assertEquals(1, imported.summary.getAsJsonArray(
                    "pathCondition").size());
            JsonArray effects = imported.summary.getAsJsonArray("heapEffects");
            assertEquals(2, effects.size());
            assertEquals(0, effects.get(0).getAsJsonObject()
                    .get("rawConditionIndex").getAsInt());
            assertEquals(1, effects.get(1).getAsJsonObject()
                    .get("rawConditionIndex").getAsInt());
            assertEquals(0, effects.get(1).getAsJsonObject()
                    .get("normalizedConditionIndex").getAsInt());
            assertEquals(1, effects.get(0).getAsJsonObject()
                    .get("occurrence").getAsInt());
            assertEquals(2, effects.get(1).getAsJsonObject()
                    .get("occurrence").getAsInt());
            assertEquals(effects.get(0).getAsJsonObject()
                            .get("outputPort").getAsString(),
                    effects.get(1).getAsJsonObject()
                            .get("inputPort").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void failsClosedForDeclaredVoidHeapTransformerWithoutEvidence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 10,
                    symbol("M_L_field_REGION.P.in.0_example/Store", "L"),
                    symbol("key", "I"),
                    symbol("value", "example/Value")));

            JsonArray methods = new JsonArray();
            methods.add("<example.Store: void update()>");
            methods.add("<example.Store: void prune()>");
            // A pure accessor with no causal edge is not itself asserted to be
            // a heap transformer by the fail-closed contract.
            methods.add("<example.Store: example.Value lookup()>");
            JsonArray causalEdges = new JsonArray();
            causalEdges.add(causalEdge("DF.WRITE.1",
                    "<example.Store: void update()>",
                    "<example.Store: void update()>#u1", "HEAP_WRITE",
                    "field_mutation"));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, true, new JsonArray(),
                    methods, causalEdges);

            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            JsonObject coverage = model.getAsJsonObject(
                    "staticTransformerCoverage");
            assertTrue(coverage.get("applicable").getAsBoolean());
            assertEquals(1, coverage.get("declaredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("coveredWriteSiteCount").getAsInt());
            assertEquals(0, coverage.get("uncoveredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("edgeFreeVoidMethodCount").getAsInt());
            assertFalse(coverage.get("complete").getAsBoolean());
            assertFalse(model.get("complete").getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNMODELED_DECLARED_HEAP_TRANSFORMER"));
            assertTrue(imported.diagnostics.contains(
                    "<example.Store: void prune()>"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void failsClosedWhenStaticHeapWriteCountExceedsRuntimeEffects()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 10,
                    symbol("M_L_field_REGION.P.in.0_example/Store", "L"),
                    symbol("key", "I"),
                    symbol("value", "example/Value")));
            JsonArray methods = new JsonArray();
            methods.add("<example.Store: void update()>");
            JsonArray causalEdges = new JsonArray();
            causalEdges.add(causalEdge("DF.WRITE.1",
                    "<example.Store: void update()>",
                    "<example.Store: void update()>#u1", "HEAP_WRITE",
                    "field_mutation"));
            causalEdges.add(causalEdge("DF.WRITE.2",
                    "<example.Store: void update()>",
                    "<example.Store: void update()>#u2", "HEAP_WRITE",
                    "field_mutation"));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, true, new JsonArray(),
                    methods, causalEdges);

            JsonObject coverage = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "staticTransformerCoverage");
            assertEquals(2, coverage.get("declaredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("coveredWriteSiteCount").getAsInt());
            assertEquals(1, coverage.get("uncoveredWriteSiteCount").getAsInt());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNOBSERVED_DECLARED_HEAP_WRITE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void outputClosureAdmitsOnlyRequestedOutputSliceMethods()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/Map put", 10,
                    symbolCopy(map), symbol("key1", "I"),
                    symbol("value1", "example/Value")));
            path.add(methodExpressionAt("java/util/Map put",
                    "example.Unrelated.touch()", 20, symbolCopy(map),
                    symbol("key2", "I"),
                    symbol("value2", "example/Value")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);
            assertEquals(1, imported.summary.getAsJsonArray(
                    "pathCondition").size());
            assertEquals(1, imported.summary.getAsJsonArray(
                    "heapEffects").size());
            JsonObject normalization = imported.summary.getAsJsonObject(
                    "pathConditionNormalization");
            assertEquals("REQUESTED_OUTPUT_SLICE_METHOD",
                    normalization.get("policy").getAsString());
            assertEquals(1, normalization.get("filteredConditionCount")
                    .getAsInt());
            assertTrue(imported.diagnostics.contains(
                    "FILTERED_NON_SEMANTIC_PATH_CONDITIONS"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void diagnosesUnsupportedAndMalformedMapMutations()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap putIfAbsent", 20,
                    symbolCopy(map), symbol("key", "I"),
                    symbol("value", "example/Value")));
            path.add(methodExpression("java/util/HashMap put", 21,
                    symbolCopy(map), symbol("missingValue", "I")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);
            assertEquals(0, imported.summary.getAsJsonArray("heapEffects").size());
            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(1, model.get("unsupportedMutationCount").getAsInt());
            assertEquals(1, model.get("malformedMutationCount").getAsInt());
            assertTrue(!model.get("complete").getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNSUPPORTED_MAP_MUTATION_OPERATION"));
            assertTrue(imported.diagnostics.contains(
                    "MALFORMED_MAP_MUTATION_EXPRESSION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void bindsFreshDefaultConstructedMapToEmptyInitialState()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 30,
                    symbol("freshMap", "java/util/HashMap"),
                    symbol("key", "I"), symbol("value", "example/Value")));
            JsonArray initializers = new JsonArray();
            initializers.add(freshMapInitializer("STATIC_INIT.REGION.P.0"));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, false, initializers);

            assertTrue(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(0, model.get("syntheticInputCount").getAsInt());
            assertEquals(1, model.get("initializedInputCount").getAsInt());
            assertEquals(1, model.get("initializerCount").getAsInt());

            JsonObject initializer = imported.summary.getAsJsonArray(
                    "heapStateInitializers").get(0).getAsJsonObject();
            assertEquals("MAP_EMPTY", initializer.get("kind").getAsString());
            assertEquals("REGION.P.state.heapMap0.empty",
                    initializer.get("statePort").getAsString());
            assertEquals("REGION.P.out.0",
                    initializer.get("requestedOutputPort").getAsString());
            assertEquals("JAVA_PLATFORM_DEFAULT_MAP_CONSTRUCTOR_SEMANTICS",
                    initializer.get("emptyStateAuthority").getAsString());

            JsonObject effect = imported.summary.getAsJsonArray("heapEffects")
                    .get(0).getAsJsonObject();
            assertEquals("STATIC_FRESH_EMPTY_MAP",
                    effect.get("inputBinding").getAsString());
            assertEquals(initializer.get("statePort").getAsString(),
                    effect.get("inputPort").getAsString());
            assertEquals("REGION.P.out.0",
                    effect.get("outputPort").getAsString());
            assertEquals("STATIC_FRESH_ALLOCATION_TO_REQUESTED_OUTPUT",
                    effect.get("outputBinding").getAsString());

            MapFixture observed = importObservedMapStateFixture(
                    folder.getRoot().toPath().resolve("observed"), true,
                    true);
            assertTrue(observed.diagnostics, observed.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals("[\"REGION.P.in.0\",\"REGION.P.in.1\"]",
                    observed.summary.getAsJsonObject(
                            "inputMaterializationAdmission")
                            .getAsJsonArray("admittedObservedInputs")
                            .toString());
            assertEquals(1, observed.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "runtimeHeapObservationImport").get(
                    "mapStateInputObservationCount").getAsInt());
            assertEquals("REGION.P.in.0", observed.summary
                    .getAsJsonArray("finiteMapSnapshots").get(0)
                    .getAsJsonObject().get("statePort").getAsString());
            assertEquals("REGION.P.in.0", observed.summary
                    .getAsJsonArray("heapEffects").get(0).getAsJsonObject()
                    .get("inputPort").getAsString());
            assertEquals("REGION.P.out.0", observed.summary
                    .getAsJsonArray("heapEffects").get(0).getAsJsonObject()
                    .get("outputPort").getAsString());

            MapFixture badIdentity = importObservedMapStateFixture(
                    folder.getRoot().toPath().resolve("bad-identity"),
                    false, true);
            MapFixture badSnapshot = importObservedMapStateFixture(
                    folder.getRoot().toPath().resolve("bad-snapshot"),
                    true, false);
            assertFalse(badIdentity.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertFalse(badSnapshot.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(badIdentity.diagnostics.contains(
                    "INCOMPLETE_RUNTIME_MAP_STATE_INPUT_OBSERVATION"));
            assertTrue(badSnapshot.diagnostics.contains(
                    "INCOMPLETE_RUNTIME_MAP_STATE_INPUT_OBSERVATION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsAmbiguousFreshMapAllocationEvidence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/HashMap put", 31,
                    symbol("freshMap", "java/util/HashMap"),
                    symbol("key", "I"), symbol("value", "example/Value")));
            JsonArray initializers = new JsonArray();
            initializers.add(freshMapInitializer("STATIC_INIT.REGION.P.0"));
            initializers.add(freshMapInitializer("STATIC_INIT.REGION.P.1"));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path, false, initializers);

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapStateInitializers").size());
            assertTrue(imported.diagnostics.contains(
                    "AMBIGUOUS_MAP_ALLOCATION_INITIALIZER"));
            assertTrue(imported.diagnostics.contains(
                    "UNBOUND_MAP_PRE_STATE_PORT"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsGuardExcludedNoRemoveAsMapIdentityWithEntryRead()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = mapInputExpression();
            JsonObject key = symbol("entryKey", "I");
            JsonArray observations = new JsonArray();
            observations.add(runtimeMapEntryRead(map, key,
                    "<example.Store: void prune()>", 3, 0, 1, 1));

            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations,
                    defaultReadSymbolize(), tokenFieldObservations(103));

            assertTrue(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
            JsonArray effects = imported.summary.getAsJsonArray(
                    "heapEffects");
            assertEquals(1, effects.size());
            JsonObject identity = effects.get(0).getAsJsonObject();
            assertEquals("MAP_IDENTITY", identity.get("kind").getAsString());
            assertEquals("REGION.P.in.0",
                    identity.get("inputPort").getAsString());
            assertEquals("REGION.P.out.0",
                    identity.get("outputPort").getAsString());
            assertEquals("MAP_STATE.REGION.P.0",
                    identity.get("stateFamily").getAsString());
            assertEquals(0, identity.get("stateOrdinalBefore").getAsInt());
            assertEquals(1, identity.get("stateOrdinalAfter").getAsInt());

            JsonArray importedObservations = imported.summary.getAsJsonArray(
                    "heapObservations");
            assertEquals(1, importedObservations.size());
            JsonObject observation = importedObservations.get(0)
                    .getAsJsonObject();
            assertEquals("MAP_ENTRY_READ",
                    observation.get("kind").getAsString());
            assertEquals("REGION.P.in.0",
                    observation.get("statePort").getAsString());
            assertEquals("EXACT_ACTIVATION_MAP_INPUT_EXPRESSION",
                    observation.get("stateBindingAuthority").getAsString());
            assertTrue(observation.get("entryValueFieldBindingComplete")
                    .getAsBoolean());
            assertTrue(observation.get("complete").getAsBoolean());
            JsonObject binding = observation.getAsJsonArray(
                    "entryFieldBindings").get(0).getAsJsonObject();
            assertEquals("REGION.P.in.1",
                    binding.get("baseInputSymbol").getAsString());
            assertTrue(binding.get("dynamicFieldSymbol").getAsString()
                    .startsWith("REGION.P.in.1.field."));
            assertEquals("<example.Value: long expiry>",
                    binding.get("fieldSignature").getAsString());
            assertEquals("long", binding.get("fieldJavaType").getAsString());
            assertEquals("RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_"
                            + "AND_ENTRY_VALUE_TOKEN_JOIN",
                    binding.get("authority").getAsString());

            JsonObject model = imported.summary.getAsJsonObject(
                    "heapEffectModel");
            assertEquals(1, model.get("identityEffectCount").getAsInt());
            assertEquals(1, model.get("observationCount").getAsInt());
            assertTrue(model.getAsJsonObject("runtimeHeapObservationImport")
                    .get("complete").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void validatesFiniteMapSnapshotBesideItsExactFirstEntryRead()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String method = "<example.Store: void prune()>";
            JsonObject map = mapInputExpression();
            JsonObject key = constant("Y_I_7", "java/lang/Integer");
            JsonObject read = runtimeMapEntryRead(map, key, method, 3,
                    0, 1, 1);
            JsonArray observations = new JsonArray();
            observations.add(read);
            observations.add(runtimeFiniteMapEntrySnapshot(map, key,
                    method, 3, 1, 1));

            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations,
                    defaultReadSymbolize(), tokenFieldObservations(103));

            assertTrue(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            JsonObject admission = imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "runtimeHeapObservationImport");
            assertTrue(admission.get("complete").getAsBoolean());
            assertEquals(2, admission.get("recordCount").getAsInt());
            assertEquals(2, admission.get("validatedCount").getAsInt());
            assertEquals(1, admission.get("mapEntryReadCount").getAsInt());
            assertEquals(1, admission.get("finiteMapSnapshotCount")
                    .getAsInt());
            assertEquals(1, imported.summary.getAsJsonArray(
                    "heapObservations").size());
            assertFalse(imported.diagnostics.contains(
                    "UNSUPPORTED_RUNTIME_HEAP_OBSERVATION_KIND"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsFiniteMapSnapshotWithoutStableExactCertificate()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String method = "<example.Store: void prune()>";
            JsonObject map = mapInputExpression();
            JsonObject key = constant("Y_I_7", "java/lang/Integer");
            JsonObject read = runtimeMapEntryRead(map, key, method, 3,
                    0, 1, 1);
            JsonObject snapshot = runtimeFiniteMapEntrySnapshot(map, key,
                    method, 3, 1, 1);
            snapshot.addProperty("sizeStable", false);
            JsonArray observations = new JsonArray();
            observations.add(read);
            observations.add(snapshot);

            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations,
                    defaultReadSymbolize(), tokenFieldObservations(103));

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "INCOMPLETE_RUNTIME_FINITE_MAP_SNAPSHOT"));
            assertEquals(0, imported.summary.getAsJsonObject(
                    "heapEffectModel").getAsJsonObject(
                    "runtimeHeapObservationImport")
                    .get("finiteMapSnapshotCount").getAsInt());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsIndependentDynamicFieldInstancesForTwoMapEntries()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String prune = "<example.Store: void prune()>";
            String materializationSite = prune + "#u4";
            JsonObject map = mapInputExpression();
            JsonObject firstKey = symbol("entryKey1", "I");
            JsonObject secondKey = symbol("entryKey2", "I");
            JsonObject firstRead = runtimeMapEntryRead(map, firstKey,
                    prune, 3, 0, 1, 1);
            JsonObject secondRead = runtimeMapEntryRead(map, secondKey,
                    prune, 3, 0, 2, 2);
            secondRead.addProperty("keyObjectToken", 202L);
            secondRead.addProperty("valueObjectToken", 203L);
            secondRead.addProperty("entryObjectToken", 204L);
            JsonArray observations = new JsonArray();
            observations.add(firstRead);
            observations.add(secondRead);

            String firstDynamic = dynamicFieldSymbol("REGION.P.in.1",
                    materializationSite, 1);
            String secondDynamic = dynamicFieldSymbol("REGION.P.in.1",
                    materializationSite, 2);
            JsonArray dynamicBindings = new JsonArray();
            dynamicBindings.add(dynamicFieldBinding(firstDynamic,
                    materializationSite, 1, 105L, firstRead, firstKey));
            dynamicBindings.add(dynamicFieldBinding(secondDynamic,
                    materializationSite, 2, 205L, secondRead, secondKey));
            JsonArray fieldObservations = new JsonArray();
            fieldObservations.add(dynamicFieldObservation(firstDynamic,
                    materializationSite, 1, 105L, firstRead));
            fieldObservations.add(dynamicFieldObservation(secondDynamic,
                    materializationSite, 2, 205L, secondRead));
            JsonArray mappings = new JsonArray();
            JsonObject firstExpression = symbol(
                    "M_J_field_" + firstDynamic + "_expiry", "J");
            JsonObject secondExpression = symbol(
                    "M_J_field_" + secondDynamic + "_expiry", "J");
            mappings.add(branchMapping(prune, 4, 1, true,
                    firstExpression));
            mappings.add(branchMapping(prune, 4, 2, true,
                    secondExpression));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), new JsonArray(), true,
                    new JsonArray(), singletonString(prune),
                    guardedWriteEdges(prune), observations,
                    defaultReadSymbolize(), mappings, fieldObservations,
                    dynamicBindings);

            assertTrue(imported.diagnostics,
                    imported.summary.get("relationallyComplete")
                            .getAsBoolean());
            assertEquals(0, imported.diagnostics.trim().length());
            assertEquals(2, imported.summary.getAsJsonArray(
                    "dynamicFieldBindings").size());
            JsonArray importedReads = imported.summary.getAsJsonArray(
                    "heapObservations");
            assertEquals(2, importedReads.size());
            JsonObject firstBinding = importedReads.get(0).getAsJsonObject()
                    .getAsJsonArray("entryFieldBindings").get(0)
                    .getAsJsonObject();
            JsonObject secondBinding = importedReads.get(1).getAsJsonObject()
                    .getAsJsonArray("entryFieldBindings").get(0)
                    .getAsJsonObject();
            assertEquals("REGION.P.in.1", firstBinding.get(
                    "baseInputSymbol").getAsString());
            assertEquals("REGION.P.in.1", secondBinding.get(
                    "baseInputSymbol").getAsString());
            assertEquals(firstDynamic, firstBinding.get(
                    "dynamicFieldSymbol").getAsString());
            assertEquals(secondDynamic, secondBinding.get(
                    "dynamicFieldSymbol").getAsString());
            assertFalse(firstBinding.has("fieldSymbol"));
            assertEquals(firstExpression, firstBinding.get(
                    "fieldExpression"));
            assertEquals(secondExpression, secondBinding.get(
                    "fieldExpression"));
            JsonObject importedDynamic = imported.summary.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            assertEquals(103L, importedDynamic.get(
                    "entryValueOwnerObjectToken").getAsLong());
            assertEquals(105L, importedDynamic.get(
                    "leafOwnerObjectToken").getAsLong());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsReadOnlyMapEntryWithExactDynamicStateBase()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture imported = importNonMutatingDynamicMapReadFixture(
                    folder.getRoot().toPath(), "VALID");

            assertFalse(imported.diagnostics, imported.diagnostics.contains(
                    "UNRESOLVED_HEAP_OBSERVATION_STATE_PORT"));
            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapEffects").size());
            assertEquals(0, imported.summary.getAsJsonObject(
                    "heapEffectModel").get("candidateMutationCount")
                    .getAsInt());
            assertEquals(imported.diagnostics, 1,
                    imported.summary.getAsJsonArray(
                            "heapObservations").size());
            JsonObject observation = imported.summary.getAsJsonArray(
                    "heapObservations").get(0).getAsJsonObject();
            assertTrue(observation.get("complete").getAsBoolean());
            assertTrue(observation.get("stateBaseComplete").getAsBoolean());
            assertEquals("NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_"
                            + "FIELD_BASE_V1",
                    observation.get("stateBindingAuthority").getAsString());
            assertTrue(observation.get("statePort").getAsString().matches(
                    "REGION\\.P\\.state\\.heapObservation\\.[0-9a-f]{12}"));
            assertNotEquals("REGION.P.in.1",
                    observation.get("statePort").getAsString());
            assertEquals(1, observation.getAsJsonArray(
                    "entryFieldBindings").size());
            JsonObject proof = observation.getAsJsonObject(
                    "stateBaseProof");
            assertEquals(observation.get("statePort").getAsString(),
                    proof.get("statePort").getAsString());
            assertEquals(101L, proof.get("backingMapObjectToken")
                    .getAsLong());
            assertEquals(0, proof.get("candidateMutationCount").getAsInt());
            assertEquals(0, proof.get("heapEffectCount").getAsInt());
            assertTrue(proof.get("complete").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void readOnlyDynamicMapStateBaseFailsClosedWithoutExactProofs()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            for (String mode : new String[]{"INVALID_VM_MAPPING",
                    "DUPLICATE_VM_MAPPING", "INVALID_SLICE_BINDING"}) {
                MapFixture imported = importNonMutatingDynamicMapReadFixture(
                        folder.getRoot().toPath().resolve(mode), mode);
                JsonArray importedObservations = imported.summary.has(
                        "heapObservations") ? imported.summary
                        .getAsJsonArray("heapObservations") : null;
                if (importedObservations == null
                        || importedObservations.size() == 0) {
                    // A missing or duplicate immutable witness now rejects
                    // the result before heap-observation import.  That is a
                    // stronger fail-closed outcome than retaining an
                    // incomplete observation from the retired mapping-field
                    // validation path.
                    assertTrue(mode + ": " + imported.diagnostics,
                            !imported.diagnostics.trim().isEmpty());
                    continue;
                }
                JsonObject observation = importedObservations.get(0)
                        .getAsJsonObject();
                assertFalse(mode, observation.get("complete").getAsBoolean());
                assertFalse(mode, observation.has("stateBaseProof"));
                assertFalse(mode, observation.has("stateBaseComplete"));
                assertTrue(mode, imported.diagnostics.contains(
                        "UNRESOLVED_HEAP_OBSERVATION_STATE_PORT"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void certifiesOnlyUniqueRawExpiryFallbackWithValidSiblingOperator()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture valid = importRawExpiryFallbackFixture(
                    folder.getRoot().toPath().resolve("valid"), "VALID");
            assertTrue(valid.diagnostics,
                    valid.summary.get("relationallyComplete").getAsBoolean());
            JsonObject rawOne = valid.summary.getAsJsonObject(
                    "pathConditionNormalization").getAsJsonArray(
                    "conditionIndexMap").get(1).getAsJsonObject();
            assertEquals("RETAINED", rawOne.get("status").getAsString());
            assertEquals(
                    "CERTIFIED_DYNAMIC_MAP_ENTRY_FIELD_RAW_PC_"
                            + "SIBLING_BRANCH_TEMPLATE_V1",
                    rawOne.get("admissionAuthority").getAsString());
            int normalized = rawOne.get("normalizedConditionIndex")
                    .getAsInt();
            assertEquals(">=", valid.summary.getAsJsonArray(
                    "pathCondition").get(normalized).getAsJsonObject()
                    .get("_op").getAsString());
            JsonObject entryBinding = valid.summary.getAsJsonArray(
                    "heapObservations").get(0).getAsJsonObject()
                    .getAsJsonArray("entryFieldBindings").get(0)
                    .getAsJsonObject();
            assertEquals("EXACT_SEMANTIC_RAW_PC_DYNAMIC_SYMBOL_FALLBACK",
                    entryBinding.get("fieldExpressionAuthority")
                            .getAsString());
            assertEquals(-1, valid.summary.getAsJsonArray("branchMappings")
                    .get(0).getAsJsonObject().get("rawConditionIndex")
                    .getAsInt());

            String[] rejected = new String[]{"MALFORMED_OPERATOR",
                    "DUPLICATE_DYNAMIC", "DUPLICATE_RAW",
                    "WRONG_ENTRY_VALUE_OWNER"};
            for (String mutation : rejected) {
                MapFixture invalid = importRawExpiryFallbackFixture(
                        folder.getRoot().toPath().resolve(
                                mutation.toLowerCase(java.util.Locale.ROOT)),
                        mutation);
                assertFalse(mutation + ": " + invalid.diagnostics,
                        invalid.summary.get("relationallyComplete")
                                .getAsBoolean());
                JsonObject rejectedRaw = invalid.summary.getAsJsonObject(
                        "pathConditionNormalization").getAsJsonArray(
                        "conditionIndexMap").get(1).getAsJsonObject();
                assertEquals(mutation, "FILTERED",
                        rejectedRaw.get("status").getAsString());
                assertEquals(mutation,
                        "BINARY_CONDITION_WITHOUT_INSTRUMENTED_BRANCH_MAPPING",
                        rejectedRaw.get("reason").getAsString());
                assertTrue(mutation + ": " + invalid.diagnostics,
                        invalid.diagnostics.contains(
                                "WRONG_ENTRY_VALUE_OWNER".equals(mutation)
                                        ? "INCOMPLETE_DYNAMIC_FIELD_BINDING"
                                        : "MISSING_DYNAMIC_FIELD_EXPRESSION"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsExactAndDiscoveredContainerBindingsFromMaterializations()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture exact = importContainerDynamicFixture(
                    folder.getRoot().toPath().resolve("exact"), "VALID");
            MapFixture discovered = importContainerDynamicFixture(
                    folder.getRoot().toPath().resolve("discovered"),
                    "VALID_DISCOVERY");

            for (MapFixture imported : java.util.Arrays.asList(exact,
                    discovered)) {
                assertTrue(imported.diagnostics,
                        imported.summary.get("relationallyComplete")
                                .getAsBoolean());
                assertEquals(0, imported.diagnostics.trim().length());
                JsonObject binding = imported.summary.getAsJsonArray(
                        "dynamicFieldBindings").get(0).getAsJsonObject();
                assertEquals(2, binding.get("schemaVersion").getAsInt());
                assertEquals("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING",
                        binding.get("kind").getAsString());
                assertEquals(
                        "EXACT_REQUESTED_OUTPUT_MAP_PUT_KEY_DYNAMIC_SYMBOL",
                        binding.get("fieldExpressionAuthority").getAsString());
                assertTrue(binding.get("fieldExpression").isJsonObject());
                assertEquals(
                        "RAW_SEMANTIC_REQUESTED_OUTPUT_MAP_PUT_KEY_EXACT_"
                                + "DYNAMIC_SYMBOL_V1",
                        binding.get("consumerWitnessAuthority")
                                .getAsString());
                assertEquals("EXACT_ARRAY_INDEX", binding.getAsJsonObject(
                        "containerSelector").get("selectorAuthority")
                        .getAsString());
            }
            assertEquals("EXACT_ARRAY_INDEX", exact.summary.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject()
                    .getAsJsonObject("containerSelector").get(
                            "resolvedFromSelectorAuthority").getAsString());
            assertEquals("DISCOVER_UNIQUE_IDENTITY_INDEX",
                    discovered.summary.getAsJsonArray(
                            "dynamicFieldBindings").get(0).getAsJsonObject()
                            .getAsJsonObject("containerSelector").get(
                            "resolvedFromSelectorAuthority").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsIncompleteContainerElementFieldBindingJoins()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String[] cases = new String[]{
                    "WRONG_DECLARATION", "WRONG_INDEX", "WRONG_CELL",
                    "WRONG_TOKEN", "WRONG_SCOPE", "DUPLICATE",
                    "MIXED_MAP_SELECTOR", "MISSING_OBSERVATION",
                    "MISSING_MAP_PUT_CONSUMER", "WRONG_BRIDGE_AUTHORITY",
                    "WRONG_ACTUAL_HOOK_SITE", "AMBIGUOUS_MAP_PUT_CONSUMER"
            };
            for (String name : cases) {
                MapFixture imported = importContainerDynamicFixture(
                        folder.getRoot().toPath().resolve(
                                name.toLowerCase(java.util.Locale.ROOT)),
                        name);
                assertFalse(name + ": " + imported.diagnostics,
                        imported.summary.get("relationallyComplete")
                                .getAsBoolean());
                assertTrue(name + ": " + imported.diagnostics,
                        imported.diagnostics.contains("DUPLICATE".equals(name)
                                ? "DUPLICATE_DYNAMIC_FIELD_BINDING"
                                : "INCOMPLETE_DYNAMIC_FIELD_BINDING"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsDeclaredEntryReadWithMissingToken()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject read = runtimeMapEntryRead(mapInputExpression(),
                    symbol("entryKey", "I"),
                    "<example.Store: void prune()>", 3, 0, 1, 1);
            read.remove("valueObjectTokenKnown");
            JsonArray observations = new JsonArray();
            observations.add(read);
            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations,
                    defaultReadSymbolize(), tokenFieldObservations(103));

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapObservations").size());
            assertTrue(imported.diagnostics.contains(
                    "INCOMPLETE_RUNTIME_HEAP_OBSERVATION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsDuplicateDeclaredEntryRead()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject read = runtimeMapEntryRead(mapInputExpression(),
                    symbol("entryKey", "I"),
                    "<example.Store: void prune()>", 3, 0, 1, 1);
            JsonArray observations = new JsonArray();
            observations.add(read);
            observations.add(read.deepCopy());
            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations,
                    defaultReadSymbolize(), tokenFieldObservations(103));

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "DUPLICATE_RUNTIME_HEAP_OBSERVATION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsAmbiguousEntryReadStatePort()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject ambiguousMap = symbol(
                    "M_L_REGION.P.in.0+REGION.P.in.2", "L");
            JsonArray observations = new JsonArray();
            observations.add(runtimeMapEntryRead(ambiguousMap,
                    symbol("entryKey", "I"),
                    "<example.Store: void prune()>", 3, 0, 1, 1));
            JsonArray symbolize = defaultReadSymbolize();
            symbolize.add(inputAction("REGION.P.in.2",
                    "<example.Store: java.util.Map shadow>"));
            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations, symbolize,
                    tokenFieldObservations(103));

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "AMBIGUOUS_HEAP_OBSERVATION_STATE_PORT"));
            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapEffects").size());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsGuardedIdentityWhenReadStateDoesNotMapToOutput()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject foreignMap = symbol(
                    "M_L_field_REGION.P.in.2_example/Store", "L");
            JsonArray observations = new JsonArray();
            observations.add(runtimeMapEntryRead(foreignMap,
                    symbol("entryKey", "I"),
                    "<example.Store: void prune()>", 3, 0, 1, 1));
            JsonArray symbolize = defaultReadSymbolize();
            symbolize.add(inputAction("REGION.P.in.2",
                    "<example.Store: java.util.Map shadow>"));
            MapFixture imported = importGuardedNoRemoveFixture(
                    folder.getRoot().toPath(), observations, symbolize,
                    tokenFieldObservations(103));

            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(imported.diagnostics.contains(
                    "UNRESOLVED_GUARDED_MAP_IDENTITY_STATE"));
            assertEquals("REGION.P.in.2", imported.summary.getAsJsonArray(
                    "heapObservations").get(0).getAsJsonObject()
                    .get("statePort").getAsString());
            assertEquals(0, imported.summary.getAsJsonArray(
                    "heapEffects").size());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void admitsSystemClockAsUnforcedVmEnvironment()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String vmClock =
                    "<java.lang.System: long currentTimeMillis()>.return";
            JsonObject placeholder = placeholderExpression(
                    "currentTimeMills", 3);
            PlaceholderFixture imported = importPlaceholderFixture(
                    folder.getRoot().toPath(),
                    exactCurrentTimePlaceholderMaterialization(
                            vmClock),
                    placeholderCondition(placeholder), false,
                    vmClock);

            assertTrue(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            JsonObject admission = imported.summary.getAsJsonObject(
                    "inputMaterializationAdmission");
            assertTrue(admission.get("complete").getAsBoolean());
            assertEquals(0, admission.getAsJsonArray(
                    "observedSymbolizedInputs").size());
            assertEquals("REGION.TIME.in.0", admission.getAsJsonArray(
                    "admittedVmIntrinsicPlaceholderInputs").get(0)
                    .getAsString());
            JsonArray requirements = imported.summary.getAsJsonArray(
                    "unforcedEnvironmentValidationRequirements");
            assertEquals(1, requirements.size());
            JsonObject requirement = requirements.get(0).getAsJsonObject();
            assertEquals("UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT",
                    requirement.get("kind").getAsString());
            assertEquals("currentTimeMills",
                    requirement.get("placeholderFunction").getAsString());
            assertEquals("CUSTOM_JDK_SYMBOLIC_ND_FUNC",
                    requirement.get("captureAuthority").getAsString());
            assertEquals(vmClock,
                    requirement.get("cell").getAsString());
            assertFalse(requirement.get("modelControllable")
                    .getAsBoolean());
            assertEquals("UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION",
                    requirement.get("replayPolicy").getAsString());
            assertEquals("currentTimeMills#3", requirement.getAsJsonArray(
                    "placeholderEvidenceIdentities").get(0).getAsString());
            JsonArray bindings = imported.summary.getAsJsonArray(
                    "vmIntrinsicPlaceholderBindings");
            assertEquals(1, bindings.size());
            JsonObject binding = bindings.get(0).getAsJsonObject();
            assertEquals(1, binding.get("schemaVersion").getAsInt());
            assertEquals("VM_INTRINSIC_PLACEHOLDER_PORT_BINDING",
                    binding.get("kind").getAsString());
            assertEquals("currentTimeMills#3", binding.get(
                    "placeholderIdentity").getAsString());
            assertEquals(3, binding.get("placeholderCount").getAsInt());
            assertEquals("REGION.TIME.in.0",
                    binding.get("inputPort").getAsString());
            assertEquals(vmClock,
                    binding.get("cell").getAsString());
            assertEquals("UNIQUE_USED_PLACEHOLDER_IDENTITY_TO_EXACT_"
                            + "SLICE_INPUT",
                    binding.get("ownerAuthority").getAsString());
            JsonObject bindingAdmission = imported.summary.getAsJsonObject(
                    "vmIntrinsicPlaceholderBindingAdmission");
            assertEquals(1, bindingAdmission.get("schemaVersion").getAsInt());
            assertTrue(bindingAdmission.get("complete").getAsBoolean());
            assertFalse(imported.diagnostics.contains(
                    "SLICE_INPUT_NOT_SYMBOLIZED"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsExactOutboundArgumentExpressionInsteadOfVoidRoot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject summary = importExactOutputCaptureFixture(
                    folder.getRoot().toPath(),
                    symbol("M_L_field_REGION.OUT.in.0_java/lang/String", "L"),
                    1);

            assertTrue(summary.get("relationallyComplete").getAsBoolean());
            assertEquals("M_L_field_REGION.OUT.in.0_java/lang/String",
                    summary.getAsJsonObject("outputExpressions")
                            .getAsJsonObject("REGION.OUT.out.0")
                            .get("_exp").getAsString());
            assertTrue(summary.getAsJsonObject("outputExpressionAdmission")
                    .get("complete").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactOutboundArgumentCaptureFailsClosedWhenAmbiguousOrConstant()
            throws Exception {
        TemporaryFolder first = new TemporaryFolder();
        first.create();
        TemporaryFolder second = new TemporaryFolder();
        second.create();
        try {
            JsonObject ambiguous = importExactOutputCaptureFixture(
                    first.getRoot().toPath(),
                    symbol("M_L_field_REGION.OUT.in.0_java/lang/String", "L"),
                    2);
            assertFalse(ambiguous.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(String.valueOf(ambiguous.getAsJsonObject(
                    "outputExpressionAdmission").get("issues"))
                    .contains("AMBIGUOUS_EXACT_OUTPUT_EXPRESSION_CAPTURE"));

            JsonObject constant = importExactOutputCaptureFixture(
                    second.getRoot().toPath(), constant("Y_L_value", "L"), 1);
            assertFalse(constant.get("relationallyComplete").getAsBoolean());
            assertTrue(String.valueOf(constant.getAsJsonObject(
                    "outputExpressionAdmission").get("issues"))
                    .contains("NON_SYMBOLIC_OUTPUT_EXPRESSION"));
        } finally {
            first.delete();
            second.delete();
        }
    }

    @Test
    public void importsExactFieldAssignmentRhsAsHeapStateOutput()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture imported = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath(), "NORMAL", true, true,
                    symbol("M_L_field_REGION.FIELD.in.0_java/lang/String",
                            "L"));

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals("M_L_field_REGION.FIELD.in.0_java/lang/String",
                    imported.summary.getAsJsonObject("outputExpressions")
                            .getAsJsonObject("REGION.FIELD.out.0")
                            .get("_exp").getAsString());
            JsonObject admission = imported.summary.getAsJsonObject(
                    "outputExpressionAdmission");
            assertTrue(admission.get("complete").getAsBoolean());
            assertEquals("EXACT_FIELD_ASSIGNMENT_RHS",
                    admission.get("authority").getAsString());
            assertTrue(imported.summary.getAsJsonObject("heapEffectModel")
                    .getAsJsonObject("staticTransformerCoverage")
                    .get("complete").getAsBoolean());
            assertTrue(imported.summary.getAsJsonObject("heapEffectModel")
                    .getAsJsonObject("staticTransformerCoverage")
                    .getAsJsonArray("matches").toString().contains(
                            "RUNTIME_EXACT_FIELD_ASSIGNMENT_RHS_CAPTURE"));

            MapFixture projected = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("projected"),
                    "NORMAL", true, true, JsonNull.INSTANCE);
            assertTrue(projected.diagnostics, projected.summary.get(
                    "relationallyComplete").getAsBoolean());
            JsonObject projectedExpression = projected.summary
                    .getAsJsonObject("outputExpressions")
                    .getAsJsonObject("REGION.FIELD.out.0");
            assertEquals("SymbolExpression", projectedExpression.get(
                    "_type").getAsString());
            assertEquals("REGION.FIELD.in.0", projectedExpression.get(
                    "_causynth_projection_input_port").getAsString());
            assertEquals("[\"value\"]", projectedExpression.getAsJsonArray(
                    "_causynth_projection_field_path").toString());
            assertEquals("EXACT_FIELD_ASSIGNMENT_RHS_FROM_UNIQUE_PROJECTED_"
                            + "INPUT_CARRIER",
                    projected.summary.getAsJsonObject(
                            "outputExpressionAdmission")
                            .get("authority").getAsString());
            assertEquals(0, projected.summary.getAsJsonObject(
                    "inputMaterializationAdmission").getAsJsonArray(
                    "observedSymbolizedInputs").size());
            assertEquals("[\"REGION.FIELD.in.0\"]", projected.summary
                    .getAsJsonObject("inputMaterializationAdmission")
                    .getAsJsonArray("admittedConcreteFallbackInputs")
                    .toString());
            assertEquals(1, projected.summary.getAsJsonArray(
                    "ignoredRuntimeHeapEvidence").size());
            assertEquals("OUTSIDE_REQUESTED_OUTPUT_SLICE",
                    projected.summary.getAsJsonArray(
                            "ignoredRuntimeHeapEvidence").get(0)
                            .getAsJsonObject().get("reason").getAsString());

            MapFixture causalGuardObservation =
                    importExactFieldAssignmentCaptureFixture(
                            folder.getRoot().toPath().resolve(
                                    "causal-map-observation"),
                            "NORMAL", true, true,
                            "<example.State: java.lang.String value>",
                            JsonNull.INSTANCE, "CAUSAL_MAP_OBSERVATION");
            assertFalse(causalGuardObservation.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals(0, causalGuardObservation.summary.getAsJsonArray(
                    "ignoredRuntimeHeapEvidence").size());
            assertTrue(causalGuardObservation.diagnostics,
                    causalGuardObservation.diagnostics.contains(
                            "INCOMPLETE_RUNTIME_HEAP_OBSERVATION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsVmAttestedGuardedConstantFieldAssignment()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture imported = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath(), "NORMAL", true, true,
                    "<example.State: int value>",
                    constant("Y_I_10", "I"), "EXACT");

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals("Y_I_10", imported.summary.getAsJsonObject(
                    "outputExpressions").getAsJsonObject(
                    "REGION.FIELD.out.0").get("_exp").getAsString());
            assertEquals("EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_"
                            + "PATH_GUARD",
                    imported.summary.getAsJsonObject(
                            "outputExpressionAdmission")
                            .get("authority").getAsString());
            assertEquals(1, imported.summary.getAsJsonArray(
                    "pathCondition").size());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void guardedNullEarlyReturnDropsOnlyUnexecutedLazyInputs()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture imported = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath(), "NORMAL", true, true,
                    "<example.State: int value>",
                    constant("Y_I_10", "I"),
                    "EXACT_NULL_WITH_UNUSED_INPUT");

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            JsonObject admission = imported.summary.getAsJsonObject(
                    "inputMaterializationAdmission");
            assertTrue(admission.get("complete").getAsBoolean());
            assertEquals("[\"REGION.FIELD.in.1\"]", admission
                    .getAsJsonArray("pathInactiveSliceInputs").toString());
            assertEquals("EXACT_VM_WITNESS_GUARDED_CONSTANT_OUTPUT_PLUS_"
                            + "UNEXECUTED_LAZY_INPUT_V1",
                    admission.getAsJsonArray("pathInactiveProofs").get(0)
                            .getAsJsonObject().get("authority").getAsString());
            assertFalse(imported.diagnostics.contains(
                    "SLICE_INPUT_NOT_SYMBOLIZED:REGION.FIELD.in.1"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsVmAttestedStringPredicateGuardedConstant()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture imported = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath(), "NORMAL", true, true,
                    "<example.State: int value>",
                    constant("Y_I_10", "I"),
                    "EXACT_STRING_PREDICATE");

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals("EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_"
                            + "PATH_GUARD",
                    imported.summary.getAsJsonObject(
                            "outputExpressionAdmission")
                            .get("authority").getAsString());
            JsonObject guard = imported.summary.getAsJsonArray(
                    "pathCondition").get(0).getAsJsonObject();
            assertEquals("OpStrExpression",
                    guard.get("_type").getAsString());
            assertEquals("contains", guard.get("_name").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void guardedConstantRejectsValueMismatchFilteredAndForgedGuards()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            MapFixture valueMismatch =
                    importExactFieldAssignmentCaptureFixture(
                            root.resolve("value"), "NORMAL", true, true,
                            "<example.State: int value>",
                            constant("Y_I_11", "I"), "EXACT");
            MapFixture filtered = importExactFieldAssignmentCaptureFixture(
                    root.resolve("filtered"), "NORMAL", true, true,
                    "<example.State: int value>",
                    constant("Y_I_10", "I"), "FILTERED");
            MapFixture forged = importExactFieldAssignmentCaptureFixture(
                    root.resolve("forged"), "NORMAL", true, true,
                    "<example.State: int value>",
                    constant("Y_I_10", "I"), "FORGED_SEMANTIC");
            MapFixture forgedOperator =
                    importExactFieldAssignmentCaptureFixture(
                            root.resolve("forged-operator"), "NORMAL", true,
                            true, "<example.State: int value>",
                            constant("Y_I_10", "I"), "FORGED_OPERATOR");
            MapFixture inactiveEnvelope =
                    importExactFieldAssignmentCaptureFixture(
                            root.resolve("inactive-envelope"), "NORMAL", true,
                            true, "<example.State: int value>",
                            constant("Y_I_10", "I"), "INACTIVE_ENVELOPE");

            assertFalse(valueMismatch.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(valueMismatch.summary.getAsJsonObject(
                    "outputExpressionAdmission").get("issues").toString()
                    .contains("GUARDED_CONSTANT_CAPTURE_VALUE_MISMATCH"));
            assertFalse(filtered.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(filtered.summary.getAsJsonObject(
                    "outputExpressionAdmission").get("issues").toString()
                    .contains("CONSTANT_OUTPUT_PATH_GUARD_NOT_EXACT_VM_"
                            + "EVENT"));
            assertFalse(forged.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(forged.summary.getAsJsonObject(
                    "outputExpressionAdmission").get("issues").toString()
                    .contains("CONSTANT_OUTPUT_PATH_GUARD_NOT_EXACT_VM_"
                            + "EVENT"));
            assertFalse(forgedOperator.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(forgedOperator.summary.getAsJsonObject(
                    "outputExpressionAdmission").get("issues").toString()
                    .contains("CONSTANT_OUTPUT_PATH_GUARD_NOT_EXACT_VM_"
                            + "EVENT"));
            assertFalse(inactiveEnvelope.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(inactiveEnvelope.summary.getAsJsonObject(
                    "outputExpressionAdmission").get("issues").toString()
                    .contains("GUARDED_CONSTANT_VM_PRIMITIVE_ENVELOPE_"
                            + "INVALID"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void arrayFieldOutputRequiresCompleteTypedArrayValueExpression()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String field = "<example.State: example.Key[] value>";
            JsonObject arrayValue = arrayValueExpression(
                    "[Lexample/Key;", "Lexample/Key;", true,
                    symbol("M_L_field_REGION.FIELD.in.0_element",
                            "example/Key"));
            MapFixture accepted = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("accepted"), "NORMAL",
                    true, true, field, arrayValue);

            assertTrue(accepted.diagnostics, accepted.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals("ArrayValueExpression", accepted.summary
                    .getAsJsonObject("outputExpressions")
                    .getAsJsonObject("REGION.FIELD.out.0")
                    .get("_type").getAsString());
            assertTrue(accepted.summary.getAsJsonObject(
                    "outputExpressionAdmission").get("complete")
                    .getAsBoolean());

            MapFixture lengthOnly = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("length-only"),
                    "NORMAL", true, true, field,
                    symbol("M_I_field_REGION.FIELD.in.0_length", "I"));
            assertFalse(lengthOnly.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(lengthOnly.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains(
                            "ARRAY_OUTPUT_VALUE_EXPRESSION_REQUIRED"));

            JsonObject incomplete = arrayValue.deepCopy();
            incomplete.addProperty("_elements_complete", false);
            MapFixture incompleteElements =
                    importExactFieldAssignmentCaptureFixture(
                            folder.getRoot().toPath().resolve("incomplete"),
                            "NORMAL", true, true, field, incomplete);
            assertFalse(incompleteElements.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertTrue(incompleteElements.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains("ARRAY_OUTPUT_ELEMENTS_INCOMPLETE"));

            JsonObject wrongDescriptor = arrayValue.deepCopy();
            wrongDescriptor.addProperty("_java_type", "[Lexample/Other;");
            MapFixture mismatched = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("wrong-descriptor"),
                    "NORMAL", true, true, field, wrongDescriptor);
            assertFalse(mismatched.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(mismatched.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains("ARRAY_OUTPUT_JAVA_TYPE_MISMATCH"));

            JsonObject missingElement = arrayValue.deepCopy();
            missingElement.getAsJsonArray("_elements").get(0)
                    .getAsJsonObject().remove("expression");
            MapFixture missing = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("missing-element"),
                    "NORMAL", true, true, field, missingElement);
            assertFalse(missing.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(missing.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains(
                            "ARRAY_OUTPUT_ELEMENT_EXPRESSION_MISSING"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void importsExactEngineArrayInputBridgeForNormalizedLoad()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String cell = "<example.ArrayHandler: int run("
                    + "java.lang.Object[])>.param0:java.lang.Object[]";
            JsonArray bindings = singletonObject(engineArrayInputBinding(
                    "REGION.ARRAY.in.0", cell, "AL_1", 41));
            MapFixture fixture = importEngineArrayBridgeFixture(
                    folder.getRoot().toPath(), bindings, false, false);

            assertTrue(fixture.summary.get("relationallyComplete")
                    .getAsBoolean());
            JsonObject admitted = fixture.summary.getAsJsonArray(
                    "engineArrayInputBindings").get(0).getAsJsonObject();
            assertEquals("AL_1",
                    admitted.get("engineArrayId").getAsString());
            assertEquals("[Ljava/lang/Object;", admitted.get(
                    "inputJavaTypeDescriptor").getAsString());
            assertEquals("ArrayValueExpression", admitted.getAsJsonObject(
                    "arrayValueExpression").get("_type").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void engineArrayIdAndConcretePrimitiveLiteralAreFrozenToType() {
        assertTrue(ConcolicSummaryImporter
                .engineArrayIdMatchesComponentForTests("AI_12", "[I"));
        assertTrue(ConcolicSummaryImporter
                .engineArrayIdMatchesComponentForTests("AL_7",
                        "[Ljava/lang/Object;"));
        assertFalse(ConcolicSummaryImporter
                .engineArrayIdMatchesComponentForTests("AL_12", "[I"));
        assertFalse(ConcolicSummaryImporter
                .engineArrayIdMatchesComponentForTests("VM_ARRAY_12", "[I"));
        assertTrue(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("I", "Y_I_-17"));
        assertTrue(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("B", "Y_B_-128"));
        assertTrue(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("C", "Y_C_65535"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("B", "Y_B_128"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("C", "Y_C_-1"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("I", "Y_I_01"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("I", "Y_I_-0"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("I",
                        "Y_I_2147483648"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("I", "Y_J_-17"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("I", "M_I_value"));
        assertFalse(ConcolicSummaryImporter
                .validConcretePrimitiveLiteralForTests("Z", "Y_Z_maybe"));
    }

    @Test
    public void importsSchema3MapValuesAndRejectsKeySetView()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture values = importMapProjectionFixture(
                    folder.getRoot().toPath().resolve("values"),
                    "MAP_VALUES_VIEW", "");
            assertTrue(values.diagnostics,
                    values.summary.get("relationallyComplete")
                            .getAsBoolean());
            JsonArray bindings = values.summary.getAsJsonArray(
                    "dynamicFieldBindings");
            assertEquals(2, bindings.size());
            assertEquals(3, bindings.get(0).getAsJsonObject().get(
                    "schemaVersion").getAsInt());

            MapFixture keySet = importMapProjectionFixture(
                    folder.getRoot().toPath().resolve("keyset"),
                    "MAP_KEY_SET_VIEW", "");
            assertFalse(keySet.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(keySet.diagnostics, keySet.diagnostics.contains(
                    "MAP_PROJECTION"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void schema3MapProjectionRejectsScopeTokenIndexLengthIdentityAndType()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            for (String fault : new String[]{"SCOPE", "TOKEN", "ORDER",
                    "LENGTH", "IDENTITY", "TYPE", "DUPLICATE_KEY",
                    "FLOAT_ZERO_KEY", "IDENTITY_MAP", "FIELD_WRITE",
                    "FIELD_VALUE", "IMPLEMENTATION_DRIFT",
                    "FIELD_SIGNATURE_DRIFT"}) {
                MapFixture fixture = importMapProjectionFixture(
                        folder.getRoot().toPath().resolve(fault),
                        "MAP_VALUES_VIEW", fault);
                assertFalse(fault + ":" + fixture.diagnostics,
                        fixture.summary.get("relationallyComplete")
                                .getAsBoolean());
                assertTrue(fault + ":" + fixture.diagnostics,
                        fixture.diagnostics.contains("MAP_PROJECTION"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void arrayLoadWithoutExactEngineBridgeFailsClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture fixture = importEngineArrayBridgeFixture(
                    folder.getRoot().toPath(), null, false, false);

            assertFalse(fixture.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, fixture.summary.getAsJsonArray(
                    "engineArrayInputBindings").size());
            assertTrue(fixture.diagnostics.contains(
                    "MISSING_ENGINE_ARRAY_INPUT_BINDING"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void unusedButExactSymbolizedArrayBridgeRemainsAdmissible()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String method = "<example.ArrayHandler: int run("
                    + "java.lang.Object[],java.lang.Object[])>";
            JsonArray bindings = new JsonArray();
            bindings.add(engineArrayInputBinding("REGION.ARRAY.in.0",
                    method + ".param0:java.lang.Object[]",
                    "AL_1", 41));
            bindings.add(engineArrayInputBinding("REGION.ARRAY.in.1",
                    method + ".param1:java.lang.Object[]",
                    "AL_2", 42));
            MapFixture fixture = importEngineArrayBridgeFixture(
                    folder.getRoot().toPath(), bindings, false, true);

            assertTrue(fixture.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(2, fixture.summary.getAsJsonArray(
                    "engineArrayInputBindings").size());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mismatchedVmArrayIdentityAndArrayStoreFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String cell = "<example.ArrayHandler: int run("
                    + "java.lang.Object[])>.param0:java.lang.Object[]";
            JsonObject bad = engineArrayInputBinding("REGION.ARRAY.in.0",
                    cell, "AL_1", 41);
            bad.getAsJsonObject("arrayValueExpression").addProperty(
                    "_engine_array_id", "AL_3");
            bad.addProperty("symbolizationPrefix", "REGION.ARRAY.in.00");
            bad.addProperty("sameArrayObjectTokenVerified", false);
            MapFixture identity = importEngineArrayBridgeFixture(
                    folder.getRoot().toPath().resolve("identity"),
                    singletonObject(bad), false, false);
            assertFalse(identity.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(identity.diagnostics.contains(
                    "ARRAY_VALUE_ENGINE_ARRAY_ID_MISMATCH"));
            assertTrue(identity.diagnostics.contains(
                    "ARRAY_SYMBOLIZATION_PREFIX_OR_MODE_INVALID"));
            assertTrue(identity.diagnostics.contains(
                    "ARRAY_OBJECT_IDENTITY_INVALID"));

            JsonArray valid = singletonObject(engineArrayInputBinding(
                    "REGION.ARRAY.in.0", cell, "AL_1", 41));
            MapFixture store = importEngineArrayBridgeFixture(
                    folder.getRoot().toPath().resolve("store"),
                    valid, true, false);
            assertFalse(store.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(store.diagnostics.contains(
                    "ENGINE_ARRAY_STORE_UNSUPPORTED"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void fieldAssignmentRhsCaptureFailsClosedWithoutExitIdentityOrRelation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture abnormal = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("abnormal"), "THROW",
                    true, true, symbol(
                            "M_L_field_REGION.FIELD.in.0_java/lang/String",
                            "L"));
            assertFalse(abnormal.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(abnormal.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains(
                            "FIELD_ASSIGNMENT_RHS_REQUIRES_NORMAL_EXIT"));

            MapFixture identity = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("identity"), "NORMAL",
                    false, true, symbol(
                            "M_L_field_REGION.FIELD.in.0_java/lang/String",
                            "L"));
            assertFalse(identity.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(identity.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains(
                            "INVALID_POST_ASSIGNMENT_FIELD_OWNER_OR_VALUE_"
                                    + "IDENTITY_PROOF"));

            MapFixture relation = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("relation"), "NORMAL",
                    true, false, symbol(
                            "M_L_field_REGION.FIELD.in.0_java/lang/String",
                            "L"));
            assertFalse(relation.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(relation.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains(
                            "INCOMPLETE_EXACT_FIELD_ASSIGNMENT_RHS_RELATION"));

            MapFixture unbound = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("unbound"), "NORMAL",
                    true, true, symbol("unboundInternal", "L"));
            assertFalse(unbound.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertTrue(unbound.summary.getAsJsonObject(
                    "outputExpressionAdmission").getAsJsonArray("issues")
                    .toString().contains(
                            "FIELD_ASSIGNMENT_RHS_RELATION_NOT_CLOSED_"
                                    + "OVER_SLICE_INPUTS"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsInexactOrUnboundVmTimePlaceholderEvidence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            JsonObject exactBinding =
                    exactCurrentTimePlaceholderMaterialization();

            JsonElement[] evidence = new JsonElement[]{
                    placeholderCondition(placeholderExpression(
                            "currentTimeMillis", 1)),
                    placeholderCondition(placeholderExpression(
                            "nanoTime", 1)),
                    placeholderCondition(placeholderExpression(
                            "currentTimeMills", 0)),
                    JsonParser.parseString("{\"note\":\"PlaceholderExpression "
                            + "currentTimeMills #1\"}")
            };
            for (int index = 0; index < evidence.length; index++) {
                PlaceholderFixture rejected = importPlaceholderFixture(
                        root.resolve("bad-evidence-" + index), exactBinding,
                        evidence[index]);
                assertPlaceholderRejected(rejected,
                        "VM_INTRINSIC_PLACEHOLDER_EVIDENCE_"
                                + "MISSING_OR_INVALID");
            }

            PlaceholderFixture noBinding = importPlaceholderFixture(
                    root.resolve("missing-binding"), null,
                    placeholderCondition(placeholderExpression(
                            "currentTimeMills", 1)));
            assertPlaceholderRejected(noBinding,
                    "SLICE_INPUT_NOT_SYMBOLIZED");

            JsonObject nanoBinding = exactBinding.deepCopy();
            nanoBinding.addProperty("cell",
                    "<java.lang.System: long nanoTime()>.return");
            nanoBinding.addProperty("placeholderFunction", "nanoTime");
            PlaceholderFixture wrongBinding = importPlaceholderFixture(
                    root.resolve("wrong-binding"), nanoBinding,
                    placeholderCondition(placeholderExpression(
                            "currentTimeMills", 1)));
            assertPlaceholderRejected(wrongBinding,
                    "VM_INTRINSIC_PLACEHOLDER_BINDING_INVALID");

            JsonObject controlledBinding = exactBinding.deepCopy();
            controlledBinding.addProperty("modelControllable", true);
            PlaceholderFixture falselyControlled = importPlaceholderFixture(
                    root.resolve("controlled-binding"), controlledBinding,
                    placeholderCondition(placeholderExpression(
                            "currentTimeMills", 1)));
            assertPlaceholderRejected(falselyControlled,
                    "VM_INTRINSIC_PLACEHOLDER_BINDING_INVALID");

            PlaceholderFixture falselySymbolized = importPlaceholderFixture(
                    root.resolve("falsely-symbolized"), exactBinding,
                    placeholderCondition(placeholderExpression(
                            "currentTimeMills", 1)), true);
            assertPlaceholderRejected(falselySymbolized,
                    "VM_INTRINSIC_PLACEHOLDER_MUST_REMAIN_UNFORCED");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsAmbiguousUsedVmTimePlaceholderOwnerBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject ambiguous = binaryCondition(
                    "virtual long example.TimeHandler.handle():12", "!=",
                    placeholderExpression("currentTimeMills", 3),
                    placeholderExpression("currentTimeMills", 4));
            PlaceholderFixture imported = importPlaceholderFixture(
                    folder.getRoot().toPath(),
                    exactCurrentTimePlaceholderMaterialization(), ambiguous);

            assertTrue(imported.summary.getAsJsonObject(
                    "inputMaterializationAdmission").get("complete")
                    .getAsBoolean());
            assertFalse(imported.summary.get("relationallyComplete")
                    .getAsBoolean());
            assertEquals(0, imported.summary.getAsJsonArray(
                    "vmIntrinsicPlaceholderBindings").size());
            JsonObject admission = imported.summary.getAsJsonObject(
                    "vmIntrinsicPlaceholderBindingAdmission");
            assertFalse(admission.get("complete").getAsBoolean());
            assertTrue(admission.getAsJsonArray("failures").toString(),
                    admission.getAsJsonArray("failures").toString().contains(
                            "USED_IDENTITY_NOT_UNIQUE"));
            assertTrue(imported.diagnostics.contains(
                    "INCOMPLETE_VM_INTRINSIC_PLACEHOLDER_BINDING"));
        } finally {
            folder.delete();
        }
    }

    private static void assertPlaceholderRejected(
            PlaceholderFixture rejected, String diagnostic) {
        assertFalse(rejected.summary.get("relationallyComplete")
                .getAsBoolean());
        JsonObject admission = rejected.summary.getAsJsonObject(
                "inputMaterializationAdmission");
        assertFalse(admission.get("complete").getAsBoolean());
        assertEquals(0, admission.getAsJsonArray(
                "admittedVmIntrinsicPlaceholderInputs").size());
        assertEquals(0, rejected.summary.getAsJsonArray(
                "unforcedEnvironmentValidationRequirements").size());
        assertTrue(rejected.diagnostics.contains(diagnostic));
    }

    private static PlaceholderFixture importPlaceholderFixture(
            Path root, JsonObject materialization, JsonElement evidence)
            throws Exception {
        return importPlaceholderFixture(root, materialization, evidence,
                false);
    }

    private static PlaceholderFixture importPlaceholderFixture(
            Path root, JsonObject materialization, JsonElement evidence,
            boolean falselyReportSymbolized) throws Exception {
        return importPlaceholderFixture(root, materialization, evidence,
                falselyReportSymbolized,
                "<java.lang.System: long currentTimeMillis()>.return");
    }

    private static PlaceholderFixture importPlaceholderFixture(
            Path root, JsonObject materialization, JsonElement evidence,
            boolean falselyReportSymbolized, String environmentCell)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.TimeHandler: long handle()>";
        String inputPort = "REGION.TIME.in.0";

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.TIME");
        activation.addProperty("regionId", "REGION.TIME");
        activation.addProperty("regionInstanceId",
                "REGION.TIME@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        slice.addProperty("outputPort", "REGION.TIME.out.0");
        slice.add("inputPorts", singletonString(inputPort));
        slice.add("methods", singletonString(method));
        activation.add("requestedOutputSlice", slice);
        JsonObject declared = new JsonObject();
        declared.addProperty("symbol", inputPort);
        declared.addProperty("cell", environmentCell);
        declared.addProperty("sourceKind", "ENVIRONMENT");
        declared.addProperty("location", "ENVIRONMENT_MODEL");
        JsonArray symbolize = new JsonArray();
        symbolize.add(declared);
        activation.add("symbolize", symbolize);
        JsonArray materializations = new JsonArray();
        if (materialization != null) {
            materializations.add(materialization.deepCopy());
        }
        activation.add("materializations", materializations);
        JsonObject requestedOutput = new JsonObject();
        requestedOutput.addProperty("portId", "REGION.TIME.out.0");
        requestedOutput.addProperty("kind", "PRIMITIVE");
        activation.add("requestedOutput", requestedOutput);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.TIME.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        JsonArray outputs = new JsonArray();
        outputs.add(outputAction);
        activation.add("outputs", outputs);
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.TIME");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        write(regions, region + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.TIME");
        raw.addProperty("regionId", "REGION.TIME");
        raw.addProperty("exitKind", "NORMAL");
        JsonArray symbolizedInputs = new JsonArray();
        if (falselyReportSymbolized) {
            symbolizedInputs.add(inputPort);
        }
        raw.add("symbolizedInputs", symbolizedInputs);
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("rootOutputExpression", constant("Y_J_1", "J"));
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.TIME");
        engine.addProperty("activationId", "ACT.TIME");
        JsonArray path = new JsonArray();
        path.add(evidence.deepCopy());
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics, root.resolve("cache"));
        JsonObject summary = JsonParser.parseString(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        return new PlaceholderFixture(summary, new String(
                Files.readAllBytes(diagnostics), StandardCharsets.UTF_8));
    }

    private static JsonObject exactCurrentTimePlaceholderMaterialization() {
        return exactCurrentTimePlaceholderMaterialization(
                "<java.lang.System: long currentTimeMillis()>.return");
    }

    private static JsonObject exactCurrentTimePlaceholderMaterialization(
            String environmentCell) {
        JsonObject result = new JsonObject();
        result.addProperty("symbol", "REGION.TIME.in.0");
        result.addProperty("cell", environmentCell);
        result.addProperty("sourceKind", "ENVIRONMENT");
        result.addProperty("location", "ENVIRONMENT_MODEL");
        result.addProperty("bindingMode", "VM_INTRINSIC_PLACEHOLDER");
        result.addProperty("placeholderFunction", "currentTimeMills");
        result.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        result.addProperty("modelControllable", false);
        result.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        return result;
    }

    private static JsonObject placeholderExpression(String function,
                                                    int count) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "PlaceholderExpression");
        result.addProperty("_java_type", "J");
        result.addProperty("_place_holder_func", function);
        result.addProperty("_count", count);
        return result;
    }

    private static JsonObject placeholderCondition(JsonElement placeholder) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", ">");
        result.add("_left", placeholder.deepCopy());
        result.add("_right", constant("Y_J_0", "J"));
        result.addProperty("_code_position",
                "virtual long example.TimeHandler.handle():12");
        return result;
    }

    private static MapFixture importGuardedNoRemoveFixture(
            Path root, JsonElement observations, JsonArray symbolize,
            JsonElement fieldObservations) throws Exception {
        String prune = "<example.Store: void prune()>";
        JsonArray canonicalFields = new JsonArray();
        JsonArray dynamicBindings = new JsonArray();
        JsonArray mappings = readGuardMappings(prune);
        if (observations != null && observations.isJsonArray()) {
            JsonObject read = null;
            for (JsonElement element : observations.getAsJsonArray()) {
                if (element.isJsonObject()
                        && "MAP_ENTRY_READ".equals(element.getAsJsonObject()
                        .get("kind").getAsString())) {
                    read = element.getAsJsonObject();
                    break;
                }
            }
            if (read != null) {
                String site = prune + "#u3";
                String dynamic = dynamicFieldSymbol(
                        "REGION.P.in.1", site, 1);
                long leafToken = read.get("valueObjectToken").getAsLong();
                if (fieldObservations != null
                        && fieldObservations.isJsonArray()
                        && fieldObservations.getAsJsonArray().size() == 1
                        && fieldObservations.getAsJsonArray().get(0)
                        .isJsonObject()
                        && fieldObservations.getAsJsonArray().get(0)
                        .getAsJsonObject().has("leafOwnerObjectToken")) {
                    leafToken = fieldObservations.getAsJsonArray().get(0)
                            .getAsJsonObject().get("leafOwnerObjectToken")
                            .getAsLong();
                }
                dynamicBindings.add(dynamicFieldBinding(dynamic, site, 1,
                        leafToken, read, read.getAsJsonObject(
                        "keyExpression")));
                canonicalFields.add(dynamicFieldObservation(dynamic, site,
                        1, leafToken, read));
                mappings = new JsonArray();
                mappings.add(branchMapping(prune, 4, 1, true,
                        symbol("M_J_field_" + dynamic
                                + "_example/Value", "J")));
            }
        }
        return importMapFixture(root, new JsonArray(), true,
                new JsonArray(), singletonString(prune),
                guardedWriteEdges(prune), observations,
                symbolize, mappings, canonicalFields, dynamicBindings);
    }

    private static JsonObject mapInputExpression() {
        return symbol("M_L_field_REGION.P.in.0_example/Store", "L");
    }

    private static JsonArray singletonString(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonInteger(int value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonObject(JsonObject value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray guardedWriteEdges(String method) {
        JsonArray edges = new JsonArray();
        edges.add(causalEdge("DF.WRITE.READ", method, method + "#u5",
                "HEAP_WRITE", "field_mutation"));
        edges.add(guardedMutationEdge("DF.GUARD.READ", method,
                4, 5, false));
        return edges;
    }

    private static JsonArray readGuardMappings(String method) {
        JsonArray mappings = new JsonArray();
        mappings.add(branchMapping(method, 4, 1, true,
                symbol("M_J_field_REGION.P.in.1_expiry", "J")));
        return mappings;
    }

    private static JsonArray defaultReadSymbolize() {
        JsonArray actions = new JsonArray();
        actions.add(fieldAccessAction("REGION.P.in.1", "expiry"));
        return actions;
    }

    private static JsonArray tokenFieldObservations(long ownerToken) {
        JsonObject observation = fieldObservation(
                "REGION.P.in.1", "expiry", 42);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("leafOwnerObjectToken", ownerToken);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("leafOwnerClass", "example.Value");
        JsonArray result = new JsonArray();
        result.add(observation);
        return result;
    }

    private static JsonObject dynamicFieldBinding(
            String dynamicSymbol, String siteId, int occurrence,
            long ownerToken, JsonObject entryRead, JsonObject keyExpression) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicSymbol);
        binding.addProperty("baseInputSymbol", "REGION.P.in.1");
        binding.addProperty("dynamicFieldSymbol", dynamicSymbol);
        binding.addProperty("materializationSiteId", siteId);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        JsonArray path = new JsonArray();
        path.add("expiry");
        binding.add("fieldPath", path);
        binding.addProperty("leafOwnerObjectToken", ownerToken);
        binding.addProperty("entryValueOwnerObjectToken",
                entryRead.get("valueObjectToken").getAsLong());
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.P");
        binding.addProperty("entryReadObservationId",
                entryRead.get("observationId").getAsString());
        binding.add("keyExpression", keyExpression.deepCopy());
        binding.addProperty("keyExpressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT");
        binding.addProperty("complete", true);
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        return binding;
    }

    private static JsonObject dynamicFieldObservation(
            String dynamicSymbol, String siteId, int occurrence,
            long ownerToken, JsonObject entryRead) {
        JsonObject observation = new JsonObject();
        observation.addProperty("symbol", dynamicSymbol);
        observation.addProperty("baseInputSymbol", "REGION.P.in.1");
        observation.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicSymbol);
        observation.addProperty("dynamicFieldSymbol", dynamicSymbol);
        observation.addProperty("materializationSiteId", siteId);
        observation.addProperty("materializationOccurrence", occurrence);
        observation.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        JsonArray path = new JsonArray();
        path.add("expiry");
        observation.add("fieldPath", path.deepCopy());
        observation.add("path", path.deepCopy());
        observation.addProperty("phase", "AT_MATERIALIZATION");
        observation.addProperty("available", true);
        observation.addProperty("leafOwnerObjectToken", ownerToken);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("accessOwnerObjectToken",
                entryRead.get("valueObjectToken").getAsLong());
        observation.addProperty("accessOwnerObjectTokenKnown", true);
        observation.addProperty("leafOwnerClass", "example.Value");
        observation.addProperty("entryReadObservationId",
                entryRead.get("observationId").getAsString());
        JsonArray readIds = new JsonArray();
        readIds.add(entryRead.get("observationId").getAsString());
        observation.add("entryReadObservationIds", readIds);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("dynamicFieldBindingAuthority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        observation.addProperty("dynamicFieldBindingComplete", true);
        observation.addProperty("complete", true);
        return observation;
    }

    private static MapFixture importNonMutatingDynamicMapReadFixture(
            Path root, String mode) throws Exception {
        String method = "<example.Store: void prune()>";
        String base = "REGION.P.in.1";
        String materializationSite = method + "#u8";
        String dependencyCell =
                "<example.State: example.Guard state>"
                        + "#field:guard#field:expiry";
        String dynamic = dynamicFieldSymbol(base, materializationSite, 1);
        JsonObject key = constant("Y_I_7", "I");
        JsonObject witness = mapRefWitnessRecord();
        JsonObject read = runtimeMapEntryRead(witness.get("mapExpression"),
                key, method, 4, 0, 1, 1);
        for (java.util.Map.Entry<String, JsonElement> entry
                : witness.entrySet()) {
            read.add(entry.getKey(), entry.getValue().deepCopy());
        }
        JsonArray observations = new JsonArray();
        observations.add(read);

        JsonArray deepPath = strings("state", "guard", "expiry");
        JsonObject dynamicBinding = dynamicFieldBinding(dynamic,
                materializationSite, 1, 105L, read, key);
        dynamicBinding.add("fieldPath", deepPath.deepCopy());
        JsonArray dynamicBindings = new JsonArray();
        dynamicBindings.add(dynamicBinding);
        JsonObject fieldObservation = dynamicFieldObservation(dynamic,
                materializationSite, 1, 105L, read);
        fieldObservation.add("fieldPath", deepPath.deepCopy());
        fieldObservation.add("path", deepPath.deepCopy());
        JsonArray fieldObservations = new JsonArray();
        fieldObservations.add(fieldObservation);

        JsonObject action = fieldAccessAction(base, "expiry");
        action.addProperty("cell", dependencyCell);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("accessMethod", method);
        action.addProperty("accessSiteId", materializationSite);
        action.addProperty("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        action.addProperty("leafFieldSignature",
                "<example.Value: long expiry>");
        action.add("fieldPath", deepPath.deepCopy());
        JsonArray actions = new JsonArray();
        actions.add(action);

        JsonObject expression = symbol("M_J_field_" + dynamic
                + "_example/Value", "J");
        JsonObject condition = binaryCondition(
                "virtual void example.Store.prune():11", ">",
                expression, constant("Y_J_0", "J"));
        JsonArray path = new JsonArray();
        path.add(condition.deepCopy());
        JsonObject mapping = branchMapping(method, 11, 1, true,
                condition);
        mapping.addProperty("vmOccurrence", 1);
        mapping.addProperty("conditionIndex", 0);
        mapping.addProperty("rawConditionIndex", 0);
        mapping.addProperty("engineConditionIndex", 0);
        mapping.addProperty("pathConditionBaseline", 0);
        mapping.addProperty("rawPathConditionBaseline", 0);
        mapping.addProperty("enginePathConditionBaseline", 0);
        mapping.addProperty("pathConditionSize", 1);
        mapping.addProperty("rawPathConditionSize", 1);
        mapping.addProperty("enginePathConditionSize", 1);
        mapping.addProperty("mappingPolicy",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
        mapping.addProperty("conditionAuthority",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
        mapping.addProperty("vmBranchEventExpected", true);
        mapping.addProperty("vmBranchEventValidated",
                !"INVALID_VM_MAPPING".equals(mode));
        mapping.addProperty("vmBranchEventId", 1);
        mapping.addProperty("vmBranchEventAuthority",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
        mapping.addProperty("vmThreadContextId", 2);
        mapping.addProperty("vmOwnerJavaThreadId", 3);
        mapping.addProperty("vmOwnerOsThreadId", 4);
        mapping.addProperty("overrideMode", "NONE");
        mapping.add("vmConditionIndices", singletonInteger(0));
        mapping.add("rawCondition", condition.deepCopy());
        mapping.add("condition", condition.deepCopy());
        if (!"INVALID_VM_MAPPING".equals(mode)) {
            JsonObject vmEvent = new JsonObject();
            vmEvent.addProperty("authority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
            vmEvent.addProperty("contextId", 2L);
            vmEvent.addProperty("eventId", 1L);
            vmEvent.addProperty("opcode", 153);
            vmEvent.addProperty("ownerJavaThreadId", 3L);
            vmEvent.addProperty("ownerOsThreadId", 4L);
            vmEvent.addProperty("codePosition",
                    condition.get("_code_position").getAsString());
            vmEvent.addProperty("predicateNormalization", "IDENTITY");
            mapping.add("witness", BranchWitness.vmPc(
                    method + "#u11", method, 11, 1, true,
                    condition, 0, vmEvent).toJson());
        }
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        if ("DUPLICATE_VM_MAPPING".equals(mode)) {
            JsonObject duplicate = mapping.deepCopy();
            duplicate.addProperty("vmBranchEventId", 2);
            mappings.add(duplicate);
        }

        JsonObject inputBinding = new JsonObject();
        inputBinding.addProperty("dependencyCell", dependencyCell);
        inputBinding.addProperty("inputPort", base);
        inputBinding.addProperty("bindingAuthority",
                "INVALID_SLICE_BINDING".equals(mode)
                        ? "ALIAS_HEURISTIC" : "EXACT_CELL_IDENTITY");
        inputBinding.add("dependencyMethods", singletonString(method));
        JsonObject slice = new JsonObject();
        slice.addProperty("structuralComplete", true);
        slice.addProperty("truncated", false);
        slice.add("inputBindings", singletonObject(inputBinding));
        slice.add("sites", strings(method + "#u4", materializationSite,
                method + "#u11"));
        slice.addProperty("_fixtureRequestedOutputCell",
                "<example.Output: int result>");

        JsonArray causalEdges = new JsonArray();
        causalEdges.add(causalEdge("DF.READ.NON_MUTATING", method,
                materializationSite, "HEAP_READ", "field_read"));

        return importMapFixture(root, path, true, new JsonArray(),
                singletonString(method), causalEdges,
                observations, actions, mappings, fieldObservations,
                dynamicBindings, slice, new JsonArray());
    }

    private static MapFixture importRawExpiryFallbackFixture(
            Path root, String mutation) throws Exception {
        String prune = "<example.Store: void prune()>";
        String site = "<example.Value: long getExpiry()>#u1";
        JsonObject map = mapInputExpression();
        JsonObject firstKey = symbol("entryKey1", "I");
        JsonObject secondKey = symbol("entryKey2", "I");
        JsonObject firstRead = runtimeMapEntryRead(map, firstKey, prune,
                3, 1, 1, 1);
        JsonObject secondRead = runtimeMapEntryRead(map, secondKey, prune,
                3, "DUPLICATE_RAW".equals(mutation) ? 1 : 2, 2, 2);
        secondRead.addProperty("keyObjectToken", 202L);
        secondRead.addProperty("valueObjectToken", 203L);
        secondRead.addProperty("entryObjectToken", 204L);
        JsonArray reads = new JsonArray();
        reads.add(firstRead);
        reads.add(secondRead);

        String firstDynamic = dynamicFieldSymbol("REGION.P.in.1", site, 1);
        String secondDynamic = dynamicFieldSymbol("REGION.P.in.1", site, 2);
        JsonArray bindings = new JsonArray();
        JsonObject firstBinding = dynamicFieldBinding(firstDynamic, site, 1,
                103L, firstRead, firstKey);
        bindings.add(firstBinding);
        bindings.add(dynamicFieldBinding(secondDynamic, site, 2, 203L,
                secondRead, secondKey));
        if ("DUPLICATE_DYNAMIC".equals(mutation)) {
            bindings.add(firstBinding.deepCopy());
        } else if ("WRONG_ENTRY_VALUE_OWNER".equals(mutation)) {
            firstBinding.addProperty("entryValueOwnerObjectToken", 999L);
        }
        JsonArray fields = new JsonArray();
        fields.add(dynamicFieldObservation(firstDynamic, site, 1, 103L,
                firstRead));
        fields.add(dynamicFieldObservation(secondDynamic, site, 2, 203L,
                secondRead));

        JsonObject firstExpression = symbol(
                "M_J_field_" + firstDynamic + "_example/Value", "J");
        JsonObject secondExpression = symbol(
                "M_J_field_" + secondDynamic + "_example/Value", "J");
        JsonObject candidate = binaryCondition(
                "virtual void example.Store.prune():187", ">",
                firstExpression, "DUPLICATE_RAW".equals(mutation)
                        ? secondExpression : constant("Y_J_0", "J"));
        String siblingDynamic = "DUPLICATE_RAW".equals(mutation)
                ? dynamicFieldSymbol("REGION.P.in.1", site, 3)
                : secondDynamic;
        JsonObject siblingRaw = binaryCondition(
                "virtual void example.Store.prune():187", ">",
                symbol("M_J_field_" + siblingDynamic
                        + "_example/Value", "J"), constant("Y_J_0", "J"));
        JsonObject siblingSemantic = siblingRaw.deepCopy();
        siblingSemantic.addProperty("_op",
                "MALFORMED_OPERATOR".equals(mutation) ? "" : ">=");
        JsonArray path = new JsonArray();
        path.add(binaryCondition(
                "virtual void example.Store.prune():185", "!=",
                symbol("hasNext", "Z"), constant("Y_I_0", "I")));
        path.add(candidate);
        path.add(siblingRaw);

        JsonArray mappings = new JsonArray();
        mappings.add(unmappedBranchMapping(prune, 4, 1, 0, 2));
        if ("DUPLICATE_RAW".equals(mutation)) {
            mappings.add(unmappedBranchMapping(prune, 4, 2, 0, 2));
        }
        JsonObject sibling = branchMapping(prune, 4,
                "DUPLICATE_RAW".equals(mutation) ? 3 : 2,
                true, siblingSemantic);
        sibling.addProperty("conditionIndex", 2);
        sibling.addProperty("rawConditionIndex", 2);
        sibling.addProperty("engineConditionIndex", 2);
        sibling.add("rawCondition", siblingRaw.deepCopy());
        sibling.addProperty("conditionCodePosition",
                "virtual void example.Store.prune():187");
        sibling.addProperty("conditionNormalization",
                "JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE");
        mappings.add(sibling);

        return importMapFixture(root, path, true, new JsonArray(),
                singletonString(prune), guardedWriteEdges(prune),
                reads, defaultReadSymbolize(), mappings,
                fields, bindings);
    }

    private static JsonObject unmappedBranchMapping(
            String method, int unit, int occurrence,
            int baseline, int boundary) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", method + "#u" + unit);
        mapping.addProperty("method", method);
        mapping.addProperty("unitIndex", unit);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", true);
        mapping.addProperty("observedOutcome", true);
        mapping.addProperty("effectiveOutcome", true);
        mapping.addProperty("overrideApplied", false);
        mapping.addProperty("conditionIndex", -1);
        mapping.addProperty("rawConditionIndex", -1);
        mapping.addProperty("rawPathConditionBaseline", baseline);
        mapping.addProperty("enginePathConditionBaseline", baseline);
        mapping.addProperty("rawPathConditionSize", boundary);
        mapping.addProperty("enginePathConditionSize", boundary);
        return mapping;
    }

    private static JsonObject binaryCondition(
            String codePosition, String operator,
            JsonElement left, JsonElement right) {
        JsonObject condition = new JsonObject();
        condition.addProperty("_code_position", codePosition);
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_op", operator);
        condition.add("_left", left.deepCopy());
        condition.add("_right", right.deepCopy());
        return condition;
    }

    private static String dynamicFieldSymbol(String base, String siteId,
                                             int occurrence)
            throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] bytes = digest.digest(siteId.getBytes(StandardCharsets.UTF_8));
        StringBuilder hash = new StringBuilder();
        for (byte item : bytes) {
            hash.append(String.format("%02x", item & 0xff));
        }
        return base + ".field." + hash.substring(0, 12) + ".occ."
                + occurrence;
    }

    private static MapFixture importContainerDynamicFixture(
            Path root, String mutation) throws Exception {
        String base = "REGION.P.in.1";
        String containerPort = "REGION.P.in.2";
        String field = "<example.Value: long expiry>";
        String containerCell =
                "<example.Envelope: example.Value[] values>";
        String site = "<example.Store: void update()>#u6";
        int occurrence = 1;
        int elementIndex = 2;
        String dynamic = dynamicFieldSymbol(base, site, occurrence);

        JsonArray actions = new JsonArray();
        actions.add(fieldAccessAction(base, "expiry"));
        JsonObject containerAction = new JsonObject();
        containerAction.addProperty("symbol", containerPort);
        containerAction.addProperty("bindingMode", "FIELD_ACCESS");
        containerAction.addProperty("field", containerCell);
        containerAction.addProperty("cell", containerCell);
        containerAction.add("fieldPath",
                JsonParser.parseString("[\"values\"]"));
        actions.add(containerAction);

        boolean discovery = "VALID_DISCOVERY".equals(mutation);
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind", "ARRAY_ELEMENT_FIELD");
        declaration.addProperty("bindingId", "CONTAINER.FIELD.0");
        declaration.addProperty("baseInputSymbol", base);
        declaration.addProperty("containerInputPort", containerPort);
        declaration.addProperty("containerInputCell", containerCell);
        declaration.addProperty("selectorAuthority", discovery
                ? "DISCOVER_UNIQUE_IDENTITY_INDEX" : "EXACT_ARRAY_INDEX");
        declaration.addProperty("elementIndex",
                discovery ? -1 : elementIndex);
        declaration.addProperty("elementOccurrence",
                discovery ? -1 : occurrence);
        declaration.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        declaration.addProperty("fieldMaterializationSiteId", site);
        declaration.addProperty("declaredFieldOwnerClass",
                "example.Value");
        declaration.addProperty("declaredFieldType", "long");
        JsonArray declarations = singletonObject(declaration);

        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "CONTAINER.FIELD.0");
        selector.addProperty("containerInputPort", containerPort);
        selector.addProperty("containerInputCell", containerCell);
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority", discovery
                ? "DISCOVER_UNIQUE_IDENTITY_INDEX" : "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", elementIndex);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Value");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("containerObjectToken", 201L);
        selector.addProperty("elementObjectToken", 202L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.P");
        selector.addProperty("containerObservationLocation",
                "FIELD_ACCESS");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);

        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        addContainerSiteBridge(binding, site, occurrence,
                "CONTAINER.FIELD.0", 202L);
        binding.addProperty("fieldSignature", field);
        binding.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        binding.addProperty("leafOwnerObjectToken", 202L);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.P");
        binding.add("containerSelector", selector.deepCopy());
        addContainerSelectorFlatFields(binding, selector);
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                        + "AND_STABLE_FIELD_SITE_OCCURRENCE");
        binding.addProperty("complete", true);
        JsonArray bindings = singletonObject(binding);

        JsonObject observation = new JsonObject();
        observation.addProperty("symbol", dynamic);
        observation.addProperty("phase", "AT_MATERIALIZATION");
        observation.add("path",
                JsonParser.parseString("[\"expiry\"]"));
        observation.addProperty("available", true);
        observation.addProperty("leafOwnerObjectToken", 202L);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("baseInputSymbol", base);
        observation.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        observation.addProperty("dynamicFieldSymbol", dynamic);
        observation.addProperty("materializationSiteId", site);
        observation.addProperty("materializationOccurrence", occurrence);
        addContainerSiteBridge(observation, site, occurrence,
                "CONTAINER.FIELD.0", 202L);
        observation.addProperty("dynamicFieldBindingSchemaVersion", 2);
        observation.addProperty("dynamicFieldBindingKind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        observation.addProperty("fieldSignature", field);
        observation.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        observation.add("containerSelector", selector.deepCopy());
        addContainerSelectorFlatFields(observation, selector);
        observation.addProperty("dynamicFieldBindingAuthority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                        + "AND_STABLE_FIELD_SITE_OCCURRENCE");
        observation.addProperty("dynamicFieldBindingComplete", true);
        observation.addProperty("complete", true);
        JsonArray observations = singletonObject(observation);

        JsonArray mappings = new JsonArray();
        JsonObject consumerKey = symbol(
                "M_J_field_" + dynamic + "_example/Value", "J");
        JsonArray semanticPath = new JsonArray();
        semanticPath.add(methodExpression("java/util/HashMap put", 19,
                mapInputExpression(), consumerKey.deepCopy(),
                symbol("putValue", "example/Value")));
        mappings.add(branchMapping("<example.Store: void update()>", 6,
                occurrence, true, symbol(
                        "M_J_field_" + dynamic + "_expiry", "J")));

        if ("WRONG_DECLARATION".equals(mutation)) {
            declaration.remove("fieldMaterializationSiteId");
        } else if ("WRONG_INDEX".equals(mutation)) {
            binding.getAsJsonObject("containerSelector").addProperty(
                    "elementIndex", elementIndex + 1);
        } else if ("WRONG_CELL".equals(mutation)) {
            declaration.addProperty("containerInputCell",
                    "<example.Envelope: example.Value[] other>");
        } else if ("WRONG_TOKEN".equals(mutation)) {
            binding.addProperty("leafOwnerObjectToken", 999L);
        } else if ("WRONG_SCOPE".equals(mutation)) {
            binding.addProperty("objectTokenScope", "ACT.OTHER");
        } else if ("DUPLICATE".equals(mutation)) {
            bindings.add(binding.deepCopy());
        } else if ("MIXED_MAP_SELECTOR".equals(mutation)) {
            binding.addProperty("entryReadObservationId", "MAP.READ.0");
            binding.add("keyExpression", symbol("entryKey", "I"));
        } else if ("MISSING_OBSERVATION".equals(mutation)) {
            observations = new JsonArray();
        } else if ("MISSING_MAP_PUT_CONSUMER".equals(mutation)) {
            semanticPath = new JsonArray();
        } else if ("WRONG_BRIDGE_AUTHORITY".equals(mutation)) {
            binding.addProperty("materializationSiteBridgeAuthority",
                    "UNTRUSTED_BRIDGE");
        } else if ("WRONG_ACTUAL_HOOK_SITE".equals(mutation)) {
            binding.addProperty("actualHookSiteId", "not-a-hook-site");
        } else if ("AMBIGUOUS_MAP_PUT_CONSUMER".equals(mutation)) {
            semanticPath.add(methodExpression("java/util/HashMap put", 20,
                    mapInputExpression(), consumerKey.deepCopy(),
                    symbol("putValue2", "example/Value")));
        }

        return importMapFixture(root, semanticPath, true,
                new JsonArray(), new JsonArray(), new JsonArray(), null,
                actions, mappings, observations, bindings, null,
                new JsonArray(), declarations);
    }

    private static void addContainerSiteBridge(
            JsonObject target, String effectiveSite,
            int effectiveOccurrence, String bindingId,
            long elementObjectToken) {
        target.addProperty("actualHookSiteId", effectiveSite);
        target.addProperty("actualHookOccurrence", effectiveOccurrence);
        target.addProperty("effectiveMaterializationSiteId",
                effectiveSite);
        target.addProperty("effectiveMaterializationOccurrence",
                effectiveOccurrence);
        target.addProperty("materializationSiteBridgeAuthority",
                "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_EXACT_"
                        + "ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1");
        target.addProperty("materializationSiteBridgeBindingId", bindingId);
        target.addProperty(
                "materializationSiteBridgeElementObjectToken",
                elementObjectToken);
        target.addProperty("materializationSiteBridgeObjectTokenScope",
                "ACT.P");
    }

    private static void addContainerSelectorFlatFields(
            JsonObject target, JsonObject selector) {
        target.addProperty("containerBindingId",
                selector.get("bindingId").getAsString());
        target.addProperty("containerInputPort",
                selector.get("containerInputPort").getAsString());
        target.addProperty("containerInputCell",
                selector.get("containerInputCell").getAsString());
        target.addProperty("selectorAuthority",
                selector.get("selectorAuthority").getAsString());
        target.addProperty("resolvedFromSelectorAuthority",
                selector.get("resolvedFromSelectorAuthority").getAsString());
        target.addProperty("elementIndex",
                selector.get("elementIndex").getAsInt());
        target.addProperty("elementOccurrence",
                selector.get("elementOccurrence").getAsInt());
        target.addProperty("declaredFieldOwnerClass",
                selector.get("declaredFieldOwnerClass").getAsString());
        target.addProperty("declaredFieldType",
                selector.get("declaredFieldType").getAsString());
    }

    private static JsonObject inputAction(String symbol, String cell) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("field", cell);
        return action;
    }

    private static JsonObject runtimeMapEntryRead(
            JsonElement mapExpression, JsonElement keyExpression,
            String originMethod, int originUnitIndex, int pcBoundary,
            int occurrence, long eventSequence) {
        String siteId = originMethod + "#u" + originUnitIndex;
        JsonObject observation = new JsonObject();
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("operation", "java.util.Iterator.next");
        observation.addProperty("observationId",
                "MAP_ENTRY_READ:" + siteId + "#" + occurrence);
        observation.addProperty("eventSequence", eventSequence);
        observation.addProperty("occurrence", occurrence);
        observation.addProperty("originMethod", originMethod);
        observation.addProperty("originUnitIndex", originUnitIndex);
        observation.addProperty("siteId", siteId);
        observation.addProperty("viewKind", "ENTRY_SET");
        observation.addProperty("rawPathConditionBoundary", pcBoundary);
        observation.addProperty("pcBoundary", pcBoundary);
        observation.addProperty("provenanceAuthority",
                "ACTIVATION_LOCAL_BACKED_ENTRY_SET_IDENTITY_AT_NEXT");
        observation.addProperty("mapBindingAuthority",
                "BOUND_ENTRY_SET_VIEW_BACKING_MAP_IDENTITY");
        observation.addProperty("entryBindingAuthority",
                "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT");
        observation.addProperty("keyBindingAuthority",
                "SAME_MAP_ENTRY_GET_KEY_AT_NEXT");
        observation.addProperty("valueBindingAuthority",
                "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT");
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("expressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT");
        observation.addProperty("keyExpressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT");
        observation.addProperty("valueExpressionAuthority",
                "AFTER_MATCHED_FIELD_SYMBOLIZATION");
        observation.addProperty("backingMapObjectToken", 101L);
        observation.addProperty("backingMapObjectTokenKnown", true);
        observation.addProperty("entryObjectToken", 104L);
        observation.addProperty("entryObjectTokenKnown", true);
        observation.addProperty("entryWasNull", false);
        observation.addProperty("keyObjectToken", 102L);
        observation.addProperty("keyObjectTokenKnown", true);
        observation.addProperty("keyWasNull", false);
        observation.addProperty("valueObjectToken", 103L);
        observation.addProperty("valueObjectTokenKnown", true);
        observation.addProperty("valueWasNull", false);
        observation.add("mapExpression", mapExpression.deepCopy());
        observation.add("keyExpression", keyExpression.deepCopy());
        observation.add("valueExpression",
                symbol("expiredValue", "example/Value"));
        observation.addProperty("entryBindingComplete", true);
        observation.addProperty("expressionBindingComplete", true);
        observation.addProperty("objectTokenBindingComplete", true);
        observation.addProperty("bindingAuthorityComplete", true);
        observation.addProperty("runtimeProvenanceComplete", true);
        observation.addProperty("complete", true);
        return observation;
    }

    private static JsonObject runtimeFiniteMapEntrySnapshot(
            JsonElement mapExpression, JsonElement keyExpression,
            String originMethod, int originUnitIndex, int occurrence,
            long eventSequence) {
        String siteId = originMethod + "#u" + originUnitIndex;
        JsonObject valueExpression = new JsonObject();
        valueExpression.addProperty("_type", "SymbolExpression");
        valueExpression.addProperty("_java_type", "L");
        valueExpression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T103");
        JsonObject entry = new JsonObject();
        entry.addProperty("index", 0);
        entry.add("keyExpression", keyExpression.deepCopy());
        entry.addProperty("keyObjectToken", 102L);
        entry.add("valueExpression", valueExpression.deepCopy());
        entry.addProperty("valueObjectToken", 103L);
        entry.addProperty("valueWasNull", false);
        entry.addProperty("valueExpressionAuthority",
                "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1");

        JsonObject snapshot = new JsonObject();
        snapshot.addProperty("schemaVersion", 1);
        snapshot.addProperty("kind", "FINITE_MAP_ENTRY_SNAPSHOT");
        snapshot.addProperty("operation", "java.util.Map.entrySet");
        snapshot.addProperty("observationId",
                "FINITE_MAP_ENTRY_SNAPSHOT:" + siteId + "#" + occurrence);
        snapshot.addProperty("eventSequence", eventSequence);
        snapshot.addProperty("eventSequenceAuthority",
                "SAME_ITERATOR_NEXT_AS_MAP_ENTRY_READ");
        snapshot.addProperty("originMethod", originMethod);
        snapshot.addProperty("originUnitIndex", originUnitIndex);
        snapshot.addProperty("siteId", siteId);
        snapshot.addProperty("viewKind", "ENTRY_SET");
        snapshot.addProperty("viewOriginSiteId", originMethod + "#u1");
        snapshot.addProperty("iteratorOriginSiteId", originMethod + "#u2");
        snapshot.addProperty("mapImplementationClass",
                "java.util.HashMap");
        snapshot.addProperty("mapImplementationAuthority",
                "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                        + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1");
        snapshot.addProperty("mapObjectToken", 101L);
        snapshot.addProperty("backingMapObjectToken", 101L);
        snapshot.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        snapshot.addProperty("objectTokenScope", "ACT.P");
        snapshot.add("mapExpression", mapExpression.deepCopy());
        snapshot.addProperty("mapExpressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_FIRST_ENTRY_SET_NEXT");
        snapshot.addProperty("entryCount", 1);
        snapshot.addProperty("finiteEntryBound", 4096);
        snapshot.addProperty("sizeBefore", 1);
        snapshot.addProperty("entrySetSizeBefore", 1);
        snapshot.addProperty("sizeAfter", 1);
        snapshot.addProperty("entrySetSizeAfter", 1);
        JsonArray keys = new JsonArray();
        keys.add(keyExpression.deepCopy());
        snapshot.add("keyExpressions", keys);
        JsonArray keyTokens = new JsonArray();
        keyTokens.add(102L);
        snapshot.add("keyObjectTokens", keyTokens);
        snapshot.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEYS_AT_SAME_EXECUTION_"
                        + "ENTRY_SET_SNAPSHOT");
        JsonArray valueTokens = new JsonArray();
        valueTokens.add(103L);
        snapshot.add("valueObjectTokens", valueTokens);
        JsonArray values = new JsonArray();
        values.add(valueExpression.deepCopy());
        snapshot.add("valueExpressions", values);
        snapshot.addProperty("valueExpressionAuthority",
                "PER_ENTRY_EXACT_RUNTIME_NULL_OR_ACTIVATION_LOCAL_OBJECT_"
                        + "TOKEN_REF_WITNESS_V1");
        JsonArray entries = new JsonArray();
        entries.add(entry);
        snapshot.add("entries", entries);
        snapshot.addProperty("keysDistinct", true);
        snapshot.addProperty("firstIteratorEntryMatched", true);
        snapshot.addProperty("sizeStable", true);
        snapshot.addProperty("entrySetStable", true);
        snapshot.addProperty("authority",
                "FIRST_BOUND_ENTRY_SET_ITERATOR_NEXT_EXACT_HASHMAP_OR_"
                        + "LINKEDHASHMAP_SAME_EXECUTION_AT_ITERATOR_NEXT_"
                        + "STABLE_SIZE_"
                        + "AND_ENTRY_SET_DISTINCT_IMMUTABLE_KEYS_V1");
        snapshot.addProperty("complete", true);
        return snapshot;
    }

    private static MapFixture importMapFixture(Path root, JsonArray path)
            throws Exception {
        return importMapFixture(root, path, true, new JsonArray());
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, new JsonArray(), new JsonArray());
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                null, new JsonArray(), null, null, null,
                null, new JsonArray(), null, null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                null, additionalSymbolize, branchMappings,
                fieldObservations, null, null, new JsonArray(), null,
                null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                runtimeHeapObservations,
                additionalSymbolize, branchMappings, fieldObservations,
                dynamicFieldBindings, null, new JsonArray());
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings,
                                               JsonObject sliceMetadata,
                                               JsonArray omittedSymbolizedInputs)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                runtimeHeapObservations,
                additionalSymbolize, branchMappings, fieldObservations,
                dynamicFieldBindings, sliceMetadata,
                omittedSymbolizedInputs, null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings,
                                               JsonObject sliceMetadata,
                                               JsonArray omittedSymbolizedInputs,
                                               JsonElement containerBindings)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                runtimeHeapObservations,
                additionalSymbolize, branchMappings, fieldObservations,
                dynamicFieldBindings, sliceMetadata,
                omittedSymbolizedInputs, containerBindings, null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings,
                                               JsonObject sliceMetadata,
                                               JsonArray omittedSymbolizedInputs,
                                               JsonElement containerBindings,
                                               JsonElement engineArrayBindings)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.Store: void update()>";
        String cell = "<example.Store: java.util.Map data>";
        if (sliceMetadata != null
                && sliceMetadata.has("_fixtureRequestedOutputCell")) {
            cell = sliceMetadata.get("_fixtureRequestedOutputCell")
                    .getAsString();
        }
        if (sliceMetadata != null
                && sliceMetadata.has(
                "captureDischargedByHeapEffectTransformer")
                && sliceMetadata.get(
                "captureDischargedByHeapEffectTransformer")
                .getAsBoolean()
                && sliceMetadata.has("captureDischargeOutputCell")) {
            cell = sliceMetadata.get("captureDischargeOutputCell")
                    .getAsString();
        }

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.P");
        activation.addProperty("regionId", "REGION.P");
        activation.addProperty("regionInstanceId",
                "REGION.P@fixture#call10");
        activation.addProperty("rootCallId", 10);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("rootMethod", method);
        JsonArray requestedOutputMethods = new JsonArray();
        requestedOutputMethods.add(method);
        for (JsonElement sliceMethod : sliceMethods) {
            if (sliceMethod.isJsonPrimitive()
                    && !containsString(requestedOutputMethods,
                    sliceMethod.getAsString())) {
                requestedOutputMethods.add(sliceMethod.getAsString());
            }
        }
        activation.add("requestedOutputMethods", requestedOutputMethods);
        JsonArray symbolize = new JsonArray();
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.P.in.0");
        input.addProperty("cell", cell);
        input.addProperty("field", cell);
        if (existingMapInput) {
            symbolize.add(input);
        }
        for (JsonElement action : additionalSymbolize) {
            symbolize.add(action.deepCopy());
        }
        if (containerBindings != null) {
            // Production plans retain the raw static actions in symbolize
            // and publish the runtime-executable FIELD_ACCESS refinements in
            // materializations.  The importer must mirror the runtime's
            // prefer-refined contract instead of inspecting the raw action.
            activation.add("materializations", symbolize.deepCopy());
            JsonArray rawSymbolize = symbolize.deepCopy();
            for (JsonElement element : rawSymbolize) {
                if (element.isJsonObject()) {
                    element.getAsJsonObject().remove("bindingMode");
                }
            }
            activation.add("symbolize", rawSymbolize);
            activation.add("containerElementFieldBindings",
                    containerBindings.deepCopy());
        } else {
            activation.add("symbolize", symbolize);
        }
        JsonArray outputs = new JsonArray();
        JsonObject outputPort = new JsonObject();
        outputPort.addProperty("symbol", "REGION.P.out.0");
        outputPort.addProperty("cell", cell);
        outputPort.addProperty("kind", "HEAP_STATE");
        outputPort.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        outputs.add(outputPort);
        activation.add("outputs", outputs);
        JsonObject requestedOutput = new JsonObject();
        requestedOutput.addProperty("portId", "REGION.P.out.0");
        requestedOutput.addProperty("cell", cell);
        requestedOutput.addProperty("kind", "HEAP_STATE");
        activation.add("requestedOutput", requestedOutput);
        if (sliceMetadata != null && sliceMetadata.has(
                "captureDischargedByHeapEffectTransformer")
                && sliceMetadata.get(
                "captureDischargedByHeapEffectTransformer")
                .getAsBoolean()) {
            activation.addProperty("requestedOutputCaptureRequired", false);
            activation.addProperty("requestedOutputCaptureComplete", true);
            activation.add("requestedOutputCapture", new JsonArray());
            JsonObject heapBinding = new JsonObject();
            heapBinding.addProperty("inputPort", "REGION.P.in.0");
            heapBinding.addProperty("outputPort", "REGION.P.out.0");
            heapBinding.addProperty("cell", cell);
            heapBinding.addProperty("bindingAuthority",
                    "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM");
            JsonArray heapBindings = new JsonArray();
            heapBindings.add(heapBinding);
            activation.add("heapStateBindings", heapBindings);
        }
        JsonObject requestedOutputSlice = new JsonObject();
        requestedOutputSlice.addProperty("outputPort", "REGION.P.out.0");
        requestedOutputSlice.addProperty("outputCell", cell);
        requestedOutputSlice.addProperty("complete", true);
        JsonArray sliceInputs = new JsonArray();
        if (existingMapInput) sliceInputs.add("REGION.P.in.0");
        for (JsonElement action : additionalSymbolize) {
            if (action.isJsonObject()
                    && action.getAsJsonObject().has("symbol")) {
                sliceInputs.add(action.getAsJsonObject().get("symbol")
                        .getAsString());
            }
        }
        requestedOutputSlice.add("inputPorts", sliceInputs);
        requestedOutputSlice.add("heapInitializers",
                heapInitializers.deepCopy());
        if (sliceMethods.size() > 0) {
            requestedOutputSlice.add("methods", sliceMethods.deepCopy());
        }
        if (causalEdges.size() > 0) {
            requestedOutputSlice.add("causalEdges", causalEdges.deepCopy());
        }
        if (sliceMetadata != null) {
            for (java.util.Map.Entry<String, JsonElement> entry
                    : sliceMetadata.entrySet()) {
                if (entry.getKey().startsWith("_fixture")) continue;
                requestedOutputSlice.add(entry.getKey(),
                        entry.getValue().deepCopy());
            }
        }
        activation.add("requestedOutputSlice", requestedOutputSlice);
        JsonArray edgeBindings = new JsonArray();
        JsonObject edgeBinding = new JsonObject();
        edgeBinding.addProperty("edgeId", "EDGE.P");
        edgeBinding.addProperty("writerEventSeq", 10);
        edgeBinding.addProperty("readerEventSeq", 20);
        edgeBindings.add(edgeBinding);
        activation.add("edgeBindings", edgeBindings);
        write(activations, activation.toString() + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.P");
        region.addProperty("rootMethod", method);
        JsonArray methods = new JsonArray();
        methods.add(method);
        methods.add("<example.Unrelated: void touch()>");
        region.add("methods", methods);
        write(regions, region.toString() + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.P");
        raw.addProperty("regionId", "REGION.P");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        JsonArray symbolizedInputs = new JsonArray();
        if (existingMapInput && !containsString(omittedSymbolizedInputs,
                "REGION.P.in.0")) {
            symbolizedInputs.add("REGION.P.in.0.selectedField");
        }
        for (JsonElement action : additionalSymbolize) {
            if (action.isJsonObject()
                    && action.getAsJsonObject().has("symbol")) {
                String symbol = action.getAsJsonObject().get("symbol")
                        .getAsString();
                if (!containsString(omittedSymbolizedInputs, symbol)) {
                    symbolizedInputs.add(symbol);
                }
            }
        }
        raw.add("symbolizedInputs", symbolizedInputs);
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.P");
        engine.addProperty("activationId", "ACT.P");
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        if (runtimeHeapObservations != null) {
            raw.add("runtimeHeapObservations",
                    runtimeHeapObservations.deepCopy());
        }
        if (branchMappings != null) {
            raw.add("branchMappings", branchMappings.deepCopy());
        }
        if (fieldObservations != null) {
            raw.add("fieldObservations", fieldObservations.deepCopy());
        }
        if (dynamicFieldBindings != null) {
            raw.add("dynamicFieldBindings",
                    dynamicFieldBindings.deepCopy());
        }
        if (engineArrayBindings != null) {
            raw.add("engineArrayInputBindings",
                    engineArrayBindings.deepCopy());
        }
        write(results, raw.toString() + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics, root.resolve("cache"));
        String summaryRows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = summaryRows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(summaryRows).getAsJsonObject();
        String diagnosticRows = new String(Files.readAllBytes(diagnostics),
                StandardCharsets.UTF_8);
        return new MapFixture(summary, diagnosticRows);
    }

    private static boolean containsString(JsonArray values, String value) {
        if (values == null) {
            return false;
        }
        for (JsonElement element : values) {
            if (element.isJsonPrimitive()
                    && value.equals(element.getAsString())) {
                return true;
            }
        }
        return false;
    }

    private static MapFixture importObservedMapStateFixture(
            Path root, boolean identityComplete, boolean snapshotComplete)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.Store: void update()>";
        String site = method + "#u5";
        String mapCell = "<example.Store: java.util.Map data>";
        String containerCell = "<example.Batch: example.Value[] values>";
        String authority =
                "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1";

        JsonObject mapAction = observedContainerAction("REGION.P.in.0",
                mapCell, "MAP_STATE_INPUT_OBSERVATION", authority);
        JsonObject containerAction = observedContainerAction(
                "REGION.P.in.1", containerCell,
                "CONTAINER_INPUT_OBSERVATION", authority);
        JsonArray actions = new JsonArray();
        actions.add(mapAction);
        actions.add(containerAction);

        JsonObject edge = causalEdge("DF.MAP.WRITE", method, site,
                "HEAP_WRITE", "field_mutation");
        edge.addProperty("invoke",
                "<java.util.Map: java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>");
        edge.addProperty("fromCell", method + "::$r1");
        edge.addProperty("toCell", mapCell);
        JsonObject obligation = exactTransformerObligation(
                "DF.MAP.WRITE", method, site, mapCell);
        JsonObject slice = exactTransformerSliceMetadata(mapCell,
                singletonObject(obligation), new JsonArray());
        slice.addProperty("requestedStateTransformerContractOutputPort",
                "REGION.P.out.0");
        slice.addProperty("outputPort", "REGION.P.out.0");
        slice.addProperty("outputCell", mapCell);
        JsonArray inputPorts = new JsonArray();
        inputPorts.add("REGION.P.in.0");
        inputPorts.add("REGION.P.in.1");
        slice.add("inputPorts", inputPorts);
        slice.add("causalEdges", singletonObject(edge));
        slice.add("causalEdgeIds", singletonString("DF.MAP.WRITE"));
        slice.add("methods", singletonString(method));
        slice.add("staticSites", singletonString(site));
        slice.addProperty("structuralComplete", true);
        slice.addProperty("truncated", false);
        slice.addProperty("complete", true);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.P");
        activation.addProperty("regionId", "REGION.P");
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.add("requestedOutputMethods", singletonString(method));
        activation.add("materializations", actions);
        activation.add("symbolize", actions.deepCopy());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        requested.addProperty("cell", mapCell);
        requested.addProperty("kind", "HEAP_STATE");
        activation.add("requestedOutput", requested);
        activation.add("requestedOutputSlice", slice);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.P.out.0");
        outputAction.addProperty("cell", mapCell);
        outputAction.addProperty("kind", "HEAP_STATE");
        activation.add("outputs", singletonObject(outputAction));
        JsonObject heapBinding = new JsonObject();
        heapBinding.addProperty("inputPort", "REGION.P.in.0");
        heapBinding.addProperty("outputPort", "REGION.P.out.0");
        heapBinding.addProperty("cell", mapCell);
        heapBinding.addProperty("bindingAuthority",
                "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM");
        activation.add("heapStateBindings", singletonObject(heapBinding));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.P");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        write(regions, region + "\n");

        JsonObject mapObservation = observedEmptyMapState(
                mapAction, method + "#u1", authority,
                identityComplete, snapshotComplete);
        JsonArray approximations = new JsonArray();
        approximations.add(firstContainerEvidence("REGION.P.in.0",
                mapCell, method + "#u1", authority, 2));
        approximations.add(firstContainerEvidence("REGION.P.in.1",
                containerCell, "<example.Batch: example.Value[] get()>#u1",
                authority, 5));
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.P");
        raw.addProperty("regionId", "REGION.P");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("symbolizedInputs", new JsonArray());
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("runtimeApproximations", approximations);
        raw.add("runtimeHeapObservations",
                singletonObject(mapObservation));
        raw.add("finalFieldObservations", singletonObject(
                observedMapAtExit(mapObservation)));
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.P");
        engine.addProperty("activationId", "ACT.P");
        JsonArray path = new JsonArray();
        path.add(methodExpression("java/util/HashMap put", 42,
                symbol("M_L'java/util/HashMap'_25", "java/util/HashMap"),
                symbol("key", "I"), symbol("value", "example/Value")));
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics, root.resolve("cache"));
        JsonObject summary = JsonParser.parseString(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        return new MapFixture(summary, new String(
                Files.readAllBytes(diagnostics), StandardCharsets.UTF_8));
    }

    private static MapFixture importObservedMapMutationFixture(
            Path root, JsonObject mutation, String invoke,
            boolean duplicateCausalEdge) throws Exception {
        importObservedMapStateFixture(root, true, true);

        Path activations = root.resolve("activation.jsonl");
        JsonObject activation = JsonParser.parseString(new String(
                Files.readAllBytes(activations), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        JsonArray causalEdges = activation.getAsJsonObject(
                "requestedOutputSlice").getAsJsonArray("causalEdges");
        JsonObject edge = causalEdges.get(0).getAsJsonObject();
        if (invoke == null) {
            edge.remove("invoke");
        } else {
            edge.addProperty("invoke", invoke);
        }
        if (duplicateCausalEdge) {
            causalEdges.add(edge.deepCopy());
        }
        write(activations, activation + "\n");

        Path results = root.resolve("results.jsonl");
        JsonObject raw = JsonParser.parseString(new String(
                Files.readAllBytes(results), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        raw.getAsJsonObject("engineSummary").add("pathCondition",
                singletonObject(mutation));
        write(results, raw + "\n");

        Path output = root.resolve("mutation-summaries.jsonl");
        Path diagnostics = root.resolve("mutation-diagnostics.jsonl");
        ConcolicSummaryImporter.importSummaries(results, activations,
                root.resolve("regions.jsonl"), output, diagnostics,
                root.resolve("mutation-cache"));
        JsonObject summary = JsonParser.parseString(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        return new MapFixture(summary, new String(
                Files.readAllBytes(diagnostics), StandardCharsets.UTF_8));
    }

    private static JsonObject observedContainerAction(
            String symbol, String cell, String mode, String authority) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("field", cell);
        action.addProperty("observed", true);
        action.addProperty("bindingMode", mode);
        action.addProperty("modelControllable", false);
        action.addProperty("containerObservationAuthority", authority);
        return action;
    }

    private static JsonObject firstContainerEvidence(
            String symbol, String cell, String site, String authority,
            long token) {
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", 1);
        evidence.addProperty("kind",
                "BOUNDED_CONTAINER_INPUT_OBSERVATION");
        evidence.addProperty("authority", authority);
        evidence.addProperty("inputSymbol", symbol);
        evidence.addProperty("inputCell", cell);
        evidence.addProperty("siteId", site);
        evidence.addProperty("outcome",
                "FIRST_MATCHING_CONTAINER_SELECTED");
        evidence.addProperty("selectedObjectToken", token);
        evidence.addProperty("complete", true);
        return evidence;
    }

    private static JsonObject observedEmptyMapState(
            JsonObject action, String site, String authority,
            boolean identityComplete, boolean snapshotComplete) {
        JsonObject observation = new JsonObject();
        String symbol = action.get("symbol").getAsString();
        String cell = action.get("cell").getAsString();
        int marker = site.lastIndexOf("#u");
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_STATE_INPUT_OBSERVATION");
        observation.addProperty("symbol", symbol);
        observation.addProperty("phase", "AT_MAP_STATE_INPUT");
        observation.add("path", singletonString("data"));
        observation.addProperty("available", true);
        observation.addProperty("accessOwnerObjectToken", 3);
        observation.addProperty("accessOwnerObjectTokenKnown", true);
        observation.addProperty("leafOwnerObjectToken", 3);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("valueClass", "java.util.HashMap");
        observation.addProperty("valueObjectToken", 2);
        observation.addProperty("valueObjectTokenKnown", true);
        observation.addProperty("collectionSize", 0);
        observation.addProperty("observationId",
                "MAP_STATE_INPUT:" + site + "#" + symbol);
        observation.addProperty("eventSequence", 1);
        observation.addProperty("originMethod", site.substring(0, marker));
        observation.addProperty("originUnitIndex", Integer.parseInt(
                site.substring(marker + 2)));
        observation.addProperty("siteId", site);
        observation.addProperty("inputSymbol", symbol);
        observation.addProperty("inputCell", cell);
        observation.addProperty("bindingMode",
                "MAP_STATE_INPUT_OBSERVATION");
        observation.addProperty("selectionAuthority", authority);
        observation.addProperty("modelControllable", false);
        observation.addProperty("vmReferenceSymbolized", false);
        observation.addProperty("mapImplementationClass",
                "java.util.HashMap");
        observation.addProperty("mapObjectToken", 2);
        observation.addProperty("backingMapObjectToken", 2);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("identityBindingComplete",
                identityComplete);
        observation.addProperty("entryCount", 0);
        observation.addProperty("finiteEntryBound", 4096);
        observation.add("keyExpressions", new JsonArray());
        observation.add("valueObjectTokens", new JsonArray());
        observation.add("entries", new JsonArray());
        observation.addProperty("snapshotComplete", snapshotComplete);
        observation.addProperty("snapshotAuthority",
                "SAME_FIELD_HOOK_STABLE_BOUNDED_ENTRY_SET_SNAPSHOT_V1");
        observation.addProperty("complete", true);
        observation.addProperty("mapStateInputSymbol", symbol);
        observation.addProperty("mapStateInputCell", cell);
        observation.addProperty("mapStateInputObservationId",
                observation.get("observationId").getAsString());
        observation.addProperty("mapStateInputObjectToken", 2);
        observation.addProperty("mapStateInputBindingAuthority", authority);
        observation.addProperty("mapStateInputBindingComplete", true);
        return observation;
    }

    private static JsonObject observedMapAtExit(JsonObject input) {
        JsonObject exit = new JsonObject();
        exit.addProperty("symbol", input.get("symbol").getAsString());
        exit.addProperty("phase", "AT_REGION_EXIT");
        exit.add("path", input.get("path").deepCopy());
        exit.addProperty("available", true);
        exit.addProperty("leafOwnerObjectToken", 3);
        exit.addProperty("leafOwnerObjectTokenKnown", true);
        exit.addProperty("valueClass", "java.util.HashMap");
        exit.addProperty("valueObjectToken", 2);
        exit.addProperty("valueObjectTokenKnown", true);
        exit.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        exit.addProperty("objectTokenScope", "ACT.P");
        return exit;
    }

    private static JsonObject incompleteMapEntryObservation(String siteId) {
        int marker = siteId.lastIndexOf("#u");
        JsonObject observation = new JsonObject();
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("operation", "java.util.Iterator.next");
        observation.addProperty("originMethod", siteId.substring(0, marker));
        observation.addProperty("originUnitIndex", Integer.parseInt(
                siteId.substring(marker + 2)));
        observation.addProperty("siteId", siteId);
        observation.addProperty("occurrence", 1);
        observation.addProperty("observationId",
                "MAP_ENTRY_READ:" + siteId + "#1");
        observation.addProperty("pcBoundary", 0);
        observation.addProperty("rawPathConditionBoundary", 0);
        observation.addProperty("complete", false);
        observation.addProperty("unresolvedReason",
                "symbolic expressions unavailable for [map]");
        return observation;
    }

    private static JsonObject causalEdge(String edgeId, String method,
                                         String siteId, String transferKind,
                                         String kind) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("method", method);
        edge.addProperty("siteId", siteId);
        edge.addProperty("transferKind", transferKind);
        edge.addProperty("kind", kind);
        return edge;
    }

    private static JsonObject exactProjectedInputBinding(
            String dependencyCell, String authority, String sinkSite) {
        JsonObject binding = new JsonObject();
        binding.addProperty("dependencyCell", dependencyCell);
        binding.addProperty("inputPort", "REGION.FIELD.in.0");
        binding.addProperty("bindingAuthority", authority);
        binding.add("dependencyMethods", singletonString(
                "<example.Heartbeat: void install(example.Snapshot)>"));
        binding.add("requestedStateTransformerSinkSites",
                singletonString(sinkSite));
        binding.add("requestedStateTransformerGuardSites", new JsonArray());
        binding.addProperty(
                "requestedStateTransformerSinkClosureComplete", true);
        binding.addProperty("requestedStateTransformerSinkExclusive", true);
        binding.add("requestedStateTransformerUnclassifiedEdgeIds",
                new JsonArray());
        binding.addProperty("requestedStateTransformerSinkAuthority",
                "STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                        + "REQUESTED_STATE_TRANSFORMERS");
        return binding;
    }

    private static JsonObject exactTransformerSliceMetadata(
            String outputCell, JsonArray obligations,
            JsonArray inputBindings) {
        JsonObject metadata = new JsonObject();
        metadata.add("inputBindings", inputBindings.deepCopy());
        metadata.addProperty("requestedStateTransformerContractVersion", 1);
        metadata.addProperty(
                "requestedStateTransformerContractApplicable", true);
        metadata.addProperty(
                "requestedStateTransformerContractOutputPort",
                "REGION.P.out.0");
        metadata.addProperty(
                "requestedStateTransformerContractOutputCell", outputCell);
        metadata.add("requestedStateTransformerObligations",
                obligations.deepCopy());
        metadata.addProperty("requestedStateTransformerObligationCount",
                obligations.size());
        metadata.add("requestedStateTransformerContractIssues",
                new JsonArray());
        metadata.addProperty(
                "requestedStateTransformerContractComplete", true);
        metadata.addProperty(
                "requestedStateTransformerContractAuthority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1");
        return metadata;
    }

    private static void addHeapEffectCaptureDischarge(
            JsonObject metadata, String outputCell, String inputPort) {
        metadata.addProperty(
                "captureDischargedByHeapEffectTransformer", true);
        metadata.addProperty("captureDischargeInputPort", inputPort);
        metadata.addProperty("captureDischargeOutputPort",
                "REGION.P.out.0");
        metadata.addProperty("captureDischargeOutputCell", outputCell);
        metadata.addProperty("captureDischargeAuthority",
                "HEAP_EFFECT_STATE_TRANSFORMER");
        metadata.add("captureBindings", new JsonArray());
        metadata.addProperty("captureBindingsRequired", false);
        metadata.addProperty("captureBindingsComplete", true);
        metadata.add("captureBindingIssues", new JsonArray());
    }

    private static JsonObject exactTransformerObligation(
            String edgeId, String method, String siteId,
            String outputCell) {
        JsonObject obligation = new JsonObject();
        obligation.addProperty("siteId", siteId);
        obligation.addProperty("method", method);
        obligation.addProperty("targetCell", outputCell);
        obligation.addProperty("transferKind", "HEAP_WRITE");
        obligation.addProperty("kind", "field_mutation");
        JsonArray edgeIds = new JsonArray();
        edgeIds.add(edgeId);
        obligation.add("causalEdgeIds", edgeIds);
        obligation.addProperty("authority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL");
        return obligation;
    }

    private static JsonObject transformerInputBinding(
            String inputPort, String dependencyCell, JsonArray sinkSites,
            JsonArray guardSites) {
        JsonObject binding = new JsonObject();
        binding.addProperty("inputPort", inputPort);
        binding.addProperty("dependencyCell", dependencyCell);
        binding.addProperty("bindingAuthority", "EXACT_CELL_IDENTITY");
        binding.add("dependencyMethods", new JsonArray());
        binding.add("requestedStateTransformerSinkSites",
                sinkSites.deepCopy());
        binding.add("requestedStateTransformerGuardSites",
                guardSites.deepCopy());
        binding.addProperty(
                "requestedStateTransformerSinkClosureComplete", true);
        binding.addProperty("requestedStateTransformerSinkExclusive", true);
        binding.add("requestedStateTransformerUnclassifiedEdgeIds",
                new JsonArray());
        binding.addProperty("requestedStateTransformerSinkAuthority",
                "STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                        + "REQUESTED_STATE_TRANSFORMERS");
        return binding;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) {
            result.add(value);
        }
        return result;
    }

    private static JsonArray stringsAsObjects(JsonObject... values) {
        JsonArray result = new JsonArray();
        for (JsonObject value : values) {
            result.add(value);
        }
        return result;
    }

    private static MapFixture importOrderedPutFixture(
            Path root, String mutation) throws Exception {
        String method = "<example.Store: void update()>";
        String outputCell = "<example.Store: java.util.Map data>";
        String base = "REGION.P.in.1";
        String containerPort = "REGION.P.in.2";
        String containerCell =
                "<example.Envelope: example.Value[] values>";
        String field = "<example.Value: long id>";
        int[] loadUnits = new int[]{13, 19, 25, 31};
        int[] fieldUnits = new int[]{14, 20, 26, 32};
        int[] writeUnits = new int[]{17, 23, 29, 35};
        long arrayToken = 500L;
        String engineArrayId = "AL_1";

        JsonArray actions = new JsonArray();
        actions.add(fieldAccessAction(base, "id"));
        JsonObject containerAction = new JsonObject();
        containerAction.addProperty("symbol", containerPort);
        containerAction.addProperty("bindingMode", "FIELD_ACCESS");
        containerAction.addProperty("field", containerCell);
        containerAction.addProperty("cell", containerCell);
        containerAction.add("fieldPath",
                JsonParser.parseString("[\"values\"]"));
        actions.add(containerAction);

        JsonArray declarations = new JsonArray();
        JsonArray dynamicBindings = new JsonArray();
        JsonArray fieldObservations = new JsonArray();
        JsonObject[] putExpressions = new JsonObject[4];
        JsonObject[] loadExpressions = new JsonObject[4];
        JsonElement[] putValues = new JsonElement[4];
        String[] dynamicSymbols = new String[4];
        JsonArray causalEdges = new JsonArray();
        JsonArray obligations = new JsonArray();
        JsonArray sinkSites = new JsonArray();

        for (int index = 0; index < 4; index++) {
            String bindingId = "CONTAINER.FIELD." + index;
            String fieldSite = method + "#u" + fieldUnits[index];
            String loadSite = method + "#u" + loadUnits[index];
            String writeSite = method + "#u" + writeUnits[index];
            String dynamic = dynamicFieldSymbol(base, fieldSite, 1);
            dynamicSymbols[index] = dynamic;

            JsonObject declaration = new JsonObject();
            declaration.addProperty("schemaVersion", 1);
            declaration.addProperty("kind", "ARRAY_ELEMENT_FIELD");
            declaration.addProperty("bindingId", bindingId);
            declaration.addProperty("baseInputSymbol", base);
            declaration.addProperty("containerInputPort",
                    "PORT".equals(mutation)
                            ? "REGION.P.in.missing" : containerPort);
            declaration.addProperty("containerInputCell", containerCell);
            declaration.addProperty("selectorAuthority",
                    "EXACT_ARRAY_INDEX");
            declaration.addProperty("elementIndex", index);
            declaration.addProperty("elementOccurrence", 1);
            declaration.add("fieldPath",
                    JsonParser.parseString("[\"id\"]"));
            declaration.addProperty("declaredFieldSignature", field);
            declaration.addProperty("declaredFieldOwnerClass",
                    "example.Value");
            declaration.addProperty("declaredFieldType", "long");
            declaration.addProperty("declaredFieldName", "id");
            declaration.addProperty("method", method);
            declaration.addProperty("fieldMaterializationSiteId",
                    fieldSite);
            declaration.addProperty("arrayLoadSiteId", loadSite);
            declaration.add("proofCausalEdgeIds", strings(
                    "PROOF." + index + ".0", "PROOF." + index + ".1",
                    "PROOF." + index + ".2", "PROOF." + index + ".3"));
            declaration.addProperty("proofAuthority",
                    "STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_FIELD_"
                            + "FOUR_EDGE_JOIN_V1");
            declaration.addProperty("complete", true);
            declarations.add(declaration);

            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "ARRAY_INDEX");
            selector.addProperty("bindingId", bindingId);
            selector.addProperty("containerInputPort", containerPort);
            selector.addProperty("containerInputCell", containerCell);
            selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
            selector.addProperty("resolvedFromSelectorAuthority",
                    "EXACT_ARRAY_INDEX");
            selector.addProperty("elementIndex", index);
            selector.addProperty("elementOccurrence", 1);
            selector.addProperty("declaredFieldOwnerClass",
                    "example.Value");
            selector.addProperty("declaredFieldType", "long");
            selector.addProperty("containerObjectToken",
                    "TOKEN".equals(mutation) ? 999L : arrayToken);
            selector.addProperty("elementObjectToken", 601L + index);
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", "ACT.P");
            selector.addProperty("containerObservationLocation",
                    "FIELD_ACCESS");
            selector.addProperty("authority",
                    "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                            + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
            selector.addProperty("complete", true);

            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 2);
            binding.addProperty("kind",
                    "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            binding.addProperty("baseInputSymbol", base);
            binding.addProperty("dynamicFieldSymbol", dynamic);
            binding.addProperty("materializationSiteId", fieldSite);
            binding.addProperty("materializationOccurrence", 1);
            binding.addProperty("fieldSignature", field);
            binding.add("fieldPath",
                    JsonParser.parseString("[\"id\"]"));
            binding.addProperty("leafOwnerObjectToken", 601L + index);
            binding.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            binding.addProperty("objectTokenScope", "ACT.P");
            binding.add("containerSelector", selector.deepCopy());
            addContainerSelectorFlatFields(binding, selector);
            addContainerSiteBridge(binding, fieldSite, 1, bindingId,
                    601L + index);
            binding.addProperty("actualHookSiteId",
                    "<example.Value: long getId()>#u1");
            binding.addProperty("actualHookOccurrence", index + 1);
            binding.addProperty("authority",
                    "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                            + "AND_STABLE_FIELD_SITE_OCCURRENCE");
            binding.addProperty("complete", true);
            dynamicBindings.add(binding);

            JsonObject observation = new JsonObject();
            observation.addProperty("symbol", dynamic);
            observation.addProperty("phase", "AT_MATERIALIZATION");
            observation.add("path",
                    JsonParser.parseString("[\"id\"]"));
            observation.addProperty("available", true);
            observation.addProperty("leafOwnerObjectToken", 601L + index);
            observation.addProperty("leafOwnerObjectTokenKnown", true);
            observation.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            observation.addProperty("objectTokenScope", "ACT.P");
            observation.addProperty("baseInputSymbol", base);
            observation.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            observation.addProperty("dynamicFieldSymbol", dynamic);
            observation.addProperty("materializationSiteId", fieldSite);
            observation.addProperty("materializationOccurrence", 1);
            addContainerSiteBridge(observation, fieldSite, 1, bindingId,
                    601L + index);
            observation.addProperty("actualHookSiteId",
                    "<example.Value: long getId()>#u1");
            observation.addProperty("actualHookOccurrence", index + 1);
            observation.addProperty("dynamicFieldBindingSchemaVersion", 2);
            observation.addProperty("dynamicFieldBindingKind",
                    "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
            observation.addProperty("fieldSignature", field);
            observation.add("fieldPath",
                    JsonParser.parseString("[\"id\"]"));
            observation.add("containerSelector", selector.deepCopy());
            addContainerSelectorFlatFields(observation, selector);
            observation.addProperty("dynamicFieldBindingAuthority",
                    "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                            + "AND_STABLE_FIELD_SITE_OCCURRENCE");
            observation.addProperty("dynamicFieldBindingComplete", true);
            observation.addProperty("complete", true);
            fieldObservations.add(observation);

            String edgeId = "DF.PUT." + index;
            JsonObject causal = causalEdge(edgeId, method, writeSite,
                    "HEAP_WRITE", "field_mutation");
            causal.addProperty("fromCell", method + "::value" + index);
            causal.addProperty("toCell", outputCell);
            causalEdges.add(causal);
            obligations.add(exactTransformerObligation(edgeId, method,
                    writeSite, outputCell));
            sinkSites.add(writeSite);
        }

        JsonObject map = mapInputExpression();
        for (int index = 0; index < 4; index++) {
            JsonElement value = symbol("EL_1-0-" + (index + 1),
                    "Lexample/Value;");
            putValues[index] = value;
            loadExpressions[index] = arrayLoadExpression(engineArrayId,
                    index, value, 100 + index);
            putExpressions[index] = methodExpression(
                    "java/util/HashMap put", 100 + index,
                    map.deepCopy(), symbol(
                            "M_J_field_" + dynamicSymbols[index]
                                    + "_example/Value", "J"),
                    value.deepCopy());
        }
        if ("KEY".equals(mutation)) {
            JsonElement first = putExpressions[0].getAsJsonArray(
                    "_param_list").get(1).deepCopy();
            putExpressions[0].getAsJsonArray("_param_list").set(1,
                    putExpressions[1].getAsJsonArray("_param_list").get(1)
                            .deepCopy());
            putExpressions[1].getAsJsonArray("_param_list").set(1, first);
        }
        if ("LOAD".equals(mutation)) {
            loadExpressions[0].add("_value_exp",
                    symbol("EL_1-0-wrong", "Lexample/Value;"));
        }
        JsonArray path = new JsonArray();
        for (int index = 0; index < 4; index++) {
            if ("CARDINALITY".equals(mutation) && index == 3) continue;
            if ("ORDER".equals(mutation) && index == 1) {
                path.add(methodExpression("java/util/HashMap remove", 99,
                        map.deepCopy(), symbol("interveningKey", "J")));
            }
            path.add(loadExpressions[index]);
            path.add(putExpressions[index]);
        }

        JsonObject containerInput = transformerInputBinding(containerPort,
                containerCell, sinkSites, new JsonArray());
        JsonArray inputBindings = stringsAsObjects(containerInput);
        JsonObject sliceMetadata = exactTransformerSliceMetadata(outputCell,
                obligations, inputBindings);
        addHeapEffectCaptureDischarge(sliceMetadata, outputCell,
                "REGION.P.in.0");

        JsonElement[] arrayElements = new JsonElement[4];
        for (int index = 0; index < 4; index++) {
            arrayElements[index] = symbol("M_L_array_element_" + index,
                    "Lexample/Value;");
        }
        JsonObject arrayValue = arrayValueExpression(
                "[Lexample/Value;", "Lexample/Value;", true,
                arrayElements);
        arrayValue.addProperty("_engine_array_id", engineArrayId);
        arrayValue.addProperty("_engine_array_id_authority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        JsonObject engineArray = new JsonObject();
        engineArray.addProperty("schemaVersion", 1);
        engineArray.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        engineArray.addProperty("sourceActivationId", "ACT.P");
        engineArray.addProperty("inputPort", containerPort);
        engineArray.addProperty("inputCell", containerCell);
        engineArray.addProperty("inputJavaType", "example.Value[]");
        engineArray.addProperty("inputJavaTypeDescriptor",
                "[Lexample/Value;");
        engineArray.addProperty("symbolizationPrefix", containerPort);
        engineArray.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        engineArray.addProperty("engineArrayId", engineArrayId);
        engineArray.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        engineArray.addProperty("arrayObjectToken", arrayToken);
        engineArray.addProperty("symbolizationArrayObjectToken", arrayToken);
        engineArray.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        engineArray.addProperty("sameArrayObjectTokenVerified", true);
        engineArray.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        engineArray.addProperty("objectTokenScope", "ACT.P");
        engineArray.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        engineArray.add("arrayValueExpression", arrayValue);
        engineArray.addProperty("complete", true);

        return importMapFixture(root, path, true, new JsonArray(),
                singletonString(method), causalEdges, null, actions,
                new JsonArray(), fieldObservations, dynamicBindings,
                sliceMetadata, new JsonArray(), declarations,
                singletonObject(engineArray));
    }

    private static JsonObject arrayLoadExpression(
            String engineArrayId, int index, JsonElement value, int line) {
        JsonObject load = new JsonObject();
        load.addProperty("_code_position",
                "virtual void example.Store.update():" + line);
        load.addProperty("_type", "_array_expr");
        load.addProperty("_arr_str", engineArrayId);
        load.addProperty("_is_load", true);
        load.add("_index_exp", constant("Y_I_" + index, "I"));
        load.add("_value_exp", value.deepCopy());
        return load;
    }

    private static ExactTransformerFixture exactTransformerFixture(
            JsonArray inputBindings) {
        ExactTransformerFixture fixture = new ExactTransformerFixture();
        fixture.outputCell = "<example.Store: java.util.Map data>";
        fixture.update = "<example.Store: void update()>";
        fixture.prune = "<example.Store: void prune()>";
        fixture.wrapper = "<example.Store: void wrapper()>";
        fixture.updateSite = fixture.update + "#u1";
        fixture.pruneSite = fixture.prune + "#u15";
        fixture.outerGuardSite = fixture.prune + "#u6";
        fixture.innerGuardSite = fixture.prune + "#u14";

        JsonObject map = symbol(
                "M_L_field_REGION.P.in.0_example/Store", "L");
        fixture.path.add(methodExpression("java/util/HashMap put", 19,
                symbolCopy(map), symbol("putKey", "I"),
                symbol("putValue", "example/Value")));
        fixture.methods.add(fixture.update);
        fixture.methods.add(fixture.prune);
        fixture.methods.add(fixture.wrapper);

        JsonObject updateWrite = causalEdge("DF.WRITE.UPDATE",
                fixture.update, fixture.updateSite, "HEAP_WRITE",
                "field_mutation");
        updateWrite.addProperty("fromCell", fixture.update + "::key");
        updateWrite.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(updateWrite);
        JsonObject pruneWrite = causalEdge("DF.WRITE.PRUNE",
                fixture.prune, fixture.pruneSite, "HEAP_WRITE",
                "field_mutation");
        pruneWrite.addProperty("fromCell", fixture.prune + "::expiredKey");
        pruneWrite.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(pruneWrite);
        JsonObject otherFieldWrite = causalEdge("DF.WRITE.OTHER",
                fixture.wrapper, fixture.wrapper + "#u2", "HEAP_WRITE",
                "field_write");
        otherFieldWrite.addProperty("fromCell", fixture.wrapper
                + "::enabled");
        otherFieldWrite.addProperty("toCell",
                "<example.Store: boolean enabled>");
        fixture.causalEdges.add(otherFieldWrite);
        JsonObject outer = guardedMutationEdge("DF.GUARD.OUTER",
                fixture.prune, 6, 15, false);
        outer.addProperty("fromCell", fixture.prune + "::hasNext");
        outer.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(outer);
        JsonObject inner = guardedMutationEdge("DF.GUARD.INNER",
                fixture.prune, 14, 15, false);
        inner.addProperty("fromCell", fixture.prune + "::expiryPredicate");
        inner.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(inner);

        JsonArray obligations = new JsonArray();
        obligations.add(exactTransformerObligation("DF.WRITE.UPDATE",
                fixture.update, fixture.updateSite, fixture.outputCell));
        obligations.add(exactTransformerObligation("DF.WRITE.PRUNE",
                fixture.prune, fixture.pruneSite, fixture.outputCell));
        fixture.sliceMetadata = exactTransformerSliceMetadata(
                fixture.outputCell, obligations, inputBindings);
        fixture.branchMappings.add(branchMapping(fixture.prune, 6, 1,
                true, symbol("outerLoopGate", "Z")));
        return fixture;
    }

    private static final class ExactTransformerFixture {
        private String outputCell;
        private String update;
        private String prune;
        private String wrapper;
        private String updateSite;
        private String pruneSite;
        private String outerGuardSite;
        private String innerGuardSite;
        private final JsonArray path = new JsonArray();
        private final JsonArray methods = new JsonArray();
        private final JsonArray causalEdges = new JsonArray();
        private final JsonArray branchMappings = new JsonArray();
        private JsonObject sliceMetadata;
    }

    private static JsonObject guardedMutationEdge(
            String edgeId, String method, int guardUnitIndex,
            int mutationUnitIndex, boolean requiredOutcome) {
        JsonObject edge = causalEdge(edgeId, method,
                method + "#u" + guardUnitIndex, "GUARD",
                "heap_mutation_path_guard");
        edge.addProperty("guardSiteId", method + "#u" + guardUnitIndex);
        edge.addProperty("guardedMutationCount", 1);
        edge.addProperty("guardedMutationsAuthority",
                "STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE");
        JsonObject mutation = new JsonObject();
        mutation.addProperty("guardSiteId",
                method + "#u" + guardUnitIndex);
        mutation.addProperty("guardedMutationSiteId",
                method + "#u" + mutationUnitIndex);
        mutation.addProperty("method", method);
        mutation.addProperty("unitIndex", mutationUnitIndex);
        mutation.addProperty("requiredOutcome", requiredOutcome);
        JsonArray mutations = new JsonArray();
        mutations.add(mutation);
        edge.add("guardedMutations", mutations);
        return edge;
    }

    private static JsonObject branchMapping(
            String method, int unitIndex, int occurrence,
            boolean observedOutcome, JsonElement condition) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", method + "#u" + unitIndex);
        mapping.addProperty("method", method);
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", observedOutcome);
        mapping.addProperty("observedOutcome", observedOutcome);
        mapping.addProperty("effectiveOutcome", observedOutcome);
        mapping.addProperty("overrideApplied", false);
        mapping.addProperty("conditionIndex", -1);
        mapping.addProperty("rawConditionIndex", -1);
        mapping.add("condition", condition.deepCopy());
        return mapping;
    }

    private static JsonObject fieldAccessAction(String symbol,
                                                String field) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("field", "<example.Value: long " + field + ">");
        action.addProperty("cell", "<example.Value: long " + field + ">");
        JsonArray path = new JsonArray();
        path.add(field);
        action.add("fieldPath", path);
        return action;
    }

    private static JsonObject fieldObservation(String symbol, String field,
                                               int leafOwnerIdentity) {
        JsonObject observation = new JsonObject();
        observation.addProperty("symbol", symbol);
        observation.addProperty("phase", "AT_MATERIALIZATION");
        JsonArray path = new JsonArray();
        path.add(field);
        observation.add("path", path);
        observation.addProperty("available", true);
        observation.addProperty("leafOwnerIdentity", leafOwnerIdentity);
        return observation;
    }

    private static JsonObject freshMapInitializer(String initializerId) {
        JsonObject initializer = new JsonObject();
        initializer.addProperty("initializerId", initializerId);
        initializer.addProperty("kind",
                "FRESH_DEFAULT_CONSTRUCTED_OBJECT");
        initializer.addProperty("allocatedType", "java.util.HashMap");
        initializer.addProperty("allocationEdgeId", "EDGE.ALLOC.0");
        initializer.addProperty("allocationMethod",
                "<example.Store: void update()>");
        initializer.addProperty("allocationSiteId", "SITE.ALLOC.0");
        initializer.addProperty("constructor",
                "<java.util.HashMap: void <init>()>");
        initializer.addProperty("constructorArgumentCount", 0);
        initializer.addProperty("outputPort", "REGION.P.out.0");
        JsonArray proof = new JsonArray();
        proof.add("EDGE.ALLOC.0");
        initializer.add("proofEdgeIds", proof);
        initializer.addProperty("proofComplete", true);
        initializer.addProperty("selectionAuthority",
                "STATIC_ALLOCATION_CONSTRUCTOR_AND_FORWARD_CAUSAL_PATH");
        initializer.addProperty("captureBoundaryRequirement",
                "REGION_ROOT_ENTRY_PRECEDES_ALLOCATION");
        return initializer;
    }

    private static JsonObject importExactOutputCaptureFixture(
            Path root, JsonElement expression, int captureCount)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String rootMethod = "<example.Root: void run()>";
        String caller = "<example.Client: void send()>";
        String callee = "<example.Protocol: void accept(java.lang.String)>";
        String outputCell = callee + ".param0:java.lang.String";

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId",
                "REGION.OUT.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.OUT.out.0");
        capture.addProperty("outputCell", outputCell);
        capture.addProperty("callerMethod", caller);
        capture.addProperty("unitIndex", 7);
        capture.addProperty("siteId", caller + "#u7");
        capture.addProperty("calleeMethod", callee);
        capture.addProperty("argumentIndex", 0);
        capture.addProperty("occurrence", 1);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.OUT");
        activation.addProperty("regionId", "REGION.OUT");
        activation.addProperty("regionInstanceId",
                "REGION.OUT@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", rootMethod);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.OUT.out.0");
        requested.addProperty("cell", outputCell);
        requested.addProperty("kind", "SINK_STATE");
        activation.add("requestedOutput", requested);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.OUT.out.0");
        slice.addProperty("complete", true);
        slice.add("inputPorts", singletonString("REGION.OUT.in.0"));
        slice.add("methods", singletonString(rootMethod));
        activation.add("requestedOutputSlice", slice);
        activation.add("requestedOutputCapture", singletonObject(capture));
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.OUT.in.0");
        input.addProperty("cell", rootMethod + ".param0:java.lang.String");
        input.addProperty("location", "ARGUMENT");
        activation.add("symbolize", singletonObject(input));
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.OUT.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        activation.add("outputs", singletonObject(outputAction));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.OUT");
        region.addProperty("rootMethod", rootMethod);
        region.add("methods", singletonString(rootMethod));
        write(regions, region + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.OUT");
        raw.addProperty("regionId", "REGION.OUT");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", singletonString("REGION.OUT.in.0"));
        raw.add("rootOutputExpression", constant("Y_L_NULL", "L"));
        JsonArray captures = new JsonArray();
        for (int index = 0; index < captureCount; index++) {
            JsonObject observed = capture.deepCopy();
            observed.addProperty("expressionCaptured", true);
            observed.add("expression", expression.deepCopy());
            captures.add(observed);
        }
        raw.add("outputCaptures", captures);
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.OUT");
        engine.addProperty("activationId", "ACT.OUT");
        engine.add("pathCondition", new JsonArray());
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics, root.resolve("cache"));
        return JsonParser.parseString(new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim()).getAsJsonObject();
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, JsonElement expression)
            throws Exception {
        return importExactFieldAssignmentCaptureFixture(root, exitKind,
                identityVerified, rhsRelationComplete,
                "<example.State: java.lang.String value>", expression);
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, String field,
            JsonElement expression) throws Exception {
        return importExactFieldAssignmentCaptureFixture(root, exitKind,
                identityVerified, rhsRelationComplete, field, expression,
                false);
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, String field,
            JsonElement expression, boolean exactVmGuard) throws Exception {
        return importExactFieldAssignmentCaptureFixture(root, exitKind,
                identityVerified, rhsRelationComplete, field, expression,
                exactVmGuard ? "EXACT" : "NONE");
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, String field,
            JsonElement expression, String guardMode) throws Exception {
        boolean causalMapObservation =
                "CAUSAL_MAP_OBSERVATION".equals(guardMode);
        boolean nullGuardWithUnusedInput =
                "EXACT_NULL_WITH_UNUSED_INPUT".equals(guardMode);
        boolean exactVmGuard = !"NONE".equals(guardMode)
                && !causalMapObservation;
        boolean projectedDischarge = expression == null
                || expression.isJsonNull();
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = projectedDischarge
                ? "<example.Heartbeat: void install(example.Snapshot)>"
                : "<example.Heartbeat: void install(java.lang.String)>";
        String site = method + "#u3";
        String edgeId = "DF.FIELD.WRITE";

        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId",
                "REGION.FIELD.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.FIELD.out.0");
        capture.addProperty("outputCell", field);
        capture.addProperty("method", method);
        capture.addProperty("unitIndex", 3);
        capture.addProperty("siteId", site);
        capture.addProperty("unit", "r0." + field + " = r1");
        capture.addProperty("fieldSignature", field);
        capture.addProperty("fieldOwnerExpression", "r0");
        capture.addProperty("fieldOwnerCell", method + "::r0");
        capture.addProperty("fieldOwnerDeclaredType", "example.State");
        capture.addProperty("fieldOwnerBindingKind",
                "INSTANCE_FIELD_LHS_BASE");
        capture.addProperty("fieldOwnerBindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS");
        capture.addProperty("rhsExpression", "r1");
        capture.addProperty("rhsCell", method + "::r1");
        capture.addProperty("rhsCausalEdgeId", edgeId);
        capture.addProperty("rhsRelation", "value_flow");
        capture.addProperty("rhsRelationComplete", rhsRelationComplete);
        capture.addProperty("rhsRelationAuthority",
                "STATIC_EXACT_HEAP_WRITE_VALUE_FLOW");
        capture.addProperty("causalEdgeId", edgeId);
        capture.addProperty("transferKind", "HEAP_WRITE");
        capture.addProperty("bindingKind", "field_write");
        capture.addProperty("bindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS");
        capture.addProperty("occurrence", 1);
        capture.addProperty("occurrenceAuthority",
                "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_"
                        + "SITE_LAST_WRITE_OCCURRENCE");
        capture.addProperty("runtimeFieldOwnerObjectId", 17);
        capture.addProperty("runtimeFieldOwnerBindingAuthority",
                "RUNTIME_EXACT_FIELD_WRITE_RECEIVER_IDENTITY");
        capture.addProperty("runtimeEventSeq", 5);

        JsonObject obligation = exactTransformerObligation(edgeId, method,
                site, field);
        obligation.addProperty("kind", "field_write");
        JsonObject causal = causalEdge(edgeId, method, site, "HEAP_WRITE",
                "field_write");
        causal.addProperty("fromCell", method + "::r1");
        causal.addProperty("toCell", field);
        JsonArray inputBindings = new JsonArray();
        JsonArray causalEdges = new JsonArray();
        if (projectedDischarge) {
            String baseCell = method + ".param0:example.Snapshot";
            String projectedCell = baseCell + "#field:value";
            JsonObject baseBinding = exactProjectedInputBinding(baseCell,
                    "EXACT_CELL_IDENTITY", site);
            JsonObject projectedBinding = exactProjectedInputBinding(
                    projectedCell,
                    "UNIQUE_EXACT_PROJECTED_VALUE_CARRIER", site);
            inputBindings.add(baseBinding);
            inputBindings.add(projectedBinding);
            JsonObject projection = causalEdge("DF.FIELD.PROJECTION",
                    method, method + "#synthetic:projected_local_def_use",
                    "VALUE_PASS", "projected_local_def_use");
            projection.addProperty("fromCell", projectedCell);
            projection.addProperty("toCell", method + "::r1");
            causalEdges.add(projection);
            if (causalMapObservation) {
                JsonObject guard = causalEdge("DF.FIELD.GUARD", method,
                        method + "#u2", "GUARD",
                        "path_guard_dependency");
                guard.addProperty("fromCell", projectedCell);
                guard.addProperty("toCell", method + "::guard");
                causalEdges.add(guard);
            }
        }
        causalEdges.add(causal);
        JsonObject slice = exactTransformerSliceMetadata(field,
                singletonObject(obligation), inputBindings);
        slice.addProperty("requestedStateTransformerContractOutputPort",
                "REGION.FIELD.out.0");
        slice.addProperty("outputPort", "REGION.FIELD.out.0");
        slice.addProperty("outputCell", field);
        JsonArray sliceInputs = singletonString("REGION.FIELD.in.0");
        if (nullGuardWithUnusedInput) {
            sliceInputs.add("REGION.FIELD.in.1");
        }
        slice.add("inputPorts", sliceInputs);
        slice.add("methods", singletonString(method));
        slice.add("causalEdges", causalEdges);
        JsonArray causalEdgeIds = singletonString(edgeId);
        if (projectedDischarge) {
            causalEdgeIds.add("DF.FIELD.PROJECTION");
            if (causalMapObservation) {
                causalEdgeIds.add("DF.FIELD.GUARD");
            }
        }
        slice.add("causalEdgeIds", causalEdgeIds);
        slice.addProperty("causalEdgeCount", causalEdges.size());
        slice.add("captureBindings", singletonObject(capture));
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("complete", true);
        slice.addProperty("structuralComplete", true);
        slice.addProperty("truncated", false);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.FIELD");
        activation.addProperty("regionId", "REGION.FIELD");
        activation.addProperty("regionInstanceId",
                "REGION.FIELD@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.FIELD.out.0");
        requested.addProperty("cell", field);
        requested.addProperty("kind", "HEAP_STATE");
        activation.add("requestedOutput", requested);
        activation.add("requestedOutputSlice", slice);
        activation.add("requestedOutputCapture", singletonObject(capture));
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.FIELD.in.0");
        input.addProperty("cell", method + ".param0:"
                + (projectedDischarge ? "example.Snapshot"
                : "java.lang.String"));
        input.addProperty("location", "ARGUMENT");
        JsonArray symbolize = singletonObject(input);
        if (nullGuardWithUnusedInput) {
            JsonObject unused = new JsonObject();
            unused.addProperty("symbol", "REGION.FIELD.in.1");
            unused.addProperty("cell", method + ".param1:int");
            unused.addProperty("location", "ARGUMENT");
            unused.addProperty("bindingMode", "LOCAL_DEFINITION");
            unused.addProperty("lazy", true);
            symbolize.add(unused);
        }
        activation.add("symbolize", symbolize);
        if (projectedDischarge) {
            JsonObject fallback = input.deepCopy();
            fallback.addProperty("bindingMode", "CONCRETE_PASSTHROUGH");
            fallback.addProperty("concreteFallback", true);
            activation.add("concreteFallbacks", singletonObject(fallback));
            activation.add("materializations", new JsonArray());
        }
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.FIELD.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        activation.add("outputs", singletonObject(outputAction));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.FIELD");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        write(regions, region + "\n");

        JsonObject observed = new JsonObject();
        observed.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        observed.addProperty("captureBindingId",
                "REGION.FIELD.out.0.capture.0");
        observed.addProperty("outputPort", "REGION.FIELD.out.0");
        observed.addProperty("outputCell", field);
        observed.addProperty("method", method);
        observed.addProperty("unitIndex", 3);
        observed.addProperty("siteId", site);
        observed.addProperty("fieldSignature", field);
        observed.addProperty("requestedOccurrence", 1);
        observed.addProperty("occurrence", 1);
        observed.addProperty("captureAuthority",
                "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT");
        observed.addProperty("declaredFieldOwnerVerified", true);
        observed.addProperty("declaredFieldTypeVerified", true);
        observed.addProperty("observedFieldValueAvailable", true);
        observed.addProperty("assignmentIdentityVerified", identityVerified);
        observed.addProperty("fieldOwnerObjectTokenKnown", true);
        observed.addProperty("fieldOwnerObjectToken", 1);
        observed.addProperty("assignedValueObjectTokenKnown", true);
        observed.addProperty("assignedValueObjectToken", 2);
        observed.addProperty("observedFieldValueObjectToken", 2);
        observed.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observed.addProperty("objectTokenScope", "ACT.FIELD");
        observed.addProperty("assignedValueClass", "java.lang.String");
        observed.addProperty("observedFieldValueClass", "java.lang.String");
        observed.addProperty("assignedValueWasNull", false);
        observed.addProperty("observedFieldValueWasNull", false);
        observed.addProperty("assignmentIdentityMode",
                "REFERENCE_IDENTITY");
        observed.addProperty("assignmentIdentityAuthority",
                "EXACT_DECLARED_FIELD_REFLECTION_AND_REFERENCE_IDENTITY");
        observed.addProperty("expressionCaptured", !projectedDischarge);
        if (!projectedDischarge) {
            observed.add("expression", expression.deepCopy());
        }
        if (exactVmGuard) {
            observed.addProperty("expressionEnvelopeSchemaVersion", 1);
            observed.addProperty("expressionEnvelopeActive",
                    !"INACTIVE_ENVELOPE".equals(guardMode));
            observed.addProperty("assignedValueClass", "java.lang.Integer");
            observed.addProperty("observedFieldValueClass",
                    "java.lang.Integer");
            observed.addProperty("assignedValueWasNull", false);
            observed.addProperty("observedFieldValueWasNull", false);
            observed.addProperty("assignmentIdentityMode",
                    "BOXED_PRIMITIVE_VALUE_EQUALITY");
            observed.addProperty("concretePrimitiveValue", "10");
            observed.addProperty("expressionEnvelopeKind",
                    "CONCRETE_PRIMITIVE");
            observed.addProperty("expressionEnvelopeSymbolic", false);
            observed.addProperty("expressionEnvelopeAuthority",
                    "VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1");
            observed.addProperty("expressionEnvelopeJavaTypeDescriptor",
                    "I");
        }

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.FIELD");
        raw.addProperty("regionId", "REGION.FIELD");
        raw.addProperty("exitKind", exitKind);
        JsonArray unresolvedInputs = new JsonArray();
        if (projectedDischarge) {
            unresolvedInputs.add("REGION.FIELD.out.0.capture.0: "
                    + "field-assignment expression capture failed");
        }
        raw.add("unresolvedInputs", unresolvedInputs);
        raw.add("symbolizedInputs", projectedDischarge
                ? new JsonArray()
                : singletonString("REGION.FIELD.in.0"));
        raw.add("rootOutputExpression", constant("Y_L_NULL", "L"));
        raw.add("outputCaptures", singletonObject(observed));
        if (exactVmGuard || projectedDischarge) {
            JsonArray runtimeHeapObservations = new JsonArray();
            if (projectedDischarge) {
                runtimeHeapObservations.add(incompleteMapEntryObservation(
                        causalMapObservation ? method + "#u2"
                                : "<example.UnrelatedMap: void scan()>#u7"));
            }
            raw.add("runtimeHeapObservations", runtimeHeapObservations);
        }
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.FIELD");
        engine.addProperty("activationId", "ACT.FIELD");
        JsonArray pathCondition = new JsonArray();
        if (exactVmGuard) {
            String codePosition = "FILTERED".equals(guardMode)
                    ? "virtual void example.Unrelated.install(jobject):12"
                    : "virtual void example.Heartbeat.install(jobject):12";
            JsonElement rawLeft = "FORGED_SEMANTIC".equals(guardMode)
                    ? symbol("M_L_unrelated_guard", "L")
                    : symbol("M_L_field_REGION.FIELD.in.0_java/lang/String",
                    "L");
            JsonObject condition;
            if ("EXACT_STRING_PREDICATE".equals(guardMode)) {
                condition = stringPredicate(codePosition, "contains", false,
                        symbol("M_L'String'_REGION.FIELD.in.0_example/State",
                                "java/lang/String"),
                        stringConstant("ready"));
            } else {
                JsonObject right = nullGuardWithUnusedInput
                        ? symbol("N", "")
                        : constant("Y_L_NULL", "L");
                condition = binaryCondition(
                        codePosition, "!=", rawLeft,
                        right);
            }
            JsonObject semanticCondition = condition.deepCopy();
            if ("FORGED_SEMANTIC".equals(guardMode)) {
                semanticCondition.add("_left", symbol(
                        "M_L_field_REGION.FIELD.in.0_java/lang/String",
                        "L"));
            } else if ("FORGED_OPERATOR".equals(guardMode)) {
                semanticCondition.addProperty("_op", "==");
            }
            pathCondition.add(condition.deepCopy());
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", method + "#u2");
            mapping.addProperty("method", method);
            mapping.addProperty("unitIndex", 2);
            mapping.addProperty("occurrence", 1);
            mapping.addProperty("vmOccurrence", 1);
            mapping.addProperty("outcome", true);
            mapping.addProperty("observedOutcome", true);
            mapping.addProperty("effectiveOutcome", true);
            mapping.addProperty("overrideApplied", false);
            mapping.addProperty("overrideMode", "NONE");
            mapping.addProperty("conditionIndex", 0);
            mapping.addProperty("rawConditionIndex", 0);
            mapping.addProperty("rawPathConditionBaseline", 0);
            mapping.addProperty("enginePathConditionBaseline", 0);
            mapping.addProperty("rawPathConditionSize", 1);
            mapping.addProperty("enginePathConditionSize", 1);
            mapping.addProperty("mappingPolicy",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
            mapping.addProperty("conditionAuthority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
            mapping.addProperty("vmBranchEventExpected", true);
            mapping.addProperty("vmBranchEventValidated", true);
            mapping.addProperty("vmBranchEventId", 1);
            mapping.addProperty("vmBranchEventAuthority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
            mapping.addProperty("vmThreadContextId", 2);
            mapping.addProperty("vmOwnerJavaThreadId", 3);
            mapping.addProperty("vmOwnerOsThreadId", 4);
            JsonArray vmConditionIndices = new JsonArray();
            vmConditionIndices.add(0);
            mapping.add("vmConditionIndices", vmConditionIndices);
            mapping.add("rawCondition", condition.deepCopy());
            mapping.add("condition", semanticCondition);
            raw.add("branchMappings", singletonObject(mapping));
        }
        engine.add("pathCondition", pathCondition);
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics, root.resolve("cache"));
        String rows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = rows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(rows).getAsJsonObject();
        String diagnosticRows = new String(Files.readAllBytes(diagnostics),
                StandardCharsets.UTF_8);
        return new MapFixture(summary, diagnosticRows);
    }

    private static MapFixture importEngineArrayBridgeFixture(
            Path root, JsonArray bindings, boolean store,
            boolean includeUnusedArray) throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = includeUnusedArray
                ? "<example.ArrayHandler: int run(java.lang.Object[],"
                + "java.lang.Object[])>"
                : "<example.ArrayHandler: int run(java.lang.Object[])>";

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.ARRAY");
        activation.addProperty("regionId", "REGION.ARRAY");
        activation.addProperty("regionInstanceId",
                "REGION.ARRAY@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        slice.addProperty("outputPort", "REGION.ARRAY.out.0");
        JsonArray inputPorts = new JsonArray();
        inputPorts.add("REGION.ARRAY.in.0");
        if (includeUnusedArray) inputPorts.add("REGION.ARRAY.in.1");
        slice.add("inputPorts", inputPorts);
        slice.add("methods", singletonString(method));
        activation.add("requestedOutputSlice", slice);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.ARRAY.out.0");
        requested.addProperty("kind", "PRIMITIVE");
        activation.add("requestedOutput", requested);

        JsonArray materializations = new JsonArray();
        JsonArray regionInputs = new JsonArray();
        for (int index = 0; index < (includeUnusedArray ? 2 : 1);
                index++) {
            String port = "REGION.ARRAY.in." + index;
            String cell = method + ".param" + index
                    + ":java.lang.Object[]";
            JsonObject action = new JsonObject();
            action.addProperty("symbol", port);
            action.addProperty("cell", cell);
            action.addProperty("javaType", "java.lang.Object[]");
            action.addProperty("location", "ARGUMENT");
            materializations.add(action);
            JsonObject input = new JsonObject();
            input.addProperty("portId", port);
            input.addProperty("cell", cell);
            input.addProperty("javaType", "java.lang.Object[]");
            regionInputs.add(input);
        }
        activation.add("materializations", materializations);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.ARRAY.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        activation.add("outputs", singletonObject(outputAction));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.ARRAY");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        region.add("symbolicInputs", regionInputs);
        write(regions, region + "\n");

        JsonObject load = new JsonObject();
        load.addProperty("_type", "_array_expr");
        load.addProperty("_is_load", !store);
        load.addProperty("_arr_str", "AL_1");
        load.add("_index_exp", constant("Y_I_0", "I"));
        load.add("_value_exp", symbol("M_L_ARRAY_VALUE",
                "Ljava/lang/Object;"));
        load.addProperty("_code_position", "virtual int "
                + "example.ArrayHandler.run(java.lang.Object"
                + (includeUnusedArray ? "[],java.lang.Object[]" : "[]")
                + "):12");
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.ARRAY");
        engine.addProperty("activationId", "ACT.ARRAY");
        engine.add("pathCondition", singletonObject(load));

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.ARRAY");
        raw.addProperty("regionId", "REGION.ARRAY");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", inputPorts.deepCopy());
        raw.add("rootOutputExpression", constant("Y_I_1", "I"));
        raw.add("engineSummary", engine);
        if (bindings != null) {
            raw.add("engineArrayInputBindings", bindings.deepCopy());
        }
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics, root.resolve("cache"));
        String rows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = rows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(rows).getAsJsonObject();
        return new MapFixture(summary, new String(Files.readAllBytes(
                diagnostics), StandardCharsets.UTF_8));
    }

    private static MapFixture importMapProjectionFixture(
            Path root, String operation, String fault) throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.ProjectionProducer: example.Value[] "
                + "export()>";
        String mapPort = "REGION.MAP.in.0";
        String outputPort = "REGION.MAP.out.0";
        String mapCell = "<example.ProjectionProducer: java.util.Map values>";
        String outputCell =
                "<example.Payload: example.Value[] values>";
        String fieldSignature = "<example.Value: long expiry>";
        String staticBindingId = "BIND.MAP.EXPIRY";
        String snapshotSite = method + "#u6";
        String materializationSite = snapshotSite + "#map-element:"
                + staticBindingId;

        JsonObject action = new JsonObject();
        action.addProperty("symbol", mapPort);
        action.addProperty("cell", mapCell);
        action.addProperty("field", mapCell);
        action.addProperty("javaType", "java.util.Map");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        JsonArray mapPath = new JsonArray();
        mapPath.add("values");
        action.add("fieldPath", mapPath);

        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind",
                "MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD");
        declaration.addProperty("bindingId", staticBindingId);
        declaration.addProperty("mapInputPort", mapPort);
        declaration.addProperty("mapInputCell", mapCell);
        declaration.addProperty("outputPort", outputPort);
        declaration.addProperty("outputCell", outputCell);
        declaration.add("outputFieldPath", singletonString("values"));
        declaration.addProperty("outputValidationMode",
                "ROOT_RETURN_PROJECTED_FIELD");
        declaration.addProperty("mapProjectionOperation", operation);
        declaration.addProperty("mapViewSiteId", method + "#u5");
        declaration.addProperty("snapshotSiteId", snapshotSite);
        declaration.addProperty("downstreamRegionInstance",
                "REGION.DOWNSTREAM@fixture#call2");
        declaration.addProperty("downstreamInputPort",
                "REGION.DOWNSTREAM.in.0");
        declaration.addProperty("downstreamBaseInputSymbol",
                "REGION.DOWNSTREAM.in.1");
        declaration.addProperty("downstreamContainerBindingId",
                "BIND.DOWNSTREAM.ARRAY.EXPIRY");
        declaration.addProperty("declaredFieldSignature", fieldSignature);
        declaration.addProperty("declaredFieldOwnerClass", "example.Value");
        declaration.addProperty("declaredFieldType", "long");
        declaration.addProperty("declaredFieldName", "expiry");
        declaration.add("fieldPath", singletonString("expiry"));
        declaration.addProperty("selectorAuthority",
                "CURRENT_EXECUTION_ENTRY_SNAPSHOT_THEN_EXACT_"
                        + "OUTPUT_INDEX_IDENTITY");
        declaration.add("projectionProofCausalEdgeIds",
                singletonString("EDGE.MAP.TO.ARRAY"));
        declaration.addProperty("recursiveElementProjectionComposable",
                true);
        declaration.addProperty("complete", true);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.MAP");
        activation.addProperty("regionId", "REGION.MAP");
        activation.addProperty("regionInstanceId",
                "REGION.MAP@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        slice.addProperty("outputPort", outputPort);
        slice.add("inputPorts", singletonString(mapPort));
        slice.add("methods", singletonString(method));
        activation.add("requestedOutputSlice", slice);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", outputPort);
        requested.addProperty("cell", outputCell);
        requested.addProperty("kind", "REFERENCE");
        activation.add("requestedOutput", requested);
        activation.add("materializations", singletonObject(action));
        activation.add("mapValueElementFieldProjections",
                singletonObject(declaration));
        write(activations, activation + "\n");

        JsonObject input = new JsonObject();
        input.addProperty("portId", mapPort);
        input.addProperty("cell", mapCell);
        input.addProperty("javaType", "java.util.Map");
        JsonObject outputSchema = new JsonObject();
        outputSchema.addProperty("portId", outputPort);
        outputSchema.addProperty("cell", outputCell);
        outputSchema.addProperty("javaType", "example.Value[]");
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.MAP");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        region.add("symbolicInputs", singletonObject(input));
        region.add("outputs", singletonObject(outputSchema));
        write(regions, region + "\n");

        JsonArray snapshotTokens = new JsonArray();
        snapshotTokens.add(601L);
        snapshotTokens.add(602L);
        JsonArray snapshotKeys = new JsonArray();
        snapshotKeys.add(constant("Y_I_11", "java/lang/Integer"));
        snapshotKeys.add(constant("Y_I_22", "java/lang/Integer"));
        JsonObject entry = mapProjectionObservation("ENTRY_SNAPSHOT",
                operation, mapPort, outputPort, outputCell, 501L);
        entry.addProperty("snapshotElementCount", 2);
        entry.add("snapshotElementObjectTokens", snapshotTokens.deepCopy());
        entry.add("snapshotEntryKeyExpressions", snapshotKeys.deepCopy());
        entry.addProperty("entryKeyExpressionAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        entry.addProperty("entrySnapshotComplete", true);
        JsonObject outputObservation = mapProjectionObservation(
                "OUTPUT_IDENTITY_VALIDATION", operation, mapPort,
                outputPort, outputCell, 501L);
        outputObservation.addProperty("outputIdentityVerified", true);
        outputObservation.addProperty("outputArrayObjectToken", 701L);
        outputObservation.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        outputObservation.addProperty("outputDeclaredFieldOwnerVerified",
                true);
        outputObservation.addProperty("outputDeclaredFieldTypeVerified",
                true);
        outputObservation.addProperty("projectedFieldBindingCount", 2);
        outputObservation.addProperty("outputFieldValueVerifiedCount", 2);
        outputObservation.addProperty("outputFieldValueFlowVerified", true);
        outputObservation.addProperty("fieldValueFlowAuthority",
                "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                        + "DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_INTERVENING_"
                        + "RUNTIME_FIELD_WRITE_AND_EXACT_OUTPUT_RECHECK");

        JsonArray bindings = new JsonArray();
        JsonArray fieldObservations = new JsonArray();
        JsonArray symbolized = singletonString(mapPort);
        for (int index = 0; index < 2; index++) {
            String dynamic = mapPort + ".field."
                    + testSha256(materializationSite).substring(0, 12)
                    + ".occ." + (index + 1);
            JsonObject selector = mapProjectionSelector(staticBindingId,
                    operation, mapPort, mapCell, outputPort, outputCell,
                    fieldSignature, index, 501L, 601L + index, 701L, true);
            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 3);
            binding.addProperty("kind",
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            binding.addProperty("baseInputSymbol", mapPort);
            binding.addProperty("dynamicFieldSymbol", dynamic);
            binding.addProperty("materializationSiteId", materializationSite);
            binding.addProperty("materializationOccurrence", index + 1);
            binding.addProperty("fieldSignature", fieldSignature);
            binding.add("fieldPath", singletonString("expiry"));
            binding.addProperty("leafOwnerObjectToken", 601L + index);
            binding.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            binding.addProperty("objectTokenScope", "ACT.MAP");
            binding.add("mapProjectionSelector", selector);
            binding.addProperty("authority",
                    "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                            + "EXACT_OUTPUT_IDENTITY");
            binding.addProperty("complete", true);
            bindings.add(binding);
            symbolized.add(dynamic);

            JsonObject observedSelector = selector.deepCopy();
            observedSelector.addProperty("outputArrayObjectToken", 0L);
            observedSelector.addProperty("outputIdentityVerified", false);
            observedSelector.addProperty("outputVerificationAuthority", "");
            observedSelector.addProperty(
                    "noInterveningFieldWriteVerified", false);
            observedSelector.addProperty("outputFieldValueVerified", false);
            observedSelector.addProperty("fieldValueFlowAuthority", "");
            observedSelector.addProperty("complete", false);
            JsonObject field = new JsonObject();
            field.addProperty("symbol", dynamic);
            field.addProperty("phase", "AT_MAP_PROJECTION_ENTRY");
            field.add("path", singletonString("expiry"));
            field.addProperty("exactFieldSignature", fieldSignature);
            field.addProperty("exactFieldSignatureAuthority",
                    "BYTECODE_GETFIELD_DECLARING_OWNER_NAME_AND_TYPE");
            field.addProperty("accessOwnerClass", "example.Value");
            field.addProperty("accessOwnerObjectToken", 601L + index);
            field.addProperty("accessOwnerObjectTokenKnown", true);
            field.addProperty("leafOwnerClass", "example.Value");
            field.addProperty("leafOwnerObjectToken", 601L + index);
            field.addProperty("leafOwnerObjectTokenKnown", true);
            field.addProperty("available", true);
            field.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            field.addProperty("objectTokenScope", "ACT.MAP");
            field.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            field.addProperty("dynamicFieldBindingKind",
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
            field.add("mapProjectionSelector", observedSelector);
            fieldObservations.add(field);
        }

        if ("SCOPE".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "objectTokenScope", "ACT.OTHER");
        } else if ("TOKEN".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "elementObjectToken", 0L);
        } else if ("ORDER".equals(fault)) {
            JsonElement first = bindings.remove(0);
            bindings.add(first);
        } else if ("LENGTH".equals(fault)) {
            entry.addProperty("snapshotElementCount", 3);
        } else if ("IDENTITY".equals(fault)) {
            outputObservation.addProperty("outputIdentityVerified", false);
        } else if ("TYPE".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "declaredFieldType", "int");
        } else if ("DUPLICATE_KEY".equals(fault)) {
            entry.getAsJsonArray("snapshotEntryKeyExpressions").set(1,
                    entry.getAsJsonArray("snapshotEntryKeyExpressions")
                            .get(0).deepCopy());
        } else if ("FLOAT_ZERO_KEY".equals(fault)) {
            JsonObject negativeZero = constant("Y_F_-0.0",
                    "java/lang/Float");
            entry.getAsJsonArray("snapshotEntryKeyExpressions").set(0,
                    negativeZero.deepCopy());
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").add("expectedMapKey",
                    negativeZero.deepCopy());
            fieldObservations.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").add("expectedMapKey",
                    negativeZero.deepCopy());
        } else if ("IDENTITY_MAP".equals(fault)) {
            entry.addProperty("mapImplementationClass",
                    "java.util.IdentityHashMap");
            outputObservation.addProperty("mapImplementationClass",
                    "java.util.IdentityHashMap");
            for (JsonElement element : bindings) {
                element.getAsJsonObject().getAsJsonObject(
                        "mapProjectionSelector").addProperty(
                        "mapImplementationClass",
                        "java.util.IdentityHashMap");
            }
            for (JsonElement element : fieldObservations) {
                element.getAsJsonObject().getAsJsonObject(
                        "mapProjectionSelector").addProperty(
                        "mapImplementationClass",
                        "java.util.IdentityHashMap");
            }
        } else if ("FIELD_WRITE".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "noInterveningFieldWriteVerified", false);
        } else if ("FIELD_VALUE".equals(fault)) {
            outputObservation.addProperty("outputFieldValueFlowVerified",
                    false);
        } else if ("IMPLEMENTATION_DRIFT".equals(fault)) {
            outputObservation.addProperty("mapImplementationClass",
                    "java.util.HashMap");
        } else if ("FIELD_SIGNATURE_DRIFT".equals(fault)) {
            fieldObservations.get(0).getAsJsonObject().addProperty(
                    "exactFieldSignature", "<example.Value: int expiry>");
        }

        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.MAP");
        engine.addProperty("activationId", "ACT.MAP");
        engine.add("pathCondition", new JsonArray());
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.MAP");
        raw.addProperty("regionId", "REGION.MAP");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", symbolized);
        raw.add("dynamicFieldBindings", bindings);
        raw.add("fieldObservations", fieldObservations);
        JsonArray projectionRows = new JsonArray();
        projectionRows.add(entry);
        projectionRows.add(outputObservation);
        raw.add("mapValueElementProjectionObservations", projectionRows);
        raw.add("rootOutputExpression", arrayValueExpression(
                "[Lexample/Value;", "Lexample/Value;", true,
                symbol("M_L_map_output_0", "Lexample/Value;"),
                symbol("M_L_map_output_1", "Lexample/Value;")));
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics, root.resolve("cache"));
        String rows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = rows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(rows).getAsJsonObject();
        return new MapFixture(summary, new String(Files.readAllBytes(
                diagnostics), StandardCharsets.UTF_8));
    }

    private static JsonObject mapProjectionObservation(
            String phase, String operation, String mapPort,
            String outputPort, String outputCell, long mapToken) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "MAP_VALUE_OUTPUT_ARRAY_PROJECTION");
        row.addProperty("phase", phase);
        row.addProperty("groupId", mapPort + "\n" + outputPort + "\n"
                + outputCell + "\n" + operation);
        row.addProperty("mapInputPort", mapPort);
        row.addProperty("outputPort", outputPort);
        row.addProperty("outputCell", outputCell);
        row.addProperty("mapProjectionOperation", operation);
        row.addProperty("mapObjectToken", mapToken);
        row.addProperty("mapImplementationClass",
                "java.util.LinkedHashMap");
        row.addProperty("mapImplementationAuthority",
                "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                        + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1");
        row.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        row.addProperty("objectTokenScope", "ACT.MAP");
        row.addProperty("crossExecutionOrdinalAuthority", "NONE");
        row.addProperty("identityPolicy",
                "ENTRYSET_KEY_AND_MAP_VIEW_ELEMENT_SAME_EXECUTION_"
                        + "POSITIONAL_REFERENCE_EQUALITY");
        row.addProperty("entrySetViewOrderVerified", true);
        row.addProperty("entrySetViewOrderAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        row.addProperty("complete", true);
        return row;
    }

    private static JsonObject mapProjectionSelector(
            String bindingId, String operation, String mapPort,
            String mapCell, String outputPort, String outputCell,
            String signature, int index, long mapToken, long elementToken,
            long outputToken, boolean complete) {
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", bindingId);
        selector.addProperty("mapInputPort", mapPort);
        selector.addProperty("mapInputCell", mapCell);
        selector.addProperty("outputPort", outputPort);
        selector.addProperty("outputCell", outputCell);
        selector.addProperty("mapProjectionOperation", operation);
        selector.addProperty("outputIndex", index);
        selector.addProperty("elementOccurrence", index + 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Value");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature", signature);
        selector.addProperty("mapObjectToken", mapToken);
        selector.addProperty("elementObjectToken", elementToken);
        selector.addProperty("outputArrayObjectToken", outputToken);
        selector.addProperty("outputIdentityVerified", complete);
        selector.addProperty("outputVerificationAuthority", complete
                ? "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD" : "");
        selector.addProperty("mapImplementationClass",
                "java.util.LinkedHashMap");
        selector.addProperty("mapImplementationAuthority",
                "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                        + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1");
        selector.addProperty("entryConcreteFieldValueCaptured", true);
        selector.addProperty("noInterveningFieldWriteVerified", complete);
        selector.addProperty("outputFieldValueVerified", complete);
        selector.addProperty("fieldValueFlowAuthority", complete
                ? "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                + "DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_INTERVENING_"
                + "RUNTIME_FIELD_WRITE_AND_EXACT_OUTPUT_RECHECK" : "");
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.MAP");
        selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
        selector.add("expectedMapKey", constant("Y_I_"
                + (index == 0 ? "11" : "22"), "java/lang/Integer"));
        selector.addProperty("expectedMapKeyAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        selector.addProperty("sourceOutputIndexAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        selector.addProperty("replaySelectionAuthority",
                "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_EXACT_"
                        + "OUTPUT_IDENTITY");
        selector.addProperty("authority",
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_EXACT_"
                        + "OUTPUT_IDENTITY");
        selector.addProperty("complete", complete);
        return selector;
    }


    private static String testSha256(String value) throws Exception {
        byte[] digest = MessageDigest.getInstance("SHA-256").digest(
                value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte current : digest) {
            result.append(String.format("%02x", current & 0xff));
        }
        return result.toString();
    }

    private static JsonObject engineArrayInputBinding(
            String port, String cell, String engineArrayId,
            long objectToken) {
        JsonObject expression = arrayValueExpression(
                "[Ljava/lang/Object;", "Ljava/lang/Object;", true);
        expression.addProperty("_engine_array_id", engineArrayId);
        expression.addProperty("_engine_array_id_authority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        result.addProperty("sourceActivationId", "ACT.ARRAY");
        result.addProperty("inputPort", port);
        result.addProperty("inputCell", cell);
        result.addProperty("inputJavaType", "java.lang.Object[]");
        result.addProperty("inputJavaTypeDescriptor",
                "[Ljava/lang/Object;");
        result.addProperty("symbolizationPrefix", port);
        result.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        result.addProperty("engineArrayId", engineArrayId);
        result.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        result.addProperty("arrayObjectToken", objectToken);
        result.addProperty("symbolizationArrayObjectToken", objectToken);
        result.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        result.addProperty("sameArrayObjectTokenVerified", true);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", "ACT.ARRAY");
        result.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        result.add("arrayValueExpression", expression);
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject arrayValueExpression(
            String javaType, String componentType, boolean complete,
            JsonElement... expressions) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ArrayValueExpression");
        result.addProperty("_schema_version", 1);
        result.addProperty("_java_type", javaType);
        result.addProperty("_component_java_type", componentType);
        result.addProperty("_concrete_length", expressions.length);
        result.add("_length_exp", constant("Y_I_" + expressions.length,
                "I"));
        result.addProperty("_elements_complete", complete);
        result.addProperty("_authority",
                "VM_EXACT_FINITE_ARRAY_VALUE_V1");
        JsonArray elements = new JsonArray();
        for (int index = 0; index < expressions.length; index++) {
            JsonObject element = new JsonObject();
            element.addProperty("index", index);
            element.addProperty("provenance", "SYMBOLIC_ELEMENT");
            element.add("expression", expressions[index].deepCopy());
            elements.add(element);
        }
        result.add("_elements", elements);
        return result;
    }

    private static JsonObject methodExpression(String name, int line,
                                               JsonElement... parameters) {
        return methodExpressionAt(name, "example.Store.update()", line,
                parameters);
    }

    private static JsonObject methodExpressionAt(
            String name, String method, int line, JsonElement... parameters) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "MethodExpression");
        result.addProperty("_name", name);
        result.addProperty("_code_position", "virtual void " + method
                + ":" + line);
        JsonArray params = new JsonArray();
        for (JsonElement parameter : parameters) {
            params.add(parameter);
        }
        result.add("_param_list", params);
        result.add("_res_exp", JsonNull.INSTANCE);
        return result;
    }

    private static JsonObject symbol(String expression, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", expression);
        return result;
    }

    private static JsonObject constant(String expression, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", expression);
        return result;
    }

    private static JsonObject stringConstant(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConStringSymbolExp");
        result.addProperty("_java_type", "java/lang/String");
        result.addProperty("_exp", "Y_L'String'_" + value);
        return result;
    }

    private static JsonObject stringPredicate(String codePosition,
                                              String operation,
                                              boolean negated,
                                              JsonElement... parameters) {
        JsonObject result = new JsonObject();
        result.addProperty("_code_position", codePosition);
        result.addProperty("_type", "OpStrExpression");
        result.addProperty("_name", operation);
        result.addProperty("_is_not", negated);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : parameters) {
            arguments.add(parameter);
        }
        result.add("_param_list", arguments);
        return result;
    }

    private static JsonObject symbolCopy(JsonObject value) {
        return value.deepCopy();
    }

    private static String effect(JsonArray effects, int index, String field) {
        return effects.get(index).getAsJsonObject().get(field).getAsString();
    }

    private static final class MapFixture {
        private final JsonObject summary;
        private final String diagnostics;

        private MapFixture(JsonObject summary, String diagnostics) {
            this.summary = summary;
            this.diagnostics = diagnostics;
        }
    }

    private static final class PlaceholderFixture {
        private final JsonObject summary;
        private final String diagnostics;

        private PlaceholderFixture(JsonObject summary, String diagnostics) {
            this.summary = summary;
            this.diagnostics = diagnostics;
        }
    }

    private static void write(Path path, String value) throws Exception {
        String[] lines = value.split("\\n", -1);
        StringBuilder canonical = new StringBuilder();
        for (int index = 0; index < lines.length; index++) {
            String line = lines[index];
            if (!line.trim().isEmpty()) {
                JsonElement parsed = JsonParser.parseString(line);
                if (parsed.isJsonObject()
                        && "CONCOLIC_REGION_RESULT".equals(
                        parsed.getAsJsonObject().has("event")
                                ? parsed.getAsJsonObject().get("event")
                                .getAsString() : "")) {
                    line = canonicalRuntimeResultForTest(
                            parsed.getAsJsonObject()).toString();
                } else if (parsed.isJsonObject()
                        && parsed.getAsJsonObject().has("activationId")) {
                    JsonObject activation = parsed.getAsJsonObject();
                    if (!activation.has("materializations")) {
                        JsonElement declarations = activation.get(
                                "symbolize");
                        activation.add("materializations",
                                declarations != null
                                        && declarations.isJsonArray()
                                        ? declarations.deepCopy()
                                        : new JsonArray());
                    }
                    line = activation.toString();
                }
            }
            canonical.append(line);
            if (index + 1 < lines.length) canonical.append('\n');
        }
        writeVerbatim(path, canonical.toString());
    }

    private static JsonObject canonicalRuntimeResultForTest(JsonObject raw) {
        JsonObject result = raw.deepCopy();
        if (!result.has("schemaVersion")) {
            result.addProperty("schemaVersion", 1);
        }
        if (!result.has("executionMode")) {
            result.addProperty("executionMode", "SYMBOLIC_CONCOLIC");
        }
        if (!result.has("pathConditionIsolationPolicy")) {
            result.addProperty("pathConditionIsolationPolicy",
                    ConcolicSummaryImporter.PATH_CONDITION_ISOLATION_POLICY);
        }
        for (String field : new String[]{"runtimeHeapObservations",
                "dynamicFieldBindings"}) {
            if (!result.has(field)) result.add(field, new JsonArray());
        }

        JsonObject engine = result.has("engineSummary")
                && result.get("engineSummary").isJsonObject()
                ? result.getAsJsonObject("engineSummary")
                : new JsonObject();
        if (!engine.has("schemaVersion")) {
            engine.addProperty("schemaVersion", 1);
        }
        if (!engine.has("engine")) {
            engine.addProperty("engine", "openjdk8-zero-concolic");
        }
        if (!engine.has("active")) engine.addProperty("active", true);
        if (!engine.has("regionId")) {
            engine.addProperty("regionId", result.get("regionId")
                    .getAsString());
        }
        if (!engine.has("activationId")) {
            engine.addProperty("activationId", result.get("activationId")
                    .getAsString());
        }
        if (!engine.has("threadContextId")) {
            engine.addProperty("threadContextId", 1L);
        }
        if (!engine.has("pathConditionRecordingPaused")) {
            engine.addProperty("pathConditionRecordingPaused", true);
        }
        if (!engine.has("pathConditionPauseDepth")) {
            engine.addProperty("pathConditionPauseDepth", 1);
        }
        if (!engine.has("pathCondition")) {
            engine.add("pathCondition", new JsonArray());
        }
        result.add("engineSummary", engine);
        return result;
    }

    private static void writeVerbatim(Path path, String value)
            throws Exception {
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }
}
