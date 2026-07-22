package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class ConcolicCampaignRunnerTest {
    @Test
    public void replayActivationCertificatesExactGenericReferenceNullGuard() {
        String engine = "M_L_REGION.9.in.0_example/Payload";
        JsonObject task = nullGuardTask(engine);
        JsonObject source = nullGuardSource("example.Payload");
        JsonObject assignment = nullGuardAssignment(engine,
                "example.Payload");

        JsonObject replay = ConcolicCampaignRunner.replayActivation(task,
                source, singleton(assignment));

        JsonArray proofs = replay.getAsJsonArray(
                "concreteGuardReplayProofs");
        assertEquals(replay.toString(), 1, proofs.size());
        JsonObject proof = proofs.get(0).getAsJsonObject();
        assertEquals("REFERENCE_NULL_CONCRETE_GUARD_REPLAY_PROOF",
                proof.get("kind").getAsString());
        assertEquals("SOLVER_EXACT_REFERENCE_NULL_GUARD_AND_"
                        + "MODEL_ASSIGNMENT_V1",
                proof.get("authority").getAsString());
        assertEquals(engine, proof.get("modelAssignmentKey").getAsString());
        assertEquals(engine, proof.get("engineSymbol").getAsString());
        assertEquals("REGION.9.in.0",
                proof.get("inputSymbol").getAsString());
        assertEquals("ROOT#u7", proof.get("siteId").getAsString());
        assertEquals("TARGET", proof.get("proofRole").getAsString());
        assertEquals(0, proof.get("sourceConditionIndex").getAsInt());
        assertEquals(0, proof.get("constraintIndex").getAsInt());
        assertEquals(-1, proof.get("expectedBranchPrefixOrdinal")
                .getAsInt());
        assertEquals(1, proof.get("occurrence").getAsInt());
        assertTrue(proof.get("outcome").getAsBoolean());
        assertEquals("==", proof.getAsJsonObject("condition")
                .get("_op").getAsString());
        assertEquals(64, proof.get("conditionSha256").getAsString()
                .length());
        assertTrue(proof.get("requiresExactVmBranchEvent").getAsBoolean());
        assertTrue(proof.get("requiresZeroPathConditionSuffix")
                .getAsBoolean());
        assertTrue(proof.get("requiresUniqueAppliedNullModelAssignment")
                .getAsBoolean());
    }

    @Test
    public void replayActivationDoesNotCertificateMismatchedOrPrimitiveNull() {
        String engine = "M_L_REGION.9.in.0_example/Payload";
        JsonObject task = nullGuardTask(engine);
        JsonObject source = nullGuardSource("example.Payload");
        JsonObject mismatch = nullGuardAssignment(
                "M_L_REGION.9.in.1_example/Payload", "example.Payload");
        JsonObject mismatchedReplay = ConcolicCampaignRunner
                .replayActivation(task, source, singleton(mismatch));
        assertEquals(0, mismatchedReplay.getAsJsonArray(
                "concreteGuardReplayProofs").size());

        JsonObject primitive = nullGuardAssignment(engine, "int");
        primitive.remove("referenceNullnessEncodingAuthority");
        JsonObject primitiveReplay = ConcolicCampaignRunner
                .replayActivation(task, nullGuardSource("int"),
                        singleton(primitive));
        assertEquals(0, primitiveReplay.getAsJsonArray(
                "concreteGuardReplayProofs").size());

        JsonArray duplicate = new JsonArray();
        duplicate.add(nullGuardAssignment(engine, "example.Payload"));
        duplicate.add(nullGuardAssignment(engine, "example.Payload"));
        JsonObject ambiguousReplay = ConcolicCampaignRunner
                .replayActivation(task, source, duplicate);
        assertEquals(0, ambiguousReplay.getAsJsonArray(
                "concreteGuardReplayProofs").size());

        JsonObject vmSymbolicTask = nullGuardTask(engine);
        vmSymbolicTask.addProperty("concreteGuardReplayProofRequired",
                false);
        JsonObject vmSymbolicReplay = ConcolicCampaignRunner
                .replayActivation(vmSymbolicTask, source, singleton(
                        nullGuardAssignment(engine, "example.Payload")));
        assertEquals("a VM-symbolic NULL guard must use its real PC instead "
                        + "of a conditionless-guard certificate", 0,
                vmSymbolicReplay.getAsJsonArray(
                        "concreteGuardReplayProofs").size());
        assertFalse(vmSymbolicReplay.getAsJsonObject("targetBranch")
                .get("concreteGuardReplayProofRequired").getAsBoolean());
    }

    @Test
    public void replayActivationCertificatesNullPrefixAndTargetCatalog() {
        String engine = "M_L_REGION.9.in.0_example/Payload";
        JsonObject task = nullGuardTask(engine);
        JsonObject condition = task.getAsJsonObject(
                "negatedCondition").deepCopy();
        JsonObject semantic = JsonParser.parseString(
                "{\"_type\":\"BinaryExpression\","
                        + "\"_left\":{\"_type\":\"SymbolExpression\","
                        + "\"_java_type\":\"I\",\"_exp\":\"M_I_x\"},"
                        + "\"_op\":\">=\",\"_right\":{"
                        + "\"_type\":\"ConstExpr\","
                        + "\"_java_type\":\"I\",\"_exp\":\"Y_I_0\"}}")
                .getAsJsonObject();
        JsonArray prefix = new JsonArray();
        prefix.add(semantic.deepCopy());
        prefix.add(condition.deepCopy());
        task.add("prefix", prefix);
        JsonArray constraints = new JsonArray();
        constraints.add(semantic.deepCopy());
        constraints.add(condition.deepCopy());
        constraints.add(condition.deepCopy());
        task.add("constraints", constraints);
        JsonObject expected = new JsonObject();
        expected.addProperty("siteId", "ROOT#u7");
        expected.addProperty("occurrence", 1);
        expected.addProperty("outcome", true);
        expected.addProperty("conditionIndex", 1);
        expected.addProperty("concreteGuardReplayProofRequired", true);
        task.add("expectedBranchPrefix", singleton(expected));
        task.addProperty("flipSite", "ROOT#u8");
        task.addProperty("conditionIndex", 2);

        JsonObject replay = ConcolicCampaignRunner.replayActivation(task,
                nullGuardSource("example.Payload"), singleton(
                        nullGuardAssignment(engine, "example.Payload")));

        JsonArray proofs = replay.getAsJsonArray(
                "concreteGuardReplayProofs");
        assertEquals(replay.toString(), 2, proofs.size());
        JsonObject prefixProof = proofs.get(0).getAsJsonObject();
        JsonObject targetProof = proofs.get(1).getAsJsonObject();
        assertEquals("PREFIX", prefixProof.get("proofRole").getAsString());
        assertEquals("ROOT#u7", prefixProof.get("siteId").getAsString());
        assertEquals(0, prefixProof.get("expectedBranchPrefixOrdinal")
                .getAsInt());
        assertEquals(1, prefixProof.get("sourceConditionIndex").getAsInt());
        assertEquals("TARGET", targetProof.get("proofRole").getAsString());
        assertEquals("ROOT#u8", targetProof.get("siteId").getAsString());
        assertEquals(2, targetProof.get("sourceConditionIndex").getAsInt());
        assertEquals(3, replay.getAsJsonArray(
                "pathReplayConstraints").size());
    }

    @Test
    public void replayActivationDistinguishesTwoNullAssignmentsAtRepeatedSite()
            throws Exception {
        String engineA = "M_L_REGION.9.in.0_example/Payload";
        String engineB = "M_L_REGION.9.in.1_example/Payload";
        JsonObject conditionA = nullGuardTask(engineA)
                .getAsJsonObject("negatedCondition").deepCopy();
        JsonObject conditionB = nullGuardTask(engineB)
                .getAsJsonObject("negatedCondition").deepCopy();
        JsonObject task = nullGuardTask(engineB);
        task.addProperty("flipOccurrence", 2);
        task.addProperty("conditionIndex", 1);
        task.add("prefix", singleton(conditionA.deepCopy()));
        JsonArray constraints = new JsonArray();
        constraints.add(conditionA.deepCopy());
        constraints.add(conditionB.deepCopy());
        task.add("constraints", constraints);
        JsonObject expected = new JsonObject();
        expected.addProperty("siteId", "ROOT#u7");
        expected.addProperty("occurrence", 1);
        expected.addProperty("outcome", true);
        expected.addProperty("conditionIndex", 0);
        expected.addProperty("concreteGuardReplayProofRequired", true);
        task.add("expectedBranchPrefix", singleton(expected));

        JsonObject actionA = nullGuardAction("example.Payload",
                "REGION.9.in.0", 0);
        JsonObject actionB = nullGuardAction("example.Payload",
                "REGION.9.in.1", 1);
        JsonObject source = nullGuardSource("example.Payload");
        JsonArray actions = new JsonArray();
        actions.add(actionA.deepCopy());
        actions.add(actionB.deepCopy());
        source.add("symbolize", actions.deepCopy());
        source.add("materializations", actions.deepCopy());
        JsonArray assignments = new JsonArray();
        assignments.add(nullGuardAssignment(engineA, "example.Payload",
                "REGION.9.in.0", 0));
        assignments.add(nullGuardAssignment(engineB, "example.Payload",
                "REGION.9.in.1", 1));

        JsonObject replay = ConcolicCampaignRunner.replayActivation(task,
                source, assignments);

        JsonArray proofs = replay.getAsJsonArray(
                "concreteGuardReplayProofs");
        assertEquals(replay.toString(), 2, proofs.size());
        JsonObject first = proofs.get(0).getAsJsonObject();
        JsonObject second = proofs.get(1).getAsJsonObject();
        assertEquals("PREFIX", first.get("proofRole").getAsString());
        assertEquals("TARGET", second.get("proofRole").getAsString());
        assertEquals("ROOT#u7", first.get("siteId").getAsString());
        assertEquals("ROOT#u7", second.get("siteId").getAsString());
        assertEquals(1, first.get("occurrence").getAsInt());
        assertEquals(2, second.get("occurrence").getAsInt());
        assertEquals(engineA, first.get("modelAssignmentKey")
                .getAsString());
        assertEquals(engineB, second.get("modelAssignmentKey")
                .getAsString());
    }

    @Test
    public void replayActivationRejectsDuplicateConcreteGuardEventIdentity() {
        String engine = "M_L_REGION.9.in.0_example/Payload";
        JsonObject condition = nullGuardTask(engine)
                .getAsJsonObject("negatedCondition").deepCopy();
        JsonObject task = nullGuardTask(engine);
        task.addProperty("conditionIndex", 1);
        task.add("prefix", singleton(condition.deepCopy()));
        JsonArray constraints = new JsonArray();
        constraints.add(condition.deepCopy());
        constraints.add(condition.deepCopy());
        task.add("constraints", constraints);
        JsonObject expected = new JsonObject();
        expected.addProperty("siteId", "ROOT#u7");
        expected.addProperty("occurrence", 1);
        expected.addProperty("outcome", true);
        expected.addProperty("conditionIndex", 0);
        expected.addProperty("concreteGuardReplayProofRequired", true);
        task.add("expectedBranchPrefix", singleton(expected));

        JsonObject replay = ConcolicCampaignRunner.replayActivation(task,
                nullGuardSource("example.Payload"), singleton(
                        nullGuardAssignment(engine, "example.Payload")));

        assertEquals(replay.toString(), 0, replay.getAsJsonArray(
                "concreteGuardReplayProofs").size());
    }

    @Test
    public void exactReplayScheduleAdmissionAcceptsOrderedPrefixAndTarget() {
        JsonObject task = exactScheduleTask();
        JsonObject raw = exactScheduleRaw();

        JsonObject admission = ConcolicCampaignRunner
                .exactReplayScheduleAdmission(task, raw);

        assertTrue(admission.toString(), admission.get("valid")
                .getAsBoolean());
        assertTrue(admission.getAsJsonObject("orderedPrefixValidation")
                .get("valid").getAsBoolean());
        assertTrue(admission.getAsJsonObject("scheduledTargetValidation")
                .get("valid").getAsBoolean());
    }

    @Test
    public void exactReplayScheduleAdmissionRejectsPrefixOrderAndOutcome() {
        JsonObject task = exactScheduleTask();
        JsonObject reversed = exactScheduleRaw();
        JsonArray mappings = reversed.getAsJsonArray("branchMappings");
        JsonArray reordered = new JsonArray();
        reordered.add(mappings.get(1).deepCopy());
        reordered.add(mappings.get(0).deepCopy());
        reordered.add(mappings.get(2).deepCopy());
        reversed.add("branchMappings", reordered);
        JsonObject orderAdmission = ConcolicCampaignRunner
                .exactReplayScheduleAdmission(task, reversed);
        assertFalse(orderAdmission.get("valid").getAsBoolean());
        assertFalse(orderAdmission.getAsJsonObject(
                "orderedPrefixValidation").get(
                "runtimePositionsStrictlyIncreasing").getAsBoolean());

        JsonObject wrongOutcome = exactScheduleRaw();
        wrongOutcome.getAsJsonArray("branchMappings").get(0)
                .getAsJsonObject().addProperty("effectiveOutcome", false);
        JsonObject outcomeAdmission = ConcolicCampaignRunner
                .exactReplayScheduleAdmission(task, wrongOutcome);
        assertFalse(outcomeAdmission.get("valid").getAsBoolean());
        assertFalse(outcomeAdmission.getAsJsonObject(
                "orderedPrefixValidation").get(
                "runtimeOutcomesExactAndUnforced").getAsBoolean());
    }

    @Test
    public void exactReplayScheduleAdmissionRejectsWrongOrMissingTarget() {
        JsonObject task = exactScheduleTask();
        JsonObject wrongOccurrence = exactScheduleRaw();
        wrongOccurrence.getAsJsonArray("branchMappings").get(2)
                .getAsJsonObject().addProperty("occurrence", 2);
        assertFalse(ConcolicCampaignRunner.exactReplayScheduleAdmission(
                task, wrongOccurrence).get("valid").getAsBoolean());

        JsonObject wrongOutcome = exactScheduleRaw();
        JsonObject target = wrongOutcome.getAsJsonArray("branchMappings")
                .get(2).getAsJsonObject();
        target.addProperty("observedOutcome", false);
        target.addProperty("effectiveOutcome", false);
        target.addProperty("scheduledOutcomeMatched", false);
        assertFalse(ConcolicCampaignRunner.exactReplayScheduleAdmission(
                task, wrongOutcome).get("valid").getAsBoolean());

        JsonObject missingScheduleEvidence = exactScheduleRaw();
        missingScheduleEvidence.getAsJsonArray("branchMappings").get(2)
                .getAsJsonObject().remove("scheduledTarget");
        JsonObject missingAdmission = ConcolicCampaignRunner
                .exactReplayScheduleAdmission(task,
                        missingScheduleEvidence);
        assertFalse(missingAdmission.get("valid").getAsBoolean());
        assertTrue(missingAdmission.getAsJsonArray("failures").toString()
                .contains("SCHEDULED_FLIP_TARGET_NOT_EXACT"));
    }

    @Test
    public void campaignDoesNotCacheReplayWithoutExactSchedulerEvidence()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        MissingScheduleEvidenceBackend backend =
                new MissingScheduleEvidenceBackend();

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 4, 4, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertEquals(2, backend.executions);
        assertTrue(result.state.pathRecords.toString(),
                result.state.pathRecords.toString().contains(
                        "SCHEDULED_FLIP_TARGET_NOT_EXACT"));
        assertFalse(result.state.summaries.stream().anyMatch(value ->
                text(value, "activationId").startsWith("ACT.PATH.")));
        assertFalse(result.manifest.get("complete").getAsBoolean());
    }

    @Test
    public void solverFlipGetsFreshSingleMemberBundleAndScheduleIdentity()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject seed = fixture.state.activations.stream()
                .filter(value -> "ACT.U.SEED".equals(text(value,
                        "activationId")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "seed activation missing"));
        seed.addProperty("scheduleId", "SCHEDULE.SEED");
        seed.addProperty("executionPhase", "CAPTURE_OUTPUT_PATH");
        seed.addProperty("activationSelectionRequired", "ACT.U.SEED");
        seed.addProperty("activationBundleRootActivationId", "ACT.U.SEED");
        seed.addProperty("activationBundleScheduleId", "SCHEDULE.SEED");
        seed.addProperty("activationBundleSize", 1);
        seed.addProperty("activationBundleIndex", 0);
        seed.addProperty("activationBundleMemberRole", "PRIMARY");
        seed.addProperty("reachabilitySupportForActivationId",
                "ACT.STALE.ROOT");
        FakeBackend backend = new FakeBackend();

        ConcolicCampaignRunner.run(fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(4, 2, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertEquals(Arrays.asList("OUTPUT_SEED", "PATH_FLIP"),
                backend.kinds);
        JsonObject seedReplay = backend.requests.get(0)
                .getAsJsonObject("activation");
        assertTrue(text(seedReplay, "activationId").startsWith(
                "ACT.OUTPUT."));
        assertEquals("SCHEDULE.SEED", text(seedReplay, "scheduleId"));
        assertEquals("CAPTURE_OUTPUT_PATH", text(seedReplay,
                "executionPhase"));
        assertEquals("ACT.U.SEED", text(seedReplay,
                "activationBundleRootActivationId"));

        JsonObject request = backend.requests.get(1);
        JsonObject task = request.getAsJsonObject("pathTask");
        String suffix = shortHashForTest(text(task, "queryKey"));
        String activationId = "ACT.PATH." + suffix;
        String scheduleId = "SCHEDULE.PATH." + suffix;
        JsonObject replay = request.getAsJsonObject("activation");
        assertEquals(activationId, text(replay, "activationId"));
        assertEquals(scheduleId, text(replay, "scheduleId"));
        assertFalse("SCHEDULE.SEED".equals(text(replay, "scheduleId")));
        assertEquals("REPLAY_OUTPUT_PATH_FLIP", text(replay,
                "executionPhase"));
        assertEquals(activationId, text(replay,
                "activationSelectionRequired"));
        assertEquals(activationId, text(replay,
                "activationBundleRootActivationId"));
        assertEquals(scheduleId, text(replay,
                "activationBundleScheduleId"));
        assertEquals(1, replay.get("activationBundleSize").getAsInt());
        assertEquals(0, replay.get("activationBundleIndex").getAsInt());
        assertEquals("PRIMARY", text(replay,
                "activationBundleMemberRole"));
        assertFalse(replay.has("reachabilitySupportForActivationId"));
    }

    @Test
    public void closesSeedFlipImportCacheAndMergeLoopAutomatically()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        FakeBackend backend = new FakeBackend();
        ConcolicCampaignRunner.Bounds bounds = new ConcolicCampaignRunner.Bounds(
                32, 32, 32, 60_000L, 10_000L,
                RecursiveRegionWorklist.Bounds.defaults(),
                RegionPathWorklist.Bounds.defaults());

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend, bounds, Paths.get("z3"));

        assertTrue(result.manifest.toString(),
                result.manifest.get("complete").getAsBoolean());
        assertEquals("COMPLETE_AUTOMATIC_REGION_CLOSURE",
                result.manifest.get("status").getAsString());
        // Once the opposite branch is admitted, its summary is exact evidence
        // for the reverse frontier.  Do not execute that already-covered flip
        // a second time.
        assertEquals(2, backend.executions);
        assertEquals(Arrays.asList("OUTPUT_SEED", "PATH_FLIP"),
                backend.kinds);
        assertEquals(1, result.state.pathRecords.size());
        assertEquals(1, result.mergedSummaries.size());
        assertEquals(2, result.mergedSummaries.get(0)
                .getAsJsonObject("regionRelation").get("caseCount")
                .getAsInt());
        assertFalse(result.manifest.get("domainSemanticAdapterUsed")
                .getAsBoolean());
        assertFalse(result.manifest.get("branchOverrideAccepted")
                .getAsBoolean());
        assertTrue(result.manifest.get(
                "eligibleToReportAutomaticRelationship").getAsBoolean());
        assertEquals("SAME_EXECUTION_REQUIRED", text(result.manifest,
                "runtimeDiscoveryMode"));
        assertTrue(result.manifest.get(
                "sameExecutionRuntimeDiscoveryRequired").getAsBoolean());
        assertTrue(result.manifest.get(
                "runtimeGraphClosureClaimed").getAsBoolean());
        assertFalse(result.manifest.get(
                "eligibleToReportBoundedFixedGraphRelationship")
                .getAsBoolean());

        java.nio.file.Path output = Files.createTempDirectory(
                "campaign-resume-test-");
        ConcolicCampaignRunner.writeOutputs(output, result);
        assertTrue(Files.size(output.resolve("campaign_activations.jsonl"))
                > 0L);
        assertTrue(Files.size(output.resolve(
                "campaign_edge_validations.jsonl")) > 0L);
        assertTrue(Files.size(output.resolve("campaign_roots.jsonl")) > 0L);
        assertTrue(Files.size(output.resolve(
                "campaign_state_manifest.json")) > 0L);
    }

    @Test
    public void fixedValidatedGraphReportsOnlyBoundedFixedGraphEligibility()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        FixedGraphBackend backend = new FixedGraphBackend();

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(
                        32, 32, 32, 60_000L, 10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertTrue(result.manifest.toString(),
                result.manifest.get("complete").getAsBoolean());
        assertEquals("FIXED_VALIDATED_GRAPH", text(result.manifest,
                "runtimeDiscoveryMode"));
        assertEquals("COMPLETE_BOUNDED_FIXED_RUNTIME_GRAPH_CLOSURE",
                text(result.manifest, "status"));
        assertFalse(result.manifest.get(
                "sameExecutionRuntimeDiscoveryRequired").getAsBoolean());
        assertFalse(result.manifest.get(
                "runtimeGraphClosureClaimed").getAsBoolean());
        assertFalse(result.manifest.get(
                "eligibleToReportAutomaticRelationship").getAsBoolean());
        assertTrue(result.manifest.get(
                "eligibleToReportBoundedFixedGraphRelationship")
                .getAsBoolean());
        assertEquals(
                "VALIDATED_UNFORCED_REPLAYS_WITHIN_RUNTIME_SELECTED_FIXED_GRAPH_AND_DECLARED_BOUNDS",
                text(result.manifest, "soundnessScope"));
        // A fixed-graph campaign must ignore any accidental discovery rows
        // returned by a custom backend instead of widening its authority.
        assertFalse(result.state.edges.stream().anyMatch(value ->
                "EDGE.V.T".equals(text(value, "edgeId"))));
        assertFalse(result.state.activations.stream().anyMatch(value ->
                text(value, "activationId").startsWith("DISCOVERED.")));
    }

    @Test
    public void campaignSnapshotRoundTripsAndRejectsTamperOrPartialGeneration()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, new FakeBackend(),
                new ConcolicCampaignRunner.Bounds(32, 32, 32, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));
        Path output = Files.createTempDirectory("campaign-snapshot-");
        Path regions = output.resolve("regions.jsonl");
        writeJsonlForTest(regions, result.state.regions);
        ConcolicCampaignRunner.writeOutputs(output, result);
        String[] argv = snapshotCli(output, regions);

        JsonObject driftedRegion = new JsonObject();
        driftedRegion.addProperty("regionId", "REGION.DRIFTED");
        writeJsonlForTest(regions,
                Collections.singletonList(driftedRegion));

        ConcolicCampaignRunner.State restored =
                ConcolicCampaignRunner.readCliState(argv);
        assertEquals(text(result.state.regions.get(0), "regionId"),
                text(restored.regions.get(0), "regionId"));
        assertEquals(text(result.state.roots.get(0), "activationId"),
                text(restored.roots.get(0), "activationId"));
        assertEquals(result.state.summaries.size(),
                restored.summaries.size());
        assertEquals(result.state.pathRecords.size(),
                restored.pathRecords.size());
        ConcolicCampaignRunner.State automatic =
                ConcolicCampaignRunner.readCliState(snapshotCliWithoutResume(
                        output, regions));
        assertEquals(text(result.state.roots.get(0), "activationId"),
                text(automatic.roots.get(0), "activationId"));

        JsonObject pointer = JsonParser.parseString(new String(
                Files.readAllBytes(output.resolve(
                        "campaign_state_manifest.json")),
                StandardCharsets.UTF_8)).getAsJsonObject();
        Path immutableManifest = output.resolve(text(pointer, "manifest"));
        JsonObject generation = JsonParser.parseString(new String(
                Files.readAllBytes(immutableManifest),
                StandardCharsets.UTF_8)).getAsJsonObject();
        assertEquals(2, pointer.get("schemaVersion").getAsInt());
        assertEquals(2, generation.get("schemaVersion").getAsInt());
        assertEquals(text(pointer, "campaignCompleteManifestSha256"),
                text(generation, "campaignCompleteManifestSha256"));
        Path immutableCompletion = output.resolve(text(pointer,
                "campaignCompleteManifest"));
        assertEquals(text(generation, "campaignCompleteManifest"),
                immutableCompletion.getFileName().toString());
        assertArrayEquals(Files.readAllBytes(output.resolve(
                        "concolic_campaign_manifest.json")),
                Files.readAllBytes(immutableCompletion));
        String rootsFile = "";
        for (JsonElement element : generation.getAsJsonArray("stateFiles")) {
            JsonObject entry = element.getAsJsonObject();
            if ("ROOTS".equals(text(entry, "role"))) {
                rootsFile = text(entry, "file");
            }
        }
        assertFalse(rootsFile.isEmpty());
        Files.write(immutableManifest.getParent().resolve(rootsFile),
                "{}\n".getBytes(StandardCharsets.UTF_8),
                java.nio.file.StandardOpenOption.APPEND);
        assertSnapshotReadFails(argv,
                "CAMPAIGN_STATE_FILE_HASH_MISMATCH:ROOTS");

        ConcolicCampaignRunner.writeOutputs(output, result);
        pointer = JsonParser.parseString(new String(Files.readAllBytes(
                output.resolve("campaign_state_manifest.json")),
                StandardCharsets.UTF_8)).getAsJsonObject();
        immutableCompletion = output.resolve(text(pointer,
                "campaignCompleteManifest"));
        Files.write(immutableCompletion, "{}\n".getBytes(
                        StandardCharsets.UTF_8),
                java.nio.file.StandardOpenOption.APPEND);
        assertSnapshotReadFails(argv,
                "CAMPAIGN_COMPLETION_SNAPSHOT_HASH_MISMATCH");

        ConcolicCampaignRunner.writeOutputs(output, result);
        pointer = JsonParser.parseString(new String(Files.readAllBytes(
                output.resolve("campaign_state_manifest.json")),
                StandardCharsets.UTF_8)).getAsJsonObject();
        pointer.addProperty("campaignCompleteManifestSha256",
                "0000000000000000000000000000000000000000000000000000000000000000");
        Files.write(output.resolve("campaign_state_manifest.json"),
                (pointer.toString() + "\n").getBytes(StandardCharsets.UTF_8));
        assertSnapshotReadFails(argv,
                "CAMPAIGN_COMPLETION_SNAPSHOT_BINDING_MISMATCH");

        ConcolicCampaignRunner.writeOutputs(output, result);
        pointer = JsonParser.parseString(new String(Files.readAllBytes(
                output.resolve("campaign_state_manifest.json")),
                StandardCharsets.UTF_8)).getAsJsonObject();
        immutableManifest = output.resolve(text(pointer, "manifest"));
        Files.delete(immutableManifest);
        assertSnapshotReadFails(argv,
                "CAMPAIGN_STATE_GENERATION_MANIFEST_MISSING");
    }

    @Test
    public void campaignLockRejectsConcurrentOwnerAndReleasesCleanly()
            throws Exception {
        Path output = Files.createTempDirectory("campaign-lock-");
        try (ConcolicCampaignRunner.CampaignLock ignored =
                     ConcolicCampaignRunner.acquireCampaignLock(output)) {
            try {
                ConcolicCampaignRunner.acquireCampaignLock(output);
                throw new AssertionError(
                        "second campaign unexpectedly acquired the lock");
            } catch (java.io.IOException expected) {
                assertTrue(expected.getMessage().contains(
                        "CAMPAIGN_ALREADY_RUNNING"));
            }
        }
        try (ConcolicCampaignRunner.CampaignLock ignored =
                     ConcolicCampaignRunner.acquireCampaignLock(output)) {
            assertTrue(Files.isRegularFile(output.resolve("campaign.lock")));
        }
    }

    @Test
    public void rejectsUnvalidatedOrCrossInstanceTargetRootBeforeExecution()
            throws Exception {
        for (int mode = 0; mode < 2; mode++) {
            Fixture fixture = fixture();
            JsonObject root = fixture.state.roots.get(0);
            String expectedGap;
            if (mode == 0) {
                root.addProperty("replayAlreadyValidated", false);
                expectedGap = "TARGET_REPLAY_NOT_VALIDATED";
            } else {
                root.getAsJsonObject("validatedTargetSummary").addProperty(
                        "regionInstanceId", "REGION.T@other-trace#call2");
                expectedGap =
                        "VALIDATED_TARGET_SUMMARY_INSTANCE_MISMATCH";
            }
            FakeBackend backend = new FakeBackend();

            ConcolicCampaignRunner.Result result =
                    ConcolicCampaignRunner.run(fixture.state, backend,
                            new ConcolicCampaignRunner.Bounds(
                                    4, 4, 4, 10_000L, 1_000L,
                                    RecursiveRegionWorklist.Bounds.defaults(),
                                    RegionPathWorklist.Bounds.defaults()),
                            Paths.get("z3"));

            assertEquals(0, backend.executions);
            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertEquals(0, result.manifest.get(
                    "admittedTargetRootCount").getAsInt());
            assertFalse(result.manifest.get(
                    "targetRootAdmissionComplete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                    .contains(expectedGap));
        }
    }

    @Test
    public void leavesMappingOnlyEdgeAsGapWithoutLaunchingCapture()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject edge = fixture.state.edges.get(0);
        edge.addProperty("composable", false);
        edge.addProperty("eligibleForAutomaticDerivation", false);
        edge.addProperty("eligibleForAutomaticSmt", false);
        edge.addProperty("eligibleForRecursiveDiscovery", true);
        edge.addProperty("status",
                "PORT_MAPPING_OBSERVED_VALUE_EQUALITY_UNPROVEN");
        edge.addProperty("valueEqualityObserved", false);
        edge.addProperty("confirmedValueEqualityPairCount", 0);
        edge.addProperty("exclusionReason",
                "RUNTIME_VALUE_EQUALITY_NOT_PROVEN");
        FakeBackend backend = new FakeBackend();

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(4, 4, 4, 10_000L,
                        1_000L, RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals(0, backend.executions);
        assertEquals(0, result.manifest.get(
                "automaticallyEligibleUpstreamRequestCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "deferredUnprovenMappingRequestCount").getAsInt());
        assertFalse(result.manifest.get("unprovenMappingRequestsExecuted")
                .getAsBoolean());
    }

    @Test
    public void outputCapturePrefersActivationBoundToExactDownstreamCall() {
        Fixture fixture = fixture();
        JsonObject old = fixture.state.activations.get(0);
        old.addProperty("activationId", "ACT.UPSTREAM.2");
        old.addProperty("regionInstanceId", "REGION.U#call3468");
        old.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requestedOutput = new JsonObject();
        requestedOutput.addProperty("portId", "REGION.U.out.0");
        old.add("requestedOutput", requestedOutput);

        JsonObject aligned = old.deepCopy();
        aligned.addProperty("activationId", "ACT.UPSTREAM.3");
        aligned.addProperty("regionInstanceId", "REGION.U#call3545");
        JsonArray bindings = new JsonArray();
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE.U.T");
        binding.addProperty("fromOutputPort", "REGION.U.out.0");
        binding.addProperty("fromOutputCell",
                "<example.Upstream: int value>");
        binding.addProperty("toInputPort", "REGION.T.in.0");
        binding.addProperty("toInputCell", "<example.Target: int value>");
        binding.addProperty("toRegionInstance", "REGION.T#call7004");
        bindings.add(binding);
        aligned.add("edgeBindings", bindings);
        fixture.state.activations.add(aligned);

        JsonObject request = new JsonObject();
        request.addProperty("requestId", "REQUEST.TARGET.ALIGNED");
        request.addProperty("upstreamRegion", "REGION.U");
        request.addProperty("upstreamOutputPort",
                "<example.Upstream: int value>");
        request.addProperty("downstreamInputPort",
                "<example.Target: int value>");
        request.addProperty("downstreamRegionInstance",
                "REGION.T#call7004");
        request.addProperty("edgeId", "EDGE.U.T");
        JsonArray references = new JsonArray();
        JsonObject oldReference = new JsonObject();
        oldReference.addProperty("activationId", "ACT.UPSTREAM.2");
        references.add(oldReference);
        JsonObject alignedReference = new JsonObject();
        alignedReference.addProperty("activationId", "ACT.UPSTREAM.3");
        references.add(alignedReference);
        request.add("upstreamActivations", references);

        JsonObject selected = ConcolicCampaignRunner.outputActivation(request,
                fixture.state);

        assertEquals("REGION.U#call3545", selected.get(
                "regionInstanceId").getAsString());
        assertEquals("ACT.UPSTREAM.3", selected.get(
                "selectedUpstreamActivationId").getAsString());
        assertEquals("REGION.T#call7004", selected.getAsJsonArray(
                "edgeBindings").get(0).getAsJsonObject().get(
                "toRegionInstance").getAsString());
    }

    @Test
    public void acceptedExecutionNamespacesAndAdmitsNewGraphEvidence()
            throws Exception {
        Fixture fixture = fixture();
        fixture.state.regions.add(region("REGION.V", "REGION.V.out.0",
                "<example.V: int value>"));
        DiscoveryBackend backend = new DiscoveryBackend(true, false);
        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 1, 8, 10_000L,
                        1_000L, RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertTrue(result.state.activations.stream().anyMatch(value ->
                "EXEC.seed::ACT.0".equals(text(value, "activationId"))
                        && "EXEC.seed::REGION.V@test#call1".equals(
                        text(value, "regionInstanceId"))));
        JsonObject edge = result.state.edges.stream().filter(value ->
                "EDGE.V.T".equals(text(value, "edgeId")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "dynamic edge was not admitted"));
        JsonObject binding = edge.getAsJsonArray("validatedBindings")
                .get(0).getAsJsonObject();
        assertEquals("EXEC.seed::REGION.V@test#call1",
                text(binding, "fromRegionInstance"));
        assertEquals("EXEC.seed::REGION.T@test#call2",
                text(binding, "toRegionInstance"));
        assertTrue(result.manifest.getAsJsonObject("graphWorklist")
                .getAsJsonArray("visitedRegions").toString()
                .contains("REGION.V"));
    }

    @Test
    public void discoveredEdgeBindingsUnionWithoutDowngradingProof()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject existing = fixture.state.edges.get(0);
        JsonArray oldBindings = new JsonArray();
        JsonObject oldBinding = new JsonObject();
        oldBinding.addProperty("fromRegionInstance", "REGION.U#old");
        oldBinding.addProperty("toRegionInstance", "REGION.T#old");
        oldBinding.addProperty("valueEqualityObserved", true);
        oldBindings.add(oldBinding);
        existing.add("validatedBindings", oldBindings);
        existing.addProperty("validatedBindingCount", 1);

        EdgeMergeBackend backend = new EdgeMergeBackend();
        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(4, 1, 4, 10_000L,
                        1_000L, RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        JsonObject merged = result.state.edges.stream().filter(value ->
                "EDGE.U.T".equals(text(value, "edgeId")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "merged edge missing"));
        assertTrue(merged.get("composable").getAsBoolean());
        assertEquals("CONFIRMED_RUNTIME_VALUE_EQUALITY",
                text(merged, "status"));
        assertEquals(2, merged.getAsJsonArray("validatedBindings").size());
        assertTrue(merged.getAsJsonArray("validatedBindings").toString()
                .contains("EXEC.merge::REGION.U#new"));
    }

    @Test
    public void rejectedSeedDoesNotAdmitDiscoveredEvidence()
            throws Exception {
        Fixture fixture = fixture();
        fixture.state.regions.add(region("REGION.V", "REGION.V.out.0",
                "<example.V: int value>"));
        DiscoveryBackend backend = new DiscoveryBackend(false, false);

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(2, 1, 2, 10_000L,
                        1_000L, RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertFalse(result.state.activations.stream().anyMatch(value ->
                text(value, "activationId").startsWith("EXEC.seed::")));
        assertFalse(result.state.edges.stream().anyMatch(value ->
                "EDGE.V.T".equals(text(value, "edgeId"))));
    }

    @Test
    public void onlyValidatedUnforcedFlipAdmitsItsDiscovery()
            throws Exception {
        Assume.assumeTrue(z3Available());
        for (boolean validReplay : Arrays.asList(true, false)) {
            Fixture fixture = fixture();
            fixture.state.regions.add(region("REGION.V", "REGION.V.out.0",
                    "<example.V: int value>"));
            FlipDiscoveryBackend backend = new FlipDiscoveryBackend(
                    validReplay);

            ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                    fixture.state, backend,
                    new ConcolicCampaignRunner.Bounds(8, 2, 4, 10_000L,
                            10_000L,
                            RecursiveRegionWorklist.Bounds.defaults(),
                            RegionPathWorklist.Bounds.defaults()),
                    Paths.get("z3"));

            assertEquals(validReplay, result.state.activations.stream()
                    .anyMatch(value -> text(value, "activationId")
                            .startsWith("EXEC.flip::")));
            assertEquals(validReplay, result.state.edges.stream()
                    .anyMatch(value -> "EDGE.V.T".equals(
                            text(value, "edgeId"))));
        }
    }

    @Test
    public void focusedTransitionRunsBeforeOrdinaryClosureAndStopsOnPromotion()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFixture();
        FocusedTransitionBackend backend = new FocusedTransitionBackend();
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(5, 3, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Arrays.asList("TRANSITION_DISCOVERY_SEED", "PATH_FLIP",
                "TARGET_REBASE"), backend.kinds);
        assertEquals(3, result.manifest.get("executionCount").getAsInt());
        assertEquals(1, result.manifest.get("solverQueryCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "transitionPromotionCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "targetRebaseExecutionCount").getAsInt());
        assertEquals(result.manifest.toString(), 1, result.manifest.get(
                "targetRebaseValidationCount").getAsInt());
        assertTrue(result.manifest.get("focusedTargetComplete")
                .getAsBoolean());
        assertTrue(result.manifest.get("complete").getAsBoolean());
        assertEquals("COMPLETE_FOCUSED_TRANSITION_DISCOVERY",
                text(result.manifest, "status"));
        assertFalse(result.manifest.get(
                "eligibleToReportAutomaticRelationship").getAsBoolean());
        assertTrue(result.state.pathRecords.stream().anyMatch(value ->
                "TRANSITION_VALIDATED".equals(text(value, "status"))));
        JsonObject promoted = result.state.summaries.stream().filter(value ->
                value.has("transitionDiscoveryProvenance"))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "focused transition summary was not promoted"));
        assertEquals("ACT.U.SEED", text(promoted.getAsJsonObject(
                "transitionDiscoveryProvenance"), "sourceActivationId"));
        assertEquals("EXEC.focus.flip::REGION.U@test#call1",
                text(promoted, "regionInstanceId"));
        assertEquals(text(promoted, "regionInstanceId"),
                text(promoted.getAsJsonArray("edgeBindings").get(0)
                        .getAsJsonObject(), "fromRegionInstance"));
        assertEquals("EXEC.focus.flip::REGION.V@test#call2",
                text(promoted.getAsJsonArray("edgeBindings").get(0)
                        .getAsJsonObject(), "toRegionInstance"));
        assertTrue(result.state.edges.stream().anyMatch(value ->
                "EDGE.U.V".equals(text(value, "edgeId"))
                        && value.get("composable").getAsBoolean()));
        JsonObject consumer = result.state.activations.stream()
                .filter(value -> "REGION.V".equals(text(value, "regionId")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "consumer activation was not admitted"));
        assertEquals(1, consumer.getAsJsonArray(
                "reachabilitySupportActivations").size());
        assertTrue(text(consumer.getAsJsonArray(
                "reachabilitySupportActivations").get(0)
                .getAsJsonObject(), "activationId").startsWith("ACT.PATH."));
        assertTrue(result.manifest.get(
                "postDiscoveryTargetRebaseReady").getAsBoolean());
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW", text(
                result.manifest, "postDiscoveryTargetRebaseActivationId"));
        assertEquals("EXEC.focus.flip::REGION.T@test#call9", text(
                result.manifest,
                "postDiscoveryTargetRebaseRegionInstanceId"));
        assertFalse("REGION.T@test#call2".equals(text(result.manifest,
                "postDiscoveryTargetRebaseRegionInstanceId")));
        assertTrue(result.manifest.get(
                "postDiscoveryTargetRebaseCompleted").getAsBoolean());
        assertFalse(result.manifest.get(
                "postDiscoveryTargetRebaseRequired").getAsBoolean());
        JsonObject rebasedRoot = result.state.roots.get(0);
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW",
                text(rebasedRoot, "activationId"));
        assertEquals("EXEC.focus.flip::REGION.T@test#call9",
                text(rebasedRoot, "regionInstanceId"));
        assertEquals("FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                        + "TARGET_REPLAY",
                text(rebasedRoot, "replayValidationAuthority"));
        assertEquals("FRESH_INSTANCE_IMPORTED_UNFORCED_TARGET_PREFIX_PLUS_"
                        + "OBSERVED_TARGET",
                text(rebasedRoot, "formulaAuthority"));
        assertFalse(rebasedRoot.getAsJsonObject("symbolicContext")
                .toString().contains("REGION.T@test#call2"));
        assertTrue(rebasedRoot.getAsJsonObject("symbolicContext")
                .toString().contains(
                        "EXEC.focus.flip::REGION.T@test#call9"));
        JsonObject admittedFreshSummary = result.state.summaries.stream()
                .filter(value -> "ADMITTED_FRESH_VALIDATED_TARGET".equals(
                        text(value, "summaryCacheAdmission")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "fresh target summary was not admitted"));
        assertTrue(admittedFreshSummary.has("directedTargetQuery"));
        assertTrue(admittedFreshSummary.has("freshObservedTargetQuery"));
        assertTrue(admittedFreshSummary.has("derivedDirectedTargetQuery"));
        assertFalse(admittedFreshSummary.get("directedTargetQuery").equals(
                admittedFreshSummary.get("freshObservedTargetQuery")));
        JsonObject freshObservedQuery = admittedFreshSummary
                .getAsJsonObject("freshObservedTargetQuery");
        assertEquals(text(rebasedRoot, "activationId"),
                text(freshObservedQuery, "activationId"));
        assertEquals(rebasedRoot.get("constraints"),
                freshObservedQuery.get("constraints"));
        assertEquals(rebasedRoot.get("symbolicContext"),
                freshObservedQuery.get("symbolicContext"));
        assertEquals(text(admittedFreshSummary, "derivedQuerySha256"),
                text(admittedFreshSummary.getAsJsonObject(
                        "freshTargetSummaryAdmission"),
                        "derivedQuerySha256"));
        assertEquals("CURRENT_EDGE_LEDGER_EXACT_TARGET_ENDPOINT_INSTANCE",
                text(admittedFreshSummary.getAsJsonObject(
                        "freshTargetSummaryAdmission"), "edgeAuthority"));
        assertFalse(backend.kinds.contains("OUTPUT_SEED"));

        Path snapshotDirectory = Files.createTempDirectory(
                "fresh-target-resume-");
        Path snapshotRegions = snapshotDirectory.resolve("regions.jsonl");
        writeJsonlForTest(snapshotRegions, result.state.regions);
        ConcolicCampaignRunner.writeOutputs(snapshotDirectory, result);
        ConcolicCampaignRunner.State restored =
                ConcolicCampaignRunner.readCliState(snapshotCli(
                        snapshotDirectory, snapshotRegions));
        FocusedTransitionBackend resumedBackend =
                new FocusedTransitionBackend();
        ConcolicCampaignRunner.Result resumed = ConcolicCampaignRunner.run(
                restored, resumedBackend,
                new ConcolicCampaignRunner.Bounds(4, 1, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);
        assertTrue(resumedBackend.kinds.isEmpty());
        assertEquals(0, resumed.manifest.get(
                "targetRebaseExecutionCount").getAsInt());
        assertTrue(resumed.manifest.get(
                "postDiscoveryTargetRebaseCompleted").getAsBoolean());
        assertFalse(resumed.manifest.get(
                "postDiscoveryTargetRebaseRequired").getAsBoolean());
    }

    @Test
    public void focusedTransitionRefinesUnknownFieldOccurrenceThenReplaysExactOutput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFieldCaptureFixture();
        DeferredFieldCaptureBackend backend =
                new DeferredFieldCaptureBackend(
                        OutputRefinementMode.EXACT);
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 4, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Arrays.asList("TRANSITION_DISCOVERY_SEED", "PATH_FLIP",
                "TRANSITION_OUTPUT_REPLAY", "TARGET_REBASE"),
                backend.kinds);
        assertEquals(4, result.manifest.get("executionCount").getAsInt());
        assertEquals(1, result.manifest.get("solverQueryCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "transitionOutputReplayExecutionCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "transitionPromotionCount").getAsInt());
        assertEquals(1, result.manifest.get(
                "targetRebaseValidationCount").getAsInt());
        assertTrue(result.manifest.toString(),
                result.manifest.get("complete").getAsBoolean());

        JsonObject seedActivation = backend.requests.get(0)
                .getAsJsonObject("activation");
        assertTrue(seedActivation.get(
                "requestedOutputSliceComplete").getAsBoolean());
        assertTrue(seedActivation.get(
                "requestedOutputCaptureRequired").getAsBoolean());
        assertFalse(seedActivation.get(
                "requestedOutputCaptureComplete").getAsBoolean());
        assertTrue(seedActivation.get("schedulerReady").getAsBoolean());
        JsonObject staticCapture = seedActivation.getAsJsonArray(
                "requestedOutputCapture").get(0).getAsJsonObject();
        assertEquals(0, staticCapture.get("occurrence").getAsInt());
        assertEquals("RUNTIME_INSTANCE_REFINEMENT_REQUIRED",
                text(staticCapture, "occurrenceAuthority"));

        JsonObject outputReplay = backend.requests.get(2);
        assertTrue(outputReplay.get(
                "requiresUnforcedBranchValidation").getAsBoolean());
        JsonObject exactActivation = outputReplay.getAsJsonObject(
                "activation");
        assertTrue(RegionCaptureGoal.from(exactActivation)
                .isTransitionDiscovery());
        assertTrue(exactActivation.get(
                "requestedOutputCaptureComplete").getAsBoolean());
        assertTrue(exactActivation.getAsJsonArray("modelAssignments")
                .size() > 0);
        assertFalse(exactActivation.getAsJsonObject("targetBranch")
                .get("desiredOutcome").getAsBoolean());
        JsonObject exactCapture = exactActivation.getAsJsonArray(
                "requestedOutputCapture").get(0).getAsJsonObject();
        assertEquals(1, exactCapture.get("occurrence").getAsInt());
        assertEquals("RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                        + "LAST_WRITE_OCCURRENCE",
                text(exactCapture, "occurrenceAuthority"));
        assertEquals(17, exactCapture.get(
                "runtimeFieldOwnerObjectId").getAsInt());

        JsonObject refinement = outputReplay.getAsJsonObject(
                "transitionOutputRefinement");
        assertEquals("EXEC.field.probe",
                text(refinement, "probeExecutionId"));
        assertEquals("ACT.UPSTREAM.FRESH",
                text(refinement, "refinedActivationId"));
        assertEquals("ACT.U.SEED", text(refinement,
                "sourceActivationId"));
        assertEquals("REGION.U@test#call1", text(refinement,
                "sourceRegionInstanceId"));
        assertEquals("REGION.U.out.0.capture.0", text(refinement,
                "captureBindingId"));
        assertEquals(1, refinement.get("occurrence").getAsInt());
        assertEquals("FRESH_RUNTIME_REFINED_EXACT_OUTPUT_CAPTURE",
                text(refinement, "authority"));

        JsonObject promoted = result.state.summaries.stream().filter(value ->
                value.has("transitionDiscoveryProvenance"))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "exact deferred output replay was not promoted"));
        assertEquals("EXEC.field.output::REGION.U@test#call1",
                text(promoted, "regionInstanceId"));
        assertEquals("EXEC.field.output", text(objectForTest(
                objectForTest(promoted, "transitionDiscoveryProvenance"),
                "promotionAdmission"), "executionId"));
        JsonObject finalAdmission = promoted.getAsJsonObject(
                "finalExecutionOutputCaptureAdmission");
        assertEquals("EXEC.field.output", text(finalAdmission,
                "executionId"));
        assertEquals("FINAL_EXECUTION_RUNTIME_RECONFIRMED_EXACT_"
                        + "OUTPUT_CAPTURE",
                text(finalAdmission, "authority"));
        assertEquals(23, promoted.getAsJsonArray(
                "requestedOutputCapture").get(0).getAsJsonObject().get(
                "runtimeFieldOwnerObjectId").getAsInt());
    }

    @Test
    public void focusedTransitionFailsClosedWhenFreshFieldRefinementIsMissing()
            throws Exception {
        assertDeferredFieldRefinementGap(OutputRefinementMode.MISSING,
                "FRESH_RUNTIME_OUTPUT_CAPTURE_REFINEMENT_MISSING");
    }

    @Test
    public void focusedTransitionFailsClosedWhenFreshFieldRefinementIsAmbiguous()
            throws Exception {
        assertDeferredFieldRefinementGap(OutputRefinementMode.AMBIGUOUS,
                "FRESH_RUNTIME_OUTPUT_CAPTURE_REFINEMENT_AMBIGUOUS");
    }

    @Test
    public void focusedTransitionFailsClosedWhenFinalExecutionDoesNotReconfirmOutput()
            throws Exception {
        assertFinalFieldRefinementGap(OutputRefinementMode.FINAL_MISSING,
                "FINAL_EXECUTION_EXACT_OUTPUT_CAPTURE_NOT_RECONFIRMED");
    }

    @Test
    public void focusedTransitionFailsClosedWhenFinalOccurrenceChanged()
            throws Exception {
        assertFinalFieldRefinementGap(
                OutputRefinementMode.FINAL_OCCURRENCE_CHANGED,
                "FINAL_EXECUTION_EXACT_OUTPUT_CAPTURE_NOT_RECONFIRMED");
    }

    private static void assertDeferredFieldRefinementGap(
            OutputRefinementMode mode, String reason) throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFieldCaptureFixture();
        DeferredFieldCaptureBackend backend =
                new DeferredFieldCaptureBackend(mode);
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 3, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Arrays.asList("TRANSITION_DISCOVERY_SEED", "PATH_FLIP"),
                backend.kinds);
        assertEquals(2, result.manifest.get("executionCount").getAsInt());
        assertEquals(0, result.manifest.get(
                "transitionPromotionCount").getAsInt());
        assertFalse(result.manifest.get("focusedTargetComplete")
                .getAsBoolean());
        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString(),
                result.manifest.getAsJsonArray("gaps").toString()
                        .contains(reason));
        assertTrue(result.state.pathRecords.toString(),
                result.state.pathRecords.toString().contains(reason));
        assertFalse(backend.kinds.contains("TRANSITION_OUTPUT_REPLAY"));
        assertFalse(result.state.summaries.stream().anyMatch(value ->
                value.has("transitionDiscoveryProvenance")));
    }

    private static void assertFinalFieldRefinementGap(
            OutputRefinementMode mode, String reason) throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFieldCaptureFixture();
        DeferredFieldCaptureBackend backend =
                new DeferredFieldCaptureBackend(mode);
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 3, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Arrays.asList("TRANSITION_DISCOVERY_SEED", "PATH_FLIP",
                "TRANSITION_OUTPUT_REPLAY"), backend.kinds);
        assertEquals(3, result.manifest.get("executionCount").getAsInt());
        assertEquals(0, result.manifest.get(
                "transitionPromotionCount").getAsInt());
        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString(),
                result.manifest.getAsJsonArray("gaps").toString()
                        .contains(reason));
        assertFalse(result.state.summaries.stream().anyMatch(value ->
                value.has("transitionDiscoveryProvenance")));
    }

    @Test
    public void focusedTransitionWithOneExecutionReportsBoundedGap()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFixture();
        FocusedTransitionBackend backend = new FocusedTransitionBackend();
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(4, 1, 2, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Collections.singletonList(
                "TRANSITION_DISCOVERY_SEED"), backend.kinds);
        assertEquals(1, result.manifest.get("executionCount").getAsInt());
        assertEquals(0, result.manifest.get(
                "transitionPromotionCount").getAsInt());
        assertFalse(result.manifest.get("focusedTargetComplete")
                .getAsBoolean());
        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("CAMPAIGN_EXECUTION_OR_SOLVER_BOUND"));
    }

    @Test
    public void focusedTransitionSeedCheckpointResumesAtFlipWithoutRecapture()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFixture();
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");
        FocusedTransitionBackend seedBackend =
                new FocusedTransitionBackend();

        ConcolicCampaignRunner.Result checkpoint =
                ConcolicCampaignRunner.run(fixture.state, seedBackend,
                        new ConcolicCampaignRunner.Bounds(4, 1, 2,
                                60_000L, 10_000L,
                                RecursiveRegionWorklist.Bounds.defaults(),
                                RegionPathWorklist.Bounds.defaults()),
                        Paths.get("z3"), focus, true);

        assertEquals(Collections.singletonList(
                "TRANSITION_DISCOVERY_SEED"), seedBackend.kinds);
        assertTrue(checkpoint.state.summaries.stream().anyMatch(value ->
                RegionCaptureGoal.from(value).isTransitionDiscovery()
                        && "QUARANTINED".equals(text(value,
                        "summaryCacheAdmission"))));
        assertTrue(checkpoint.state.pathRecords.stream().anyMatch(value ->
                "TRANSITION_SEED_CAPTURED".equals(text(value,
                        "status"))));
        Path checkpointDirectory = Files.createTempDirectory(
                "transition-seed-checkpoint-");
        ConcolicCampaignRunner.writeOutputs(checkpointDirectory,
                checkpoint);
        List<JsonObject> persistedSummaries = readJsonlForTest(
                checkpointDirectory.resolve("campaign_summaries.jsonl"));
        assertTrue(persistedSummaries.stream().anyMatch(value ->
                RegionCaptureGoal.from(value).isTransitionDiscovery()
                        && "QUARANTINED".equals(text(value,
                        "summaryCacheAdmission"))));
        Path persistedRegions = checkpointDirectory.resolve(
                "regions.jsonl");
        writeJsonlForTest(persistedRegions, checkpoint.state.regions);
        ConcolicCampaignRunner.State persistedCheckpoint =
                ConcolicCampaignRunner.readCliState(new String[]{
                        "--regions", persistedRegions.toString(),
                        "--activations", checkpointDirectory.resolve(
                                "campaign_activations.jsonl").toString(),
                        "--edges", checkpointDirectory.resolve(
                                "campaign_edge_validations.jsonl").toString(),
                        "--roots", checkpointDirectory.resolve(
                                "campaign_roots.jsonl").toString(),
                        "--output-dir", checkpointDirectory.toString(),
                        "--resume-state-manifest",
                        checkpointDirectory.resolve(
                                "campaign_state_manifest.json").toString(),
                        "--", "/bin/true"});
        assertEquals(text(checkpoint.state.roots.get(0), "activationId"),
                text(persistedCheckpoint.roots.get(0), "activationId"));

        FocusedTransitionBackend replayBackend =
                new FocusedTransitionBackend();
        ConcolicCampaignRunner.Result resumed = ConcolicCampaignRunner.run(
                persistedCheckpoint, replayBackend,
                new ConcolicCampaignRunner.Bounds(4, 1, 2, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Collections.singletonList("PATH_FLIP"),
                replayBackend.kinds);
        assertEquals(1, resumed.manifest.get("executionCount").getAsInt());
        assertEquals(1, resumed.manifest.get(
                "transitionPromotionCount").getAsInt());
        assertFalse(resumed.state.summaries.stream().anyMatch(value ->
                RegionCaptureGoal.from(value).isTransitionDiscovery()
                        && "QUARANTINED".equals(text(value,
                        "summaryCacheAdmission"))));
        assertTrue(resumed.manifest.get(
                "postDiscoveryTargetRebaseRequired").getAsBoolean());
        assertTrue(resumed.manifest.getAsJsonArray("gaps").toString()
                .contains("TARGET_REBASE_EXECUTION_BOUND"));

        FocusedTransitionBackend rebaseBackend =
                new FocusedTransitionBackend();
        ConcolicCampaignRunner.Result rebased = ConcolicCampaignRunner.run(
                resumed.state, rebaseBackend,
                new ConcolicCampaignRunner.Bounds(4, 1, 2, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Collections.singletonList("TARGET_REBASE"),
                rebaseBackend.kinds);
        assertEquals(1, rebased.manifest.get(
                "targetRebaseValidationCount").getAsInt());
        assertTrue(rebased.manifest.get(
                "postDiscoveryTargetRebaseCompleted").getAsBoolean());
        assertFalse(rebased.manifest.get(
                "postDiscoveryTargetRebaseRequired").getAsBoolean());
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW",
                text(rebased.state.roots.get(0), "activationId"));
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW", text(
                rebaseBackend.requests.get(0).getAsJsonObject(
                        "activation"), "activationId"));
    }

    @Test
    public void ordinaryResumeCapturesConsumerAfterFreshTargetFormulaRebuild()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFixture();
        FocusedTransitionBackend transitionBackend =
                new FocusedTransitionBackend();
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");
        ConcolicCampaignRunner.Result focused = ConcolicCampaignRunner.run(
                fixture.state, transitionBackend,
                new ConcolicCampaignRunner.Bounds(5, 3, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);
        ConsumerBundleBackend backend = new ConsumerBundleBackend();

        ConcolicCampaignRunner.Result resumed = ConcolicCampaignRunner.run(
                focused.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 1, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertEquals(1, backend.requests.size());
        JsonObject request = backend.requests.get(0);
        assertEquals("OUTPUT_SEED", text(request, "kind"));
        assertEquals("REGION.V", text(request, "regionId"));
        assertEquals(1, request.getAsJsonArray(
                "reachabilitySupportActivations").size());
        JsonObject support = request.getAsJsonArray(
                "reachabilitySupportActivations").get(0).getAsJsonObject();
        assertTrue(text(support, "activationId").startsWith("ACT.PATH."));
        assertTrue(support.has("targetBranch"));
        assertEquals("REGION.V", text(request.getAsJsonObject(
                "activation"), "regionId"));
        assertTrue(resumed.state.summaries.stream().anyMatch(value ->
                "REGION.V".equals(text(value, "regionId"))));
        assertFalse(resumed.manifest.get(
                "postDiscoveryTargetRebaseRequired").getAsBoolean());
        assertTrue(resumed.manifest.get(
                "postDiscoveryTargetRebaseCompleted").getAsBoolean());
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW", text(
                resumed.manifest,
                "postDiscoveryTargetRebaseActivationId"));
        assertTrue(resumed.manifest.get(
                "targetWorklistUsesRebasedInstance").getAsBoolean());
    }

    @Test
    public void rejectedTargetRebasePreservesOldRootRetriesAndDoesNotLoop()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFixture();
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");
        FocusedTransitionBackend rejecting =
                new FocusedTransitionBackend(true);

        ConcolicCampaignRunner.Result rejected =
                ConcolicCampaignRunner.run(fixture.state, rejecting,
                        new ConcolicCampaignRunner.Bounds(5, 3, 1,
                                60_000L, 10_000L,
                                RecursiveRegionWorklist.Bounds.defaults(),
                                RegionPathWorklist.Bounds.defaults()),
                        Paths.get("z3"), focus, true);

        assertEquals(Arrays.asList("TRANSITION_DISCOVERY_SEED", "PATH_FLIP",
                "TARGET_REBASE"), rejecting.kinds);
        assertEquals(1, rejected.manifest.get(
                "targetRebaseExecutionCount").getAsInt());
        assertEquals(0, rejected.manifest.get(
                "targetRebaseValidationCount").getAsInt());
        assertFalse(rejected.manifest.get(
                "postDiscoveryTargetRebaseCompleted").getAsBoolean());
        assertTrue(rejected.manifest.get(
                "postDiscoveryTargetRebaseRequired").getAsBoolean());
        assertEquals("ACT.TARGET", text(rejected.state.roots.get(0),
                "activationId"));
        assertEquals("REGION.T@test#call2", text(rejected.state.roots.get(0),
                "regionInstanceId"));
        assertEquals("SAME_INSTANCE_IMPORTED_UNFORCED_TARGET_REPLAY",
                text(rejected.state.roots.get(0),
                        "replayValidationAuthority"));
        assertTrue(rejected.manifest.getAsJsonArray("gaps").toString()
                .contains("TARGET_REBASE_DOWNSTREAM_INJECTION_OR_"
                        + "OVERRIDE_USED"));
        assertTrue(rejected.state.pathRecords.stream().anyMatch(value ->
                "TARGET_REBASE_REJECTED".equals(text(value, "status"))));
        JsonObject persistedPreparedActivation = rejected.state.activations
                .stream().filter(value ->
                        "EXEC.focus.flip::ACT.TARGET.NEW".equals(text(value,
                                "activationId")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "rejected prepared target activation was not "
                                + "persisted"));
        assertTrue(persistedPreparedActivation.get(
                "targetObservationOnly").getAsBoolean());
        assertTrue(persistedPreparedActivation.get(
                "postDiscoveryTargetRebaseCandidate").getAsBoolean());

        FocusedTransitionBackend retry = new FocusedTransitionBackend();
        ConcolicCampaignRunner.Result recovered =
                ConcolicCampaignRunner.run(rejected.state, retry,
                        new ConcolicCampaignRunner.Bounds(4, 1, 1,
                                60_000L, 10_000L,
                                RecursiveRegionWorklist.Bounds.defaults(),
                                RegionPathWorklist.Bounds.defaults()),
                        Paths.get("z3"), focus, true);

        assertEquals(Collections.singletonList("TARGET_REBASE"),
                retry.kinds);
        assertTrue(recovered.manifest.get("complete").getAsBoolean());
        assertEquals(1, recovered.manifest.get(
                "targetRebaseValidationCount").getAsInt());
        JsonObject recoveredRoot = recovered.state.roots.get(0);
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW",
                text(recoveredRoot, "activationId"));
        assertEquals("EXEC.focus.flip::REGION.T@test#call9",
                text(recoveredRoot, "regionInstanceId"));

        FocusedTransitionBackend noLoop = new FocusedTransitionBackend();
        ConcolicCampaignRunner.Result stable =
                ConcolicCampaignRunner.run(recovered.state, noLoop,
                        new ConcolicCampaignRunner.Bounds(4, 1, 1,
                                60_000L, 10_000L,
                                RecursiveRegionWorklist.Bounds.defaults(),
                                RegionPathWorklist.Bounds.defaults()),
                        Paths.get("z3"), focus, true);
        assertTrue(noLoop.kinds.isEmpty());
        assertEquals(0, stable.manifest.get(
                "targetRebaseExecutionCount").getAsInt());
        assertTrue(stable.manifest.get(
                "postDiscoveryTargetRebaseCompleted").getAsBoolean());
        assertEquals("EXEC.focus.flip::ACT.TARGET.NEW",
                text(stable.state.roots.get(0), "activationId"));
    }

    @Test
    public void targetRebaseRejectsSummaryIdCacheCollisionBeforeRootMutation()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = focusedTransitionFixture();
        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.U.V", "ACT.U.SEED", "U#u1");
        ConcolicCampaignRunner.Result pending = ConcolicCampaignRunner.run(
                fixture.state, new FocusedTransitionBackend(),
                new ConcolicCampaignRunner.Bounds(4, 2, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);
        JsonObject collision = new JsonObject();
        collision.addProperty("summaryId",
                "SUMMARY.TARGET.REBASE.EXEC.focus.target.rebase");
        collision.addProperty("cacheKey", "CACHE.CONFLICTING");
        collision.addProperty("activationId",
                "EXEC.focus.flip::ACT.TARGET.NEW");
        collision.addProperty("regionId", "REGION.T");
        collision.addProperty("regionInstanceId",
                "EXEC.focus.flip::REGION.T@test#call9");
        pending.state.summaries.add(collision);

        FocusedTransitionBackend backend = new FocusedTransitionBackend();
        ConcolicCampaignRunner.Result rejected = ConcolicCampaignRunner.run(
                pending.state, backend,
                new ConcolicCampaignRunner.Bounds(4, 1, 1, 60_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"), focus, true);

        assertEquals(Collections.singletonList("TARGET_REBASE"),
                backend.kinds);
        assertEquals(0, rejected.manifest.get(
                "targetRebaseValidationCount").getAsInt());
        assertEquals("ACT.TARGET", text(rejected.state.roots.get(0),
                "activationId"));
        assertTrue(rejected.state.pathRecords.toString().contains(
                "FRESH_TARGET_SUMMARY_ID_COLLISION"));
        assertFalse(rejected.state.summaries.stream().anyMatch(value ->
                "ADMITTED_FRESH_VALIDATED_TARGET".equals(text(value,
                        "summaryCacheAdmission"))));
    }

    @Test
    public void exceptionalOutputFlipIsMaterializationGapAndIsNotMerged()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        ExceptionalOutputFlipBackend backend =
                new ExceptionalOutputFlipBackend();

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 4, 4, 10_000L,
                        10_000L,
                        RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertEquals(2, backend.executions);
        assertEquals(1, result.state.pathRecords.size());
        JsonObject record = result.state.pathRecords.get(0);
        assertEquals("MATERIALIZATION_GAP", text(record, "status"));
        assertEquals("OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT",
                text(record, "reason"));
        assertTrue(record.getAsJsonObject("replayValidation")
                .get("flippedBranchValidated").getAsBoolean());
        assertTrue(record.getAsJsonObject("replayValidation")
                .get("outputClosureAdmissionGap").getAsBoolean());
        assertTrue(result.manifest.getAsJsonObject("pathWorklist")
                .getAsJsonArray("gaps").toString()
                .contains("EXPLORATION_GAP"));
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("EXPLORATION_GAP"));
        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertTrue(result.state.summaries.stream()
                .filter(value -> objectForTest(value, "regionRelation")
                        .size() == 0)
                .allMatch(value -> !value.has("exceptionType")
                        || text(value, "exceptionType").isEmpty()));
    }

    @Test
    public void commandBackendIsolatesRetriesFromStaleAttemptProducts()
            throws Exception {
        Path output = Files.createTempDirectory("campaign-command-");
        Path regions = output.resolve("regions.jsonl");
        Files.write(regions, new byte[0]);
        JsonObject request = new JsonObject();
        request.addProperty("kind", "OUTPUT_SEED");
        request.addProperty("requestKey", "fresh-discovery");
        request.addProperty("activationId", "ACT.REQUEST");
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.REQUEST");
        request.add("activation", activation);
        Path execution = output.resolve("executions").resolve(
                shortHashForTest("fresh-discovery"));
        Files.createDirectories(execution);
        Files.write(execution.resolve("discovered_activation_plan.jsonl"),
                "{\"activationId\":\"STALE\"}\n".getBytes(
                        StandardCharsets.UTF_8));
        Files.write(execution.resolve("discovered_edge_validation.jsonl"),
                "{\"edgeId\":\"STALE\"}\n".getBytes(
                        StandardCharsets.UTF_8));
        Files.write(execution.resolve("concolic_region_summaries.jsonl"),
                "{\"summaryId\":\"STALE\"}\n".getBytes(
                        StandardCharsets.UTF_8));
        String script = "test ! -e \"$CAUSYNTH_CAMPAIGN_RESULTS\""
                + " && test ! -e \"$CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS\""
                + " && test ! -e \"$CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES\""
                + " && test \"$(dirname \"$CAUSYNTH_CAMPAIGN_RESULTS\")\""
                + " = \"$(dirname \"$CAUSYNTH_CAMPAIGN_REQUEST\")\""
                + " && test \"$(dirname \"$CAUSYNTH_CAMPAIGN_RESULTS\")\""
                + " = \"$(dirname \"$CAUSYNTH_CAMPAIGN_ACTIVATION_PLAN\")\""
                + " && printf '{\"activationId\":\"%s\"}\\n'"
                + " \"$CAUSYNTH_CAMPAIGN_EXECUTION_ID\""
                + " > \"$CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS\""
                + " && printf '%s\\n' '{\"edgeId\":\"EDGE.FRESH\"}'"
                + " > \"$CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES\""
                + " && : > \"$CAUSYNTH_CAMPAIGN_RESULTS\"";
        ConcolicCampaignRunner.CommandBackend backend =
                new ConcolicCampaignRunner.CommandBackend(output, regions,
                        Arrays.asList("/bin/sh", "-c", script), 10_000L);

        ConcolicCampaignRunner.ExecutionOutcome first = backend.execute(
                request);
        Path firstAttempt = execution.resolve("attempts").resolve(
                ConcolicCampaignRunner.CommandBackend
                        .filesystemSafeExecutionId(first.executionId));
        Files.write(firstAttempt.resolve("discovered_activation_plan.jsonl"),
                "{\"activationId\":\"STALE.ATTEMPT\"}\n".getBytes(
                        StandardCharsets.UTF_8));

        ConcolicCampaignRunner.ExecutionOutcome second = backend.execute(
                request);
        Path secondAttempt = execution.resolve("attempts").resolve(
                ConcolicCampaignRunner.CommandBackend
                        .filesystemSafeExecutionId(second.executionId));

        assertEquals("SUCCEEDED", first.status);
        assertEquals("SUCCEEDED", second.status);
        assertTrue(first.executionId.startsWith("EXEC."
                + shortHashForTest("fresh-discovery") + "."));
        assertTrue(second.executionId.startsWith("EXEC."
                + shortHashForTest("fresh-discovery") + "."));
        assertFalse(firstAttempt.equals(secondAttempt));
        assertTrue(Files.isDirectory(firstAttempt));
        assertTrue(Files.isDirectory(secondAttempt));
        assertEquals(first.executionId,
                text(first.discoveredActivations.get(0), "activationId"));
        assertEquals(second.executionId,
                text(second.discoveredActivations.get(0), "activationId"));
        assertNull(first.summary);
        assertNull(second.summary);
        assertEquals("EDGE.FRESH", text(second.discoveredEdges.get(0),
                "edgeId"));
        assertTrue(new String(Files.readAllBytes(firstAttempt.resolve(
                "discovered_activation_plan.jsonl")), StandardCharsets.UTF_8)
                .contains("STALE.ATTEMPT"));
        assertTrue(new String(Files.readAllBytes(execution.resolve(
                "discovered_activation_plan.jsonl")), StandardCharsets.UTF_8)
                .contains("STALE"));
        assertTrue(Files.isRegularFile(secondAttempt.resolve(
                "activation_plan.jsonl")));
        assertTrue(Files.isRegularFile(secondAttempt.resolve(
                "capture_request.json")));
        assertTrue(Files.isRegularFile(secondAttempt.resolve(
                "concolic_region_results.jsonl")));
        assertTrue(Files.isRegularFile(secondAttempt.resolve(
                "concolic_region_summaries.jsonl")));
        assertTrue(Files.isRegularFile(secondAttempt.resolve(
                "concolic_import_diagnostics.jsonl")));
    }

    @Test
    public void commandBackendExecutesSupportThenPrimaryAsOneBundle()
            throws Exception {
        Path output = Files.createTempDirectory("campaign-bundle-");
        Path regions = output.resolve("regions.jsonl");
        Files.write(regions, new byte[0]);
        JsonObject support = new JsonObject();
        support.addProperty("activationId", "ACT.SUPPORT.FLIP");
        support.addProperty("regionId", "REGION.U");
        support.addProperty("rootMethod", "<example.U: void replay()>");
        support.addProperty("receiverRuntimeClass", "example.ProducerWorker");
        support.addProperty("threadName", "rpc-producer");
        support.addProperty("threadIdSelectionUsed", false);
        support.addProperty("invocationOrdinalWithinContext", 1);
        support.addProperty("rootContextSelectionAuthority",
                "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1");
        JsonObject primary = new JsonObject();
        primary.addProperty("activationId", "ACT.CONSUMER.CAPTURE");
        primary.addProperty("regionId", "REGION.V");
        primary.addProperty("rootMethod", "<example.V: void capture()>");
        primary.addProperty("receiverRuntimeClass", "example.ConsumerWorker");
        primary.addProperty("threadName", "rpc-consumer");
        primary.addProperty("threadIdSelectionUsed", false);
        primary.addProperty("invocationOrdinalWithinContext", 1);
        primary.addProperty("rootContextSelectionAuthority",
                "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1");
        JsonArray supportBundle = new JsonArray();
        supportBundle.add(support);
        primary.add("reachabilitySupportActivations",
                supportBundle.deepCopy());
        JsonObject request = new JsonObject();
        request.addProperty("kind", "OUTPUT_SEED");
        request.addProperty("requestKey", "support-bundle");
        request.addProperty("activationId", "ACT.CONSUMER.CAPTURE");
        request.add("activation", primary);
        request.add("reachabilitySupportActivations",
                supportBundle.deepCopy());
        String script = "test \"$CAUSYNTH_CAMPAIGN_ACTIVATION_ID\" = ALL"
                + " && test \"$(wc -l < \"$CAUSYNTH_CAMPAIGN_ACTIVATION_PLAN\")\" -eq 2"
                + " && : > \"$CAUSYNTH_CAMPAIGN_RESULTS\""
                + " && : > \"$CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS\""
                + " && : > \"$CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES\"";
        ConcolicCampaignRunner.CommandBackend backend =
                new ConcolicCampaignRunner.CommandBackend(output, regions,
                        Arrays.asList("/bin/sh", "-c", script), 10_000L);

        ConcolicCampaignRunner.ExecutionOutcome outcome = backend.execute(
                request);
        Path attempt = output.resolve("executions")
                .resolve(shortHashForTest("support-bundle"))
                .resolve("attempts").resolve(
                        ConcolicCampaignRunner.CommandBackend
                                .filesystemSafeExecutionId(
                                        outcome.executionId));
        List<String> rows = Files.readAllLines(attempt.resolve(
                "activation_plan.jsonl"), StandardCharsets.UTF_8);

        assertEquals("SUCCEEDED", outcome.status);
        assertEquals(2, rows.size());
        assertEquals("ACT.SUPPORT.FLIP", text(JsonParser.parseString(
                rows.get(0)).getAsJsonObject(), "activationId"));
        assertEquals("ACT.CONSUMER.CAPTURE", text(JsonParser.parseString(
                rows.get(1)).getAsJsonObject(), "activationId"));
        assertEquals("ALL", text(JsonParser.parseString(rows.get(0))
                .getAsJsonObject(), "activationSelectionRequired"));
        assertEquals("ALL", text(JsonParser.parseString(rows.get(1))
                .getAsJsonObject(), "activationSelectionRequired"));
        assertEquals("example.ProducerWorker", text(JsonParser.parseString(
                rows.get(0)).getAsJsonObject(), "receiverRuntimeClass"));
        assertEquals("rpc-producer", text(JsonParser.parseString(rows.get(0))
                .getAsJsonObject(), "threadName"));
        assertEquals("example.ConsumerWorker", text(JsonParser.parseString(
                rows.get(1)).getAsJsonObject(), "receiverRuntimeClass"));
        assertEquals("rpc-consumer", text(JsonParser.parseString(rows.get(1))
                .getAsJsonObject(), "threadName"));
        assertEquals(1, JsonParser.parseString(rows.get(1)).getAsJsonObject()
                .get("invocationOrdinalWithinContext").getAsInt());
        assertFalse(JsonParser.parseString(rows.get(1)).getAsJsonObject()
                .get("threadIdSelectionUsed").getAsBoolean());
        assertFalse(rows.get(0).contains(
                "reachabilitySupportActivations"));
        assertFalse(rows.get(1).contains(
                "reachabilitySupportActivations"));
        String manifest = new String(Files.readAllBytes(attempt.resolve(
                "execution_manifest.json")), StandardCharsets.UTF_8);
        assertTrue(manifest.contains(
                "ALL_REQUIRED_REACHABILITY_BUNDLE"));
        assertTrue(manifest.contains(
                "\"reachabilitySupportActivationCount\": 1"));

        JsonObject supportRow = new JsonObject();
        supportRow.addProperty("activationId", "ACT.SUPPORT.FLIP");
        supportRow.addProperty("regionId", "REGION.U");
        JsonObject primaryRow = new JsonObject();
        primaryRow.addProperty("activationId", "ACT.CONSUMER.CAPTURE");
        primaryRow.addProperty("regionId", "REGION.V");
        assertEquals("ACT.CONSUMER.CAPTURE", text(
                ConcolicCampaignRunner.CommandBackend.primaryExecutionRow(
                        Arrays.asList(supportRow, primaryRow), request),
                "activationId"));
        assertNull(ConcolicCampaignRunner.CommandBackend.primaryExecutionRow(
                Arrays.asList(primaryRow, primaryRow.deepCopy()), request));
    }

    @Test
    public void executionDirectoryNameIsSafeAndCollisionResistant() {
        String unsafe = "../EXEC /\\\\name:with?unsafe#characters";
        String first = ConcolicCampaignRunner.CommandBackend
                .filesystemSafeExecutionId(unsafe);
        String second = ConcolicCampaignRunner.CommandBackend
                .filesystemSafeExecutionId(unsafe.replace('?', '*'));

        assertFalse(first.contains("/"));
        assertFalse(first.contains("\\"));
        assertFalse(".".equals(first));
        assertFalse("..".equals(first));
        assertFalse(first.equals(second));
        assertEquals(first, ConcolicCampaignRunner.CommandBackend
                .filesystemSafeExecutionId(unsafe));
    }

    @Test
    public void cliExposesCampaignGraphAndPathBounds() {
        ConcolicCampaignRunner.Bounds bounds =
                ConcolicCampaignRunner.parseCliBounds(new String[]{
                        "--regions", "regions.jsonl",
                        "--activations", "activations.jsonl",
                        "--edges", "edges.jsonl",
                        "--roots", "roots.jsonl",
                        "--output-dir", "campaign",
                        "--max-iterations", "11",
                        "--max-executions", "12",
                        "--max-solver-queries", "13",
                        "--max-wall-clock-ms", "14000",
                        "--solver-timeout-ms", "15000",
                        "--graph-max-depth", "16",
                        "--graph-max-regions", "17",
                        "--graph-max-activations-per-region", "18",
                        "--graph-max-alternative-writers-per-read", "19",
                        "--graph-max-queries", "20",
                        "--graph-max-paths", "21",
                        "--graph-max-wall-clock-ms", "22000",
                        "--path-max-paths-per-region", "23",
                        "--path-max-flips-per-path", "24",
                        "--path-max-tasks", "25",
                        "--path-max-wall-clock-ms", "26000",
                        "--", "/bin/true"});

        assertEquals(11, bounds.maxIterations);
        assertEquals(12, bounds.maxExecutions);
        assertEquals(13, bounds.maxSolverQueries);
        assertEquals(14_000L, bounds.maxWallClockMillis);
        assertEquals(15_000L, bounds.solverTimeoutMillis);
        assertEquals(16, bounds.graphBounds.maxDepth);
        assertEquals(17, bounds.graphBounds.maxRegions);
        assertEquals(18, bounds.graphBounds.maxActivationsPerRegion);
        assertEquals(19, bounds.graphBounds.maxAlternativeWritersPerRead);
        assertEquals(20, bounds.graphBounds.maxQueries);
        assertEquals(21, bounds.graphBounds.maxPaths);
        assertEquals(22_000L, bounds.graphBounds.maxWallClockMillis);
        assertEquals(23, bounds.pathBounds.maxPathsPerRegion);
        assertEquals(24, bounds.pathBounds.maxFlipsPerPath);
        assertEquals(25, bounds.pathBounds.maxTasks);
        assertEquals(26_000L, bounds.pathBounds.maxWallClockMillis);

        assertEquals(
                ConcolicCampaignRunner.RuntimeDiscoveryMode
                        .SAME_EXECUTION_REQUIRED,
                ConcolicCampaignRunner.parseCliRuntimeDiscoveryMode(
                        new String[]{
                                "--regions", "regions.jsonl",
                                "--activations", "activations.jsonl",
                                "--edges", "edges.jsonl",
                                "--roots", "roots.jsonl",
                                "--output-dir", "campaign",
                                "--", "/bin/true"}));
        assertEquals(
                ConcolicCampaignRunner.RuntimeDiscoveryMode
                        .FIXED_VALIDATED_GRAPH,
                ConcolicCampaignRunner.parseCliRuntimeDiscoveryMode(
                        new String[]{
                                "--regions", "regions.jsonl",
                                "--activations", "activations.jsonl",
                                "--edges", "edges.jsonl",
                                "--roots", "roots.jsonl",
                                "--output-dir", "campaign",
                                "--runtime-discovery-mode",
                                "FIXED_VALIDATED_GRAPH",
                                "--", "/bin/true"}));

        String[] focused = new String[]{
                "--regions", "regions.jsonl",
                "--activations", "activations.jsonl",
                "--edges", "edges.jsonl",
                "--roots", "roots.jsonl",
                "--output-dir", "campaign",
                "--transition-focus-edge", "EDGE.U.V",
                "--transition-focus-activation", "ACT.U.SEED",
                "--transition-focus-guard", "U#u1",
                "--transition-focus-only", "true",
                "--", "/bin/true"};
        RegionTransitionDiscoveryWorklist.Focus focus =
                ConcolicCampaignRunner.parseCliTransitionFocus(focused);
        assertEquals("EDGE.U.V", focus.edgeId);
        assertEquals("ACT.U.SEED", focus.activationId);
        assertEquals("U#u1", focus.guardSiteId);
        assertTrue(ConcolicCampaignRunner.parseCliTransitionFocusOnly(
                focused));
    }

    @Test
    public void fixedGraphCommandBackendDoesNotRequestDiscoveryFiles()
            throws Exception {
        Path output = Files.createTempDirectory("campaign-fixed-graph-");
        Path regions = output.resolve("regions.jsonl");
        Files.write(regions, new byte[0]);
        JsonObject request = new JsonObject();
        request.addProperty("kind", "OUTPUT_SEED");
        request.addProperty("requestKey", "fixed-graph");
        request.addProperty("activationId", "ACT.REQUEST");
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.REQUEST");
        request.add("activation", activation);
        String script = "test -z \"${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS+x}\""
                + " && test -z \"${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES+x}\""
                + " && test \"$CAUSYNTH_CAMPAIGN_RUNTIME_DISCOVERY_MODE\""
                + " = FIXED_VALIDATED_GRAPH"
                + " && : > \"$CAUSYNTH_CAMPAIGN_RESULTS\"";
        ConcolicCampaignRunner.CommandBackend backend =
                new ConcolicCampaignRunner.CommandBackend(output, regions,
                        Arrays.asList("/bin/sh", "-c", script), 10_000L,
                        ConcolicCampaignRunner.RuntimeDiscoveryMode
                                .FIXED_VALIDATED_GRAPH);

        ConcolicCampaignRunner.ExecutionOutcome outcome = backend.execute(
                request);
        Path attempt = output.resolve("executions")
                .resolve(shortHashForTest("fixed-graph"))
                .resolve("attempts").resolve(
                        ConcolicCampaignRunner.CommandBackend
                                .filesystemSafeExecutionId(
                                        outcome.executionId));

        assertEquals("SUCCEEDED", outcome.status);
        assertTrue(outcome.discoveredActivations.isEmpty());
        assertTrue(outcome.discoveredEdges.isEmpty());
        assertFalse(Files.exists(attempt.resolve(
                "discovered_activation_plan.jsonl")));
        assertFalse(Files.exists(attempt.resolve(
                "discovered_edge_validation.jsonl")));
        String manifest = new String(Files.readAllBytes(attempt.resolve(
                "execution_manifest.json")), StandardCharsets.UTF_8);
        assertTrue(manifest.contains(
                "\"runtimeDiscoveryMode\": \"FIXED_VALIDATED_GRAPH\""));
        String persistedRequest = new String(Files.readAllBytes(
                attempt.resolve("capture_request.json")),
                StandardCharsets.UTF_8);
        assertTrue(persistedRequest.contains(
                "\"runtimeDiscoveryMode\": \"FIXED_VALIDATED_GRAPH\""));
    }

    @Test
    public void commandBackendRetainsFreshRawEvidenceAfterBugExit()
            throws Exception {
        Path output = Files.createTempDirectory("campaign-bug-exit-");
        Path regions = output.resolve("regions.jsonl");
        Files.write(regions, new byte[0]);
        JsonObject request = new JsonObject();
        request.addProperty("kind", "PATH_FLIP");
        request.addProperty("requestKey", "natural-bug-exit");
        request.addProperty("activationId", "ACT.REQUEST");
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.REQUEST");
        request.add("activation", activation);
        String script = ": > \"$CAUSYNTH_CAMPAIGN_RESULTS\"; "
                + "printf '%s\\n' '{\"activationId\":\"ACT.BUG\"}'"
                + " > \"$CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS\"; "
                + ": > \"$CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES\"; "
                + "exit 7";
        ConcolicCampaignRunner.CommandBackend backend =
                new ConcolicCampaignRunner.CommandBackend(output, regions,
                        Arrays.asList("/bin/sh", "-c", script), 10_000L);

        ConcolicCampaignRunner.ExecutionOutcome outcome = backend.execute(
                request);

        assertEquals("SUCCEEDED_WITH_NONZERO_EXIT_7", outcome.status);
        assertEquals(1, outcome.discoveredActivations.size());
        assertEquals("ACT.BUG", text(outcome.discoveredActivations.get(0),
                "activationId"));
        assertNull(outcome.summary);
    }

    @Test
    public void commandBackendRejectsRawEvidenceWithoutDiscoveryCompletion()
            throws Exception {
        Path output = Files.createTempDirectory("campaign-no-discovery-");
        Path regions = output.resolve("regions.jsonl");
        Files.write(regions, new byte[0]);
        JsonObject request = new JsonObject();
        request.addProperty("kind", "OUTPUT_SEED");
        request.addProperty("requestKey", "missing-discovery");
        request.addProperty("activationId", "ACT.REQUEST");
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.REQUEST");
        request.add("activation", activation);
        String script = ": > \"$CAUSYNTH_CAMPAIGN_RESULTS\"";
        ConcolicCampaignRunner.CommandBackend backend =
                new ConcolicCampaignRunner.CommandBackend(output, regions,
                        Arrays.asList("/bin/sh", "-c", script), 10_000L);

        ConcolicCampaignRunner.ExecutionOutcome outcome = backend.execute(
                request);

        assertEquals("DISCOVERY_FAILED", outcome.status);
        assertNull(outcome.summary);
        assertTrue(outcome.discoveredActivations.isEmpty());
        assertTrue(outcome.discoveredEdges.isEmpty());
    }

    @Test
    public void resumeEdgesMergePersistedWitnessesWithoutDowngrade()
            throws Exception {
        Path directory = Files.createTempDirectory("campaign-edge-resume-");
        Path primary = directory.resolve("initial.jsonl");
        Path resumed = directory.resolve("campaign_edge_validations.jsonl");
        JsonObject proven = fixture().state.edges.get(0).deepCopy();
        JsonObject oldBinding = new JsonObject();
        oldBinding.addProperty("fromRegionInstance", "REGION.U#old");
        oldBinding.addProperty("toRegionInstance", "REGION.T#old");
        oldBinding.addProperty("valueEqualityObserved", true);
        JsonArray oldBindings = new JsonArray();
        oldBindings.add(oldBinding);
        proven.add("validatedBindings", oldBindings);
        proven.addProperty("validatedBindingCount", 1);
        JsonObject persisted = proven.deepCopy();
        JsonObject newBinding = oldBinding.deepCopy();
        newBinding.addProperty("fromRegionInstance",
                "EXEC.resume::REGION.U#new");
        JsonArray persistedBindings = new JsonArray();
        persistedBindings.add(newBinding);
        persisted.add("validatedBindings", persistedBindings);
        persisted.addProperty("status", "ENDPOINTS_OBSERVED");
        persisted.addProperty("validatedRelation", "");
        persisted.addProperty("composable", false);
        persisted.addProperty("eligibleForAutomaticDerivation", false);
        persisted.addProperty("eligibleForAutomaticSmt", false);
        persisted.addProperty("confirmedValueEqualityPairCount", 0);
        persisted.addProperty("valueEqualityObserved", false);
        Files.write(primary, (proven.toString() + "\n").getBytes(
                StandardCharsets.UTF_8));
        Files.write(resumed, (persisted.toString() + "\n").getBytes(
                StandardCharsets.UTF_8));

        List<JsonObject> edges = ConcolicCampaignRunner.readEdges(primary,
                Collections.singletonList(resumed));

        assertEquals(1, edges.size());
        assertTrue(edges.get(0).get("composable").getAsBoolean());
        assertEquals("CONFIRMED_RUNTIME_VALUE_EQUALITY",
                text(edges.get(0), "status"));
        assertEquals(2, edges.get(0).getAsJsonArray(
                "validatedBindings").size());
    }

    @Test
    public void missingActivationCanBeDiscoveredAndRetriedWithoutStaleGap()
            throws Exception {
        Fixture fixture = fixture();
        fixture.state.regions.add(region("REGION.A", "REGION.A.out.0",
                "<example.A: int value>"));
        fixture.state.edges.add(composableEdge("EDGE.A.T", "REGION.A",
                "REGION.A.out.0"));
        LateActivationBackend backend = new LateActivationBackend();

        ConcolicCampaignRunner.Result result = ConcolicCampaignRunner.run(
                fixture.state, backend,
                new ConcolicCampaignRunner.Bounds(8, 4, 4, 10_000L,
                        1_000L, RecursiveRegionWorklist.Bounds.defaults(),
                        RegionPathWorklist.Bounds.defaults()),
                Paths.get("z3"));

        assertEquals(Arrays.asList("REGION.U", "REGION.A"),
                backend.capturedRegions);
        assertTrue(result.state.activations.stream().anyMatch(value ->
                "EXEC.late::ACT.0".equals(text(value, "activationId"))));
        assertFalse(result.manifest.getAsJsonArray("gaps").toString()
                .contains("MISSING_OUTPUT_ACTIVATION"));
        assertFalse(result.manifest.getAsJsonArray("gaps").toString()
                .contains("OUTPUT_CAPTURE_MATERIALIZATION_NOT_READY"));
    }

    private static Fixture focusedTransitionFixture() {
        Fixture fixture = fixture();
        JsonObject upstream = fixture.state.regions.get(0);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.U.out.0");
        slice.addProperty("outputCell", "<example.Upstream: int value>");
        slice.addProperty("complete", true);
        JsonArray sites = new JsonArray();
        sites.add("U#u1");
        slice.add("sites", sites);
        slice.add("inputPorts", new JsonArray());
        JsonArray slices = new JsonArray();
        slices.add(slice);
        upstream.add("outputSlices", slices);

        JsonObject producer = fixture.state.activations.get(0);
        producer.addProperty("regionInstanceId",
                "REGION.U@test#call1");
        JsonObject guard = new JsonObject();
        guard.addProperty("siteId", "U#u1");
        guard.addProperty("role", "REACHABILITY");
        guard.addProperty("observed", true);
        guard.addProperty("observedOutcome", true);
        guard.addProperty("requiredOutcome", false);
        guard.addProperty("selectedOccurrence", 1);
        JsonArray branches = new JsonArray();
        branches.add(guard);
        producer.add("branches", branches);

        fixture.state.regions.add(region("REGION.V", "REGION.V.out.0",
                "<example.V: int value>"));
        fixture.state.edges.clear();
        JsonObject candidate = new JsonObject();
        candidate.addProperty("edgeId", "EDGE.U.V");
        candidate.addProperty("fromRegion", "REGION.U");
        candidate.addProperty("fromPort", "REGION.U.out.0");
        candidate.addProperty("toRegion", "REGION.V");
        candidate.addProperty("toPort", "REGION.V.in.0");
        candidate.addProperty("candidateRelation", "EQUALITY");
        candidate.addProperty("composable", false);
        candidate.addProperty("eligibleForAutomaticDerivation", false);
        candidate.addProperty("eligibleForAutomaticSmt", false);
        candidate.addProperty("mappingOnly", true);
        candidate.addProperty("payloadEqualityCheckRequired", true);
        candidate.addProperty("mappingAuthority",
                "STATIC_EXACT_PROTOCOL_PORT_MAPPING");
        fixture.state.edges.add(candidate);

        JsonObject bridge = new JsonObject();
        bridge.addProperty("edgeId", "EDGE.V.T");
        bridge.addProperty("fromRegion", "REGION.V");
        bridge.addProperty("fromPort", "REGION.V.out.0");
        bridge.addProperty("toRegion", "REGION.T");
        bridge.addProperty("toPort", "REGION.T.in.0");
        bridge.addProperty("validatedRelation", "EQUALITY");
        bridge.addProperty("composable", true);
        bridge.addProperty("eligibleForAutomaticDerivation", true);
        bridge.addProperty("eligibleForAutomaticSmt", true);
        bridge.addProperty("status", "CONFIRMED_RUNTIME_VALUE_EQUALITY");
        bridge.addProperty("valueEqualityObserved", true);
        bridge.addProperty("confirmedValueEqualityPairCount", 1);
        bridge.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        bridge.add("evidence", new JsonArray());
        fixture.state.edges.add(bridge);
        return fixture;
    }

    private static Fixture focusedTransitionFieldCaptureFixture() {
        Fixture fixture = focusedTransitionFixture();
        String root = "<example.Upstream: int run(int)>";
        String method = "<example.State: void install(java.lang.Object)>";
        String field = "<example.State: java.lang.Object value>";
        String site = method + "#u3";
        String edgeId = "DF.FIELD.WRITE";

        JsonObject upstream = fixture.state.regions.get(0);
        JsonObject output = upstream.getAsJsonArray("outputs")
                .get(0).getAsJsonObject();
        output.addProperty("cell", field);
        output.addProperty("kind", "HEAP_STATE");

        JsonObject causal = new JsonObject();
        causal.addProperty("edgeId", edgeId);
        causal.addProperty("method", method);
        causal.addProperty("siteId", site);
        causal.addProperty("fromCell", method + "::r1");
        causal.addProperty("toCell", field);
        causal.addProperty("transferKind", "HEAP_WRITE");
        causal.addProperty("kind", "field_write");

        JsonObject obligation = new JsonObject();
        obligation.addProperty("siteId", site);
        obligation.addProperty("method", method);
        obligation.addProperty("targetCell", field);
        obligation.addProperty("transferKind", "HEAP_WRITE");
        obligation.addProperty("kind", "field_write");
        JsonArray obligationEdges = new JsonArray();
        obligationEdges.add(edgeId);
        obligation.add("causalEdgeIds", obligationEdges);
        obligation.addProperty("authority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL");

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.U.out.0");
        slice.addProperty("outputCell", field);
        slice.addProperty("complete", true);
        slice.addProperty("selection",
                "REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE");
        JsonArray sites = new JsonArray();
        sites.add("U#u1");
        sites.add(site);
        slice.add("sites", sites);
        JsonArray methods = new JsonArray();
        methods.add(root);
        methods.add(method);
        slice.add("methods", methods);
        JsonArray inputs = new JsonArray();
        inputs.add("REGION.U.in.0");
        slice.add("inputPorts", inputs);
        JsonArray causalEdges = new JsonArray();
        causalEdges.add(causal);
        slice.add("causalEdges", causalEdges);
        JsonArray causalEdgeIds = new JsonArray();
        causalEdgeIds.add(edgeId);
        slice.add("causalEdgeIds", causalEdgeIds);
        slice.addProperty("causalEdgeCount", 1);
        JsonArray captures = new JsonArray();
        captures.add(fieldCaptureBinding(0, 0));
        slice.add("captureBindings", captures);
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("unresolvedInputs", new JsonArray());
        slice.addProperty("requestedStateTransformerContractVersion", 1);
        slice.addProperty(
                "requestedStateTransformerContractApplicable", true);
        slice.addProperty("requestedStateTransformerContractOutputPort",
                "REGION.U.out.0");
        slice.addProperty("requestedStateTransformerContractOutputCell",
                field);
        JsonArray obligations = new JsonArray();
        obligations.add(obligation);
        slice.add("requestedStateTransformerObligations", obligations);
        slice.addProperty("requestedStateTransformerObligationCount", 1);
        slice.add("requestedStateTransformerContractIssues",
                new JsonArray());
        slice.addProperty(
                "requestedStateTransformerContractComplete", true);
        slice.addProperty("requestedStateTransformerContractAuthority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1");
        JsonArray slices = new JsonArray();
        slices.add(slice);
        upstream.add("outputSlices", slices);

        // Force transition discovery to resolve the selected output from the
        // new exact static slice.  The ordinary producer activation observed
        // only the early-return guard and therefore has no dynamic occurrence.
        JsonObject producer = fixture.state.activations.get(0);
        producer.remove("requestedOutputSlice");
        producer.remove("requestedOutputCapture");
        producer.remove("requestedOutputCaptureRequired");
        producer.remove("requestedOutputCaptureComplete");
        producer.addProperty("requestedOutputSliceComplete", false);
        return fixture;
    }

    private static JsonObject fieldCaptureBinding(int occurrence,
                                                  int ownerObjectId) {
        String method = "<example.State: void install(java.lang.Object)>";
        String field = "<example.State: java.lang.Object value>";
        String site = method + "#u3";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId",
                "REGION.U.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.U.out.0");
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
        capture.addProperty("rhsCausalEdgeId", "DF.FIELD.WRITE");
        capture.addProperty("rhsRelation", "value_flow");
        capture.addProperty("rhsRelationComplete", true);
        capture.addProperty("rhsRelationAuthority",
                "STATIC_EXACT_HEAP_WRITE_VALUE_FLOW");
        capture.addProperty("causalEdgeId", "DF.FIELD.WRITE");
        capture.addProperty("transferKind", "HEAP_WRITE");
        capture.addProperty("bindingKind", "field_write");
        capture.addProperty("bindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS");
        capture.addProperty("occurrence", occurrence);
        if (occurrence > 0) {
            capture.addProperty("occurrenceAuthority",
                    "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                            + "LAST_WRITE_OCCURRENCE");
            capture.addProperty("runtimeFieldOwnerObjectId", ownerObjectId);
            capture.addProperty("runtimeFieldOwnerBindingAuthority",
                    "RUNTIME_EXACT_FIELD_WRITE_RECEIVER_IDENTITY");
            capture.addProperty("runtimeCallId", 41);
            capture.addProperty("runtimeEventSeq", 42);
        } else {
            capture.addProperty("occurrenceAuthority",
                    "RUNTIME_INSTANCE_REFINEMENT_REQUIRED");
        }
        return capture;
    }

    private static JsonObject runtimeRefinedFieldActivation(
            JsonObject probeActivation, String activationId,
            int occurrence, int ownerObjectId) {
        JsonObject result = probeActivation.deepCopy();
        result.addProperty("activationId", activationId);
        result.addProperty("regionId", "REGION.U");
        result.addProperty("regionInstanceId", "REGION.U@test#call1");
        result.addProperty("rootMethod",
                "<example.Upstream: int run(int)>");
        result.addProperty("selectedUpstreamActivationId", "ACT.U.SEED");
        result.addProperty("selectedBaseActivationId", "ACT.U.SEED");
        result.addProperty("runtimeRefinementExecutionId",
                "EXEC.field.probe");
        result.addProperty("runtimeRefinementAuthority",
                "FRESH_EXECUTION_OBSERVED_REGION_CALL_TREE");
        result.addProperty("requestedOutputSliceComplete", true);
        result.addProperty("requestedOutputCaptureRequired", true);
        result.addProperty("requestedOutputCaptureComplete", true);
        result.addProperty("schedulerReady", true);
        result.addProperty("symbolicReady", true);
        result.addProperty("boundaryReady", true);
        JsonObject exact = fieldCaptureBinding(occurrence, ownerObjectId);
        JsonArray captures = new JsonArray();
        captures.add(exact);
        result.add("requestedOutputCapture", captures);
        JsonObject slice = result.getAsJsonObject(
                "requestedOutputSlice").deepCopy();
        slice.add("captureBindings", captures.deepCopy());
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        result.add("requestedOutputSlice", slice);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.U.out.0");
        outputAction.addProperty("cell",
                "<example.State: java.lang.Object value>");
        outputAction.addProperty("kind", "HEAP_STATE");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        JsonArray outputs = new JsonArray();
        outputs.add(outputAction);
        result.add("outputs", outputs);
        RegionCaptureGoal.outputClosure().writeTo(result);
        return result;
    }

    private enum OutputRefinementMode {
        EXACT,
        MISSING,
        AMBIGUOUS,
        FINAL_MISSING,
        FINAL_OCCURRENCE_CHANGED
    }

    private static final class DeferredFieldCaptureBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private final OutputRefinementMode mode;
        private final List<String> kinds = new ArrayList<>();
        private final List<JsonObject> requests = new ArrayList<>();

        private DeferredFieldCaptureBackend(OutputRefinementMode mode) {
            this.mode = mode;
        }

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            requests.add(request.deepCopy());
            String kind = text(request, "kind");
            kinds.add(kind);
            JsonObject activation = request.getAsJsonObject("activation");
            if ("TRANSITION_DISCOVERY_SEED".equals(kind)) {
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        pathOnlyTransitionSummary(activation, ">", true),
                        "EXEC.field.seed",
                        Collections.<JsonObject>emptyList(),
                        Collections.<JsonObject>emptyList());
            }
            if ("PATH_FLIP".equals(kind)) {
                boolean desired = request.getAsJsonObject("pathTask")
                        .get("desiredOutcome").getAsBoolean();
                List<JsonObject> refined = new ArrayList<>();
                if (mode == OutputRefinementMode.EXACT
                        || mode == OutputRefinementMode.FINAL_MISSING
                        || mode == OutputRefinementMode
                        .FINAL_OCCURRENCE_CHANGED) {
                    refined.add(runtimeRefinedFieldActivation(activation,
                            "ACT.UPSTREAM.FRESH", 1, 17));
                } else if (mode == OutputRefinementMode.AMBIGUOUS) {
                    refined.add(runtimeRefinedFieldActivation(activation,
                            "ACT.UPSTREAM.FRESH.1", 1, 17));
                    refined.add(runtimeRefinedFieldActivation(activation,
                            "ACT.UPSTREAM.FRESH.2", 2, 19));
                }
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, desired),
                        pathOnlyTransitionSummary(activation,
                                desired ? ">" : "<=", desired),
                        "EXEC.field.probe", refined,
                        Collections.<JsonObject>emptyList());
            }
            if ("TRANSITION_OUTPUT_REPLAY".equals(kind)) {
                if (mode == OutputRefinementMode.MISSING
                        || mode == OutputRefinementMode.AMBIGUOUS) {
                    throw new AssertionError("inexact fresh refinement must "
                            + "not schedule output replay");
                }
                boolean desired = request.getAsJsonObject("pathTask")
                        .get("desiredOutcome").getAsBoolean();
                JsonObject source = freshSourceActivation();
                JsonObject consumer = freshConsumerActivation();
                JsonObject target = freshTargetActivation();
                List<JsonObject> discovered = new ArrayList<>();
                discovered.add(source);
                if (mode != OutputRefinementMode.FINAL_MISSING) {
                    discovered.add(runtimeRefinedFieldActivation(activation,
                            "ACT.UPSTREAM.FINAL",
                            mode == OutputRefinementMode
                                    .FINAL_OCCURRENCE_CHANGED ? 2 : 1,
                            23));
                }
                discovered.add(consumer);
                discovered.add(target);
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, desired),
                        exactTransitionSummary(activation,
                                desired ? ">" : "<=", desired),
                        "EXEC.field.output",
                        discovered,
                        Arrays.asList(FocusedTransitionBackend
                                        .focusedComposableEdge(),
                                FocusedTransitionBackend
                                        .freshTargetEdge()));
            }
            if ("TARGET_REBASE".equals(kind)) {
                return FocusedTransitionBackend.targetRebaseOutcome(
                        request, "EXEC.field.target.rebase");
            }
            throw new AssertionError("unexpected campaign request " + kind);
        }

        private static JsonObject pathOnlyTransitionSummary(
                JsonObject activation, String operator, boolean outcome) {
            JsonObject result = summary(activation, operator, outcome);
            result.add("captureGoal",
                    RegionCaptureGoal.transitionDiscovery().toJson());
            result.addProperty("regionInstanceId",
                    "REGION.U@test#call1");
            result.addProperty("requestedOutputSliceComplete", true);
            result.add("requestedOutputSlice", activation.getAsJsonObject(
                    "requestedOutputSlice").deepCopy());
            result.add("requestedOutputCapture", activation.getAsJsonArray(
                    "requestedOutputCapture").deepCopy());
            result.addProperty("requestedOutputCaptureRequired", true);
            result.addProperty("requestedOutputCaptureComplete", false);
            result.addProperty("relationallyComplete", false);
            result.add("outputExpressions", new JsonObject());
            JsonObject admission = new JsonObject();
            admission.addProperty("complete", false);
            admission.addProperty("authority", "NONE");
            JsonArray issues = new JsonArray();
            issues.add("MISSING_EXACT_OUTPUT_EXPRESSION_CAPTURE");
            admission.add("issues", issues);
            result.add("outputExpressionAdmission", admission);
            result.addProperty("normalExit", true);
            return result;
        }

        private static JsonObject exactTransitionSummary(
                JsonObject activation, String operator, boolean outcome) {
            JsonObject result = summary(activation, operator, outcome);
            result.add("captureGoal",
                    RegionCaptureGoal.transitionDiscovery().toJson());
            result.addProperty("regionInstanceId",
                    "REGION.U@test#call1");
            result.addProperty("requestedOutputSliceComplete", true);
            result.add("requestedOutputSlice", activation.getAsJsonObject(
                    "requestedOutputSlice").deepCopy());
            result.add("requestedOutputCapture", activation.getAsJsonArray(
                    "requestedOutputCapture").deepCopy());
            result.addProperty("requestedOutputCaptureRequired", true);
            result.addProperty("requestedOutputCaptureComplete", true);
            JsonObject admission = new JsonObject();
            admission.addProperty("complete", true);
            admission.addProperty("authority",
                    "EXACT_FIELD_ASSIGNMENT_RHS");
            admission.add("issues", new JsonArray());
            result.add("outputExpressionAdmission", admission);
            result.addProperty("relationallyComplete", true);
            result.addProperty("normalExit", true);
            return result;
        }

        private static JsonObject freshSourceActivation() {
            JsonObject source = new JsonObject();
            source.addProperty("activationId", "ACT.U.SEED");
            source.addProperty("regionId", "REGION.U");
            source.addProperty("regionInstanceId",
                    "REGION.U@test#call1");
            source.addProperty("rootMethod",
                    "<example.Upstream: int run(int)>");
            source.addProperty("test", "local-test");
            source.addProperty("invocationOrdinal", 1);
            source.addProperty("replayable", true);
            return source;
        }

        private static JsonObject freshConsumerActivation() {
            JsonObject consumer = new JsonObject();
            consumer.addProperty("activationId", "ACT.V.1");
            consumer.addProperty("regionId", "REGION.V");
            consumer.addProperty("regionInstanceId",
                    "REGION.V@test#call2");
            consumer.addProperty("rootMethod",
                    "<example.V: int run(int)>");
            consumer.addProperty("test", "local-test");
            consumer.addProperty("invocationOrdinal", 1);
            consumer.addProperty("replayable", true);
            consumer.addProperty("symbolicReady", true);
            return consumer;
        }

        private static JsonObject freshTargetActivation() {
            JsonObject target = new JsonObject();
            target.addProperty("activationId", "ACT.TARGET.NEW");
            target.addProperty("regionId", "REGION.T");
            target.addProperty("regionInstanceId",
                    "REGION.T@test#call9");
            target.addProperty("rootMethod",
                    "<example.Target: void fail(int)>");
            target.addProperty("test", "local-test");
            target.addProperty("invocationOrdinal", 1);
            target.addProperty("replayable", true);
            return target;
        }
    }

    private static final class FocusedTransitionBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private final List<String> kinds = new ArrayList<>();
        private final List<JsonObject> requests = new ArrayList<>();
        private final boolean rejectTargetRebase;
        private final boolean omitFreshTargetContext;

        private FocusedTransitionBackend() {
            this(false, false);
        }

        private FocusedTransitionBackend(boolean rejectTargetRebase) {
            this(rejectTargetRebase, false);
        }

        private FocusedTransitionBackend(boolean rejectTargetRebase,
                                         boolean omitFreshTargetContext) {
            this.rejectTargetRebase = rejectTargetRebase;
            this.omitFreshTargetContext = omitFreshTargetContext;
        }

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            requests.add(request.deepCopy());
            String kind = text(request, "kind");
            kinds.add(kind);
            JsonObject activation = request.getAsJsonObject("activation");
            if ("TRANSITION_DISCOVERY_SEED".equals(kind)) {
                assertEquals("ACT.U.SEED", text(activation,
                        "selectedUpstreamActivationId"));
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        transitionSummary(activation, ">", true),
                        "EXEC.focus.seed",
                        Collections.<JsonObject>emptyList(),
                        Collections.<JsonObject>emptyList());
            }
            if ("TARGET_REBASE".equals(kind)) {
                ConcolicCampaignRunner.ExecutionOutcome outcome =
                        targetRebaseOutcome(request,
                        "EXEC.focus.target.rebase");
                if (rejectTargetRebase) {
                    JsonObject unexpected = new JsonObject();
                    unexpected.addProperty("symbol", "REGION.T.in.0");
                    unexpected.addProperty("value", 0);
                    outcome.rawResult.getAsJsonArray(
                            "modelAssignmentsApplied").add(unexpected);
                }
                return outcome;
            }
            JsonObject task = request.getAsJsonObject("pathTask");
            boolean desired = task.get("desiredOutcome").getAsBoolean();
            JsonObject consumer = new JsonObject();
            consumer.addProperty("activationId", "ACT.V.1");
            consumer.addProperty("regionId", "REGION.V");
            consumer.addProperty("regionInstanceId", "REGION.V@test#call2");
            consumer.addProperty("rootMethod", "<example.V: int run(int)>");
            consumer.addProperty("test", "local-test");
            consumer.addProperty("invocationOrdinal", 1);
            consumer.addProperty("replayable", true);
            consumer.addProperty("symbolicReady", true);
            JsonObject source = new JsonObject();
            source.addProperty("activationId", "ACT.U.SEED");
            source.addProperty("regionId", "REGION.U");
            source.addProperty("regionInstanceId",
                    "REGION.U@test#call1");
            source.addProperty("rootMethod",
                    "<example.Upstream: int run(int)>");
            source.addProperty("test", "local-test");
            source.addProperty("invocationOrdinal", 1);
            JsonObject target = new JsonObject();
            target.addProperty("activationId", "ACT.TARGET.NEW");
            target.addProperty("regionId", "REGION.T");
            target.addProperty("regionInstanceId",
                    "REGION.T@test#call9");
            target.addProperty("rootMethod",
                    "<example.Target: void fail(int)>");
            target.addProperty("test", "local-test");
            target.addProperty("invocationOrdinal", 1);
            target.addProperty("replayable", true);
            JsonObject edge = focusedComposableEdge();
            List<JsonObject> discoveredEdges = omitFreshTargetContext
                    ? Collections.singletonList(edge)
                    : Arrays.asList(edge, freshTargetEdge());
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw(activation, desired),
                    transitionSummary(activation,
                            desired ? ">" : "<=", desired),
                    "EXEC.focus.flip", Arrays.asList(source, consumer,
                    target),
                    discoveredEdges);
        }

        private static ConcolicCampaignRunner.ExecutionOutcome
        targetRebaseOutcome(JsonObject request, String executionId) {
            JsonObject activation = request.getAsJsonObject("activation");
            assertTrue(request.get(
                    "requiresUnforcedBranchValidation").getAsBoolean());
            assertTrue(activation.get(
                    "targetReplayRequired").getAsBoolean());
            assertTrue(activation.get(
                    "downstreamInjectionProhibited").getAsBoolean());
            assertEquals(1, request.getAsJsonArray(
                    "reachabilitySupportActivations").size());
            assertEquals(0, activation.getAsJsonArray(
                    "modelAssignments").size());
            assertEquals(0, activation.getAsJsonArray(
                    "replayMaterializations").size());
            assertEquals(0, activation.getAsJsonArray(
                    "forcedBranches").size());

            JsonObject target = activation.getAsJsonObject("targetBranch");
            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("activationId", text(activation,
                    "activationId"));
            raw.addProperty("regionId", text(activation, "regionId"));
            raw.addProperty("regionInstanceId", text(activation,
                    "regionInstanceId"));
            raw.addProperty("branchOverrideUsed", false);
            raw.addProperty("forcedBranchUsed", false);
            raw.addProperty("forcedBranchCount", 0);
            raw.addProperty("exitKind", "THROW");
            raw.addProperty("exceptionType",
                    "java.lang.IllegalStateException");
            raw.add("replayMaterializationsApplied", new JsonArray());
            raw.add("modelAssignmentsApplied", new JsonArray());
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", text(target, "siteId"));
            mapping.addProperty("occurrence", target.get(
                    "occurrence").getAsInt());
            mapping.addProperty("outcome", target.get(
                    "desiredOutcome").getAsBoolean());
            mapping.addProperty("observedOutcome", target.get(
                    "desiredOutcome").getAsBoolean());
            mapping.addProperty("conditionIndex", 0);
            mapping.addProperty("scheduledOutcomeMatched", true);
            mapping.addProperty("overrideApplied", false);
            JsonObject observedTargetCondition = targetCondition();
            mapping.add("condition", observedTargetCondition.deepCopy());
            JsonArray mappings = new JsonArray();
            mappings.add(mapping);
            raw.add("branchMappings", mappings);

            JsonObject summary = new JsonObject();
            summary.addProperty("summaryId", "SUMMARY.TARGET.REBASE."
                    + executionId);
            summary.addProperty("cacheKey", "CACHE.TARGET.REBASE."
                    + executionId);
            summary.addProperty("activationId", text(activation,
                    "activationId"));
            summary.addProperty("regionId", text(activation, "regionId"));
            summary.addProperty("regionInstanceId", text(activation,
                    "regionInstanceId"));
            summary.addProperty("valid", true);
            summary.addProperty("targetReplayValidated", true);
            summary.addProperty("branchOverrideUsed", false);
            summary.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
            JsonArray path = new JsonArray();
            path.add(observedTargetCondition.deepCopy());
            summary.add("pathCondition", path);
            summary.add("branchMappings", mappings.deepCopy());
            summary.add("engineArrayInputBindings", new JsonArray());
            summary.add("directedTargetQuery", activation.getAsJsonObject(
                    "directedTargetQuery").deepCopy());
            JsonObject admission = new JsonObject();
            admission.addProperty("required", true);
            admission.addProperty("valid", true);
            admission.addProperty("branchOverrideAccepted", false);
            admission.addProperty("authority",
                    "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_"
                            + "OBSERVATION");
            summary.add("executionAdmission", admission);
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED_WITH_NONZERO_EXIT_1", raw, summary,
                    executionId, Collections.<JsonObject>emptyList(),
                    Collections.<JsonObject>emptyList());
        }

        private static JsonObject transitionSummary(JsonObject activation,
                                                    String operator,
                                                    boolean outcome) {
            JsonObject result = summary(activation, operator, outcome);
            result.add("captureGoal",
                    RegionCaptureGoal.transitionDiscovery().toJson());
            result.addProperty("requestedOutputSliceComplete", true);
            result.addProperty("regionInstanceId", text(activation,
                    "regionInstanceId"));
            result.add("requestedOutputSlice", activation.getAsJsonObject(
                    "requestedOutputSlice").deepCopy());
            return result;
        }

        private static JsonObject focusedComposableEdge() {
            JsonObject edge = new JsonObject();
            edge.addProperty("edgeId", "EDGE.U.V");
            edge.addProperty("fromRegion", "REGION.U");
            edge.addProperty("fromPort", "REGION.U.out.0");
            edge.addProperty("toRegion", "REGION.V");
            edge.addProperty("toPort", "REGION.V.in.0");
            edge.addProperty("candidateRelation", "EQUALITY");
            edge.addProperty("validatedRelation", "EQUALITY");
            edge.addProperty("status",
                    "CONFIRMED_RUNTIME_VALUE_EQUALITY");
            edge.addProperty("composable", true);
            edge.addProperty("eligibleForAutomaticDerivation", true);
            edge.addProperty("eligibleForAutomaticSmt", true);
            edge.addProperty("valueEqualityObserved", true);
            edge.addProperty("valueEqualityAuthority",
                    "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
            edge.addProperty("confirmedValueEqualityPairCount", 1);
            JsonObject binding = new JsonObject();
            binding.addProperty("fromRegionInstance",
                    "REGION.U@test#call1");
            binding.addProperty("toRegionInstance",
                    "REGION.V@test#call2");
            binding.addProperty("valueEqualityObserved", true);
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            edge.add("validatedBindings", bindings);
            edge.addProperty("validatedBindingCount", 1);
            return edge;
        }

        private static JsonObject freshTargetEdge() {
            JsonObject edge = new JsonObject();
            edge.addProperty("edgeId", "EDGE.V.T");
            edge.addProperty("fromRegion", "REGION.V");
            edge.addProperty("fromPort", "REGION.V.out.0");
            edge.addProperty("toRegion", "REGION.T");
            edge.addProperty("toPort", "REGION.T.in.0");
            edge.addProperty("candidateRelation", "EQUALITY");
            edge.addProperty("validatedRelation", "EQUALITY");
            edge.addProperty("status",
                    "CONFIRMED_RUNTIME_VALUE_EQUALITY");
            edge.addProperty("composable", true);
            edge.addProperty("eligibleForAutomaticDerivation", true);
            edge.addProperty("eligibleForAutomaticSmt", true);
            edge.addProperty("valueEqualityObserved", true);
            edge.addProperty("valueEqualityAuthority",
                    "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
            edge.addProperty("confirmedValueEqualityPairCount", 1);
            JsonObject binding = new JsonObject();
            binding.addProperty("fromRegionInstance",
                    "REGION.V@test#call2");
            binding.addProperty("toRegionInstance",
                    "REGION.T@test#call9");
            binding.addProperty("valueEqualityObserved", true);
            binding.addProperty("valueEqualityAuthority",
                    "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
            binding.addProperty("valueFingerprint", "fp-target");
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            edge.add("validatedBindings", bindings);
            edge.addProperty("validatedBindingCount", 1);
            return edge;
        }
    }

    private static final class ConsumerBundleBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private final List<JsonObject> requests = new ArrayList<>();

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            requests.add(request.deepCopy());
            JsonObject activation = request.getAsJsonObject("activation");
            assertEquals(1, request.getAsJsonArray(
                    "reachabilitySupportActivations").size());
            JsonObject summary = closedSummary(activation);
            summary.addProperty("normalExit", true);
            summary.addProperty("requestedOutputSliceComplete", true);
            JsonObject raw = new JsonObject();
            raw.addProperty("branchOverrideUsed", false);
            raw.addProperty("exitKind", "NORMAL");
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw, summary, "EXEC.consumer.capture",
                    Collections.<JsonObject>emptyList(),
                    Collections.<JsonObject>emptyList());
        }
    }

    private static final class MissingScheduleEvidenceBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private int executions;

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            executions++;
            JsonObject activation = request.getAsJsonObject("activation");
            if ("OUTPUT_SEED".equals(text(request, "kind"))) {
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        summary(activation, ">", true));
            }
            JsonObject task = request.getAsJsonObject("pathTask");
            boolean desired = task.get("desiredOutcome").getAsBoolean();
            JsonObject raw = raw(activation, desired);
            raw.getAsJsonArray("branchMappings").get(0).getAsJsonObject()
                    .remove("scheduledTarget");
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw,
                    summary(activation, desired ? ">" : "<=", desired));
        }
    }

    private static final class FakeBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private int executions;
        private final List<String> kinds = new ArrayList<>();
        private final List<JsonObject> requests = new ArrayList<>();

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            executions++;
            requests.add(request.deepCopy());
            kinds.add(request.get("kind").getAsString());
            JsonObject activation = request.getAsJsonObject("activation");
            if ("OUTPUT_SEED".equals(request.get("kind").getAsString())) {
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        summary(activation, ">", true));
            }
            JsonObject task = request.getAsJsonObject("pathTask");
            boolean desired = task.get("desiredOutcome").getAsBoolean();
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw(activation, desired),
                    summary(activation, desired ? ">" : "<=", desired));
        }
    }

    private static final class FixedGraphBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private int executions;

        @Override
        public ConcolicCampaignRunner.RuntimeDiscoveryMode
        runtimeDiscoveryMode() {
            return ConcolicCampaignRunner.RuntimeDiscoveryMode
                    .FIXED_VALIDATED_GRAPH;
        }

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            executions++;
            JsonObject activation = request.getAsJsonObject("activation");
            JsonObject imported;
            boolean observed = true;
            if ("OUTPUT_SEED".equals(text(request, "kind"))) {
                imported = summary(activation, ">", true);
            } else {
                boolean desired = request.getAsJsonObject("pathTask")
                        .get("desiredOutcome").getAsBoolean();
                observed = desired;
                imported = summary(activation, desired ? ">" : "<=",
                        desired);
            }
            JsonObject discovered = activation.deepCopy();
            discovered.addProperty("activationId",
                    "DISCOVERED." + executions);
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw(activation, observed), imported,
                    "EXEC.fixed." + executions,
                    Collections.singletonList(discovered),
                    Collections.singletonList(dynamicEdge()));
        }
    }

    private static final class DiscoveryBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private final boolean validSeed;
        private final boolean invalidReplay;

        private DiscoveryBackend(boolean validSeed, boolean invalidReplay) {
            this.validSeed = validSeed;
            this.invalidReplay = invalidReplay;
        }

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            JsonObject activation = request.getAsJsonObject("activation");
            JsonObject raw = raw(activation, true);
            if (invalidReplay) raw.addProperty("branchOverrideUsed", true);
            JsonObject imported = validSeed
                    ? summary(activation, ">", true) : null;
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw, imported, "EXEC.seed",
                    Collections.singletonList(
                            discoveredActivation(activation)),
                    Collections.singletonList(dynamicEdge()));
        }
    }

    private static final class FlipDiscoveryBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private final boolean validReplay;

        private FlipDiscoveryBackend(boolean validReplay) {
            this.validReplay = validReplay;
        }

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            JsonObject activation = request.getAsJsonObject("activation");
            if ("OUTPUT_SEED".equals(text(request, "kind"))) {
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        summary(activation, ">", true));
            }
            boolean desired = request.getAsJsonObject("pathTask")
                    .get("desiredOutcome").getAsBoolean();
            JsonObject raw = raw(activation, desired);
            if (!validReplay) raw.addProperty("branchOverrideUsed", true);
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw,
                    summary(activation, desired ? ">" : "<=", desired),
                    "EXEC.flip",
                    Collections.singletonList(
                            discoveredActivation(activation)),
                    Collections.singletonList(dynamicEdge()));
        }
    }

    private static final class ExceptionalOutputFlipBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private int executions;

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            executions++;
            JsonObject activation = request.getAsJsonObject("activation");
            if ("OUTPUT_SEED".equals(text(request, "kind"))) {
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        summary(activation, ">", true));
            }
            boolean desired = request.getAsJsonObject("pathTask")
                    .get("desiredOutcome").getAsBoolean();
            JsonObject raw = raw(activation, desired);
            raw.addProperty("exitKind", "EXCEPTION");
            raw.addProperty("exceptionType",
                    "java.util.NoSuchElementException");
            JsonObject imported = summary(activation,
                    desired ? ">" : "<=", desired);
            imported.addProperty("normalExit", false);
            imported.addProperty("exceptionType",
                    "java.util.NoSuchElementException");
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw, imported);
        }
    }

    private static final class EdgeMergeBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            JsonObject activation = request.getAsJsonObject("activation");
            JsonObject edge = fixture().state.edges.get(0).deepCopy();
            edge.addProperty("status", "ENDPOINTS_OBSERVED");
            edge.addProperty("validatedRelation", "");
            edge.addProperty("composable", false);
            edge.addProperty("eligibleForAutomaticDerivation", false);
            edge.addProperty("eligibleForAutomaticSmt", false);
            edge.addProperty("confirmedValueEqualityPairCount", 0);
            edge.addProperty("valueEqualityObserved", false);
            JsonObject binding = new JsonObject();
            binding.addProperty("fromRegionInstance", "REGION.U#new");
            binding.addProperty("toRegionInstance", "REGION.T#new");
            binding.addProperty("orderConfirmed", true);
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            edge.add("validatedBindings", bindings);
            edge.addProperty("validatedBindingCount", 1);
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw(activation, true),
                    summary(activation, ">", true), "EXEC.merge",
                    Collections.<JsonObject>emptyList(),
                    Collections.singletonList(edge));
        }
    }

    private static final class LateActivationBackend
            implements ConcolicCampaignRunner.ExecutionBackend {
        private final List<String> capturedRegions = new ArrayList<>();

        @Override
        public ConcolicCampaignRunner.ExecutionOutcome execute(
                JsonObject request) {
            JsonObject activation = request.getAsJsonObject("activation");
            String region = text(activation, "regionId");
            capturedRegions.add(region);
            if ("REGION.U".equals(region)) {
                JsonObject discovered = activation.deepCopy();
                discovered.addProperty("activationId", "ACT.0");
                discovered.addProperty("regionInstanceId",
                        "REGION.A@test#call1");
                discovered.addProperty("regionId", "REGION.A");
                discovered.addProperty("rootMethod",
                        "<example.A: int run(int)>");
                discovered.remove("selectedUpstreamActivationId");
                discovered.remove("selectedBaseActivationId");
                discovered.remove("requestedOutput");
                return new ConcolicCampaignRunner.ExecutionOutcome(
                        "SUCCEEDED", raw(activation, true),
                        closedSummary(activation), "EXEC.late",
                        Collections.singletonList(discovered),
                        Collections.<JsonObject>emptyList());
            }
            return new ConcolicCampaignRunner.ExecutionOutcome(
                    "SUCCEEDED", raw(activation, true),
                    closedSummary(activation));
        }
    }

    private static JsonObject dynamicEdge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.V.T");
        edge.addProperty("fromRegion", "REGION.V");
        edge.addProperty("fromPort", "REGION.V.out.0");
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("toPort", "REGION.T.in.0");
        edge.addProperty("relation", "EQUALITY");
        edge.addProperty("candidateRelation", "EQUALITY");
        edge.addProperty("validatedRelation", "EQUALITY");
        edge.addProperty("status", "CONFIRMED_RUNTIME_VALUE_EQUALITY");
        edge.addProperty("composable", true);
        edge.addProperty("eligibleForAutomaticDerivation", true);
        edge.addProperty("eligibleForAutomaticSmt", true);
        edge.addProperty("valueEqualityObserved", true);
        edge.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        edge.addProperty("confirmedValueEqualityPairCount", 1);
        JsonObject binding = new JsonObject();
        binding.addProperty("fromRegionInstance", "REGION.V@test#call1");
        binding.addProperty("toRegionInstance", "REGION.T@test#call2");
        binding.addProperty("valueEqualityObserved", true);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        edge.add("validatedBindings", bindings);
        edge.addProperty("validatedBindingCount", 1);
        return edge;
    }

    private static JsonObject composableEdge(String edgeId, String producer,
                                             String outputPort) {
        JsonObject edge = fixture().state.edges.get(0).deepCopy();
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("fromRegion", producer);
        edge.addProperty("fromPort", outputPort);
        edge.remove("validatedBindings");
        edge.addProperty("validatedBindingCount", 0);
        return edge;
    }

    private static JsonObject discoveredActivation(JsonObject source) {
        JsonObject discovered = source.deepCopy();
        discovered.addProperty("activationId", "ACT.0");
        discovered.addProperty("regionInstanceId",
                "REGION.V@test#call1");
        discovered.addProperty("regionId", "REGION.V");
        discovered.addProperty("rootMethod", "<example.V: int run(int)>");
        discovered.remove("selectedUpstreamActivationId");
        discovered.remove("selectedBaseActivationId");
        discovered.remove("requestedOutput");
        return discovered;
    }

    private static JsonObject raw(JsonObject activation, boolean outcome) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("regionId", "REGION.U");
        raw.addProperty("activationId",
                activation.get("activationId").getAsString());
        raw.addProperty("allModelAssignmentsApplied", true);
        JsonArray appliedAssignments = activation.has("modelAssignments")
                ? activation.getAsJsonArray("modelAssignments").deepCopy()
                : new JsonArray();
        raw.addProperty("modelAssignmentAppliedCount",
                appliedAssignments.size());
        raw.add("modelAssignmentsApplied", appliedAssignments);
        raw.addProperty("branchOverrideUsed", false);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");
        raw.add("replayMaterializationsApplied", new JsonArray());
        JsonArray mappings = new JsonArray();
        JsonObject observed = mapping(outcome);
        JsonObject target = activation.has("targetBranch")
                && activation.get("targetBranch").isJsonObject()
                ? activation.getAsJsonObject("targetBranch") : null;
        if (target != null
                && text(target, "siteId").equals(text(observed, "siteId"))
                && target.get("occurrence").getAsInt()
                == observed.get("occurrence").getAsInt()) {
            boolean desired = target.get("desiredOutcome").getAsBoolean();
            observed.addProperty("scheduledTarget", true);
            observed.addProperty("scheduledDesiredOutcome", desired);
            observed.addProperty("scheduledOutcomeMatched",
                    desired == outcome);
        }
        mappings.add(observed);
        raw.add("branchMappings", mappings);
        return raw;
    }

    private static JsonObject summary(JsonObject activation, String operator,
                                      boolean outcome) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY."
                + activation.get("activationId").getAsString() + "."
                + operator.replace("=", "E"));
        summary.addProperty("activationId",
                activation.get("activationId").getAsString());
        summary.addProperty("regionId", "REGION.U");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        summary.add("requestedOutput", activation.getAsJsonObject(
                "requestedOutput").deepCopy());
        JsonArray path = new JsonArray();
        path.add(condition(operator));
        summary.add("pathCondition", path);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(outcome));
        summary.add("branchMappings", mappings);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.U.out.0", symbol());
        summary.add("outputExpressions", outputs);
        summary.add("heapStateInitializers", new JsonArray());
        summary.add("heapEffects", new JsonArray());
        JsonObject model = new JsonObject();
        model.addProperty("complete", true);
        model.addProperty("effectCount", 0);
        model.addProperty("initializerCount", 0);
        model.addProperty("initializedInputCount", 0);
        model.addProperty("mapStateFamilyCount", 0);
        summary.add("heapEffectModel", model);
        summary.addProperty("normalExit", true);
        return summary;
    }

    private static JsonObject objectForTest(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static List<JsonObject> readJsonlForTest(Path path)
            throws Exception {
        List<JsonObject> result = new ArrayList<>();
        for (String line : Files.readAllLines(path,
                StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) {
                result.add(JsonParser.parseString(line).getAsJsonObject());
            }
        }
        return result;
    }

    private static void writeJsonlForTest(Path path,
                                          List<JsonObject> rows)
            throws Exception {
        StringBuilder content = new StringBuilder();
        for (JsonObject row : rows) {
            content.append(row).append(System.lineSeparator());
        }
        Files.write(path, content.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static String[] snapshotCli(Path output, Path regions) {
        return new String[]{
                "--regions", regions.toString(),
                "--activations", output.resolve(
                        "campaign_activations.jsonl").toString(),
                "--edges", output.resolve(
                        "campaign_edge_validations.jsonl").toString(),
                "--roots", output.resolve(
                        "campaign_roots.jsonl").toString(),
                "--output-dir", output.toString(),
                "--resume-state-manifest", output.resolve(
                        "campaign_state_manifest.json").toString(),
                "--", "/bin/true"};
    }

    private static String[] snapshotCliWithoutResume(Path output,
                                                     Path regions) {
        return new String[]{
                "--regions", regions.toString(),
                "--activations", output.resolve(
                        "campaign_activations.jsonl").toString(),
                "--edges", output.resolve(
                        "campaign_edge_validations.jsonl").toString(),
                "--roots", output.resolve(
                        "campaign_roots.jsonl").toString(),
                "--output-dir", output.toString(),
                "--", "/bin/true"};
    }

    private static void assertSnapshotReadFails(String[] argv,
                                                String expectedProblem)
            throws Exception {
        try {
            ConcolicCampaignRunner.readCliState(argv);
            throw new AssertionError(
                    "tampered campaign snapshot was accepted");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains(expectedProblem));
        }
    }

    private static JsonObject closedSummary(JsonObject activation) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.CLOSED."
                + text(activation, "regionId"));
        summary.addProperty("activationId", text(activation,
                "activationId"));
        summary.addProperty("regionId", text(activation, "regionId"));
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        summary.add("requestedOutput", activation.getAsJsonObject(
                "requestedOutput").deepCopy());
        JsonObject relation = new JsonObject();
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.addProperty("complete", true);
        relation.add("inputPorts", new JsonArray());
        summary.add("regionRelation", relation);
        return summary;
    }

    private static JsonObject mapping(boolean outcome) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", "U#u1");
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("conditionIndex", 0);
        mapping.addProperty("outcome", outcome);
        mapping.addProperty("observedOutcome", outcome);
        mapping.addProperty("effectiveOutcome", outcome);
        mapping.addProperty("overrideApplied", false);
        return mapping;
    }

    private static JsonObject nullGuardTask(String engineSymbol) {
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", "QUERY.NULL.GUARD");
        task.addProperty("flipSite", "ROOT#u7");
        task.addProperty("flipOccurrence", 1);
        task.addProperty("conditionIndex", 0);
        task.addProperty("desiredOutcome", true);
        task.addProperty("concreteGuardReplayProofRequired", true);
        task.add("expectedBranchPrefix", new JsonArray());
        task.add("prefix", new JsonArray());
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Ljava/lang/Object;");
        symbol.addProperty("_exp", engineSymbol);
        JsonObject nil = new JsonObject();
        nil.addProperty("_type", "SymbolExpression");
        nil.addProperty("_java_type", "Ljava/lang/Object;");
        nil.addProperty("_exp", "N");
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.add("_left", symbol);
        condition.addProperty("_op", "==");
        condition.add("_right", nil);
        task.add("negatedCondition", condition);
        task.add("constraints", singleton(condition.deepCopy()));
        return task;
    }

    private static JsonObject nullGuardSource(String javaType) {
        JsonObject source = new JsonObject();
        source.addProperty("activationId", "ACT.SEED");
        source.addProperty("regionId", "REGION.9");
        source.addProperty("rootMethod", "<example.Root: void run("
                + javaType + ")>");
        JsonObject action = nullGuardAction(javaType);
        source.add("symbolize", singleton(action));
        source.add("materializations", singleton(action.deepCopy()));
        return source;
    }

    private static JsonObject nullGuardAction(String javaType) {
        return nullGuardAction(javaType, "REGION.9.in.0", 0);
    }

    private static JsonObject nullGuardAction(String javaType,
                                              String inputSymbol,
                                              int argumentIndex) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", inputSymbol);
        action.addProperty("cell", "<example.Root: " + javaType
                + " input>");
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", argumentIndex);
        action.addProperty("javaType", javaType);
        return action;
    }

    private static JsonObject nullGuardAssignment(String engineSymbol,
                                                  String javaType) {
        return nullGuardAssignment(engineSymbol, javaType,
                "REGION.9.in.0", 0);
    }

    private static JsonObject nullGuardAssignment(String engineSymbol,
                                                  String javaType,
                                                  String inputSymbol,
                                                  int argumentIndex) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", engineSymbol);
        assignment.addProperty("solverSymbol", "sym__payload__ref_"
                + argumentIndex);
        assignment.addProperty("nullnessSolverSymbol",
                "sym__payload__is_null_" + argumentIndex);
        assignment.addProperty("modelIsNull", true);
        assignment.addProperty("inputSymbol", inputSymbol);
        assignment.addProperty("valueType", "NULL");
        assignment.addProperty("value", "null");
        assignment.addProperty("referenceNullnessEncodingAuthority",
                "JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.add("target", nullGuardAction(javaType, inputSymbol,
                argumentIndex));
        return assignment;
    }

    private static JsonArray singleton(JsonElement value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonObject exactScheduleTask() {
        JsonObject task = new JsonObject();
        task.addProperty("flipSite", "U#target");
        task.addProperty("flipOccurrence", 1);
        task.addProperty("conditionIndex", 2);
        task.addProperty("desiredOutcome", true);
        JsonArray prefix = new JsonArray();
        prefix.add(expectedPrefix("U#first", 1, 0, true));
        prefix.add(expectedPrefix("U#second", 1, 1, false));
        task.add("expectedBranchPrefix", prefix);
        return task;
    }

    private static JsonObject exactScheduleRaw() {
        JsonObject raw = new JsonObject();
        JsonArray mappings = new JsonArray();
        mappings.add(exactMapping("U#first", 1, 0, true, false));
        mappings.add(exactMapping("U#second", 1, 1, false, false));
        mappings.add(exactMapping("U#target", 1, 2, true, true));
        raw.add("branchMappings", mappings);
        return raw;
    }

    private static JsonObject expectedPrefix(String site, int occurrence,
                                             int conditionIndex,
                                             boolean outcome) {
        JsonObject row = new JsonObject();
        row.addProperty("siteId", site);
        row.addProperty("occurrence", occurrence);
        row.addProperty("conditionIndex", conditionIndex);
        row.addProperty("outcome", outcome);
        return row;
    }

    private static JsonObject exactMapping(String site, int occurrence,
                                           int conditionIndex,
                                           boolean outcome,
                                           boolean scheduled) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("conditionIndex", conditionIndex);
        mapping.addProperty("outcome", outcome);
        mapping.addProperty("observedOutcome", outcome);
        mapping.addProperty("effectiveOutcome", outcome);
        mapping.addProperty("overrideApplied", false);
        if (scheduled) {
            mapping.addProperty("scheduledTarget", true);
            mapping.addProperty("scheduledDesiredOutcome", outcome);
            mapping.addProperty("scheduledOutcomeMatched", true);
        }
        return mapping;
    }

    private static JsonObject condition(String operator) {
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.add("_left", symbol());
        condition.addProperty("_op", operator);
        JsonObject zero = new JsonObject();
        zero.addProperty("_type", "ConstExpr");
        zero.addProperty("_java_type", "I");
        zero.addProperty("_exp", "Y_I_0");
        condition.add("_right", zero);
        return condition;
    }

    private static JsonObject targetCondition() {
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        JsonObject targetSymbol = new JsonObject();
        targetSymbol.addProperty("_type", "SymbolExpression");
        targetSymbol.addProperty("_java_type", "I");
        targetSymbol.addProperty("_exp",
                "M_I_field_REGION.T.in.0_java/lang/Integer");
        condition.add("_left", targetSymbol);
        condition.addProperty("_op", "==");
        JsonObject zero = new JsonObject();
        zero.addProperty("_type", "ConstExpr");
        zero.addProperty("_java_type", "I");
        zero.addProperty("_exp", "Y_I_0");
        condition.add("_right", zero);
        return condition;
    }

    private static JsonObject symbol() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp",
                "M_I_field_REGION.U.in.0_java/lang/Integer");
        return symbol;
    }

    private static JsonObject region(String id, String outputPort,
                                     String outputCell) {
        JsonObject region = new JsonObject();
        region.addProperty("regionId", id);
        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", outputCell);
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        region.add("outputs", outputs);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", outputCell);
        slice.addProperty("complete", true);
        slice.add("inputPorts", new JsonArray());
        JsonArray slices = new JsonArray();
        slices.add(slice);
        region.add("outputSlices", slices);
        return region;
    }

    private static String text(JsonObject object, String field) {
        return object != null && object.has(field)
                ? object.get(field).getAsString() : "";
    }

    private static String shortHashForTest(String value) throws Exception {
        byte[] bytes = MessageDigest.getInstance("SHA-256").digest(
                value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte item : bytes) {
            result.append(String.format("%02x", item & 0xff));
        }
        return result.substring(0, 16);
    }

    private static Fixture fixture() {
        JsonObject upstream = new JsonObject();
        upstream.addProperty("regionId", "REGION.U");
        JsonArray outputs = new JsonArray();
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.U.out.0");
        output.addProperty("cell", "<example.Upstream: int value>");
        outputs.add(output);
        upstream.add("outputs", outputs);
        JsonObject target = new JsonObject();
        target.addProperty("regionId", "REGION.T");
        JsonArray inputs = new JsonArray();
        JsonObject input = new JsonObject();
        input.addProperty("portId", "REGION.T.in.0");
        input.addProperty("cell", "<example.Target: int value>");
        inputs.add(input);
        target.add("symbolicInputs", inputs);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.U.SEED");
        activation.addProperty("regionId", "REGION.U");
        activation.addProperty("rootMethod", "<example.Upstream: int run(int)>");
        activation.addProperty("test", "local-test");
        activation.addProperty("replayable", true);
        activation.addProperty("symbolicReady", true);
        activation.addProperty("requestedOutputSliceComplete", true);
        activation.addProperty("requestedOutputSlicePolicy",
                "NEUTRAL_TEST_OUTPUT_DEPENDENCY_CLOSURE");
        JsonObject outputSlice = new JsonObject();
        outputSlice.addProperty("complete", true);
        JsonArray outputSites = new JsonArray();
        outputSites.add("U#u1");
        outputSlice.add("sites", outputSites);
        activation.add("requestedOutputSlice", outputSlice);
        JsonArray materializations = new JsonArray();
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.U.in.0");
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", 0);
        materializations.add(action);
        activation.add("materializations", materializations);

        JsonObject targetActivation = new JsonObject();
        targetActivation.addProperty("activationId", "ACT.TARGET");
        targetActivation.addProperty("regionId", "REGION.T");
        targetActivation.addProperty("regionInstanceId",
                "REGION.T@test#call2");
        targetActivation.addProperty("rootMethod",
                "<example.Target: void fail(int)>");
        targetActivation.addProperty("test", "local-test");
        targetActivation.addProperty("replayable", true);
        targetActivation.add("captureGoal",
                RegionCaptureGoal.targetBranch().toJson());
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId",
                "<example.Target: void fail(int)>#u1");
        targetBranch.addProperty("occurrence", 1);
        targetBranch.addProperty("desiredOutcome", false);
        targetBranch.addProperty("validationOnly", true);
        targetBranch.addProperty("branchOverrideAllowed", false);
        targetActivation.add("targetBranch", targetBranch);
        JsonObject targetQuery = new JsonObject();
        targetQuery.addProperty("activationId", "ACT.TARGET");
        targetQuery.addProperty("regionId", "REGION.T");
        targetQuery.addProperty("regionInstanceId",
                "REGION.T@test#call2");
        targetQuery.addProperty("siteId",
                "<example.Target: void fail(int)>#u1");
        targetQuery.addProperty("occurrence", 1);
        targetQuery.addProperty("desiredOutcome", false);
        targetQuery.addProperty("readyForSolver", true);
        targetQuery.addProperty("readyForReplay", false);
        JsonObject originalTargetCondition = condition("!=");
        JsonObject negatedTargetCondition = condition("==");
        targetQuery.add("originalTargetCondition",
                originalTargetCondition);
        targetQuery.add("negatedTargetCondition",
                negatedTargetCondition.deepCopy());
        JsonArray targetConstraints = new JsonArray();
        targetConstraints.add(negatedTargetCondition.deepCopy());
        targetQuery.add("constraints", targetConstraints);
        JsonObject targetQueryContext = new JsonObject();
        targetQueryContext.addProperty("regionInstanceId",
                "REGION.T@test#call2");
        targetQuery.add("symbolicContext", targetQueryContext);
        targetQuery.add("captureGoal",
                RegionCaptureGoal.targetBranch().toJson());
        targetActivation.add("directedTargetQuery", targetQuery);

        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.U.T");
        edge.addProperty("fromRegion", "REGION.U");
        edge.addProperty("fromPort", "REGION.U.out.0");
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("toPort", "REGION.T.in.0");
        edge.addProperty("validatedRelation", "EQUALITY");
        edge.addProperty("composable", true);
        edge.addProperty("eligibleForAutomaticDerivation", true);
        edge.addProperty("eligibleForAutomaticSmt", true);
        edge.addProperty("status", "CONFIRMED_RUNTIME_VALUE_EQUALITY");
        edge.addProperty("valueEqualityObserved", true);
        edge.addProperty("confirmedValueEqualityPairCount", 1);
        edge.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        edge.add("evidence", new JsonArray());

        JsonObject root = new JsonObject();
        root.addProperty("activationId", "ACT.TARGET");
        root.addProperty("regionId", "REGION.T");
        root.addProperty("regionInstanceId", "REGION.T@test#call2");
        root.addProperty("rootMethod", "<example.Target: void fail(int)>");
        root.addProperty("test", "local-test");
        root.addProperty("siteId", "<example.Target: void fail(int)>#u1");
        root.addProperty("occurrence", 1);
        root.addProperty("desiredOutcome", false);
        root.addProperty("readyForSolver", true);
        root.addProperty("readyForReplay", false);
        root.addProperty("replayAlreadyValidated", true);
        root.addProperty("targetReplayValidated", true);
        root.addProperty("validatedSummaryId", "SUMMARY.TARGET.VALIDATED");
        root.addProperty("replayValidationAuthority",
                "SAME_INSTANCE_IMPORTED_UNFORCED_TARGET_REPLAY");
        root.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        JsonObject symbolicContext = new JsonObject();
        symbolicContext.addProperty("regionInstanceId",
                "REGION.T@test#call2");
        root.add("symbolicContext", symbolicContext);
        JsonObject validatedSummary = new JsonObject();
        validatedSummary.addProperty("summaryId",
                "SUMMARY.TARGET.VALIDATED");
        validatedSummary.addProperty("activationId", "ACT.TARGET");
        validatedSummary.addProperty("regionId", "REGION.T");
        validatedSummary.addProperty("regionInstanceId",
                "REGION.T@test#call2");
        validatedSummary.addProperty("targetReplayValidated", true);
        validatedSummary.addProperty("branchOverrideUsed", false);
        JsonObject targetAdmission = new JsonObject();
        targetAdmission.addProperty("required", true);
        targetAdmission.addProperty("valid", true);
        targetAdmission.addProperty("branchOverrideAccepted", false);
        targetAdmission.addProperty("authority",
                "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION");
        validatedSummary.add("executionAdmission", targetAdmission);
        root.add("validatedTargetSummary", validatedSummary);

        JsonObject importedTargetSummary = validatedSummary.deepCopy();
        importedTargetSummary.addProperty("cacheKey",
                "CACHE.SUMMARY.TARGET.VALIDATED");
        importedTargetSummary.addProperty("valid", true);
        importedTargetSummary.add("captureGoal",
                RegionCaptureGoal.targetBranch().toJson());

        ConcolicCampaignRunner.State state =
                new ConcolicCampaignRunner.State(
                        Arrays.asList(upstream, target),
                        Arrays.asList(activation, targetActivation),
                        Collections.singletonList(edge),
                        Collections.singletonList(root),
                        Collections.singletonList(importedTargetSummary),
                        Collections.<JsonObject>emptyList());
        return new Fixture(state);
    }

    private static final class Fixture {
        private final ConcolicCampaignRunner.State state;

        private Fixture(ConcolicCampaignRunner.State state) {
            this.state = state;
        }
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
