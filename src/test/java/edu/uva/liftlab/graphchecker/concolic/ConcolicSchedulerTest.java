package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSchedulerTest {
    private static final String ROOT = "<example.Server: void receive()>";
    private static final String CALLBACK = "<example.Callback: void handle()>";
    private static final String TARGET = "<example.Manager: byte[] lookup(int)>#u8";
    private static final String USERNAME = CALLBACK + "::$r4";
    private static final String ALL_KEYS =
            "<example.Manager: java.util.Map allKeys>";
    private static final String CURRENT_KEY_ID =
            "<example.Manager: example.BlockKey currentKey>#field:keyId";

    @Test
    public void schedulesDirectedFlipAndBuildsTypedMergePlan() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0",
                            "--force-branch-validation", "true"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.jobs.size());
            JsonObject job = result.jobs.get(0);
            assertEquals("CAPTURE_THEN_NEGATE", job.get("phase").getAsString());
            assertEquals("LOCAL_UNIT_TEST",
                    job.get("workloadKind").getAsString());
            assertTrue(job.get("captureReady").getAsBoolean());
            JsonObject target = job.getAsJsonObject("targetBranch");
            assertTrue(target.get("observedOutcome").getAsBoolean());
            assertFalse(target.get("desiredOutcome").getAsBoolean());
            assertEquals(1, target.get("occurrence").getAsInt());

            JsonObject scheduled = result.scheduledActivations.get(0);
            assertEquals("example.Server", scheduled.get(
                    "receiverRuntimeClass").getAsString());
            assertEquals("rpc-handler",
                    scheduled.get("threadName").getAsString());
            assertEquals(1, scheduled.get(
                    "invocationOrdinalWithinContext").getAsInt());
            assertFalse(scheduled.get("threadIdSelectionUsed")
                    .getAsBoolean());
            assertEquals("TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                            + "THREAD_NAME_CONTEXT_ORDINAL_V1",
                    scheduled.get("rootContextSelectionAuthority")
                            .getAsString());
            assertFalse(scheduled.get("discoverySymbolicReady").getAsBoolean());
            assertTrue(scheduled.get("schedulerReady").getAsBoolean());
            assertTrue(scheduled.get("symbolicReady").getAsBoolean());
            assertEquals("LOCAL_DEFINITION", scheduled
                    .getAsJsonArray("materializations").get(0)
                    .getAsJsonObject().get("bindingMode").getAsString());
            assertEquals(36, scheduled.getAsJsonArray("materializations")
                    .get(0).getAsJsonObject()
                    .getAsJsonArray("definitionSites").get(0)
                    .getAsJsonObject().get("unitIndex").getAsInt());
            assertEquals("FIELD_ACCESS", scheduled
                    .getAsJsonArray("materializations").get(1)
                    .getAsJsonObject().get("bindingMode").getAsString());
            JsonObject projected = scheduled
                    .getAsJsonArray("materializations").get(2)
                    .getAsJsonObject();
            assertEquals("example.Manager",
                    projected.get("accessOwnerClass").getAsString());
            assertEquals("currentKey",
                    projected.get("accessField").getAsString());
            assertEquals("example.BlockKey",
                    projected.get("leafOwnerClass").getAsString());
            assertEquals("keyId", projected.get("leafField").getAsString());
            assertEquals(2, projected.getAsJsonArray("fieldPath").size());
            assertEquals("SOOT_BRANCH_OVERRIDE_VALIDATION", scheduled
                    .getAsJsonArray("forcedBranches").get(0)
                    .getAsJsonObject().get("mode").getAsString());

            assertEquals(1, result.mergePlan
                    .getAsJsonArray("equalityClasses").size());
            assertEquals(1, result.mergePlan
                    .getAsJsonArray("versionedStateMerges").size());
            assertTrue(Files.isRegularFile(fixture.output.resolve(
                    "scheduled_activation_plan.jsonl")));
            assertTrue(Files.isRegularFile(fixture.output.resolve(
                    "symbolic_merge_plan.json")));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void differentTargetInputPortsRemainIndependentStateMerges()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String keyIdSource =
                    "<example.NameNode: int exportedKeyId>";
            String keyRegion = "{\"regionId\":\"REGION.12\","
                    + "\"rootMethod\":\"<example.NameNode: void "
                    + "exportKeyId()>\",\"symbolicInputs\":[],"
                    + "\"outputs\":[{\"portId\":\"REGION.12.out.0\","
                    + "\"cell\":\"" + keyIdSource + "\"}]}\n";
            Files.write(fixture.regions,
                    keyRegion.getBytes(StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.APPEND);

            String keyEdge = "{\"edgeId\":\"E.KEY_ID\","
                    + "\"fromRegion\":\"REGION.12\","
                    + "\"toRegion\":\"REGION.0\","
                    + "\"fromPort\":\"" + keyIdSource + "\","
                    + "\"toPort\":\"" + CURRENT_KEY_ID + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"validatedRelation\":\"READ_FROM\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true,"
                    + "\"confirmedReadFromPairCount\":1,"
                    + "\"status\":\"CONFIRMED_READ_FROM\","
                    + "\"eligibleForAutomaticDerivation\":true,"
                    + "\"eligibleForAutomaticSmt\":true,"
                    + "\"composable\":true,\"evidence\":[{"
                    + "\"writeSeq\":3,\"readSeq\":4,"
                    + "\"receiverObjectId\":8,"
                    + "\"orderConfirmed\":true}]}\n";
            Files.write(fixture.edges,
                    keyEdge.getBytes(StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.APPEND);

            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan",
                            fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0",
                            "--force-branch-validation", "true"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            JsonArray direct = result.mergePlan.getAsJsonArray(
                    "versionedStateMerges");
            assertEquals(2, direct.size());
            assertEquals(0, result.mergePlan.getAsJsonArray(
                    "alternativeWriterGroups").size());
            assertTrue(direct.toString().contains("REGION.0.in.1"));
            assertTrue(direct.toString().contains("REGION.0.in.2"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void capturedSummaryProducesPrefixPlusNegatedTargetQuery()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject captured = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.summaries),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonObject bridge = new JsonObject();
            bridge.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
            bridge.addProperty("inputPort", "REGION.0.in.25");
            bridge.addProperty("engineArrayId", "VM_ARRAY_FATAL");
            JsonArray bridges = new JsonArray();
            bridges.add(bridge);
            captured.add("engineArrayInputBindings", bridges);
            Files.write(fixture.summaries,
                    (captured + "\n").getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.queries.size());
            JsonObject query = result.queries.get(0);
            assertTrue(query.get("readyForSolver").getAsBoolean());
            assertTrue(query.get("readyForReplay").getAsBoolean());
            assertFalse(query.get("targetReplayValidated").getAsBoolean());
            assertFalse(query.get("replayAlreadyValidated").getAsBoolean());
            assertEquals(2, query.get("conditionIndex").getAsInt());
            JsonArray constraints = query.getAsJsonArray("constraints");
            assertEquals(3, constraints.size());
            assertEquals("==", constraints.get(2).getAsJsonObject()
                    .get("_op").getAsString());
            assertEquals("!=", query.getAsJsonObject(
                    "originalTargetCondition").get("_op").getAsString());
            assertEquals("FINITE_MAP_SEMANTIC_MODEL", query
                    .getAsJsonObject("semanticModel").get("solver")
                    .getAsString());
            assertEquals(6, query.getAsJsonArray("replayMaterializations")
                    .get(0).getAsJsonObject().get("unitIndex").getAsInt());
            assertEquals("REFERENCE_RESULT", query
                    .getAsJsonArray("replayMaterializations").get(0)
                    .getAsJsonObject().get("kind").getAsString());
            assertEquals("MAP_LOOKUP", query
                    .getAsJsonArray("replayMaterializations").get(0)
                    .getAsJsonObject().get("operationSemantics").getAsString());
            assertEquals(1, query.getAsJsonArray("replayMaterializations")
                    .get(0).getAsJsonObject().get("occurrence").getAsInt());
            assertEquals("DROP_OLD_SUFFIX",
                    query.get("suffixPolicy").getAsString());
            assertEquals("REGION.0@testMiniDfs#call7",
                    query.get("regionInstanceId").getAsString());
            assertEquals(bridges, query.getAsJsonArray(
                    "engineArrayInputBindings"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void validatedReplayKeepsItsSameInstanceDirectedQuery()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String[] argv = new String[]{
                    "--regions", fixture.regions.toString(),
                    "--activation-plan", fixture.activations.toString(),
                    "--edge-validations", fixture.edges.toString(),
                    "--static-graph", fixture.staticGraph.toString(),
                    "--summaries", fixture.summaries.toString(),
                    "--output-dir", fixture.output.toString(),
                    "--region-id", "REGION.0"};
            ConcolicScheduler.Result initial = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(argv));
            JsonObject directedQuery = initial.queries.get(0).deepCopy();

            JsonObject summary = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.summaries),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            summary.addProperty("summaryId", "SUMMARY.REGION.0.VALIDATED");
            summary.addProperty("regionInstanceId",
                    "REGION.0@testMiniDfs#call7");
            summary.addProperty("targetReplayValidated", true);
            summary.addProperty("branchOverrideUsed", false);
            JsonObject admission = new JsonObject();
            admission.addProperty("required", true);
            admission.addProperty("valid", true);
            admission.addProperty("branchOverrideAccepted", false);
            admission.addProperty("authority",
                    "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION");
            summary.add("executionAdmission", admission);
            summary.add("directedTargetQuery", directedQuery);
            Files.write(fixture.summaries,
                    (summary + "\n").getBytes(StandardCharsets.UTF_8));

            ConcolicScheduler.Result reused = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(argv));

            assertEquals(1, reused.queries.size());
            JsonObject query = reused.queries.get(0);
            assertTrue(query.get("readyForSolver").getAsBoolean());
            assertFalse(query.get("readyForReplay").getAsBoolean());
            assertTrue(query.get("replayAlreadyValidated").getAsBoolean());
            assertTrue(query.get("targetReplayValidated").getAsBoolean());
            assertEquals("SUMMARY.REGION.0.VALIDATED",
                    query.get("validatedSummaryId").getAsString());
            JsonObject validatedSummary = query.getAsJsonObject(
                    "validatedTargetSummary");
            assertEquals("REGION.0@testMiniDfs#call7", validatedSummary
                    .get("regionInstanceId").getAsString());
            assertTrue(validatedSummary.get("targetReplayValidated")
                    .getAsBoolean());
            assertFalse(validatedSummary.get("branchOverrideUsed")
                    .getAsBoolean());
            assertEquals("REGION.0@testMiniDfs#call7", query
                    .getAsJsonObject("symbolicContext")
                    .get("regionInstanceId").getAsString());
            assertEquals("REGION.0@testMiniDfs#call7",
                    query.get("regionInstanceId").getAsString());
            assertEquals("TARGET_REPLAY_VALIDATED", reused.jobs.get(0)
                    .get("phase").getAsString());
            assertFalse(reused.scheduledActivations.get(0)
                    .has("replayMaterializations"));
            assertFalse(reused.scheduledActivations.get(0)
                    .get("targetReplayRequired").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void sameActivationIdFromAnotherTraceIsNotTargetProvenance()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject stale = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.summaries),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            stale.addProperty("regionInstanceId",
                    "REGION.0@another-trace#call7");
            Files.write(fixture.summaries,
                    (stale + "\n").getBytes(StandardCharsets.UTF_8));

            ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0"}));

            assertEquals(0, result.queries.size());
            assertEquals("CAPTURE_THEN_NEGATE", result.jobs.get(0)
                    .get("phase").getAsString());
            assertFalse(result.scheduledActivations.get(0)
                    .has("directedTargetQuery"));
            assertFalse(result.scheduledActivations.get(0)
                    .get("targetReplayRequired").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void captureOnlyIgnoresStaleSummaryAndEmitsNoReplayAction()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0",
                            "--capture-only"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(0, result.queries.size());
            assertEquals("CAPTURE_ONLY", result.jobs.get(0)
                    .get("phase").getAsString());
            assertFalse(result.scheduledActivations.get(0)
                    .has("replayMaterializations"));
            assertTrue(result.summary.get("captureOnly").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void fatalCaptureDefersNonMaterializableFrontierInputs()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject activation = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.activations),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonObject environment = new JsonObject();
            environment.addProperty("symbol", "REGION.0.in.env");
            environment.addProperty("cell", "<example.Clock: long now()>.return");
            environment.addProperty("location", "ENVIRONMENT_MODEL");
            environment.addProperty("sourceKind", "ENVIRONMENT");
            activation.getAsJsonArray("symbolize").add(environment);
            Files.write(fixture.activations,
                    (activation.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0",
                            "--capture-only"}));

            JsonObject job = result.jobs.get(0);
            assertTrue(job.get("captureReady").getAsBoolean());
            assertFalse(job.get("materializationComplete").getAsBoolean());
            assertEquals(1, job.get("deferredMaterializationCount").getAsInt());
            assertTrue(job.get("executableMaterializationCount").getAsInt()
                    > 0);
            JsonObject scheduled = result.scheduledActivations.get(0);
            assertTrue(scheduled.get("schedulerReady").getAsBoolean());
            assertFalse(scheduled.get("materializationComplete")
                    .getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void captureOnlySchedulesOutputClosureWithoutBranchTarget()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String activation = "{\"activationId\":\"ACT.PRODUCER.0\","
                    + "\"regionInstanceId\":\"REGION.11@test#call7\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"<example.Updater: void run()>\","
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"symbolicReady\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSliceComplete\":true,"
                    + "\"requestedOutput\":{"
                    + "\"portId\":\"REGION.11.out.0\","
                    + "\"cell\":\"" + ALL_KEYS + "\","
                    + "\"kind\":\"HEAP_STATE\"},"
                    + "\"edgeBindings\":[{"
                    + "\"edgeId\":\"E.STATE\","
                    + "\"writerEventSeq\":10,\"readerEventSeq\":20}],"
                    + "\"symbolize\":[],\"outputs\":[],\"branches\":[]}\n";
            Files.write(fixture.activations,
                    activation.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.jobs.size());
            assertEquals("CAPTURE_OUTPUT_PATH", result.jobs.get(0)
                    .get("phase").getAsString());
            assertEquals("OUTPUT_CLOSURE", result.jobs.get(0)
                    .getAsJsonObject("captureGoal").get("kind")
                    .getAsString());
            assertFalse(result.jobs.get(0).has("targetBranch"));
            assertFalse(result.scheduledActivations.get(0)
                    .has("targetBranch"));
            assertEquals(0, result.queries.size());
            assertEquals(1, result.summary.get("upstreamCaptureJobCount")
                    .getAsInt());

            Files.write(fixture.activations, activation.replace(
                    "\"requestedOutputSliceComplete\":true",
                    "\"requestedOutputSliceComplete\":false")
                    .getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result blocked =
                    ConcolicScheduler.schedule(arguments);
            assertFalse(blocked.jobs.get(0).get("captureReady")
                    .getAsBoolean());
            assertFalse(blocked.scheduledActivations.get(0)
                    .get("symbolicReady").getAsBoolean());

            String deferred = activation.replace("\"symbolize\":[]",
                    "\"symbolize\":[{\"symbol\":\"REGION.11.in.env\","
                            + "\"cell\":\"<example.Clock: long now()>.return\","
                            + "\"location\":\"ENVIRONMENT_MODEL\"}]");
            Files.write(fixture.activations,
                    deferred.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result deferredClosure =
                    ConcolicScheduler.schedule(arguments);
            assertFalse(deferredClosure.jobs.get(0).get("captureReady")
                    .getAsBoolean());
            assertFalse(deferredClosure.jobs.get(0)
                    .get("materializationComplete").getAsBoolean());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void expandsRecursiveReachabilitySupportBeforePrimaryActivation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject primary = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.activations),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonObject nn = JsonParser.parseString("{"
                    + "\"activationId\":\"ACT.NN\","
                    + "\"regionId\":\"REGION.1\","
                    + "\"regionInstanceId\":\"REGION.1@test#call1\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"<example.Client: void send()>\","
                    + "\"invocationOrdinal\":1,\"symbolize\":[]}")
                    .getAsJsonObject();
            JsonObject heartbeat = JsonParser.parseString("{"
                    + "\"activationId\":\"ACT.HEARTBEAT\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"regionInstanceId\":\"REGION.11@test#call2\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"<example.Updater: void run()>\","
                    + "\"invocationOrdinal\":1,\"symbolize\":[]}")
                    .getAsJsonObject();
            JsonArray heartbeatSupport = new JsonArray();
            heartbeatSupport.add(nn);
            heartbeat.add("reachabilitySupportActivations",
                    heartbeatSupport);
            JsonArray primarySupport = new JsonArray();
            primarySupport.add(heartbeat);
            primary.add("reachabilitySupportActivations", primarySupport);
            Files.write(fixture.activations,
                    (primary + "\n").getBytes(StandardCharsets.UTF_8));

            ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.0", "--capture-only"}));

            assertEquals(1, result.jobs.size());
            assertEquals(3, result.scheduledActivations.size());
            assertEquals("ACT.NN", result.scheduledActivations.get(0)
                    .get("activationId").getAsString());
            assertEquals("ACT.HEARTBEAT", result.scheduledActivations.get(1)
                    .get("activationId").getAsString());
            assertEquals("ACT.0", result.scheduledActivations.get(2)
                    .get("activationId").getAsString());
            assertEquals("REACHABILITY_SUPPORT",
                    result.scheduledActivations.get(0)
                            .get("activationBundleMemberRole").getAsString());
            assertEquals("PRIMARY", result.scheduledActivations.get(2)
                    .get("activationBundleMemberRole").getAsString());
            assertEquals("ALL", result.jobs.get(0)
                    .get("activationSelectionRequired").getAsString());
            assertEquals(2, result.jobs.get(0)
                    .get("reachabilitySupportActivationCount").getAsInt());
            assertEquals(2, result.summary
                    .get("reachabilitySupportActivationCount").getAsInt());
            assertEquals("ALL", result.summary
                    .get("activationSelectionRequired").getAsString());
            assertFalse(result.scheduledActivations.get(0)
                    .has("reachabilitySupportActivations"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void selectiveArgumentFieldPathsMustBeNonEmptyForCapture()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String root = "<example.Updater: void apply(example.Envelope)>";
            String activation = "{\"activationId\":\"ACT.PRODUCER.0\","
                    + "\"regionInstanceId\":\"REGION.11@test#call7\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSliceComplete\":true,"
                    + "\"requestedOutput\":{"
                    + "\"portId\":\"REGION.11.out.0\","
                    + "\"cell\":\"" + ALL_KEYS + "\","
                    + "\"kind\":\"HEAP_STATE\"},"
                    + "\"edgeBindings\":[{"
                    + "\"edgeId\":\"E.STATE\","
                    + "\"writerEventSeq\":10,\"readerEventSeq\":20}],"
                    + "\"symbolize\":[{"
                    + "\"symbol\":\"REGION.11.in.0\","
                    + "\"cell\":\"" + root
                    + ".param0:example.Envelope\","
                    + "\"sourceKind\":\"ROOT_ARGUMENT\","
                    + "\"location\":\"ARGUMENT_FIELD_PATH\","
                    + "\"observed\":true,\"index\":0,"
                    + "\"fieldPaths\":[[\"payload\",\"entries\"]]}],"
                    + "\"outputs\":[],\"branches\":[]}\n";
            Files.write(fixture.activations,
                    activation.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only"});

            ConcolicScheduler.Result ready =
                    ConcolicScheduler.schedule(arguments);
            assertTrue(ready.jobs.get(0).get("captureReady").getAsBoolean());
            JsonObject materialization = ready.scheduledActivations.get(0)
                    .getAsJsonArray("materializations").get(0)
                    .getAsJsonObject();
            assertEquals("ROOT_ENTRY",
                    materialization.get("bindingMode").getAsString());
            assertEquals("entries", materialization
                    .getAsJsonArray("fieldPaths").get(0).getAsJsonArray()
                    .get(1).getAsString());

            Files.write(fixture.activations, activation.replace(
                    "[[\"payload\",\"entries\"]]", "[]")
                    .getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result blocked =
                    ConcolicScheduler.schedule(arguments);
            assertFalse(blocked.jobs.get(0).get("captureReady").getAsBoolean());
            assertEquals("UNRESOLVED_ARGUMENT_FIELD_PATH",
                    blocked.scheduledActivations.get(0)
                            .getAsJsonArray("materializations").get(0)
                            .getAsJsonObject().get("bindingMode").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void projectedMethodLocalUsesOnlyDeclaredProjectionSegments()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String root = "<example.Updater: void <init>(example.Keys)>";
            String cell = root + "::$r2#field:currentKey#field:keyId";
            String activation = "{\"activationId\":\"ACT.FIELD.0\","
                    + "\"regionInstanceId\":\"REGION.11@test#call7\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSliceComplete\":true,"
                    + "\"requestedOutput\":{"
                    + "\"portId\":\"REGION.11.out.0\","
                    + "\"cell\":\"" + ALL_KEYS + "\","
                    + "\"kind\":\"HEAP_STATE\"},"
                    + "\"symbolize\":[{"
                    + "\"symbol\":\"REGION.11.in.0\","
                    + "\"cell\":\"" + cell + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"location\":\"HEAP_OBJECT_FIELD\"}],"
                    + "\"outputs\":[],\"branches\":[]}\n";
            Files.write(fixture.activations,
                    activation.getBytes(StandardCharsets.UTF_8));

            ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.FIELD.0",
                            "--capture-only"}));

            JsonObject binding = result.scheduledActivations.get(0)
                    .getAsJsonArray("materializations").get(0)
                    .getAsJsonObject();
            assertEquals("FIELD_ACCESS",
                    binding.get("bindingMode").getAsString());
            assertEquals(2, binding.getAsJsonArray("fieldPath").size());
            assertEquals("currentKey", binding.getAsJsonArray("fieldPath")
                    .get(0).getAsString());
            assertEquals("keyId", binding.getAsJsonArray("fieldPath")
                    .get(1).getAsString());
            assertEquals("currentKey",
                    binding.get("accessField").getAsString());
            assertEquals("", binding.get("accessOwnerClass").getAsString());
            assertEquals("keyId", binding.get("leafField").getAsString());
            assertEquals("", binding.get("leafOwnerClass").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void outputClosureMaterializesCallReturnAtExactDefinition()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String root = "<example.Updater: void run()>";
            String call = "<example.Source: boolean isEnabled()>";
            String returned = call + ".return";
            String local = root + "::$z0";
            String site = root + "#u3";
            String activation = "{\"activationId\":\"ACT.PRODUCER.0\","
                    + "\"regionInstanceId\":\"REGION.11@test#call7\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSliceComplete\":true,"
                    + "\"requestedOutputMethods\":[\"" + root + "\"],"
                    + "\"requestedOutputSlice\":{\"sites\":[\""
                    + site + "\"]},"
                    + "\"requestedOutput\":{"
                    + "\"portId\":\"REGION.11.out.0\","
                    + "\"cell\":\"" + ALL_KEYS + "\","
                    + "\"kind\":\"HEAP_STATE\"},"
                    + "\"edgeBindings\":[{"
                    + "\"edgeId\":\"E.STATE\","
                    + "\"writerEventSeq\":10,\"readerEventSeq\":20}],"
                    + "\"symbolize\":[{"
                    + "\"symbol\":\"REGION.11.in.0\","
                    + "\"cell\":\"" + returned + "\","
                    + "\"sourceKind\":\"OPAQUE_CALL\","
                    + "\"location\":\"CALL_RETURN\","
                    + "\"observed\":false}],"
                    + "\"outputs\":[],\"branches\":[]}\n";
            Files.write(fixture.activations,
                    activation.getBytes(StandardCharsets.UTF_8));
            String graph = "{\"id\":\"DF.RETURN\","
                    + "\"transferKind\":\"FUNCTION_RETURN\","
                    + "\"fromCell\":\"" + returned + "\","
                    + "\"toCell\":\"" + local + "\","
                    + "\"method\":\"" + root + "\","
                    + "\"unitIndex\":3,\"siteId\":\"" + site + "\","
                    + "\"unit\":\"$z0 = virtualinvoke r1."
                    + call + "()\"}\n";
            Files.write(fixture.staticGraph,
                    graph.getBytes(StandardCharsets.UTF_8));

            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only"});
            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertTrue(result.jobs.get(0).get("captureReady").getAsBoolean());
            JsonArray materializations = result.scheduledActivations.get(0)
                    .getAsJsonArray("materializations");
            assertEquals(1, materializations.size());
            JsonObject binding = materializations.get(0).getAsJsonObject();
            assertEquals("LOCAL_DEFINITION",
                    binding.get("bindingMode").getAsString());
            assertEquals("CALL_RETURN_DEFINITION",
                    binding.get("sourceBindingMode").getAsString());
            assertEquals(root, binding.get("method").getAsString());
            assertEquals("$z0", binding.get("local").getAsString());
            assertEquals(3, binding.getAsJsonArray("definitionSites").get(0)
                    .getAsJsonObject().get("unitIndex").getAsInt());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void verifiedVmClockPlaceholderNeedsNoCaptureMaterialization() {
        JsonObject activation = JsonParser.parseString("{"
                + "\"activationId\":\"ACT.ENV.0\","
                + "\"regionId\":\"REGION.7\","
                + "\"requestedOutputSliceComplete\":true,"
                + "\"symbolize\":[{"
                + "\"symbol\":\"REGION.7.in.0\","
                + "\"cell\":\"<java.lang.System: long "
                + "currentTimeMillis()>.return\","
                + "\"sourceKind\":\"ENVIRONMENT\","
                + "\"location\":\"ENVIRONMENT_MODEL\"}]}"
        ).getAsJsonObject();

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation,
                java.util.Collections.<JsonObject>emptyList());

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertTrue(prepared.get("materializationComplete").getAsBoolean());
        assertEquals(0, prepared.get("executableMaterializationCount")
                .getAsInt());
        assertEquals(0, prepared.get("deferredMaterializationCount")
                .getAsInt());
        assertEquals(1, prepared.get("vmIntrinsicPlaceholderCount")
                .getAsInt());
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        assertEquals("VM_INTRINSIC_PLACEHOLDER",
                binding.get("bindingMode").getAsString());
        assertEquals("currentTimeMills",
                binding.get("placeholderFunction").getAsString());
        assertFalse(binding.get("modelControllable").getAsBoolean());
        assertEquals("UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION",
                binding.get("replayPolicy").getAsString());
    }

    @Test
    public void unverifiedEnvironmentSourceStillBlocksOutputCapture() {
        JsonObject activation = JsonParser.parseString("{"
                + "\"activationId\":\"ACT.ENV.1\","
                + "\"regionId\":\"REGION.7\","
                + "\"requestedOutputSliceComplete\":true,"
                + "\"symbolize\":[{"
                + "\"symbol\":\"REGION.7.in.0\","
                + "\"cell\":\"<example.Clock: long now()>.return\","
                + "\"sourceKind\":\"ENVIRONMENT\","
                + "\"location\":\"ENVIRONMENT_MODEL\"}]}"
        ).getAsJsonObject();

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation,
                java.util.Collections.<JsonObject>emptyList());

        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertFalse(prepared.get("materializationComplete").getAsBoolean());
        assertEquals(0, prepared.get("vmIntrinsicPlaceholderCount")
                .getAsInt());
    }

    @Test
    public void exactArrayFieldEvidenceSurvivesSchedulerMaterialization() {
        String method = "<example.ArrayReader: void run()>";
        JsonObject activation = arrayFieldCaptureActivation(
                exactArrayFieldAction(method));

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation,
                java.util.Collections.<JsonObject>emptyList());

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertTrue(prepared.get("materializationComplete").getAsBoolean());
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        assertEquals(method + "#u7",
                binding.get("consumedFieldSiteId").getAsString());
        assertEquals("DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1",
                binding.get("consumedFieldRootAuthority").getAsString());
        assertTrue(binding.get("arrayFieldMaterializationComplete")
                .getAsBoolean());
    }

    @Test
    public void missingConsumedArraySiteCannotBeUpgradedByScheduler() {
        JsonObject action = exactArrayFieldAction(
                "<example.ArrayReader: void run()>");
        action.remove("consumedFieldSiteId");
        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.<JsonObject>emptyList());

        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertFalse(prepared.get("materializationComplete").getAsBoolean());
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        assertEquals("EXACT_CONSUMED_FIELD_METHOD_UNIT_SITE_MISSING",
                binding.get("materializationIssue").getAsString());
    }

    @Test
    public void incompleteConsumedArrayBindingCannotBeScheduled() {
        JsonObject action = exactArrayFieldAction(
                "<example.ArrayReader: void run()>");
        action.remove("consumedFieldBindingComplete");
        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.<JsonObject>emptyList());

        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertFalse(prepared.get("materializationComplete").getAsBoolean());
        assertEquals("PLANNER_CONSUMED_FIELD_BINDING_INCOMPLETE",
                prepared.getAsJsonArray("materializations").get(0)
                        .getAsJsonObject().get("materializationIssue")
                        .getAsString());
    }

    @Test
    public void missingConsumedArrayOccurrenceCannotBeScheduled() {
        JsonObject action = exactArrayFieldAction(
                "<example.ArrayReader: void run()>");
        action.remove("consumedFieldOccurrence");
        action.remove("consumedFieldOccurrenceAuthority");
        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.<JsonObject>emptyList());

        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertEquals("EXACT_CONSUMED_FIELD_OCCURRENCE_INVALID",
                prepared.getAsJsonArray("materializations").get(0)
                        .getAsJsonObject().get("materializationIssue")
                        .getAsString());
    }

    @Test
    public void schedulerRejectsPlannerHeapFieldMetadataConflict() {
        JsonObject action = exactArrayFieldAction(
                "<example.ArrayReader: void run()>");
        action.add("fieldPath", JsonParser.parseString("[\"other\"]"));
        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.<JsonObject>emptyList());

        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertFalse(prepared.get("materializationComplete").getAsBoolean());
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        assertEquals("[\"other\"]",
                binding.getAsJsonArray("fieldPath").toString());
        assertTrue(binding.get("materializationIssue").getAsString()
                .contains("FIELD_PATH_LEAF_MISMATCH"));
    }

    @Test
    public void directArrayAuthorityRejectsNestedLogicalPath() {
        JsonObject action = exactArrayFieldAction(
                "<example.ArrayReader: void run()>");
        action.add("fieldPath", JsonParser.parseString(
                "[\"payload\",\"values\"]"));
        JsonObject declaration = new JsonObject();
        declaration.add("fieldPath", JsonParser.parseString(
                "[\"payload\",\"values\"]"));
        declaration.addProperty("fieldSignature",
                "<example.ArrayState: example.Value[] values>");
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        action.add("fieldPathLeafDeclarations", declarations);
        // Avoid the HEAP cell consistency guard obscuring the root-authority
        // defense: this shape models a non-HEAP FIELD_ACCESS binding.
        action.addProperty("location", "FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.<JsonObject>emptyList());
        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertEquals("DIRECT_ARRAY_ROOT_REQUIRES_ONE_EXACT_LEAF",
                prepared.getAsJsonArray("materializations").get(0)
                        .getAsJsonObject().get("materializationIssue")
                        .getAsString());
    }

    @Test
    public void uniqueDefinitionFinalizesPendingLocalArrayRoot() {
        String root = "<example.LocalArray: void run()>";
        String localCell = root + "::$r0";
        JsonObject action = exactArrayFieldAction(root);
        action.addProperty("cell", localCell);
        action.addProperty("location", "REGION_LIVE_IN");
        action.add("fieldPath", JsonParser.parseString("[\"values\"]"));
        action.addProperty("consumedFieldBindingComplete", false);
        action.addProperty("consumedFieldSiteBindingComplete", true);
        action.addProperty("consumedFieldBindingIssue",
                "LOCAL_ROOT_DEFINITION_PENDING_SCHEDULER");
        action.addProperty("consumedFieldRootAuthority",
                "LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                        + "SCHEDULER_DEFINITION_INDEX_V1");
        action.addProperty("consumedFieldPendingRootKind",
                "LOCAL_DEFINITION");
        action.addProperty("consumedFieldPendingRootMethod", root);
        action.addProperty("consumedFieldPendingRootLocal", "$r0");
        JsonObject definition = JsonParser.parseString("{"
                + "\"fromCell\":\"source\","
                + "\"toCell\":\"" + localCell + "\","
                + "\"method\":\"" + root + "\","
                + "\"unitIndex\":3,\"unit\":\"$r0 = source\"}")
                .getAsJsonObject();

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.singletonList(definition));
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertEquals("LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_"
                        + "AND_LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                binding.get("consumedFieldRootAuthority").getAsString());
        assertEquals("AUTHORITATIVE_UNIQUE_STATIC_DEFINITION_SITE_V1",
                binding.get("consumedFieldRootResolutionAuthority")
                        .getAsString());
        assertEquals(3, binding.getAsJsonArray("definitionSites").get(0)
                .getAsJsonObject().get("unitIndex").getAsInt());
    }

    @Test
    public void uniqueCallReturnDefinitionFinalizesPendingArrayRoot() {
        String root = "<example.CallReturnArray: void run()>";
        String returned = "<example.ArraySource: example.Value[] read()>"
                + ".return";
        JsonObject action = pendingArrayCallReturnAction(root, returned);
        JsonObject definition = callReturnDefinition(returned, root,
                "$r0", 4);

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Collections.singletonList(definition));
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertTrue(prepared.get("materializationComplete").getAsBoolean());
        assertEquals(1, prepared.getAsJsonArray("materializations").size());
        assertEquals("LOCAL_DEFINITION",
                binding.get("bindingMode").getAsString());
        assertEquals("LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_"
                        + "AND_LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                binding.get("consumedFieldRootAuthority").getAsString());
        assertEquals("AUTHORITATIVE_UNIQUE_STATIC_DEFINITION_SITE_V1",
                binding.get("consumedFieldRootResolutionAuthority")
                        .getAsString());
        assertEquals(4, binding.getAsJsonArray("definitionSites").get(0)
                .getAsJsonObject().get("unitIndex").getAsInt());
    }

    @Test
    public void multipleCallReturnDefinitionsCannotClaimUniqueArrayRoot() {
        String root = "<example.CallReturnArray: void run()>";
        String returned = "<example.ArraySource: example.Value[] read()>"
                + ".return";
        JsonObject action = pendingArrayCallReturnAction(root, returned);
        JsonObject first = callReturnDefinition(returned, root, "$r0", 4);
        JsonObject second = callReturnDefinition(returned, root, "$r1", 9);

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                java.util.Arrays.asList(first, second));
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();

        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertFalse(prepared.get("materializationComplete").getAsBoolean());
        assertEquals(1, prepared.getAsJsonArray("materializations").size());
        assertEquals("UNRESOLVED_CALL_RETURN_DEFINITION",
                binding.get("bindingMode").getAsString());
        assertEquals(2, binding.getAsJsonArray("definitionSites").size());
        assertEquals("ARRAY_CALL_RETURN_ROOT_REQUIRES_ONE_EXACT_"
                        + "FILTERED_RETURN_SITE:2",
                binding.get("materializationIssue").getAsString());
        assertFalse(binding.has("consumedFieldRootResolutionAuthority"));
    }

    @Test
    public void ordinaryCallReturnStillExpandsMultipleExactDefinitions() {
        String root = "<example.CallReturnScalar: void run()>";
        String returned = "<example.ScalarSource: int read()>.return";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.SCALAR.in.0");
        action.addProperty("cell", returned);
        action.addProperty("javaType", "int");
        action.addProperty("location", "CALL_RETURN");
        JsonObject activation = arrayFieldCaptureActivation(action);
        JsonObject first = callReturnDefinition(returned, root, "$i0", 2);
        JsonObject second = callReturnDefinition(returned, root, "$i1", 6);

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation, java.util.Arrays.asList(first, second));

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertTrue(prepared.get("materializationComplete").getAsBoolean());
        assertEquals(2, prepared.getAsJsonArray("materializations").size());
        assertEquals("LOCAL_DEFINITION", prepared
                .getAsJsonArray("materializations").get(0)
                .getAsJsonObject().get("bindingMode").getAsString());
        assertEquals("LOCAL_DEFINITION", prepared
                .getAsJsonArray("materializations").get(1)
                .getAsJsonObject().get("bindingMode").getAsString());
    }

    private static JsonObject arrayFieldCaptureActivation(JsonObject action) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.ARRAY.FIELD");
        activation.addProperty("regionId", "REGION.ARRAY");
        activation.addProperty("requestedOutputSliceComplete", true);
        JsonArray symbolize = new JsonArray();
        symbolize.add(action);
        activation.add("symbolize", symbolize);
        return activation;
    }

    private static JsonObject exactArrayFieldAction(String method) {
        String signature =
                "<example.ArrayState: example.Value[] values>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.ARRAY.in.0");
        action.addProperty("cell", signature);
        action.addProperty("field", signature);
        action.addProperty("javaType", "example.Value[]");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("consumedFieldBindingComplete", true);
        action.addProperty("consumedFieldMethod", method);
        action.addProperty("consumedFieldUnitIndex", 7);
        action.addProperty("consumedFieldSiteId", method + "#u7");
        action.addProperty("consumedFieldSiteAuthority",
                "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                        + "OWNER_WITHIN_REGION_INSTANCE_V1");
        action.addProperty("consumedFieldRootAuthority",
                "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1");
        action.addProperty("consumedFieldOccurrence", 1);
        action.addProperty("consumedFieldOccurrenceAuthority",
                "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
        return action;
    }

    private static JsonObject pendingArrayCallReturnAction(
            String method, String returned) {
        JsonObject action = exactArrayFieldAction(method);
        action.addProperty("cell", returned);
        action.addProperty("location", "CALL_RETURN");
        action.add("fieldPath", JsonParser.parseString("[\"values\"]"));
        action.addProperty("consumedFieldBindingComplete", false);
        action.addProperty("consumedFieldSiteBindingComplete", true);
        action.addProperty("consumedFieldBindingIssue",
                "LOCAL_ROOT_DEFINITION_PENDING_SCHEDULER");
        action.addProperty("consumedFieldRootAuthority",
                "LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                        + "SCHEDULER_DEFINITION_INDEX_V1");
        action.addProperty("consumedFieldPendingRootKind",
                "CALL_RETURN_DEFINITION");
        return action;
    }

    private static JsonObject callReturnDefinition(String returned,
                                                   String method,
                                                   String local,
                                                   int unitIndex) {
        JsonObject definition = new JsonObject();
        definition.addProperty("fromCell", returned);
        definition.addProperty("toCell", method + "::" + local);
        definition.addProperty("method", method);
        definition.addProperty("unitIndex", unitIndex);
        definition.addProperty("siteId", method + "#u" + unitIndex);
        definition.addProperty("unit", local + " = source()");
        return definition;
    }

    @Test
    public void negateHandlesPrimitiveComparisonOperators() {
        JsonObject condition = JsonParser.parseString(
                "{\"_type\":\"BinaryExpression\",\"_op\":\"<\"}")
                .getAsJsonObject();
        assertEquals(">=", ConcolicScheduler.negate(condition)
                .getAsJsonObject().get("_op").getAsString());
    }

    @Test
    public void freshObservedQueryRebuildsFormulaAndExactNestedContext() {
        FreshFixture fixture = freshFixture();

        ConcolicScheduler.FreshTargetQueryResult result =
                ConcolicScheduler.rebuildFreshObservedTargetQuery(
                        fixture.regions, fixture.activations, fixture.edges,
                        fixture.template, fixture.target,
                        fixture.summary, "EXEC.NEW");

        assertTrue(result.reason, result.ready);
        assertEquals(3, result.admission.get("selectedBindingCount")
                .getAsInt());
        JsonObject query = result.query;
        assertEquals("KEEP_FRESH_OBSERVED_DESIRED_TARGET_CONDITION",
                query.get("targetPolicy").getAsString());
        assertEquals("==", query.getAsJsonArray("constraints").get(1)
                .getAsJsonObject().get("_op").getAsString());
        assertEquals("==", query.getAsJsonObject(
                "freshObservedTargetCondition").get("_op").getAsString());
        assertEquals("!=", query.getAsJsonObject(
                "originalTargetCondition").get("_op").getAsString());
        assertFalse(query.has("semanticModel"));
        assertFalse(query.has("replayMaterializations"));
        assertEquals("ENGINE.NEW", query.getAsJsonArray(
                "engineArrayInputBindings").get(0).getAsJsonObject()
                .get("engineArrayId").getAsString());

        JsonObject context = query.getAsJsonObject("symbolicContext");
        JsonObject equality = context.getAsJsonArray("equalityRelations")
                .get(0).getAsJsonObject();
        JsonObject equalityBinding = equality.getAsJsonArray(
                "selectedBindings").get(0).getAsJsonObject();
        assertEquals("A.NEW", equalityBinding.get(
                "fromRegionInstance").getAsString());
        assertEquals("T.NEW", equalityBinding.get(
                "toRegionInstance").getAsString());
        JsonObject alternatives = context.getAsJsonArray(
                "alternativeWriterGroups").get(0).getAsJsonObject();
        assertEquals(2, alternatives.getAsJsonArray("alternatives").size());
        for (int index = 0; index < 2; index++) {
            JsonObject selected = alternatives.getAsJsonArray(
                    "alternatives").get(index).getAsJsonObject()
                    .getAsJsonArray("selectedBindings").get(0)
                    .getAsJsonObject();
            assertEquals("T.NEW", selected.get("toRegionInstance")
                    .getAsString());
            assertFalse(selected.get("fromRegionInstance").getAsString()
                    .endsWith(".OLD"));
        }
    }

    @Test
    public void freshObservedQueryRejectsOtherEndpointFromOldExecution() {
        FreshFixture fixture = freshFixture();
        fixture.upstreamA.addProperty("discoveredExecutionId", "EXEC.OLD");

        ConcolicScheduler.FreshTargetQueryResult result =
                ConcolicScheduler.rebuildFreshObservedTargetQuery(
                        fixture.regions, fixture.activations, fixture.edges,
                        fixture.template, fixture.target,
                        fixture.summary, "EXEC.NEW");

        assertFalse(result.ready);
        assertEquals("FRESH_TARGET_SYMBOLIC_CONTEXT_ENDPOINT_INVALID",
                result.reason);
        assertTrue(result.admission.getAsJsonArray("contextGaps")
                .toString().contains(
                        "ENDPOINT_TRANSITION_EXECUTION_NOT_ATTESTED"));
    }

    @Test
    public void freshObservedQueryRejectsMappedConditionMismatchAndEmptyContext() {
        FreshFixture mismatch = freshFixture();
        mismatch.summary.getAsJsonArray("branchMappings").get(0)
                .getAsJsonObject().getAsJsonObject("condition")
                .addProperty("_op", "!=");
        ConcolicScheduler.FreshTargetQueryResult mismatched =
                ConcolicScheduler.rebuildFreshObservedTargetQuery(
                        mismatch.regions, mismatch.activations,
                        mismatch.edges, mismatch.template, mismatch.target,
                        mismatch.summary, "EXEC.NEW");
        assertFalse(mismatched.ready);
        assertEquals("FRESH_TARGET_MAPPING_CONDITION_PATH_MISMATCH",
                mismatched.reason);

        FreshFixture empty = freshFixture();
        ConcolicScheduler.FreshTargetQueryResult noContext =
                ConcolicScheduler.rebuildFreshObservedTargetQuery(
                        empty.regions, empty.activations,
                        Collections.<JsonObject>emptyList(), empty.template,
                        empty.target, empty.summary, "EXEC.NEW");
        assertFalse(noContext.ready);
        assertEquals("FRESH_TARGET_SYMBOLIC_CONTEXT_EMPTY",
                noContext.reason);
    }

    @Test
    public void scheduleUsesFreshObservedRebuildForTargetObservation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            FreshFixture fixture = freshFixture();
            fixture.target.addProperty("replayable", true);
            fixture.target.addProperty("rootMethod", "<T: void fail()>");
            fixture.target.addProperty("test", "fresh-test");
            fixture.target.addProperty("targetObservationOnly", true);
            fixture.target.addProperty("targetRebaseAuthority",
                    "FRESH_INSTANCE_UPSTREAM_SUPPORT_TARGET_OBSERVATION");
            fixture.target.addProperty("targetRebaseSourceExecutionId",
                    "EXEC.NEW");
            fixture.target.addProperty("replacesTargetActivationId",
                    "ACT.T.OLD");
            fixture.target.addProperty("replacesTargetRegionInstanceId",
                    "T.OLD");
            fixture.target.add("directedTargetQuery",
                    fixture.template.deepCopy());
            RegionCaptureGoal.targetBranch().writeTo(fixture.target);
            ConcolicScheduler.FreshTargetQueryResult campaignRebuild =
                    ConcolicScheduler.rebuildFreshObservedTargetQuery(
                            fixture.regions, fixture.activations,
                            fixture.edges, fixture.template, fixture.target,
                            fixture.summary, "EXEC.NEW");
            assertTrue(campaignRebuild.reason, campaignRebuild.ready);
            fixture.summary.add("freshObservedTargetQuery",
                    campaignRebuild.query.deepCopy());
            JsonObject summaryAdmission = new JsonObject();
            summaryAdmission.addProperty("authority",
                    "FRESH_SUMMARY_PATH_AND_CURRENT_RUNTIME_EDGE_LEDGER");
            summaryAdmission.addProperty("sourceSummaryId",
                    "SUMMARY.T.NEW");
            summaryAdmission.addProperty("targetReplayExecutionId",
                    "EXEC.REPLAY");
            summaryAdmission.addProperty("derivedQuerySha256",
                    "sha256:fixture");
            summaryAdmission.addProperty("edgeAuthority",
                    "CURRENT_EDGE_LEDGER_EXACT_TARGET_ENDPOINT_INSTANCE");
            summaryAdmission.addProperty(
                    "upstreamReachabilitySupportCount", 2);
            summaryAdmission.addProperty("downstreamInjectionUsed", false);
            fixture.summary.add("freshTargetSummaryAdmission",
                    summaryAdmission);

            Path root = folder.getRoot().toPath();
            Path regions = root.resolve("regions.jsonl");
            Path activations = root.resolve("activations.jsonl");
            Path edges = root.resolve("edges.jsonl");
            Path summaries = root.resolve("summaries.jsonl");
            writeRows(regions, fixture.regions);
            writeRows(activations, fixture.activations);
            writeRows(edges, fixture.edges);
            writeRows(summaries, Collections.singletonList(fixture.summary));

            ConcolicScheduler.Result scheduled = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", regions.toString(),
                            "--activation-plan", activations.toString(),
                            "--edge-validations", edges.toString(),
                            "--summaries", summaries.toString(),
                            "--output-dir", root.resolve("out").toString(),
                            "--activation-id", "ACT.T.NEW"}));

            assertEquals(1, scheduled.queries.size());
            JsonObject query = scheduled.queries.get(0);
            assertTrue(query.get("readyForSolver").getAsBoolean());
            assertTrue(query.get("replayAlreadyValidated").getAsBoolean());
            assertEquals("SUMMARY.T.NEW",
                    query.get("validatedSummaryId").getAsString());
            assertEquals("FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_"
                            + "UNFORCED_TARGET_REPLAY",
                    query.get("replayValidationAuthority").getAsString());
            assertEquals("SUMMARY.T.NEW", query.getAsJsonObject(
                    "validatedTargetSummary").get("summaryId").getAsString());
            assertEquals("ACT.T.OLD", query.getAsJsonObject(
                    "targetRebaseProvenance").get("replacesActivationId")
                    .getAsString());
            assertEquals("FRESH_INSTANCE_IMPORTED_UNFORCED_TARGET_PREFIX_"
                            + "PLUS_OBSERVED_TARGET",
                    query.get("formulaAuthority").getAsString());
            assertEquals("T.NEW", query.getAsJsonObject("symbolicContext")
                    .get("regionInstanceId").getAsString());
            assertFalse(query.getAsJsonArray("constraints").toString()
                    .contains("T.OLD"));
            assertFalse(query.getAsJsonObject("symbolicContext").toString()
                    .contains("T.OLD"));
            assertEquals("TARGET_REPLAY_VALIDATED", scheduled.jobs.get(0)
                    .get("phase").getAsString());

            Path composed = root.resolve("composed.smt2");
            Path manifest = root.resolve("composed-manifest.json");
            Path relationships = root.resolve("relationships.json");
            ConcolicSmtComposer.Result handoff = ConcolicSmtComposer.compose(
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", root.resolve("out")
                            .resolve("branch_queries.jsonl").toString(),
                            "--summaries", summaries.toString(),
                            "--regions", regions.toString(),
                            "--merge-plan", root.resolve("out")
                            .resolve("symbolic_merge_plan.json").toString(),
                            "--output", composed.toString(),
                            "--manifest", manifest.toString(),
                            "--relationships", relationships.toString(),
                            "--fatal-region", "REGION.T",
                            "--activation-id", "ACT.T.NEW"}));
            assertTrue(handoff.manifest.toString(), handoff.manifest.get(
                    "fatalReplayValidated").getAsBoolean());
            assertEquals("SUMMARY.T.NEW", handoff.manifest.get(
                    "validatedFatalReplaySummary").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void freshScheduleRejectsUnenrichedSummaryWithoutAuthorityDowngrade()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            FreshFixture fixture = freshFixture();
            fixture.target.addProperty("replayable", true);
            fixture.target.addProperty("rootMethod", "<T: void fail()>");
            fixture.target.addProperty("test", "fresh-test");
            fixture.target.addProperty("targetObservationOnly", true);
            fixture.target.addProperty("targetRebaseAuthority",
                    "FRESH_INSTANCE_UPSTREAM_SUPPORT_TARGET_OBSERVATION");
            fixture.target.addProperty("targetRebaseSourceExecutionId",
                    "EXEC.NEW");
            fixture.target.addProperty("replacesTargetActivationId",
                    "ACT.T.OLD");
            fixture.target.addProperty("replacesTargetRegionInstanceId",
                    "T.OLD");
            fixture.target.add("directedTargetQuery",
                    fixture.template.deepCopy());
            RegionCaptureGoal.targetBranch().writeTo(fixture.target);
            Path root = folder.getRoot().toPath();
            Path regions = root.resolve("regions.jsonl");
            Path activations = root.resolve("activations.jsonl");
            Path edges = root.resolve("edges.jsonl");
            Path summaries = root.resolve("summaries.jsonl");
            writeRows(regions, fixture.regions);
            writeRows(activations, fixture.activations);
            writeRows(edges, fixture.edges);
            writeRows(summaries, Collections.singletonList(fixture.summary));

            ConcolicScheduler.Result scheduled = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", regions.toString(),
                            "--activation-plan", activations.toString(),
                            "--edge-validations", edges.toString(),
                            "--summaries", summaries.toString(),
                            "--output-dir", root.resolve("out").toString(),
                            "--activation-id", "ACT.T.NEW"}));

            JsonObject query = scheduled.queries.get(0);
            assertFalse(query.get("readyForSolver").getAsBoolean());
            assertFalse(query.get("replayAlreadyValidated").getAsBoolean());
            assertEquals("NONE", query.get("replayValidationAuthority")
                    .getAsString());
            assertEquals("FRESH_SCHEDULE_SUMMARY_QUERY_MISSING",
                    query.get("blocker").getAsString());
            assertFalse(query.toString().contains(
                    "SAME_INSTANCE_IMPORTED_UNFORCED_TARGET_REPLAY"));
            assertFalse(scheduled.jobs.get(0).has(
                    "targetReplayAlreadyValidated"));
        } finally {
            folder.delete();
        }
    }

    private static void writeRows(Path path, List<JsonObject> rows)
            throws Exception {
        StringBuilder content = new StringBuilder();
        for (JsonObject row : rows) content.append(row).append('\n');
        Files.write(path, content.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static FreshFixture freshFixture() {
        JsonObject upstreamA = region("REGION.A", "REGION.A.out.0",
                "A_CELL", false);
        JsonObject upstreamB = region("REGION.B", "REGION.B.out.0",
                "B_CELL", false);
        JsonObject targetRegion = region("REGION.T", "REGION.T.in.0",
                "T_CELL", true);

        JsonObject oldA = activation("ACT.A.OLD", "REGION.A", "A.OLD",
                "EXEC.OLD");
        JsonObject oldB = activation("ACT.B.OLD", "REGION.B", "B.OLD",
                "EXEC.OLD");
        JsonObject oldTarget = activation("ACT.T.OLD", "REGION.T",
                "T.OLD", "EXEC.OLD");
        JsonObject freshA = activation("ACT.A.NEW", "REGION.A", "A.NEW",
                "EXEC.NEW");
        JsonObject freshB = activation("ACT.B.NEW", "REGION.B", "B.NEW",
                "EXEC.NEW");
        JsonObject freshTarget = activation("ACT.T.NEW", "REGION.T",
                "T.NEW", "EXEC.NEW");
        freshTarget.addProperty("postDiscoveryTargetExecutionId",
                "EXEC.NEW");
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId", "T#u7");
        targetBranch.addProperty("occurrence", 1);
        targetBranch.addProperty("desiredOutcome", false);
        freshTarget.add("targetBranch", targetBranch);

        JsonObject template = new JsonObject();
        template.addProperty("activationId", "ACT.T.OLD");
        template.addProperty("regionId", "REGION.T");
        template.addProperty("regionInstanceId", "T.OLD");
        template.addProperty("siteId", "T#u7");
        template.addProperty("occurrence", 1);
        template.addProperty("desiredOutcome", false);

        JsonObject prefix = condition(">");
        JsonObject observed = condition("==");
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.T.NEW");
        summary.addProperty("activationId", "ACT.T.NEW");
        summary.addProperty("regionId", "REGION.T");
        summary.addProperty("regionInstanceId", "T.NEW");
        summary.addProperty("valid", true);
        summary.addProperty("targetReplayValidated", true);
        summary.addProperty("branchOverrideUsed", false);
        summary.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        JsonObject replayAdmission = new JsonObject();
        replayAdmission.addProperty("required", true);
        replayAdmission.addProperty("valid", true);
        replayAdmission.addProperty("branchOverrideAccepted", false);
        replayAdmission.addProperty("authority",
                "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION");
        summary.add("executionAdmission", replayAdmission);
        JsonArray path = new JsonArray();
        path.add(prefix);
        path.add(observed);
        summary.add("pathCondition", path);
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", "T#u7");
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("conditionIndex", 1);
        mapping.addProperty("observedOutcome", false);
        mapping.addProperty("overrideApplied", false);
        mapping.add("condition", observed.deepCopy());
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        summary.add("branchMappings", mappings);
        JsonObject engine = new JsonObject();
        engine.addProperty("engineArrayId", "ENGINE.NEW");
        JsonArray engines = new JsonArray();
        engines.add(engine);
        summary.add("engineArrayInputBindings", engines);

        JsonObject equality = edge("EDGE.EQ", "EQUALITY", "REGION.A",
                "A_CELL", "REGION.T", "T_CELL");
        JsonArray equalityBindings = new JsonArray();
        equalityBindings.add(equalityBinding("A.OLD", "T.OLD"));
        equalityBindings.add(equalityBinding("A.NEW", "T.NEW"));
        equality.add("validatedBindings", equalityBindings);
        JsonObject heapA = edge("EDGE.HEAP.A", "READ_FROM", "REGION.A",
                "A_CELL", "REGION.T", "T_CELL");
        JsonArray heapABindings = new JsonArray();
        heapABindings.add(heapBinding("A.OLD", "T.OLD", 1));
        heapABindings.add(heapBinding("A.NEW", "T.NEW", 2));
        heapA.add("validatedBindings", heapABindings);
        JsonObject heapB = edge("EDGE.HEAP.B", "READ_FROM", "REGION.B",
                "B_CELL", "REGION.T", "T_CELL");
        // Exercise fallback endpoint parsing: REGION.B::REGION.B.out.0 must
        // still belong to REGION.B, not REGION.B::REGION.B.
        heapB.addProperty("fromPort", "REGION.B.out.0");
        JsonArray heapBBindings = new JsonArray();
        heapBBindings.add(heapBinding("B.OLD", "T.OLD", 3));
        heapBBindings.add(heapBinding("B.NEW", "T.NEW", 4));
        heapB.add("validatedBindings", heapBBindings);

        return new FreshFixture(Arrays.asList(upstreamA, upstreamB,
                targetRegion), Arrays.asList(oldA, oldB, oldTarget, freshA,
                freshB, freshTarget), Arrays.asList(equality, heapA, heapB),
                template, freshTarget, freshA, summary);
    }

    private static JsonObject region(String id, String port, String cell,
                                     boolean input) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", id);
        JsonObject value = new JsonObject();
        value.addProperty("portId", port);
        value.addProperty("cell", cell);
        JsonArray values = new JsonArray();
        values.add(value);
        result.add(input ? "symbolicInputs" : "outputs", values);
        return result;
    }

    private static JsonObject activation(String id, String region,
                                         String instance,
                                         String execution) {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", id);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", instance);
        result.addProperty("discoveredExecutionId", execution);
        return result;
    }

    private static JsonObject edge(String id, String relation,
                                   String fromRegion, String fromCell,
                                   String toRegion, String toCell) {
        JsonObject result = new JsonObject();
        result.addProperty("edgeId", id);
        result.addProperty("fromRegion", fromRegion);
        result.addProperty("fromPort", fromCell);
        result.addProperty("toRegion", toRegion);
        result.addProperty("toPort", toCell);
        result.addProperty("validatedRelation", relation);
        result.addProperty("status", "READ_FROM".equals(relation)
                ? "CONFIRMED_READ_FROM"
                : "CONFIRMED_RUNTIME_VALUE_EQUALITY");
        result.addProperty("composable", true);
        result.addProperty("eligibleForAutomaticDerivation", true);
        result.addProperty("eligibleForAutomaticSmt", true);
        result.addProperty("confirmedReadFromPairCount", 2);
        result.addProperty("confirmedValueEqualityPairCount", 2);
        if ("EQUALITY".equals(relation)) {
            result.addProperty("valueEqualityObserved", true);
            result.addProperty("valueEqualityAuthority",
                    "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        } else {
            result.addProperty("requiresOrder", true);
            result.addProperty("requiresObjectIdentity", true);
        }
        JsonArray executions = new JsonArray();
        executions.add("EXEC.OLD");
        executions.add("EXEC.NEW");
        result.add("discoveredExecutionIds", executions);
        return result;
    }

    private static JsonObject equalityBinding(String from, String to) {
        JsonObject result = new JsonObject();
        result.addProperty("fromRegionInstance", from);
        result.addProperty("toRegionInstance", to);
        result.addProperty("valueEqualityObserved", true);
        result.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        result.addProperty("valueFingerprint", "sha256:" + from + ":" + to);
        return result;
    }

    private static JsonObject heapBinding(String from, String to,
                                          int receiver) {
        JsonObject result = new JsonObject();
        result.addProperty("fromRegionInstance", from);
        result.addProperty("toRegionInstance", to);
        result.addProperty("writeSeq", receiver * 10);
        result.addProperty("readSeq", receiver * 10 + 1);
        result.addProperty("receiverObjectId", receiver);
        return result;
    }

    private static JsonObject condition(String operator) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", operator);
        return result;
    }

    private static final class FreshFixture {
        private final List<JsonObject> regions;
        private final List<JsonObject> activations;
        private final List<JsonObject> edges;
        private final JsonObject template;
        private final JsonObject target;
        private final JsonObject upstreamA;
        private final JsonObject summary;

        private FreshFixture(List<JsonObject> regions,
                             List<JsonObject> activations,
                             List<JsonObject> edges,
                             JsonObject template, JsonObject target,
                             JsonObject upstreamA, JsonObject summary) {
            this.regions = regions;
            this.activations = activations;
            this.edges = edges;
            this.template = template;
            this.target = target;
            this.upstreamA = upstreamA;
            this.summary = summary;
        }
    }

    private static Fixture fixture(Path root, boolean includeSummary)
            throws Exception {
        Fixture result = new Fixture(root);
        String regions = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                + ROOT + "\",\"symbolicInputs\":["
                + "{\"portId\":\"REGION.0.in.0\",\"cell\":\""
                + USERNAME + "\"},"
                + "{\"portId\":\"REGION.0.in.1\",\"cell\":\""
                + ALL_KEYS + "\"},"
                + "{\"portId\":\"REGION.0.in.2\",\"cell\":\""
                + CURRENT_KEY_ID + "\"}],\"outputs\":[]}\n"
                + "{\"regionId\":\"REGION.1\",\"rootMethod\":"
                + "\"<example.Client: void send()>\",\"symbolicInputs\":[],"
                + "\"outputs\":[{\"portId\":\"REGION.1.out.0\","
                + "\"cell\":\"client.userName\"}]}\n"
                + "{\"regionId\":\"REGION.11\",\"rootMethod\":"
                + "\"<example.Updater: void run()>\",\"symbolicInputs\":[],"
                + "\"outputs\":[{\"portId\":\"REGION.11.out.0\","
                + "\"cell\":\"" + ALL_KEYS + "\"}]}\n";
        Files.write(result.regions, regions.getBytes(StandardCharsets.UTF_8));

        String activation = "{\"activationId\":\"ACT.0\","
                + "\"regionId\":\"REGION.0\","
                + "\"regionInstanceId\":\"REGION.0@testMiniDfs#call7\","
                + "\"rootCallId\":7,\"test\":\"testMiniDfs\","
                + "\"rootMethod\":\"" + ROOT + "\","
                + "\"receiverType\":\"example.Server\","
                + "\"receiverRuntimeClass\":\"example.Server\","
                + "\"threadName\":\"rpc-handler\","
                + "\"threadIdSelectionUsed\":false,"
                + "\"invocationOrdinalWithinContext\":1,"
                + "\"rootContextSelectionAuthority\":"
                + "\"TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                + "THREAD_NAME_CONTEXT_ORDINAL_V1\","
                + "\"invocationOrdinal\":1,\"replayable\":true,"
                + "\"symbolicReady\":false,\"symbolize\":["
                + "{\"symbol\":\"REGION.0.in.0\",\"cell\":\""
                + USERNAME + "\",\"location\":\"REGION_LIVE_IN\"},"
                + "{\"symbol\":\"REGION.0.in.1\",\"cell\":\""
                + ALL_KEYS + "\",\"location\":\"HEAP_OBJECT_FIELD\"},"
                + "{\"symbol\":\"REGION.0.in.2\",\"cell\":\""
                + CURRENT_KEY_ID
                + "\",\"location\":\"HEAP_OBJECT_FIELD\"}],"
                + "\"branches\":[{\"siteId\":\"" + TARGET + "\","
                + "\"policy\":\"PATH_ASSUMPTION\",\"observed\":true,"
                + "\"observedOutcome\":true,\"requiredOutcome\":false,"
                + "\"matchesRequiredOutcome\":false,"
                + "\"selectedOccurrence\":1,\"occurrences\":["
                + "{\"occurrence\":1,\"seq\":8,\"outcome\":true,"
                + "\"matchesRequiredOutcome\":false}]}]}\n";
        Files.write(result.activations,
                activation.getBytes(StandardCharsets.UTF_8));

        String edges = "{\"edgeId\":\"E.SASL\","
                + "\"fromRegion\":\"REGION.1\","
                + "\"toRegion\":\"REGION.0\","
                + "\"fromPort\":\"client.userName\","
                + "\"toPort\":\"" + USERNAME + "\","
                + "\"kind\":\"SASL_TRANSFER\","
                + "\"validatedRelation\":\"EQUALITY\","
                + "\"status\":\"CONFIRMED_RUNTIME_VALUE_EQUALITY\","
                + "\"valueEqualityObserved\":true,"
                + "\"confirmedValueEqualityPairCount\":1,"
                + "\"valueEqualityAuthority\":"
                + "\"RUNTIME_COMPLETE_VALUE_FINGERPRINT\","
                + "\"eligibleForAutomaticDerivation\":true,"
                + "\"eligibleForAutomaticSmt\":true,"
                + "\"composable\":true,\"evidence\":[{"
                + "\"valueEqualityObserved\":true,"
                + "\"valueEqualityAuthority\":"
                + "\"RUNTIME_COMPLETE_VALUE_FINGERPRINT\","
                + "\"valueFingerprint\":\"sha256:fixture\"}]}\n"
                + "{\"edgeId\":\"E.STATE\","
                + "\"fromRegion\":\"REGION.11\","
                + "\"toRegion\":\"REGION.0\","
                + "\"fromPort\":\"" + ALL_KEYS + "\","
                + "\"toPort\":\"" + ALL_KEYS + "\","
                + "\"kind\":\"SHARED_STATE\","
                + "\"validatedRelation\":\"READ_FROM\","
                + "\"requiresOrder\":true,"
                + "\"requiresObjectIdentity\":true,"
                + "\"confirmedReadFromPairCount\":1,"
                + "\"status\":\"CONFIRMED_READ_FROM\","
                + "\"eligibleForAutomaticDerivation\":true,"
                + "\"eligibleForAutomaticSmt\":true,"
                + "\"composable\":true,\"evidence\":[{"
                + "\"writeSeq\":1,\"readSeq\":2,"
                + "\"receiverObjectId\":7,"
                + "\"orderConfirmed\":true}]}\n";
        Files.write(result.edges, edges.getBytes(StandardCharsets.UTF_8));

        String staticGraph = "{\"id\":\"DF.DEF\",\"toCell\":\""
                + USERNAME + "\",\"method\":\"" + CALLBACK
                + "\",\"unitIndex\":36,\"unit\":\"$r4 = "
                + "virtualinvoke r12.<javax.security.auth.callback.NameCallback: "
                + "java.lang.String getDefaultName()>()\"}\n"
                + "{\"id\":\"DF.MAP\",\"kind\":\"map_lookup_state\","
                + "\"method\":\""
                + "<example.Manager: byte[] lookup(int)>\","
                + "\"unitIndex\":6,\"siteId\":\""
                + "<example.Manager: byte[] lookup(int)>#u6\","
                + "\"invoke\":\"<java.util.Map: java.lang.Object "
                + "get(java.lang.Object)>\",\"unit\":\"$r3 = "
                + "interfaceinvoke $r1.<java.util.Map: java.lang.Object "
                + "get(java.lang.Object)>($r2)\"}\n";
        Files.write(result.staticGraph,
                staticGraph.getBytes(StandardCharsets.UTF_8));

        if (includeSummary) {
            String summary = "{\"summaryId\":\"SUMMARY.REGION.0.SEED\","
                    + "\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\","
                    + "\"regionInstanceId\":"
                    + "\"REGION.0@testMiniDfs#call7\","
                    + "\"captureGoal\":{\"kind\":\"TARGET_BRANCH\","
                    + "\"scope\":\"ONE_DIRECTED_BRANCH\"},"
                    + "\"valid\":true,\"targetReplayValidated\":false,"
                    + "\"branchOverrideUsed\":false,"
                    + "\"executionAdmission\":{\"required\":false,"
                    + "\"valid\":true,\"branchOverrideAccepted\":false,"
                    + "\"authority\":"
                    + "\"OBSERVED_UNFORCED_TARGET_SEED_PATH_ONLY\"},"
                    + "\"pathCondition\":["
                    + "{\"_type\":\"BinaryExpression\",\"_op\":\">\"},"
                    + "{\"_type\":\"MethodExpression\","
                    + "\"_name\":\"java/util/HashMap get\","
                    + "\"_param_list\":[{\"_type\":\"SymbolExpression\","
                    + "\"_exp\":\"MAP\"},{\"_type\":\"SymbolExpression\","
                    + "\"_exp\":\"KEY\"}],\"_res_exp\":{"
                    + "\"_type\":\"SymbolExpression\",\"_exp\":\"RESULT\"}},"
                    + "{\"_type\":\"BinaryExpression\",\"_op\":\"!=\","
                    + "\"_left\":{\"_type\":\"SymbolExpression\","
                    + "\"_exp\":\"RESULT\"},\"_right\":{"
                    + "\"_type\":\"SymbolExpression\",\"_exp\":\"N\"}},"
                    + "{\"_type\":\"BinaryExpression\",\"_op\":\"==\"}],"
                    + "\"branchMappings\":[{\"siteId\":\"" + TARGET
                    + "\",\"conditionIndex\":2}]}\n";
            Files.write(result.summaries,
                    summary.getBytes(StandardCharsets.UTF_8));
        }
        return result;
    }

    private static final class Fixture {
        private final Path regions;
        private final Path activations;
        private final Path edges;
        private final Path staticGraph;
        private final Path summaries;
        private final Path output;

        private Fixture(Path root) {
            this.regions = root.resolve("regions.jsonl");
            this.activations = root.resolve("activations.jsonl");
            this.edges = root.resolve("edges.jsonl");
            this.staticGraph = root.resolve("static.jsonl");
            this.summaries = root.resolve("summaries.jsonl");
            this.output = root.resolve("schedule");
        }
    }
}
