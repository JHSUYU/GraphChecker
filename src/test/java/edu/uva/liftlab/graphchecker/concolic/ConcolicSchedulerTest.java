package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
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
import static org.junit.Assert.fail;

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
            JsonObject target = job.getAsJsonObject(
                    "branchCaptureSelector");
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
    public void runtimeDefinitionMethodsMustBeExplicitStringArray()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject activation = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.activations),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            activation.remove("runtimeDefinitionMethods");
            JsonArray observed = new JsonArray();
            observed.add(CALLBACK);
            activation.add("observedMethods", observed);
            Files.write(fixture.activations, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0"});
            try {
                ConcolicScheduler.schedule(arguments);
                fail("observedMethods must not replace canonical runtime definitions");
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage().contains(
                        "runtimeDefinitionMethods array"));
            }

            JsonArray malformed = new JsonArray();
            malformed.add(7);
            activation.add("runtimeDefinitionMethods", malformed);
            Files.write(fixture.activations, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));
            try {
                ConcolicScheduler.schedule(arguments);
                fail("numeric runtime method must fail closed");
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage().contains(
                        "non-string value"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergePlanUsesProvenCanonicalProducerOutputInsteadOfTransport()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String returnCell =
                    "<example.Client: java.lang.String compute()>#return";
            String canonicalInput =
                    "<javax.security.auth.callback.NameCallback: "
                            + "java.lang.String defaultName>";
            String regions = new String(Files.readAllBytes(fixture.regions),
                    StandardCharsets.UTF_8);
            String rawInput = "{\"portId\":\"REGION.0.in.0\",\"cell\":\""
                    + USERNAME + "\"}";
            assertTrue(regions.contains(rawInput));
            regions = regions.replace(rawInput,
                    "{\"portId\":\"REGION.0.in.0\",\"cell\":\""
                            + canonicalInput + "\"}");
            String oldOutput = "\"outputs\":[{\"portId\":"
                    + "\"REGION.1.out.0\",\"cell\":"
                    + "\"client.userName\"}]";
            assertTrue(regions.contains(oldOutput));
            regions = regions.replace(oldOutput, "\"outputs\":["
                    + "{\"portId\":\"REGION.1.out.0\","
                    + "\"cell\":\"client.userName\"},"
                    + "{\"portId\":\"REGION.1.out.1\","
                    + "\"cell\":\"" + returnCell + "\"}]");
            Files.write(fixture.regions,
                    regions.getBytes(StandardCharsets.UTF_8));
            String activations = new String(Files.readAllBytes(
                    fixture.activations), StandardCharsets.UTF_8);
            Files.write(fixture.activations, activations.replace(USERNAME,
                    canonicalInput).getBytes(StandardCharsets.UTF_8));

            String staticGraph = new String(Files.readAllBytes(
                    fixture.staticGraph), StandardCharsets.UTF_8)
                    + accessorInputProof("DF.ACCESSOR.UNIQUE",
                    canonicalInput, USERNAME);
            Files.write(fixture.staticGraph,
                    staticGraph.getBytes(StandardCharsets.UTF_8));

            String edges = new String(Files.readAllBytes(fixture.edges),
                    StandardCharsets.UTF_8);
            String rawEndpoints = "\"fromPort\":\"client.userName\","
                    + "\"toPort\":\"" + USERNAME + "\",";
            assertTrue(edges.contains(rawEndpoints));
            edges = edges.replace(rawEndpoints, rawEndpoints
                    + "\"fromOutputPort\":\"REGION.1.out.1\","
                    + "\"fromOutputCell\":\"" + returnCell + "\","
                    + "\"aliasProofEdgeIds\":[\"DF.RETURN_TO_RPC\"],"
                    + "\"aliasProofComplete\":true,"
                    + "\"aliasProofAuthority\":"
                    + "\"CONFIGURED_RPC_PRODUCER_RETURN_AND_STATIC_EXACT_"
                    + "PUBLISH_VALUE_FLOW_V1\",");
            Files.write(fixture.edges,
                    edges.getBytes(StandardCharsets.UTF_8));

            ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.0",
                            "--force-branch-validation", "true"}));

            JsonObject equality = result.mergePlan.getAsJsonArray(
                    "equalityRelations").get(0).getAsJsonObject();
            assertEquals("REGION.1.out.1",
                    equality.get("fromEndpoint").getAsString());
            assertEquals(returnCell, equality.get("fromCell").getAsString());
            assertEquals("REGION.0.in.0",
                    equality.get("toEndpoint").getAsString());
            assertEquals(canonicalInput,
                    equality.get("toCell").getAsString());
            assertEquals(USERNAME,
                    equality.get("rawToCell").getAsString());
            assertEquals("DF.ACCESSOR.UNIQUE", equality.get(
                    "toCanonicalizationProofEdgeId").getAsString());
            assertEquals(ConcolicScheduler
                            .ACCESSOR_INPUT_CANONICALIZATION_AUTHORITY,
                    equality.get("toCanonicalizationAuthority")
                            .getAsString());

            Files.write(fixture.staticGraph, (staticGraph
                    + accessorInputProof("DF.ACCESSOR.AMBIGUOUS",
                    canonicalInput, USERNAME)).getBytes(
                    StandardCharsets.UTF_8));
            ConcolicScheduler.Result ambiguous = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", folder.getRoot().toPath()
                            .resolve("ambiguous-consumer").toString(),
                            "--region-id", "REGION.0",
                            "--force-branch-validation", "true"}));
            JsonObject raw = ambiguous.mergePlan.getAsJsonArray(
                    "equalityRelations").get(0).getAsJsonObject();
            assertEquals("REGION.0::" + USERNAME,
                    raw.get("toEndpoint").getAsString());
            assertEquals(USERNAME, raw.get("toCell").getAsString());
            assertFalse(raw.has("toCanonicalizationProofEdgeId"));

            Files.write(fixture.staticGraph,
                    staticGraph.getBytes(StandardCharsets.UTF_8));

            Files.write(fixture.edges, edges.replace(
                    "\"aliasProofComplete\":true",
                    "\"aliasProofComplete\":false").getBytes(
                    StandardCharsets.UTF_8));
            ConcolicScheduler.Result invalid = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", folder.getRoot().toPath()
                            .resolve("invalid-canonical").toString(),
                            "--region-id", "REGION.0",
                            "--force-branch-validation", "true"}));
            assertEquals(0, invalid.mergePlan.getAsJsonArray(
                    "equalityRelations").size());
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
                    + "\"composable\":true,\"validatedBindings\":[{"
                    + "\"writeEvidenceKind\":\"FIELD_ASSIGNMENT\","
                    + "\"writeEvidenceAuthority\":"
                    + "\"RUNTIME_EXACT_FIELD_WRITE_EVENT_V1\","
                    + "\"orderAuthority\":"
                    + "\"GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1\","
                    + "\"writeSeq\":3,\"readSeq\":4,"
                    + "\"receiverObjectId\":8,"
                    + "\"fieldReceiverIdentityConfirmed\":true,"
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
    public void capturedSummaryProducesCanonicalTargetSolverQuery()
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
            BranchReplayContract contract = BranchReplayContract.fromJson(
                    query.getAsJsonObject("replayContract"));
            assertEquals(TARGET, contract.source().siteId());
            assertEquals(1, contract.orderedPrefix().size());
            assertEquals("==", contract.requiredSatisfiedPredicate()
                    .getAsJsonObject().get("_op").getAsString());
            assertEquals(1, SolverPathContext.fromJson(query
                    .getAsJsonObject("solverPathContext")).size());
            assertFalse(query.has("constraints"));
            assertFalse(query.has("originalTargetCondition"));
            assertFalse(query.has("negatedTargetCondition"));
            assertEquals(BranchReplayContract.DROP_SOURCE_SUFFIX,
                    query.getAsJsonObject("replayContract")
                            .get("suffixPolicy").getAsString());
            assertEquals("REGION.0@testMiniDfs#call7",
                    query.get("regionInstanceId").getAsString());
            assertEquals(bridges, query.getAsJsonArray(
                    "engineArrayInputBindings"));
            assertFalse(result.scheduledActivations.get(0)
                    .has("replayContract"));
            assertTrue(result.scheduledActivations.get(0)
                    .has("branchCaptureSelector"));
            assertFalse(result.scheduledActivations.get(0)
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
                    .has("replayContract"));
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
            assertTrue(result.summary.get("captureOnly").getAsBoolean());
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
                    + "\"runtimeDefinitionMethods\":["
                    + "\"<example.Updater: void run()>\"],"
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
            assertFalse(result.jobs.get(0).has("branchCaptureSelector"));
            assertFalse(result.scheduledActivations.get(0)
                    .has("targetBranch"));
            assertFalse(result.scheduledActivations.get(0)
                    .has("branchCaptureSelector"));
            assertEquals(0, result.queries.size());
            assertEquals(1, result.summary.get("upstreamCaptureJobCount")
                    .getAsInt());

            String observedMapPrestate = activation.replace(
                    "\"symbolize\":[]",
                    "\"symbolize\":[{\"symbol\":\"REGION.11.in.map\","
                            + "\"cell\":\"" + ALL_KEYS + "\","
                            + "\"field\":\"" + ALL_KEYS + "\","
                            + "\"sourceKind\":\"SHARED_HEAP\","
                            + "\"location\":\"HEAP_OBJECT_FIELD\","
                            + "\"javaType\":\"java.util.Map\","
                            + "\"observed\":true}]");
            Files.write(fixture.activations,
                    observedMapPrestate.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result mapState =
                    ConcolicScheduler.schedule(arguments);
            JsonObject mapBinding = mapState.scheduledActivations.get(0)
                    .getAsJsonArray("materializations").get(0)
                    .getAsJsonObject();
            assertEquals("MAP_STATE_INPUT_OBSERVATION",
                    mapBinding.get("bindingMode").getAsString());
            assertTrue(mapBinding.get("mapStateObservationOnly")
                    .getAsBoolean());
            assertFalse(mapBinding.get("modelControllable")
                    .getAsBoolean());
            assertEquals(ALL_KEYS,
                    mapBinding.get("mapStateRequestedOutputCell")
                            .getAsString());

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
            assertFalse(blocked.jobs.get(0).get("captureReady")
                    .getAsBoolean());

            JsonObject autoCapture = JsonParser.parseString(activation)
                    .getAsJsonObject();
            autoCapture.addProperty("requestedOutputCaptureRequired", true);
            autoCapture.addProperty("requestedOutputCaptureComplete", false);
            JsonArray captureTemplates = new JsonArray();
            JsonObject encryptedCapture = new JsonObject();
            encryptedCapture.addProperty("captureBindingId", "CAP.0");
            encryptedCapture.addProperty("siteId",
                    "<example.Client: void encrypted()>#u7");
            encryptedCapture.addProperty("callerMethod",
                    "<example.Client: void encrypted()>");
            encryptedCapture.addProperty("occurrence", 0);
            captureTemplates.add(encryptedCapture);
            JsonObject plainCapture = new JsonObject();
            plainCapture.addProperty("captureBindingId", "CAP.1");
            plainCapture.addProperty("siteId",
                    "<example.Client: void plain()>#u9");
            plainCapture.addProperty("callerMethod",
                    "<example.Client: void plain()>");
            plainCapture.addProperty("occurrence", 0);
            captureTemplates.add(plainCapture);
            autoCapture.add("requestedOutputCapture", captureTemplates);
            Files.write(fixture.activations,
                    (autoCapture + "\n").getBytes(StandardCharsets.UTF_8));
            Files.write(fixture.runtimeInstances,
                    ("{\"regionInstanceId\":"
                            + "\"REGION.11@test#call7\","
                            + "\"observedMethods\":["
                            + "\"<example.Client: void encrypted()>\"]}\n")
                            .getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments autoCaptureArguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan",
                            fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--runtime-region-instances",
                            fixture.runtimeInstances.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only"});
            JsonObject automaticallyRefined = ConcolicScheduler.schedule(
                    autoCaptureArguments).scheduledActivations.get(0);
            JsonObject automaticCapture = automaticallyRefined
                    .getAsJsonArray("requestedOutputCapture").get(0)
                    .getAsJsonObject();
            assertEquals("<example.Client: void encrypted()>#u7",
                    automaticCapture.get("siteId").getAsString());
            assertEquals(1, automaticCapture.get("occurrence").getAsInt());
            assertTrue(automaticallyRefined.get(
                    "requestedOutputCaptureOccurrenceApproximate")
                    .getAsBoolean());
            assertTrue(automaticallyRefined.get(
                    "requestedOutputCaptureComplete").getAsBoolean());

            ConcolicScheduler.Arguments explicitCaptureArguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan",
                            fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only",
                            "--requested-output-capture-site",
                            "<example.Client: void plain()>#u9",
                            "--requested-output-capture-occurrence", "3"});
            JsonObject explicitlyRefined = ConcolicScheduler.schedule(
                    explicitCaptureArguments).scheduledActivations.get(0);
            JsonObject explicitCapture = explicitlyRefined.getAsJsonArray(
                    "requestedOutputCapture").get(0).getAsJsonObject();
            assertEquals("<example.Client: void plain()>#u9",
                    explicitCapture.get("siteId").getAsString());
            assertEquals(3, explicitCapture.get("occurrence").getAsInt());
            assertEquals("CONFIGURED_EXACT_CAPTURE_SITE_AND_OCCURRENCE_V1",
                    explicitlyRefined.get(
                            "requestedOutputCaptureSelectionAuthority")
                            .getAsString());

            String deferred = activation.replace("\"symbolize\":[]",
                    "\"symbolize\":[{\"symbol\":\"REGION.11.in.env\","
                            + "\"cell\":\"<example.Clock: long now()>.return\","
                            + "\"location\":\"ENVIRONMENT_MODEL\"}]");
            Files.write(fixture.activations,
                    deferred.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result deferredClosure =
                    ConcolicScheduler.schedule(arguments);
            assertTrue(deferredClosure.jobs.get(0).get("captureReady")
                    .getAsBoolean());
            assertTrue(deferredClosure.jobs.get(0)
                    .get("materializationComplete").getAsBoolean());
            assertEquals(1, deferredClosure.jobs.get(0)
                    .get("concreteFallbackCount").getAsInt());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void outputClosureCarriesOrderedRuntimeValueEqualityBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            setSaslEqualityEvidence(fixture, 10, 20);
            String activation = "{\"activationId\":\"ACT.NN\","
                    + "\"regionInstanceId\":\"REGION.1@test#call1\","
                    + "\"regionId\":\"REGION.1\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"<example.Client: void send()>\","
                    + "\"runtimeDefinitionMethods\":["
                    + "\"<example.Client: void send()>\"],"
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"symbolicReady\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSliceComplete\":true,"
                    + "\"requestedOutput\":{"
                    + "\"portId\":\"REGION.1.out.0\","
                    + "\"cell\":\"client.userName\","
                    + "\"kind\":\"VALUE\"},"
                    + "\"symbolize\":[],\"outputs\":[],"
                    + "\"branches\":[]}\n";
            Files.write(fixture.activations,
                    activation.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.NN", "--capture-only"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            JsonObject scheduledBinding = result.scheduledActivations.get(0)
                    .getAsJsonArray("edgeBindings").get(0)
                    .getAsJsonObject();
            assertRuntimeEqualityBinding(scheduledBinding);
            JsonObject jobBinding = result.jobs.get(0)
                    .getAsJsonArray("edgeBindings").get(0)
                    .getAsJsonObject();
            assertEquals(scheduledBinding, jobBinding);

            // Equality is not admitted from fingerprint coincidence alone;
            // the concrete producer event must precede the consumer event.
            setSaslEqualityEvidence(fixture, 20, 10);
            ConcolicScheduler.Result unordered =
                    ConcolicScheduler.schedule(arguments);
            assertEquals(0, unordered.jobs.get(0)
                    .getAsJsonArray("edgeBindings").size());

            // Repeated endpoint observations in a long-running root describe
            // one semantic transfer. Prefer the nearest ordered witness even
            // when it appears after a less precise row.
            setSaslEqualityEvidence(fixture, 10, 20);
            prependSaslEqualityEvidence(fixture, 1, 100);
            ConcolicScheduler.Result repeated =
                    ConcolicScheduler.schedule(arguments);
            assertEquals(1, repeated.jobs.get(0)
                    .getAsJsonArray("edgeBindings").size());
            assertRuntimeEqualityBinding(repeated.jobs.get(0)
                    .getAsJsonArray("edgeBindings").get(0)
                    .getAsJsonObject());
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
            setSaslEqualityEvidence(fixture, 10, 20);
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
            RegionCaptureGoal.outputClosure().writeTo(nn);
            JsonObject heartbeat = JsonParser.parseString("{"
                    + "\"activationId\":\"ACT.HEARTBEAT\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"regionInstanceId\":\"REGION.11@test#call2\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"<example.Updater: void run()>\","
                    + "\"invocationOrdinal\":1,\"symbolize\":[]}")
                    .getAsJsonObject();
            RegionCaptureGoal.outputClosure().writeTo(heartbeat);
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
            assertRuntimeEqualityBinding(result.scheduledActivations.get(0)
                    .getAsJsonArray("edgeBindings").get(0)
                    .getAsJsonObject());
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
                    + "\"runtimeDefinitionMethods\":[\"" + root + "\"],"
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
            ConcolicScheduler.Result fallback =
                    ConcolicScheduler.schedule(arguments);
            assertTrue(fallback.jobs.get(0).get("captureReady")
                    .getAsBoolean());
            assertTrue(fallback.jobs.get(0).get("materializationComplete")
                    .getAsBoolean());
            assertFalse(fallback.jobs.get(0).get("symbolicCoverageComplete")
                    .getAsBoolean());
            assertEquals(0, fallback.scheduledActivations.get(0)
                    .getAsJsonArray("materializations").size());
            assertEquals("UNRESOLVED_ARGUMENT_FIELD_PATH",
                    fallback.scheduledActivations.get(0)
                            .getAsJsonArray("concreteFallbacks").get(0)
                            .getAsJsonObject().get("concreteFallbackReason")
                            .getAsString());
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
                    + "\"runtimeDefinitionMethods\":[\"" + root + "\"],"
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
                    + "\"runtimeDefinitionMethods\":[\"" + root + "\"],"
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSliceComplete\":true,"
                    + "\"requestedOutputMethods\":[\"" + root + "\"],"
                    + "\"requestedOutputSlice\":{\"sites\":[\""
                    + site + "\"]},"
                    + "\"requestedOutputCaptureRequired\":false,"
                    + "\"requestedOutputCaptureComplete\":true,"
                    + "\"requestedOutputCapture\":[],"
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
                    + "\"observed\":false,"
                    + "\"deferredResolution\":true,"
                    + "\"deferredResolutionAuthority\":"
                    + "\"AUTHORITATIVE_SCHEDULER_DEFINITION_INDEX_"
                    + "REQUIRED_V1\"}],"
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
            assertFalse(binding.has("deferredResolution"));
            assertFalse(binding.has("deferredResolutionAuthority"));
            assertTrue(binding.get("deferredResolutionDischarged")
                    .getAsBoolean());
            assertEquals("AUTHORITATIVE_STATIC_CALL_RETURN_DEFINITION_"
                            + "SITE_V1",
                    binding.get("deferredResolutionDischargeAuthority")
                            .getAsString());
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
        RegionCaptureGoal.outputClosure().writeTo(activation);

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
    public void schedulerBuildsExecutablePlanOnlyFromDeclarations() {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("symbol", "REGION.CANONICAL.in.0");
        declaration.addProperty("cell", "example.Input.value");
        declaration.addProperty("location", "ARGUMENT");
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.CANONICAL");
        activation.addProperty("regionId", "REGION.CANONICAL");
        RegionCaptureGoal.outputClosure().writeTo(activation);
        activation.addProperty("requestedOutputSliceComplete", true);

        JsonArray retiredExecutablePlan = new JsonArray();
        retiredExecutablePlan.add(declaration.deepCopy());
        activation.add("materializations", retiredExecutablePlan);
        JsonObject missingDeclaration =
                ConcolicScheduler.prepareOutputCapture(activation,
                        Collections.<JsonObject>emptyList());
        assertTrue(missingDeclaration.get("schedulerReady").getAsBoolean());
        assertEquals(0, missingDeclaration.getAsJsonArray(
                "materializations").size());

        activation.add("symbolize", new JsonArray());
        JsonObject explicitEmptyDeclaration =
                ConcolicScheduler.prepareOutputCapture(activation,
                        Collections.<JsonObject>emptyList());
        assertEquals(0, explicitEmptyDeclaration.getAsJsonArray(
                "materializations").size());

        JsonArray declarations = new JsonArray();
        declarations.add(declaration.deepCopy());
        activation.add("symbolize", declarations);
        JsonObject scheduled = ConcolicScheduler.prepareOutputCapture(
                activation, Collections.<JsonObject>emptyList());
        JsonArray executable = scheduled.getAsJsonArray("materializations");
        assertEquals(1, executable.size());
        assertEquals("ROOT_ENTRY", executable.get(0).getAsJsonObject()
                .get("bindingMode").getAsString());
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
    public void invalidArrayEvidenceUsesConcreteFallback() {
        String method = "<example.ArrayReader: void run()>";
        JsonObject missingSite = exactArrayFieldAction(method);
        missingSite.remove("consumedFieldSiteId");
        JsonObject incompleteBinding = exactArrayFieldAction(method);
        incompleteBinding.remove("consumedFieldBindingComplete");
        JsonObject missingOccurrence = exactArrayFieldAction(method);
        missingOccurrence.remove("consumedFieldOccurrence");
        missingOccurrence.remove("consumedFieldOccurrenceAuthority");
        JsonObject metadataConflict = exactArrayFieldAction(method);
        metadataConflict.add("fieldPath",
                JsonParser.parseString("[\"other\"]"));

        List<JsonObject> actions = Arrays.asList(missingSite,
                incompleteBinding, missingOccurrence, metadataConflict);
        List<String> reasons = Arrays.asList(
                "EXACT_CONSUMED_FIELD_METHOD_UNIT_SITE_MISSING",
                "PLANNER_CONSUMED_FIELD_BINDING_INCOMPLETE",
                "EXACT_CONSUMED_FIELD_OCCURRENCE_INVALID",
                "PLANNER_EXACT_FIELD_METADATA_CONFLICTS_WITH_STATIC_CELL");
        for (int index = 0; index < actions.size(); index++) {
            JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                    arrayFieldCaptureActivation(actions.get(index)),
                    Collections.<JsonObject>emptyList());

            assertTrue(prepared.get("schedulerReady").getAsBoolean());
            assertTrue(prepared.get("materializationComplete").getAsBoolean());
            assertFalse(prepared.get("symbolicCoverageComplete")
                    .getAsBoolean());
            assertEquals(0, prepared.getAsJsonArray("materializations")
                    .size());
            assertEquals(reasons.get(index), prepared
                    .getAsJsonArray("concreteFallbacks").get(0)
                    .getAsJsonObject().get("concreteFallbackReason")
                    .getAsString());
        }
    }

    @Test
    public void exactDeclaredDeepLeafOwnerSurvivesMaterialization() {
        String root = "<example.StateNode: example.GuardNode state>";
        String leaf = "<example.BooleanLeaf: boolean enabled>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.DEEP.in.0");
        action.addProperty("cell", root
                + "#field:guard#field:enabled");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("observed", true);
        action.addProperty("valueObjectId", 42L);
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", root);
        action.addProperty("accessOwnerClass", "example.StateNode");
        action.addProperty("accessFieldType", "example.GuardNode");
        action.addProperty("accessField", "state");
        action.addProperty("field", leaf);
        action.addProperty("leafFieldSignature", leaf);
        action.addProperty("leafOwnerClass", "example.BooleanLeaf");
        action.addProperty("leafField", "enabled");
        action.addProperty("javaType", "boolean");
        action.addProperty("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        action.add("fieldPath", JsonParser.parseString(
                "[\"state\",\"guard\",\"enabled\"]"));
        JsonObject declaration = new JsonObject();
        declaration.add("fieldPath", action.get("fieldPath").deepCopy());
        declaration.addProperty("fieldSignature", leaf);
        declaration.addProperty("declaredFieldOwnerClass",
                "example.BooleanLeaf");
        declaration.addProperty("declaredFieldType", "boolean");
        declaration.addProperty("complete", true);
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        action.add("fieldPathLeafDeclarations", declarations);

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                arrayFieldCaptureActivation(action),
                Collections.<JsonObject>emptyList());

        assertEquals(1, prepared.getAsJsonArray("materializations").size());
        assertEquals(0, prepared.getAsJsonArray("concreteFallbacks").size());
        JsonObject binding = prepared.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        assertEquals("FIELD_ACCESS",
                binding.get("bindingMode").getAsString());
        assertEquals("example.BooleanLeaf",
                binding.get("leafOwnerClass").getAsString());
        assertEquals("boolean", binding.get("javaType").getAsString());
        assertEquals(3, binding.getAsJsonArray("fieldPath").size());
    }

    @Test
    public void uniqueDefinitionFinalizesPendingLocalArrayRoot() {
        String root = "<example.LocalArray: void run()>";
        String localCell = root + "::$r0";
        JsonObject action = exactArrayFieldAction(root);
        action.addProperty("cell", localCell);
        action.addProperty("location", "REGION_LIVE_IN");
        action.addProperty("deferredResolution", true);
        action.addProperty("deferredResolutionAuthority",
                "AUTHORITATIVE_SCHEDULER_DEFINITION_INDEX_REQUIRED_V1");
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
        assertFalse(binding.has("deferredResolution"));
        assertEquals("AUTHORITATIVE_STATIC_LOCAL_DEFINITION_SITE_V1",
                binding.get("deferredResolutionDischargeAuthority")
                        .getAsString());
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
        JsonObject binding = prepared.getAsJsonArray("concreteFallbacks")
                .get(0).getAsJsonObject();

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertTrue(prepared.get("materializationComplete").getAsBoolean());
        assertFalse(prepared.get("symbolicCoverageComplete").getAsBoolean());
        assertEquals(0, prepared.getAsJsonArray("materializations").size());
        assertEquals("CONCRETE_PASSTHROUGH",
                binding.get("bindingMode").getAsString());
        assertEquals(2, binding.getAsJsonArray("definitionSites").size());
        assertEquals("ARRAY_CALL_RETURN_ROOT_REQUIRES_ONE_EXACT_"
                        + "FILTERED_RETURN_SITE:2",
                binding.get("concreteFallbackReason").getAsString());
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
        RegionCaptureGoal.outputClosure().writeTo(activation);
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
        assertEquals(">=", BranchPredicateAlgebra.complement(condition)
                .getAsJsonObject().get("_op").getAsString());
    }

    private static void writeRows(Path path, List<JsonObject> rows)
            throws Exception {
        StringBuilder content = new StringBuilder();
        for (JsonObject row : rows) content.append(row).append('\n');
        Files.write(path, content.toString().getBytes(StandardCharsets.UTF_8));
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

    private static void setSaslEqualityEvidence(Fixture fixture,
                                                long writer,
                                                long reader)
            throws Exception {
        List<String> rows = Files.readAllLines(fixture.edges,
                StandardCharsets.UTF_8);
        JsonArray rewritten = new JsonArray();
        boolean found = false;
        for (String row : rows) {
            if (row.trim().isEmpty()) continue;
            JsonObject edge = JsonParser.parseString(row).getAsJsonObject();
            if ("E.SASL".equals(edge.get("edgeId").getAsString())) {
                JsonObject evidence = edge.getAsJsonArray(
                        "validatedBindings")
                        .get(0).getAsJsonObject().deepCopy();
                evidence.addProperty("fromRegionInstance",
                        "REGION.1@test#call1");
                evidence.addProperty("toRegionInstance",
                        "REGION.0@testMiniDfs#call7");
                evidence.addProperty("fromEndpointSeq", writer);
                evidence.addProperty("toEndpointSeq", reader);
                evidence.addProperty("orderConfirmed", writer < reader);
                JsonArray singleton = new JsonArray();
                singleton.add(evidence);
                edge.add("validatedBindings", singleton);
                found = true;
            }
            rewritten.add(edge);
        }
        assertTrue(found);
        StringBuilder content = new StringBuilder();
        for (JsonElement element : rewritten) {
            content.append(element).append('\n');
        }
        Files.write(fixture.edges,
                content.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static void prependSaslEqualityEvidence(Fixture fixture,
                                                    long writer,
                                                    long reader)
            throws Exception {
        List<String> rows = Files.readAllLines(fixture.edges,
                StandardCharsets.UTF_8);
        StringBuilder content = new StringBuilder();
        boolean found = false;
        for (String row : rows) {
            if (row.trim().isEmpty()) continue;
            JsonObject edge = JsonParser.parseString(row).getAsJsonObject();
            if ("E.SASL".equals(edge.get("edgeId").getAsString())) {
                JsonArray current = edge.getAsJsonArray(
                        "validatedBindings");
                JsonObject duplicate = current.get(0).getAsJsonObject()
                        .deepCopy();
                duplicate.addProperty("fromEndpointSeq", writer);
                duplicate.addProperty("toEndpointSeq", reader);
                duplicate.addProperty("orderConfirmed", writer < reader);
                JsonArray repeated = new JsonArray();
                repeated.add(duplicate);
                for (JsonElement element : current) {
                    repeated.add(element.deepCopy());
                }
                edge.add("validatedBindings", repeated);
                found = true;
            }
            content.append(edge).append('\n');
        }
        assertTrue(found);
        Files.write(fixture.edges,
                content.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static void assertRuntimeEqualityBinding(JsonObject binding) {
        assertEquals("E.SASL", binding.get("edgeId").getAsString());
        assertEquals("EQUALITY", binding.get("relationKind").getAsString());
        assertEquals("RUNTIME_CONFIRMED_VALUE_EQUALITY", binding.get(
                "selectionAuthority").getAsString());
        assertEquals("REGION.1@test#call1", binding.get(
                "fromRegionInstance").getAsString());
        assertEquals("REGION.0@testMiniDfs#call7", binding.get(
                "toRegionInstance").getAsString());
        assertEquals("REGION.1.out.0", binding.get(
                "fromOutputPort").getAsString());
        assertEquals("REGION.0.in.0", binding.get(
                "toInputPort").getAsString());
        assertEquals(10, binding.get("writerEventSeq").getAsInt());
        assertEquals(20, binding.get("readerEventSeq").getAsInt());
        assertTrue(binding.get("orderConfirmed").getAsBoolean());
        assertTrue(binding.get("valueEqualityObserved").getAsBoolean());
        assertEquals("RUNTIME_COMPLETE_VALUE_FINGERPRINT", binding.get(
                "valueEqualityAuthority").getAsString());
        assertEquals("GLOBAL_TRACE_ENDPOINT_SEQUENCE", binding.get(
                "endpointOrderAuthority").getAsString());
        assertEquals("EXEC.fixture", binding.get(
                "discoveredExecutionId").getAsString());
        assertEquals("sha256:fixture", binding.get(
                "valueFingerprint").getAsString());
        assertFalse(binding.get("objectIdentityRequired").getAsBoolean());
        assertFalse(binding.has("receiverObjectId"));
        assertFalse(binding.has("objectIdentityConfirmed"));
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

    private static String accessorInputProof(String edgeId, String fromCell,
                                             String toCell) {
        String getter = "<javax.security.auth.callback.NameCallback: "
                + "java.lang.String getDefaultName()>";
        return "{\"id\":\"" + edgeId + "\","
                + "\"kind\":\"accessor_field_return\","
                + "\"transferKind\":\"HEAP_READ\","
                + "\"relation\":\"value_flow\","
                + "\"direction\":\"backward_provenance\","
                + "\"mappingOnly\":false,"
                + "\"semanticAssertionsAllowed\":true,"
                + "\"eligibleForAutomaticDerivation\":true,"
                + "\"eligibleForAutomaticSmt\":true,"
                + "\"fromCell\":\"" + fromCell + "\","
                + "\"toCell\":\"" + toCell + "\","
                + "\"invoke\":\"" + getter + "\","
                + "\"declaredFieldSignature\":\"" + fromCell + "\","
                + "\"declaredFieldOwner\":"
                + "\"javax.security.auth.callback.NameCallback\","
                + "\"declaredFieldType\":\"java.lang.String\","
                + "\"declaredFieldName\":\"defaultName\","
                + "\"declaredFieldAuthority\":"
                + "\"SOOT_RESOLVED_DECLARATION_HIERARCHY\","
                + "\"accessorImplementationMethod\":\"" + getter + "\","
                + "\"accessorImplementationAuthority\":"
                + "\"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY\"}\n";
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
                + "\"runtimeDefinitionMethods\":[\"" + ROOT + "\","
                + "\"" + CALLBACK + "\","
                + "\"<example.Manager: byte[] lookup(int)>\"],"
                + "\"receiverType\":\"example.Server\","
                + "\"receiverRuntimeClass\":\"example.Server\","
                + "\"threadName\":\"rpc-handler\","
                + "\"threadIdSelectionUsed\":false,"
                + "\"invocationOrdinalWithinContext\":1,"
                + "\"rootContextSelectionAuthority\":"
                + "\"TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                + "THREAD_NAME_CONTEXT_ORDINAL_V1\","
                + "\"invocationOrdinal\":1,\"replayable\":true,"
                + "\"captureGoal\":{\"kind\":\"TARGET_BRANCH\","
                + "\"scope\":\"ONE_DIRECTED_BRANCH\"},"
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
                + "\"endpointOrderAuthority\":"
                + "\"GLOBAL_TRACE_ENDPOINT_SEQUENCE\","
                + "\"endpointCorrelationAuthority\":"
                + "\"NEAREST_PRECEDING_MATCHING_SOURCE_ENDPOINT\","
                + "\"discoveredExecutionId\":\"EXEC.fixture\","
                + "\"eligibleForAutomaticDerivation\":true,"
                + "\"eligibleForAutomaticSmt\":true,"
                + "\"composable\":true,\"validatedBindings\":[{"
                + "\"fromRegionInstance\":\"REGION.1@test#call1\","
                + "\"toRegionInstance\":"
                + "\"REGION.0@testMiniDfs#call7\","
                + "\"valueEqualityObserved\":true,"
                + "\"valueEqualityAuthority\":"
                + "\"RUNTIME_COMPLETE_VALUE_FINGERPRINT\","
                + "\"valueFingerprint\":\"sha256:fixture\","
                + "\"endpointOrderAuthority\":"
                + "\"GLOBAL_TRACE_ENDPOINT_SEQUENCE\","
                + "\"fromEndpointSeq\":10,\"toEndpointSeq\":20,"
                + "\"orderConfirmed\":true}]}\n"
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
                + "\"composable\":true,\"validatedBindings\":[{"
                + "\"writeEvidenceKind\":\"FIELD_ASSIGNMENT\","
                + "\"writeEvidenceAuthority\":"
                + "\"RUNTIME_EXACT_FIELD_WRITE_EVENT_V1\","
                + "\"orderAuthority\":"
                + "\"GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1\","
                + "\"writeSeq\":1,\"readSeq\":2,"
                + "\"receiverObjectId\":7,"
                + "\"fieldReceiverIdentityConfirmed\":true,"
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
            JsonObject summary = new JsonObject();
            summary.addProperty("summaryId", "SUMMARY.REGION.0.SEED");
            summary.addProperty("activationId", "ACT.0");
            summary.addProperty("regionId", "REGION.0");
            summary.addProperty("regionInstanceId",
                    "REGION.0@testMiniDfs#call7");
            summary.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
            summary.addProperty("valid", true);
            summary.addProperty("branchOverrideUsed", false);
            JsonObject admission = new JsonObject();
            admission.addProperty("required", false);
            admission.addProperty("valid", true);
            admission.addProperty("branchOverrideAccepted", false);
            admission.addProperty("authority",
                    "OBSERVED_UNFORCED_TARGET_SEED_PATH_ONLY");
            summary.add("executionAdmission", admission);

            JsonObject prefixCondition = JsonParser.parseString(
                    "{\"_type\":\"BinaryExpression\",\"_op\":\">\"}")
                    .getAsJsonObject();
            JsonObject relation = JsonParser.parseString(
                    "{\"_type\":\"MethodExpression\","
                            + "\"_name\":\"java/util/HashMap get\","
                            + "\"_param_list\":["
                            + "{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"MAP\"},"
                            + "{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"KEY\"}],"
                            + "\"_res_exp\":{\"_type\":"
                            + "\"SymbolExpression\",\"_exp\":\"RESULT\"}}")
                    .getAsJsonObject();
            JsonObject targetCondition = JsonParser.parseString(
                    "{\"_type\":\"BinaryExpression\",\"_op\":\"!=\","
                            + "\"_left\":{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"RESULT\"},"
                            + "\"_right\":{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"N\"}}")
                    .getAsJsonObject();
            JsonArray path = new JsonArray();
            path.add(prefixCondition);
            path.add(relation);
            path.add(targetCondition);
            summary.add("pathCondition", path);

            JsonObject prefixEvent = new JsonObject();
            prefixEvent.addProperty("eventId", 1);
            prefixEvent.addProperty("contextId", 7);
            BranchWitness prefixWitness = BranchWitness.vmPc(
                    "<example.Manager: byte[] lookup(int)>#u1",
                    "<example.Manager: byte[] lookup(int)>", 1, 1, true,
                    prefixCondition, 0, prefixEvent);
            JsonObject targetEvent = new JsonObject();
            targetEvent.addProperty("eventId", 2);
            targetEvent.addProperty("contextId", 7);
            BranchWitness targetWitness = BranchWitness.vmPc(TARGET,
                    "<example.Manager: byte[] lookup(int)>", 8, 1, true,
                    targetCondition, 2, targetEvent);
            JsonObject prefixMapping = new JsonObject();
            prefixMapping.addProperty("siteId", prefixWitness.siteId());
            prefixMapping.addProperty("occurrence", 1);
            prefixMapping.addProperty("conditionIndex", 0);
            prefixMapping.addProperty("summaryPcIndex", 0);
            prefixMapping.add("witness", prefixWitness.toJson());
            JsonObject targetMapping = new JsonObject();
            targetMapping.addProperty("siteId", TARGET);
            targetMapping.addProperty("occurrence", 1);
            targetMapping.addProperty("conditionIndex", 2);
            targetMapping.addProperty("summaryPcIndex", 2);
            targetMapping.add("witness", targetWitness.toJson());
            JsonArray mappings = new JsonArray();
            mappings.add(prefixMapping);
            mappings.add(targetMapping);
            summary.add("branchMappings", mappings);
            Files.write(result.summaries,
                    (summary + "\n").getBytes(StandardCharsets.UTF_8));
        }
        return result;
    }

    private static final class Fixture {
        private final Path regions;
        private final Path activations;
        private final Path edges;
        private final Path staticGraph;
        private final Path summaries;
        private final Path runtimeInstances;
        private final Path output;

        private Fixture(Path root) {
            this.regions = root.resolve("regions.jsonl");
            this.activations = root.resolve("activations.jsonl");
            this.edges = root.resolve("edges.jsonl");
            this.staticGraph = root.resolve("static.jsonl");
            this.summaries = root.resolve("summaries.jsonl");
            this.runtimeInstances = root.resolve(
                    "runtime-region-instances.jsonl");
            this.output = root.resolve("schedule");
        }
    }
}
