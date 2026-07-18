package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class Hdfs11741BootstrapComposerTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void buildsSymbolicOneEntryExpiryBootstrapWithModelQuery()
            throws Exception {
        Fixture fixture = new Fixture(folder.getRoot().toPath(), true);

        Hdfs11741BootstrapComposer.Result result =
                Hdfs11741BootstrapComposer.compose(fixture.arguments(true));

        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertFalse(result.manifest.get("relationallyComplete")
                .getAsBoolean());
        assertTrue(result.manifest.get("domainSemanticAdapterUsed")
                .getAsBoolean());
        assertTrue(result.manifest.get(
                "eligibleForApproximateBootstrapModel").getAsBoolean());
        assertTrue(result.manifest.get("innerMapExpirySymbolic")
                .getAsBoolean());
        assertEquals("REGION.T", result.manifest.getAsJsonObject(
                "selectedRegions").getAsJsonObject("target")
                .get("regionId").getAsString());
        assertEquals("REGION.D", result.manifest.getAsJsonObject(
                "portMappings").getAsJsonObject("datanodeMapPost")
                .get("regionId").getAsString());
        assertEquals(5, result.manifest.getAsJsonObject(
                "supplementalEvidence").get("replaySummaryCount")
                .getAsInt());
        assertTrue(result.manifest.getAsJsonObject("supplementalEvidence")
                .get("replaySummariesRequired").getAsBoolean());
        assertEquals(5, result.manifest.getAsJsonObject(
                "supplementalEvidence").getAsJsonObject(
                "selectedReplaySummaries").size());
        assertTrue(result.manifest.getAsJsonObject("supplementalEvidence")
                .getAsJsonObject("replayFormulaProjection")
                .getAsJsonArray("emittedAssertions").size() >= 5);

        String smt = result.smtLib;
        assertTrue(smt.contains("(declare-const dn_iterator_key_id Int)"));
        assertTrue(smt.contains("(< (select dn_expiry_after_add "
                + "dn_iterator_key_id) remove_now)"));
        assertTrue(smt.contains("(= dn_keys_after_remove (store "
                + "dn_keys_after_add dn_iterator_key_id false))"));
        assertTrue(smt.contains("(< cached_dek_expiry observation_time)"));
        assertTrue(smt.contains("(< old_block_key_expiry "
                + "observation_time)"));
        assertTrue(smt.contains("(distinct nn_later_current_key_id "
                + "nn_snapshot_key_id)"));
        assertTrue(smt.contains("(= lookup_key_id sasl_server_key_id)"));
        assertTrue(smt.contains("(not (select dn_keys_at_target "
                + "lookup_key_id))"));
        assertTrue(smt.indexOf("(get-model)")
                > smt.indexOf("(check-sat)"));
        assertTrue(smt.contains("(get-value (exception_reached"));
        assertTrue(smt.contains("; replay summary: SUMMARY.REGION.K"));
        assertTrue(smt.contains("summary_path_REGION_K"));
        assertFalse("the iterator key must not be a workload constant",
                smt.contains("dn_iterator_key_id 1005215027"));

        Hdfs11741ReplaySelector.Result replaySelection =
                Hdfs11741ReplaySelector.select(
                        fixture.replaySelectorArguments());
        assertEquals(5, replaySelection.selections.size());
        JsonObject selectedActivations = replaySelection.manifest
                .getAsJsonObject("selectedActivations");
        assertEquals("ACT.NN.LATEST", selectedActivations
                .getAsJsonObject("namenode").get("activationId")
                .getAsString());
        assertEquals("ACT.DN.LATEST", selectedActivations
                .getAsJsonObject("datanode").get("activationId")
                .getAsString());
        assertEquals("ACT.KU", selectedActivations
                .getAsJsonObject("keyUpdater").get("activationId")
                .getAsString());
        assertEquals("ACT.BAL.FIRST", selectedActivations
                .getAsJsonObject("balancer").get("activationId")
                .getAsString());
        assertEquals("ACT.TARGET.FIRST.AFTER", selectedActivations
                .getAsJsonObject("target").get("activationId")
                .getAsString());
        JsonObject runtimeSelection = replaySelection.manifest
                .getAsJsonObject("dispatcherTargetRuntimeEvidence");
        assertEquals("REGION.B@fixture#call40", runtimeSelection.get(
                "fromRegionInstance").getAsString());
        assertEquals("REGION.T@fixture#call41", runtimeSelection.get(
                "toRegionInstance").getAsString());
        assertTrue(runtimeSelection.get("uniqueValidatedBinding")
                .getAsBoolean());
        assertEquals(5, Files.readAllLines(fixture.replaySelection,
                StandardCharsets.UTF_8).size());
        assertTrue(replaySelection.manifest.get("causalBoundsVerified")
                .getAsBoolean());
        assertTrue(replaySelection.manifest.getAsJsonObject("causalBounds")
                .getAsJsonObject("namenodeToDatanode")
                .get("strictlyBefore").getAsBoolean());
        assertFalse(replaySelection.manifest.get(
                "configuredGeneratedActivationIds").getAsBoolean());
        JsonObject transport = replaySelection.manifest.getAsJsonObject(
                "configuredTransportBindings");
        assertEquals(1, transport.get("schemaVersion").getAsInt());
        assertEquals("POLICY_DERIVED_HDFS_RPC_SNAPSHOT_BINDING_V1",
                transport.get("authority").getAsString());
        assertTrue(transport.get("policyDerived").getAsBoolean());
        assertFalse(transport.get("configuredGeneratedRegionIds")
                .getAsBoolean());
        assertFalse(transport.get("configuredGeneratedActivationIds")
                .getAsBoolean());
        assertEquals(2, transport.get("bindingCount").getAsInt());
        JsonArray resolvedBindings = transport.getAsJsonArray("bindings");
        JsonObject keyBinding = resolvedBindings.get(0).getAsJsonObject();
        JsonObject keySource = keyBinding.getAsJsonObject("source");
        assertEquals("namenode", keySource.get("role").getAsString());
        assertEquals("REGION.N", keySource.get("regionId").getAsString());
        assertEquals("REGION.N@fixture#call20", keySource.get(
                "regionInstanceId").getAsString());
        assertEquals("MAP_PUT", keySource.get("effectKind").getAsString());
        assertEquals("keyExpression", keySource.get("expressionField")
                .getAsString());
        assertTrue(keySource.get("selectorPreserved").getAsBoolean());
        JsonObject updaterTarget = keyBinding.getAsJsonArray("targets")
                .get(0).getAsJsonObject();
        assertEquals("REGION.K.out.0", updaterTarget.get("portId")
                .getAsString());
        assertEquals("REGION.K@fixture#call30", updaterTarget.get(
                "regionInstanceId").getAsString());
        assertEquals("keyId", updaterTarget.getAsJsonArray("fieldPath")
                .get(0).getAsString());
        JsonObject datanodeKeyTarget = keyBinding.getAsJsonArray("targets")
                .get(1).getAsJsonObject();
        assertEquals("REGION.D.in.2", datanodeKeyTarget.get("portId")
                .getAsString());
        JsonObject expiryBinding = resolvedBindings.get(1)
                .getAsJsonObject();
        assertEquals("REGION.N.in.1", expiryBinding.getAsJsonObject(
                "source").get("portId").getAsString());
        assertEquals("REGION.D.in.3", expiryBinding.getAsJsonArray(
                "targets").get(0).getAsJsonObject().get("portId")
                .getAsString());
        JsonObject captures = replaySelection.manifest.getAsJsonObject(
                "roleCapturePolicies");
        assertEquals("OUTPUT_CLOSURE", captures.getAsJsonObject(
                "keyUpdater").get("kind").getAsString());
        assertEquals("KU.CURRENT.OUT", captures.getAsJsonObject(
                "keyUpdater").get("requestedOutputCell").getAsString());
        assertEquals("TARGET_BRANCH", captures.getAsJsonObject("target")
                .get("kind").getAsString());

        try {
            Hdfs11741BootstrapComposer.compose(fixture.arguments(false));
            fail("all five replay summaries must be required");
        } catch (java.io.IOException exception) {
            assertTrue(exception.getMessage(), exception.getMessage()
                    .contains("FIVE_REPLAY_SUMMARIES_REQUIRED:0"));
        }
    }

    @Test
    public void missingRuntimeRelationsRemainExplicitApproximations()
            throws Exception {
        Fixture fixture = new Fixture(folder.getRoot().toPath(), false);

        Hdfs11741BootstrapComposer.Result result =
                Hdfs11741BootstrapComposer.compose(fixture.arguments(true));

        JsonArray approximations = result.manifest.getAsJsonArray(
                "approximations");
        assertTrue(hasApproximation(approximations,
                "MISSING_RUNTIME_SASL_EQUALITY"));
        assertTrue(hasApproximation(approximations,
                "MISSING_RUNTIME_SHARED_STATE_EDGE"));
        assertEquals(0, result.manifest.getAsJsonObject(
                "runtimeEvidence").get("confirmedEdgeCount").getAsInt());
        assertEquals("APPROXIMATE_BOOTSTRAP_SMT_READY",
                result.manifest.get("status").getAsString());
    }

    @Test
    public void expiryContainerSnapshotIsNeverApproximated() throws Exception {
        Fixture fixture = new Fixture(folder.getRoot().toPath(), true);
        String malformed = new String(Files.readAllBytes(fixture.regions),
                StandardCharsets.UTF_8).replace(
                "\"schemaVersion\":2,\"kind\":\"ARRAY_ELEMENT_FIELD\"",
                "\"schemaVersion\":1,\"kind\":\"ARRAY_ELEMENT_FIELD\"");
        Files.write(fixture.regions,
                malformed.getBytes(StandardCharsets.UTF_8));

        try {
            Hdfs11741BootstrapComposer.compose(fixture.arguments(true));
            fail("schema-2 expiry evidence must be required");
        } catch (java.io.IOException exception) {
            assertTrue(exception.getMessage(), exception.getMessage()
                    .contains("CONTAINER_BINDING_CARDINALITY:expiry:0"));
        }
    }

    @Test
    public void everySelectedRoleMustBeObservedByThePinnedWorkload()
            throws Exception {
        Fixture fixture = new Fixture(folder.getRoot().toPath(), true);
        StringBuilder retained = new StringBuilder();
        for (String line : Files.readAllLines(fixture.activationPlan,
                StandardCharsets.UTF_8)) {
            if (!line.contains("\"regionId\":\"REGION.B\"")) {
                retained.append(line).append('\n');
            }
        }
        write(fixture.activationPlan, retained.toString());

        try {
            Hdfs11741BootstrapComposer.compose(fixture.arguments(true));
            fail("an unobserved selected role must reject composition");
        } catch (java.io.IOException exception) {
            assertTrue(exception.getMessage(), exception.getMessage()
                    .contains("WORKLOAD_DID_NOT_OBSERVE_ALL_ROLES"));
        }
    }

    @Test
    public void frozenStaticArtifactHashMustMatchRuntimeProvenance()
            throws Exception {
        Fixture fixture = new Fixture(folder.getRoot().toPath(), true);
        String provenance = new String(Files.readAllBytes(
                fixture.offlineProvenance), StandardCharsets.UTF_8)
                .replaceFirst("\\\"staticGraphSha256\\\":\\\"[0-9a-f]+\\\"",
                        "\"staticGraphSha256\":\"deadbeef\"");
        write(fixture.offlineProvenance, provenance);

        try {
            Hdfs11741BootstrapComposer.compose(fixture.arguments(true));
            fail("a stale static graph must reject composition");
        } catch (java.io.IOException exception) {
            assertTrue(exception.getMessage(), exception.getMessage()
                    .contains("PROVENANCE_HASH_MISMATCH:staticGraph"));
        }
    }

    private static boolean hasApproximation(JsonArray values, String id) {
        for (JsonElement element : values) {
            JsonObject value = element.getAsJsonObject();
            if (id.equals(value.get("id").getAsString())) return true;
        }
        return false;
    }

    private static final class Fixture {
        private final Path policy;
        private final Path regions;
        private final Path staticGraph;
        private final Path regionEdges;
        private final Path runtimeEdges;
        private final Path runtimeSummary;
        private final Path activationPlan;
        private final Path offlineProvenance;
        private final Path targetQuery;
        private final Path replaySummary;
        private final Path output;
        private final Path manifest;
        private final Path replaySelection;
        private final Path replaySelectionManifest;

        private Fixture(Path root, boolean runtimeConfirmed)
                throws Exception {
            policy = root.resolve(unique("policy.json"));
            regions = root.resolve(unique("regions.jsonl"));
            staticGraph = root.resolve(unique("static.jsonl"));
            regionEdges = root.resolve(unique("region-edges.jsonl"));
            runtimeEdges = root.resolve(unique("runtime-edges.jsonl"));
            runtimeSummary = root.resolve(unique("runtime-summary.json"));
            activationPlan = root.resolve(unique("activations.jsonl"));
            offlineProvenance = root.resolve(unique("provenance.json"));
            targetQuery = root.resolve(unique("target-query.jsonl"));
            replaySummary = root.resolve(unique("replay.jsonl"));
            output = root.resolve(unique("bootstrap.smt2"));
            manifest = root.resolve(unique("manifest.json"));
            replaySelection = root.resolve(unique("replay-selection.jsonl"));
            replaySelectionManifest = root.resolve(unique(
                    "replay-selection-manifest.json"));
            write(policy, policy());
            write(regions, regions());
            write(staticGraph, staticGraph());
            write(regionEdges, regionEdges());
            write(runtimeEdges, runtimeConfirmed ? runtimeEdges() : "");
            write(runtimeSummary, "{\"schemaVersion\":1,"
                    + "\"staticRegionCount\":5,"
                    + "\"staticRegionEdgeCount\":1,"
                    + "\"runtimeRegionInstanceCount\":5,"
                    + "\"runtimeRegionEdgeValidationCount\":2,"
                    + "\"activationCount\":5,"
                    + "\"truncatedCallTreeInstanceCount\":0,"
                    + "\"truncatedPathSignatureInstanceCount\":0,"
                    + "\"skippedContainedCallCount\":0,"
                    + "\"skippedPathSignatureEventCount\":0,"
                    + "\"truncated\":false}\n");
            write(activationPlan, activations());
            write(offlineProvenance, "{\"schemaVersion\":2,"
                    + "\"kind\":\"OFFLINE_TRACE_AGGREGATION\","
                    + "\"test\":\"example.Test#workload\","
                    + "\"complete\":true,"
                    + "\"aggregationComplete\":true,"
                    + "\"replayJvmAggregation\":false,"
                    + "\"runtimePathEvidenceComplete\":true,"
                    + "\"staticGraphSha256\":\""
                    + sha256(staticGraph) + "\","
                    + "\"symbolicRegionsSha256\":\""
                    + sha256(regions) + "\","
                    + "\"symbolicRegionEdgesSha256\":\""
                    + sha256(regionEdges) + "\","
                    + "\"runtimeRegionSummarySha256\":\""
                    + sha256(runtimeSummary) + "\"}\n");
            write(replaySummary, replaySummaries());
            write(targetQuery, targetQuery());
        }

        private Hdfs11741BootstrapComposer.Arguments arguments(
                boolean includeReplay) {
            java.util.List<String> values = new java.util.ArrayList<>();
            add(values, "--policy", policy);
            add(values, "--regions", regions);
            add(values, "--static-graph", staticGraph);
            add(values, "--region-edges", regionEdges);
            add(values, "--runtime-edge-validations", runtimeEdges);
            add(values, "--runtime-summary", runtimeSummary);
            add(values, "--activation-plan", activationPlan);
            add(values, "--offline-provenance", offlineProvenance);
            add(values, "--target-query", targetQuery);
            if (includeReplay) add(values, "--replay-summary",
                    replaySummary);
            add(values, "--output", output);
            add(values, "--manifest", manifest);
            return Hdfs11741BootstrapComposer.Arguments.parse(
                    values.toArray(new String[0]));
        }

        private Hdfs11741ReplaySelector.Arguments replaySelectorArguments() {
            java.util.List<String> values = new java.util.ArrayList<>();
            add(values, "--policy", policy);
            add(values, "--regions", regions);
            add(values, "--activation-plan", activationPlan);
            add(values, "--runtime-edges", runtimeEdges);
            add(values, "--output", replaySelection);
            add(values, "--manifest", replaySelectionManifest);
            return Hdfs11741ReplaySelector.Arguments.parse(
                    values.toArray(new String[0]));
        }

        private static void add(java.util.List<String> values, String name,
                                Path path) {
            values.add(name);
            values.add(path.toString());
        }

        private static String unique(String suffix) {
            return java.util.UUID.randomUUID().toString() + "-" + suffix;
        }
    }

    private static String policy() {
        return "{"
                + "\"schemaVersion\":1,"
                + "\"profileId\":\"HDFS-11741-TEST\","
                + "\"workload\":\"example.Test#workload\","
                + "\"regions\":{"
                + regionSelector("target", "TARGET.ROOT", "TARGET.ANCHOR",
                "TARGET.METHOD") + ","
                + regionSelector("namenode", "NN.ROOT", "NN.ANCHOR",
                "REMOVE.METHOD") + ","
                + regionSelector("keyUpdater", "KU.ROOT", "KU.ANCHOR",
                "ADD.METHOD", "CACHE.METHOD") + ","
                + regionSelector("datanode", "DN.ROOT", "DN.ANCHOR",
                "ADD.METHOD", "REMOVE.METHOD") + ","
                + regionSelector("balancer", "BAL.ROOT", "BAL.ANCHOR",
                "CACHE.METHOD") + "},"
                + "\"replaySelection\":{\"schemaVersion\":1,"
                + "\"producerOutputs\":{"
                + producerOutput("namenode", "NN.MAP") + ","
                + producerOutput("keyUpdater", "KU.CURRENT.OUT") + ","
                + producerOutput("datanode", "DN.MAP") + ","
                + producerOutput("balancer", "BAL.SASL.USER") + "}},"
                + "\"ports\":{"
                + port("targetMap", "target", "symbolicInputs", "T.MAP")
                + "," + port("targetEncodedKey", "target",
                "symbolicInputs", "T.USER")
                + "," + port("targetFailure", "target", "outputs",
                "T.FAIL")
                + "," + port("namenodeMapPre", "namenode",
                "symbolicInputs", "NN.MAP")
                + "," + port("namenodeMapPost", "namenode", "outputs",
                "NN.MAP")
                + "," + port("namenodeExpiry", "namenode",
                "symbolicInputs", "KEY.EXPIRY")
                + "," + port("namenodeNow", "namenode",
                "symbolicInputs", "CLOCK.NOW")
                + "," + port("datanodeMapPre", "datanode",
                "symbolicInputs", "DN.MAP")
                + "," + port("datanodeMapPost", "datanode", "outputs",
                "DN.MAP")
                + "," + port("datanodeSnapshot", "datanode",
                "symbolicInputs", "DN.SNAPSHOT")
                + "," + port("datanodeEntryKey", "datanode",
                "symbolicInputs", "KEY.ID")
                + "," + port("datanodeEntryExpiry", "datanode",
                "symbolicInputs", "KEY.EXPIRY")
                + "," + port("datanodeNow", "datanode",
                "symbolicInputs", "CLOCK.NOW")
                + "," + port("keyUpdaterCurrentKey", "keyUpdater",
                "outputs", "KU.CURRENT.OUT")
                + "," + port("balancerCachedKey", "balancer",
                "symbolicInputs", "BAL.CACHED.KEY")
                + "," + port("balancerSaslUsername", "balancer",
                "outputs", "BAL.SASL.USER") + "},"
                + "\"transportBindings\":" + transportBindings() + ","
                + "\"targetGuard\":{\"siteId\":\"TARGET.METHOD#u8\","
                + "\"requiredOutcome\":false},"
                + "\"containerBindings\":{"
                + "\"keyId\":{\"schemaVersion\":1,"
                + "\"fieldPath\":[\"keyId\"],"
                + "\"declaredFieldSignature\":\"KEY.ID.FIELD\","
                + "\"materializationMode\":\"FIELD_ACCESS_HOOK\"},"
                + "\"expiry\":{\"schemaVersion\":2,"
                + "\"fieldPath\":[\"expiryDate\"],"
                + "\"declaredFieldSignature\":\"KEY.EXPIRY.FIELD\","
                + "\"materializationMode\":\"CONTAINER_SNAPSHOT\"}},"
                + "\"staticEvidence\":{"
                + "\"targetMethod\":\"TARGET.METHOD\","
                + "\"removeMethod\":\"REMOVE.METHOD\","
                + "\"structuredEncoding\":\"DECIMAL_KEY_ID_PREFIX\","
                + "\"requiredTargetEdgeKinds\":[\"map_lookup_state\","
                + "\"map_lookup_key\",\"exception_guard\","
                + "\"seed_exception_throw\"],"
                + "\"requiredRemoveEdgeKinds\":[\"field_mutation\","
                + "\"heap_mutation_path_guard\",\"call_return\","
                + "\"accessor_field_return\",\"local_def_use\"]},"
                + "\"runtimeEvidence\":{"
                + "\"saslKinds\":[\"SASL_TRANSFER\"],"
                + "\"sharedStateKinds\":[\"SHARED_STATE\"],"
                + "\"regionEdgeMappingKinds\":[\"snapshot\"]},"
                + "\"approximationPolicy\":{"
                + "\"allowOuterLoopSingleWitness\":true,"
                + "\"allowNnSnapshotFanout\":true,"
                + "\"allowPreFixCachePersistence\":true,"
                + "\"allowSaslCodecRoundTrip\":true,"
                + "\"allowMissingRuntimeEquality\":true,"
                + "\"outerLoopAuthority\":"
                + "\"CONFIGURED_BOUNDED_EXTERNAL_LOOP_PATH_PREFIX_V1\","
                + "\"allowedOuterLoopRootMethods\":[\"DN.ROOT\"]},"
                + "\"researchScope\":{\"repository\":\"fixture\"}}";
    }

    private static String regionSelector(String role, String root,
                                         String anchor,
                                         String... required) {
        StringBuilder result = new StringBuilder("\"").append(role)
                .append("\":{\"rootMethod\":\"").append(root)
                .append("\",\"anchorMethod\":\"").append(anchor)
                .append("\",\"requiredMethods\":[");
        for (int index = 0; index < required.length; index++) {
            if (index > 0) result.append(',');
            result.append('"').append(required[index]).append('"');
        }
        return result.append("]}").toString();
    }

    private static String port(String role, String region, String collection,
                               String cell) {
        return "\"" + role + "\":{\"region\":\"" + region
                + "\",\"collection\":\"" + collection
                + "\",\"cell\":\"" + cell + "\"}";
    }

    private static String producerOutput(String role, String cell) {
        return "\"" + role + "\":{\"cell\":\"" + cell + "\"}";
    }

    private static String transportBindings() {
        return "{\"schemaVersion\":1,\"authority\":"
                + "\"POLICY_DERIVED_HDFS_RPC_SNAPSHOT_BINDING_V1\","
                + "\"bindings\":[{\"bindingId\":"
                + "\"NN_SNAPSHOT_KEY_FANOUT\",\"source\":{"
                + "\"role\":\"namenode\",\"kind\":"
                + "\"UNIFORM_HEAP_EFFECT_EXPRESSION\","
                + "\"effectKind\":\"MAP_PUT\","
                + "\"expressionField\":\"keyExpression\","
                + "\"expectedSort\":\"Int\"},\"targets\":[{"
                + "\"role\":\"keyUpdater\",\"portAlias\":"
                + "\"keyUpdaterCurrentKey\",\"fieldPath\":[\"keyId\"],"
                + "\"declaredFieldSignature\":\"KEY.ID.FIELD\","
                + "\"expectedSort\":\"Int\"},{\"role\":\"datanode\","
                + "\"portAlias\":\"datanodeEntryKey\","
                + "\"expectedSort\":\"Int\"}],"
                + "\"includeSourcePathGuards\":true,"
                + "\"approximation\":\"CONFIGURED_NN_SNAPSHOT_FANOUT\"},"
                + "{\"bindingId\":\"NN_SNAPSHOT_EXPIRY_FANOUT\","
                + "\"source\":{\"role\":\"namenode\","
                + "\"kind\":\"PORT_ALIAS\","
                + "\"portAlias\":\"namenodeExpiry\","
                + "\"expectedSort\":\"Int\"},\"targets\":[{"
                + "\"role\":\"datanode\",\"portAlias\":"
                + "\"datanodeEntryExpiry\","
                + "\"expectedSort\":\"Int\"}],"
                + "\"includeSourcePathGuards\":true,"
                + "\"approximation\":"
                + "\"CONFIGURED_NN_SNAPSHOT_FANOUT\"}]}";
    }

    private static String regions() {
        String target = region("REGION.T", "TARGET.ROOT", "TARGET.ANCHOR",
                "[\"TARGET.METHOD\"]",
                "[{\"portId\":\"REGION.T.in.0\",\"cell\":\"T.MAP\"},"
                        + "{\"portId\":\"REGION.T.in.1\","
                        + "\"cell\":\"T.USER\"}]",
                "[{\"portId\":\"REGION.T.out.0\","
                        + "\"cell\":\"T.FAIL\"}]",
                ",\"branchPolicies\":[{\"siteId\":\"TARGET.METHOD#u8\","
                        + "\"requiredOutcome\":false}]");
        String nn = region("REGION.N", "NN.ROOT", "NN.ANCHOR",
                "[\"REMOVE.METHOD\"]",
                "[{\"portId\":\"REGION.N.in.0\",\"cell\":\"NN.MAP\"},"
                        + "{\"portId\":\"REGION.N.in.1\","
                        + "\"cell\":\"KEY.EXPIRY\"},"
                        + "{\"portId\":\"REGION.N.in.2\","
                        + "\"cell\":\"CLOCK.NOW\"}]",
                "[{\"portId\":\"REGION.N.out.0\","
                        + "\"cell\":\"NN.MAP\"}]",
                outputSlice("REGION.N.out.0", "NN.MAP"));
        String keyUpdater = region("REGION.K", "KU.ROOT", "KU.ANCHOR",
                "[\"ADD.METHOD\",\"CACHE.METHOD\"]",
                "[{\"portId\":\"REGION.K.in.0\","
                        + "\"cell\":\"KU.CURRENT.IN\"}]",
                "[{\"portId\":\"REGION.K.out.0\","
                        + "\"cell\":\"KU.CURRENT.OUT\"}]",
                outputSlice("REGION.K.out.0", "KU.CURRENT.OUT"));
        String dnExtra = ",\"outputSlices\":[{"
                + "\"outputPort\":\"REGION.D.out.0\","
                + "\"outputCell\":\"DN.MAP\","
                + "\"structuralComplete\":true,\"truncated\":false,"
                + "\"containerElementFieldBindings\":[{"
                + "\"schemaVersion\":1,\"kind\":\"ARRAY_ELEMENT_FIELD\","
                + "\"bindingId\":\"BIND.KEY\",\"complete\":true,"
                + "\"baseInputSymbol\":\"REGION.D.in.2\","
                + "\"containerInputPort\":\"REGION.D.in.1\","
                + "\"fieldPath\":[\"keyId\"],"
                + "\"declaredFieldSignature\":\"KEY.ID.FIELD\","
                + "\"materializationMode\":\"FIELD_ACCESS_HOOK\","
                + "\"proofCausalEdgeIds\":[\"K1\",\"K2\",\"K3\","
                + "\"K4\"]},{"
                + "\"schemaVersion\":2,\"kind\":\"ARRAY_ELEMENT_FIELD\","
                + "\"bindingId\":\"BIND.EXPIRY\",\"complete\":true,"
                + "\"baseInputSymbol\":\"REGION.D.in.3\","
                + "\"containerInputPort\":\"REGION.D.in.1\","
                + "\"fieldPath\":[\"expiryDate\"],"
                + "\"declaredFieldSignature\":\"KEY.EXPIRY.FIELD\","
                + "\"materializationMode\":\"CONTAINER_SNAPSHOT\","
                + "\"proofCausalEdgeIds\":[\"E1\",\"E2\",\"E3\","
                + "\"E4\",\"E5\"]}]}]";
        String dn = region("REGION.D", "DN.ROOT", "DN.ANCHOR",
                "[\"ADD.METHOD\",\"REMOVE.METHOD\"]",
                "[{\"portId\":\"REGION.D.in.0\",\"cell\":\"DN.MAP\"},"
                        + "{\"portId\":\"REGION.D.in.1\","
                        + "\"cell\":\"DN.SNAPSHOT\"},"
                        + "{\"portId\":\"REGION.D.in.2\","
                        + "\"cell\":\"KEY.ID\"},"
                        + "{\"portId\":\"REGION.D.in.3\","
                        + "\"cell\":\"KEY.EXPIRY\"},"
                        + "{\"portId\":\"REGION.D.in.4\","
                        + "\"cell\":\"CLOCK.NOW\"}]",
                "[{\"portId\":\"REGION.D.out.0\","
                        + "\"cell\":\"DN.MAP\"}]", dnExtra);
        String bal = region("REGION.B", "BAL.ROOT", "BAL.ANCHOR",
                "[\"CACHE.METHOD\"]",
                "[{\"portId\":\"REGION.B.in.0\","
                        + "\"cell\":\"BAL.CACHED.KEY\"}]",
                "[{\"portId\":\"REGION.B.out.0\","
                        + "\"cell\":\"BAL.SASL.USER\"}]",
                outputSlice("REGION.B.out.0", "BAL.SASL.USER"));
        return target + "\n" + nn + "\n" + keyUpdater + "\n"
                + dn + "\n" + bal + "\n";
    }

    private static String outputSlice(String port, String cell) {
        return ",\"outputSlices\":[{\"outputPort\":\"" + port
                + "\",\"outputCell\":\"" + cell
                + "\",\"structuralComplete\":true,"
                + "\"truncated\":false}]";
    }

    private static String region(String id, String root, String anchor,
                                 String methods, String inputs,
                                 String outputs, String extra) {
        return "{\"regionId\":\"" + id + "\",\"rootMethod\":\""
                + root + "\",\"anchorMethod\":\"" + anchor
                + "\",\"methods\":" + methods + ",\"symbolicInputs\":"
                + inputs + ",\"outputs\":" + outputs
                + ",\"truncated\":false" + extra + "}";
    }

    private static String staticGraph() {
        StringBuilder result = new StringBuilder();
        int index = 0;
        for (String kind : new String[]{"map_lookup_state",
                "map_lookup_key", "exception_guard",
                "seed_exception_throw"}) {
            result.append(edge("T" + index++, "TARGET.METHOD", kind, ""));
        }
        index = 0;
        for (String kind : new String[]{"field_mutation",
                "heap_mutation_path_guard", "call_return",
                "accessor_field_return", "local_def_use"}) {
            result.append(edge("R" + index++, "REMOVE.METHOD", kind, ""));
        }
        for (String id : new String[]{"K1", "K2", "K3", "K4", "E1",
                "E2", "E3", "E4", "E5"}) {
            result.append(edge(id, "ADD.METHOD", "proof", ""));
        }
        result.append(edge("ENC", "ENCODE.METHOD",
                "structured_scalar_encoding_dependency",
                ",\"structuredEncoding\":\"DECIMAL_KEY_ID_PREFIX\""));
        return result.toString();
    }

    private static String edge(String id, String method, String kind,
                               String extra) {
        return "{\"id\":\"" + id + "\",\"method\":\"" + method
                + "\",\"kind\":\"" + kind + "\",\"fromCell\":\"A\","
                + "\"toCell\":\"B\"" + extra + "}\n";
    }

    private static String regionEdges() {
        return "{\"edgeId\":\"RE.0\",\"fromRegion\":\"REGION.N\","
                + "\"toRegion\":\"REGION.D\",\"mappingKind\":"
                + "\"snapshot\",\"kind\":\"RPC_RETURN\"}\n";
    }

    private static String runtimeEdges() {
        return "{\"edgeId\":\"RT.SASL\",\"fromRegion\":\"REGION.B\","
                + "\"toRegion\":\"REGION.T\",\"kind\":"
                + "\"SASL_TRANSFER\",\"mappingKind\":"
                + "\"SASL_TRANSFER\",\"status\":"
                + "\"CONFIRMED_RUNTIME_VALUE_EQUALITY\","
                + "\"validation\":"
                + "\"COMPLETE_ENDPOINT_VALUE_FINGERPRINT_EQUALITY\","
                + "\"producerRegionUniquelyConfirmed\":true,"
                + "\"valueEqualityAuthority\":"
                + "\"RUNTIME_COMPLETE_VALUE_FINGERPRINT\","
                + "\"endpointOrderAuthority\":"
                + "\"GLOBAL_TRACE_ENDPOINT_SEQUENCE\","
                + "\"confirmedValueEqualityPairCount\":1,"
                + "\"validatedBindings\":[{\"fromRegionInstance\":"
                + "\"REGION.B@fixture#call40\","
                + "\"toRegionInstance\":\"REGION.T@fixture#call41\","
                + "\"test\":\"example.Test#workload\","
                + "\"orderConfirmed\":true,"
                + "\"valueEqualityObserved\":true,"
                + "\"valueFingerprint\":\"sha256:"
                + "0000000000000000000000000000000000000000000000000000000000000000\","
                + "\"valueEqualityAuthority\":"
                + "\"RUNTIME_COMPLETE_VALUE_FINGERPRINT\","
                + "\"endpointOrderAuthority\":"
                + "\"GLOBAL_TRACE_ENDPOINT_SEQUENCE\","
                + "\"endpointCorrelationAuthority\":"
                + "\"NEAREST_PRECEDING_SOURCE_ROOT_THEN_ENDPOINT\","
                + "\"fromEndpointSeq\":400,\"toEndpointSeq\":410}]}\n"
                + "{\"edgeId\":\"RT.MAP\",\"fromRegion\":\"REGION.D\","
                + "\"toRegion\":\"REGION.T\",\"kind\":"
                + "\"SHARED_STATE\",\"status\":\"CONFIRMED_READ_FROM\","
                + "\"confirmedReadFromPairCount\":1}\n";
    }

    private static String activations() {
        StringBuilder result = new StringBuilder();
        result.append(activation("ACT.TARGET.BEFORE", "REGION.T",
                "TARGET.ROOT", 5, 1, ""));
        result.append(activation("ACT.NN.EARLY", "REGION.N", "NN.ROOT",
                10, 1, ""));
        result.append(activation("ACT.DN.EARLY", "REGION.D", "DN.ROOT",
                11, 1, ""));
        result.append(activation("ACT.NN.LATEST", "REGION.N", "NN.ROOT",
                20, 2, ""));
        result.append(activation("ACT.DN.LATEST", "REGION.D", "DN.ROOT",
                21, 2, ""));
        // A derived output-closure activation shares the exact runtime root;
        // the semantic timeline selector must retain the frozen base row.
        result.append(activation("ACT.DN.DERIVED", "REGION.D", "DN.ROOT",
                21, 2, "ACT.DN.LATEST"));
        // This is before KeyUpdater but after the selected DN snapshot.  NN
        // must be bounded by DN, not merely by the later updater pivot.
        result.append(activation("ACT.NN.AFTER.DN", "REGION.N", "NN.ROOT",
                25, 3, ""));
        result.append(activation("ACT.KU", "REGION.K", "KU.ROOT",
                30, 1, ""));
        result.append(activation("ACT.BAL.FIRST", "REGION.B", "BAL.ROOT",
                40, 1, ""));
        result.append(activation("ACT.TARGET.FIRST.AFTER", "REGION.T",
                "TARGET.ROOT", 41, 2, ""));
        result.append(activation("ACT.BAL.LATE", "REGION.B", "BAL.ROOT",
                50, 2, ""));
        result.append(activation("ACT.TARGET.LATE", "REGION.T",
                "TARGET.ROOT", 51, 3, ""));
        return result.toString();
    }

    private static String activation(String activation, String region,
                                     String root, int call, int ordinal,
                                     String derivedFrom) {
        return "{\"activationId\":\"" + activation
                + "\",\"regionId\":\"" + region
                + "\",\"regionInstanceId\":\"" + region
                + "@fixture#call" + call + "\",\"rootCallId\":" + call
                + ",\"invocationOrdinal\":" + ordinal
                + ",\"rootMethod\":\"" + root
                + "\",\"observedRootMethod\":\"" + root
                + "\",\"staticRootMethod\":\"" + root
                + "\",\"anchorObserved\":true,\"test\":"
                + "\"example.Test#workload\""
                + ("REGION.T".equals(region)
                ? ",\"branches\":[{\"siteId\":\"TARGET.METHOD#u8\","
                + "\"observed\":true,\"requiredOutcome\":false}]" : "")
                + (derivedFrom.isEmpty() ? "" : ",\"derivedFromActivationId\":\""
                + derivedFrom + "\"") + "}\n";
    }

    private static String replaySummaries() {
        return namenodeReplaySummary()
                + replaySummary("REGION.K", "KU.ROOT", "REGION.K.in.0",
                "REGION.K.out.0")
                + replaySummary("REGION.D", "DN.ROOT", "REGION.D.in.3",
                "REGION.D.out.0")
                + replaySummary("REGION.B", "BAL.ROOT", "REGION.B.in.0",
                "REGION.B.out.0")
                + replaySummary("REGION.T", "TARGET.ROOT", "ENGINE.TARGET.KEY",
                "REGION.T.out.0");
    }

    private static String namenodeReplaySummary() {
        String base = replaySummary("REGION.N", "NN.ROOT",
                "REGION.N.in.1", "REGION.N.out.0").replace(
                "M_I_field_REGION.N.in.1_fixture", "NN.SNAPSHOT.KEY");
        String effect = ",\"heapEffects\":[{\"kind\":\"MAP_PUT\","
                + "\"keyExpression\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"java/lang/Integer\","
                + "\"_exp\":\"NN.SNAPSHOT.KEY\"}}]";
        return base.substring(0, base.length() - 2) + effect + "}\n";
    }

    private static String targetQuery() {
        String symbol = "M_I_field_ENGINE.TARGET.KEY_fixture";
        String original = "{\"_type\":\"BinaryExpression\","
                + "\"_left\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"I\",\"_exp\":\"" + symbol
                + "\"},\"_op\":\"<\",\"_right\":{\"_type\":"
                + "\"ConstExpr\",\"_java_type\":\"I\","
                + "\"_exp\":\"Y_I_7\"}}";
        String negated = original.replace("\"_op\":\"<\"",
                "\"_op\":\">=\"");
        return "{\"activationId\":\"ACT.REGION.T\","
                + "\"regionId\":\"REGION.T\","
                + "\"regionInstanceId\":\"INSTANCE.TARGET\","
                + "\"siteId\":\"TARGET.METHOD#u8\","
                + "\"occurrence\":1,\"observedOutcome\":true,"
                + "\"desiredOutcome\":false,\"conditionIndex\":0,"
                + "\"prefixPolicy\":\"KEEP_CONDITIONS_BEFORE_TARGET\","
                + "\"targetPolicy\":\"NEGATE_TARGET_CONDITION\","
                + "\"suffixPolicy\":\"DROP_OLD_SUFFIX\","
                + "\"readyForSolver\":true,\"readyForReplay\":true,"
                + "\"targetReplayValidated\":false,"
                + "\"originalTargetCondition\":" + original + ","
                + "\"negatedTargetCondition\":" + negated + ","
                + "\"constraints\":[" + negated + "],"
                + "\"semanticModel\":{\"status\":\"SAT\","
                + "\"theory\":\"MAP_LOOKUP_ABSENCE\","
                + "\"keyExpression\":{\"_type\":"
                + "\"SymbolExpression\",\"_java_type\":\"I\","
                + "\"_exp\":\"" + symbol + "\"}}}\n";
    }

    private static String replaySummary(String region, String root,
                                        String input, String output) {
        String symbol = "M_I_field_" + input + "_fixture";
        return "{\"summaryId\":\"SUMMARY." + region + "\","
                + "\"activationId\":\"ACT." + region + "\","
                + "\"regionId\":\"" + region + "\","
                + "\"rootMethod\":\"" + root + "\","
                + "\"engine\":\"fixture-concolic\","
                + "\"valid\":true,\"relationallyComplete\":true,"
                + "\"normalExit\":true,"
                + "\"pathCondition\":[{\"_type\":"
                + "\"BinaryExpression\",\"_left\":{\"_type\":"
                + "\"SymbolExpression\",\"_java_type\":\"I\","
                + "\"_exp\":\"" + symbol + "\"},\"_op\":\"<\","
                + "\"_right\":{\"_type\":\"ConstExpr\","
                + "\"_java_type\":\"I\",\"_exp\":\"Y_I_7\"}}],"
                + "\"outputExpressions\":{\"" + output + "\":{"
                + "\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"I\",\"_exp\":\"" + symbol
                + "\"}}}\n";
    }

    private static void write(Path path, String value) throws Exception {
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] hash = digest.digest(Files.readAllBytes(path));
        StringBuilder result = new StringBuilder();
        for (byte value : hash) result.append(String.format("%02x",
                value & 0xff));
        return result.toString();
    }
}
