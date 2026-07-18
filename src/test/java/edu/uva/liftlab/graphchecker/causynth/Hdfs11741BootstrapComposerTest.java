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
        assertEquals(1, result.manifest.getAsJsonObject(
                "supplementalEvidence").get("replaySummaryCount")
                .getAsInt());

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
        assertFalse("the iterator key must not be a workload constant",
                smt.contains("dn_iterator_key_id 1005215027"));
    }

    @Test
    public void missingRuntimeRelationsRemainExplicitApproximations()
            throws Exception {
        Fixture fixture = new Fixture(folder.getRoot().toPath(), false);

        Hdfs11741BootstrapComposer.Result result =
                Hdfs11741BootstrapComposer.compose(fixture.arguments(false));

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
            Hdfs11741BootstrapComposer.compose(fixture.arguments(false));
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
            Hdfs11741BootstrapComposer.compose(fixture.arguments(false));
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
            Hdfs11741BootstrapComposer.compose(fixture.arguments(false));
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
        private final Path replaySummary;
        private final Path output;
        private final Path manifest;

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
            replaySummary = root.resolve(unique("replay.jsonl"));
            output = root.resolve(unique("bootstrap.smt2"));
            manifest = root.resolve(unique("manifest.json"));
            write(policy, policy());
            write(regions, regions());
            write(staticGraph, staticGraph());
            write(regionEdges, regionEdges());
            write(runtimeEdges, runtimeConfirmed ? runtimeEdges() : "");
            write(runtimeSummary, "{\"schemaVersion\":1,"
                    + "\"staticRegionCount\":4,"
                    + "\"staticRegionEdgeCount\":1,"
                    + "\"runtimeRegionInstanceCount\":4,"
                    + "\"runtimeRegionEdgeValidationCount\":2,"
                    + "\"activationCount\":4,"
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
            write(replaySummary, "{\"summaryId\":\"OPTIONAL.REPLAY\","
                    + "\"relationallyComplete\":false}\n");
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
            if (includeReplay) add(values, "--replay-summary",
                    replaySummary);
            add(values, "--output", output);
            add(values, "--manifest", manifest);
            return Hdfs11741BootstrapComposer.Arguments.parse(
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
                + regionSelector("datanode", "DN.ROOT", "DN.ANCHOR",
                "ADD.METHOD", "REMOVE.METHOD") + ","
                + regionSelector("balancer", "BAL.ROOT", "BAL.ANCHOR",
                "CACHE.METHOD") + "},"
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
                + "," + port("balancerCachedKey", "balancer",
                "symbolicInputs", "BAL.CACHED.KEY")
                + "," + port("balancerSaslUsername", "balancer",
                "outputs", "BAL.SASL.USER") + "},"
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
                        + "\"cell\":\"NN.MAP\"}]", "");
        String dnExtra = ",\"outputSlices\":[{"
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
                        + "\"cell\":\"BAL.SASL.USER\"}]", "");
        return target + "\n" + nn + "\n" + dn + "\n" + bal + "\n";
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
                + "\"SASL_TRANSFER\",\"status\":"
                + "\"CONFIRMED_VALUE_EQUALITY\","
                + "\"confirmedValueEqualityPairCount\":1}\n"
                + "{\"edgeId\":\"RT.MAP\",\"fromRegion\":\"REGION.D\","
                + "\"toRegion\":\"REGION.T\",\"kind\":"
                + "\"SHARED_STATE\",\"status\":\"CONFIRMED_READ_FROM\","
                + "\"confirmedReadFromPairCount\":1}\n";
    }

    private static String activations() {
        StringBuilder result = new StringBuilder();
        int call = 10;
        for (String id : new String[]{"REGION.T", "REGION.N", "REGION.D",
                "REGION.B"}) {
            result.append("{\"activationId\":\"ACT.").append(id)
                    .append("\",\"regionId\":\"").append(id)
                    .append("\",\"regionInstanceId\":\"").append(id)
                    .append("@fixture#call").append(call)
                    .append("\",\"rootCallId\":").append(call++)
                    .append(",\"test\":\"example.Test#workload\"}\n");
        }
        return result.toString();
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
