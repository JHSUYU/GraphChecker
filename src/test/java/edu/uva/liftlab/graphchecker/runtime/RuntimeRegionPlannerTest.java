package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeRegionPlannerTest {
    private static final String HANDLE = "<example.Handler: void handle(java.lang.Object[])>";
    private static final String IDENTIFIER = "<example.Handler: example.Token getIdentifier(java.lang.String)>";
    private static final String PASSWORD = "<example.Handler: char[] getPassword(example.Token)>";
    private static final String RETRIEVE = "<example.Manager: byte[] retrievePassword(example.Token)>";
    private static final String SASL_CLIENT =
            "<example.SaslClient: void doSaslHandshake(java.lang.String)>";
    private static final String SASL_SERVER =
            "<example.SaslServerCallbackHandler: void handle(java.lang.Object[])>";
    private static final String NAME_CALLBACK_DEFAULT =
            "<javax.security.auth.callback.NameCallback: java.lang.String getDefaultName()>";

    private static void assertDeferredInputReady(
            String cell, String sourceKind, String location,
            String authority) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.DEFER\","
                    + "\"rootMethod\":\"" + HANDLE
                    + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.DEFER.in.0\",\"cell\":\"" + cell
                    + "\",\"sourceKind\":\"" + sourceKind
                    + "\",\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            writeRegions(regions, row.getBytes(StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), null,
                    companionStaticGraph(regions).toFile(),
                    Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());
            assertEquals("READY",
                    admissionState(result.activations.get(0)));
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    result.activations.get(0).get("symbolize")).get(0);
            assertEquals(location, action.get("location"));
            assertEquals(Boolean.TRUE, action.get("deferredResolution"));
            assertEquals(authority,
                    action.get("deferredResolutionAuthority"));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result planArrayFieldRead(
            boolean repeated, boolean receiverIsRoot) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String method = "<example.ArrayReader: void run()>";
            String field = "<example.ArrayState: example.Value[] allKeys>";
            String row = "{\"regionId\":\"REGION.ARRAY\","
                    + "\"rootMethod\":\"" + method + "\","
                    + "\"anchorMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + method + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.ARRAY.in.0\",\"cell\":\"" + field
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            writeRegions(regions, row.getBytes(StandardCharsets.UTF_8));
            int receiver = receiverIsRoot ? 42 : 91;
            List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                    new ArrayList<>();
            fields.add(exactFieldRead(2, method, 1, 7, field, receiver,
                    701));
            if (repeated) {
                fields.add(exactFieldRead(3, method, 1, 7, field, receiver,
                        701));
            }
            return RuntimeRegionPlanner.plan(regions.toFile(), null,
                    companionStaticGraph(regions).toFile(),
                    Collections.singletonList(methodContext(1, method, 1,
                            "PROCESS", "reader", 55L)),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    fields);
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.FieldAccessEvent exactFieldRead(
            long seq, String method, long callId, int unitIndex,
            String field, int receiverObjectId, int valueObjectId) {
        return new RuntimeRegionPlanner.FieldAccessEvent(seq,
                "FIELD_READ", method, callId, unitIndex,
                method + "#u" + unitIndex, field, receiverObjectId,
                valueObjectId, "", "fp", true, 1, "");
    }

    @Test
    public void derivesOutputClosureActivationFromConfirmedReadFrom()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            Path graph = folder.getRoot().toPath().resolve(
                    "static_dataflow_edges.jsonl");
            String updater = "<example.Updater: void run()>";
            String reader = "<example.Reader: void handle()>";
            String absentAnchor = "<example.Updater: void fatalAnchor()>";
            String field = "<example.State: java.util.Map entries>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + updater + "\","
                    + "\"anchorMethod\":\"" + absentAnchor + "\","
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.W.in.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:entries\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + field + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\"],"
                    + "\"inputBindings\":[{"
                    + "\"dependencyCell\":\"<example.Request: int key>\","
                    + "\"inputPort\":\"REGION.W.in.0\","
                    + "\"bindingAuthority\":"
                    + "\"UNIQUE_ROOT_ARGUMENT_CARRIER\","
                    + "\"requestedStateTransformerSinkSites\":[\""
                    + updater + "#u15\"],"
                    + "\"requestedStateTransformerGuardSites\":[\""
                    + updater + "#u14\"],"
                    + "\"requestedStateTransformerSinkClosureComplete\":true,"
                    + "\"requestedStateTransformerSinkExclusive\":true,"
                    + "\"requestedStateTransformerUnclassifiedEdgeIds\":[],"
                    + "\"requestedStateTransformerSinkAuthority\":"
                    + "\"STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_REQUESTED_STATE_TRANSFORMERS\"}],"
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[\"DF.1\","
                    + "\"DF.WRITE\"],"
                    + "\"causalEdges\":[{"
                    + "\"edgeId\":\"DF.1\","
                    + "\"method\":\"" + updater + "\","
                    + "\"siteId\":\"" + updater + "#u6\","
                    + "\"transferKind\":\"GUARD\","
                    + "\"kind\":\"heap_mutation_path_guard\","
                    + "\"guardSiteId\":\"" + updater + "#u6\","
                    + "\"guardedMutationSiteId\":\"" + updater + "#u15\","
                    + "\"requiredOutcome\":false,"
                    + "\"guardedMutationCount\":1,"
                    + "\"guardedMutationsAuthority\":\"STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE\","
                    + "\"guardedMutations\":[{"
                    + "\"guardSiteId\":\"" + updater + "#u6\","
                    + "\"guardedMutationSiteId\":\"" + updater + "#u15\","
                    + "\"method\":\"" + updater + "\","
                    + "\"unitIndex\":15,"
                    + "\"requiredOutcome\":false}]},{"
                    + "\"edgeId\":\"DF.WRITE\","
                    + "\"method\":\"" + updater + "\","
                    + "\"siteId\":\"" + updater + "#u15\","
                    + "\"fromCell\":\"" + updater + "::key\","
                    + "\"toCell\":\"" + field + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"invoke\":\"<java.util.Iterator: void remove()>\"}],"
                    + "\"requestedStateTransformerContractVersion\":1,"
                    + "\"requestedStateTransformerContractApplicable\":true,"
                    + "\"requestedStateTransformerContractOutputPort\":"
                    + "\"REGION.W.out.0\","
                    + "\"requestedStateTransformerContractOutputCell\":"
                    + "\"" + field + "\","
                    + "\"requestedStateTransformerObligations\":[{"
                    + "\"siteId\":\"" + updater + "#u15\","
                    + "\"method\":\"" + updater + "\","
                    + "\"targetCell\":\"" + field + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.WRITE\"],"
                    + "\"authority\":\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL\"}],"
                    + "\"requestedStateTransformerObligationCount\":1,"
                    + "\"requestedStateTransformerContractIssues\":[],"
                    + "\"requestedStateTransformerContractComplete\":true,"
                    + "\"requestedStateTransformerContractAuthority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1\","
                    + "\"heapInitializers\":[{"
                    + "\"initializerId\":\"STATIC_INIT.REGION.W.0\","
                    + "\"kind\":\"FRESH_DEFAULT_CONSTRUCTED_OBJECT\","
                    + "\"allocatedType\":\"java.util.HashMap\","
                    + "\"constructorArgumentCount\":0,"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + field + "\","
                    + "\"proofEdgeIds\":[\"DF.1\"],"
                    + "\"proofComplete\":true}],"
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":true,"
                    + "\"captureBindings\":[{"
                    + "\"captureKind\":\"FIELD_ASSIGNMENT_RHS\","
                    + "\"captureBindingId\":\"REGION.W.out.0.capture.0\","
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + field + "\","
                    + "\"method\":\"" + updater + "\","
                    + "\"siteId\":\"" + updater + "#u15\","
                    + "\"unitIndex\":15,"
                    + "\"unit\":\"r0." + field + " = key\","
                    + "\"fieldSignature\":\"" + field + "\","
                    + "\"fieldOwnerExpression\":\"r0\","
                    + "\"fieldOwnerCell\":\"" + updater + "::r0\","
                    + "\"fieldOwnerDeclaredType\":\"example.State\","
                    + "\"fieldOwnerBindingKind\":\"INSTANCE_FIELD_LHS_BASE\","
                    + "\"fieldOwnerBindingAuthority\":\"STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS\","
                    + "\"rhsExpression\":\"key\","
                    + "\"rhsCell\":\"" + updater + "::key\","
                    + "\"rhsCausalEdgeId\":\"DF.WRITE\","
                    + "\"rhsRelation\":\"value_flow\","
                    + "\"rhsRelationComplete\":true,"
                    + "\"rhsRelationAuthority\":\"STATIC_EXACT_HEAP_WRITE_VALUE_FLOW\","
                    + "\"causalEdgeId\":\"DF.WRITE\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"bindingKind\":\"field_write\","
                    + "\"bindingAuthority\":\"STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS\","
                    + "\"occurrence\":0}],"
                    + "\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}"
                    + System.lineSeparator();
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.R.in.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:entries\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}"
                    + System.lineSeparator();
            JsonObject compactWriter = JsonParser.parseString(writerRegion)
                    .getAsJsonObject();
            compactWriter.addProperty("schemaVersion", 2);
            JsonObject compactSlice = compactWriter
                    .getAsJsonArray("outputSlices").get(0)
                    .getAsJsonObject();
            JsonArray embedded = compactSlice.getAsJsonArray("causalEdges");
            StringBuilder canonicalGraph = new StringBuilder();
            for (JsonElement element : embedded) {
                JsonObject canonical = element.getAsJsonObject().deepCopy();
                String id = canonical.remove("edgeId").getAsString();
                canonical.addProperty("id", id);
                canonical.addProperty("canonicalCatalogMarker", true);
                canonicalGraph.append(canonical).append('\n');
            }
            compactSlice.remove("causalEdges");
            writerRegion = compactWriter + System.lineSeparator();
            writeRegions(regions, (writerRegion + readerRegion)
                    .getBytes(StandardCharsets.UTF_8));
            writeStaticGraph(graph, canonicalGraph.toString().getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.PRODUCER\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + field + "\","
                    + "\"toPort\":\"" + field + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}"
                    + System.lineSeparator();
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(4,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(2, "FIELD_WRITE",
                            updater, 11, field, 77, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(5, "FIELD_READ",
                            reader, 22, field, 77, 88, "");
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(), graph.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(write, read));

            assertEquals(3, result.activations.size());
            Map<String, Object> upstream = result.activations.get(2);
            Map<String, Object> captureGoal = (Map<String, Object>)
                    upstream.get("captureGoal");
            assertEquals("OUTPUT_CLOSURE", captureGoal.get("kind"));
            assertEquals("READY", admissionState(upstream));
            assertFalse(upstream.containsKey("requestedOutputSliceComplete"));
            assertEquals(11L, upstream.get("rootCallId"));
            assertEquals(1, ((List<?>) upstream.get("edgeBindings")).size());
            assertCanonicalOutputOnly(upstream);
            @SuppressWarnings("unchecked")
            Map<String, Object> retainedSlice = outputSlice(
                    upstream, "REGION.W.out.0");
            @SuppressWarnings("unchecked")
            Map<String, Object> retainedOutput = (Map<String, Object>)
                    outputMember(upstream, "REGION.W.out.0").get("output");
            assertEquals(field, retainedOutput.get("cell"));
            assertEquals(1, ((java.util.List<?>) upstream.get(
                    "heapStateBindings")).size());
            assertEquals(1, ((java.util.List<?>) upstream.get(
                    "symbolize")).size());
            assertEquals(true, retainedSlice.get(
                    "captureBindingsComplete"));
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> outputCaptures =
                    (List<Map<String, Object>>) retainedSlice.get(
                            "captureBindings");
            assertEquals(1, outputCaptures.size());
            assertEquals(1, outputCaptures.get(0).get("occurrence"));
            assertEquals("FIELD_ASSIGNMENT_RHS",
                    outputCaptures.get(0).get("captureKind"));
            assertEquals(updater + "#u15",
                    outputCaptures.get(0).get("siteId"));
            assertEquals(field,
                    outputCaptures.get(0).get("fieldSignature"));
            assertEquals(77,
                    outputCaptures.get(0).get(
                            "runtimeFieldOwnerObjectId"));
            assertEquals("RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_"
                            + "SITE_LAST_WRITE_OCCURRENCE",
                    outputCaptures.get(0).get("occurrenceAuthority"));
            assertEquals(Boolean.TRUE,
                    outputCaptures.get(0).get("rhsRelationComplete"));
            assertEquals(Collections.singletonList(updater),
                    retainedSlice.get("methods"));
            assertEquals(true, retainedSlice.get("complete"));
            assertTrue(String.valueOf(retainedSlice.get("inputBindings"))
                    .contains("UNIQUE_ROOT_ARGUMENT_CARRIER"));
            assertTrue(String.valueOf(retainedSlice.get("heapInitializers"))
                    .contains("FRESH_DEFAULT_CONSTRUCTED_OBJECT"));
            assertEquals(2, retainedSlice.get("causalEdgeCount"));
            assertEquals(1, retainedSlice.get(
                    "requestedStateTransformerContractVersion"));
            assertEquals(true, retainedSlice.get(
                    "requestedStateTransformerContractComplete"));
            assertEquals(1, retainedSlice.get(
                    "requestedStateTransformerObligationCount"));
            assertTrue(String.valueOf(retainedSlice.get(
                    "requestedStateTransformerObligations")).contains(
                    updater + "#u15"));
            assertTrue(String.valueOf(retainedSlice.get("inputBindings"))
                    .contains("requestedStateTransformerSinkSites=["
                            + updater + "#u15]"));
            assertTrue(String.valueOf(retainedSlice.get("inputBindings"))
                    .contains("requestedStateTransformerGuardSites=["
                            + updater + "#u14]"));
            assertTrue(String.valueOf(retainedSlice.get("causalEdges"))
                    .contains("STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE"));
            assertTrue(String.valueOf(retainedSlice.get("causalEdges"))
                    .contains("guardedMutationSiteId=" + updater + "#u15"));
            assertTrue(String.valueOf(retainedSlice.get("causalEdges"))
                    .contains("invoke=<java.util.Iterator: void remove()>"));
            assertTrue(result.activationsJsonl().contains(
                    "\"fromOutputPort\":\"REGION.W.out.0\""));
            assertTrue(result.activationsJsonl().contains(
                    "\"toInputPort\":\"REGION.R.in.0\""));
            @SuppressWarnings("unchecked")
            Map<String, Object> edgeBinding =
                    ((List<Map<String, Object>>) upstream.get(
                            "edgeBindings")).get(0);
            assertEquals(field, edgeBinding.get("rawToInputCell"));
            assertEquals(Boolean.TRUE, edgeBinding.get(
                    "canonicalInputResolutionUsed"));
            assertEquals("UNIQUE_EXACT_TARGET_REGION_SYMBOLIC_INPUT_CELL_V1",
                    edgeBinding.get("canonicalInputResolutionAuthority"));
            assertTrue(result.activationsJsonl().contains(
                    "\"writerEventSeq\":2"));
            assertEquals(1, derivedActivationCount(result));

            // The same compact row must fail closed when even one referenced
            // canonical edge is absent.
            String firstCanonicalRow = canonicalGraph.toString()
                    .split("\\n")[0] + "\n";
            writeStaticGraph(graph, firstCanonicalRow.getBytes(
                    StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result missingEdge =
                    RuntimeRegionPlanner.plan(regions.toFile(),
                            edges.toFile(), graph.toFile(),
                            Arrays.asList(writeRoot, readRoot),
                            Collections.<RuntimeRegionPlanner.RuntimeEvent>
                                    emptyList(),
                            Arrays.asList(write, read));
            assertEquals("DISCOVERED",
                    admissionState(missingEdge.activations.get(2)));
            assertFalse(missingEdge.activations.get(2).containsKey(
                    "requestedOutputSlice"));
            assertFalse(missingEdge.activations.get(2).containsKey(
                    "outputClosure"));
            assertTrue(String.valueOf(missingEdge.activations.get(2).get(
                    "outputClosureIssues")).contains(
                    "OUTPUT_MEMBER_INCOMPLETE"));
            assertTrue(String.valueOf(missingEdge.warnings).contains(
                    "STATIC_CAUSAL_EDGE_ID_UNRESOLVED:DF.WRITE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void groupsJointPrimitiveDemandAndIsolatesOtherConsumer()
            throws Exception {
        RuntimeRegionPlanner.Result result = jointPrimitiveDemandResult(
                false);
        List<Map<String, Object>> derived = derivedActivations(result);
        assertEquals(2, derived.size());

        Map<String, Object> joint = upstreamDemandFor(
                derived, "REGION.DXY");
        assertCanonicalOutputOnly(joint);
        assertEquals("READY", admissionState(joint));
        assertEquals(2, ((List<?>) outputClosure(joint).get(
                "members")).size());
        assertEquals("<example.State: int x>",
                ((Map<?, ?>) outputMember(joint,
                        "REGION.P.out.x").get("output")).get("cell"));
        assertEquals("<example.State: int y>",
                ((Map<?, ?>) outputMember(joint,
                        "REGION.P.out.y").get("output")).get("cell"));
        assertEquals(Boolean.TRUE, outputSlice(joint,
                "REGION.P.out.x").get("captureBindingsComplete"));
        assertEquals(Boolean.TRUE, outputSlice(joint,
                "REGION.P.out.y").get("captureBindingsComplete"));
        assertEquals(2, ((List<?>) joint.get("symbolize")).size());
        assertEquals(2, ((List<?>) joint.get("branches")).size());
        // E.X.1 and E.X.2 deliberately fan out the same output within the
        // same demand; E.Y contributes the second output member.
        assertEquals(Arrays.asList("E.X.1", "E.X.2", "E.Y"),
                edgeBindingIds(joint));

        Map<String, Object> isolated = upstreamDemandFor(
                derived, "REGION.DX");
        assertCanonicalOutputOnly(isolated);
        assertEquals(1, ((List<?>) outputClosure(isolated).get(
                "members")).size());
        assertEquals("REGION.P.out.x",
                ((Map<?, ?>) outputMember(isolated,
                        "REGION.P.out.x").get("output")).get("portId"));
        assertEquals(Collections.singletonList("E.X.DX"),
                edgeBindingIds(isolated));
    }

    @Test
    public void incompleteJointMemberFailsWholeDemandWithoutSingletonFallback()
            throws Exception {
        RuntimeRegionPlanner.Result result = jointPrimitiveDemandResult(
                true);
        List<Map<String, Object>> derived = derivedActivations(result);
        assertEquals(2, derived.size());

        Map<String, Object> rejected = upstreamDemandFor(
                derived, "REGION.DXY");
        assertEquals("DISCOVERED", admissionState(rejected));
        assertFalse(rejected.containsKey("outputClosure"));
        assertFalse(rejected.containsKey("requestedOutput"));
        assertFalse(rejected.containsKey("requestedOutputSlice"));
        assertTrue(String.valueOf(rejected.get("outputClosureIssues"))
                .contains("OUTPUT_MEMBER_INCOMPLETE:REGION.P.out.y"));
        assertEquals(3, ((List<?>) rejected.get("edgeBindings")).size());

        // The unrelated D{x} demand remains independently usable.
        Map<String, Object> isolated = upstreamDemandFor(
                derived, "REGION.DX");
        assertCanonicalOutputOnly(isolated);
        assertEquals("READY", admissionState(isolated));
        assertEquals(1, ((List<?>) outputClosure(isolated).get(
                "members")).size());
    }

    @Test
    public void refinesOutputClosureToObservedRuntimeAlternative()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String constructor = "<example.State: void <init>()>";
            String updater = "<example.State: void merge(example.Payload)>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.State: java.util.Map allKeys>";
            String payload =
                    "<example.Payload: java.lang.Object allKeys>";
            String alternative =
                    "<example.ConstructorSeed: java.lang.Object allKeys>";
            String unresolvedAlternative = alternative
                    + " [output slice input has no region port]";
            String updaterSite = updater + "#u3";
            String runtimeBranch = updater + "#u4";
            String unobservedBranch = updater + "#u15";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + constructor + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + constructor + "\",\""
                    + updater + "\"],\"symbolicInputs\":["
                    + "{\"portId\":\"REGION.W.in.0\",\"cell\":\""
                    + state + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"},"
                    + "{\"portId\":\"REGION.W.in.1\",\"cell\":\""
                    + payload + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"},"
                    + "{\"portId\":\"REGION.W.in.2\",\"cell\":\""
                    + alternative
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\","
                    + "\"REGION.W.in.1\",\"REGION.W.in.2\"],"
                    + "\"inputBindings\":["
                    + sliceBinding(state, "REGION.W.in.0", updater) + ","
                    + sliceBinding(payload, "REGION.W.in.1", updater) + ","
                    + sliceBinding(alternative, "REGION.W.in.2",
                    constructor) + "],"
                    + "\"methods\":[\"" + constructor + "\",\""
                    + updater + "\"],\"sites\":[\"" + constructor
                    + "#u1\",\"" + updaterSite + "\",\""
                    + unobservedBranch + "\"],"
                    + "\"causalEdgeIds\":[\"DF.C\",\"DF.U\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.C", constructor,
                    constructor + "#u1") + ","
                    + causalReference("DF.U", updater, updaterSite) + "],"
                    + "\"structuralComplete\":true,"
                    // Broad-region truncation is diagnostic once the output
                    // slice was independently rebuilt within its own budget.
                    + "\"regionTruncated\":true,"
                    + "\"unresolvedInputs\":[\""
                    + unresolvedAlternative + "\"],"
                    + "\"unresolvedInputDetails\":[{"
                    + "\"dependencyCell\":\"" + alternative + "\","
                    + "\"dependencyMethods\":[\"" + constructor + "\"],"
                    + "\"reason\":\"OUTPUT_SLICE_INPUT_HAS_NO_REGION_PORT\","
                    + "\"diagnostic\":\"" + unresolvedAlternative + "\","
                    + "\"provenanceAuthority\":"
                    + "\"STATIC_EXACT_DEPENDENCY_METHOD_"
                    + "CONSUMER_SET_V1\"}],"
                    + "\"requestedStateTransformerContractVersion\":1,"
                    + "\"requestedStateTransformerContractApplicable\":true,"
                    + "\"requestedStateTransformerContractOutputPort\":"
                    + "\"REGION.W.out.0\","
                    + "\"requestedStateTransformerContractOutputCell\":"
                    + "\"" + state + "\","
                    + "\"requestedStateTransformerObligations\":[{"
                    + "\"siteId\":\"" + constructor + "#u1\","
                    + "\"method\":\"" + constructor + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.C\"],"
                    + "\"authority\":\"STATIC_EXACT_REQUESTED_"
                    + "OUTPUT_TARGET_CELL\"},{"
                    + "\"siteId\":\"" + updaterSite + "\","
                    + "\"method\":\"" + updater + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.U\"],"
                    + "\"authority\":\"STATIC_EXACT_REQUESTED_"
                    + "OUTPUT_TARGET_CELL\"}],"
                    + "\"requestedStateTransformerObligationCount\":2,"
                    + "\"requestedStateTransformerContractIssues\":[],"
                    + "\"requestedStateTransformerContractComplete\":true,"
                    + "\"requestedStateTransformerContractAuthority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1\","
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":false,"
                    + "\"captureBindings\":[],"
                    + "\"captureBindingIssues\":["
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + constructor + "#u1\","
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + updaterSite + "\"],"
                    + "\"heapInitializers\":[{"
                    + "\"initializerId\":\"STATIC_INIT.C\","
                    + "\"kind\":\"FRESH_DEFAULT_CONSTRUCTED_OBJECT\","
                    + "\"allocatedType\":\"java.util.HashMap\","
                    + "\"allocationMethod\":\"" + constructor + "\","
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"proofComplete\":true}],\"complete\":false,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\""
                    + runtimeBranch + "\",\"policy\":\"PIN\","
                    + "\"guard\":\"runtime\",\"role\":"
                    + "\"OUTPUT_RELATION\"},{\"siteId\":\""
                    + unobservedBranch + "\",\"policy\":\"PIN\","
                    + "\"guard\":\"alternative\",\"role\":"
                    + "\"OUTPUT_RELATION\"}],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            writeRegions(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.RUNTIME.PATH\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent updateRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent payloadRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", updater, 11, payload, 99, 66, "");
            RuntimeRegionPlanner.FieldAccessEvent stateRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(3,
                            "FIELD_READ", updater, 11, state, 42, 88, "");
            RuntimeRegionPlanner.RuntimeEvent mutation =
                    new RuntimeRegionPlanner.RuntimeEvent(4,
                            "CALL_SITE_ENTER", updater, 11, 40, 0,
                            updaterSite,
                            "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                            -1, "java.util.Map", 88, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent mutationReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(5,
                            "CALL_SITE_RETURN", updater, 11, 40, 0,
                            updaterSite, -1, "", 0, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH",
                            updater, 11, 0, 0, runtimeBranch, -1, "", 0,
                            "", true, true);
            RuntimeRegionPlanner.FieldAccessEvent downstreamRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    Arrays.asList(updateRoot, readRoot),
                    Arrays.asList(mutation, mutationReturn, branch),
                    Arrays.asList(payloadRead, stateRead, downstreamRead));

            assertEquals(3, result.activations.size());
            @SuppressWarnings("unchecked")
            Map<String, Object> output = result.activations.get(2);
            assertFalse(output.containsKey("requestedOutputSliceComplete"));
            assertCanonicalOutputOnly(output);
            Map<String, Object> slice = outputSlice(
                    output, "REGION.W.out.0");
            assertEquals(false, slice.get("captureBindingsRequired"));
            assertEquals(true, slice.get("captureBindingsComplete"));
            assertEquals(Collections.singletonList(updater),
                    slice.get("methods"));
            assertEquals(2, ((java.util.List<?>) output.get("symbolize"))
                    .size());
            assertEquals(1, ((java.util.List<?>) output.get(
                    "heapStateBindings")).size());
            assertEquals(true, slice.get("complete"));
            assertEquals(true, slice.get("structuralComplete"));
            assertEquals(true, slice.get("runtimeRefinementComplete"));
            assertEquals("OBSERVED_REGION_CALL_TREE_AND_STATIC_DEPENDENCY_"
                            + "METHOD_PROVENANCE",
                    slice.get("runtimeRefinementAuthority"));
            assertEquals(Arrays.asList("REGION.W.in.0", "REGION.W.in.1"),
                    slice.get("inputPorts"));
            assertTrue(String.valueOf(slice.get("sites")).contains(
                    runtimeBranch));
            assertFalse(String.valueOf(slice.get("sites")).contains(
                    constructor + "#u1"));
            assertFalse(String.valueOf(slice.get("sites")).contains(
                    unobservedBranch));
            assertTrue(String.valueOf(slice.get(
                    "excludedPathAlternativeSites")).contains(
                    unobservedBranch));
            assertEquals(Collections.singletonList("DF.U"),
                    slice.get("causalEdgeIds"));
            assertTrue(((java.util.List<?>) slice.get("heapInitializers"))
                    .isEmpty());
            assertEquals(Boolean.TRUE, slice.get(
                    "captureDischargedByHeapEffectTransformer"));
            assertEquals("REGION.W.in.0", slice.get(
                    "captureDischargeInputPort"));
            assertEquals("HEAP_EFFECT_STATE_TRANSFORMER", slice.get(
                    "captureDischargeAuthority"));
            assertEquals(Boolean.TRUE, slice.get(
                    "requestedStateTransformerContractComplete"));
            assertEquals(1, slice.get(
                    "requestedStateTransformerObligationCount"));
            assertTrue(((java.util.List<?>) slice.get("captureBindings"))
                    .isEmpty());
            assertTrue(String.valueOf(slice.get(
                    "excludedAlternativeInputPorts")).contains(
                    "REGION.W.in.2"));
            assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
            assertTrue(String.valueOf(slice.get(
                    "excludedAlternativeUnresolvedInputs")).contains(
                    unresolvedAlternative));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void runtimeClosureReslicesFrozenGraphToTwoSharedFields()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path graph = folder.getRoot().toPath().resolve(
                    "static_dataflow_edges.jsonl");
            String root = "<example.Worker: void run()>";
            String anchor = "<example.Consumer: void execute()>";
            String getA = "<example.RpcBus: int getA()>";
            String getB = "<example.RpcBus: int getB()>";
            String other = "<example.OtherConsumer: void execute()>";
            String fieldA = "<example.RpcBus: int a>";
            String fieldB = "<example.RpcBus: int b>";
            String aliasA = "<example.Consumer: example.RpcBus bus>#field:a";
            String aliasB = "<example.Consumer: example.RpcBus bus>#field:b";
            String localA = anchor + "::$i0";
            String localB = anchor + "::$i1";
            String getterLocalA = getA + "::i0";
            String getterLocalB = getB + "::i0";
            String getAReturn = getA + ".return";
            String getBReturn = getB + ".return";
            String booleanReturn =
                    "<java.lang.Boolean: boolean booleanValue()>.return";
            String guardSite = anchor + "#u8";
            String failure = anchor + "#u11#exception:example.Bug";
            String region = "{\"regionId\":\"REGION.0\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"anchorMethod\":\"" + anchor + "\","
                    + "\"methods\":[\"" + root + "\",\"" + anchor
                    + "\",\"" + getA + "\",\"" + getB + "\",\""
                    + other + "\"],\"symbolicInputs\":["
                    + inputPort("REGION.0.in.0", fieldA, "SHARED_HEAP") + ","
                    + inputPort("REGION.0.in.1", fieldB, "SHARED_HEAP") + ","
                    + inputPort("REGION.0.in.2", getAReturn, "OPAQUE_CALL") + ","
                    + inputPort("REGION.0.in.3", getBReturn, "OPAQUE_CALL") + ","
                    + inputPort("REGION.0.in.4", aliasA, "SHARED_HEAP") + ","
                    + inputPort("REGION.0.in.5", aliasB, "SHARED_HEAP") + ","
                    + inputPort("REGION.0.in.6", booleanReturn,
                    "OPAQUE_CALL") + "],"
                    + "\"outputs\":[{\"portId\":\"REGION.0.out.0\","
                    + "\"cell\":\"" + failure + "\","
                    + "\"kind\":\"FAILURE_PREDICATE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + guardSite
                    + "\",\"policy\":\"PATH_ASSUMPTION\","
                    + "\"guard\":\"a <= b\",\"requiredOutcome\":false,"
                    + "\"role\":\"REACHABILITY\"}],\"models\":[]}\n";
            writeRegions(regions, region.getBytes(StandardCharsets.UTF_8));

            String frozen = frozenDemandEdge("DF.GA", "GUARD",
                    "control_depends_on", localA, failure, anchor,
                    guardSite, 8)
                    + frozenDemandEdge("DF.GB", "GUARD",
                    "control_depends_on", localB, failure, anchor,
                    guardSite, 8)
                    + frozenDemandEdge("DF.CA", "FUNCTION_RETURN",
                    "value_flow", getAReturn, localA, anchor,
                    anchor + "#u2", 2)
                    + frozenDemandEdge("DF.CB", "FUNCTION_RETURN",
                    "value_flow", getBReturn, localB, anchor,
                    anchor + "#u4", 4)
                    + frozenDemandEdge("DF.RA", "VALUE_PASS",
                    "value_flow", getterLocalA, getAReturn, getA,
                    getA + "#u16", 16)
                    + frozenDemandEdge("DF.RB", "VALUE_PASS",
                    "value_flow", getterLocalB, getBReturn, getB,
                    getB + "#u16", 16)
                    + frozenDemandEdge("DF.FA", "HEAP_READ", "value_flow",
                    fieldA, getterLocalA, getA, getA + "#u8", 8)
                    + frozenDemandEdge("DF.AA", "HEAP_READ", "value_flow",
                    aliasA, getterLocalA, getA, getA + "#u8", 8)
                    + frozenDemandEdge("DF.FB", "HEAP_READ", "value_flow",
                    fieldB, getterLocalB, getB, getB + "#u8", 8)
                    + frozenDemandEdge("DF.AB", "HEAP_READ", "value_flow",
                    aliasB, getterLocalB, getB, getB + "#u8", 8);
            writeStaticGraph(graph, frozen.getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                    method(1, root, 1, 0, 0),
                    method(2, anchor, 2, 1, 1),
                    method(3, getA, 3, 2, 2),
                    method(4, getB, 4, 2, 4));
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(9, "BRANCH",
                            anchor, 2, 0, 0, guardSite, -1, "", 0,
                            "", true, true);
            RuntimeRegionPlanner.FieldAccessEvent readA =
                    new RuntimeRegionPlanner.FieldAccessEvent(5,
                            "FIELD_READ", getA, 3, 8, getA + "#u8",
                            fieldA, 77, 0, "-1", "", false, 0,
                            "TEST_NO_FINGERPRINT");
            RuntimeRegionPlanner.FieldAccessEvent readB =
                    new RuntimeRegionPlanner.FieldAccessEvent(6,
                            "FIELD_READ", getB, 4, 8, getB + "#u8",
                            fieldB, 77, 0, "10", "", false, 0,
                            "TEST_NO_FINGERPRINT");
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), null, graph.toFile(), methods,
                    Collections.singletonList(branch),
                    Arrays.asList(readA, readB));

            assertEquals(1, result.activations.size());
            Map<String, Object> activation = result.activations.get(0);
            assertFalse(activation.containsKey("concreteDemandSlice"));
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> actions =
                    (List<Map<String, Object>>) activation.get("symbolize");
            assertEquals(2, actions.size());
            assertEquals("HEAP_OBJECT_FIELD", actions.get(0).get("location"));
            assertEquals("HEAP_OBJECT_FIELD", actions.get(1).get("location"));
            assertEquals(fieldA, actions.get(0).get("cell"));
            assertEquals(fieldB, actions.get(1).get("cell"));
            assertFalse(String.valueOf(activation.get(
                    "runtimeDefinitionMethods")).contains(other));
            assertEquals("READY", admissionState(activation));
        } finally {
            folder.delete();
        }
    }

    private static String inputPort(String id, String cell,
                                    String sourceKind) {
        return "{\"portId\":\"" + id + "\",\"cell\":\"" + cell
                + "\",\"sourceKind\":\"" + sourceKind
                + "\",\"projection\":\"value\"}";
    }

    private static String frozenDemandEdge(
            String id, String transferKind, String relation,
            String fromCell, String toCell, String method,
            String siteId, int unitIndex) {
        return "{\"id\":\"" + id + "\",\"kind\":\"test_edge\","
                + "\"schemaVersion\":2,"
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"transferKind\":\"" + transferKind + "\","
                + "\"relation\":\"" + relation + "\","
                + "\"fromCell\":\"" + fromCell + "\","
                + "\"toCell\":\"" + toCell + "\","
                + "\"method\":\"" + method + "\","
                + "\"siteId\":\"" + siteId + "\","
                + "\"unitIndex\":" + unitIndex + "}\n";
    }

    private static RuntimeRegionPlanner.Result heapReachingDefinitionResult(
            boolean includeOldWrite, boolean includeNewWrite,
            int newWriteReceiver, boolean exactNewWriteSite)
            throws Exception {
        return heapReachingDefinitionResult(includeOldWrite, includeNewWrite,
                newWriteReceiver, exactNewWriteSite, true);
    }

    private static RuntimeRegionPlanner.Result heapReachingDefinitionResult(
            boolean includeOldWrite, boolean includeNewWrite,
            int newWriteReceiver, boolean exactNewWriteSite,
            boolean newWriteInsideClosure) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String root = "<example.Consumer: void run(int,int)>";
            String externalWriter = "<example.Writer: void publish(int)>";
            String field = "<example.State: int value>";
            String oldInput = root + ".param0:int";
            String newInput = root + ".param1:int";
            String oldRhs = root + "::oldValue";
            String newRhs = root + "::newValue";
            String readLocal = root + "::observed";
            String guardSite = root + "#u6";
            String failure = guardSite + "#exception:example.Bug";
            Path regions = folder.getRoot().toPath().resolve(
                    "regions.jsonl");
            Path graph = folder.getRoot().toPath().resolve("graph.jsonl");
            String region = "{\"regionId\":\"REGION.C\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"anchorMethod\":\"" + root + "\","
                    + "\"methods\":[\"" + root + "\"],"
                    + "\"symbolicInputs\":["
                    + inputPort("REGION.C.in.0", field, "SHARED_HEAP")
                    + ',' + inputPort("REGION.C.in.1", oldInput,
                    "ROOT_ARGUMENT")
                    + ',' + inputPort("REGION.C.in.2", newInput,
                    "ROOT_ARGUMENT") + "],"
                    + "\"outputs\":[{\"portId\":\"REGION.C.out.0\","
                    + "\"cell\":\"" + failure + "\","
                    + "\"kind\":\"FAILURE_PREDICATE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\""
                    + guardSite + "\",\"policy\":\"PATH_ASSUMPTION\","
                    + "\"guard\":\"observed == 0\","
                    + "\"requiredOutcome\":false,"
                    + "\"role\":\"REACHABILITY\"}],\"models\":[]}\n";
            writeRegions(regions, region.getBytes(StandardCharsets.UTF_8));

            String newWriteSite = exactNewWriteSite
                    ? root + "#u4" : root + "#u40";
            int newWriteUnit = exactNewWriteSite ? 4 : 40;
            String frozen = frozenDemandEdge("DF.GUARD", "GUARD",
                    "control_depends_on", readLocal, failure, root,
                    guardSite, 6)
                    + frozenDemandEdge("DF.READ", "HEAP_READ",
                    "value_flow", field, readLocal, root,
                    root + "#u5", 5)
                    + frozenDemandEdge("DF.WRITE.OLD", "HEAP_WRITE",
                    "value_flow", oldRhs, field, root,
                    root + "#u2", 2)
                    + frozenDemandEdge("DF.OLD.RHS", "VALUE_PASS",
                    "value_flow", oldInput, oldRhs, root,
                    root + "#u1", 1)
                    + frozenDemandEdge("DF.WRITE.NEW", "HEAP_WRITE",
                    "value_flow", newRhs, field, root,
                    newWriteSite, newWriteUnit)
                    + frozenDemandEdge("DF.NEW.RHS", "VALUE_PASS",
                    "value_flow", newInput, newRhs, root,
                    root + "#u3", 3);
            writeStaticGraph(graph, frozen.getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "METHOD_ARGUMENT", root, 1, 0, 0,
                            root + "#entry", 0, "int", 0, "1",
                            false, false),
                    new RuntimeRegionPlanner.RuntimeEvent(3,
                            "METHOD_ARGUMENT", root, 1, 0, 0,
                            root + "#entry", 1, "int", 0, "2",
                            false, false),
                    new RuntimeRegionPlanner.RuntimeEvent(7, "BRANCH",
                            root, 1, 0, 0, guardSite, -1, "", 0,
                            "", true, true));
            List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                    new ArrayList<>();
            // Deliberately publish the newer write before the older one.
            // Reaching-definition selection is by maximum sequence, never
            // by the incidental order of the input event collection.
            if (includeNewWrite) {
                fields.add(new RuntimeRegionPlanner.FieldAccessEvent(5,
                        "FIELD_WRITE", newWriteInsideClosure
                        ? root : externalWriter,
                        newWriteInsideClosure ? 1 : 2, 4,
                        (newWriteInsideClosure ? root : externalWriter)
                                + "#u4",
                        field, newWriteReceiver, 0, "2", "", false,
                        0, "TEST_NO_FINGERPRINT"));
            }
            if (includeOldWrite) {
                fields.add(new RuntimeRegionPlanner.FieldAccessEvent(4,
                        "FIELD_WRITE", root, 1, 2, root + "#u2",
                        field, 77, 0, "1", "", false, 0,
                        "TEST_NO_FINGERPRINT"));
            }
            fields.add(new RuntimeRegionPlanner.FieldAccessEvent(6,
                    "FIELD_READ", root, 1, 5, root + "#u5", field,
                    77, 0, includeNewWrite && newWriteReceiver == 77
                    ? "2" : includeOldWrite ? "1" : "0", "", false,
                    0, "TEST_NO_FINGERPRINT"));

            List<RuntimeRegionPlanner.MethodEvent> methods =
                    new ArrayList<>();
            methods.add(method(1, root, 1, 0, 0));
            if (includeNewWrite && !newWriteInsideClosure) {
                methods.add(method(2, externalWriter, 2, 0, 0));
            }
            return RuntimeRegionPlanner.plan(regions.toFile(), null,
                    graph.toFile(), methods, runtime, fields);
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result
    mapValueProjectionActivationResult(boolean includeExactFieldRead) {
        String mapField = "<example.Producer: java.util.Map elements>";
        String outputField = "<example.Payload: example.Element[] elements>";
        String elementField = "<example.Element: long expiryDate>";
        String mapLocal = "<example.Producer: example.Payload export()>::$r1";
        String viewLocal = "<example.Producer: example.Payload export()>::$r2";
        String arrayLocal = "<example.Producer: example.Payload export()>::$r3";

        List<Map<String, Object>> causal = new ArrayList<>();
        if (includeExactFieldRead) {
            causal.add(row("edgeId", "GOOD.FIELD", "fromCell", mapField,
                    "toCell", mapLocal, "transferKind", "HEAP_READ",
                    "kind", "field_read"));
        }
        causal.add(row("edgeId", "BAD.GUARD", "fromCell", mapField,
                "toCell", mapLocal, "transferKind", "GUARD",
                "kind", "path_guard_dependency"));
        causal.add(projectionEdge("VIEW", mapLocal, viewLocal,
                "MAP_VALUES_VIEW", false));
        causal.add(projectionEdge("SNAP", viewLocal, arrayLocal,
                "COLLECTION_TO_ARRAY", true));
        causal.add(row("edgeId", "OUT", "fromCell", arrayLocal,
                "toCell", outputField, "transferKind", "HEAP_WRITE",
                "kind", "field_write"));

        Map<String, Object> producerSlice = row(
                "outputPort", "REGION.P.out.keys",
                "outputCell", outputField,
                "complete", true,
                "inputBindings", Collections.singletonList(row(
                        "dependencyCell", mapField,
                        "inputPort", "REGION.P.in.map")),
                "causalEdges", causal);
        Map<String, Object> producer = row(
                "activationId", "ACT.P.OUT",
                "regionId", "REGION.P",
                "regionInstanceId", "REGION.P@test#call1",
                "captureGoal", row("kind", "OUTPUT_CLOSURE"),
                "requestedOutputCaptureRequired", false,
                "requestedOutput", row("portId", "REGION.P.out.keys",
                        "cell", outputField),
                "requestedOutputSlice", producerSlice,
                "edgeBindings", Collections.singletonList(row(
                        "edgeId", "EDGE.PD",
                        "toRegionInstance", "REGION.D@test#call2",
                        "toInputPort", "REGION.D.in.keys")),
                "admission", row("state", "READY", "mode",
                        "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY",
                        "blockers", Collections.emptyList()));

        Map<String, Object> downstreamBinding = row(
                "schemaVersion", 1,
                "kind", "ARRAY_ELEMENT_FIELD",
                "bindingId", "BIND.DOWNSTREAM.EXPIRY",
                "baseInputSymbol", "REGION.D.in.expiry",
                "containerInputPort", "REGION.D.in.keys",
                "declaredFieldSignature", elementField,
                "declaredFieldOwnerClass", "example.Element",
                "declaredFieldType", "long",
                "declaredFieldName", "expiryDate",
                "fieldPath", Collections.singletonList("expiryDate"),
                "complete", true);
        Map<String, Object> downstream = row(
                "activationId", "ACT.D.OUT",
                "regionId", "REGION.D",
                "regionInstanceId", "REGION.D@test#call2",
                "captureGoal", row("kind", "OUTPUT_CLOSURE"),
                "requestedOutputSlice", row(
                        "complete", true,
                        "containerElementFieldBindings",
                        Collections.singletonList(downstreamBinding)));
        RuntimeRegionPlanner.Result result =
                new RuntimeRegionPlanner.Result();
        result.activations.add(producer);
        result.activations.add(downstream);
        return result;
    }

    private static Map<String, Object> projectionEdge(
            String id, String from, String to, String operation,
            boolean snapshot) {
        return row("edgeId", id, "fromCell", from, "toCell", to,
                "siteId", "<example.Producer: example.Payload export()>#u"
                        + (snapshot ? "3" : "2"),
                "transferKind", "MODEL_TRANSFORM",
                "kind", snapshot ? "container_snapshot_projection"
                        : "container_backed_view_projection",
                "containerProjectionContractVersion", 1,
                "containerProjectionOperation", operation,
                "containerProjectionAuthority",
                "JAVA_COLLECTION_API_EXACT_SIGNATURE_WHITELIST_V1",
                "receiverValueDependencyComplete", true,
                "elementIdentityPreserving", true,
                "backedView", !snapshot,
                "snapshot", snapshot);
    }

    private static Map<String, Object> row(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index + 1 < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }

    private static RuntimeRegionPlanner.Result containerBindingRuntimeResult(
            boolean mismatchedSite) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writer = "<example.Secret: void addKeys(example.Keys)>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.Secret: java.util.Map allKeys>";
            String key = "<example.KeyBase: int keyId>";
            String keys = "<example.Keys: example.Key[] allKeys>";
            String fieldSite = writer + (mismatchedSite ? "#u99" : "#u14");
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writer + "\","
                    + "\"anchorMethod\":\"" + writer + "\","
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"symbolicInputs\":["
                    + "{\"portId\":\"REGION.W.in.key\",\"cell\":\""
                    + key + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"},"
                    + "{\"portId\":\"REGION.W.in.keys\",\"cell\":\""
                    + keys + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.key\","
                    + "\"REGION.W.in.keys\"],"
                    + "\"inputBindings\":["
                    + sliceBinding(key, "REGION.W.in.key", writer) + ","
                    + sliceBinding(keys, "REGION.W.in.keys", writer) + "],"
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"sites\":[\"" + writer + "#u11\",\""
                    + writer + "#u13\",\"" + writer + "#u14\"],"
                    + "\"causalEdgeIds\":[\"A\",\"C\",\"G\",\"P\"],"
                    + "\"causalEdges\":["
                    + causalReference("A", writer, writer + "#u13") + ","
                    + causalReference("C", writer, writer + "#u11") + ","
                    + causalReference("G", writer, writer + "#u14") + ","
                    + causalReference("P", writer, writer + "#u14") + "],"
                    + "\"containerElementFieldBindings\":[{"
                    + "\"schemaVersion\":1,"
                    + "\"kind\":\"ARRAY_ELEMENT_FIELD\","
                    + "\"bindingId\":\"BIND.ARRAY.0\","
                    + "\"baseInputSymbol\":\"REGION.W.in.key\","
                    + "\"containerInputPort\":\"REGION.W.in.keys\","
                    + "\"containerInputCell\":\"" + keys + "\","
                    + "\"selectorAuthority\":\"EXACT_ARRAY_INDEX\","
                    + "\"elementIndex\":0,\"elementOccurrence\":1,"
                    + "\"fieldPath\":[\"keyId\"],"
                    + "\"declaredFieldSignature\":\"" + key + "\","
                    + "\"declaredFieldOwnerClass\":\"example.KeyBase\","
                    + "\"declaredFieldType\":\"int\","
                    + "\"declaredFieldName\":\"keyId\","
                    + "\"method\":\"" + writer + "\","
                    + "\"fieldMaterializationSiteId\":\"" + fieldSite
                    + "\",\"arrayLoadSiteId\":\"" + writer + "#u13\","
                    + "\"proofCausalEdgeIds\":[\"A\",\"C\",\"G\",\"P\"],"
                    + "\"proofAuthority\":\"STATIC_EXACT_CONTAINER_ARRAY_"
                    + "ACCESSOR_DECLARED_FIELD_FOUR_EDGE_JOIN_V1\","
                    + "\"complete\":true}],"
                    + "\"complete\":true,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":\"REGION.R.in.0\","
                    + "\"cell\":\"" + state + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            writeRegions(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    writer, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent keyRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", writer, 11, key, 501, 0, "7");
            RuntimeRegionPlanner.FieldAccessEvent keysRead =
                    exactFieldRead(3, writer, 11, 11, keys, 502, 600);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(4,
                            "FIELD_WRITE", writer, 11, state, 42, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(keyRead, keysRead, write, read));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result arrayInputAliasRuntimeResult(
            boolean ambiguousCanonicalPort) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writer = "<example.Handler: void process()>";
            String reader = "<example.Reader: void consume()>";
            String carrier = "<example.Command: example.Keys keys>";
            String promoted = carrier + "#field:allKeys";
            String exact = "<example.Keys: example.Key[] allKeys>";
            String key = "<example.Key: int keyId>";
            String state = "<example.Handler: java.util.Map state>";
            String extraPort = ambiguousCanonicalPort
                    ? ",\"REGION.W.in.exact.duplicate\"" : "";
            String extraInput = ambiguousCanonicalPort
                    ? ",{\"portId\":\"REGION.W.in.exact.duplicate\","
                    + "\"cell\":\"" + exact + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}" : "";
            String extraBinding = ambiguousCanonicalPort
                    ? "," + sliceBinding(exact,
                    "REGION.W.in.exact.duplicate", writer) : "";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writer + "\","
                    + "\"anchorMethod\":\"" + writer + "\","
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.W.in.key\",\"cell\":\"" + key
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"},{\"portId\":"
                    + "\"REGION.W.in.promoted\",\"cell\":\""
                    + promoted + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"},{\"portId\":"
                    + "\"REGION.W.in.exact\",\"cell\":\"" + exact
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}" + extraInput + "],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{\"outputPort\":"
                    + "\"REGION.W.out.0\",\"outputCell\":\"" + state
                    + "\",\"inputPorts\":[\"REGION.W.in.key\","
                    + "\"REGION.W.in.promoted\",\"REGION.W.in.exact\""
                    + extraPort + "],\"inputBindings\":["
                    + sliceBinding(key, "REGION.W.in.key", writer) + ",{"
                    + "\"dependencyCell\":\""
                    + promoted + "\",\"inputPort\":"
                    + "\"REGION.W.in.promoted\",\"bindingAuthority\":"
                    + "\"OUTPUT_SLICE_FRONTIER_PROMOTION\","
                    + "\"dependencyMethods\":[\"" + writer + "\"]},{"
                    + "\"dependencyCell\":\"" + promoted + "\","
                    + "\"inputPort\":\"REGION.W.in.promoted\","
                    + "\"bindingAuthority\":"
                    + "\"UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN\","
                    + "\"dependencyMethods\":[\"" + writer + "\"]},"
                    + sliceBinding(exact, "REGION.W.in.exact", writer)
                    + extraBinding + "],\"methods\":[\"" + writer
                    + "\"],\"sites\":[\"" + writer + "#u5\",\""
                    + writer + "#u6\",\"" + writer + "#u7\",\""
                    + writer + "#u8\",\"" + writer + "#u9\"],"
                    + "\"causalEdgeIds\":[\"A\",\"C\",\"G\",\"P\"],"
                    + "\"causalEdges\":["
                    + causalReference("A", writer, writer + "#u5") + ","
                    + causalReference("C", writer, writer + "#u6") + ","
                    + causalReference("G", writer, writer + "#u8") + ","
                    + causalReference("P", writer, writer + "#u9") + "],"
                    + "\"containerElementFieldBindings\":[{"
                    + "\"schemaVersion\":1,"
                    + "\"kind\":\"ARRAY_ELEMENT_FIELD\","
                    + "\"bindingId\":\"BIND.ALIAS.CONTAINER\","
                    + "\"baseInputSymbol\":\"REGION.W.in.key\","
                    + "\"containerInputPort\":\"REGION.W.in.promoted\","
                    + "\"containerInputCell\":\"" + exact + "\","
                    + "\"selectorAuthority\":\"EXACT_ARRAY_INDEX\","
                    + "\"elementIndex\":0,\"elementOccurrence\":1,"
                    + "\"fieldPath\":[\"keyId\"],"
                    + "\"declaredFieldSignature\":\"" + key + "\","
                    + "\"declaredFieldOwnerClass\":\"example.Key\","
                    + "\"declaredFieldType\":\"int\","
                    + "\"declaredFieldName\":\"keyId\","
                    + "\"method\":\"" + writer + "\","
                    + "\"fieldMaterializationSiteId\":\"" + writer
                    + "#u8\",\"arrayLoadSiteId\":\"" + writer
                    + "#u7\",\"proofCausalEdgeIds\":[\"A\",\"C\","
                    + "\"G\",\"P\"],\"proofAuthority\":"
                    + "\"STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_"
                    + "FIELD_FOUR_EDGE_JOIN_V1\",\"complete\":true}],"
                    + "\"complete\":true,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            writeRegions(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    writer, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent carrierRead =
                    exactFieldRead(2, writer, 11, 5, carrier, 700, 800);
            RuntimeRegionPlanner.FieldAccessEvent exactArrayRead =
                    exactFieldRead(3, writer, 11, 6, exact, 800, 900);
            RuntimeRegionPlanner.FieldAccessEvent keyRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(3,
                            "FIELD_READ", writer, 11, key, 901, 0, "7");
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(4,
                            "FIELD_WRITE", writer, 11, state, 42, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(carrierRead, exactArrayRead, keyRead,
                            write, read));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result primitiveInputAliasRuntimeResult(
            boolean differentReceiver, boolean interveningWrite)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writer = "<example.Handler: void process()>";
            String reader = "<example.Reader: void consume()>";
            String carrier = "<example.Handler: example.Producer producer>";
            String projected = carrier + "#field:input";
            String exact = "<example.Producer: int input>";
            String state = "<example.Handler: int state>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writer + "\","
                    + "\"anchorMethod\":\"" + writer + "\","
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.W.in.projected\",\"cell\":\""
                    + projected + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:input\"},{\"portId\":"
                    + "\"REGION.W.in.exact\",\"cell\":\"" + exact
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{\"outputPort\":"
                    + "\"REGION.W.out.0\",\"outputCell\":\"" + state
                    + "\",\"inputPorts\":[\"REGION.W.in.projected\","
                    + "\"REGION.W.in.exact\"],\"inputBindings\":[{"
                    + "\"dependencyCell\":\"" + projected + "\","
                    + "\"inputPort\":\"REGION.W.in.projected\","
                    + "\"bindingAuthority\":"
                    + "\"UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN\","
                    + "\"dependencyMethods\":[\"" + writer + "\"]},"
                    + sliceBinding(exact, "REGION.W.in.exact", writer)
                    + "],\"methods\":[\"" + writer + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[\"P\"],"
                    + "\"causalEdges\":["
                    + causalReference("P", writer, writer + "#u5") + "],"
                    + "\"complete\":true,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            writeRegions(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    writer, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent carrierRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", writer, 11, carrier, 700, 800, "");
            RuntimeRegionPlanner.FieldAccessEvent leafWrite =
                    new RuntimeRegionPlanner.FieldAccessEvent(3,
                            "FIELD_WRITE", writer, 11, exact, 800, 0, "9");
            RuntimeRegionPlanner.FieldAccessEvent exactRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(
                            interveningWrite ? 4 : 3,
                            "FIELD_READ", writer, 11, 6, writer + "#u6",
                            exact, differentReceiver ? 801 : 800, 0, "3",
                            "", false, 0, "");
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(
                            interveningWrite ? 5 : 4,
                            "FIELD_WRITE", writer, 11, state, 42, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            List<RuntimeRegionPlanner.FieldAccessEvent> fieldEvents =
                    new ArrayList<>();
            fieldEvents.add(carrierRead);
            if (interveningWrite) {
                fieldEvents.add(leafWrite);
            }
            fieldEvents.add(exactRead);
            fieldEvents.add(write);
            fieldEvents.add(read);
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    fieldEvents);
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result mutationDischargeGateResult(
            String unresolvedOwner, String retainedKind,
            boolean contractComplete) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String alternative = "<example.State: void initialize()>";
            String updater = "<example.State: void addKeys()>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.State: java.util.Map allKeys>";
            String missing = "<example.Seed: int alternative>";
            String alternativeSite = alternative + "#u3";
            String updaterSite = updater + "#u7";
            String unresolvedMethod = "OBSERVED".equals(unresolvedOwner)
                    ? updater : alternative;
            String diagnostic = missing
                    + " [output slice input has no region port]";
            String contractIssues = contractComplete ? "[]"
                    : "[\"STATIC_TRANSFORMER_LEDGER_GAP\"]";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + alternative + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + alternative + "\",\""
                    + updater + "\"],\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.W.in.0\",\"cell\":\""
                    + state + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\"],"
                    + "\"inputBindings\":["
                    + sliceBinding(state, "REGION.W.in.0", updater) + "],"
                    + "\"methods\":[\"" + alternative + "\",\""
                    + updater + "\"],\"sites\":[\"" + alternativeSite
                    + "\",\"" + updaterSite + "\"],"
                    + "\"causalEdgeIds\":[\"DF.A\",\"DF.U\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.A", alternative,
                    alternativeSite) + ","
                    + "{\"edgeId\":\"DF.U\",\"method\":\""
                    + updater + "\",\"siteId\":\"" + updaterSite
                    + "\",\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"" + retainedKind + "\"}],"
                    + "\"structuralComplete\":true,"
                    + "\"unresolvedInputs\":[\"" + diagnostic + "\"],"
                    + "\"unresolvedInputDetails\":[{"
                    + "\"dependencyCell\":\"" + missing + "\","
                    + "\"dependencyMethods\":[\"" + unresolvedMethod
                    + "\"],\"reason\":"
                    + "\"OUTPUT_SLICE_INPUT_HAS_NO_REGION_PORT\","
                    + "\"diagnostic\":\"" + diagnostic + "\","
                    + "\"provenanceAuthority\":"
                    + "\"STATIC_EXACT_DEPENDENCY_METHOD_CONSUMER_SET_V1\"}],"
                    + "\"requestedStateTransformerContractVersion\":1,"
                    + "\"requestedStateTransformerContractApplicable\":true,"
                    + "\"requestedStateTransformerContractOutputPort\":"
                    + "\"REGION.W.out.0\","
                    + "\"requestedStateTransformerContractOutputCell\":"
                    + "\"" + state + "\","
                    + "\"requestedStateTransformerObligations\":[{"
                    + "\"siteId\":\"" + alternativeSite + "\","
                    + "\"method\":\"" + alternative + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.A\"],"
                    + "\"authority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL\"},{"
                    + "\"siteId\":\"" + updaterSite + "\","
                    + "\"method\":\"" + updater + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"" + retainedKind + "\","
                    + "\"causalEdgeIds\":[\"DF.U\"],"
                    + "\"authority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL\"}],"
                    + "\"requestedStateTransformerObligationCount\":2,"
                    + "\"requestedStateTransformerContractIssues\":"
                    + contractIssues + ","
                    + "\"requestedStateTransformerContractComplete\":"
                    + contractComplete + ","
                    + "\"requestedStateTransformerContractAuthority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1\","
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":false,"
                    + "\"captureBindings\":[],"
                    + "\"captureBindingIssues\":["
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + alternativeSite + "\","
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + updaterSite + "\"],"
                    + "\"complete\":false,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            writeRegions(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent stateRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", updater, 11, state, 42, 88, "");
            RuntimeRegionPlanner.RuntimeEvent mutation =
                    new RuntimeRegionPlanner.RuntimeEvent(3,
                            "CALL_SITE_ENTER", updater, 11, 30, 0,
                            updaterSite,
                            "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                            -1, "java.util.Map", 88, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent mutationReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(4,
                            "CALL_SITE_RETURN", updater, 11, 30, 0,
                            updaterSite, -1, "", 0, "", false, false);
            RuntimeRegionPlanner.FieldAccessEvent downstreamRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Arrays.asList(mutation, mutationReturn),
                    Arrays.asList(stateRead, downstreamRead));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result containerMutationReadFromResult(
            boolean includeReturn, int readerContainerObjectId)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writerRoot = "<example.KeyUpdater: void loop()>";
            String addKeys = "<example.SecretManager: void addKeys()>";
            String reader = "<example.SecretManager: void retrieve()>";
            String field = "<example.SecretManager: java.util.Map allKeys>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writerRoot + "\","
                    + "\"anchorMethod\":\"" + addKeys + "\","
                    + "\"methods\":[\"" + writerRoot + "\",\""
                    + addKeys + "\"],\"symbolicInputs\":[],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + field + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            writeRegions(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.ALL_KEYS\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + field + "\","
                    + "\"toPort\":\"" + field + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writer = methodContext(1,
                    writerRoot, 1, "DATANODE", "KeyUpdater", 101L);
            RuntimeRegionPlanner.MethodEvent contained =
                    new RuntimeRegionPlanner.MethodEvent(5190, "testHandle",
                            "DATANODE", "KeyUpdater", 101L, addKeys,
                            273814159, "example.SecretManager", 2, 1, 0,
                            519000L);
            RuntimeRegionPlanner.MethodEvent read = methodContext(14000,
                    reader, 3, "DATANODE", "DataXceiver", 202L);
            List<RuntimeRegionPlanner.RuntimeEvent> runtime =
                    new ArrayList<>();
            for (int index = 0; index < 513; index++) {
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(index + 2L,
                        "BRANCH", writerRoot, 1, 0, 0,
                        writerRoot + "#u" + index, -1, "", 0, "",
                        true, (index & 1) == 0));
            }
            String put = "<java.util.Map: java.lang.Object put("
                    + "java.lang.Object,java.lang.Object)>";
            runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5199,
                    "CALL_SITE_ENTER", addKeys, 2, 5199, 0,
                    addKeys + "#u22", put, -1, "java.util.HashMap",
                    128017166, "", false, false));
            runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5207,
                    "CALL_SITE_ENTER", addKeys, 2, 5207, 0,
                    addKeys + "#u23", put, -1, "java.util.HashMap",
                    128017166, "", false, false));
            if (includeReturn) {
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5201,
                        "CALL_SITE_RETURN", addKeys, 2, 5199, 0,
                        addKeys + "#u22", -1, "", 0, "", false,
                        false));
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5211,
                        "CALL_SITE_RETURN", addKeys, 2, 5207, 0,
                        addKeys + "#u23", -1, "", 0, "", false,
                        false));
            }
            RuntimeRegionPlanner.FieldAccessEvent writerFieldRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(5197,
                            "FIELD_READ", addKeys, 2, field, 273814159,
                            128017166, "");
            RuntimeRegionPlanner.FieldAccessEvent readerFieldRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(14261,
                            "FIELD_READ", reader, 3, field, 273814159,
                            readerContainerObjectId, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    Arrays.asList(writer, contained, read), runtime,
                    Arrays.asList(writerFieldRead, readerFieldRead));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result jointPrimitiveDemandResult(
            boolean incompleteY) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String producer = "<example.Producer: void produce()>";
            String dxy = "<example.JointConsumer: void consume()>";
            String dx = "<example.XConsumer: void consume()>";
            String inputX = "<example.Input: int x>";
            String inputY = "<example.Input: int y>";
            String outputX = "<example.State: int x>";
            String outputY = "<example.State: int y>";

            JsonObject producerRegion = new JsonObject();
            producerRegion.addProperty("regionId", "REGION.P");
            producerRegion.addProperty("rootMethod", producer);
            producerRegion.addProperty("anchorMethod", producer);
            producerRegion.add("methods", jsonStrings(producer));
            JsonArray producerInputs = new JsonArray();
            producerInputs.add(primitivePort("REGION.P.in.x", inputX));
            producerInputs.add(primitivePort("REGION.P.in.y", inputY));
            producerRegion.add("symbolicInputs", producerInputs);
            JsonArray producerOutputs = new JsonArray();
            producerOutputs.add(outputPort("REGION.P.out.x", outputX));
            producerOutputs.add(outputPort("REGION.P.out.y", outputY));
            producerRegion.add("outputs", producerOutputs);
            JsonArray slices = new JsonArray();
            slices.add(directPrimitiveSlice(producer, "REGION.P.out.x",
                    outputX, "REGION.P.in.x", inputX, 1, 10,
                    "DF.X", true));
            slices.add(directPrimitiveSlice(producer, "REGION.P.out.y",
                    outputY, "REGION.P.in.y", inputY, 2, 11,
                    "DF.Y", !incompleteY));
            producerRegion.add("outputSlices", slices);
            JsonArray policies = new JsonArray();
            policies.add(branchPolicy(producer + "#u10", "x > 0"));
            policies.add(branchPolicy(producer + "#u11", "y > 0"));
            producerRegion.add("branchPolicies", policies);
            producerRegion.add("models", new JsonArray());

            JsonObject jointConsumer = consumerRegion(
                    "REGION.DXY", dxy,
                    new String[]{"REGION.DXY.in.x", "REGION.DXY.in.y"},
                    new String[]{outputX, outputY});
            JsonObject xConsumer = consumerRegion(
                    "REGION.DX", dx,
                    new String[]{"REGION.DX.in.x"},
                    new String[]{outputX});
            writeRegions(regions, (producerRegion + "\n"
                    + jointConsumer + "\n" + xConsumer + "\n").getBytes(
                    StandardCharsets.UTF_8));

            String regionEdges = regionEdge("E.X.1", "REGION.P",
                    "REGION.DXY", outputX)
                    + regionEdge("E.X.2", "REGION.P",
                    "REGION.DXY", outputX)
                    + regionEdge("E.Y", "REGION.P",
                    "REGION.DXY", outputY)
                    + regionEdge("E.X.DX", "REGION.P",
                    "REGION.DX", outputX);
            Files.write(edges, regionEdges.getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                    methodContext(1, producer, 11, "PROCESS", "producer",
                            101L),
                    methodContext(10, dxy, 22, "PROCESS", "joint",
                            202L),
                    methodContext(20, dx, 33, "PROCESS", "x-only",
                            303L));
            List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                    new RuntimeRegionPlanner.RuntimeEvent(4, "BRANCH",
                            producer, 11, 0, 0, producer + "#u10",
                            -1, "", 0, "", true, true),
                    new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                            producer, 11, 0, 0, producer + "#u11",
                            -1, "", 0, "", true, false));
            List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                    Arrays.asList(
                            new RuntimeRegionPlanner.FieldAccessEvent(2,
                                    "FIELD_READ", producer, 11, inputX,
                                    66, 0, "1"),
                            new RuntimeRegionPlanner.FieldAccessEvent(3,
                                    "FIELD_READ", producer, 11, inputY,
                                    66, 0, "2"),
                            new RuntimeRegionPlanner.FieldAccessEvent(6,
                                    "FIELD_WRITE", producer, 11, outputX,
                                    77, 88, "3"),
                            new RuntimeRegionPlanner.FieldAccessEvent(7,
                                    "FIELD_WRITE", producer, 11, outputY,
                                    77, 99, "4"),
                            new RuntimeRegionPlanner.FieldAccessEvent(11,
                                    "FIELD_READ", dxy, 22, outputX,
                                    77, 88, "3"),
                            new RuntimeRegionPlanner.FieldAccessEvent(12,
                                    "FIELD_READ", dxy, 22, outputY,
                                    77, 99, "4"),
                            new RuntimeRegionPlanner.FieldAccessEvent(21,
                                    "FIELD_READ", dx, 33, outputX,
                                    77, 88, "3"));
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(), methods, runtime,
                    fields);
        } finally {
            folder.delete();
        }
    }

    private static JsonObject primitivePort(String port, String cell) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        result.addProperty("cell", cell);
        result.addProperty("sourceKind", "SHARED_HEAP");
        result.addProperty("projection", "value");
        return result;
    }

    private static JsonObject outputPort(String port, String cell) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        result.addProperty("cell", cell);
        result.addProperty("kind", "HEAP_STATE");
        return result;
    }

    private static JsonObject directPrimitiveSlice(
            String method, String outputPort, String outputCell,
            String inputPort, String inputCell, int assignmentUnit,
            int branchUnit, String causalEdgeId,
            boolean captureBindingsComplete) {
        JsonObject result = new JsonObject();
        result.addProperty("outputPort", outputPort);
        result.addProperty("outputCell", outputCell);
        result.add("inputPorts", jsonStrings(inputPort));
        JsonObject inputBinding = new JsonObject();
        inputBinding.addProperty("dependencyCell", inputCell);
        inputBinding.addProperty("inputPort", inputPort);
        inputBinding.addProperty("bindingAuthority", "EXACT_CELL_IDENTITY");
        inputBinding.add("dependencyMethods", jsonStrings(method));
        JsonArray inputBindings = new JsonArray();
        inputBindings.add(inputBinding);
        result.add("inputBindings", inputBindings);
        result.add("methods", jsonStrings(method));
        result.add("sites", jsonStrings(method + "#u" + branchUnit));
        result.add("causalEdgeIds", jsonStrings(causalEdgeId));

        JsonObject causal = new JsonObject();
        causal.addProperty("edgeId", causalEdgeId);
        causal.addProperty("method", method);
        causal.addProperty("siteId", method + "#u" + assignmentUnit);
        causal.addProperty("unitIndex", assignmentUnit);
        causal.addProperty("fromCell", inputCell);
        causal.addProperty("toCell", outputCell);
        causal.addProperty("transferKind", "HEAP_WRITE");
        causal.addProperty("kind", "field_write");
        causal.addProperty("relation", "value_flow");
        causal.addProperty("schemaVersion", 2);
        causal.addProperty("semanticMode", "ASSERTABLE");
        JsonArray causalEdges = new JsonArray();
        causalEdges.add(causal);
        result.add("causalEdges", causalEdges);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId", outputPort + ".capture");
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", outputCell);
        capture.addProperty("method", method);
        capture.addProperty("siteId", method + "#u" + assignmentUnit);
        capture.addProperty("unitIndex", assignmentUnit);
        capture.addProperty("unit", "state assignment");
        capture.addProperty("fieldSignature", outputCell);
        capture.addProperty("fieldOwnerExpression", "state");
        capture.addProperty("fieldOwnerCell", method + "::state");
        capture.addProperty("fieldOwnerDeclaredType", "example.State");
        capture.addProperty("fieldOwnerBindingKind",
                "INSTANCE_FIELD_LHS_BASE");
        capture.addProperty("fieldOwnerBindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS");
        capture.addProperty("rhsExpression", inputPort);
        capture.addProperty("rhsCell", inputCell);
        capture.addProperty("rhsCausalEdgeId", causalEdgeId);
        capture.addProperty("rhsRelation", "value_flow");
        capture.addProperty("rhsRelationComplete", true);
        capture.addProperty("rhsRelationAuthority",
                "STATIC_EXACT_HEAP_WRITE_VALUE_FLOW");
        capture.addProperty("causalEdgeId", causalEdgeId);
        capture.addProperty("transferKind", "HEAP_WRITE");
        capture.addProperty("bindingKind", "field_write");
        capture.addProperty("bindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS");
        capture.addProperty("occurrence", 0);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        result.addProperty("captureBindingsRequired", true);
        result.addProperty("captureBindingsComplete",
                captureBindingsComplete);
        result.add("captureBindings", captures);
        result.addProperty("structuralComplete", true);
        result.addProperty("complete", captureBindingsComplete);
        result.addProperty("selection",
                "REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE");
        return result;
    }

    private static JsonObject branchPolicy(String site, String guard) {
        JsonObject result = new JsonObject();
        result.addProperty("siteId", site);
        result.addProperty("policy", "PATH_ASSUMPTION");
        result.addProperty("guard", guard);
        result.addProperty("requiredOutcome", true);
        result.addProperty("role", "REACHABILITY");
        return result;
    }

    private static JsonObject consumerRegion(
            String regionId, String method, String[] ports, String[] cells) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", regionId);
        result.addProperty("rootMethod", method);
        result.addProperty("anchorMethod", method);
        result.add("methods", jsonStrings(method));
        JsonArray inputs = new JsonArray();
        for (int index = 0; index < ports.length; index++) {
            inputs.add(primitivePort(ports[index], cells[index]));
        }
        result.add("symbolicInputs", inputs);
        result.add("outputs", new JsonArray());
        result.add("branchPolicies", new JsonArray());
        result.add("models", new JsonArray());
        return result;
    }

    private static String regionEdge(
            String id, String fromRegion, String toRegion, String cell) {
        return "{\"edgeId\":\"" + id + "\","
                + "\"fromRegion\":\"" + fromRegion + "\","
                + "\"toRegion\":\"" + toRegion + "\","
                + "\"fromPort\":\"" + cell + "\","
                + "\"toPort\":\"" + cell + "\","
                + "\"kind\":\"SHARED_STATE\","
                + "\"relation\":\"READ_FROM_CANDIDATE\","
                + "\"requiresOrder\":true,"
                + "\"requiresObjectIdentity\":true}\n";
    }

    private static JsonArray jsonStrings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) {
            result.add(value);
        }
        return result;
    }

    private static List<Map<String, Object>> derivedActivations(
            RuntimeRegionPlanner.Result result) {
        List<Map<String, Object>> derived = new ArrayList<>();
        for (Map<String, Object> activation : result.activations) {
            if (String.valueOf(activation.get("activationId"))
                    .startsWith("ACT.UPSTREAM.")) {
                derived.add(activation);
            }
        }
        return derived;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> upstreamDemandFor(
            List<Map<String, Object>> derived, String downstreamRegion) {
        for (Map<String, Object> activation : derived) {
            List<Map<String, Object>> bindings =
                    (List<Map<String, Object>>) activation.get(
                            "edgeBindings");
            if (!bindings.isEmpty() && downstreamRegion.equals(
                    bindings.get(0).get("toRegion"))) {
                return activation;
            }
        }
        throw new AssertionError("missing upstream demand for "
                + downstreamRegion);
    }

    @SuppressWarnings("unchecked")
    private static List<String> edgeBindingIds(
            Map<String, Object> activation) {
        List<String> result = new ArrayList<>();
        for (Map<String, Object> binding
                : (List<Map<String, Object>>) activation.get(
                "edgeBindings")) {
            result.add(String.valueOf(binding.get("edgeId")));
        }
        return result;
    }

    private static Map<String, Object> requestedOutputActivation(
            RuntimeRegionPlanner.Result result) {
        for (Map<String, Object> activation : result.activations) {
            if (activation.containsKey("requestedOutputSlice")) {
                return activation;
            }
        }
        throw new AssertionError("missing requested-output activation");
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> requestedOutputSlice(
            RuntimeRegionPlanner.Result result) {
        return (Map<String, Object>) requestedOutputActivation(result).get(
                "requestedOutputSlice");
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> outputClosure(
            Map<String, Object> activation) {
        Object encoded = activation.get("outputClosure");
        assertTrue("missing canonical outputClosure: " + activation,
                encoded instanceof JsonObject);
        return (Map<String, Object>) jsonValue((JsonElement) encoded);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> outputMember(
            Map<String, Object> activation, String outputPort) {
        List<Map<String, Object>> members =
                (List<Map<String, Object>>) outputClosure(activation).get(
                        "members");
        for (Map<String, Object> member : members) {
            Map<String, Object> output =
                    (Map<String, Object>) member.get("output");
            if (outputPort.equals(output.get("portId"))) {
                return member;
            }
        }
        throw new AssertionError("missing outputClosure member "
                + outputPort);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> outputSlice(
            Map<String, Object> activation, String outputPort) {
        return (Map<String, Object>) outputMember(
                activation, outputPort).get("slice");
    }

    private static void assertCanonicalOutputOnly(
            Map<String, Object> activation) {
        assertTrue(activation.containsKey("outputClosure"));
        for (String legacy : Arrays.asList("requestedOutput",
                "requestedOutputSlice", "requestedOutputCapture",
                "requestedOutputCaptureRequired",
                "requestedOutputCaptureComplete",
                "requestedOutputMethods", "outputs")) {
            assertFalse("canonical writer retained " + legacy,
                    activation.containsKey(legacy));
        }
    }

    private static Object jsonValue(JsonElement element) {
        if (element == null || element.isJsonNull()) {
            return null;
        }
        if (element.isJsonObject()) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (Map.Entry<String, JsonElement> entry
                    : element.getAsJsonObject().entrySet()) {
                result.put(entry.getKey(), jsonValue(entry.getValue()));
            }
            return result;
        }
        if (element.isJsonArray()) {
            List<Object> result = new ArrayList<>();
            for (JsonElement member : element.getAsJsonArray()) {
                result.add(jsonValue(member));
            }
            return result;
        }
        if (element.getAsJsonPrimitive().isBoolean()) {
            return element.getAsBoolean();
        }
        if (element.getAsJsonPrimitive().isNumber()) {
            Number number = element.getAsNumber();
            double decimal = number.doubleValue();
            long integral = number.longValue();
            if (Double.compare(decimal, (double) integral) == 0) {
                if (integral >= Integer.MIN_VALUE
                        && integral <= Integer.MAX_VALUE) {
                    return (int) integral;
                }
                return integral;
            }
            return decimal;
        }
        return element.getAsString();
    }

    private static String carrierBinding(String dependencyCell) {
        return "{\"dependencyCell\":\"" + dependencyCell + "\","
                + "\"inputPort\":\"REGION.W.in.0\","
                + "\"bindingAuthority\":"
                + "\"UNIQUE_ROOT_ARGUMENT_CARRIER\"}";
    }

    private static String sliceBinding(String dependencyCell,
                                       String inputPort, String method) {
        return "{\"dependencyCell\":\"" + dependencyCell + "\","
                + "\"inputPort\":\"" + inputPort + "\","
                + "\"bindingAuthority\":\"EXACT_CELL_IDENTITY\","
                + "\"dependencyMethods\":[\"" + method + "\"]}";
    }

    private static String causalReference(String edgeId, String method,
                                          String siteId) {
        return "{\"edgeId\":\"" + edgeId + "\",\"method\":\""
                + method + "\",\"siteId\":\"" + siteId + "\","
                + "\"transferKind\":\"HEAP_WRITE\","
                + "\"kind\":\"field_mutation\"}";
    }

    private static String accessorFieldRegion(String field, String getter,
                                              String site) {
        return "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                + "\",\"methods\":[\"" + HANDLE + "\",\"" + getter
                + "\"],\"symbolicInputs\":[{\"portId\":"
                + "\"REGION.0.in.0\",\"cell\":\"" + field
                + "\",\"sourceKind\":\"SHARED_HEAP\","
                + "\"projection\":\"value\","
                + "\"bindingMode\":\"FIELD_ACCESS\","
                + "\"accessFieldSignature\":\"" + field + "\","
                + "\"accessOwnerClass\":\"example.Command\","
                + "\"accessFieldType\":\"int\","
                + "\"accessField\":\"action\","
                + "\"accessorCallerMethod\":\"" + HANDLE + "\","
                + "\"accessorCallSiteId\":\"" + site + "\","
                + "\"accessorCallUnitIndex\":11,"
                + "\"accessorDeclaredCallee\":\"" + getter + "\","
                + "\"accessorImplementationMethod\":\"" + getter
                + "\",\"accessorImplementationAuthority\":"
                + "\"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY\","
                + "\"accessorCallSiteAuthority\":"
                + "\"STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                + "ACCESSOR_CALLSITE_V1\"}],\"outputs\":[],"
                + "\"branchPolicies\":[],\"models\":[]}\n";
    }

    private static String frozenAccessorEdge(String id, String field,
                                             String getter, String site) {
        return "{\"id\":\"" + id
                + "\",\"schemaVersion\":2"
                + ",\"semanticMode\":\"ASSERTABLE\""
                + ",\"kind\":\"accessor_field_return\","
                + "\"transferKind\":\"HEAP_READ\","
                + "\"relation\":\"value_flow\","
                + "\"fromCell\":\"" + field + "\","
                + "\"toCell\":\"" + HANDLE + "::$r4\","
                + "\"method\":\"" + HANDLE + "\","
                + "\"siteId\":\"" + site + "\","
                + "\"unitIndex\":11,\"invoke\":\"" + getter + "\","
                + "\"declaredFieldSignature\":\"" + field + "\","
                + "\"declaredFieldOwner\":\"example.Command\","
                + "\"declaredFieldType\":\"java.lang.String\","
                + "\"declaredFieldName\":\"name\","
                + "\"declaredFieldAuthority\":"
                + "\"SOOT_RESOLVED_DECLARATION_HIERARCHY\","
                + "\"accessorImplementationMethod\":\"" + getter + "\","
                + "\"accessorImplementationAuthority\":"
                + "\"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY\"}";
    }

    private static RuntimeRegionPlanner.Result planSaslUsernameEdge(
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> events) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String fromPort = SASL_CLIENT + ".param3:java.lang.String";
            writeRegions(regions, (regionWithOutput("REGION.LEGACY.FIRST",
                    "<example.UnobservedProducer: void run()>", fromPort)
                    + regionWithOutput("REGION.C", SASL_CLIENT, fromPort)
                    + region("REGION.S", SASL_SERVER)).getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.SASL.RUNTIME\","
                    + "\"fromRegion\":\"REGION.LEGACY.FIRST\","
                    + "\"toRegion\":\"REGION.S\","
                    + "\"fromPort\":\"" + fromPort + "\","
                    + "\"toPort\":\"" + SASL_SERVER + "::$r4\","
                    + "\"kind\":\"SASL_TRANSFER\","
                    + "\"candidateRelation\":\"EQUALITY\","
                    + "\"mappingKind\":\"hdfs_sasl_username\","
                    + "\"mappingAuthority\":"
                    + "\"STATIC_HDFS_SASL_CONTRACT\","
                    + "\"payloadEqualityCheckRequired\":true,"
                    + "\"requiresOrder\":true,"
                    + "\"semanticMode\":\"MAPPING_ONLY\","
                    + "\"evidence\":[\"STATIC_PROTOCOL\","
                    + "\"mapping evidence retained\"],"
                    + "\"siteId\":\"synthetic:hdfs_sasl_username\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    companionStaticGraph(regions).toFile(),
                    methods, events, Collections.emptyList());
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result demandSlicedSaslInputResult(
            boolean ambiguous) throws Exception {
        return demandSlicedSaslInputResult(ambiguous, "HEAP_READ",
                "value_flow");
    }

    private static RuntimeRegionPlanner.Result demandSlicedSaslInputResult(
            boolean duplicateDefinition, String directTransferKind,
            String directRelation) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            Path graph = folder.getRoot().toPath().resolve(
                    "static_dataflow_edges.jsonl");
            String fromPort = SASL_CLIENT + ".param3:java.lang.String";
            String rawEndpoint = SASL_SERVER + "::$r4";
            String defaultField = "<javax.security.auth.callback."
                    + "NameCallback: java.lang.String defaultName>";
            String guardSite = SASL_SERVER + "#u8";
            String failure = SASL_SERVER + "#u11#exception:example.Bug";
            String serverRegion = "{\"regionId\":\"REGION.S\","
                    + "\"rootMethod\":\"" + SASL_SERVER + "\","
                    + "\"anchorMethod\":\"" + SASL_SERVER + "\","
                    + "\"methods\":[\"" + SASL_SERVER + "\"],"
                    + "\"symbolicInputs\":["
                    + inputPort("REGION.S.in.0", defaultField,
                    "PROTOCOL_INPUT")
                    + "],\"outputs\":[{\"portId\":\"REGION.S.out.0\","
                    + "\"cell\":\"" + failure + "\","
                    + "\"kind\":\"FAILURE_PREDICATE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + guardSite
                    + "\",\"policy\":\"PATH_ASSUMPTION\","
                    + "\"guard\":\"name == null\","
                    + "\"requiredOutcome\":false,"
                    + "\"role\":\"REACHABILITY\"}],\"models\":[]}\n";
            writeRegions(regions, (regionWithOutput("REGION.C", SASL_CLIENT,
                    fromPort) + serverRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.SASL.DEMAND\","
                    + "\"fromRegion\":\"REGION.C\","
                    + "\"toRegion\":\"REGION.S\","
                    + "\"fromPort\":\"" + fromPort + "\","
                    + "\"toPort\":\"" + rawEndpoint + "\","
                    + "\"kind\":\"SASL_TRANSFER\","
                    + "\"candidateRelation\":\"EQUALITY\","
                    + "\"mappingKind\":\"hdfs_sasl_username\","
                    + "\"mappingAuthority\":"
                    + "\"STATIC_HDFS_SASL_CONTRACT\","
                    + "\"payloadEqualityCheckRequired\":true,"
                    + "\"requiresOrder\":true,"
                    + "\"semanticMode\":\"MAPPING_ONLY\","
                    + "\"siteId\":\"synthetic:hdfs_sasl_username\"}\n")
                    .getBytes(StandardCharsets.UTF_8));
            String frozen = frozenDemandEdge("DF.GUARD", "GUARD",
                    "control_depends_on", rawEndpoint, failure,
                    SASL_SERVER, guardSite, 8)
                    + frozenDemandEdge("DF.DIRECT.DEFAULT",
                    directTransferKind, directRelation, defaultField,
                    rawEndpoint, SASL_SERVER,
                    SASL_SERVER + "#u4", 4)
                    + (duplicateDefinition ? frozenDemandEdge(
                    "DF.DIRECT.DUPLICATE", directTransferKind,
                    directRelation, defaultField, rawEndpoint, SASL_SERVER,
                    SASL_SERVER + "#u5", 5) : "");
            writeStaticGraph(graph, frozen.getBytes(StandardCharsets.UTF_8));

            String fingerprint = "sha256:same-sasl-user";
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(55, "BRANCH",
                            SASL_SERVER, 2, 0, 0, guardSite, -1, "", 0,
                            "", true, true);
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    graph.toFile(), Arrays.asList(
                            methodContext(1, SASL_CLIENT, 1, "BALANCER",
                                    "Dispatcher", 31L),
                            methodContext(20, SASL_SERVER, 2, "DATANODE",
                                    "DataXceiver", 41L)),
                    Arrays.asList(saslArgument(10, 1, fingerprint),
                            saslCallbackReturn(50, 2, fingerprint), branch),
                    Collections.emptyList());
        } finally {
            folder.delete();
        }
    }

    private static Map<String, Object> edgeValidationFor(
            RuntimeRegionPlanner.Result result, String fromRegion) {
        for (Map<String, Object> validation : result.edgeValidations) {
            if (fromRegion.equals(validation.get("fromRegion"))) {
                return validation;
            }
        }
        throw new AssertionError("missing edge validation from "
                + fromRegion);
    }

    @SuppressWarnings("unchecked")
    private static void assertActivationInputContract(
            Map<String, Object> activation) {
        List<Map<String, Object>> symbolize =
                (List<Map<String, Object>>) activation.get("symbolize");
        List<String> inputPorts = new ArrayList<>();
        for (Map<String, Object> action : symbolize) {
            String symbol = String.valueOf(action.get("symbol"));
            assertFalse(symbol.isEmpty());
            assertFalse(inputPorts.contains(symbol));
            inputPorts.add(symbol);
        }
    }

    private static String regionWithOutput(String id, String method,
                                           String outputCell) {
        return "{\"regionId\":\"" + id + "\",\"rootMethod\":\""
                + method + "\",\"anchorMethod\":\"" + method
                + "\",\"methods\":[\"" + method
                + "\"],\"symbolicInputs\":[],\"outputs\":[{"
                + "\"portId\":\"" + id + ".out.0\",\"cell\":\""
                + outputCell + "\",\"kind\":\"SINK_STATE\"}],"
                + "\"branchPolicies\":[],\"models\":[]}\n";
    }

    private static RuntimeRegionPlanner.RuntimeEvent saslArgument(
            long seq, long callId, String fingerprint) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "METHOD_ARGUMENT",
                SASL_CLIENT, callId, 0, 0, SASL_CLIENT + "#entry", "",
                3, "java.lang.String", 101, "", false, false,
                fingerprint, true, 1, "COMPLETE");
    }

    private static RuntimeRegionPlanner.RuntimeEvent methodArgument(
            long seq, String method, long callId, int argumentIndex,
            String runtimeType) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "METHOD_ARGUMENT",
                method, callId, 0, 0, method + "#entry", "",
                argumentIndex, runtimeType, (int) (seq + 100), "", false,
                false, "", false, 0, "TEST_NO_FINGERPRINT");
    }

    private static RuntimeRegionPlanner.RuntimeEvent saslCallbackReturn(
            long seq, long callId, String fingerprint) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "CALL_SITE_RETURN",
                SASL_SERVER, callId, 9, 0, SASL_SERVER + "#u4",
                NAME_CALLBACK_DEFAULT, -1, "java.lang.String", 102, "",
                false, false, fingerprint, true, 1, "COMPLETE");
    }

    private static RuntimeRegionPlanner.MethodEvent method(long seq, String method,
                                                            long callId,
                                                            long parentCallId,
                                                            long parentSiteId) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle", "DATANODE",
                "DataXceiver-1", 27L, method, 42, "example.Handler", callId,
                parentCallId, parentSiteId, seq * 100L);
    }

    private static RuntimeRegionPlanner.MethodEvent methodWithReceiver(
            long seq, String method, long callId, int receiverObjectId) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle",
                "DATANODE", "DataXceiver-1", 27L, method,
                receiverObjectId, "example.Actor", callId, 0, 0,
                seq * 100L);
    }

    private static RuntimeRegionPlanner.MethodEvent rootContextMethod(
            long seq, String method, long callId, String threadName,
            String receiverRuntimeClass, long tid) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle",
                "WORKER", threadName, tid, method, (int) (100 + callId),
                receiverRuntimeClass, callId, 0, 0, seq * 100L);
    }

    private static RuntimeRegionPlanner.MethodEvent methodContext(
            long seq, String method, long callId, String process,
            String threadName, long tid) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle", process,
                threadName, tid, method, 42, "example.State", callId,
                0, 0, seq * 100L);
    }

    private static void writeRegions(Path path, byte[] rows)
            throws IOException {
        StringBuilder regions = new StringBuilder();
        Map<String, JsonObject> canonicalEdges = new LinkedHashMap<>();
        String input = new String(rows, StandardCharsets.UTF_8);
        for (String line : input.split("\\r?\\n")) {
            if (line.trim().isEmpty()) {
                continue;
            }
            JsonObject region = JsonParser.parseString(line)
                    .getAsJsonObject();
            region.addProperty("schemaVersion", 2);
            for (JsonElement sliceElement
                    : region.has("outputSlices")
                    ? region.getAsJsonArray("outputSlices")
                    : new JsonArray()) {
                JsonObject slice = sliceElement.getAsJsonObject();
                JsonArray embedded = slice.has("causalEdges")
                        ? slice.getAsJsonArray("causalEdges")
                        : new JsonArray();
                for (JsonElement edgeElement : embedded) {
                    JsonObject edge = edgeElement.getAsJsonObject().deepCopy();
                    JsonElement edgeId = edge.remove("edgeId");
                    String id = edgeId == null ? "" : edgeId.getAsString();
                    if (id.isEmpty()) {
                        throw new IOException("embedded test edge lacks id");
                    }
                    edge.addProperty("schemaVersion", 2);
                    if (!edge.has("semanticMode")) {
                        edge.addProperty("semanticMode", "ASSERTABLE");
                    }
                    edge.addProperty("id", id);
                    JsonObject previous = canonicalEdges.put(id, edge);
                    if (previous != null && !previous.equals(edge)) {
                        throw new IOException(
                                "conflicting embedded test edge " + id);
                    }
                }
                slice.remove("causalEdges");
                slice.remove("causalEdgeCount");
            }
            regions.append(region).append('\n');
        }
        Files.write(path, regions.toString().getBytes(
                StandardCharsets.UTF_8));
        StringBuilder graph = new StringBuilder();
        for (JsonObject edge : canonicalEdges.values()) {
            graph.append(edge).append('\n');
        }
        Files.write(companionStaticGraph(path), graph.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static void writeStaticGraph(Path path, byte[] rows)
            throws IOException {
        writeVersionedRows(path, rows);
    }

    private static void writeStaticGraph(Path path, List<String> rows,
                                         java.nio.charset.Charset charset)
            throws IOException {
        writeVersionedRows(path, String.join("\n", rows).getBytes(charset));
    }

    private static void writeVersionedRows(Path path, byte[] rows)
            throws IOException {
        StringBuilder result = new StringBuilder();
        String input = new String(rows, StandardCharsets.UTF_8);
        for (String line : input.split("\\r?\\n")) {
            if (line.trim().isEmpty()) {
                continue;
            }
            JsonObject object = JsonParser.parseString(line)
                    .getAsJsonObject();
            object.addProperty("schemaVersion", 2);
            if (!object.has("semanticMode")) {
                object.addProperty("semanticMode", "ASSERTABLE");
            }
            result.append(object).append('\n');
        }
        Files.write(path, result.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static Path companionStaticGraph(Path regions) {
        return regions.resolveSibling("static_dataflow_edges.jsonl");
    }

    private static int derivedActivationCount(
            RuntimeRegionPlanner.Result result) {
        int count = 0;
        for (Map<String, Object> activation : result.activations) {
            if (String.valueOf(activation.get("activationId"))
                    .startsWith("ACT.UPSTREAM.")) {
                count++;
            }
        }
        return count;
    }

    @SuppressWarnings("unchecked")
    private static String admissionState(Map<String, Object> activation) {
        Object value = activation.get("admission");
        if (!(value instanceof Map)) {
            return "";
        }
        Object state = ((Map<String, Object>) value).get("state");
        return state == null ? "" : String.valueOf(state);
    }

    private static String region(String id, String method) {
        return "{\"regionId\":\"" + id + "\",\"rootMethod\":\""
                + method + "\",\"anchorMethod\":\"" + method
                + "\",\"methods\":[\"" + method
                + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                + "\"branchPolicies\":[],\"models\":[]}\n";
    }
}
