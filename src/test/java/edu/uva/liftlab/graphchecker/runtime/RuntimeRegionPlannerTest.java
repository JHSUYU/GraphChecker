package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeRegionPlannerTest {
    private static final Gson GSON = new Gson();
    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

            @Test
    public void oneCaptureClosesTwoDistinctWirePorts() throws Exception {
        String producerRoot = "<example.Transport: void respond(int)>";
        String firstConsumer = "<example.FirstClient: int status()>";
        String secondConsumer = "<example.SecondClient: int status()>";
        String callee =
                "<javax.servlet.http.HttpServletResponse: void setStatus(int)>";
        String firstExchange =
                "XCH.00000000-0000-3000-8000-00000000000a";
        String secondExchange =
                "XCH.00000000-0000-3000-8000-00000000000b";
        String requestExchange =
                "XCH.00000000-0000-3000-8000-00000000000c";
        String firstPort = firstExchange + ".resp.status";
        String secondPort = secondExchange + ".resp.status";
        String inputPort = requestExchange + ".req.status";
        String producerOccurrence = retained("REGION.P", 1).get(0);
        String firstOccurrence = retained("REGION.C1", 1).get(0);
        String secondOccurrence = retained("REGION.C2", 1).get(0);
        String captureSite = producerRoot + "#u7";
        String valueCell = producerRoot + ".param0:int";

        Map<String, Object> producerInput = wirePort(inputPort,
                requestExchange, "REQUEST", "METHOD_PARAMETER",
                producerRoot, -1, "", 0, "");
        Map<String, Object> firstOutput = wirePort(firstPort,
                firstExchange, "RESPONSE", "CALL_ARGUMENT",
                producerRoot, 7, callee, 0, producerOccurrence);
        Map<String, Object> secondOutput = wirePort(secondPort,
                secondExchange, "RESPONSE", "CALL_ARGUMENT",
                producerRoot, 7, callee, 0, producerOccurrence);
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", "", "selection", "STATE_CONTEXT",
                "runtimeOccurrenceIds", retained("REGION.P", 1),
                "methods", Collections.singletonList(producerRoot),
                "symbolicInputs", Collections.singletonList(producerInput),
                "outputs", Arrays.asList(firstOutput, secondOutput),
                "branchPolicies", Collections.emptyList());
        Map<String, Object> first = wireConsumerRegion("REGION.C1",
                firstConsumer, firstOccurrence, firstPort, firstExchange);
        Map<String, Object> second = wireConsumerRegion("REGION.C2",
                secondConsumer, secondOccurrence, secondPort,
                secondExchange);
        File regions = jsonl("wire-fanout-regions.jsonl",
                producer, first, second);
        File edges = jsonl("wire-fanout-edges.jsonl",
                protocolFlow("RPC.first", "REGION.P", "REGION.C1",
                        producerOccurrence, firstOccurrence, firstPort,
                        1L, 2L),
                protocolFlow("RPC.second", "REGION.P", "REGION.C2",
                        producerOccurrence, secondOccurrence, secondPort,
                        1L, 3L));
        Map<String, Object> identity = object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.wire.fanout.argument",
                "kind", "identity_binding",
                "transferKind", "IDENTITY_BINDING",
                "method", producerRoot, "siteId", captureSite,
                "unitIndex", 7, "fromCell", valueCell,
                "toCell", callee + ".param0:int",
                "regionIds", Collections.singletonList("REGION.P"));
        File refined = jsonl("wire-fanout-refined.jsonl", identity);
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "producer",
                        7, producerRoot, 10, "example.Transport", 1, 0, 0,
                        0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "first",
                        8, firstConsumer, 20, "example.FirstClient", 2, 0, 0,
                        0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "second",
                        9, secondConsumer, 30, "example.SecondClient", 3, 0,
                        0, 0L, 0L, 0L, 0L, null, false, "", ""));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime =
                Collections.singletonList(new RuntimeRegionPlanner.RuntimeEvent(
                        10L, "CALL_ARGUMENT", producerRoot, 1L, 100L, 0L,
                        captureSite, callee, 0, "", 0, "500",
                        null, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refined,
                Arrays.asList(
                        activation("REGION.P", 1L, producerRoot,
                                Collections.singletonList(1L)),
                        activation("REGION.C1", 2L, firstConsumer,
                                Collections.singletonList(2L)),
                        activation("REGION.C2", 3L, secondConsumer,
                                Collections.singletonList(3L))),
                methods, runtime, Collections.emptyList());

        Map<String, Object> producerPlan = null;
        for (Map<String, Object> plan : result.regionPlans) {
            if ("REGION.P".equals(plan.get("regionId"))) producerPlan = plan;
        }
        assertTrue(String.valueOf(result.regionPlans), producerPlan != null);
        Map<String, Object> goal = rows(
                producerPlan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        assertFalse(String.valueOf(goal), String.valueOf(
                goal.get("excludedOutputBlockers"))
                .contains("OUTPUT_ENDPOINT_AMBIGUOUS"));
        OutputClosureContract closure = OutputClosureCodec.decodeEnvelope(
                GSON.toJsonTree(goal.get("outputClosure"))
                        .getAsJsonObject());
        assertEquals(new java.util.TreeSet<>(Arrays.asList(
                firstPort, secondPort)), closure.outputPorts());
        assertEquals(2, closure.members().size());
    }

        @Test
    public void configuredSourcePhasesUseExactSiteOrderAndCallAncestry()
            throws Exception {
        String helper = "<example.Keys: void rotate()>";
        String field = "<example.Key: int keyId>";
        String consumeSite = helper + "#u3";
        String publishSite = helper + "#u7";
        Map<String, Object> region = fullRegion();
        region.put(ConfiguredSourcePhaseContract.DECLARATION_FIELD,
                Arrays.asList(
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "ROTATING.KEY", field, helper, 3),
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "ROTATING.KEY", field, helper, 7)));
        File regions = jsonl("source-phase-regions.jsonl", region);
        File edges = jsonl("source-phase-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("source-phase-refined.jsonl", refined);

        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t", 7,
                        ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t", 7,
                        TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                // The phase helper is in the recorded root subtree, but not
                // in activation.callIds: it is selected for rich tracing only.
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t", 7,
                        helper, 30, "example.Keys", 3, 2, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                // Same static site in another, unrelated activation must not
                // be admitted merely because its event is later in the trace.
                new RuntimeRegionPlanner.MethodEvent(9, "test", "other", 8,
                        helper, 40, "example.Keys", 99, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(4,
                        "CALL_SITE_ENTER", helper, 3, 301, 0,
                        consumeSite, "<example.Hook: int consume()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(5,
                        "CALL_SITE_ENTER", helper, 3, 302, 0,
                        publishSite, "<example.Hook: void publish()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6,
                        "CALL_SITE_ENTER", helper, 3, 303, 0,
                        consumeSite, "<example.Hook: int consume()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(7,
                        "CALL_SITE_ENTER", helper, 3, 304, 0,
                        publishSite, "<example.Hook: void publish()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(8, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(10,
                        "CALL_SITE_ENTER", helper, 99, 901, 0,
                        consumeSite, "<example.Hook: int consume()>",
                        -1, "", 0, "", null, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile,
                Collections.singletonList(activation("REGION.1", 1, ROOT,
                        Arrays.asList(1L, 2L))), methods, runtime,
                Collections.emptyList());

        assertEquals(1, result.regionPlans.size());
        Map<String, Object> plan = result.regionPlans.get(0);
        List<Map<String, Object>> phases = rows(plan.get(
                ConfiguredSourcePhaseContract.PLAN_FIELD));
        assertEquals(4, phases.size());
        assertEquals(Arrays.asList("PUBLISH", "PUBLISH", "PUBLISH",
                        "PUBLISH"),
                Arrays.asList(phases.get(0).get("phaseKind"),
                        phases.get(1).get("phaseKind"),
                        phases.get(2).get("phaseKind"),
                        phases.get(3).get("phaseKind")));
        assertEquals(Arrays.asList(1L, 1L, 2L, 2L), Arrays.asList(
                ((Number) phases.get(0).get("baselineOrdinal")).longValue(),
                ((Number) phases.get(1).get("baselineOrdinal")).longValue(),
                ((Number) phases.get(2).get("baselineOrdinal")).longValue(),
                ((Number) phases.get(3).get("baselineOrdinal")).longValue()));
        assertEquals(4L, phases.get(0).get("eventSeq"));
        assertEquals(301L, phases.get(0).get("invocationId"));
        assertEquals(3L, phases.get(0).get("ownerCallId"));
        assertEquals(Arrays.asList(3L, 2L, 1L),
                phases.get(0).get("enclosingCallIds"));
        assertEquals(ConfiguredSourcePhaseContract.phaseId(
                        String.valueOf(plan.get("occurrenceId")), consumeSite,
                        ConfiguredSourcePhaseContract.Phase.PUBLISH, 1),
                phases.get(0).get("phaseId"));
        List<Map<String, Object>> plannedBranches = rows(
                ((List<Map<String, Object>>) plan.get("closureGoals"))
                        .get(0).get("branches"));
        assertEquals(2L, plannedBranches.get(0).get("selectedCallId"));
        // The occurrence-level rows survive the strict plan decoder.  The
        // scheduler's task constructor copies this field verbatim.
        assertEquals(4, RegionInstancePlan.decode(
                GSON.toJsonTree(plan).getAsJsonObject()).json()
                .getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .size());
    }

        /**
     * Identity comes from the selected target event's source, while admission
     * still counts every compatible root entry the workload made -- including
     * the activations the failure closure discarded.
     */
    @Test
    public void targetOccurrenceUsesSelectedTargetSourceAndCausalAnchor()
            throws Exception {
        Map<String, Object> region = fullRegion();
        rows(region.get("branchPolicies")).get(0).put(
                "failureTarget", true);
        // The identity prefix is the selected target event's source, so the
        // retained occurrence of this region is named on that source.
        region.put("runtimeOccurrenceIds", Collections.singletonList(
                "cluster0/dn1#epoch1/region/REGION.1#1"));
        File regions = jsonl("target-source-regions.jsonl", region);
        File edges = jsonl("target-source-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("target-source-refined.jsonl", refined);
        SourceRef client = new SourceRef("EXTERNAL_APP", "CLIENT",
                "cluster0/client0", 0);
        SourceRef server = new SourceRef("CLUSTER_NODE", "DATANODE",
                "cluster0/dn1", 1);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        7, 101, 0, 0, client, true, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        8, 202, 101, 150, server, false,
                        "request#1", "api"));
        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Collections.singletonList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))), events,
                Collections.singletonList(
                        new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                                TARGET, 2, 0, 0, TARGET + "#u4", "", -1,
                                "", 0, "", Boolean.FALSE, null, "", "")),
                Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.get(0);
        assertEquals(server.key(), plan.get("sourceKey"));
        assertTrue(String.valueOf(plan.get("occurrenceId"))
                .startsWith(server.key() + "/region/"));
        assertEquals("SELECTED_TARGET_EVENT_SOURCE",
                plan.get("sourceAuthority"));
        Map<?, ?> anchor = (Map<?, ?>) ((Map<?, ?>) plan.get("rootSelector"))
                .get("causalAnchor");
        // The address names the source the activation ran on and the request
        // scope it ran inside, and holds no invocation ordinal at all.
        assertEquals(client.key(), anchor.get("sourceKey"));
        // The address is the stable source and nothing else: a request scope
        // is ambient context a replay of a long-lived service never republishes.
        // REGISTERED_SOURCE because this root's own receiver named that
        // source; see the INHERITED_CONTEXT case below for the other half.
        assertEquals("REGISTERED_SOURCE", anchor.get("kind"));
        assertFalse(anchor.containsKey("requestKeys"));
        assertFalse(((Map<?, ?>) plan.get("rootSelector"))
                .containsKey("occurrenceIndex"));

        // A replay address must survive an activation the failure closure
        // discarded: the retained activation is the second entry of its root
        // here, and an address that counted entries would have to say so.
        // This one does not - it names the same source and scope whichever
        // position the activation happens to occupy.
        Map<String, Object> discarding = fullRegion();
        discarding.put("runtimeOccurrenceIds", retained("REGION.1", 2));
        File discardedRegions = jsonl("discarded-regions.jsonl", discarding);
        File discardedEdges = jsonl("discarded-edges.jsonl");
        File discardedRefined = jsonl("discarded-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> repeated = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t",
                        7, ROOT, 30, "example.Root", 3, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "t",
                        7, TARGET, 40, "example.Target", 4, 3, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
        List<RuntimeRegionPlanner.RuntimeEvent> observed = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""));

        RuntimeRegionPlanner.Result discarded = planFiles(
                discardedRegions, discardedEdges, discardedRefined,
                Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                repeated, observed, Collections.emptyList());

        assertEquals(1, discarded.regionPlans.size());
        Map<String, Object> retainedPlan = discarded.regionPlans.get(0);
        assertTrue(String.valueOf(retainedPlan.get("occurrenceId"))
                .endsWith("#2"));
        Map<?, ?> retainedSelector =
                (Map<?, ?>) retainedPlan.get("rootSelector");
        assertFalse(retainedSelector.containsKey("occurrenceIndex"));
        Map<?, ?> retainedAnchor =
                (Map<?, ?>) retainedSelector.get("causalAnchor");
        assertEquals(RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                retainedAnchor.get("sourceKey"));
        assertEquals("UNREGISTERED_SOURCE", retainedAnchor.get("kind"));
    }

        @SuppressWarnings("unchecked")

        /**
     * The bounded versions of one endpoint fold into the single closure
     * member REGION-1 requires, and the fold subtracts nothing: every
     * version's causal delivery edge, input port and method stays in the
     * demand, the member stays anchored on the last recorded write - the
     * only single boundary that covers all of them - and every version's own
     * dynamic boundary is carried beside it in recorded write order.
     *
     * <p>The anchor alone was the loss the {@code OUTPUT_VERSION_ALIGNMENT_GAP}
     * declared.  With the whole ledger carried there is nothing left for it
     * to declare, so it is no longer published.</p>
     */
    @Test
    public void foldedOutputVersionsKeepEveryVersionsOwnEvidence() {
        OutputClosureContract early = versionClosure("RF.first",
                "REGION.1.in.early", "<example.Node: void early()>", 1, 30L);
        OutputClosureContract late = versionClosure("RF.second",
                "REGION.1.in.late", "<example.Node: void late()>", 2, 90L);

        OutputClosureContract folded =
                RuntimeRegionPlanner.coarseOccurrenceOutputVersions(
                        Arrays.asList(early, late));

        assertEquals(1, folded.members().size());
        assertTrue(String.valueOf(folded.toJson()),
                folded.executionScope().causalEdgeIds().containsAll(
                        Arrays.asList("RF.first", "RF.second")));
        assertTrue(String.valueOf(folded.toJson()),
                folded.executionScope().inputPorts().containsAll(
                        Arrays.asList("REGION.1.in.early",
                                "REGION.1.in.late")));
        assertTrue(String.valueOf(folded.toJson()),
                folded.executionScope().methods().containsAll(
                        Arrays.asList("<example.Node: void early()>",
                                "<example.Node: void late()>")));

        OutputClosureContract.Member member = folded.members().get(0);
        JsonArray versionScopes = member.slice().getAsJsonArray(
                RuntimeRegionPlanner.BOUNDED_VERSION_SCOPES);
        assertEquals(2, versionScopes.size());
        assertEquals(30L, versionScopes.get(0).getAsJsonObject()
                .get("selectedRuntimeEventSeq").getAsLong());
        assertEquals("RF.first", versionScopes.get(0).getAsJsonObject()
                .getAsJsonArray("causalEdgeIds").get(0).getAsString());
        assertEquals("REGION.1.in.early",
                versionScopes.get(0).getAsJsonObject()
                        .getAsJsonArray("inputPorts").get(0).getAsString());
        assertEquals(90L, versionScopes.get(1).getAsJsonObject()
                .get("selectedRuntimeEventSeq").getAsLong());
        assertEquals("RF.second", versionScopes.get(1).getAsJsonObject()
                .getAsJsonArray("causalEdgeIds").get(0).getAsString());
        assertEquals(90L, member.slice().get("selectedRuntimeEventSeq")
                .getAsLong());
        assertEquals(2, member.slice().get("activationLocalOccurrence")
                .getAsInt());
        assertFalse(String.valueOf(member.slice()),
                member.slice().has("alignmentGaps"));

        Map<String, Set<String>> selectedEdges = new LinkedHashMap<>();
        selectedEdges.put("REGION.1.out.state",
                Collections.singleton("RF.first"));
        OutputClosureContract projected = OutputClosureCodec
                .projectSelectedVersions(folded, selectedEdges);
        OutputClosureContract.Member selected = projected.members().get(0);
        assertEquals(Collections.singleton("RF.first"),
                projected.executionScope().causalEdgeIds());
        assertEquals(Collections.singleton("REGION.1.in.early"),
                projected.executionScope().inputPorts());
        assertEquals(30L, selected.slice()
                .get("selectedRuntimeEventSeq").getAsLong());
        assertEquals(1, selected.slice()
                .get("activationLocalOccurrence").getAsInt());
        assertEquals("REGION.1.in.early", selected.slice()
                .get("captureAnchorPort").getAsString());
        assertEquals("<example.Node: void early()>#u1", selected.slice()
                .get("captureAnchorSiteId").getAsString());
        assertEquals(31L, selected.slice()
                .get("definitionCompletionSeq").getAsLong());
        assertEquals(30L, selected.slice()
                .get("lastMutationCompletionSeq").getAsLong());
        assertEquals(7L, selected.slice()
                .get("observedDefinitionCallId").getAsLong());
        assertEquals("<example.Node: void early()>", selected.slice()
                .getAsJsonObject("replayEntry").get("method")
                .getAsString());
        assertEquals(31L, selected.slice()
                .getAsJsonArray("foldedMutationCompletionSeqs").get(0)
                .getAsLong());
        assertFalse(String.valueOf(selected.slice()), selected.slice()
                .toString().contains("<example.Node: void late()>"));
        assertEquals(1, projected.toJson().getAsJsonArray("members").get(0)
                .getAsJsonObject().getAsJsonObject("output")
                .get("outputOccurrence").getAsInt());
        assertFalse(projected.toJson().toString(), projected.toJson()
                .toString().contains("replayOccurrence"));
        assertFalse(selected.slice().has(
                RuntimeRegionPlanner.BOUNDED_VERSION_SCOPES));

        selectedEdges.put("REGION.1.out.state", new LinkedHashSet<>(
                Arrays.asList("RF.first", "RF.second")));
        OutputClosureContract selectedUnion = OutputClosureCodec
                .projectSelectedVersions(folded, selectedEdges);
        assertEquals(folded.closureFingerprint(),
                selectedUnion.closureFingerprint());

        // One version is still one member, byte for byte what it was before
        // any fold existed.
        assertEquals(late.closureFingerprint(),
                RuntimeRegionPlanner.coarseOccurrenceOutputVersions(
                        Collections.singletonList(late))
                        .closureFingerprint());
    }

    /** One recorded write version of one demanded heap output port. */
    private static OutputClosureContract versionClosure(
            String edgeId, String inputPort, String method,
            int occurrence, long writeSeq) {
        return versionClosure(edgeId, inputPort, method, occurrence,
                writeSeq, 7L);
    }

    private static OutputClosureContract versionClosure(
            String edgeId, String inputPort, String method,
            int occurrence, long writeSeq, long callId) {
        String port = "REGION.1.out.state";
        String cell = "<example.Node: int state>";
        String site = OutputCaptureSpec.FIELD_WRITE_STATE + ":"
                + ROOT + "#u5:" + cell;
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings(inputPort));
        slice.add("sites", strings(method + "#u1"));
        slice.add("staticSites", strings(ROOT + "#u5"));
        slice.add("methods", strings(method));
        slice.add("causalEdgeIds", strings(edgeId));
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("activationLocalOccurrence", occurrence);
        slice.addProperty("selectedRuntimeEventSeq", writeSeq);
        slice.addProperty("selectedRuntimeCallId", callId);
        slice.addProperty("captureAnchorPort", inputPort);
        slice.addProperty("captureAnchorSiteId", method + "#u1");
        slice.addProperty("definitionCompletionSeq", writeSeq + 1L);
        slice.addProperty("lastMutationCompletionSeq", writeSeq);
        slice.addProperty("observedDefinitionCallId", callId);
        slice.addProperty("foldedMutationCount", occurrence);
        slice.add("foldedMutationCompletionSeqs", strings(
                Long.toString(writeSeq + 1L)));
        JsonObject replayEntry = new JsonObject();
        replayEntry.addProperty("method", method);
        replayEntry.addProperty("receiverClass", "example.Node");
        slice.add("replayEntry", replayEntry);
        slice.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.state");
        capture.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        capture.add("fieldPath", strings("state"));
        capture.addProperty("javaType", "int");
        capture.addProperty("definitionMethod", ROOT);
        capture.addProperty("definitionUnitIndex", 5);
        capture.addProperty("outputSiteId", site);
        capture.addProperty("outputOccurrence", occurrence);
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);

        return OutputClosureCodec.singleton("REL.REGION.1", "REGION.1", Collections.<String>emptyList(),
                port, cell, "HEAP_STATE", "int", slice);
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Object integral(Object value) {
        if (value instanceof Double && ((Double) value) % 1 == 0) {
            return ((Double) value).longValue();
        }
        if (value instanceof Map) {
            for (Map.Entry<String, Object> entry
                    : ((Map<String, Object>) value).entrySet()) {
                entry.setValue(integral(entry.getValue()));
            }
        } else if (value instanceof List) {
            List<Object> list = (List<Object>) value;
            for (int i = 0; i < list.size(); i++) {
                list.set(i, integral(list.get(i)));
            }
        }
        return value;
    }

    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> out = new java.util.ArrayList<>();
        for (Object e : (List<?>) value) {
            if (e instanceof com.google.gson.JsonElement) {
                Map<String, Object> row = new com.google.gson.Gson().fromJson(
                        (com.google.gson.JsonElement) e,
                        new com.google.gson.reflect.TypeToken<
                                LinkedHashMap<String, Object>>() {}.getType());
                out.add((Map<String, Object>) integral(row));
            } else {
                out.add((Map<String, Object>) e);
            }
        }
        return out;
    }

    private static List<RuntimeRegionPlanner.MethodEvent> methods() {
        return Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
    }

    private static Map<String, Object> activation(
            String region, long call, String method, List<Long> calls) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", region,
                "rootCallId", call,
                "rootMethod", method,
                "selection", "STATE_CONTEXT",
                "callIds", calls,
                "observedMethods", method.equals(ROOT)
                        ? Arrays.asList(ROOT, TARGET)
                        : Collections.singletonList(method));
    }

    /**
     * Identities the region finalizer mints for the numbered observed
     * activations of {@code regionId} in a workload that registered no
     * source.  Retention is stated by identity, never by a recorded call.
     */
    private static List<String> retained(String regionId, int... ordinals) {
        List<String> result = new ArrayList<>();
        for (int ordinal : ordinals) {
            result.add("workload/unregistered#epoch0/region/" + regionId
                    + "#" + ordinal);
        }
        return result;
    }

    private static Map<String, Object> fullRegion() {
        Map<String, Object> branch = object("siteId", TARGET + "#u4",
                "method", TARGET, "unitIndex", 4,
                "requiredOutcome", false, "policy", "EXPLORE");
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1", "rootMethod", ROOT,
                "anchorMethod", TARGET,
                "selection", "EXCEPTION_CONTEXT",
                "runtimeOccurrenceIds", retained("REGION.1", 1),
                "methods", Arrays.asList(ROOT, TARGET),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.emptyList(),
                "branchPolicies", Collections.singletonList(branch));
    }

    private static Map<String, Object> wirePort(
            String portId, String exchange, String direction,
            String capture, String method, int unitIndex, String callee,
            int argumentIndex, String occurrenceId) {
        Map<String, Object> port = object(
                "portId", portId,
                "sourceKind", "COMMUNICATION_SITE_PORT",
                "dependencyRole", "VALUE_FRONTIER",
                "javaType", "int",
                "direction", direction,
                "handoffLeafPath", portId,
                "exchangeSiteKey", exchange,
                "callSiteId", unitIndex < 0 ? method
                        : method + "#u" + unitIndex,
                "outputCaptureKind", capture,
                "definitionMethod", method);
        if (unitIndex >= 0) port.put("definitionUnitIndex", unitIndex);
        if (!callee.isEmpty()) port.put("declaredCallee", callee);
        if (argumentIndex >= 0) port.put("argumentIndex", argumentIndex);
        if (!occurrenceId.isEmpty()) port.put("occurrenceId", occurrenceId);
        return port;
    }

    private static Map<String, Object> wireConsumerRegion(
            String regionId, String root, String occurrenceId,
            String portId, String exchange) {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", regionId, "rootMethod", root,
                "anchorMethod", "", "selection", "STATE_CONTEXT",
                "runtimeOccurrenceIds", Collections.singletonList(
                        occurrenceId),
                "methods", Collections.singletonList(root),
                "symbolicInputs", Collections.singletonList(wirePort(
                        portId, exchange, "RESPONSE", "CALL_RETURN",
                        root, 5, "<example.Response: int code()>", -1, "")),
                "outputs", Collections.emptyList(),
                "branchPolicies", Collections.emptyList());
    }

    private static Map<String, Object> protocolFlow(
            String edgeId, String fromRegion, String toRegion,
            String fromOccurrence, String toOccurrence, String portId,
            long fromRootCallId, long toRootCallId) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_PROTOCOL_FLOW", "edgeId", edgeId,
                "fromRegion", fromRegion, "toRegion", toRegion,
                "fromPort", portId, "toPort", portId,
                "fromRootCallId", fromRootCallId,
                "toRootCallId", toRootCallId,
                "fromOccurrenceId", fromOccurrence,
                "toOccurrenceId", toOccurrence,
                "direction", "RESPONSE", "attemptId", "attempt-1",
                "exchangeLeg", edgeId + "\nattempt-1\nRESPONSE",
                "senderEventSeq", 20L, "receiverEventSeq", 30L,
                "dependencyRole", "VALUE_FRONTIER",
                "authority", AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
    }

    private static Map<String, Object> candidateEdge() {
        return object("schemaVersion", 3, "id", "DF.1",
                "kind", "exception_guard", "transferKind", "GUARD",
                "method", TARGET, "siteId", TARGET + "#u4",
                "fromCell", "guard", "toCell", "exception");
    }

    @SafeVarargs
    private final File jsonl(String name, Map<String, Object>... rows)
            throws Exception {
        List<String> lines = new ArrayList<>();
        for (Map<String, Object> row : rows) {
            lines.add(GSON.toJson(row));
        }
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), lines, StandardCharsets.UTF_8);
        return file;
    }

        private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }

    private static RuntimeRegionPlanner.Result planFiles(
            File regionFile, File regionEdgeFile, File refinedGraphFile,
            Collection<Map<String, Object>> runtimeSeeds,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents,
            List<RuntimeRegionPlanner.FieldAccessEvent> fieldEvents) {
        return RuntimeRegionPlanner.plan(
                RuntimeRegionPlanner.read(regionFile),
                RuntimeRegionPlanner.read(regionEdgeFile),
                RuntimeRegionPlanner.RefinedFlowIndex.read(refinedGraphFile),
                String.valueOf(regionFile), String.valueOf(regionEdgeFile),
                runtimeSeeds, methods, runtimeEvents, fieldEvents,
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList());
    }

    }
