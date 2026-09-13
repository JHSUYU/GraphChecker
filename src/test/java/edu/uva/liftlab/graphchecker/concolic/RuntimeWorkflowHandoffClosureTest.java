package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/** Focused check for retaining observed communication ancestry. */
public class RuntimeWorkflowHandoffClosureTest {

    @Test
    public void inboundHandoffReplacesOnlyItsExactSymbolicInput() {
        String port = "XCH.test.resp.value";
        String receiver = "source/c/region/R.C#1";
        JsonArray actions = new JsonArray();
        actions.add(input(port, "SYMBOLIC"));
        actions.add(input("manual.root", "SYMBOLIC"));
        actions.add(input(port, "CONCRETE"));
        JsonArray edges = new JsonArray();
        edges.add(protocolEdge("source/p/region/R.P#1",
                receiver + "#a2", port));
        JsonObject declarations = new JsonObject();
        JsonArray handoffs = new JsonArray();
        handoffs.add(inboundHandoff(port));
        declarations.add(CommunicationHandoffSpec.FIELD, handoffs);

        JsonArray retained = ConcolicScheduler
                .removeInboundProtocolHandoffInputs(actions, edges,
                        receiver, CommunicationHandoffSpec.decode(
                                declarations));

        assertEquals(2, retained.size());
        assertEquals("manual.root", retained.get(0).getAsJsonObject()
                .get("symbol").getAsString());
        assertEquals("CONCRETE", retained.get(1).getAsJsonObject()
                .get("mode").getAsString());
        assertEquals(3, ConcolicScheduler
                .removeInboundProtocolHandoffInputs(actions, edges,
                        "source/other/region/R.X#1",
                        CommunicationHandoffSpec.decode(declarations))
                .size());
        assertEquals(3, ConcolicScheduler
                .removeInboundProtocolHandoffInputs(actions, edges,
                        receiver, Collections
                                .<CommunicationHandoffSpec>emptyList())
                .size());
    }

    @Test
    public void retainsBothEndpointsOnlyInsideOneObservedSession() {
        String scope = "replay-group:one";
        String producer = "source/p#1";
        String consumer = "source/c#1";
        JsonObject valid = summary(scope, "task.c", consumer,
                "task.p", producer, consumer, 2L);
        JsonObject otherSession = summary(scope, "task.ignored", consumer,
                "task.other", producer, consumer, 4L);
        otherSession.getAsJsonArray(VmHandoffEvidence.FIELD)
                .get(0).getAsJsonObject().addProperty(
                        "boundarySessionScope", "replay-group:two");

        Map<String, Set<String>> selected = RuntimeWorkflowDiscovery
                .observedHandoffEndpointTasks(
                        Arrays.asList(valid, otherSession),
                        new java.util.LinkedHashSet<>(Arrays.asList(
                                producer, consumer)));

        assertEquals(Collections.singleton(scope), selected.keySet());
        assertEquals(new java.util.LinkedHashSet<>(Arrays.asList(
                "task.p", "task.c")), selected.get(scope));
        assertEquals(Collections.emptyMap(), RuntimeWorkflowDiscovery
                .observedHandoffEndpointTasks(
                        Collections.singletonList(valid),
                Collections.singleton(consumer)));
    }

    @Test
    public void retainsObservedWriterOutsideStaticCandidateClosure()
            throws Exception {
        String scope = "replay-group:one";
        String producerOccurrence = "source/p/region/R.P#1";
        String consumerOccurrence = "source/c/region/R.C#1";
        String bridgeOccurrence = "source/b/region/R.B#1";
        String targetOccurrence = "source/t/region/R.T#1";
        String writerOccurrence = "source/w/region/R.W#1";
        JsonArray graph = new JsonArray();
        graph.add(readEdge(producerOccurrence, consumerOccurrence, 1L));
        graph.add(readEdge(consumerOccurrence, bridgeOccurrence, 2L));
        graph.add(readEdge(bridgeOccurrence, targetOccurrence, 3L));
        RegionInstancePlan producer = plan("source/p", "R.P",
                producerOccurrence, "G.P", false, graph);
        RegionInstancePlan consumer = plan("source/c", "R.C",
                consumerOccurrence, "G.C", false, graph);
        RegionInstancePlan bridge = plan("source/b", "R.B",
                bridgeOccurrence, "G.B", false, graph);
        RegionInstancePlan target = plan("source/t", "R.T",
                targetOccurrence, "G.T", true, graph);
        RegionInstancePlan writer = plan("source/w", "R.W",
                writerOccurrence, "G.W", false, graph);

        JsonObject targetSummary = new JsonObject();
        targetSummary.addProperty("boundarySessionScope", scope);
        targetSummary.addProperty("sourceKey", "source/t");
        targetSummary.addProperty("regionId", "R.T");
        targetSummary.addProperty("goalId", "G.T");
        targetSummary.addProperty("taskId", "TASK.T");
        targetSummary.addProperty("occurrenceId",
                targetOccurrence + "#a1");

        JsonObject producerSummary = taskSummary(scope, "source/p", "R.P",
                "G.P", "TASK.P", producerOccurrence + "#a1");
        JsonObject consumerSummary = summary(scope, "TASK.C",
                consumerOccurrence, "TASK.P", producerOccurrence,
                consumerOccurrence, 2L);
        JsonObject bridgeSummary = taskSummary(scope, "source/b", "R.B",
                "G.B", "TASK.B", bridgeOccurrence + "#a1");
        bridgeSummary.add(SharedStateEvidence.RECORDED_FIELD,
                guardedWriterRecord(scope, bridgeOccurrence + "#a1",
                        writerOccurrence + "#a4"));

        JsonObject writerSummary = taskSummary(scope, "source/w", "R.W",
                "G.W", "TASK.W", writerOccurrence + "#a4");

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(
                        Arrays.asList(producer, consumer, bridge, target,
                                writer),
                        Arrays.asList(targetSummary, producerSummary,
                                consumerSummary, bridgeSummary,
                                writerSummary));
        Set<String> selected = new LinkedHashSet<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            selected.add(selection.occurrenceId);
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                producerOccurrence, consumerOccurrence, bridgeOccurrence,
                targetOccurrence, writerOccurrence)), selected);
    }

    /**
     * A writer publishes its {@code writerActivationClosure} on its own
     * summary, whose recorded envelope carries no read of its own.  The
     * enclosing activation that closure names must still enter the active
     * corpus: {@code SymbolicPropagationClosure.writerCaseClosure} resolves
     * exactly that address later and fails closed when the task is absent.
     */
    @Test
    public void retainsEnclosingActivationNamedByAWriterOwnClosure()
            throws Exception {
        String scope = "replay-group:one";
        String targetOccurrence = "source/t/region/R.T#1";
        String enclosingOccurrence = "source/e/region/R.E#1";
        JsonArray graph = new JsonArray();
        RegionInstancePlan target = plan("source/t", "R.T",
                targetOccurrence, "G.T", true, graph);
        RegionInstancePlan enclosing = plan("source/e", "R.E",
                enclosingOccurrence, "G.E", false, graph);

        JsonObject targetSummary = taskSummary(scope, "source/t", "R.T",
                "G.T", "TASK.T", targetOccurrence + "#a1");
        targetSummary.add(SharedStateEvidence.RECORDED_FIELD,
                unreadWriterRecord(scope, targetOccurrence + "#a1",
                        enclosingOccurrence + "#a3", true));

        assertEquals(new LinkedHashSet<>(Arrays.asList(targetOccurrence,
                enclosingOccurrence)), selectedOccurrences(
                Arrays.asList(target, enclosing),
                Arrays.asList(targetSummary, taskSummary(scope, "source/e",
                        "R.E", "G.E", "TASK.E",
                        enclosingOccurrence + "#a3"))));

        // An incomplete closure names no case the composer may resolve, so it
        // still admits nothing: the fix widens named evidence only.
        JsonObject incomplete = taskSummary(scope, "source/t", "R.T", "G.T",
                "TASK.T", targetOccurrence + "#a1");
        incomplete.add(SharedStateEvidence.RECORDED_FIELD,
                unreadWriterRecord(scope, targetOccurrence + "#a1",
                        enclosingOccurrence + "#a3", false));
        assertEquals(Collections.singleton(targetOccurrence),
                selectedOccurrences(Arrays.asList(target, enclosing),
                        Arrays.asList(incomplete, taskSummary(scope,
                                "source/e", "R.E", "G.E", "TASK.E",
                                enclosingOccurrence + "#a3"))));
    }

    private static Set<String> selectedOccurrences(
            java.util.List<RegionInstancePlan> plans,
            java.util.List<JsonObject> summaries) throws Exception {
        Set<String> selected = new LinkedHashSet<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : RuntimeWorkflowDiscovery.rankedWorkflow(plans, summaries)
                .selections()) {
            selected.add(selection.occurrenceId);
        }
        return selected;
    }

    /**
     * One recorded versions envelope owned by the writer itself: a WRITE
     * version whose activation closure names an enclosing task, and an empty
     * read log, which is what the writer's own summary carries.
     */
    private static JsonObject unreadWriterRecord(
            String scope, String writerOccurrence,
            String enclosingOccurrence, boolean complete) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConSymbolExp");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "C_I_1");
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 3L);
        version.addProperty("versionKind", "WRITE");
        version.addProperty("regionEnterEventId", 11L);
        version.addProperty("regionId", "R.T");
        version.addProperty("taskId", "TASK.T");
        version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                "source/t");
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                writerOccurrence);
        version.add("expression", expression);
        version.add("pathGuard", SharedStateEvidence.emptyConjunction());

        JsonObject writerClosure = new JsonObject();
        writerClosure.addProperty("authority", SymbolicPropagationClosure
                .WRITER_ACTIVATION_CLOSURE_AUTHORITY);
        writerClosure.addProperty("complete", complete);
        JsonArray cases = new JsonArray();
        JsonObject writerCase = activation("TASK.T", writerOccurrence);
        writerCase.addProperty("regionId", "R.T");
        cases.add(writerCase);
        JsonObject enclosingCase = activation("TASK.E", enclosingOccurrence);
        enclosingCase.addProperty("regionId", "R.E");
        cases.add(enclosingCase);
        writerClosure.add("cases", cases);
        version.add(SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE,
                writerClosure);

        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 21L);
        location.addProperty("slot", 4);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("schemaVersion",
                SharedStateEvidence.SCHEMA_VERSION);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", true);
        JsonArray versions = new JsonArray();
        versions.add(version);
        envelope.add("versions", versions);
        envelope.addProperty("serializationTruncated", false);
        // The writer's own envelope logs no read.
        envelope.add("reads", new JsonArray());
        envelope.addProperty("readLogTruncated", false);
        JsonObject record = SharedStateEvidence.versionsRecord(
                "INSTANCE_FIELD/21#4", envelope,
                RecordedEvidenceIdentity.of("run", scope, "TASK.T",
                        writerOccurrence, "source/t", 1L));
        JsonArray records = new JsonArray();
        records.add(record);
        JsonObject recorded = new JsonObject();
        recorded.add("versions", records);
        return recorded;
    }

    @Test
    public void retainsDistinctRoutesToTheSameFailureSite() throws Exception {
        String producerOccurrence = "source/p/region/R.P#1";
        String bridgeOccurrence = "source/b/region/R.B#1";
        String directTarget = "source/d/region/R.T#1";
        String bridgedTarget = "source/d/region/R.T#2";
        JsonArray graph = new JsonArray();
        graph.add(readEdge(producerOccurrence, directTarget, 1L));
        graph.add(readEdge(producerOccurrence, bridgeOccurrence, 2L));
        graph.add(readEdge(bridgeOccurrence, bridgedTarget, 3L));

        RegionInstancePlan producer = plan("source/p", "R.P",
                producerOccurrence, "G.P", false, graph);
        RegionInstancePlan bridge = plan("source/b", "R.B",
                bridgeOccurrence, "G.B", false, graph);
        RegionInstancePlan direct = plan("source/d", "R.T",
                directTarget, "G.T1", true, graph, 20L);
        RegionInstancePlan bridged = plan("source/d", "R.T",
                bridgedTarget, "G.T2", true, graph, 10L);

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        producer, bridge, direct, bridged));
        Set<String> selected = new LinkedHashSet<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            selected.add(selection.occurrenceId);
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(directTarget,
                bridgeOccurrence, producerOccurrence, bridgedTarget)),
                selected);
    }

    private static JsonObject summary(String scope, String task,
                                      String occurrence,
                                      String producerTask,
                                      String producerOccurrence,
                                      String consumerOccurrence,
                                      long attachEvent) {
        JsonObject payload = new JsonObject();
        payload.addProperty("_type", "SymbolExpression");
        payload.addProperty("_java_type", "I");
        payload.addProperty("_exp", "x");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConsumerBoundaryExpression");
        expression.addProperty("boundaryKind", "RPC_ATTACH");
        expression.addProperty("eventId", attachEvent);
        expression.addProperty("_java_type", "I");
        expression.add("expression", payload);
        JsonObject event = VmHandoffEvidence.event("port", attachEvent - 1L,
                attachEvent, expression, producerTask, producerOccurrence);
        event.addProperty("boundarySessionScope", scope);
        event.addProperty("consumerOccurrenceId", consumerOccurrence);
        JsonArray events = new JsonArray();
        events.add(event);

        JsonObject summary = new JsonObject();
        summary.addProperty("boundarySessionScope", scope);
        summary.addProperty("taskId", task);
        summary.addProperty("occurrenceId", occurrence + "#a1");
        summary.add(VmHandoffEvidence.FIELD, events);
        return summary;
    }

    private static JsonObject readEdge(String from, String to,
                                       long receiverObjectId) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("correlationAuthority",
                SharedFieldFlow.LOCATION_MATCH_AUTHORITY);
        edge.addProperty("fromOccurrenceId", from);
        edge.addProperty("toOccurrenceId", to);
        edge.addProperty("fromOutputPort", "value");
        edge.addProperty("toInputPort", "value");
        edge.addProperty(SharedFieldFlow.EDGE_LOCATION,
                "example.State#value" + receiverObjectId);
        return edge;
    }

    private static JsonObject input(String symbol, String mode) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("mode", mode);
        return action;
    }

    private static JsonObject protocolEdge(String from, String to,
                                           String port) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("authority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("fromOccurrenceId", from);
        edge.addProperty("toOccurrenceId", to);
        edge.addProperty("fromOutputPort", port);
        edge.addProperty("toInputPort", port);
        return edge;
    }

    private static JsonObject inboundHandoff(String port) {
        JsonObject handoff = new JsonObject();
        handoff.addProperty("portId", port);
        handoff.addProperty("handoffLeafPath", port);
        handoff.addProperty("javaType", "int");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("side", "IN");
        handoff.addProperty("captureKind", "METHOD_RETURN");
        handoff.addProperty("definitionMethod", "example.Consumer.receive");
        return handoff;
    }

    private static JsonObject activation(String task, String occurrence) {
        JsonObject result = new JsonObject();
        result.addProperty("taskId", task);
        result.addProperty("occurrenceId", occurrence);
        return result;
    }

    /**
     * The job-cap refusal has to name its own top contributors: a bare count
     * says the campaign is too big but not which admission rule bought the
     * rows, which is the only thing that decides between raising the cap and
     * tightening the rule.
     */
    @Test
    public void closureAdmissionSummaryNamesTopContributors() {
        String convert = "<example.PBHelper: example.Key convert("
                + "example.KeyProto)>";
        String addKeys = "<example.Manager: void addKeys(example.Keys)>";
        java.util.List<RegionInstancePlan> rows = Arrays.asList(
                admitted("R.a", "s/region/R.a#1", null, null, addKeys),
                admitted("R.b", "s/region/R.b#1",
                        "SHARED_LOCATION_DEMAND_V1", 1, addKeys),
                admitted("R.c", "s/region/R.c#1",
                        "SHARED_LOCATION_DEMAND_V1", 2, convert),
                admitted("R.d", "s/region/R.d#1",
                        "SHARED_LOCATION_DEMAND_V1", 2, convert),
                admitted("R.e", "s/region/R.e#1",
                        "SHARED_LOCATION_DEMAND_V1", 4, convert));

        String summary = ConcolicScheduler.closureAdmissionSummary(rows);
        // Counted by basis, by depth, and by the anchors that dominate.
        assertEquals("admissionBasis={SHARED_LOCATION_DEMAND_V1=4, "
                + "TARGET_REACHABLE=1} demandDepth={-=1, 1=1, 2=2, 4=1} "
                + "topAnchors=[3x " + convert + ", 2x " + addKeys + "]",
                summary);
    }

    private static RegionInstancePlan admitted(
            String region, String occurrence, String basis, Integer depth,
            String targetMethod) {
        JsonObject encoded = plan("s", region, occurrence,
                "GOAL." + region, false, new JsonArray()).json().deepCopy();
        encoded.addProperty("targetMethod", targetMethod);
        if (basis != null) encoded.addProperty("admissionBasis", basis);
        if (depth != null) encoded.addProperty("demandDepth", depth);
        return RegionInstancePlan.decode(encoded);
    }

    private static RegionInstancePlan plan(String source, String region,
                                           String occurrence, String goal,
                                           boolean target, JsonArray edges) {
        return plan(source, region, occurrence, goal, target, edges, null);
    }

    private static RegionInstancePlan plan(String source, String region,
                                           String occurrence, String goal,
                                           boolean target, JsonArray edges,
                                           Long targetEvent) {
        JsonObject branch = new JsonObject();
        branch.addProperty("failureTarget", target);
        branch.addProperty("loopControlGuard", false);
        branch.addProperty("observed", target);
        if (target) {
            branch.addProperty("requiredOutcome", false);
            branch.addProperty("siteId", "example.Target#u1");
            if (targetEvent != null) {
                branch.addProperty("selectedRuntimeEventSeq", targetEvent);
            }
        }
        JsonArray branches = new JsonArray();
        branches.add(branch);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        JsonObject closure = new JsonObject();
        closure.addProperty("goalId", goal);
        closure.addProperty("kind", target
                ? "TARGET_REACH_CLOSURE" : "REGION_PATH_CLOSURE");
        closure.add("admission", admission);
        closure.add("branches", branches);
        closure.add("runtimeDefinitionMethods", new JsonArray());
        closure.add("edgeBindings", edges.deepCopy());
        JsonArray closures = new JsonArray();
        closures.add(closure);
        JsonObject encoded = new JsonObject();
        encoded.addProperty("sourceKey", source);
        encoded.addProperty("occurrenceId", occurrence);
        encoded.addProperty("relationKey", source + "/relation/" + region);
        encoded.addProperty("regionId", region);
        encoded.add("closureGoals", closures);
        return RegionInstancePlan.decode(encoded);
    }

    private static JsonObject taskSummary(String scope, String source,
                                          String region, String goal,
                                          String task, String occurrence) {
        JsonObject summary = new JsonObject();
        summary.addProperty("boundarySessionScope", scope);
        summary.addProperty("sourceKey", source);
        summary.addProperty("regionId", region);
        summary.addProperty("goalId", goal);
        summary.addProperty("taskId", task);
        summary.addProperty("occurrenceId", occurrence);
        return summary;
    }

    private static JsonObject guardedWriterRecord(
            String scope, String readerOccurrence,
            String writerOccurrence) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConSymbolExp");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "C_I_1");
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 2L);
        version.addProperty("versionKind", "WRITE");
        version.addProperty("regionEnterEventId", 10L);
        version.addProperty("regionId", "R.W");
        version.addProperty("taskId", "TASK.W");
        version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                "source/w");
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                writerOccurrence);
        version.add("expression", expression);
        version.add("pathGuard", SharedStateEvidence.emptyConjunction());
        JsonObject writerClosure = new JsonObject();
        writerClosure.addProperty("authority", SymbolicPropagationClosure
                .WRITER_ACTIVATION_CLOSURE_AUTHORITY);
        writerClosure.addProperty("complete", true);
        JsonArray cases = new JsonArray();
        JsonObject writerCase = activation("TASK.W", writerOccurrence);
        writerCase.addProperty("regionId", "R.W");
        cases.add(writerCase);
        writerClosure.add("cases", cases);
        version.add(SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE,
                writerClosure);

        JsonObject read = new JsonObject();
        read.addProperty("readEventId", 20L);
        read.addProperty("regionEnterEventId", 19L);
        read.addProperty("regionId", "R.B");
        read.addProperty("taskId", "TASK.B");
        read.addProperty(SharedStateEvidence.READER_SOURCE_KEY, "source/b");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                readerOccurrence);
        read.addProperty("candidateCount", 1);

        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 17L);
        location.addProperty("slot", 8);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("schemaVersion",
                SharedStateEvidence.SCHEMA_VERSION);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", true);
        JsonArray versions = new JsonArray();
        versions.add(version);
        envelope.add("versions", versions);
        envelope.addProperty("serializationTruncated", false);
        JsonArray reads = new JsonArray();
        reads.add(read);
        envelope.add("reads", reads);
        envelope.addProperty("readLogTruncated", false);
        JsonObject record = SharedStateEvidence.versionsRecord(
                "INSTANCE_FIELD/17#8", envelope,
                RecordedEvidenceIdentity.of("run", scope, "TASK.B",
                        readerOccurrence, "source/b", 1L));
        JsonArray records = new JsonArray();
        records.add(record);
        JsonObject recorded = new JsonObject();
        recorded.add("versions", records);
        return recorded;
    }
}
