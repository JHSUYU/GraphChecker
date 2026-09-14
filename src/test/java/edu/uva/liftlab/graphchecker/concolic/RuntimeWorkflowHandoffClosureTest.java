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
                attachEvent, expression, producerTask, producerOccurrence,
                consumerOccurrence,
                edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract
                        .phaseId("port", consumerOccurrence, 1, "<a.B: int v>"),
                "M_I_field_HOFF.1_a/B", "7", "I", "");
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
