package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class CausalGraphWriterTest {
    @Test
    public void projectsSelectedIdentityEvidenceAndSatWitness() {
        JsonObject producer = plan("node#epoch0", "NODE", "SERVICE", "node",
                0, "occ.producer", "relation.producer", "REGION.PRODUCER");
        producer.addProperty("requestKey", "node#epoch0/request/clientCall#1");
        producer.addProperty("requestApi", "clientCall");
        JsonObject target = plan("node#epoch1", "NODE", "SERVICE", "node",
                1, "occ.target", "relation.target", "REGION.TARGET");
        JsonObject first = causalEdge("edge.1", "OBSERVED_BASELINE",
                "ALIGNED", "trace.1");
        JsonObject second = causalEdge("edge.2", "REPLAY_CONFIRMED",
                "DEVIATED", "replay.2");

        JsonObject schedule = new JsonObject();
        schedule.add("target", identity(target));
        JsonArray producers = new JsonArray();
        producers.add(identity(producer));
        schedule.add("producers", producers);

        JsonObject composition = new JsonObject();
        composition.addProperty("fatalSite", "TARGET_BRANCH");
        JsonArray selected = new JsonArray();
        selected.add("edge.1");
        selected.add("edge.2");
        composition.add("resolvedEdgeBindings", selected);
        JsonObject ledger = new JsonObject();
        JsonObject fatal = new JsonObject();
        fatal.addProperty("name", "fatal_path");
        fatal.addProperty("solverTerm", "fatal_term");
        ledger.add("fatalPathAssertion", fatal);
        JsonArray edgeAssertions = new JsonArray();
        edgeAssertions.add(assertion("edge.1", "bind_1"));
        edgeAssertions.add(assertion("edge.2", "bind_2"));
        ledger.add("edgeAssertions", edgeAssertions);
        composition.add("operandBindingLedger", ledger);

        JsonObject begin = sourceEvent("REQUEST_BEGIN", "node#epoch0", "");
        begin.addProperty("requestId", 7);
        begin.addProperty("requestKey", "node#epoch0/request/clientCall#1");
        begin.addProperty("apiName", "clientCall");
        JsonObject restart = sourceEvent("SOURCE_RESTART", "node#epoch0",
                "node#epoch1");
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "summary.1");
        JsonObject outputClosure = new JsonObject();
        JsonObject relationProducer = new JsonObject();
        relationProducer.addProperty("relationKey", "relation.producer");
        relationProducer.addProperty("contractHash",
                "contract.relation.producer");
        outputClosure.add("producer", relationProducer);
        summary.add("outputClosure", outputClosure);
        JsonObject relation = new JsonObject();
        relation.add("cases", new JsonArray());
        summary.add("regionRelation", relation);

        JsonObject graph = CausalGraphWriter.skeleton(
                Arrays.asList(producer, target), Arrays.asList(first, second),
                Arrays.asList(begin, restart), schedule, composition,
                Collections.singletonList(summary));

        assertEquals(2, count(array(graph, "nodes"), "type", "SOURCE"));
        assertEquals(2, count(array(graph, "nodes"), "type",
                "REGION_OCCURRENCE"));
        assertEquals(1, count(array(graph, "nodes"), "type", "EXTERNAL_API"));
        assertEquals(1, count(array(graph, "edges"), "kind",
                "API_REQUEST_REACHES_REGION"));
        assertEquals(1, count(array(graph, "nodes"), "type",
                "CRITICAL_BRANCH"));
        JsonObject producerNode = find(array(graph, "nodes"),
                "occurrenceId", "occ.producer");
        assertNotNull(producerNode);
        assertEquals("summary.1", producerNode.getAsJsonArray(
                "symbolicRelations").get(0).getAsJsonObject()
                .get("summaryId").getAsString());
        JsonObject causal = find(array(graph, "edges"), "kind", "RPC");
        assertNotNull(causal);
        assertEquals(2, array(causal, "selectedEdgeIds").size());
        assertEquals(2, array(causal, "evidenceIds").size());
        assertEquals(2, array(causal, "smtAssertions").size());
        assertEquals(2, array(causal, "evidenceStates").size());
        assertEquals("REPLAY_CONFIRMED", string(causal, "evidenceState"));
        assertEquals("DEVIATED", string(causal, "alignment"));
        assertEquals("dotted", string(causal, "style"));
        assertTrue(array(graph, "gaps").toString().contains(
                "ALIGNMENT_DEVIATED"));
        assertFalse(object(graph, "coverage").get(
                "relationOrSmtBlocked").getAsBoolean());

        JsonObject reach = new JsonObject();
        JsonObject condition = new JsonObject();
        condition.addProperty("reachability", "REACHABLE");
        reach.add("reachCondition", condition);
        JsonObject roots = new JsonObject();
        JsonArray booleans = new JsonArray();
        JsonObject root = new JsonObject();
        root.addProperty("portId", "config.flag");
        root.addProperty("solverTerm", "config_flag");
        root.addProperty("javaTypeDescriptor", "Z");
        booleans.add(root);
        roots.add("booleanInputs", booleans);
        reach.add("roots", roots);
        JsonObject valuation = new JsonObject();
        valuation.addProperty("status", "sat");
        JsonArray values = new JsonArray();
        values.add(false);
        valuation.add("values", values);
        JsonArray valuations = new JsonArray();
        valuations.add(valuation);
        reach.add("valuations", valuations);

        JsonObject witness = CausalGraphWriter.witness(graph, reach,
                composition);
        assertEquals("SAT", string(witness, "verdict"));
        assertFalse(array(witness, "rootAssignments").get(0)
                .getAsJsonObject().get("value").getAsBoolean());
        assertTrue(CausalGraphWriter.dot(witness).contains("style=dotted"));
    }

    private static JsonObject plan(String sourceKey, String sourceKind,
                                   String sourceRole, String sourceId,
                                   long epoch, String occurrence,
                                   String relation, String region) {
        JsonObject row = new JsonObject();
        row.addProperty("sourceKey", sourceKey);
        row.addProperty("sourceKind", sourceKind);
        row.addProperty("sourceRole", sourceRole);
        row.addProperty("sourceId", sourceId);
        row.addProperty("sourceEpoch", epoch);
        row.addProperty("sourceAuthority", "EXPLICIT_TRACE_SOURCE");
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("relationKey", relation);
        row.addProperty("relationContractHash", "contract." + relation);
        row.addProperty("regionId", region);
        return row;
    }

    private static JsonObject identity(JsonObject plan) {
        JsonObject row = new JsonObject();
        for (String field : new String[]{"occurrenceId", "relationKey",
                "regionId"}) row.add(field, plan.get(field).deepCopy());
        return row;
    }

    private static JsonObject causalEdge(String id, String state,
                                         String alignment,
                                         String evidenceId) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", id);
        edge.addProperty("transportKind", "RPC");
        edge.addProperty("fromOccurrenceId", "occ.producer");
        edge.addProperty("toOccurrenceId", "occ.target");
        edge.addProperty("fromOutputPort", "out.value");
        edge.addProperty("toInputPort", "in.value");
        edge.addProperty("evidenceState", state);
        edge.addProperty("alignment", alignment);
        JsonArray evidence = new JsonArray();
        evidence.add(evidenceId);
        edge.add("evidenceIds", evidence);
        return edge;
    }

    private static JsonObject assertion(String edgeId, String name) {
        JsonObject row = new JsonObject();
        row.addProperty("edgeId", edgeId);
        JsonArray names = new JsonArray();
        names.add(name);
        row.add("assertionNames", names);
        return row;
    }

    private static JsonObject sourceEvent(String kind, String source,
                                          String related) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", kind);
        row.addProperty("sourceKey", source);
        if (!related.isEmpty()) row.addProperty("relatedSourceKey", related);
        return row;
    }

    private static int count(JsonArray values, String field, String expected) {
        int count = 0;
        for (JsonElement value : values) if (value.isJsonObject()
                && expected.equals(string(value.getAsJsonObject(), field))) {
            count++;
        }
        return count;
    }

    private static JsonObject find(JsonArray values, String field,
                                   String expected) {
        for (JsonElement value : values) if (value.isJsonObject()
                && expected.equals(string(value.getAsJsonObject(), field))) {
            return value.getAsJsonObject();
        }
        return null;
    }

    private static JsonArray array(JsonObject row, String field) {
        return JsonFields.array(row, field);
    }

    private static JsonObject object(JsonObject row, String field) {
        return JsonFields.object(row, field);
    }

    private static String string(JsonObject row, String field) {
        return JsonFields.string(row, field);
    }
}
