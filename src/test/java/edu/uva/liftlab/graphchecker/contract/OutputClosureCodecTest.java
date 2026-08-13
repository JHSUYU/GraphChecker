package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class OutputClosureCodecTest {
    @Test
    public void relationContractRoundTripsWithoutOccurrenceOrEdgeCopies() {
        JsonObject artifact = artifact(singleton("out", "EDGE.1"));

        OutputClosureContract closure = OutputClosureCodec.decode(artifact);

        assertEquals(3, closure.toJson().get("schemaVersion").getAsInt());
        assertEquals("REL.1", closure.producer().relationKey());
        assertEquals("REGION.1", closure.producer().regionId());
        assertEquals("HASH.1", closure.producer().contractHash());
        assertEquals(Arrays.asList("EDGE.1"), Arrays.asList(closure
                .executionScope().causalEdgeIds().toArray(new String[0])));
        assertFalse(closure.toJson().has("causalEdges"));
        assertFalse(closure.toJson().getAsJsonObject("producer")
                .has("regionInstanceId"));
        assertFalse(closure.toJson().getAsJsonObject("producer")
                .has("rootCallId"));

        JsonObject encoded = artifact.deepCopy();
        OutputClosureCodec.writeTo(encoded, closure);
        OutputClosureContract roundTrip = OutputClosureCodec.decode(encoded);
        assertEquals(closure.demandKey(), roundTrip.demandKey());
        assertEquals(closure.closureFingerprint(),
                roundTrip.closureFingerprint());
    }

    @Test
    public void mergeUsesRelationIdentityAndCanonicalPorts() {
        OutputClosureContract first = singleton("out", "EDGE.1");
        OutputClosureContract second = singleton("other", "EDGE.2");

        OutputClosureContract merged = OutputClosureCodec.merge(
                Arrays.asList(first, second));

        assertEquals(Arrays.asList("REGION.1.out.other", "REGION.1.out.out"),
                Arrays.asList(merged.outputPorts().toArray(new String[0])));
        assertEquals(Arrays.asList("EDGE.1", "EDGE.2"), Arrays.asList(
                merged.executionScope().causalEdgeIds()
                        .toArray(new String[0])));
        assertNotEquals(first.closureFingerprint(),
                merged.closureFingerprint());
    }

    @Test
    public void mergeUnionsEdgesForOneRelationMember() {
        OutputClosureContract merged = OutputClosureCodec.merge(
                Arrays.asList(singleton("out", "EDGE.1"),
                        singleton("out", "EDGE.2")));

        assertEquals(1, merged.members().size());
        assertEquals(Arrays.asList("EDGE.1", "EDGE.2"), Arrays.asList(
                merged.executionScope().causalEdgeIds()
                        .toArray(new String[0])));
    }

    @Test
    public void mergeKeepsObservedVersionsAsBestEffortCaptures() {
        JsonObject second = singleton("out", "EDGE.2").toJson();
        JsonObject member = second.getAsJsonArray("members").get(0)
                .getAsJsonObject();
        JsonObject slice = member.getAsJsonObject("slice");
        slice.addProperty("selectedRuntimeEventSeq", 20);
        slice.addProperty("activationLocalOccurrence", 2);
        JsonObject capture = slice.getAsJsonArray("captureBindings")
                .get(0).getAsJsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.second");
        capture.addProperty("accessRootInputPort", "REGION.1.in.1");

        OutputClosureContract merged = OutputClosureCodec.merge(
                Arrays.asList(singleton("out", "EDGE.1"),
                        OutputClosureCodec.decodeEnvelope(second)));

        assertEquals(2, merged.member("REGION.1.out.out")
                .captures().size());
        assertTrue(merged.member("REGION.1.out.out").slice()
                .has("alignmentGaps"));
    }

    @Test
    public void mergeRejectsDifferentRelationContracts() {
        OutputClosureContract first = singleton("out", "EDGE.1");
        JsonObject other = singleton("other", "EDGE.2").toJson();
        other.getAsJsonObject("producer").addProperty(
                "contractHash", "HASH.2");

        expectFailure(() -> OutputClosureCodec.merge(Arrays.asList(first,
                OutputClosureCodec.decodeEnvelope(other))),
                "different producer relations");
    }

    @Test
    public void oldInvocationScopedProducerFailsDirectly() {
        JsonObject closure = singleton("out", "EDGE.1").toJson();
        JsonObject producer = closure.getAsJsonObject("producer");
        producer.addProperty("regionInstanceId", "REGION.1@test#call1");
        producer.addProperty("rootCallId", 1L);

        expectFailure(() -> OutputClosureCodec.decodeEnvelope(closure),
                "retired output closure field regionInstanceId");
    }

    @Test
    public void embeddedCausalEdgesFailInsteadOfDuplicatingCatalog() {
        JsonObject closure = singleton("out", "EDGE.1").toJson();
        closure.add("causalEdges", new JsonArray());
        expectFailure(() -> OutputClosureCodec.decodeEnvelope(closure),
                "retired output closure field causalEdges");

        JsonObject slice = slice("REGION.1.out.out", "<P: int out>",
                "EDGE.1");
        slice.add("causalEdges", new JsonArray());
        expectFailure(() -> OutputClosureCodec.singleton(
                "REL.1", "REGION.1", "HASH.1", "REGION.1.out.out",
                "<P: int out>", "HEAP_STATE", "int", slice),
                "causalEdgeIds");
    }

    @Test
    public void outerRelationScopeMustMatchProducer() {
        JsonObject artifact = artifact(singleton("out", "EDGE.1"));
        artifact.addProperty("relationKey", "REL.other");
        expectFailure(() -> OutputClosureCodec.decode(artifact),
                "conflicts with artifact scope");
    }

    @Test
    public void captureSpecsRemainAvailableToRuntime() {
        OutputCaptureSpec capture = OutputClosureCodec.captureSpecs(
                singleton("out", "EDGE.1")).get(0);
        assertEquals("REGION.1.out.out", capture.outputPort());
        assertEquals("<P: int out>", capture.fieldSignature());
    }

    private static JsonObject artifact(OutputClosureContract closure) {
        JsonObject result = new JsonObject();
        result.addProperty("sourceKey", "nn0#epoch1");
        result.addProperty("occurrenceId", "OCC.1");
        result.addProperty("relationKey", "REL.1");
        result.addProperty("relationContractHash", "HASH.1");
        result.addProperty("regionId", "REGION.1");
        result.add(OutputClosureContract.FIELD, closure.toJson());
        return result;
    }

    private static OutputClosureContract singleton(
            String field, String edgeId) {
        String port = "REGION.1.out." + field;
        String cell = "<P: int " + field + ">";
        return OutputClosureCodec.singleton("REL.1", "REGION.1",
                "HASH.1", port, cell, "HEAP_STATE", "int",
                slice(port, cell, edgeId));
    }

    private static JsonObject slice(
            String port, String cell, String edgeId) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings("REGION.1.in.0"));
        slice.add("sites", strings("<P: void run()>#u1"));
        slice.add("staticSites", new JsonArray());
        slice.add("methods", strings("<P: void run()>"));
        slice.add("causalEdgeIds", strings(edgeId));
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + cell);
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        capture.add("fieldPath", strings(cell.substring(
                cell.lastIndexOf(' ') + 1, cell.length() - 1)));
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", "REGION.1.in.0");
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        return slice;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static void expectFailure(Runnable action, String text) {
        try {
            action.run();
            fail("expected IllegalArgumentException containing " + text);
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains(text));
        }
    }
}
