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
    public void buildsOneCanonicalSingletonAndRoundTrips() {
        JsonObject activation = canonicalActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");

        OutputClosureContract closure = OutputClosureCodec.decode(activation);

        assertEquals(1, closure.members().size());
        assertEquals("I",
                closure.members().get(0).javaTypeDescriptor());
        assertEquals(Arrays.asList("REGION.1.in.0"),
                Arrays.asList(closure.executionScope().inputPorts()
                        .toArray(new String[0])));

        JsonObject encoded = activation.deepCopy();
        OutputClosureCodec.writeTo(encoded, closure);
        assertTrue(encoded.has("outputClosure"));
        assertFalse(encoded.has("requestedOutput"));
        assertFalse(encoded.has("requestedOutputSlice"));
        assertFalse(encoded.has("outputs"));
        OutputClosureContract roundTrip = OutputClosureCodec.decode(encoded);
        assertEquals(closure.demandKey(), roundTrip.demandKey());
        assertEquals(closure.closureFingerprint(),
                roundTrip.closureFingerprint());
    }

    @Test
    public void memberOrderIsCanonicalAndPartOfOneJointContract() {
        OutputClosureContract left = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract right = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
        JsonObject envelope = left.toJson();
        JsonArray members = new JsonArray();
        members.add(right.toJson().getAsJsonArray("members").get(0));
        members.add(left.toJson().getAsJsonArray("members").get(0));
        envelope.add("members", members);

        expectFailure(() -> OutputClosureCodec.decodeEnvelope(envelope),
                "strictly sorted");

        JsonArray sorted = new JsonArray();
        sorted.add(left.toJson().getAsJsonArray("members").get(0));
        sorted.add(right.toJson().getAsJsonArray("members").get(0));
        envelope.add("members", sorted);
        OutputClosureContract joint =
                OutputClosureCodec.decodeEnvelope(envelope);
        assertEquals(2, joint.members().size());
        assertEquals("REGION.1.out.0", joint.members().get(0).portId());
        assertEquals("REGION.1.out.1", joint.members().get(1).portId());
        assertTrue(joint.supportedJointCapture());
    }

    @Test
    public void malformedExplicitEnvelopeNeverFallsBackToLegacy() {
        JsonObject artifact = canonicalActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");
        artifact.add("requestedOutput", new JsonObject());
        JsonObject malformed = new JsonObject();
        malformed.addProperty("schemaVersion", 99);
        artifact.add("outputClosure", malformed);

        expectFailure(() -> OutputClosureCodec.decode(artifact),
                "forbids legacy mirror");
    }

    @Test
    public void missingMemberIsRejectedInsteadOfReturningPartialValue() {
        OutputClosureContract first = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract second = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
        JsonObject envelope = first.toJson();
        JsonArray members = new JsonArray();
        members.add(first.toJson().getAsJsonArray("members").get(0));
        JsonObject malformed = second.toJson().getAsJsonArray("members")
                .get(0).getAsJsonObject().deepCopy();
        malformed.getAsJsonObject("output").remove("cell");
        members.add(malformed);
        envelope.add("members", members);

        expectFailure(() -> OutputClosureCodec.decodeEnvelope(envelope),
                "keys mismatch");
    }

    @Test
    public void demandIncludesProducerRegionAndFingerprintIncludesInvocation() {
        OutputClosureContract original = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        JsonObject otherRegion = canonicalActivation(
                "REGION.2.out.0", "<P: int x>", "DF.1");
        setProducer(otherRegion, "REGION.2",
                "REGION.2@test#call7", 7);
        OutputClosureContract moved = OutputClosureCodec.decode(otherRegion);
        assertNotEquals(original.demandKey(), moved.demandKey());

        JsonObject otherInvocation = canonicalActivation(
                "REGION.1.out.0", "<P: int x>", "DF.1");
        setProducer(otherInvocation, "REGION.1",
                "REGION.1@test#call8", 8);
        OutputClosureContract replay =
                OutputClosureCodec.decode(otherInvocation);
        assertEquals(original.demandKey(), replay.demandKey());
        assertNotEquals(original.closureFingerprint(),
                replay.closureFingerprint());
    }

    @Test
    public void jointCaptureCompletenessCannotBeInventedByMemberView() {
        OutputClosureContract first = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract second = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
        JsonObject envelope = OutputClosureCodec.merge(
                Arrays.asList(first, second)).toJson();
        envelope.getAsJsonArray("members").get(1).getAsJsonObject()
                .getAsJsonObject("slice")
                .addProperty("captureBindingsComplete", false);

        expectFailure(() -> OutputClosureCodec.decodeEnvelope(envelope),
                "multi-output V1 requires");

        JsonObject singleton = first.toJson();
        singleton.getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .addProperty("captureBindingsComplete", false);
        OutputClosureContract incomplete =
                OutputClosureCodec.decodeEnvelope(singleton);
        JsonObject activation = canonicalActivation("REGION.1.out.0",
                "<P: int x>", "DF.1");
        for (String field : new String[]{"requestedOutput",
                "requestedOutputSlice", "requestedOutputCapture",
                "requestedOutputCaptureRequired",
                "requestedOutputCaptureComplete", "requestedOutputMethods",
                "outputs"}) {
            activation.remove(field);
        }
        activation.add("outputClosure", incomplete.toJson());
        assertFalse(OutputClosureCodec.memberActivationView(
                activation, incomplete, "REGION.1.out.0")
                .get("requestedOutputCaptureComplete").getAsBoolean());
    }

    private static JsonObject canonicalActivation(
            String port, String cell, String edgeId) {
        String method = "<P: void run()>";
        String site = method + "#u2";
        String region = port.substring(0, port.indexOf(".out."));
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.1");
        activation.addProperty("regionId", region);
        activation.addProperty("regionInstanceId",
                region + "@test#call7");
        activation.addProperty("rootCallId", 7);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId", port + ".capture.0");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("method", method);
        capture.addProperty("siteId", site);
        capture.addProperty("unitIndex", 2);
        capture.addProperty("fieldSignature", cell);
        capture.addProperty("occurrence", 1);
        capture.addProperty("occurrenceAuthority",
                "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                        + "LAST_WRITE_OCCURRENCE");
        capture.addProperty("bindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS");
        JsonArray captures = new JsonArray();
        captures.add(capture);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.addProperty("complete", true);
        slice.addProperty("structuralComplete", true);
        slice.addProperty("runtimeRefined", true);
        slice.addProperty("runtimeRefinementComplete", true);
        slice.addProperty("runtimeRefinementAuthority",
                "OBSERVED_REGION_CALL_TREE");
        slice.addProperty("unresolvedInputProvenanceComplete", true);
        slice.addProperty("inputAliasCanonicalizationComplete", true);
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        slice.addProperty("regionTruncated", false);
        slice.addProperty("truncated", false);
        slice.addProperty("methodBudgetTruncated", false);
        slice.addProperty("causalCellBudgetTruncated", false);
        slice.add("unresolvedInputs", new JsonArray());
        slice.add("unresolvedInputDetails", new JsonArray());
        slice.add("truncationReasons", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("inputAliasCanonicalizationIssues", new JsonArray());
        slice.add("inputPorts", strings("REGION.1.in.0"));
        slice.add("staticInputPorts", strings("REGION.1.in.0"));
        slice.add("methods", strings(method));
        slice.add("staticMethods", strings(method));
        slice.add("sites", strings(site));
        slice.add("staticSites", strings(site));
        slice.add("causalEdgeIds", strings(edgeId));
        slice.add("staticCausalEdgeIds", strings(edgeId));
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", edgeId);
        JsonArray edges = new JsonArray();
        edges.add(edge);
        slice.add("causalEdges", edges);
        slice.add("captureBindings", captures.deepCopy());
        OutputClosureCodec.writeTo(activation, OutputClosureCodec.singleton(
                region, region + "@test#call7", 7, port, cell,
                "HEAP_STATE", "CONFIRMED_READ_FROM_EDGE", slice));
        return activation;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static void setProducer(JsonObject activation, String region,
                                    String instance, long rootCall) {
        activation.addProperty("regionId", region);
        activation.addProperty("regionInstanceId", instance);
        activation.addProperty("rootCallId", rootCall);
        JsonObject producer = activation.getAsJsonObject("outputClosure")
                .getAsJsonObject("producer");
        producer.addProperty("regionId", region);
        producer.addProperty("regionInstanceId", instance);
        producer.addProperty("rootCallId", rootCall);
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
