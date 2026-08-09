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
    public void captureSpecPreservesBoundedOutputOccurrence() {
        JsonObject activation = canonicalActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");
        JsonObject member = activation.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject();
        JsonObject output = member.getAsJsonObject("output");
        JsonObject capture = member.getAsJsonObject("slice")
                .getAsJsonArray("captureBindings").get(0).getAsJsonObject();
        capture.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("definitionMethod", "<P: void run()>");
        capture.addProperty("definitionUnitIndex", 7);
        for (JsonObject value : Arrays.asList(output, capture)) {
            value.addProperty("outputSiteId",
                    "FIELD_WRITE_STATE:<P: void run()>#u7:<P: int out>");
            value.addProperty("outputOccurrence", 3);
            value.addProperty("replayOccurrence", 3);
        }

        OutputCaptureSpec spec = OutputClosureCodec.captureSpecs(
                OutputClosureCodec.decode(activation)).get(0);
        assertTrue(spec.occurrenceScoped());
        assertEquals("FIELD_WRITE_STATE:<P: void run()>#u7:<P: int out>",
                spec.outputSiteId());
        assertEquals(3, spec.outputOccurrence());
        assertEquals(3, spec.replayOccurrence());

        // A recorded ordinal past the replay loop bound is provenance, not a
        // replay demand: the mutation writer of a demanded container may
        // well have been recorded at its site's twenty-sixth execution.
        for (JsonObject value : Arrays.asList(output, capture)) {
            value.addProperty("outputOccurrence", 26);
            value.addProperty("replayOccurrence", 26);
        }
        OutputCaptureSpec recordedPastBound = OutputClosureCodec
                .captureSpecs(OutputClosureCodec.decode(activation)).get(0);
        assertEquals(26, recordedPastBound.outputOccurrence());

        // Internal coherence of the declared identity is still validated.
        output.addProperty("replayOccurrence", 25);
        expectFailure(() -> OutputClosureCodec.captureSpecs(
                OutputClosureCodec.decode(activation)),
                "outside the bounded replay");
    }

    @Test
    public void memberOrderIsCanonicalAndPartOfOneJointContract() {
        OutputClosureContract left = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract right = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
        JsonObject envelope = left.toJson();
        JsonArray causalEdges = envelope.getAsJsonArray("causalEdges");
        causalEdges.add(right.toJson().getAsJsonArray("causalEdges").get(0));
        JsonArray members = new JsonArray();
        members.add(right.toJson().getAsJsonArray("members").get(0));
        members.add(left.toJson().getAsJsonArray("members").get(0));
        envelope.add("members", members);
        OutputClosureContract joint =
                OutputClosureCodec.decodeEnvelope(envelope);
        assertEquals(2, joint.members().size());
        assertEquals("REGION.1.out.0", joint.members().get(0).portId());
        assertEquals("REGION.1.out.1", joint.members().get(1).portId());
    }

    @Test
    public void jointCaptureSupportsPrimitiveMapAndArrayMembers() {
        OutputClosureContract scalar = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int count>",
                        "DF.1", "int"));
        OutputClosureContract map = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.1",
                        "<P: java.util.Map values>", "DF.2",
                        "java.util.Map"));
        OutputClosureContract array = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.2",
                        "<P: int[] entries>", "DF.3", "int[]"));

        OutputClosureContract joint = OutputClosureCodec.merge(
                Arrays.asList(array, scalar, map));
        OutputClosureContract roundTrip =
                OutputClosureCodec.decodeEnvelope(joint.toJson());

        assertEquals("I", roundTrip.member(
                "REGION.1.out.0").javaTypeDescriptor());
        assertEquals("Ljava/util/Map;", roundTrip.member(
                "REGION.1.out.1").javaTypeDescriptor());
        assertEquals("[I", roundTrip.member(
                "REGION.1.out.2").javaTypeDescriptor());
        assertEquals(3, OutputClosureCodec.captureSpecs(roundTrip).size());
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
                "cell must be a non-empty string");
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
    public void codecPreservesCaptureIssuesForAdmissionBoundary() {
        OutputClosureContract first = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract second = OutputClosureCodec.decode(
                canonicalActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
        JsonObject envelope = OutputClosureCodec.merge(
                Arrays.asList(first, second)).toJson();
        envelope.getAsJsonArray("members").get(1).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonArray("captureBindingIssues")
                .add("MISSING_CAPTURE");

        OutputClosureContract incompleteJoint =
                OutputClosureCodec.decodeEnvelope(envelope);
        assertEquals(1, incompleteJoint.member("REGION.1.out.1")
                .slice().getAsJsonArray("captureBindingIssues").size());

        JsonObject singleton = first.toJson();
        singleton.getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonArray("captureBindingIssues")
                .add("MISSING_CAPTURE");
        OutputClosureContract incomplete =
                OutputClosureCodec.decodeEnvelope(singleton);
        assertEquals(1, incomplete.member("REGION.1.out.0")
                .slice().getAsJsonArray("captureBindingIssues").size());
    }

    private static JsonObject canonicalActivation(
            String port, String cell, String edgeId) {
        return canonicalActivation(port, cell, edgeId, "int");
    }

    private static JsonObject canonicalActivation(
            String port, String cell, String edgeId, String javaType) {
        String method = "<P: void run()>";
        String site = method + "#u2";
        String region = port.substring(0, port.indexOf(".out."));
        JsonObject activation = new JsonObject();
        activation.addProperty("regionId", region);
        activation.addProperty("regionInstanceId",
                region + "@test#call7");
        activation.addProperty("rootCallId", 7);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", port + ".exit-field");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("accessRootInputPort", region + ".in.0");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add(FieldPathSpec.declaredField(cell).name());
        capture.add("fieldPath", fieldPath);
        capture.addProperty("fieldSignature", cell);
        capture.addProperty("javaType", javaType);
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
        slice.addProperty("inputAliasCanonicalizationComplete", true);
        slice.addProperty("regionTruncated", false);
        slice.addProperty("truncated", false);
        slice.addProperty("methodBudgetTruncated", false);
        slice.addProperty("causalCellBudgetTruncated", false);
        slice.add("inputGaps", new JsonArray());
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
                "HEAP_STATE", javaType, slice));
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
