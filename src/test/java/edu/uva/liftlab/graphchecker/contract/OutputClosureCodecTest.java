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
    public void normalizesOneCompleteLegacyActivationAndRoundTrips() {
        JsonObject legacy = legacyActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");

        OutputClosureContract closure = OutputClosureCodec.decode(legacy);

        assertEquals(1, closure.members().size());
        assertEquals("I",
                closure.members().get(0).javaTypeDescriptor());
        assertEquals(Arrays.asList("REGION.1.in.0"),
                Arrays.asList(closure.executionScope().inputPorts()
                        .toArray(new String[0])));

        JsonObject encoded = legacy.deepCopy();
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
                legacyActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract right = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
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
        JsonObject artifact = legacyActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");
        JsonObject malformed = new JsonObject();
        malformed.addProperty("schemaVersion", 99);
        artifact.add("outputClosure", malformed);

        expectFailure(() -> OutputClosureCodec.decode(artifact),
                "forbids legacy mirror");
    }

    @Test
    public void missingMemberIsRejectedInsteadOfReturningPartialValue() {
        OutputClosureContract first = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract second = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
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
    public void proofChangeOnlyChangesFingerprint() {
        OutputClosureContract original = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int out>", "DF.1"));
        JsonObject changedArtifact = legacyActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");
        changedArtifact.getAsJsonArray("requestedOutputCapture")
                .get(0).getAsJsonObject()
                .addProperty("occurrenceAuthority", "OTHER_EXACT_AUTHORITY");
        changedArtifact.getAsJsonObject("requestedOutputSlice")
                .getAsJsonArray("captureBindings").get(0).getAsJsonObject()
                .addProperty("occurrenceAuthority", "OTHER_EXACT_AUTHORITY");
        OutputClosureContract changed =
                OutputClosureCodec.decode(changedArtifact);

        assertEquals(original.demandKey(), changed.demandKey());
        assertNotEquals(original.closureFingerprint(),
                changed.closureFingerprint());
    }

    @Test
    public void explicitFieldDescriptorMustUseJvmFieldGrammar() {
        OutputClosureContract original = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int out>", "DF.1"));
        JsonObject encoded = original.toJson();
        encoded.getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("output")
                .addProperty("javaTypeDescriptor", "V");

        expectFailure(() -> OutputClosureCodec.decodeEnvelope(encoded),
                "is invalid");
        assertFalse(OutputClosureCodec.validFieldDescriptor("[V"));
        assertFalse(OutputClosureCodec.validFieldDescriptor(
                "Ljava.lang.String;"));
        assertTrue(OutputClosureCodec.validFieldDescriptor(
                "[[Ljava/lang/String;"));

        encoded.getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("output")
                .addProperty("javaTypeDescriptor", "J");
        assertEquals("J", OutputClosureCodec.decodeEnvelope(encoded)
                .members().get(0).javaTypeDescriptor());
    }

    @Test
    public void completeEmptyBranchSliceProducesNoWildcardSites() {
        JsonObject activation = legacyActivation("REGION.1.out.0",
                "<P: int out>", "DF.1");
        JsonObject slice = activation.getAsJsonObject(
                "requestedOutputSlice");
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());

        OutputClosureContract closure =
                OutputClosureCodec.decode(activation);

        assertTrue(closure.executionScope().branchSites().isEmpty());
    }

    @Test
    public void multiOutputRejectsReferenceMember() {
        OutputClosureContract first = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract second = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.1",
                        "<P: java.lang.String y>", "DF.2"));
        JsonObject envelope = first.toJson();
        JsonArray members = new JsonArray();
        members.add(first.toJson().getAsJsonArray("members").get(0));
        members.add(second.toJson().getAsJsonArray("members").get(0));
        envelope.add("members", members);

        expectFailure(() -> OutputClosureCodec.decodeEnvelope(envelope),
                "direct primitive");
    }

    @Test
    public void demandIncludesProducerRegionAndFingerprintIncludesInvocation() {
        OutputClosureContract original = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        JsonObject otherRegion = legacyActivation(
                "REGION.2.out.0", "<P: int x>", "DF.1");
        setProducer(otherRegion, "REGION.2",
                "REGION.2@test#call7", 7);
        OutputClosureContract moved = OutputClosureCodec.decode(otherRegion);
        assertNotEquals(original.demandKey(), moved.demandKey());

        JsonObject otherInvocation = legacyActivation(
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
    public void mergeDeduplicatesExactMembersAndRejectsMixedProducers() {
        OutputClosureContract first = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        OutputClosureContract second = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.1", "<P: int y>", "DF.2"));
        OutputClosureContract merged = OutputClosureCodec.merge(
                Arrays.asList(second, first, first));
        assertEquals(Arrays.asList("REGION.1.out.0", "REGION.1.out.1"),
                Arrays.asList(merged.outputPorts().toArray(new String[0])));

        JsonObject foreign = legacyActivation(
                "REGION.2.out.0", "<P: int z>", "DF.3");
        setProducer(foreign, "REGION.2", "REGION.2@test#call7", 7);
        expectFailure(() -> OutputClosureCodec.merge(Arrays.asList(
                first, OutputClosureCodec.decode(foreign))),
                "different producer");
    }

    @Test
    public void memberViewRequiresExactActivationProducerAndPort() {
        JsonObject activation = legacyActivation(
                "REGION.1.out.0", "<P: int x>", "DF.1");
        OutputClosureContract closure = OutputClosureCodec.decode(activation);
        JsonObject explicit = activation.deepCopy();
        OutputClosureCodec.writeTo(explicit, closure);
        JsonObject view = OutputClosureCodec.memberActivationView(
                explicit, closure, "REGION.1.out.0");
        assertEquals("REGION.1.out.0",
                view.getAsJsonObject("requestedOutput")
                        .get("portId").getAsString());

        explicit.addProperty("rootCallId", 8);
        expectFailure(() -> OutputClosureCodec.memberActivationView(
                explicit, closure, "REGION.1.out.0"), "conflicts");
        expectFailure(() -> OutputClosureCodec.memberActivationView(
                activation, closure, "REGION.1.out.missing"),
                "has no member");
    }

    @Test
    public void legacyReturnWithoutDirectCaptureIsSupported() {
        String method = "<P: int compute()>";
        JsonObject activation = legacyActivation(
                "REGION.1.out.0", method + ".return", "DF.1");
        setOutputKind(activation, "RETURN");
        setCaptures(activation, false, new JsonArray());

        OutputClosureContract closure = OutputClosureCodec.decode(activation);

        assertEquals("RETURN", closure.members().get(0).outputKind());
        assertEquals("I",
                closure.members().get(0).javaTypeDescriptor());
        assertFalse(closure.members().get(0).captureRequired());
    }

    @Test
    public void callCaptureChecksFormalMethodIndexAndType() {
        String formal = "<P: void publish(int)>.param0:int";
        JsonObject activation = legacyActivation(
                "REGION.1.out.0", formal, "DF.1");
        setOutputKind(activation, "REGION_OUTPUT");
        JsonObject capture = activation.getAsJsonArray(
                "requestedOutputCapture").get(0).getAsJsonObject();
        capture.remove("captureKind");
        capture.remove("fieldSignature");
        capture.remove("method");
        capture.addProperty("callerMethod", "<P: void run()>");
        capture.addProperty("calleeMethod", "<P: void publish(int)>");
        capture.addProperty("argumentIndex", 0);
        capture.addProperty("argumentCell", "<P: void run()>::i0");
        capture.addProperty("outputCell", formal);
        activation.getAsJsonObject("requestedOutputSlice")
                .addProperty("outputCell", formal);
        activation.getAsJsonObject("requestedOutputSlice")
                .add("captureBindings",
                        activation.getAsJsonArray(
                                "requestedOutputCapture").deepCopy());

        OutputClosureContract closure = OutputClosureCodec.decode(activation);
        assertEquals("I",
                closure.members().get(0).javaTypeDescriptor());

        JsonObject malformed = closure.toJson();
        malformed.getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonArray("captureBindings").get(0).getAsJsonObject()
                .addProperty("calleeMethod", "<P: void publish(long)>");
        expectFailure(() -> OutputClosureCodec.decodeEnvelope(malformed),
                "call capture endpoint");
    }

    @Test
    public void explicitCaptureLedgerCannotDiverge() {
        OutputClosureContract closure = OutputClosureCodec.decode(
                legacyActivation("REGION.1.out.0", "<P: int x>", "DF.1"));
        JsonObject encoded = closure.toJson();
        encoded.getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .add("captureBindings", new JsonArray());
        expectFailure(() -> OutputClosureCodec.decodeEnvelope(encoded),
                "capture ledger");
    }

    private static JsonObject legacyActivation(
            String port, String cell, String edgeId) {
        String method = "<P: void run()>";
        String site = method + "#u2";
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.1");
        activation.addProperty("regionId", "REGION.1");
        activation.addProperty("regionInstanceId",
                "REGION.1@test#call7");
        activation.addProperty("rootCallId", 7);

        JsonObject requested = new JsonObject();
        requested.addProperty("portId", port);
        requested.addProperty("cell", cell);
        requested.addProperty("kind", "HEAP_STATE");
        requested.addProperty("selectionAuthority",
                "CONFIRMED_READ_FROM_EDGE");
        activation.add("requestedOutput", requested);

        JsonObject output = new JsonObject();
        output.addProperty("symbol", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        activation.add("outputs", outputs);

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
        activation.add("requestedOutputCapture", captures);
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);

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
        activation.add("requestedOutputSlice", slice);
        activation.add("requestedOutputMethods", strings(method));
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
    }

    private static void setOutputKind(
            JsonObject activation, String kind) {
        activation.getAsJsonObject("requestedOutput")
                .addProperty("kind", kind);
        activation.getAsJsonArray("outputs").get(0).getAsJsonObject()
                .addProperty("kind", kind);
    }

    private static void setCaptures(
            JsonObject activation, boolean required, JsonArray captures) {
        activation.addProperty("requestedOutputCaptureRequired", required);
        activation.add("requestedOutputCapture", captures.deepCopy());
        JsonObject slice = activation.getAsJsonObject(
                "requestedOutputSlice");
        slice.addProperty("captureBindingsRequired", required);
        slice.add("captureBindings", captures.deepCopy());
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
