package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class AutomaticRegionEdgeTest {

    @Test
    public void readFromRequiresExplicitLaneOrderMetadata() {
        JsonObject binding = readFromBinding();
        assertTrue(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));

        binding.remove("programOrderRequired");
        assertFalse(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
    }

    @Test
    public void readFromLaneAndProgramOrderMustAgree() {
        JsonObject binding = readFromBinding();
        binding.addProperty("readerLaneId", "lane.writer");

        assertFalse(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
        binding.addProperty("programOrderRequired", true);
        assertTrue(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
    }

    @Test
    public void crossLaneReadFromDoesNotRequireObservedHappensBefore() {
        JsonObject binding = readFromBinding();
        binding.addProperty("writerEventSeq", 9L);
        binding.addProperty("readerEventSeq", 6L);

        assertTrue(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
    }

    @Test
    public void sameLaneReadFromRejectsReversedProgramOrder() {
        JsonObject binding = readFromBinding();
        binding.addProperty("readerLaneId", "lane.writer");
        binding.addProperty("programOrderRequired", true);
        binding.addProperty("writerEventSeq", 9L);
        binding.addProperty("readerEventSeq", 6L);

        assertFalse(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
    }

    @Test
    public void containerMutationKeepsInternalOrderButNotCrossLaneHb() {
        JsonObject binding = containerMutationBinding();
        assertTrue(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));

        binding.addProperty("mutatorEnterSeq", 3L);
        assertFalse(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
    }

    @Test
    public void sameLaneContainerMutationRejectsReversedReadOrder() {
        JsonObject binding = containerMutationBinding();
        binding.addProperty("readerLaneId", "lane.writer");
        binding.addProperty("programOrderRequired", true);

        assertFalse(AutomaticRegionEdge.trustedRuntimeReadFromBinding(
                binding));
    }

    @Test
    public void trustedConfiguredResponseMappingIsComposable() {
        JsonObject edge = responseEdge(responseBinding());

        assertTrue(AutomaticRegionEdge.composable(edge));
        assertEquals("EQUALITY", AutomaticRegionEdge.relation(edge));
    }

    @Test
    public void untrustedConfiguredMappingIsRejected() {
        JsonObject binding = responseBinding();
        binding.addProperty("correlationAuthority",
                "UNTRUSTED_RUNTIME_OBSERVATION");

        assertFalse(AutomaticRegionEdge.composable(responseEdge(binding)));
    }

    @Test
    public void responseWithReversedProtocolLineageIsRejected() {
        JsonObject binding = responseBinding();
        binding.addProperty("callerSiteEventSeq", 41L);

        assertFalse(AutomaticRegionEdge.composable(responseEdge(binding)));
    }

    @Test
    public void responseBindingMustNameConfiguredPorts() {
        JsonObject binding = responseBinding();
        binding.remove("toInputPort");

        assertFalse(AutomaticRegionEdge.composable(responseEdge(binding)));
    }

    @Test
    public void declaredFieldFamilyCandidateIsNeverComposable() {
        JsonObject candidate = readFromBinding();
        candidate.addProperty("evidenceKind",
                "DECLARED_FIELD_COORDINATION_CANDIDATE_V1");
        candidate.addProperty("correlationAuthority",
                "FAILURE_SLICED_DECLARED_FIELD_FAMILY_V1");

        assertFalse(AutomaticRegionEdge
                .trustedRuntimeCompositionBinding(candidate));
    }

    private static JsonObject responseEdge(JsonObject binding) {
        JsonObject edge = binding.deepCopy();
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("edgeId", "RP.response");
        edge.addProperty("transportKind", "TEST_RPC");
        edge.addProperty("state", "CONFIRMED_TRUSTED_CONFIGURED_RPC");
        return edge;
    }

    private static JsonObject responseBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("evidenceKind",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        binding.addProperty("protocolDirection", "RESPONSE");
        binding.addProperty("mappingId", "example.rpc.response");
        binding.addProperty("fromRegion", "REGION.server");
        binding.addProperty("toRegion", "REGION.client");
        binding.addProperty("fromRegionInstance",
                "REGION.server@test#call22");
        binding.addProperty("toRegionInstance",
                "REGION.client@test#call11");
        binding.addProperty("fromOutputPort", "REGION.server.out.response");
        binding.addProperty("toInputPort", "REGION.client.in.response");
        binding.addProperty("correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        binding.addProperty("callerSiteEventSeq", 39L);
        binding.addProperty("sendEventSeq", 40L);
        binding.addProperty("receiveEventSeq", 41L);
        return binding;
    }

    private static JsonObject readFromBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("fromRegionInstance", "REGION.writer@call1");
        binding.addProperty("toRegionInstance", "REGION.reader@call2");
        binding.addProperty("fromOutputPort", "REGION.writer.out.value");
        binding.addProperty("toInputPort", "REGION.reader.in.value");
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("receiverObjectId", 17L);
        binding.addProperty("writerEventSeq", 5L);
        binding.addProperty("readerEventSeq", 6L);
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        return binding;
    }

    private static JsonObject containerMutationBinding() {
        JsonObject binding = readFromBinding();
        binding.addProperty("evidenceKind",
                "CONTAINER_MUTATION_READ_FROM_V1");
        binding.addProperty("writerFieldReadSeq", 3L);
        binding.addProperty("mutatorEnterSeq", 4L);
        binding.addProperty("mutationCompletionSeq", 9L);
        binding.addProperty("writerEventSeq", 9L);
        binding.addProperty("readerEventSeq", 6L);
        binding.addProperty("mutationInvocationId", 21L);
        binding.addProperty("mutatorDeclaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>");
        binding.addProperty("valueObjectId", 31L);
        binding.addProperty("readerValueObjectId", 32L);
        return binding;
    }
}
