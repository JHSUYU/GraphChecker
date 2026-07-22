package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class AutomaticRegionEdgeTest {
    @Test
    public void staticContractAndEndpointOrderCannotDeclareEquality() {
        JsonObject edge = baseEquality();
        edge.addProperty("status", "CONFIRMED_PROTOCOL_MAPPING");
        edge.addProperty("mappingAuthority", "STATIC_DOMAIN_CONTRACT");
        edge.addProperty("endpointPairCount", 1);
        edge.addProperty("orderedPairCount", 1);

        assertFalse(AutomaticRegionEdge.composable(edge));
        assertTrue(AutomaticRegionEdge.discoverable(edge));
        assertTrue(AutomaticRegionEdge.exclusionReason(edge).contains(
                "RUNTIME_VALUE_EQUALITY"));
    }

    @Test
    public void completeRuntimeFingerprintCanPromoteMappedPorts() {
        JsonObject edge = baseEquality();
        edge.addProperty("status", "CONFIRMED_RUNTIME_VALUE_EQUALITY");
        edge.addProperty("valueEqualityObserved", true);
        edge.addProperty("confirmedValueEqualityPairCount", 1);
        edge.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        edge.addProperty("eligibleForAutomaticDerivation", true);
        edge.addProperty("eligibleForAutomaticSmt", true);

        assertTrue(AutomaticRegionEdge.composable(edge));
        assertTrue(AutomaticRegionEdge.discoverable(edge));

        edge.remove("eligibleForAutomaticSmt");
        assertFalse(AutomaticRegionEdge.composable(edge));

        edge.addProperty("eligibleForAutomaticSmt", true);
        edge.addProperty("valueEqualityAuthority", "RUNTIME_UNTRUSTED_ALIAS");
        assertFalse(AutomaticRegionEdge.composable(edge));
    }

    @Test
    public void confirmedReadFromRequiresValidatedRuntimeBinding() {
        JsonObject edge = new JsonObject();
        edge.addProperty("fromRegion", "REGION.WRITER");
        edge.addProperty("fromPort", "REGION.WRITER.out.0");
        edge.addProperty("toRegion", "REGION.READER");
        edge.addProperty("toPort", "REGION.READER.in.0");
        edge.addProperty("validatedRelation", "READ_FROM");
        edge.addProperty("status", "CONFIRMED_READ_FROM");
        edge.addProperty("composable", true);
        edge.addProperty("confirmedReadFromPairCount", 1);
        edge.addProperty("eligibleForAutomaticDerivation", true);
        edge.addProperty("eligibleForAutomaticSmt", true);
        edge.addProperty("eligibleForRecursiveDiscovery", false);
        edge.addProperty("requiresOrder", true);
        edge.addProperty("endpointPairCount", 1);
        edge.addProperty("orderedPairCount", 0);

        assertFalse(AutomaticRegionEdge.composable(edge));

        JsonArray bindings = new JsonArray();
        bindings.add(fieldAssignmentBinding());
        edge.add("validatedBindings", bindings);
        assertTrue(AutomaticRegionEdge.composable(edge));
        assertTrue(AutomaticRegionEdge.discoverable(edge));
    }

    @Test
    public void staticMappedTransitionIsExecutionCandidateButNeverComposable() {
        JsonObject edge = baseEquality();
        edge.addProperty("validatedRelation", "");
        edge.addProperty("candidateRelation", "EQUALITY");
        edge.addProperty("composable", false);
        edge.addProperty("eligibleForAutomaticDerivation", false);
        edge.addProperty("eligibleForAutomaticSmt", false);
        edge.addProperty("mappingOnly", true);
        edge.addProperty("payloadEqualityCheckRequired", true);
        edge.addProperty("mappingAuthority",
                "STATIC_FORMAT_AND_PORT_MAPPING");

        assertTrue(AutomaticRegionEdge.transitionDiscoveryCandidate(edge));
        assertFalse(AutomaticRegionEdge.composable(edge));
        assertFalse(AutomaticRegionEdge.discoverable(edge));
    }

    @Test
    public void arbitraryUnobservedStaticEdgeCannotTriggerTransitionRun() {
        JsonObject edge = baseEquality();
        edge.addProperty("validatedRelation", "");
        edge.addProperty("composable", false);
        edge.addProperty("eligibleForAutomaticDerivation", false);
        edge.addProperty("eligibleForAutomaticSmt", false);

        assertFalse(AutomaticRegionEdge.transitionDiscoveryCandidate(edge));
    }

    @Test
    public void containerMutationRequiresCompletionAndSameContainerIdentity() {
        JsonObject complete = containerMutationBinding();
        assertTrue(AutomaticRegionEdge
                .trustedRuntimeReadFromBinding(complete));

        JsonObject missingCompletion = complete.deepCopy();
        missingCompletion.remove("mutationCompletionSeq");
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeReadFromBinding(missingCompletion));

        JsonObject differentContainer = complete.deepCopy();
        differentContainer.addProperty("readerValueObjectId", 45);
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeReadFromBinding(differentContainer));

        JsonObject readBeforeCompletion = complete.deepCopy();
        readBeforeCompletion.addProperty("readerEventSeq", 25);
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeReadFromBinding(readBeforeCompletion));

        JsonObject edge = new JsonObject();
        edge.addProperty("validatedRelation", "READ_FROM");
        edge.addProperty("status", "CONFIRMED_READ_FROM");
        edge.addProperty("composable", true);
        edge.addProperty("confirmedReadFromPairCount", 1);
        edge.addProperty("eligibleForAutomaticDerivation", true);
        edge.addProperty("eligibleForAutomaticSmt", true);
        JsonArray bindings = new JsonArray();
        bindings.add(differentContainer);
        edge.add("validatedBindings", bindings);
        assertFalse(AutomaticRegionEdge.composable(edge));

        bindings.set(0, complete);
        assertTrue(AutomaticRegionEdge.composable(edge));
    }

    @Test
    public void fieldAssignmentRequiresExactAuthorityOrderAndIdentity() {
        JsonObject complete = fieldAssignmentBinding();
        assertTrue(AutomaticRegionEdge.trustedReadFromEvidence(complete));

        JsonObject missingKind = complete.deepCopy();
        missingKind.remove("writeEvidenceKind");
        assertFalse(AutomaticRegionEdge.trustedReadFromEvidence(missingKind));

        JsonObject missingAuthority = complete.deepCopy();
        missingAuthority.remove("writeEvidenceAuthority");
        assertFalse(AutomaticRegionEdge.trustedReadFromEvidence(
                missingAuthority));

        JsonObject unconfirmedIdentity = complete.deepCopy();
        unconfirmedIdentity.addProperty("fieldReceiverIdentityConfirmed",
                false);
        assertFalse(AutomaticRegionEdge.trustedReadFromEvidence(
                unconfirmedIdentity));

        JsonObject reversedOrder = complete.deepCopy();
        reversedOrder.addProperty("readerEventSeq", 9);
        assertFalse(AutomaticRegionEdge.trustedReadFromEvidence(reversedOrder));
    }

    private static JsonObject baseEquality() {
        JsonObject edge = new JsonObject();
        edge.addProperty("fromRegion", "REGION.UP");
        edge.addProperty("fromPort", "REGION.UP.out.0");
        edge.addProperty("toRegion", "REGION.DOWN");
        edge.addProperty("toPort", "REGION.DOWN.in.0");
        edge.addProperty("validatedRelation", "EQUALITY");
        edge.addProperty("composable", true);
        return edge;
    }

    private static JsonObject containerMutationBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("relation", "READ_FROM");
        binding.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        binding.addProperty("writeEvidenceKind",
                "FIELD_CONTAINER_MUTATION");
        binding.addProperty("writeEvidenceAuthority",
                AutomaticRegionEdge.CONTAINER_MUTATION_READ_FROM_AUTHORITY);
        binding.addProperty("mutationContractAuthority",
                AutomaticRegionEdge.CONTAINER_MUTATOR_CONTRACT_AUTHORITY);
        binding.addProperty("orderAuthority",
                AutomaticRegionEdge.TRACE_ORDER_AUTHORITY);
        binding.addProperty("writerFieldReadSeq", 10);
        binding.addProperty("mutatorEnterSeq", 20);
        binding.addProperty("mutationCompletionSeq", 30);
        binding.addProperty("writerEventSeq", 30);
        binding.addProperty("readerEventSeq", 40);
        binding.addProperty("mutationInvocationId", 20);
        binding.addProperty("valueObjectId", 44);
        binding.addProperty("readerValueObjectId", 44);
        binding.addProperty("receiverObjectId", 55);
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("containerIdentityConfirmed", true);
        binding.addProperty("fieldReceiverIdentityConfirmed", true);
        binding.addProperty("mutatorDeclaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>");
        return binding;
    }

    private static JsonObject fieldAssignmentBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("relation", "READ_FROM");
        binding.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        binding.addProperty("writeEvidenceKind", "FIELD_ASSIGNMENT");
        binding.addProperty("writeEvidenceAuthority",
                "RUNTIME_EXACT_FIELD_WRITE_EVENT_V1");
        binding.addProperty("orderAuthority",
                AutomaticRegionEdge.TRACE_ORDER_AUTHORITY);
        binding.addProperty("writerEventSeq", 10);
        binding.addProperty("readerEventSeq", 20);
        binding.addProperty("receiverObjectId", 55);
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("fieldReceiverIdentityConfirmed", true);
        return binding;
    }
}
