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
        JsonArray diagnostic = new JsonArray();
        diagnostic.add(new JsonObject());
        edge.add("evidence", diagnostic);

        assertFalse("diagnostic evidence is not a composable binding",
                AutomaticRegionEdge.composable(edge));

        JsonArray bindings = new JsonArray();
        bindings.add(new JsonObject());
        edge.add("validatedBindings", bindings);

        assertFalse("an empty canonical binding must fail closed",
                AutomaticRegionEdge.composable(edge));

        bindings.set(0, runtimeEqualityEvidence());

        assertTrue(AutomaticRegionEdge.composable(edge));

        edge.remove("eligibleForAutomaticSmt");
        assertFalse(AutomaticRegionEdge.composable(edge));

        edge.addProperty("eligibleForAutomaticSmt", true);
        edge.addProperty("valueEqualityAuthority", "RUNTIME_UNTRUSTED_ALIAS");
        assertFalse(AutomaticRegionEdge.composable(edge));
    }

    @Test
    public void runtimeEqualityWitnessTamperingFailsClosed() {
        JsonObject complete = runtimeEqualityEvidence();
        assertTrue(AutomaticRegionEdge
                .trustedRuntimeValueEqualityEvidence(complete));

        for (String field : new String[]{"fromRegionInstance",
                "toRegionInstance", "valueEqualityAuthority",
                "valueFingerprint", "endpointOrderAuthority",
                "fromEndpointSeq", "toEndpointSeq"}) {
            JsonObject tampered = complete.deepCopy();
            tampered.remove(field);
            assertFalse(field, AutomaticRegionEdge
                    .trustedRuntimeValueEqualityEvidence(tampered));
        }
        JsonObject unobserved = complete.deepCopy();
        unobserved.addProperty("valueEqualityObserved", false);
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeValueEqualityEvidence(unobserved));

        JsonObject unordered = complete.deepCopy();
        unordered.addProperty("orderConfirmed", false);
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeValueEqualityEvidence(unordered));

        JsonObject reversed = complete.deepCopy();
        reversed.addProperty("toEndpointSeq", 9);
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeValueEqualityEvidence(reversed));

        JsonObject aliases = complete.deepCopy();
        aliases.remove("fromEndpointSeq");
        aliases.remove("toEndpointSeq");
        aliases.addProperty("writerEventSeq", 10);
        aliases.addProperty("readerEventSeq", 20);
        assertTrue(AutomaticRegionEdge
                .trustedRuntimeValueEqualityEvidence(aliases));
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

    private static JsonObject runtimeEqualityEvidence() {
        JsonObject binding = new JsonObject();
        binding.addProperty("fromRegionInstance", "REGION.UP@call1");
        binding.addProperty("toRegionInstance", "REGION.DOWN@call2");
        binding.addProperty("valueEqualityObserved", true);
        binding.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        binding.addProperty("valueFingerprint", "sha256:complete");
        binding.addProperty("endpointOrderAuthority",
                AutomaticRegionEdge.VALUE_EQUALITY_ORDER_AUTHORITY);
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("fromEndpointSeq", 10);
        binding.addProperty("toEndpointSeq", 20);
        return binding;
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
