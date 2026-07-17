package edu.uva.liftlab.graphchecker.concolic;

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
    }

    @Test
    public void confirmedReadFromRemainsDiscoverableDespiteLegacyOrderFlag() {
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
}
