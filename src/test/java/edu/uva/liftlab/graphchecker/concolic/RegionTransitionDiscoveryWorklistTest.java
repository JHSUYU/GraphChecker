package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RegionTransitionDiscoveryWorklistTest {
    @Test
    public void plansExactReachabilityFlipWithoutPromotingStaticMapping() {
        JsonObject producer = region(true);
        JsonObject consumer = new JsonObject();
        consumer.addProperty("regionId", "REGION.C");
        JsonObject target = new JsonObject();
        target.addProperty("regionId", "REGION.T");
        JsonObject root = new JsonObject();
        root.addProperty("regionId", "REGION.T");

        RegionTransitionDiscoveryWorklist.Result result =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(producer, consumer, target),
                        Collections.singletonList(activation()),
                        Arrays.asList(candidate(), bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults());

        assertEquals(1, result.requests.size());
        JsonObject request = result.requests.get(0);
        assertEquals("REGION.P.out.0", request.get(
                "upstreamOutputPort").getAsString());
        assertEquals("P#u6", request.getAsJsonObject(
                "transitionGuard").get("siteId").getAsString());
        assertFalse(request.get("automaticRelationEligible").getAsBoolean());
        assertFalse(request.get("eligibleForAutomaticSmt").getAsBoolean());
        assertTrue(RegionCaptureGoal.from(request).isTransitionDiscovery());
        assertFalse(AutomaticRegionEdge.composable(candidate()));
    }

    @Test
    public void exactEndpointWithoutExactSliceFailsClosed() {
        JsonObject root = new JsonObject();
        root.addProperty("regionId", "REGION.T");

        RegionTransitionDiscoveryWorklist.Result result =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(region(false), named("REGION.C"),
                                named("REGION.T")),
                        Collections.singletonList(activation()),
                        Arrays.asList(candidate(), bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults());

        assertTrue(result.requests.isEmpty());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("NO_EXACT_OUTPUT_SLICE"));
        assertFalse(result.manifest.get("eligibleForAutomaticSmt")
                .getAsBoolean());
    }

    @Test
    public void runtimeLocalProjectionNeedsPersistedExactCanonicalAlias() {
        JsonObject root = new JsonObject();
        root.addProperty("regionId", "REGION.T");
        JsonObject edge = candidate();
        edge.addProperty("fromPort", "<P: Payload make()>::$r5#field:keys");
        edge.addProperty("fromOutputPort", "REGION.P.out.0");
        edge.addProperty("fromOutputCell", "<P: Payload make()>::payload");

        RegionTransitionDiscoveryWorklist.Result rejected =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(region(true), named("REGION.C"),
                                named("REGION.T")),
                        Collections.singletonList(activation()),
                        Arrays.asList(edge, bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults());
        assertTrue(rejected.requests.isEmpty());
        assertTrue(rejected.manifest.getAsJsonArray("gaps").toString()
                .contains("INCOMPLETE_CANONICAL_OUTPUT_ALIAS_PROOF"));

        JsonArray proof = new JsonArray();
        proof.add("DF.CALL_RETURN.1");
        proof.add("DF.PROJECT.1");
        edge.add("aliasProofEdgeIds", proof);
        edge.addProperty("aliasProofAuthority",
                "STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                        + "AND_DECLARED_RETURN_FIELD");
        edge.addProperty("aliasProofComplete", true);
        RegionTransitionDiscoveryWorklist.Result admitted =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(region(true), named("REGION.C"),
                                named("REGION.T")),
                        Collections.singletonList(activation()),
                        Arrays.asList(edge, bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults());

        assertEquals(1, admitted.requests.size());
        JsonObject request = admitted.requests.get(0);
        assertEquals("STATIC_UNIQUE_ALIAS_PROOF", request.get(
                "canonicalOutputAuthority").getAsString());
        assertEquals(2, request.getAsJsonArray("aliasProofEdgeIds").size());
        assertEquals("<P: Payload make()>::$r5#field:keys", request.get(
                "edgeOutputEndpoint").getAsString());
    }

    @Test
    public void exactFocusFiltersEdgeAndSelectsOnlyRequestedActivation() {
        JsonObject root = named("REGION.T");
        JsonObject earlier = activation();
        earlier.addProperty("activationId", "ACT.P.0");
        earlier.addProperty("regionInstanceId", "REGION.P@test#call0");
        JsonObject selected = activation();
        JsonObject noise = candidate();
        noise.addProperty("edgeId", "EDGE.A.NOISE");

        RegionTransitionDiscoveryWorklist.Focus focus =
                new RegionTransitionDiscoveryWorklist.Focus(
                        "EDGE.P.C", "ACT.P.1", "P#u6");
        RegionTransitionDiscoveryWorklist.Result result =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(region(true), named("REGION.C"),
                                named("REGION.T")),
                        Arrays.asList(earlier, selected),
                        Arrays.asList(noise, candidate(), bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults(),
                        focus);

        assertEquals(1, result.requests.size());
        JsonObject request = result.requests.get(0);
        assertEquals("EDGE.P.C", request.get("candidateEdgeId")
                .getAsString());
        assertEquals("ACT.P.1", request.get("sourceActivationId")
                .getAsString());
        assertEquals("REGION.P@test#call1", request.get(
                "sourceRegionInstanceId").getAsString());
        assertEquals("P#u6", request.getAsJsonObject("transitionGuard")
                .get("siteId").getAsString());
        assertTrue(result.manifest.get("focusConfigured").getAsBoolean());
        assertTrue(result.manifest.get("focusedEdgeSeen").getAsBoolean());
        assertTrue(result.manifest.get("focusedActivationSeen")
                .getAsBoolean());
        assertTrue(result.manifest.get("focusedGuardSeen").getAsBoolean());
        assertEquals(1, result.manifest.get("candidateEdgeCount").getAsInt());
    }

    @Test
    public void focusedGuardMustBeOneExactMismatchedReachabilityGuard() {
        JsonObject root = named("REGION.T");
        RegionTransitionDiscoveryWorklist.Result missing =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(region(true), named("REGION.C"),
                                named("REGION.T")),
                        Collections.singletonList(activation()),
                        Arrays.asList(candidate(), bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults(),
                        new RegionTransitionDiscoveryWorklist.Focus(
                                "EDGE.P.C", "ACT.P.1", "P#u99"));

        assertTrue(missing.requests.isEmpty());
        assertTrue(missing.manifest.getAsJsonArray("gaps").toString()
                .contains("FOCUSED_GUARD_NOT_UNIQUE_MISMATCHED_"
                        + "REACHABILITY_GUARD"));

        JsonObject duplicate = activation();
        duplicate.getAsJsonArray("branches").add(
                branch("P#u6", true, false));
        RegionTransitionDiscoveryWorklist.Result ambiguous =
                RegionTransitionDiscoveryWorklist.plan(
                        Arrays.asList(region(true), named("REGION.C"),
                                named("REGION.T")),
                        Collections.singletonList(duplicate),
                        Arrays.asList(candidate(), bridge()),
                        Collections.singletonList(root),
                        Collections.<JsonObject>emptyList(),
                        RegionTransitionDiscoveryWorklist.Bounds.defaults(),
                        new RegionTransitionDiscoveryWorklist.Focus(
                                "EDGE.P.C", "ACT.P.1", "P#u6"));

        assertTrue(ambiguous.requests.isEmpty());
        assertTrue(ambiguous.manifest.getAsJsonArray("gaps").toString()
                .contains("FOCUSED_GUARD_AMBIGUOUS"));
    }

    private static JsonObject region(boolean includeSlice) {
        JsonObject region = named("REGION.P");
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.P.out.0");
        output.addProperty("cell", "<P: Payload make()>::payload");
        output.addProperty("kind", "SINK_STATE");
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        region.add("outputs", outputs);
        if (includeSlice) {
            JsonObject slice = new JsonObject();
            slice.addProperty("outputPort", "REGION.P.out.0");
            slice.addProperty("outputCell", "<P: Payload make()>::payload");
            slice.addProperty("complete", true);
            JsonArray sites = new JsonArray();
            sites.add("P#u4");
            sites.add("P#u6");
            slice.add("sites", sites);
            slice.add("inputPorts", new JsonArray());
            JsonArray slices = new JsonArray();
            slices.add(slice);
            region.add("outputSlices", slices);
        }
        return region;
    }

    private static JsonObject activation() {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.P.1");
        activation.addProperty("regionInstanceId", "REGION.P@test#call1");
        activation.addProperty("regionId", "REGION.P");
        JsonObject first = branch("P#u4", false, false);
        JsonObject second = branch("P#u6", true, false);
        JsonArray branches = new JsonArray();
        branches.add(first);
        branches.add(second);
        activation.add("branches", branches);
        return activation;
    }

    private static JsonObject branch(String site, boolean observed,
                                     boolean required) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", site);
        branch.addProperty("policy", "PATH_ASSUMPTION");
        branch.addProperty("role", "REACHABILITY");
        branch.addProperty("observed", true);
        branch.addProperty("observedOutcome", observed);
        branch.addProperty("requiredOutcome", required);
        branch.addProperty("selectedOccurrence", 1);
        return branch;
    }

    private static JsonObject candidate() {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.P.C");
        edge.addProperty("fromRegion", "REGION.P");
        edge.addProperty("fromPort", "REGION.P.out.0");
        edge.addProperty("toRegion", "REGION.C");
        edge.addProperty("toPort", "REGION.C.in.0");
        edge.addProperty("candidateRelation", "EQUALITY");
        edge.addProperty("composable", false);
        edge.addProperty("eligibleForAutomaticDerivation", false);
        edge.addProperty("eligibleForAutomaticSmt", false);
        edge.addProperty("mappingOnly", true);
        edge.addProperty("payloadEqualityCheckRequired", true);
        edge.addProperty("mappingAuthority",
                "STATIC_EXACT_PROTOCOL_PORT_MAPPING");
        return edge;
    }

    private static JsonObject bridge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.C.T");
        edge.addProperty("fromRegion", "REGION.C");
        edge.addProperty("fromPort", "REGION.C.out.0");
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("toPort", "REGION.T.in.0");
        return edge;
    }

    private static JsonObject named(String id) {
        JsonObject value = new JsonObject();
        value.addProperty("regionId", id);
        return value;
    }
}
