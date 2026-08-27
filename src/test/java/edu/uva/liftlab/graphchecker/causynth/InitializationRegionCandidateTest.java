package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The birth-of-state rule: which initialization paths may be offered a
 * candidate region root, and which must be refused because a root there would
 * capture the write without the derivation of the value written.
 */
public class InitializationRegionCandidateTest {

    /** Shaped after the key-birth path: writes and derives in one frame. */
    private static final String SELF_CONTAINED_INIT =
            "<example.KeyStore: void <init>(boolean,long)>";
    private static final String SELF_CONTAINED_FIELD =
            "<example.KeyStore: java.util.Map allKeys>";
    /** A private helper the initializer itself calls. */
    private static final String INIT_HELPER =
            "<example.KeyStore: void generate()>";
    /** Shaped after the value-object case: the read is in the caller. */
    private static final String CARRIER_INIT =
            "<example.Carrier: void <init>(int,java.lang.String)>";
    private static final String CARRIER_FIELD =
            "<example.Carrier: int keyId>";
    private static final String CARRIER_CALLER =
            "<example.KeyStore: example.Carrier newCarrier()>";
    private static final String CARRIER_CALLER_OUTER =
            "<example.Manager: example.Carrier fetch()>";

    // ------------------------------------------------------------------
    // The causal bound is consumed, never re-derived
    // ------------------------------------------------------------------

    @Test
    public void demandThatNoFailureDirectedOffersNothing() {
        List<Map<String, Object>> decisions =
                StaticProgram.initializationRootDecisions("ANY_HEAP_WRITE",
                        Collections.singletonList(selfContainedSlice()),
                        callSites());

        assertEquals(1, decisions.size());
        assertEquals(StaticProgram.INITIALIZATION_REFUSED,
                decisions.get(0).get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_DEMAND_BOUND_UNSTATED,
                decisions.get(0).get(StaticProgram.INITIALIZATION_REASON));
    }

    @Test
    public void noDemandOffersNothing() {
        assertTrue(StaticProgram.initializationRootDecisions(
                StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                Collections.<Map<String, Object>>emptyList(),
                callSites()).isEmpty());
    }

    @Test
    public void aWriteOutsideAnInitializerIsNeverACandidate() {
        Map<String, Object> slice = slice(
                Collections.singletonList(
                        "<example.KeyStore: void addKeys()>#u4"),
                Collections.<String>emptyList(),
                binding("<example.KeyStore: void addKeys()>", 4,
                        SELF_CONTAINED_FIELD));

        assertTrue(StaticProgram.initializationRootDecisions(
                StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                Collections.singletonList(slice), callSites()).isEmpty());
    }

    @Test
    public void anInitializerWritingNoDeclaredFieldIsNeverACandidate() {
        Map<String, Object> slice = slice(
                Collections.singletonList(SELF_CONTAINED_INIT + "#u23"),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, ""));

        assertTrue(StaticProgram.initializationRootDecisions(
                StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                Collections.singletonList(slice), callSites()).isEmpty());
    }

    // ------------------------------------------------------------------
    // The span rule
    // ------------------------------------------------------------------

    @Test
    public void selfContainedInitializationBirthIsOffered() {
        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(selfContainedSlice()),
                        callSites()));

        assertEquals(SELF_CONTAINED_INIT,
                decision.get(StaticProgram.INITIALIZATION_ROOT));
        assertEquals(StaticProgram.INITIALIZATION_OFFERED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_SELF_CONTAINED,
                decision.get(StaticProgram.INITIALIZATION_REASON));
        assertEquals(Collections.singletonList(SELF_CONTAINED_FIELD),
                decision.get(StaticProgram.INITIALIZATION_FIELDS));
        assertEquals(Collections.singletonList(SELF_CONTAINED_INIT + "#u23"),
                decision.get(StaticProgram.INITIALIZATION_WRITE_SITES));
        assertEquals(Collections.emptyList(),
                decision.get(StaticProgram.INITIALIZATION_SEVERED_FRAMES));
    }

    @Test
    public void aHelperTheInitializerCallsStaysInsideTheSpan() {
        Map<String, Object> slice = slice(
                Arrays.asList(SELF_CONTAINED_INIT + "#u23",
                        INIT_HELPER + "#u5"),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), callSites()));

        assertEquals(StaticProgram.INITIALIZATION_OFFERED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_SELF_CONTAINED,
                decision.get(StaticProgram.INITIALIZATION_REASON));
    }

    @Test
    public void aWriteDerivedInAnEnclosingFrameIsRefused() {
        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(carrierSlice()),
                        callSites()));

        assertEquals(CARRIER_INIT,
                decision.get(StaticProgram.INITIALIZATION_ROOT));
        assertEquals(StaticProgram.INITIALIZATION_REFUSED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_ENCLOSING_FRAME,
                decision.get(StaticProgram.INITIALIZATION_REASON));
        assertEquals(Collections.singletonList(CARRIER_CALLER),
                decision.get(StaticProgram.INITIALIZATION_SEVERED_FRAMES));
    }

    @Test
    public void anEnclosingFrameIsFoundThroughTheWholeCallChain() {
        Map<String, Object> slice = slice(
                Arrays.asList(CARRIER_INIT + "#u8",
                        CARRIER_CALLER_OUTER + "#u2"),
                Collections.<String>emptyList(),
                binding(CARRIER_INIT, 8, CARRIER_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), callSites()));

        assertEquals(StaticProgram.INITIALIZATION_ENCLOSING_FRAME,
                decision.get(StaticProgram.INITIALIZATION_REASON));
        assertEquals(Collections.singletonList(CARRIER_CALLER_OUTER),
                decision.get(StaticProgram.INITIALIZATION_SEVERED_FRAMES));
    }

    @Test
    public void oneRefusedMemberRefusesTheWholeInitializationRoot() {
        // One field is derived in the initializer alone and would stand on
        // its own; a sibling field of the same initializer is not.  A root
        // spans one frame, so the failing member decides the root.
        Map<String, Object> standsAlone = slice(
                Collections.singletonList(CARRIER_INIT + "#u3"),
                Collections.<String>emptyList(),
                binding(CARRIER_INIT, 3,
                        "<example.Carrier: byte[] nonce>"));

        List<Map<String, Object>> decisions =
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Arrays.asList(standsAlone, carrierSlice()),
                        callSites());

        Map<String, Object> decision = only(decisions);
        assertEquals(StaticProgram.INITIALIZATION_REFUSED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_ENCLOSING_FRAME,
                decision.get(StaticProgram.INITIALIZATION_REASON));
        assertEquals(Arrays.asList("<example.Carrier: byte[] nonce>",
                        CARRIER_FIELD),
                decision.get(StaticProgram.INITIALIZATION_FIELDS));
    }

    @Test
    public void aWriteDependingOnDemandedSharedStateIsRefused() {
        Map<String, Object> slice = slice(
                Collections.singletonList(SELF_CONTAINED_INIT + "#u23"),
                Collections.singletonList(
                        "<example.KeyStore: example.Key currentKey>"),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), callSites()));

        assertEquals(StaticProgram.INITIALIZATION_REFUSED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_DEMANDED_HEAP_DEPENDENCE,
                decision.get(StaticProgram.INITIALIZATION_REASON));
    }

    // ------------------------------------------------------------------
    // Fail-closed exits
    // ------------------------------------------------------------------

    @Test
    public void aSliceStatingNoDefinitionSiteIsRefused() {
        Map<String, Object> slice = slice(Collections.<String>emptyList(),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), callSites()));

        assertEquals(StaticProgram.INITIALIZATION_REFUSED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_SPAN_UNDECIDABLE,
                decision.get(StaticProgram.INITIALIZATION_REASON));
    }

    @Test
    public void anUnreadableDefinitionSiteIsRefused() {
        Map<String, Object> slice = slice(
                Arrays.asList(SELF_CONTAINED_INIT + "#u23", "not-a-site"),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), callSites()));

        assertEquals(StaticProgram.INITIALIZATION_SPAN_UNDECIDABLE,
                decision.get(StaticProgram.INITIALIZATION_REASON));
    }

    @Test
    public void anUnplaceableDerivationFrameIsRefused() {
        // The recorded call relation places neither an enclosing nor a
        // called frame for this site, so the span cannot be proved.
        Map<String, Object> slice = slice(
                Arrays.asList(SELF_CONTAINED_INIT + "#u23",
                        "<example.Elsewhere: void other()>#u1"),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), callSites()));

        assertEquals(StaticProgram.INITIALIZATION_REFUSED,
                decision.get(StaticProgram.INITIALIZATION_DECISION));
        assertEquals(StaticProgram.INITIALIZATION_OUTSIDE_ROOT_SCOPE,
                decision.get(StaticProgram.INITIALIZATION_REASON));
    }

    @Test
    public void anAbsentCallRelationLeavesEveryOtherFrameUnplaceable() {
        Map<String, Object> slice = slice(
                Arrays.asList(SELF_CONTAINED_INIT + "#u23",
                        INIT_HELPER + "#u5"),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));

        Map<String, Object> decision = only(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(slice), null));

        assertEquals(StaticProgram.INITIALIZATION_OUTSIDE_ROOT_SCOPE,
                decision.get(StaticProgram.INITIALIZATION_REASON));
    }

    // ------------------------------------------------------------------
    // What the planner mints from a decision
    // ------------------------------------------------------------------

    @Test
    public void anOfferedInitializerBecomesOneCandidateRegion() {
        StaticProgram program = initializerProgram();
        program.initializationDecisions.addAll(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(selfContainedSlice()),
                        callSites()));

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(SELF_CONTAINED_INIT, INIT_HELPER));

        assertEquals(1, program.regions.size());
        Map<String, Object> region = program.regions.get(0);
        assertEquals(SymbolicRegionPlanner.INITIALIZATION_ENTRY,
                region.get("rootAuthority"));
        assertEquals(SymbolicRegionPlanner.INITIALIZATION_CONTEXT,
                region.get("selection"));
        assertEquals(SELF_CONTAINED_INIT, region.get("rootMethod"));
        assertEquals(SELF_CONTAINED_INIT, region.get("anchorMethod"));
        assertEquals(Arrays.asList(SELF_CONTAINED_INIT, INIT_HELPER),
                region.get("methods"));
        assertEquals(Collections.singletonList(SELF_CONTAINED_FIELD),
                region.get(SymbolicRegionPlanner.INITIALIZATION_DEMAND));
        assertEquals(Collections.singletonList(SELF_CONTAINED_INIT + "#u23"),
                region.get(SymbolicRegionPlanner.INITIALIZATION_WRITE_SITES));
        // An offer to observe states no value, no version and no occurrence.
        assertFalse(region.containsKey("symbolicInputs"));
        assertFalse(region.containsKey("outputs"));
        assertFalse(region.containsKey("branchPolicies"));
        // And it decodes as a first-class region row.
        StaticProgram.RegionRow decoded = StaticProgram.regionRows(
                program.regions,
                RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "test").get(0);
        assertEquals(SELF_CONTAINED_INIT, decoded.rootMethod);
        assertEquals(SymbolicRegionPlanner.INITIALIZATION_ENTRY,
                decoded.rootAuthority);
    }

    @Test
    public void aRefusedInitializerIsNeverPlanned() {
        StaticProgram program = initializerProgram();
        program.initializationDecisions.addAll(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(carrierSlice()),
                        callSites()));

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(SELF_CONTAINED_INIT, INIT_HELPER));

        assertTrue(program.regions.isEmpty());
    }

    @Test
    public void aRunWithNoDecisionsPlansNoInitializationRegion() {
        StaticProgram program = initializerProgram();

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(SELF_CONTAINED_INIT, INIT_HELPER));

        assertTrue(program.regions.isEmpty());
    }

    @Test
    public void anOfferedInitializerOutsideTheSelectedSliceIsNotPlanned() {
        StaticProgram program = initializerProgram();
        program.initializationDecisions.addAll(
                StaticProgram.initializationRootDecisions(
                        StaticProgram.FAILURE_DEMANDED_OUTPUTS,
                        Collections.singletonList(selfContainedSlice()),
                        callSites()));

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Collections.singletonList(INIT_HELPER));

        assertTrue(program.regions.isEmpty());
    }

    // ------------------------------------------------------------------
    // Fixtures
    // ------------------------------------------------------------------

    private static Map<String, Object> selfContainedSlice() {
        return slice(Collections.singletonList(SELF_CONTAINED_INIT + "#u23"),
                Collections.<String>emptyList(),
                binding(SELF_CONTAINED_INIT, 23, SELF_CONTAINED_FIELD));
    }

    private static Map<String, Object> carrierSlice() {
        return slice(Arrays.asList(CARRIER_INIT + "#u8",
                        CARRIER_CALLER + "#u2"),
                Arrays.asList("<example.KeyStore: example.Key currentKey>"),
                binding(CARRIER_INIT, 8, CARRIER_FIELD));
    }

    private static Map<String, Object> slice(List<String> staticSites,
                                             List<String> demandedHeap,
                                             Map<String, Object> binding) {
        Map<String, Object> slice = new LinkedHashMap<>();
        slice.put("staticSites", new ArrayList<>(staticSites));
        slice.put("sites", new ArrayList<String>());
        slice.put("demandedHeapDeclarations", new ArrayList<>(demandedHeap));
        slice.put("captureBindings", new ArrayList<>(
                Collections.singletonList(binding)));
        return slice;
    }

    private static Map<String, Object> binding(String definitionMethod,
                                               int unitIndex, String field) {
        Map<String, Object> binding = new LinkedHashMap<>();
        binding.put("captureKind", "FIELD_WRITE_STATE");
        binding.put("definitionMethod", definitionMethod);
        binding.put("definitionUnitIndex", unitIndex);
        binding.put("fieldSignature", field);
        return binding;
    }

    /** {@code KeyStore.<init>} calls its helper; the carrier's callers call
     *  the carrier's initializer, through one more frame above them. */
    private static Map<String, List<String>> callSites() {
        Map<String, List<String>> sites = new LinkedHashMap<>();
        sites.put(INIT_HELPER, Collections.singletonList(
                SELF_CONTAINED_INIT + "#u30"));
        sites.put(CARRIER_INIT, Collections.singletonList(
                CARRIER_CALLER + "#u4"));
        sites.put(CARRIER_CALLER, Collections.singletonList(
                CARRIER_CALLER_OUTER + "#u1"));
        return sites;
    }

    /** A program whose selected slice holds the initializer and its helper. */
    private static StaticProgram initializerProgram() {
        StaticProgram program = new StaticProgram();
        program.edges.add(callEdge(SELF_CONTAINED_INIT, INIT_HELPER));
        program.edges.add(callEdge(CARRIER_CALLER, CARRIER_INIT));
        return program;
    }

    private static Map<String, Object> callEdge(String caller,
                                                String callee) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("method", caller);
        edge.put("invoke", callee);
        edge.put("transferKind", "VALUE_PASS");
        edge.put("kind", "call_argument");
        edge.put("fromCell", caller + "::a");
        edge.put("toCell", callee + "::p0");
        return edge;
    }

    private static Map<String, Object> only(
            List<Map<String, Object>> decisions) {
        assertEquals(1, decisions.size());
        return decisions.get(0);
    }
}
