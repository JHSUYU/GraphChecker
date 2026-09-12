package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The campaign acceptance gate. Each test names one blocker the jq gate did
 * not have, or the accept path it must not withdraw.
 */
public class ClaimPolicyTest {

    /** A fault-sensitive SAT witness on a complete composition is accepted. */
    @Test
    public void connectedWitnessIsAcceptedAsSatCandidate() {
        JsonObject claim = ClaimPolicy.decide(manifest(), reach(), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE, claim.get("claim")
                .getAsString());
        assertEquals(0, claim.getAsJsonArray("blockers").size());
        assertEquals("", claim.get("whyNotAccepted").getAsString());
        assertTrue(claim.getAsJsonObject("rootSpace").get("faultSensitive")
                .getAsBoolean());
    }

    /** An open sibling path leaves a SAT candidate accepted, per README. */
    @Test
    public void openUnsatClosureDoesNotBlockSatCandidate() {
        JsonObject reach = reach();
        reach.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, false);

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                ClaimPolicy.decide(manifest(), reach, noFlows()).get("claim")
                        .getAsString());
    }

    /** A closed refutation is accepted only with closure authority. */
    @Test
    public void closedRefutationIsAcceptedAsUnsatClosed() {
        JsonObject claim = ClaimPolicy.decide(manifest(), refutation(true),
                noFlows());

        assertEquals(ClaimPolicy.UNSAT_CLOSED, claim.get("claim")
                .getAsString());
        assertEquals(0, claim.getAsJsonArray("blockers").size());
    }

    @Test
    public void openRefutationIsWithheldAsUnsatClosureIncomplete() {
        JsonObject claim = ClaimPolicy.decide(manifest(), refutation(false),
                noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.UNSAT_CLOSURE_INCOMPLETE),
                codes(claim));
    }

    @Test
    public void composerRefusalBlocksEveryClaim() {
        JsonObject manifest = manifest();
        manifest.addProperty("finalStatus", "SELECTED_MODEL_INCOMPLETE");
        manifest.add("finalStatusRefusals", parseArray(
                "[{\"code\":\"GUARDED_READ_ARM_UNNAMED\","
                        + "\"subject\":\"R#1\",\"detail\":\"x\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest, reach(), noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.COMPOSER_NOT_FINAL_READY,
                ClaimPolicy.COMPOSITION_GAPS_UNRESOLVED), codes(claim));
        assertTrue(claim.get("claimReason").getAsString()
                .contains("GUARDED_READ_ARM_UNNAMED"));
    }

    /** A solver gap is the same unresolved gap EMIT counts, under one name. */
    @Test
    public void solverGapBlocksEveryClaim() {
        JsonObject reach = reach();
        reach.add("gaps", parseArray("[\"UNDECIDED_SOLVER_VALUATIONS:2\"]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(codes(ClaimPolicy.COMPOSITION_GAPS_UNRESOLVED),
                codes(claim));
        assertTrue(blocker(claim, ClaimPolicy.COMPOSITION_GAPS_UNRESOLVED)
                .get("detail").getAsString()
                .contains("SOLVE/UNDECIDED_SOLVER_VALUATIONS:2"));
    }

    /** A root space the target provably ignores is named on its own. */
    @Test
    public void degenerateRootSpaceBlocksSatCandidate() {
        JsonObject reach = reach();
        reach.getAsJsonObject("reachCondition").addProperty("degeneracyCheck",
                "DEGENERATE_UNCONSTRAINED_ROOT_SPACE");

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.DEGENERATE_ROOT_SPACE), codes(claim));
    }

    /**
     * The hdfs-17899-bug3 finding: an undecided degeneracy question was
     * accepted as a witness by the jq gate. It is a distinct blocker from a
     * decided degenerate one, and it withholds the claim.
     */
    @Test
    public void undecidedRootSpaceBlocksSatCandidate() {
        JsonObject reach = reach();
        reach.getAsJsonObject("reachCondition").addProperty("degeneracyCheck",
                "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9");

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.UNDECIDED_ROOT_SPACE), codes(claim));
        assertEquals("UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9",
                blocker(claim, ClaimPolicy.UNDECIDED_ROOT_SPACE)
                        .get("subject").getAsString());
    }

    /** Every valuation satisfying alike means no root decides the target. */
    @Test
    public void witnessNoRootFlipsIsUnconstrainedByRoots() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(codes(ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS),
                codes(claim));
        assertFalse(claim.getAsJsonObject("rootSpace").get("faultSensitive")
                .getAsBoolean());
    }

    /** A rejected existential perturbation is the solver's own proof. */
    @Test
    public void rejectedPerturbationMakesTheWitnessFaultSensitive() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));
        reach.add("existentialRootProbe", parse(
                "{\"constrainsRootSpace\":true}"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE, claim.get("claim")
                .getAsString());
        assertTrue(ClaimPolicy.faultSensitive(
                reach.getAsJsonArray("valuations"), true));
    }

    /** A flip of two roots at once proves nothing about either of them. */
    @Test
    public void onlyOneRootFlipAtATimeProvesSensitivity() {
        JsonArray twoAtOnce = parseArray(
                "[{\"values\":[false,false],\"status\":\"sat\"},"
                        + "{\"values\":[true,true],\"status\":\"unsat\"}]");
        JsonArray oneAtATime = parseArray(
                "[{\"values\":[false,false],\"status\":\"sat\"},"
                        + "{\"values\":[false,true],\"status\":\"unsat\"}]");

        assertFalse(ClaimPolicy.faultSensitive(twoAtOnce, false));
        assertTrue(ClaimPolicy.faultSensitive(oneAtATime, false));
    }

    /**
     * A declared flow is realized when one of its own boundary families
     * reached a lowered term. That is the reading under which the blocker
     * means what its name says: the value the wire carried constrains the
     * formula.
     */
    @Test
    public void aBoundBoundaryFamilyRealizesADeclaredFlow()
            throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                ledgerManifest(bound(SASL_PORT), unbound(SASL_PORT)),
                reach(), flows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE, claim.get("claim")
                .getAsString());
        assertEquals(0, claim.getAsJsonArray("blockers").size());
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertTrue(flow.get("realized").getAsBoolean());
        assertEquals("BOUND_BOUNDARY_FAMILY",
                flow.get("mechanism").getAsString());
        // One port carries several families; the port is bound when any is.
        assertEquals(2, flow.get("familiesObserved").getAsInt());
        assertEquals(1, flow.get("familiesBound").getAsInt());
    }

    /**
     * The hdfs-17899-bug3 {@code block-key-id} shape: the composition
     * observed the flow's families and referred to none of them, so no term
     * carries the wire's value. Region ids of both endpoints still occur all
     * over that manifest, which is exactly what the old reading mistook for
     * realization.
     */
    @Test
    public void observedButUnboundFamiliesLeaveTheFlowUnrealized()
            throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                ledgerManifest(unbound(SASL_PORT), unbound(SASL_PORT)),
                reach(), flows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED),
                codes(claim));
        // The blocker names the flow, because a count cannot be acted on.
        assertEquals("data-encryption-key-id", blocker(claim,
                ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED)
                .get("subject").getAsString());
        assertTrue(blocker(claim, ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED)
                .get("detail").getAsString()
                .contains("data-encryption-key-id"));
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertFalse(flow.get("realized").getAsBoolean());
        assertEquals(2, flow.get("familiesObserved").getAsInt());
        assertEquals(0, flow.get("familiesBound").getAsInt());
    }

    /**
     * A family bound on a different flow's port does not realize this one.
     * Counting bound families in bulk, rather than per port, would.
     */
    @Test
    public void anotherFlowsBoundFamilyDoesNotRealizeThisOne()
            throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                ledgerManifest(bound(BLOCK_KEY_PORT)), reach(), flows());

        assertEquals(codes(ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED),
                codes(claim));
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertFalse(flow.get("realized").getAsBoolean());
        assertEquals(0, flow.get("familiesObserved").getAsInt());
    }

    /**
     * Consumer boundary families the composition drew but whose wire value
     * no term carries do not answer for a declared flow. Before this, any
     * family at all -- a FIELD_READ one included -- realized a flow with no
     * port evidence.
     */
    @Test
    public void boundaryFamiliesAloneDoNotRealizeAFlow() {
        JsonObject claim = ClaimPolicy.decide(
                boundaryManifest(CONSUMER_REGION, PRODUCER_REGION), reach(),
                ClaimPolicy.WireFlowEvidence.declaredOnly(
                        Collections.singletonList("block-key-id")));

        assertEquals(codes(ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED),
                codes(claim));
        assertEquals("BOUND_BOUNDARY_FAMILY",
                wireFlow(claim, "block-key-id").get("mechanism")
                        .getAsString());
    }

    /** A composition that published no handoff ledger binds nothing. */
    @Test
    public void noWireFlowLedgerBlocksTheClaim() {
        JsonObject claim = ClaimPolicy.decide(manifest(), reach(),
                ClaimPolicy.WireFlowEvidence.declaredOnly(
                        Collections.singletonList("block-key-id")));

        assertEquals(codes(ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED),
                codes(claim));
        assertEquals("block-key-id", blocker(claim,
                ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED).get("subject")
                .getAsString());
        assertEquals(0, wireFlow(claim, "block-key-id")
                .get("familiesObserved").getAsInt());
    }

    /** An experiment that declares no flow has none to realize. */
    @Test
    public void noDeclaredWireFlowNeedsNoBoundaryFamily() {
        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                ClaimPolicy.decide(manifest(), reach(), noFlows())
                        .get("claim").getAsString());
    }

    /**
     * The Composer publishes boundary families as
     * casePathConditionDependencies rows. Reading the retired
     * symbolicPropagation array instead counted zero on every real manifest.
     */
    @Test
    public void boundaryFamiliesAreCountedFromTheRowsTheComposerPublishes() {
        JsonObject manifest = boundaryManifest(CONSUMER_REGION,
                PRODUCER_REGION);

        assertFalse(manifest.has("symbolicPropagation"));
        assertEquals(2, ClaimPolicy.consumerBoundaryFamilies(manifest));
        assertEquals(0, ClaimPolicy.consumerBoundaryFamilies(manifest()));
    }

    /** A manifest that still carries the retired array is still counted. */
    @Test
    public void legacyPropagationArrayStillCountsAsBoundaryFamilies() {
        JsonObject manifest = manifest();
        JsonArray legacy = new JsonArray();
        legacy.add(parse("{\"armCount\":2}"));
        manifest.add("symbolicPropagation", legacy);

        assertEquals(1, ClaimPolicy.consumerBoundaryFamilies(manifest));
    }

    /** Region identities are read wherever the manifest names one. */
    @Test
    public void realizedRegionsAreReadFromEveryIdentityTheyAppearIn() {
        Set<String> regions = ClaimPolicy.realizedRegions(
                boundaryManifest(CONSUMER_REGION, PRODUCER_REGION));

        assertTrue(regions.contains(CONSUMER_REGION));
        assertTrue(regions.contains(PRODUCER_REGION));
        assertFalse(regions.contains(OTHER_REGION));
    }

    @Test
    public void everyZeroWitnessIsUninformative() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\","
                        + "\"existentialWitness\":[{\"value\":\"0\"},"
                        + "{\"value\":\"(- 0)\"}]},"
                        + "{\"values\":[true],\"status\":\"unsat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(codes(ClaimPolicy.WITNESS_UNINFORMATIVE), codes(claim));
        assertEquals("ALL_ZERO", blocker(claim,
                ClaimPolicy.WITNESS_UNINFORMATIVE).get("subject")
                .getAsString());
    }

    /** The hdfs-17899-bug3 witness: one vector under every valuation. */
    @Test
    public void invariantWitnessAcrossValuationsIsUninformative() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false,false],\"status\":\"sat\","
                        + "\"existentialWitness\":[{\"value\":\"7\"}]},"
                        + "{\"values\":[false,true],\"status\":\"sat\","
                        + "\"existentialWitness\":[{\"value\":\"7\"}]},"
                        + "{\"values\":[true,true],\"status\":\"unsat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(codes(ClaimPolicy.WITNESS_UNINFORMATIVE), codes(claim));
        assertEquals("INVARIANT_ACROSS_VALUATIONS", blocker(claim,
                ClaimPolicy.WITNESS_UNINFORMATIVE).get("subject")
                .getAsString());
    }

    /** A witness that moves with the roots is evidence, not a constant. */
    @Test
    public void varyingWitnessIsInformative() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false,false],\"status\":\"sat\","
                        + "\"existentialWitness\":[{\"value\":\"7\"}]},"
                        + "{\"values\":[false,true],\"status\":\"sat\","
                        + "\"existentialWitness\":[{\"value\":\"9\"}]},"
                        + "{\"values\":[true,true],\"status\":\"unsat\"}]"));

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                ClaimPolicy.decide(manifest(), reach, noFlows()).get("claim")
                        .getAsString());
    }

    @Test
    public void undecidedValuationRowBlocksTheClaim() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"unsat\"},"
                        + "{\"values\":[true],\"status\":\"unknown\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(codes(ClaimPolicy.SOLVER_UNDECIDED_VALUATIONS),
                codes(claim));
        assertEquals("1", blocker(claim,
                ClaimPolicy.SOLVER_UNDECIDED_VALUATIONS).get("subject")
                .getAsString());
    }

    @Test
    public void noExactReachabilityIsItsOwnBlocker() {
        JsonObject reach = reach();
        reach.getAsJsonObject("reachCondition").addProperty("reachability",
                "UNKNOWN");

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.NO_EXACT_REACHABILITY), codes(claim));
    }

    /** One line per blocker: the whole reason, in the owner's one view. */
    @Test
    public void whyNotAcceptedNamesEveryBlockerOnItsOwnLine() {
        JsonObject manifest = manifest();
        JsonObject reach = reach();
        reach.getAsJsonObject("reachCondition").addProperty("degeneracyCheck",
                "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9");
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest, reach,
                ClaimPolicy.WireFlowEvidence.declaredOnly(
                        Collections.singletonList("block-key-id")));
        String[] lines = claim.get("whyNotAccepted").getAsString()
                .split("\\R");

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.UNDECIDED_ROOT_SPACE,
                ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS,
                ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED), codes(claim));
        assertEquals(4, lines.length);
        assertTrue(lines[0].contains("3 blocker(s) withhold acceptance"));
        assertTrue(lines[1].contains(ClaimPolicy.UNDECIDED_ROOT_SPACE));
        assertTrue(lines[2].contains(
                ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS));
        assertTrue(lines[3].contains(
                ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED));
    }

    /** Only WIRE_FLOW rows are declared flows; no mapping file is none. */
    @Test
    public void declaredFlowsAreReadOnlyFromWireFlowRows()
            throws IOException {
        Path directory = Files.createTempDirectory("claim-policy");
        Path mappings = directory.resolve("mappings.jsonl");
        Files.write(mappings, (
                "{\"schemaVersion\":1,\"kind\":\"WIRE_FLOW\",\"id\":\"a\"}\n"
                + "{\"schemaVersion\":1,\"kind\":\"WIRE_FLOW\",\"id\":\"b\"}\n"
                + "{\"schemaVersion\":1,\"kind\":\"SHARED_FIELD\",\"id\":\"c\"}\n")
                .getBytes(StandardCharsets.UTF_8));

        assertEquals(2, ClaimPolicy.WireFlowEvidence
                .read(mappings.toString(), "").declaredCount());
        assertEquals(0, ClaimPolicy.WireFlowEvidence.read("", "")
                .declaredCount());
        assertEquals(0, ClaimPolicy.WireFlowEvidence
                .read(directory.resolve("absent.jsonl").toString(), "")
                .declaredCount());
    }

    /** The plan binds a flow's ports by the flow name the port id carries. */
    @Test
    public void plannedPortsAreReadFromTheHandoffPortIds()
            throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                boundaryManifest(CONSUMER_REGION, PRODUCER_REGION), reach(),
                flows());
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");

        assertEquals(1, flow.get("consumerRegionsPlanned").getAsInt());
        assertEquals(1, flow.get("producerRegionsPlanned").getAsInt());
    }

    private static final String CONSUMER_REGION =
            "REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de";
    private static final String PRODUCER_REGION =
            "REGION.d930c3a2-ffc2-35e8-abea-8ff12526d930";
    private static final String OTHER_REGION =
            "REGION.11111111-2222-3333-4444-555555555555";

    private static final String SASL_PORT =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70"
                    + ".req.data-encryption-key-id";
    private static final String BLOCK_KEY_PORT =
            "XCH.1174244c-3118-3892-a173-6cc5895259bf.resp.block-key-id";

    /** One Composer handoff-ledger row whose value reached a term. */
    private static JsonObject bound(String port) {
        return ledgerRow(port, true);
    }

    /** One observed family whose value no lowered expression refers to. */
    private static JsonObject unbound(String port) {
        return ledgerRow(port, false);
    }

    private static JsonObject ledgerRow(String port, boolean bound) {
        JsonObject row = new JsonObject();
        row.addProperty("familyKey", "CBF.ledger" + port.hashCode()
                + (bound ? "b" : "u"));
        row.addProperty("boundaryKind", "RPC_ATTACH");
        row.addProperty("portId", port);
        row.addProperty("valueBound", bound);
        return row;
    }

    /** A composition that published the Composer's handoff ledger. */
    private static JsonObject ledgerManifest(JsonObject... rows) {
        JsonObject manifest = boundaryManifest(CONSUMER_REGION,
                PRODUCER_REGION);
        JsonArray ledger = new JsonArray();
        for (JsonObject row : rows) ledger.add(row);
        manifest.add(ConcolicSmtComposer.WIRE_FLOW_BINDINGS, ledger);
        return manifest;
    }

    private static ClaimPolicy.WireFlowEvidence noFlows() {
        return ClaimPolicy.WireFlowEvidence.none();
    }

    /**
     * One declared flow whose exchange ports the plan bound to a consumer and
     * a producer region, written as the campaign writes them.
     */
    private static ClaimPolicy.WireFlowEvidence flows() throws IOException {
        Path directory = Files.createTempDirectory("claim-flows");
        Path mappings = directory.resolve("communication-mappings.jsonl");
        Files.write(mappings, ("{\"schemaVersion\":1,"
                + "\"kind\":\"WIRE_FLOW\","
                + "\"id\":\"data-encryption-key-id\","
                + "\"transport\":\"HDFS_SASL\","
                + "\"direction\":\"REQUEST\"}\n")
                .getBytes(StandardCharsets.UTF_8));
        Path plan = directory.resolve("concolic_region_plan.jsonl");
        Files.write(plan, ("{\"schemaVersion\":1,"
                + "\"kind\":\"CONCOLIC_REGION_PLAN\",\"regions\":["
                + "{\"regionId\":\"" + CONSUMER_REGION + "\","
                + "\"communicationHandoffs\":[{\"side\":\"IN\","
                + "\"portId\":\"XCH.da84e470-fe7e-3068-b93f-caafeef64a70"
                + ".req.data-encryption-key-id\"}]},"
                + "{\"regionId\":\"" + PRODUCER_REGION + "\","
                + "\"communicationHandoffs\":[{\"side\":\"OUT\","
                + "\"portId\":\"XCH.da84e470-fe7e-3068-b93f-caafeef64a70"
                + ".req.data-encryption-key-id\"}]}]}\n")
                .getBytes(StandardCharsets.UTF_8));
        return ClaimPolicy.WireFlowEvidence.read(mappings.toString(),
                plan.toString());
    }

    /**
     * A complete composition that drew two consumer boundary families, one
     * from each of the two named regions -- the rows the Composer publishes
     * under casePathConditionDependencies.
     */
    private static JsonObject boundaryManifest(String consumer,
                                               String producer) {
        JsonObject manifest = manifest();
        JsonArray dependencies = new JsonArray();
        int ordinal = 0;
        for (String region : Arrays.asList(consumer, producer)) {
            JsonObject arm = new JsonObject();
            arm.addProperty("regionId", region);
            arm.addProperty("occurrenceId",
                    "hdfs-17899/nn0#epoch0/region/" + region + "#1#a1");
            JsonArray arms = new JsonArray();
            arms.add(arm);
            JsonObject family = new JsonObject();
            family.addProperty("kind", "CONSUMER_BOUNDARY_CASE_DEPENDENCY");
            family.addProperty("familyKey", "CBF.fixture" + ordinal++);
            family.addProperty("boundaryKind", "RPC_ATTACH");
            family.add("arms", arms);
            dependencies.add(family);
        }
        manifest.add("casePathConditionDependencies", dependencies);
        return manifest;
    }

    private static JsonObject wireFlow(JsonObject claim, String flow) {
        for (JsonElement element : claim.getAsJsonObject("rootSpace")
                .getAsJsonArray("wireFlows")) {
            JsonObject row = element.getAsJsonObject();
            if (flow.equals(row.get("flow").getAsString())) {
                return row;
            }
        }
        throw new AssertionError("no wire-flow row for " + flow);
    }

    /** A composition the Composer published as complete and candidate-ready. */
    private static JsonObject manifest() {
        return parse("{\"schemaVersion\":2,"
                + "\"kind\":\"CONCOLIC_COMPOSED_SMT\","
                + "\"state\":\"CANDIDATE_READY\","
                + "\"finalStatus\":\"FINAL_READY\","
                + "\"finalStatusRefusals\":[],"
                + "\"symbolicPropagationComplete\":true,"
                + "\"casePathConditionDependencies\":[],"
                + "\"guardedReadModelComplete\":true,"
                + "\"gaps\":[]}");
    }

    /** A REACHABLE report whose single Boolean root decides the target. */
    private static JsonObject reach() {
        return parse("{\"schemaVersion\":4,"
                + "\"kind\":\"BOOLEAN_REACH_CONDITION_REPORT\","
                + "\"state\":\"CANDIDATE_READY\","
                + "\"unsatClosureComplete\":true,"
                + "\"gaps\":[],"
                + "\"reachCondition\":{\"formula\":\"r0\","
                + "\"reachability\":\"REACHABLE\","
                + "\"degeneracyCheck\":\"CONSTRAINED_ROOT_SPACE\"},"
                + "\"valuations\":["
                + "{\"values\":[false],\"status\":\"sat\"},"
                + "{\"values\":[true],\"status\":\"unsat\"}]}");
    }

    private static JsonObject refutation(boolean closed) {
        JsonObject reach = reach();
        reach.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, closed);
        reach.getAsJsonObject("reachCondition")
                .addProperty("reachability", "UNREACHABLE");
        reach.getAsJsonObject("reachCondition")
                .addProperty("degeneracyCheck", "NOT_APPLICABLE_NO_MODEL");
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"unsat\"},"
                        + "{\"values\":[true],\"status\":\"unsat\"}]"));
        return reach;
    }

    private static JsonObject blocker(JsonObject claim, String code) {
        for (JsonElement element : claim.getAsJsonArray("blockers")) {
            JsonObject row = element.getAsJsonObject();
            if (code.equals(row.get("code").getAsString())) {
                return row;
            }
        }
        throw new AssertionError("no blocker named " + code + " in "
                + claim.getAsJsonArray("blockers"));
    }

    private static List<String> codes(JsonObject claim) {
        List<String> codes = new ArrayList<>();
        for (JsonElement element : claim.getAsJsonArray("blockers")) {
            codes.add(element.getAsJsonObject().get("code").getAsString());
        }
        return codes;
    }

    private static List<String> codes(String... expected) {
        List<String> codes = new ArrayList<>();
        for (String code : expected) {
            codes.add(code);
        }
        return codes;
    }

    private static JsonObject parse(String json) {
        return JsonParser.parseString(json).getAsJsonObject();
    }

    private static JsonArray parseArray(String json) {
        return JsonParser.parseString(json).getAsJsonArray();
    }
}
