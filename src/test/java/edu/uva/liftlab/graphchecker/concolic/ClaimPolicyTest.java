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
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
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
                "[{\"values\":[false],\"status\":\"sat\","
                        + "\"witnessMechanisms\":[{\"kind\":\"ROOT_MOVED\","
                        + "\"solverTerm\":\"r0\",\"recordedValue\":\"3\","
                        + "\"witnessValue\":\"9\"}]},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(codes(ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS,
                ClaimPolicy.WITNESS_FREEDOM_UNEXPLAINED), codes(claim));
        assertFalse(claim.getAsJsonObject("rootSpace").get("faultSensitive")
                .getAsBoolean());
        assertEquals(WitnessLegitimacy.UNEXPLAINED_ROOT_MOVE,
                blocker(claim, ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS)
                        .get("subject").getAsString());
    }

    /**
     * The same shape with nothing unexplained in it is a finding.
     *
     * <p>No root flips the target, so the campaign cannot say the fault
     * decided it -- but the witness moved nothing the recording does not
     * allow, and withholding it discards a real statement about the program.
     * The row is reported under its own name instead of blocking.</p>
     */
    @Test
    public void anExplainedWitnessWithNoRootFlipIsAFinding() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS,
                finding(claim, ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS)
                        .get("code").getAsString());
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
     * casePathConditionDependencies rows, and that is the only place they are
     * counted from.
     */
    @Test
    public void boundaryFamiliesAreCountedFromTheRowsTheComposerPublishes() {
        JsonObject manifest = boundaryManifest(CONSUMER_REGION,
                PRODUCER_REGION);

        assertEquals(2, ClaimPolicy.consumerBoundaryFamilies(manifest));
        assertEquals(0, ClaimPolicy.consumerBoundaryFamilies(manifest()));
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
    /**
     * HDFS-17897: the probe reported "not admitted by any window up to
     * 19200000ms" for a comparison the window never refused.  With the clock
     * left unbounded the polarity is still unsat, so the window is not the
     * cause and telling a reader to widen it sends them after the wrong
     * thing; the refusal is named for what it is.
     */
    @Test
    public void aDecisionNoWindowAdmitsIsNotReportedAsAWindowProblem() {
        JsonObject claim = ClaimPolicy.decide(manifest(),
                clockOnlyReach(BooleanReachConditionExtractor
                        .CLOCK_DECISION_REFUSED_WITHOUT_WINDOW), noFlows());

        String detail = blocker(claim,
                ClaimPolicy.FAULT_POLARITY_NOT_WITNESSED)
                .get("detail").getAsString();
        assertTrue(detail.contains(BooleanReachConditionExtractor
                .CLOCK_DECISION_REFUSED_WITHOUT_WINDOW));
        assertTrue(detail.contains("no observed case taking the other"
                + " branch"));
        assertFalse(detail.contains("not admitted by any window"));
    }

    /** A decision the window really does refuse still names the window. */
    @Test
    public void aDecisionTheWindowRefusesStillNamesTheWindow() {
        JsonObject claim = ClaimPolicy.decide(manifest(),
                clockOnlyReach(BooleanReachConditionExtractor
                        .CLOCK_DECISION_OUTSIDE_WINDOW), noFlows());

        String detail = blocker(claim,
                ClaimPolicy.FAULT_POLARITY_NOT_WITNESSED)
                .get("detail").getAsString();
        assertTrue(detail.contains(BooleanReachConditionExtractor
                .CLOCK_DECISION_OUTSIDE_WINDOW));
        assertTrue(detail.contains("not admitted by any window up to"));
    }

    /** A clock-only run whose one clock group the target does not need. */
    private static JsonObject clockOnlyReach(String decisionCode) {
        return parse("{\"schemaVersion\":4,"
                + "\"kind\":\"BOOLEAN_REACH_CONDITION_REPORT\","
                + "\"state\":\"CANDIDATE_READY\","
                + "\"unsatClosureComplete\":true,"
                + "\"gaps\":[],"
                + "\"reachCondition\":{\"formula\":\"true\","
                + "\"reachability\":\"REACHABLE\","
                + "\"degeneracyCheck\":\"CONSTRAINED_ROOT_SPACE\"},"
                + "\"mechanismNecessity\":{\"mechanisms\":[{"
                + "\"mechanism\":\"CLOCK_SKEW\","
                + "\"valuationOrdinal\":0,\"necessary\":false}]},"
                + "\"clockDecisions\":{\"windowMillis\":300000,"
                + "\"probed\":true,\"decisions\":[{"
                + "\"atom\":\"(< expiry manual__MANUAL_dn)\","
                + "\"sites\":[\"hdfs-17897/dn0#epoch0 removeExpiredKeys\"],"
                + "\"decidedByWindow\":true,"
                + "\"requiredWindowMillisAbove\":19200000,"
                + "\"code\":\"" + decisionCode + "\"}]},"
                + "\"valuations\":[{\"values\":[],\"status\":\"sat\"}]}");
    }

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

    /** One reported finding, by code. */
    private static JsonObject finding(JsonObject claim, String code) {
        for (JsonElement element : claim.getAsJsonObject("rootSpace")
                .getAsJsonArray("reportedFindings")) {
            JsonObject row = element.getAsJsonObject();
            if (code.equals(row.get("code").getAsString())) {
                return row;
            }
        }
        throw new AssertionError("no reported finding named " + code + " in "
                + claim.getAsJsonObject("rootSpace")
                        .getAsJsonArray("reportedFindings"));
    }

    /** One valuation's legitimacy row. */
    private static JsonObject witnessFinding(JsonObject claim, int ordinal) {
        return claim.getAsJsonArray(WitnessLegitimacy.FINDINGS)
                .get(ordinal).getAsJsonObject();
    }

    private static JsonObject blockerOrNull(JsonObject claim, String code) {
        for (JsonElement element : claim.getAsJsonArray("blockers")) {
            JsonObject row = element.getAsJsonObject();
            if (code.equals(row.get("code").getAsString())) {
                return row;
            }
        }
        return null;
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

    /**
     * HDFS-17897: the Composer reported the DataNode's {@code allKeys} initial
     * snapshot truncated, stayed FINAL_READY with no refusal, and the witness
     * then read the fatal value out of exactly that carrier's initial arm --
     * "the key was never there" rather than "the key expired". A gap the
     * witness stands on is a blocker whatever the Composer's status says.
     */
    @Test
    public void witnessOnTruncatedInitialStateIsBlocked() {
        JsonObject claim = ClaimPolicy.decide(truncatedManifest(),
                selectionReach(true), noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        JsonObject gap = blocker(claim,
                ClaimPolicy.UNDETERMINED_INITIAL_STATE);
        assertEquals("MAP_STATE/140#-3", gap.get("subject").getAsString());
        assertTrue(gap.get("detail").getAsString()
                .contains("read_selector__initial"));
        assertEquals(1, claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("initialState")
                .getAsJsonArray("onSelectedPath").size());
    }

    /**
     * hdfs-17899-bug3: the witness sat on a reconstructed writer arm while the
     * same read's container carried the truncation gap. A free
     * {@code assoc_has} is a premise available under every arm, so the read is
     * blocked whichever arm this particular model happened to take.
     */
    @Test
    public void truncatedCarrierIsAFindingWhenAWriterArmWasTaken() {
        JsonObject claim = ClaimPolicy.decide(truncatedManifest(),
                selectionReach(false), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals("the untaken initial arm is reported, not blocked",
                ClaimPolicy.UNDETERMINED_INITIAL_STATE,
                finding(claim, ClaimPolicy.UNDETERMINED_INITIAL_STATE)
                        .get("code").getAsString());
        JsonObject initialState = claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("initialState");
        assertEquals(1, initialState.getAsJsonArray("onSelectedPath").size());
        assertEquals(1, initialState.getAsJsonArray("offSelectedPath").size());
        assertEquals(0, initialState
                .getAsJsonArray(ClaimPolicy.FREE_INITIAL_ARMS).size());
        assertTrue(initialState.get("fatalCarrierTruncated").getAsBoolean());
    }

    /** A truncated carrier the fatal read never touches is not this read's. */
    @Test
    public void truncatedCarrierOfAnotherReadIsNotBlocked() {
        JsonObject reach = selectionReach(true);
        JsonArray arms = reach.getAsJsonObject(
                BooleanReachConditionExtractor.FATAL_STATE_SELECTION)
                .getAsJsonArray("arms");
        for (JsonElement arm : arms) {
            arm.getAsJsonObject().addProperty("sessionLocationKey",
                    "MAP_STATE/11#-3");
        }

        JsonObject claim = ClaimPolicy.decide(truncatedManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE, claim.get("claim").getAsString());
        assertEquals(1, claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("initialState")
                .get("truncatedCarrierCount").getAsInt());
    }

    private static JsonObject truncatedManifest() {
        JsonObject manifest = manifest();
        manifest.add("symbolicPropagationGaps", parseArray(
                "[{\"schemaVersion\":2,"
                + "\"reason\":\"INITIAL_CONTAINER_SNAPSHOT_TRUNCATED\","
                + "\"subject\":\"MAP_STATE/140#-3\","
                + "\"detail\":\"no complete initial content snapshot\"}]"));
        return manifest;
    }

    /** A reach report whose fatal read names one initial and one writer arm. */
    private static JsonObject selectionReach(boolean initialArmSelected) {
        JsonObject reach = reach();
        reach.add(BooleanReachConditionExtractor.FATAL_STATE_SELECTION, parse(
                "{\"schemaVersion\":1,"
                + "\"kind\":\"FATAL_READ_STATE_SELECTION\","
                + "\"authority\":\"SOLVER_SELECTED_GUARDED_READ_ARM_V1\","
                + "\"resolved\":true,\"arms\":["
                + "{\"selector\":\"read_selector__initial\","
                + "\"readIdentity\":\"RFC.fatal\","
                + "\"sessionLocationKey\":\"MAP_STATE/140#-3\","
                + "\"locationKey\":\"MAP_STATE/18ffea7d#-3\","
                + "\"writerCaseOwner\":\"INITIAL_SOURCE.a706a1a\","
                + "\"initialState\":true,\"modelled\":true,"
                + "\"selected\":" + initialArmSelected + "},"
                + "{\"selector\":\"read_selector__writer\","
                + "\"readIdentity\":\"RFC.fatal\","
                + "\"sessionLocationKey\":\"MAP_STATE/140#-3\","
                + "\"locationKey\":\"MAP_STATE/18ffea7d#-3\","
                + "\"writerCaseOwner\":\"region:REGION.addKeys\","
                + "\"initialState\":false,\"modelled\":true,"
                + "\"selected\":" + !initialArmSelected + "}]}"));
        return reach;
    }


    /**
     * hdfs-17899-bug3: both polarities of the injected IPC fault marker were
     * satisfiable, and the run was accepted anyway because a perturbation of a
     * wall clock at nn0 was rejected. The marker is the experiment's
     * hypothesis; a clock three hops away is not an answer about it.
     */
    @Test
    public void faultMarkerSatisfiableInBothPolaritiesIsAFinding() {
        JsonObject claim = ClaimPolicy.decide(markerManifest(),
                markerReach(true, "-300000"), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        JsonObject reported = finding(claim,
                ClaimPolicy.FAULT_MARKER_NOT_DETERMINING);
        assertEquals("MANUAL.fault", reported.get("subject").getAsString());
        assertTrue(reported.get("detail").getAsString()
                .contains("this is a finding"));
        assertTrue("the clock at the window bound is inside it",
                witnessFinding(claim, 0).get("narrative").getAsString()
                        .contains("CLOCK_SKEW"));
        assertEquals(WitnessLegitimacy.EXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());
    }

    /**
     * The same run with the clock one millisecond past its window is not.
     *
     * <p>The window is the recording's own statement about what that clock
     * could have read. Outside it the witness is the search's answer rather
     * than the program's, and that is the freedom the ruling still blocks --
     * under its own name, with the marker row now saying which freedom it
     * was.</p>
     */
    @Test
    public void aClockOutsideItsWindowIsUnexplainedFreedom() {
        JsonObject claim = ClaimPolicy.decide(markerManifest(),
                markerReach(true, "-300001"), noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertEquals(WitnessLegitimacy.CLOCK_OUTSIDE_WINDOW,
                blocker(claim, ClaimPolicy.WITNESS_FREEDOM_UNEXPLAINED)
                        .get("subject").getAsString());
        assertTrue(blocker(claim, ClaimPolicy.FAULT_MARKER_NOT_DETERMINING)
                .get("detail").getAsString()
                .contains(WitnessLegitimacy.CLOCK_OUTSIDE_WINDOW));
        assertEquals(WitnessLegitimacy.UNEXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());
    }

    /** A wall clock at a negative time is not a clock reading at all. */
    @Test
    public void anAbsurdClockValueIsUnexplainedFreedom() {
        JsonObject reach = markerReach(true, "-5");
        reach.getAsJsonArray("valuations").get(0).getAsJsonObject()
                .getAsJsonArray("witnessMechanisms").get(0).getAsJsonObject()
                .addProperty("witnessValue", "(- 9223372036854775808)");

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertEquals(WitnessLegitimacy.ABSURD_CLOCK_VALUE,
                blocker(claim, ClaimPolicy.WITNESS_FREEDOM_UNEXPLAINED)
                        .get("subject").getAsString());
    }

    /**
     * The rotation race HDFS-17899 is about, read as the finding it is.
     *
     * <p>The witness in the polarity without the fault names one mechanism:
     * the fatal read took the target datanode's own last {@code addKeys} while
     * the key the wire named is installed a few events later. That is a thing
     * that happens, so the run is accepted and the narrative says so.</p>
     */
    @Test
    public void aRotationRaceOnTheOtherPolarityIsALegitimateFinding() {
        JsonObject reach = markerReach(true, "0");
        reach.getAsJsonArray("valuations").get(0).getAsJsonObject()
                .add("witnessMechanisms", parseArray(
                        "[{\"kind\":\"ROTATION_RACE\","
                        + "\"sessionLocationKey\":\"MAP_STATE/100#-3\","
                        + "\"readEventId\":233,"
                        + "\"laterWriterVersionId\":247}]"));

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(WitnessLegitimacy.EXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());
        assertTrue(witnessFinding(claim, 0).get("narrative").getAsString()
                .contains("ROTATION_RACE at MAP_STATE/100#-3"));
    }

    /**
     * An unenumerated existential root space is freedom nobody wrote down, so
     * it still blocks -- and now the marker row names it as the reason rather
     * than saying nothing explains the other polarity.
     */
    @Test
    public void unenumeratedRootsKeepTheMarkerRowBlockingAndNameTheFreedom() {
        JsonObject reach = markerReach(true, "-300000");
        reach.getAsJsonObject("reachCondition").addProperty("degeneracyCheck",
                "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:14");

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertEquals(codes(ClaimPolicy.UNDECIDED_ROOT_SPACE,
                ClaimPolicy.FAULT_MARKER_NOT_DETERMINING), codes(claim));
        assertTrue(blocker(claim, ClaimPolicy.FAULT_MARKER_NOT_DETERMINING)
                .get("detail").getAsString()
                .contains(WitnessLegitimacy.UNENUMERATED_EXISTENTIAL_ROOT));
        assertEquals("the freedom is named once, under its own blocker",
                "", blockerOrNull(claim,
                        ClaimPolicy.WITNESS_FREEDOM_UNEXPLAINED) == null
                        ? "" : "WITNESS_FREEDOM_UNEXPLAINED");
    }

    /** The buggy polarity is the one an accepted claim has to rest on. */
    @Test
    public void aFaultPolarityWithNoWitnessIsNotAnAcceptedClaim() {
        JsonObject reach = markerReach(true, "-300000");
        // The marker records false, so true is the buggy polarity.
        reach.getAsJsonArray("valuations").get(1).getAsJsonObject()
                .addProperty("status", "unsat");

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertEquals("MANUAL.fault",
                blocker(claim, ClaimPolicy.FAULT_POLARITY_NOT_WITNESSED)
                        .get("subject").getAsString());
    }

    /** The marker deciding the verdict is what an accepted claim rests on. */
    @Test
    public void faultMarkerThatFlipsTheVerdictIsAccepted() {
        JsonObject reach = markerReach(true, "-300000");
        reach.getAsJsonArray("valuations").get(0).getAsJsonObject()
                .addProperty("status", "unsat");

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertTrue(markerRow(claim).get("polarityDecides").getAsBoolean());
    }

    /**
     * Interior clock skew on the polarity without the fault is a finding.
     *
     * <p>The earlier reading asked the solver to show the polarity died with
     * the mechanism's roots pinned back, and called a clock that survived that
     * "decoration". A clock inside its recorded window is drift that happened;
     * whether the target could also have been reached some other way is a
     * different question and not a reason to discard this witness. The
     * necessity probe stays in the report as evidence a reader may weigh, and
     * decides nothing.</p>
     */
    @Test
    public void interiorClockSkewOnTheOtherPolarityIsALegitimateFinding() {
        JsonObject claim = ClaimPolicy.decide(markerManifest(),
                markerReach(true, "245021"), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(1, markerRow(claim)
                .getAsJsonArray("otherPolarityMechanisms").size());
        assertEquals("no necessity row is needed to accept the run",
                0, markerRow(claim).getAsJsonArray("necessaryMechanisms")
                        .size());
        assertEquals(WitnessLegitimacy.EXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());
    }

    /** The necessity probe is still published, for a reader to weigh. */
    @Test
    public void mechanismNecessityStaysInTheReportAsEvidence() {
        JsonObject reach = markerReach(true, "245021");
        reach.add(BooleanReachConditionExtractor.MECHANISM_NECESSITY, parse(
                "{\"schemaVersion\":1,"
                + "\"kind\":\"WITNESS_MECHANISM_NECESSITY\","
                + "\"authority\":\"RECORDED_ROOT_PIN_V1\","
                + "\"mechanisms\":[{\"marker\":\"manual__fault\","
                + "\"polarity\":false,\"mechanism\":\"CLOCK_SKEW\","
                + "\"pinnedRoots\":4,\"status\":\"unsat\","
                + "\"necessary\":true}]}"));

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(1, markerRow(claim)
                .getAsJsonArray("necessaryMechanisms").size());
    }

    /** The verdict must say which root the probe actually perturbed. */
    @Test
    public void probedRootNamesTheRejectedRoot() {
        JsonObject reach = reach();
        reach.add("existentialRootProbe", parse(
                "{\"authority\":\"SOLVER_WITNESS_NEIGHBOR_PERTURBATION_V1\","
                + "\"constrainsRootSpace\":true,\"perturbations\":["
                + "{\"sourceIdentity\":\"MANUAL.clock\","
                + "\"portId\":\"REGION.nn0.in.now\","
                + "\"witnessValue\":\"5\",\"perturbedValue\":\"4\","
                + "\"status\":\"skipped\","
                + "\"rejectedBy\":\"WINDOW_BOUNDARY\"},"
                + "{\"sourceIdentity\":\"MANUAL.other\","
                + "\"portId\":\"REGION.nn0.in.later\","
                + "\"witnessValue\":\"9\",\"perturbedValue\":\"8\","
                + "\"status\":\"unsat\"}]}"));

        JsonObject probed = ClaimPolicy.decide(manifest(), reach, noFlows())
                .getAsJsonObject("rootSpace").getAsJsonObject("probedRoot");

        assertTrue(probed.get("rejected").getAsBoolean());
        assertEquals("MANUAL.other", probed.get("sourceIdentity").getAsString());
        assertEquals("the window-boundary row is not a solved perturbation",
                1, probed.get("solvedPerturbations").getAsInt());
    }

    // ---- one marker, and several -----------------------------------------

    /**
     * One marker: the buggy polarity is the valuation that moves it, and the
     * finding names which marker moved and where.
     */
    @Test
    public void oneFlippedMarkerNamesItselfInTheWitnessFinding() {
        JsonObject claim = ClaimPolicy.decide(markerManifest(),
                markerReach(true, "-300000"), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        JsonObject flippedRow = witnessFinding(claim, 1);
        assertEquals(1, flippedRow.get("flippedMarkerCount").getAsInt());
        assertEquals("MANUAL.fault", flippedRow
                .getAsJsonArray("flippedMarkers").get(0).getAsJsonObject()
                .get("sourceIdentity").getAsString());
        assertTrue(flippedRow.get("narrative").getAsString()
                .startsWith("flips MANUAL.fault"));
        assertTrue("the recorded world is the other polarity",
                witnessFinding(claim, 0).get("allRecorded").getAsBoolean());
    }

    /**
     * hdfs-17899-bug1: two markers on the Balancer, one of which is the bug.
     *
     * <p>Occurrence #1 is the constructor's {@code updateBlockKeys}; failing
     * it aborts the test, so every valuation that flips it is unsatisfiable.
     * Occurrence #5 is the {@code BlockKeyUpdater} thread's periodic
     * {@code getBlockKeys}, whose catch at {@code KeyManager.java:168-170} is
     * the path production tolerates -- that is the mechanism, and the run
     * rests on it. Demanding a witness in "the" buggy polarity of every
     * declared marker would refuse this run for the marker that is not the
     * bug.</p>
     */
    @Test
    public void twoMarkersAcceptTheOneThatIsTheMechanism() {
        JsonObject claim = ClaimPolicy.decide(twoMarkerManifest(),
                twoMarkerReach("unsat", "sat", "unsat", "unsat"), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(0, claim.getAsJsonArray("blockers").size());

        // The accepted witness moved the updater thread's marker and only it.
        JsonObject accepted = witnessFinding(claim, 1);
        assertEquals("sat", accepted.get("status").getAsString());
        assertEquals(WitnessLegitimacy.EXPLAINED,
                accepted.get("verdict").getAsString());
        assertEquals(1, accepted.get("flippedMarkerCount").getAsInt());
        JsonObject moved = accepted.getAsJsonArray("flippedMarkers").get(0)
                .getAsJsonObject();
        assertEquals("MANUAL.updater", moved.get("sourceIdentity")
                .getAsString());
        assertEquals(UPDATER_OCCURRENCE, moved.get("occurrenceId")
                .getAsString());
        assertEquals(UPDATER_SITE, moved.get("siteId").getAsString());

        // The constructor's marker is reported as not being the mechanism.
        JsonObject notMechanism = findingWithSubject(claim,
                ClaimPolicy.NOT_A_MECHANISM, "MANUAL.constructor");
        assertTrue(notMechanism.get("detail").getAsString()
                .contains(CONSTRUCTOR_OCCURRENCE));
        assertTrue(notMechanism.get("detail").getAsString()
                .contains("is not the mechanism"));
        assertNull("the marker that is the mechanism is not reported",
                findingOrNull(claim, ClaimPolicy.NOT_A_MECHANISM,
                        "MANUAL.updater"));
    }

    /**
     * With no flipped valuation satisfiable, a planted marker has no buggy
     * polarity, and the run is withheld.
     *
     * <p>What the markers <em>are</em> shown to do is published all the
     * same: the recorded world is satisfiable and every flip of it is
     * refuted, so each marker decides the target at the value it recorded.
     * That is the opposite of {@link ClaimPolicy#NOT_A_MECHANISM}, which is
     * a marker no polarity of which reaches the target, and reporting it
     * here said the run rested on neither marker while the recorded
     * valuation was the satisfying one.</p>
     */
    @Test
    public void noFlippedMarkerWitnessIsNotAnAcceptedClaim() {
        JsonObject claim = ClaimPolicy.decide(twoMarkerManifest(),
                twoMarkerReach("sat", "unsat", "unsat", "unsat"), noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        JsonObject gap = blocker(claim,
                ClaimPolicy.FAULT_POLARITY_NOT_WITNESSED);
        assertEquals("MANUAL.updater,MANUAL.constructor",
                gap.get("subject").getAsString());
        assertTrue(gap.get("detail").getAsString()
                .contains("over 2 declared marker(s)"));
        JsonObject markers = claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("faultMarkers");
        for (String identity : new String[] {"MANUAL.updater",
                "MANUAL.constructor"}) {
            JsonObject row = markerByIdentity(markers, identity);
            assertTrue(identity + " decides the target",
                    row.get("polarityDecides").getAsBoolean());
            assertTrue(identity + " decides it at its recorded value",
                    row.get("reachesAtRecordedValue").getAsBoolean());
            assertNull("a marker that decides is not NOT_A_MECHANISM",
                    findingOrNull(claim, ClaimPolicy.NOT_A_MECHANISM,
                            identity));
        }
    }

    /**
     * An undecided flipped valuation is not a refutation of its marker.
     *
     * <p>hdfs-17899-bug1's recorded corpus times out on one of its four rows.
     * Calling the marker "not the mechanism" on the strength of the rows that
     * did come back would turn a solver budget into a statement about the
     * program.</p>
     */
    @Test
    public void anUndecidedFlippedValuationLeavesTheQuestionOpen() {
        JsonObject claim = ClaimPolicy.decide(twoMarkerManifest(),
                twoMarkerReach("unsat", "timeout", "unsat", "unsat"),
                noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertTrue(codes(claim).contains(
                ClaimPolicy.SOLVER_UNDECIDED_VALUATIONS));
        assertNull("one flipped row never came back, so nothing is decided"
                        + " about this marker",
                findingOrNull(claim, ClaimPolicy.NOT_A_MECHANISM,
                        "MANUAL.updater"));
        assertNotNull("the other marker's flipped rows all came back unsat",
                findingOrNull(claim, ClaimPolicy.NOT_A_MECHANISM,
                        "MANUAL.constructor"));
    }

    /**
     * "The other polarity" is the one valuation that leaves every marker as
     * recorded, not the first row that happens to assign one marker its
     * recorded value.
     *
     * <p>With two markers the older reading answered about whichever sibling
     * that row also moved: for the constructor's marker it picked
     * {@code [flipped, recorded]}, which is a statement about the updater
     * thread.</p>
     */
    @Test
    public void theOtherPolarityIsTheValuationThatMovesNoMarker() {
        JsonObject claim = ClaimPolicy.decide(twoMarkerManifest(),
                twoMarkerReach("unsat", "sat", "unsat", "unsat"), noFlows());

        JsonObject markers = claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("faultMarkers");
        assertFalse("the all-recorded valuation is unsat here",
                markers.get("allRecordedSatisfiable").getAsBoolean());
        for (JsonElement element : markers.getAsJsonArray("markers")) {
            JsonObject row = element.getAsJsonObject();
            assertFalse("every marker answers about the same recorded world",
                    row.get("recordedPolaritySatisfiable").getAsBoolean());
            assertTrue(row.get("recordedPolarityStated").getAsBoolean());
        }
        assertTrue("the updater's flip is what reaches the target",
                markerByIdentity(markers, "MANUAL.updater")
                        .get("polarityDecides").getAsBoolean());
        assertFalse(markerByIdentity(markers, "MANUAL.constructor")
                .get("polarityDecides").getAsBoolean());
    }

    private static final String UPDATER_OCCURRENCE =
            "hdfs-17899/balancer#epoch0/region/REGION.763d087e#5";
    private static final String CONSTRUCTOR_OCCURRENCE =
            "hdfs-17899/balancer#epoch0/region/REGION.763d087e#1";
    private static final String UPDATER_SITE =
            "<org.apache.hadoop.hdfs.server.balancer.KeyManager:"
            + " void run()>#u12";
    private static final String CONSTRUCTOR_SITE =
            "<org.apache.hadoop.hdfs.server.balancer.KeyManager:"
            + " void <init>(...)>#u4";

    /** Two markers, both recording false, both with a named call site. */
    private static JsonObject twoMarkerManifest() {
        JsonObject manifest = manifest();
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES, parseArray(
                "[{\"solverTerm\":\"manual__updater\","
                + "\"recordedValue\":\"false\",\"wallClock\":false,"
                + "\"siteId\":\"" + UPDATER_SITE + "\"},"
                + "{\"solverTerm\":\"manual__constructor\","
                + "\"recordedValue\":\"false\",\"wallClock\":false,"
                + "\"siteId\":\"" + CONSTRUCTOR_SITE + "\"}]"));
        manifest.add(ClockRootPhysics.MANIFEST_FIELD, parse(
                "{\"schemaVersion\":1,\"kind\":\"CLOCK_ROOT_PHYSICS\","
                + "\"clockSkewMillis\":300000,\"clockReads\":[]}"));
        return manifest;
    }

    /**
     * Four valuations over two markers, in the order the extractor enumerates
     * them: [f,f] the recorded world, [t,f] the updater's marker alone,
     * [f,t] the constructor's alone, [t,t] both.
     */
    private static JsonObject twoMarkerReach(String recorded,
                                             String updaterOnly,
                                             String constructorOnly,
                                             String both) {
        JsonObject reach = reach();
        reach.add("roots", parse(
                "{\"booleanInputs\":["
                + "{\"inputKind\":\"REGION_SYMBOLIC_INPUT\","
                + "\"sourceIdentity\":\"MANUAL.updater\","
                + "\"portId\":\"REGION.763d087e.in.getBlockKeys\","
                + "\"occurrenceId\":\"" + UPDATER_OCCURRENCE + "\","
                + "\"javaTypeDescriptor\":\"Z\","
                + "\"solverTerm\":\"manual__updater\"},"
                + "{\"inputKind\":\"REGION_SYMBOLIC_INPUT\","
                + "\"sourceIdentity\":\"MANUAL.constructor\","
                + "\"portId\":\"REGION.763d087e.in.updateBlockKeys\","
                + "\"occurrenceId\":\"" + CONSTRUCTOR_OCCURRENCE + "\","
                + "\"javaTypeDescriptor\":\"Z\","
                + "\"solverTerm\":\"manual__constructor\"}],"
                + "\"existentialInputs\":[]}"));
        reach.add("valuations", parseArray(
                "[{\"values\":[false,false],\"status\":\"" + recorded
                + "\"},"
                + "{\"values\":[true,false],\"status\":\"" + updaterOnly
                + "\",\"witnessMechanisms\":[{\"kind\":"
                + "\"MARKER_FLIPPED\",\"solverTerm\":\"manual__updater\","
                + "\"siteId\":\"" + UPDATER_SITE + "\","
                + "\"recordedValue\":\"false\","
                + "\"witnessValue\":\"true\"}]},"
                + "{\"values\":[false,true],\"status\":\""
                + constructorOnly + "\"},"
                + "{\"values\":[true,true],\"status\":\"" + both
                + "\"}]"));
        return reach;
    }

    private static JsonObject markerByIdentity(JsonObject markers,
                                               String identity) {
        for (JsonElement element : markers.getAsJsonArray("markers")) {
            JsonObject row = element.getAsJsonObject();
            if (identity.equals(row.get("sourceIdentity").getAsString())) {
                return row;
            }
        }
        throw new AssertionError("no marker row for " + identity);
    }

    private static JsonObject findingOrNull(JsonObject claim, String code,
                                            String subject) {
        for (JsonElement element : claim.getAsJsonObject("rootSpace")
                .getAsJsonArray("reportedFindings")) {
            JsonObject row = element.getAsJsonObject();
            if (code.equals(row.get("code").getAsString())
                    && subject.equals(row.get("subject").getAsString())) {
                return row;
            }
        }
        return null;
    }

    private static JsonObject findingWithSubject(JsonObject claim, String code,
                                                 String subject) {
        JsonObject row = findingOrNull(claim, code, subject);
        if (row == null) {
            throw new AssertionError("no reported finding " + code + "["
                    + subject + "] in " + claim.getAsJsonObject("rootSpace")
                            .getAsJsonArray("reportedFindings"));
        }
        return row;
    }

    /**
     * Where the manifest names no recorded value, the plan that produced it
     * does.
     *
     * <p>hdfs-17899-bug1's recorded manifest carries an empty
     * {@code recordedRootValues} while its runtime plan states
     * {@code primitiveValue: "false"} for both marker ports, with the call
     * site. Defaulting the polarity to {@code true} there inverts every
     * statement the gate makes about which marker is the mechanism -- the
     * recorded world is read as the fault and the fault as the recorded
     * world -- so the plan is consulted before the default is taken.</p>
     */
    @Test
    public void thePlanSuppliesARecordedValueTheManifestOmits()
            throws IOException {
        JsonObject manifest = markerManifest();
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES,
                new JsonArray());

        JsonObject claim = ClaimPolicy.decide(manifest,
                markerReach(true, "-300000"), planWith("false"));

        JsonObject marker = markerRow(claim);
        assertFalse(marker.get("recordedPolarity").getAsBoolean());
        assertTrue("the plan stated it, so it is not a default",
                marker.get("recordedPolarityStated").getAsBoolean());
        assertEquals(PLANNED_SITE, marker.get("siteId").getAsString());
        assertTrue("valuation 1 flips the marker off the recorded false",
                witnessFinding(claim, 1).get("flippedMarkerCount")
                        .getAsInt() == 1);
        assertTrue(witnessFinding(claim, 0).get("allRecorded")
                .getAsBoolean());
    }

    /** A manifest that does state one is the authority; the plan is backup. */
    @Test
    public void theManifestsRecordedValueWinsOverThePlans() throws IOException {
        JsonObject claim = ClaimPolicy.decide(markerManifest(),
                markerReach(true, "-300000"), planWith("true"));

        assertFalse("the manifest says false",
                markerRow(claim).get("recordedPolarity").getAsBoolean());
    }

    /** With neither stating one, the polarity reads as true and says so. */
    @Test
    public void anUnstatedRecordedValueIsMarkedAsUnstated() {
        JsonObject manifest = markerManifest();
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES,
                new JsonArray());

        JsonObject claim = ClaimPolicy.decide(manifest,
                markerReach(true, "-300000"), noFlows());

        JsonObject marker = markerRow(claim);
        assertTrue(marker.get("recordedPolarity").getAsBoolean());
        assertFalse(marker.get("recordedPolarityStated").getAsBoolean());
    }

    // ---------------------------------------------------------------
    // HDFS-17960: one configured source, recorded false, reproduced.
    // ---------------------------------------------------------------

    private static final String ORDERED_FIELD = "<org.apache.hadoop.hdfs"
            + ".server.namenode.snapshot.SnapshotManager:"
            + " boolean snapshotDeletionOrdered>";
    private static final String ORDERED_SOURCE =
            "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED";
    private static final String ORDERED_OCCURRENCE = "hdfs-17960/nn0#epoch1"
            + "/region/REGION.9492ec77#1#a1";
    private static final String ORDERED_TERM = "sym__ordered__1";

    /**
     * A configured source's recorded value reaches the gate.
     *
     * <p>It has no port, so the plan's {@code symbolize} fallback is keyed by
     * something a configured root never carries and can never fire for one;
     * the value arrives on the materialization row the Composer publishes
     * instead. Without it HDFS-17960's root defaults to {@code true} while
     * the epoch-1 NameNode recorded {@code false}.</p>
     */
    @Test
    public void aConfiguredSourceStatesItsRecordedValue() {
        JsonObject claim = ClaimPolicy.decide(orderedManifest("false"),
                orderedReach("sat", "unsat"), noFlows());

        JsonObject marker = markerRow(claim);
        assertFalse("the epoch-1 NameNode recorded false",
                marker.get("recordedPolarity").getAsBoolean());
        assertTrue("and the manifest states it",
                marker.get("recordedPolarityStated").getAsBoolean());
        assertEquals("a configured root is named by its field, not its term",
                ORDERED_SOURCE, marker.get("sourceIdentity").getAsString());
        assertEquals(ORDERED_FIELD, marker.get("siteId").getAsString());
        assertEquals(ORDERED_OCCURRENCE,
                marker.get("occurrenceId").getAsString());
    }

    /** The recorded-root ledger stays the authority where it states one. */
    @Test
    public void theRecordedRootLedgerOutranksTheMaterializationRow() {
        JsonObject manifest = orderedManifest("false");
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES, parseArray(
                "[{\"solverTerm\":\"" + ORDERED_TERM + "\","
                + "\"recordedValue\":\"true\",\"wallClock\":false,"
                + "\"siteId\":\"" + ORDERED_FIELD + "\"}]"));

        assertTrue("the ledger says true",
                markerRow(ClaimPolicy.decide(manifest,
                        orderedReach("sat", "unsat"), noFlows()))
                        .get("recordedPolarity").getAsBoolean());
    }

    /**
     * A witness at the recorded value is the finding, not a missing flip.
     *
     * <p>HDFS-17960 injects nothing: its only root is the program's own
     * configuration field, the recording already threw at the target, and the
     * satisfying valuation is the recorded {@code false}. Demanding a flip of
     * it refused the run for reproducing its own recording, and the defaulted
     * polarity hid that by reporting the reproduction as a flip.</p>
     */
    @Test
    public void aConfiguredSourceWitnessAtItsRecordedValueIsAccepted() {
        JsonObject claim = ClaimPolicy.decide(orderedManifest("false"),
                orderedReach("sat", "unsat"), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(0, claim.getAsJsonArray("blockers").size());
        JsonObject rootSpace = claim.getAsJsonObject("rootSpace");
        assertEquals(ClaimPolicy.RECORDED_ROOT_VALUES_REPRODUCED,
                rootSpace.get("acceptedWitnessKind").getAsString());
        assertEquals("nothing was planted here",
                0, rootSpace.get("plantedMarkers").getAsInt());
        assertEquals(0, rootSpace.get("acceptedValuationOrdinal").getAsInt());

        JsonObject accepted = witnessFinding(claim, 0);
        assertEquals(0, accepted.get("flippedMarkerCount").getAsInt());
        assertTrue(accepted.get("allRecorded").getAsBoolean());
        assertTrue(accepted.get("narrative").getAsString(),
                accepted.get("narrative").getAsString().contains(
                        "every declared root at its recorded value ("
                        + ORDERED_SOURCE + " = false)"));
        JsonObject marker = markerRow(claim);
        assertTrue(marker.get("polarityDecides").getAsBoolean());
        assertTrue(marker.get("reachesAtRecordedValue").getAsBoolean());
    }

    /** The reason names the valuation, the roots and the reproduction. */
    @Test
    public void theClaimReasonNamesTheReproducedRecordedCase() {
        String reason = ClaimPolicy.decide(orderedManifest("false"),
                orderedReach("sat", "unsat"), noFlows())
                .get("claimReason").getAsString();

        assertTrue(reason, reason.startsWith("valuation 0 satisfies the"
                + " target predicate inside the recorded model"));
        assertTrue(reason, reason.contains("with every declared root at the"
                + " value the recording had (" + ORDERED_SOURCE + " ("
                + ORDERED_FIELD + ") = false)"));
        assertTrue(reason, reason.contains("reproduces the recorded case"
                + " rather than a counterfactual"));
        assertTrue(reason, reason.contains("no named mechanism was needed"));
        assertTrue(reason, reason.contains(ORDERED_SOURCE
                + " reaches the target at its recorded value and at no"
                + " other"));
        assertFalse("nothing flipped, so nothing may say one did",
                reason.contains("flips"));
    }

    /** With nothing stating a recorded value, the reason says it guessed. */
    @Test
    public void theClaimReasonSaysWhenAPolarityWasNotRecorded() {
        JsonObject claim = ClaimPolicy.decide(orderedManifest(""),
                orderedReach("sat", "unsat"), noFlows());

        JsonObject marker = markerRow(claim);
        assertTrue("defaulted, because nothing recorded it",
                marker.get("recordedPolarity").getAsBoolean());
        assertFalse(marker.get("recordedPolarityStated").getAsBoolean());
        String reason = claim.get("claimReason").getAsString();
        assertTrue(reason, reason.contains(
                "[recorded value unstated, assumed true]"));
        String narrative = witnessFinding(claim, 0).get("narrative")
                .getAsString();
        assertTrue(narrative, narrative.contains(
                "off an unstated recorded value (assumed true)"));
        assertEquals("moved against a default is neither of the other two",
                ClaimPolicy.UNPLANTED_ROOT_MOVED,
                claim.getAsJsonObject("rootSpace")
                        .get("acceptedWitnessKind").getAsString());
    }

    /** The reason for a flipped planted marker names the flip and why. */
    @Test
    public void theClaimReasonNamesTheFlippedPlantedMarker() {
        JsonObject reach = markerReach(true, "-300000");
        reach.getAsJsonArray("valuations").get(0).getAsJsonObject()
                .addProperty("status", "unsat");

        JsonObject claim = ClaimPolicy.decide(markerManifest(), reach,
                noFlows());
        String reason = claim.get("claimReason").getAsString();

        assertEquals(ClaimPolicy.FLIPPED_PLANTED_MARKER,
                claim.getAsJsonObject("rootSpace")
                        .get("acceptedWitnessKind").getAsString());
        assertTrue(reason, reason.startsWith("valuation 1 satisfies"));
        assertTrue(reason, reason.contains(
                "moves 1 declared root(s) off what they recorded:"
                + " MANUAL.fault"));
        assertTrue(reason, reason.contains("explained by MARKER_FLIPPED"));
        assertTrue(reason, reason.contains(
                "the root space decides the target"));
        assertTrue(reason, reason.contains("MANUAL.fault reaches the target"
                + " only when moved off what it recorded"));
    }

    /**
     * One configured Boolean source, materialized with a recorded value.
     *
     * @param recordedValue what the field held, or "" to state none
     */
    private static JsonObject orderedManifest(String recordedValue) {
        JsonObject manifest = manifest();
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES,
                new JsonArray());
        manifest.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, parseArray(
                "[{\"kind\":\"" + ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_KIND + "\","
                + "\"sourceKey\":\"hdfs-17960/nn0#epoch1\","
                + "\"sourceId\":\"" + ORDERED_SOURCE + "\","
                + "\"sourceOccurrenceId\":\"" + ORDERED_OCCURRENCE + "\","
                + "\"fieldSignature\":\"" + ORDERED_FIELD + "\","
                + "\"javaTypeDescriptor\":\"Z\",\"sort\":\"BOOL\","
                + (recordedValue.isEmpty() ? ""
                        : "\"" + ConcolicSmtComposer.RECORDED_SOURCE_VALUE
                        + "\":\"" + recordedValue + "\",")
                + "\"solverTerm\":\"" + ORDERED_TERM + "\"}]"));
        manifest.add(ClockRootPhysics.MANIFEST_FIELD, parse(
                "{\"schemaVersion\":1,\"kind\":\"CLOCK_ROOT_PHYSICS\","
                + "\"clockSkewMillis\":300000,\"clockReads\":[]}"));
        return manifest;
    }

    /** The two polarities of that source, in enumeration order. */
    private static JsonObject orderedReach(String atFalse, String atTrue) {
        JsonObject reach = reach();
        reach.add("roots", parse(
                "{\"booleanInputs\":["
                + "{\"inputKind\":\"CONFIGURED_SOURCE_FIELD\","
                + "\"sourceKey\":\"hdfs-17960/nn0#epoch1\","
                + "\"sourceId\":\"" + ORDERED_SOURCE + "\","
                + "\"sourceOccurrenceId\":\"" + ORDERED_OCCURRENCE + "\","
                + "\"fieldSignature\":\"" + ORDERED_FIELD + "\","
                + "\"javaTypeDescriptor\":\"Z\","
                + "\"solverTerm\":\"" + ORDERED_TERM + "\"}],"
                + "\"existentialInputs\":[]}"));
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"" + atFalse + "\"},"
                + "{\"values\":[true],\"status\":\"" + atTrue + "\"}]"));
        return reach;
    }

    private static final String PLANNED_SITE =
            "<org.apache.hadoop.ipc.Client$Connection:"
            + " void sendRpcRequest(org.apache.hadoop.ipc.Client$Call)>#u17";

    /** A runtime plan that symbolizes the marker port at a recorded value. */
    private static ClaimPolicy.WireFlowEvidence planWith(String recorded)
            throws IOException {
        Path directory = Files.createTempDirectory("claim-plan-roots");
        Path plan = directory.resolve("concolic_region_plan.jsonl");
        Files.write(plan, ("{\"regionId\":\"REGION.x\","
                + "\"closureGoals\":[{\"symbolize\":["
                + "{\"portId\":\"REGION.sendRpcRequest.in.fault\","
                + "\"primitiveValue\":\"" + recorded + "\","
                + "\"javaType\":\"boolean\","
                + "\"siteId\":\"" + PLANNED_SITE + "\","
                + "\"declaredCallee\":\"<edu.uva.liftlab.graphchecker"
                + ".'annotation'.Debug: boolean makeSymbolicBoolean"
                + "(java.lang.String)>\"}]}]}\n")
                .getBytes(StandardCharsets.UTF_8));
        return ClaimPolicy.WireFlowEvidence.read("", plan.toString());
    }

    private static JsonObject markerRow(JsonObject claim) {
        return claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("faultMarkers")
                .getAsJsonArray("markers").get(0).getAsJsonObject();
    }

    private static JsonObject markerManifest() {
        JsonObject manifest = manifest();
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES, parseArray(
                "[{\"solverTerm\":\"manual__fault\","
                + "\"recordedValue\":\"false\",\"wallClock\":false}]"));
        manifest.add(ClockRootPhysics.MANIFEST_FIELD, parse(
                "{\"schemaVersion\":1,\"kind\":\"CLOCK_ROOT_PHYSICS\","
                + "\"clockSkewMillis\":300000,\"clockReads\":[]}"));
        return manifest;
    }

    /**
     * One declared marker, both polarities satisfiable, and the polarity that
     * has no fault explained only by a clock moved by {@code skewMillis}.
     */
    private static JsonObject markerReach(boolean bothSat, String skewMillis) {
        JsonObject reach = reach();
        // bug3 was accepted with both polarities sat because a perturbation of
        // an unrelated clock root was rejected; without that the older
        // TARGET_UNCONSTRAINED_BY_ROOTS blocker fires and the marker rule is
        // never the thing under test.
        reach.add("existentialRootProbe", parse(
                "{\"authority\":\"SOLVER_WITNESS_NEIGHBOR_PERTURBATION_V1\","
                + "\"constrainsRootSpace\":true,\"perturbations\":["
                + "{\"sourceIdentity\":\"MANUAL.clock\","
                + "\"portId\":\"REGION.nn0.in.now\","
                + "\"witnessValue\":\"9\",\"perturbedValue\":\"8\","
                + "\"status\":\"unsat\"}]}"));
        reach.add("roots", parse(
                "{\"booleanInputs\":[{\"inputKind\":\"REGION_SYMBOLIC_INPUT\","
                + "\"sourceIdentity\":\"MANUAL.fault\","
                + "\"portId\":\"REGION.sendRpcRequest.in.fault\","
                + "\"occurrenceId\":\"hdfs/dn0#epoch0/region/REGION.x#1\","
                + "\"javaTypeDescriptor\":\"Z\","
                + "\"solverTerm\":\"manual__fault\"}],"
                + "\"existentialInputs\":[]}"));
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\""
                + (bothSat ? "sat" : "unsat") + "\","
                + "\"witnessMechanisms\":[{\"kind\":\"CLOCK_SKEW\","
                + "\"skewMillis\":" + skewMillis + ","
                + "\"siteId\":\"BlockTokenSecretManager.updateKeys()#u28\","
                + "\"sourceKey\":\"hdfs/nn0#epoch0\"}]},"
                + "{\"values\":[true],\"status\":\"sat\","
                + "\"witnessMechanisms\":[{\"kind\":\"MARKER_FLIPPED\","
                + "\"siteId\":\"Client$Connection.sendRpcRequest#u17\"}]}]"));
        return reach;
    }


    private static final String DEK_FIELD =
            "org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey"
            + "#keyId";

    /** The wire's own family reached a term: the direct route. */
    @Test
    public void aFlowIsRealizedByItsPortFamily() throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                flowManifest(true, false), reach(), fieldFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE, claim.get("claim").getAsString());
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertTrue(flow.get("realized").getAsBoolean());
        assertEquals("PORT_FAMILY", flow.get("realizedBy").getAsString());
    }

    /**
     * HDFS-17897: the value leaves the wire on arrival. The consumer assigns
     * it to a field and the DataNode reads that field, so the term the wire's
     * value reaches is the guarded read, and asking for the port's own family
     * asks for a term nobody was going to build.
     */
    @Test
    public void aFlowIsRealizedByTheFieldItsConsumerAssigns()
            throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                flowManifest(false, true), reach(), fieldFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE, claim.get("claim").getAsString());
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertTrue(flow.get("realized").getAsBoolean());
        assertEquals("CONSUMER_FIELD_READ",
                flow.get("realizedBy").getAsString());
        assertEquals(DEK_FIELD, flow.get("consumerField").getAsString());
    }

    /** Neither route: the wire's value constrains nothing, and it is named. */
    @Test
    public void aFlowWithNeitherRouteStaysUnrealized() throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                flowManifest(false, false), reach(), fieldFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertEquals("data-encryption-key-id",
                blocker(claim, ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED)
                        .get("subject").getAsString());
        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertFalse(flow.get("realized").getAsBoolean());
        assertEquals("", flow.get("realizedBy").getAsString());
    }

    /** A read of some other field is not this flow's value. */
    @Test
    public void anotherFieldsReadDoesNotRealizeTheFlow() throws IOException {
        JsonObject manifest = flowManifest(false, false);
        manifest.getAsJsonObject("guardedReadModel").add("reads",
                readsOf("org.apache.hadoop.hdfs.server.datanode.DataNode"
                        + "#unrelated"));

        JsonObject claim = ClaimPolicy.decide(manifest, reach(),
                fieldFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
    }

    /** The port route is the stronger statement, so it is reported first. */
    @Test
    public void bothRoutesReportThePortFamily() throws IOException {
        JsonObject claim = ClaimPolicy.decide(
                flowManifest(true, true), reach(), fieldFlows());

        assertEquals("PORT_FAMILY", wireFlow(claim, "data-encryption-key-id")
                .get("realizedBy").getAsString());
    }

    /**
     * HDFS-17897: the same field is read on both sides of a wire, so a read
     * anywhere is not necessarily this flow's value.  The
     * NameNode-to-client hop counted as realized on the strength of a
     * {@code DataEncryptionKey#keyId} read that only ever happened on the
     * DataNode, which that hop never fed.  The route stands -- a downstream
     * read is how a value that left the wire is carried -- and the node
     * mismatch is reported.
     */
    @Test
    public void aFieldReadOffTheReceiverNodeIsReported() throws IOException {
        JsonObject manifest = flowManifest(false, true);
        manifest.getAsJsonObject("guardedReadModel").add("reads",
                readsOn(DEK_FIELD, "hdfs-17897/dn0#epoch0"));

        JsonObject claim = ClaimPolicy.decide(manifest, reach(),
                fieldFlows());

        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertTrue(flow.get("realized").getAsBoolean());
        assertTrue(flow.get("consumerFieldReadOffReceiverNode")
                .getAsBoolean());
        assertNotNull(findingOrNull(claim,
                ClaimPolicy.CONSUMER_FIELD_READ_OFF_RECEIVER_NODE,
                "data-encryption-key-id"));
    }

    /** A downstream read on the node the wire delivered to is this value. */
    @Test
    public void aFieldReadOnTheReceiverNodeIsNotReported() throws IOException {
        JsonObject manifest = flowManifest(false, true);
        manifest.getAsJsonObject("guardedReadModel").add("reads",
                readsOn(DEK_FIELD, "hdfs-17897/client#epoch0"));

        JsonObject claim = ClaimPolicy.decide(manifest, reach(),
                fieldFlows());

        JsonObject flow = wireFlow(claim, "data-encryption-key-id");
        assertFalse(flow.get("consumerFieldReadOffReceiverNode")
                .getAsBoolean());
        assertNull(findingOrNull(claim,
                ClaimPolicy.CONSUMER_FIELD_READ_OFF_RECEIVER_NODE,
                "data-encryption-key-id"));
    }

    private static JsonArray readsOn(String declaredField, String node) {
        JsonObject arm = new JsonObject();
        arm.addProperty("declaredField", declaredField);
        arm.addProperty("locationKey", "INSTANCE_FIELD/" + node
                + "/region/REGION.60480aef-4475-3abd-9303-ef693c04e7d0#1#a1"
                + "@receiver:1@" + declaredField);
        JsonArray arms = new JsonArray();
        arms.add(arm);
        JsonObject read = new JsonObject();
        read.add("arms", arms);
        JsonArray reads = new JsonArray();
        reads.add(read);
        return reads;
    }

    /** One declared flow whose consumer names the field it assigns to. */
    private static ClaimPolicy.WireFlowEvidence fieldFlows()
            throws IOException {
        Path directory = Files.createTempDirectory("claim-field-flows");
        Path mappings = directory.resolve("communication-mappings.jsonl");
        Files.write(mappings, ("{\"schemaVersion\":1,"
                + "\"kind\":\"WIRE_FLOW\","
                + "\"id\":\"data-encryption-key-id\","
                + "\"transport\":\"HDFS_SASL\","
                + "\"direction\":\"REQUEST\","
                + "\"consumerField\":\"" + DEK_FIELD + "\"}\n")
                .getBytes(StandardCharsets.UTF_8));
        return ClaimPolicy.WireFlowEvidence.read(mappings.toString(), "");
    }

    private static JsonObject flowManifest(boolean portBound,
                                           boolean fieldRead) {
        JsonObject manifest = manifest();
        JsonObject binding = new JsonObject();
        binding.addProperty("portId", "XCH.da84e470-fe7e-3068-b93f-"
                + "caafeef64a70.req.data-encryption-key-id");
        binding.addProperty("valueBound", portBound);
        binding.addProperty("receiverOccurrenceId",
                "hdfs-17897/client#epoch0/region/REGION.ff9377c2-8f99-3a0c-"
                        + "8f0b-c71ea893b3c5#1#a1");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        manifest.add(ConcolicSmtComposer.WIRE_FLOW_BINDINGS, bindings);
        JsonObject guardedReads = new JsonObject();
        guardedReads.add("reads", fieldRead ? readsOf(DEK_FIELD)
                : new JsonArray());
        manifest.add("guardedReadModel", guardedReads);
        return manifest;
    }

    private static JsonArray readsOf(String declaredField) {
        JsonObject arm = new JsonObject();
        arm.addProperty("declaredField", declaredField);
        JsonArray arms = new JsonArray();
        arms.add(arm);
        JsonObject read = new JsonObject();
        read.add("arms", arms);
        JsonArray reads = new JsonArray();
        reads.add(read);
        return reads;
    }

}
