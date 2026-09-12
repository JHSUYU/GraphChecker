package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

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
        JsonObject claim = ClaimPolicy.decide(manifest(), reach(), 0);

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
                ClaimPolicy.decide(manifest(), reach, 0).get("claim")
                        .getAsString());
    }

    /** A closed refutation is accepted only with closure authority. */
    @Test
    public void closedRefutationIsAcceptedAsUnsatClosed() {
        JsonObject claim = ClaimPolicy.decide(manifest(), refutation(true), 0);

        assertEquals(ClaimPolicy.UNSAT_CLOSED, claim.get("claim")
                .getAsString());
        assertEquals(0, claim.getAsJsonArray("blockers").size());
    }

    @Test
    public void openRefutationIsWithheldAsUnsatClosureIncomplete() {
        JsonObject claim = ClaimPolicy.decide(manifest(), refutation(false),
                0);

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

        JsonObject claim = ClaimPolicy.decide(manifest, reach(), 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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
     * The hdfs-17899-bug3 finding: the experiment declares cross-node wire
     * flows and the composition realized no consumer boundary family, so
     * neither side of the wire is in the formula the witness satisfies.
     */
    @Test
    public void declaredWireFlowsWithNoBoundaryFamilyBlockTheClaim() {
        JsonObject manifest = manifest();
        manifest.add("symbolicPropagation", new JsonArray());

        JsonObject claim = ClaimPolicy.decide(manifest, reach(), 2);

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED),
                codes(claim));
        assertEquals("2", blocker(claim,
                ClaimPolicy.DECLARED_WIRE_FLOWS_UNREALIZED)
                .get("subject").getAsString());
    }

    /** An experiment that declares no flow has none to realize. */
    @Test
    public void noDeclaredWireFlowNeedsNoBoundaryFamily() {
        JsonObject manifest = manifest();
        manifest.add("symbolicPropagation", new JsonArray());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                ClaimPolicy.decide(manifest, reach(), 0).get("claim")
                        .getAsString());
    }

    @Test
    public void everyZeroWitnessIsUninformative() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\","
                        + "\"existentialWitness\":[{\"value\":\"0\"},"
                        + "{\"value\":\"(- 0)\"}]},"
                        + "{\"values\":[true],\"status\":\"unsat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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
                ClaimPolicy.decide(manifest(), reach, 0).get("claim")
                        .getAsString());
    }

    @Test
    public void undecidedValuationRowBlocksTheClaim() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"unsat\"},"
                        + "{\"values\":[true],\"status\":\"unknown\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

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

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, 0);

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.NO_EXACT_REACHABILITY), codes(claim));
    }

    /** One line per blocker: the whole reason, in the owner's one view. */
    @Test
    public void whyNotAcceptedNamesEveryBlockerOnItsOwnLine() {
        JsonObject manifest = manifest();
        manifest.add("symbolicPropagation", new JsonArray());
        JsonObject reach = reach();
        reach.getAsJsonObject("reachCondition").addProperty("degeneracyCheck",
                "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9");
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest, reach, 2);
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
    public void declaredWireFlowsCountsOnlyWireFlowRows() throws IOException {
        File directory = Files.createTempDirectory("claim-policy").toFile();
        Path mappings = directory.toPath().resolve("mappings.jsonl");
        Files.write(mappings, (
                "{\"schemaVersion\":1,\"kind\":\"WIRE_FLOW\",\"id\":\"a\"}\n"
                + "{\"schemaVersion\":1,\"kind\":\"WIRE_FLOW\",\"id\":\"b\"}\n"
                + "{\"schemaVersion\":1,\"kind\":\"SHARED_FIELD\",\"id\":\"c\"}\n")
                .getBytes(StandardCharsets.UTF_8));

        assertEquals(2, ClaimPolicy.declaredWireFlows(mappings.toString()));
        assertEquals(0, ClaimPolicy.declaredWireFlows(""));
        assertEquals(0, ClaimPolicy.declaredWireFlows(
                directory.toPath().resolve("absent.jsonl").toString()));
    }

    /** A composition the Composer published as complete and candidate-ready. */
    private static JsonObject manifest() {
        return parse("{\"schemaVersion\":2,"
                + "\"kind\":\"CONCOLIC_COMPOSED_SMT\","
                + "\"state\":\"CANDIDATE_READY\","
                + "\"finalStatus\":\"FINAL_READY\","
                + "\"finalStatusRefusals\":[],"
                + "\"symbolicPropagationComplete\":true,"
                + "\"symbolicPropagation\":[{\"armCount\":2}],"
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
