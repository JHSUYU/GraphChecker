package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
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

    /**
     * A witness with nothing unexplained in it, and nothing named either.
     *
     * <p>No root flips the target and the witness names no mechanism, so
     * there is no way the program could have done it to report: the
     * valuation is satisfiable and that is all it is. "Nothing unexplained"
     * used to be enough to publish it as a finding, which is how a sat
     * answer with an empty mechanism list became an accepted claim. The
     * freedom findings are still reported; the claim is not.</p>
     */
    @Test
    public void anExplainedWitnessThatNamesNoMechanismIsNotAFinding() {
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                        + "{\"values\":[true],\"status\":\"sat\"}]"));

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertEquals("NO_MECHANISM",
                blocker(claim, ClaimPolicy.FINDING_MECHANISM_UNNAMED)
                        .get("subject").getAsString());
        assertEquals("", claim.getAsJsonObject("rootSpace")
                .get("acceptedFindingKind").getAsString());
        assertEquals(ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS,
                finding(claim, ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS)
                        .get("code").getAsString());
        assertFalse(claim.getAsJsonObject("rootSpace").get("faultSensitive")
                .getAsBoolean());
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

    @Test
    public void noExactReachabilityIsItsOwnBlocker() {
        JsonObject reach = reach();
        reach.addProperty("reachability",
                "UNKNOWN");

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.NO_EXACT_REACHABILITY), codes(claim));
    }


    /** One Composer handoff-ledger row whose value reached a term. */
    private static JsonObject bound(String port) {
        return ledgerRow(port, true);
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


    private static ClaimPolicy.PlannedSymbolicRoots noFlows() {
        return ClaimPolicy.PlannedSymbolicRoots.none();
    }


    /** The root the base fixture enumerates, and what it recorded. */
    private static final String BASE_TERM = "sym__base__1";
    private static final String BASE_SOURCE = "HDFS.CONFIG.BASE";
    private static final String BASE_FIELD =
            "<org.apache.hadoop.Base: boolean enabled>";

    /**
     * A composition whose one declared root states what it recorded.
     *
     * <p>The base fixture used to enumerate a {@code values} vector with no
     * {@code roots.booleanInputs} behind it, so every test written on it
     * asked the gate about a witness over roots the report never declared.
     * That is not a shape a run has: the extractor builds the vector from
     * the root list. Declaring the root -- a configured source, recorded
     * {@code false}, the HDFS-17960 shape -- is what makes the fixture the
     * run it claims to be, and it is what lets the base case name a finding
     * kind at all.</p>
     */
    private static JsonObject manifest() {
        JsonObject manifest = parse("{\"schemaVersion\":2,"
                + "\"kind\":\"CONCOLIC_COMPOSED_SMT\","
                + "\"state\":\"CANDIDATE_READY\","
                + "\"finalStatus\":\"FINAL_READY\","
                + "\"finalStatusRefusals\":[],"
                + "\"symbolicPropagationComplete\":true,"
                + "\"casePathConditionDependencies\":[],"
                + "\"guardedReadModelComplete\":true,"
                + "\"gaps\":[]}");
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, parseArray(
                "[{\"solverTerm\":\"" + BASE_TERM + "\","
                + "\"sourceId\":\"" + BASE_SOURCE + "\","
                + "\"siteId\":\"" + BASE_FIELD + "\","
                + "\"recordedValue\":\"false\",\"wallClock\":false}]"));
        return manifest;
    }

    /** A REACHABLE report whose single Boolean root decides the target. */
    private static JsonObject reach() {
        JsonObject reach = parse("{\"schemaVersion\":4,"
                + "\"kind\":\"ROOT_VALUATION_REPORT\","
                + "\"state\":\"CANDIDATE_READY\","
                + "\"unsatClosureComplete\":true,"
                + "\"gaps\":[],"
                + "\"reachability\":\"REACHABLE\","

                + "\"valuations\":["
                + "{\"values\":[false],\"status\":\"sat\"},"
                + "{\"values\":[true],\"status\":\"unsat\"}]}");
        reach.add("roots", parse(
                "{\"booleanInputs\":["
                + "{\"inputKind\":\"CONFIGURED_SOURCE_FIELD\","
                + "\"sourceId\":\"" + BASE_SOURCE + "\","
                + "\"fieldSignature\":\"" + BASE_FIELD + "\","
                + "\"javaTypeDescriptor\":\"Z\","
                + "\"solverTerm\":\"" + BASE_TERM + "\"}],"
                + "\"existentialInputs\":[]}"));
        return reach;
    }

    private static JsonObject refutation(boolean closed) {
        JsonObject reach = reach();
        reach.addProperty(ComposedManifest.UNSAT_CLOSURE_COMPLETE, closed);
        reach
                .addProperty("reachability", "UNREACHABLE");
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
    public void interiorClockSkewShownNecessaryIsALegitimateFinding() {
        JsonObject claim = ClaimPolicy.decide(markerManifest(),
                markerReach(true, "245021"), noFlows());

        assertEquals(ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        assertEquals(1, markerRow(claim)
                .getAsJsonArray("otherPolarityMechanisms").size());
        assertEquals(WitnessLegitimacy.EXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());
        assertEquals(WitnessLegitimacy.CLOCK_SKEW,
                witnessFinding(claim, 0).get(WitnessLegitimacy.FINDING_KIND)
                        .getAsString());
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
     * With nothing stating one, there is no polarity and the run says so.
     *
     * <p>The default this replaced read an unstated root as {@code true},
     * which made every witness at {@code false} a flip -- and that is the
     * whole of HDFS-17960's accepted finding on the laneX artifact: an
     * empty {@code recordedRootValues}, {@code recordedPolarityStated:false},
     * a witness value of {@code false}, {@code flipped:true}, and an empty
     * mechanism list under the reason "a symbolic root flips it".</p>
     */
    @Test
    public void anUnstatedRecordedValueBlocksTheClaim() {
        JsonObject manifest = markerManifest();
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES,
                new JsonArray());

        JsonObject claim = ClaimPolicy.decide(manifest,
                markerReach(true, "-300000"), noFlows());

        JsonObject marker = markerRow(claim);
        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertFalse(marker.get("recordedPolarityStated").getAsBoolean());
        assertFalse("no polarity is invented",
                marker.has("recordedPolarity"));
        assertEquals("MANUAL.fault", blocker(claim,
                ClaimPolicy.RECORDED_ROOT_VALUE_UNSTATED)
                .get("subject").getAsString());
        for (JsonElement element
                : claim.getAsJsonArray(WitnessLegitimacy.FINDINGS)) {
            assertFalse("nothing is a flip against a value nobody stated",
                    element.getAsJsonObject().getAsJsonArray(
                            "markerAssignment").get(0).getAsJsonObject()
                            .has("flipped"));
        }
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
        assertEquals(WitnessLegitimacy.RECORDED_FAILURE_EXPLAINED,
                rootSpace.get("acceptedFindingKind").getAsString());
        assertTrue(rootSpace.get("recordedFailureExplained").getAsBoolean());
        assertEquals(WitnessLegitimacy.RECORDED_FAILURE_EXPLAINED,
                accepted.get(WitnessLegitimacy.FINDING_KIND).getAsString());
        JsonObject marker = markerRow(claim);
        assertTrue(marker.get("polarityDecides").getAsBoolean());
        assertTrue(marker.get("reachesAtRecordedValue").getAsBoolean());
    }

    /**
     * The same shape with the other polarity also satisfiable is not it.
     *
     * <p>{@link WitnessLegitimacy#RECORDED_FAILURE_EXPLAINED} says the chain
     * shows the recording is root-determined, and a flip the target reaches
     * anyway shows the opposite. Without the refutation the witness is a sat
     * answer with nothing named behind it.</p>
     */
    @Test
    public void aReproducedRecordingNeedsTheOtherPolarityRefuted() {
        JsonObject claim = ClaimPolicy.decide(orderedManifest("false"),
                orderedReach("sat", "sat"), noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        assertFalse(claim.getAsJsonObject("rootSpace")
                .get("recordedFailureExplained").getAsBoolean());
        assertEquals("", claim.getAsJsonObject("rootSpace")
                .get("acceptedFindingKind").getAsString());
        assertNotNull(blocker(claim,
                ClaimPolicy.FINDING_MECHANISM_UNNAMED));
    }

    /**
     * One configured Boolean source, materialized with a recorded value.
     *
     * @param recordedValue what the field held, or "" to state none
     */
    private static JsonObject orderedManifest(String recordedValue) {
        JsonObject manifest = manifest();
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES,
                new JsonArray());
        manifest.add(ComposedManifest
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, parseArray(
                "[{\"kind\":\"" + ComposedManifest
                        .CONFIGURED_SOURCE_MATERIALIZATION_KIND + "\","
                + "\"sourceKey\":\"hdfs-17960/nn0#epoch1\","
                + "\"sourceId\":\"" + ORDERED_SOURCE + "\","
                + "\"sourceOccurrenceId\":\"" + ORDERED_OCCURRENCE + "\","
                + "\"fieldSignature\":\"" + ORDERED_FIELD + "\","
                + "\"javaTypeDescriptor\":\"Z\",\"sort\":\"BOOL\","
                + (recordedValue.isEmpty() ? ""
                        : "\"" + ComposedManifest.RECORDED_SOURCE_VALUE
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


    private static JsonObject markerRow(JsonObject claim) {
        return claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("faultMarkers")
                .getAsJsonArray("markers").get(0).getAsJsonObject();
    }

    private static JsonObject markerManifest() {
        JsonObject manifest = manifest();
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, parseArray(
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
        reach.add(RootValuationSolver.MECHANISM_NECESSITY,
                clockNecessity(0, true));
        return reach;
    }

    /**
     * The probe's answer about one valuation's clock group.
     *
     * <p>Keyed by the valuation, because "these clocks disagreed" is a claim
     * about one witness and asking it one root at a time asks about a skew
     * nobody made. Every fixture that expects a clock to be a mechanism
     * carries one: a clock that moved and nothing shows was needed is not a
     * mechanism, and a clock nobody asked about is not one either.</p>
     */
    private static JsonObject clockNecessity(int ordinal, boolean necessary) {
        return parse("{\"schemaVersion\":1,"
                + "\"kind\":\"WITNESS_MECHANISM_NECESSITY\","
                + "\"authority\":\"RECORDED_ROOT_PIN_V1\","
                + "\"mechanisms\":[{\"marker\":\"\","
                + "\"sourceIdentity\":\"\",\"polarity\":true,"
                + "\"valuationOrdinal\":" + ordinal + ","
                + "\"mechanism\":\"CLOCK_SKEW\",\"pinnedRoots\":1,"
                + "\"status\":\"" + (necessary ? "unsat" : "sat") + "\","
                + "\"necessary\":" + necessary + "}]}");
    }


}
