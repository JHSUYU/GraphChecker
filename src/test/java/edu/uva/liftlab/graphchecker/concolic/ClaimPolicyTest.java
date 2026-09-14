package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The campaign acceptance gate: each rule names either a published gap that
 * withholds the claim -- a blocker the jq gate did not have -- or an accept
 * path it must not withdraw.
 */
public class ClaimPolicyTest {
    private static final String BASE_TERM = "sym__base__1";
    private static final String BASE_SOURCE = "HDFS.CONFIG.BASE";
    private static final String BASE_FIELD =
            "<org.apache.hadoop.Base: boolean enabled>";

    /**
     * A published gap withholds the claim under its own name: no mechanism,
     * an inexact reachability answer, freedom the recording does not cover,
     * an unstated value, a reproduction whose other polarity is sat too.
     */
    @Test
    public void aPublishedGapWithholdsTheClaim() {
        // The valuation is satisfiable and that is all it is: the freedom
        // findings are still reported, the claim is not.
        JsonObject reach = reach();
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\"},"
                + "{\"values\":[true],\"status\":\"sat\"}]"));
        JsonObject claim = withheld(manifest(), reach);
        assertEquals("NO_MECHANISM",
                blocker(claim, ClaimPolicy.FINDING_MECHANISM_UNNAMED)
                        .get("subject").getAsString());
        assertEquals("", claim.getAsJsonObject("rootSpace")
                .get("acceptedFindingKind").getAsString());
        named(claim.getAsJsonObject("rootSpace").getAsJsonArray(
                "reportedFindings"),
                ClaimPolicy.TARGET_UNCONSTRAINED_BY_ROOTS);
        assertFalse(claim.getAsJsonObject("rootSpace").get("faultSensitive")
                .getAsBoolean());

        // No exact reachability is its own blocker, and the only one.
        JsonObject unknown = reach();
        unknown.addProperty("reachability", "UNKNOWN");
        claim = withheld(manifest(), unknown);
        blocker(claim, ClaimPolicy.NO_EXACT_REACHABILITY);
        assertEquals(1, claim.getAsJsonArray("blockers").size());

        // The window is the recording's own statement about what that clock
        // could have read; past it, the witness is the search's answer.
        claim = withheld(markerManifest(), markerReach("-300001"));
        assertEquals(WitnessLegitimacy.CLOCK_OUTSIDE_WINDOW,
                blocker(claim, ClaimPolicy.WITNESS_FREEDOM_UNEXPLAINED)
                        .get("subject").getAsString());
        assertTrue(blocker(claim, ClaimPolicy.FAULT_MARKER_NOT_DETERMINING)
                .get("detail").getAsString()
                .contains(WitnessLegitimacy.CLOCK_OUTSIDE_WINDOW));
        assertEquals(WitnessLegitimacy.UNEXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());

        // With nothing stating one there is no polarity, and none is
        // invented: the default this replaced made every false a flip.
        JsonObject unstated = markerManifest();
        unstated.add(ComposedManifest.RECORDED_ROOT_VALUES, new JsonArray());
        claim = withheld(unstated, markerReach("-300000"));
        assertEquals("MANUAL.fault",
                blocker(claim, ClaimPolicy.RECORDED_ROOT_VALUE_UNSTATED)
                        .get("subject").getAsString());
        assertFalse(markerRow(claim).get("recordedPolarityStated")
                .getAsBoolean());
        assertFalse("no polarity is invented",
                markerRow(claim).has("recordedPolarity"));
        assertFalse("nothing is a flip against a value nobody stated",
                witnessFinding(claim, 0).getAsJsonArray("markerAssignment")
                        .get(0).getAsJsonObject().has("flipped"));

        // RECORDED_FAILURE_EXPLAINED says the chain shows the recording is
        // root-determined, so a reproduction needs the other polarity
        // refuted.
        claim = withheld(orderedManifest(), orderedReach("sat", "sat"));
        blocker(claim, ClaimPolicy.FINDING_MECHANISM_UNNAMED);
        assertFalse(claim.getAsJsonObject("rootSpace")
                .get("recordedFailureExplained").getAsBoolean());
    }

    /**
     * An accepted claim rests on one root whose polarity decides the target.
     *
     * <p>Interior clock skew is drift that happened, so the necessity probe
     * decides nothing; and HDFS-17960 injects nothing at all -- its only
     * root is the program's own configuration field and the satisfying
     * valuation is the recorded {@code false}, so demanding a flip of it
     * refused the run for reproducing its own recording.</p>
     */
    @Test
    public void anAcceptedClaimRestsOnARootWhosePolarityDecidesTheTarget() {
        JsonObject decided = markerReach("-300000");
        decided.getAsJsonArray("valuations").get(0).getAsJsonObject()
                .addProperty("status", "unsat");
        assertTrue(markerRow(accepted(markerManifest(), decided))
                .get("polarityDecides").getAsBoolean());

        JsonObject claim = accepted(markerManifest(), markerReach("245021"));
        assertEquals(WitnessLegitimacy.EXPLAINED,
                witnessFinding(claim, 0).get("verdict").getAsString());
        assertEquals(WitnessLegitimacy.CLOCK_SKEW,
                witnessFinding(claim, 0).get(WitnessLegitimacy.FINDING_KIND)
                        .getAsString());

        claim = accepted(orderedManifest(), orderedReach("sat", "unsat"));
        assertEquals(0, claim.getAsJsonArray("blockers").size());
        JsonObject rootSpace = claim.getAsJsonObject("rootSpace");
        assertEquals(ClaimPolicy.RECORDED_ROOT_VALUES_REPRODUCED,
                rootSpace.get("acceptedWitnessKind").getAsString());
        assertEquals(WitnessLegitimacy.RECORDED_FAILURE_EXPLAINED,
                rootSpace.get("acceptedFindingKind").getAsString());
        assertTrue(rootSpace.get("recordedFailureExplained").getAsBoolean());
        assertTrue(witnessFinding(claim, 0).get("allRecorded").getAsBoolean());
        assertTrue(markerRow(claim).get("polarityDecides").getAsBoolean());
        assertTrue(markerRow(claim).get("reachesAtRecordedValue")
                .getAsBoolean());

        // And only where the witness's own path took the arm.  A recording
        // that observed the healthy outcome explains no recorded failure --
        // lane17897h elected exactly that on a healthy-observed path, with
        // the two that took the arm unsatisfiable elsewhere in the
        // disjunction -- so the run refuses and names what is missing.
        JsonObject healthy = orderedManifest();
        healthy.add(ComposedManifest.TARGET_REACH_LEDGER, ledger(true));
        JsonObject refused = withheld(healthy,
                orderedReach("sat", "unsat"));
        assertEquals("NO_SUPPORTED_WITNESS",
                blocker(refused, ClaimPolicy.FINDING_MECHANISM_UNNAMED)
                        .get("subject").getAsString());
        assertEquals("", refused.getAsJsonObject("rootSpace")
                .get("acceptedFindingKind").getAsString());
        assertFalse(refused.getAsJsonObject("rootSpace")
                .get("recordedFailureExplained").getAsBoolean());
        // And a formula that answers yes to the execution that did not fail
        // is an alarm, named and blocking, not a witness.
        blocker(refused, ClaimPolicy.FORMULA_SAT_AT_RECORDED_VALUATION);

        // A declared root is enumerated over its domain exactly as a marker
        // is over {recorded, flipped}, so the valuation that moved it is the
        // witness the claim rests on, and the claim names the root and the
        // distance: bug3's key rotation is one step of a serial number.
        JsonObject rotated = markerManifest();
        rotated.add(ComposedManifest.RECORDED_ROOT_VALUES, parseArray(
                "[{'solverTerm':'sn','sourceId':'HDFS.BLOCK_KEY.SERIAL_NO',"
                + "'siteId':'<M: int serialNo>','recordedValue':'119982',"
                + "'declaredDomainMin':'119982','declaredDomainMax':'119985',"
                + "'wallClock':false}]".replace('\'', '"')));
        // The composition states the domain on both rows it publishes about
        // a root: the one a mechanism is read against and the one the
        // enumeration reads.
        rotated.add(PathMergeComposer.MANIFEST_FIELD, parse(
                "{'roots':[{'solverTerm':'sn','declaredDomainMin':'119982',"
                + "'declaredDomainMax':'119985'}]}".replace('\'', '"')));
        JsonObject moved = reach();
        moved.add("roots", parse("{\"existentialInputs\":[{\"sourceId\":"
                + "\"HDFS.BLOCK_KEY.SERIAL_NO\",\"solverTerm\":\"sn\","
                + "\"javaTypeDescriptor\":\"I\"}],\"booleanInputs\":[]}"));
        moved.add("valuations", parseArray(
                "[{\"values\":[],\"status\":\"sat\"},"
                + "{\"values\":[],\"status\":\"sat\",\"rootAssignment\":"
                + "{\"sn\":\"119983\"},\"witnessMechanisms\":[{\"kind\":"
                + "\"MARKER_FLIPPED\",\"solverTerm\":\"sn\",\"siteId\":"
                + "\"<M: int serialNo>\",\"recordedValue\":\"119982\","
                + "\"witnessValue\":\"119983\"}]}]"));
        JsonObject rotation = accepted(rotated, moved);
        JsonObject space = rotation.getAsJsonObject("rootSpace");
        assertEquals(WitnessLegitimacy.MARKER_FLIPPED,
                space.get("acceptedFindingKind").getAsString());
        assertEquals(1, space.get("acceptedValuationOrdinal").getAsInt());
        assertTrue(rotation.get("claimReason").getAsString(),
                rotation.get("claimReason").getAsString()
                        .contains("119982 -> 119983"));

        // And a root the case declared no domain for is never a value to
        // enumerate: the composition pinned it to its recording.
        assertTrue(RootValuationSolver.declaredDomains(
                markerManifest()).isEmpty());
        assertEquals(1, RootValuationSolver.declaredDomains(rotated).size());
    }

    private static JsonObject withheld(JsonObject manifest, JsonObject reach) {
        JsonObject claim = ClaimPolicy.decide(manifest, reach,
                ClaimPolicy.PlannedSymbolicRoots.none());
        assertEquals(claim.toString(), ClaimPolicy.INCONCLUSIVE_PARTIAL,
                claim.get("claim").getAsString());
        return claim;
    }

    private static JsonObject accepted(JsonObject manifest, JsonObject reach) {
        JsonObject claim = ClaimPolicy.decide(manifest, reach,
                ClaimPolicy.PlannedSymbolicRoots.none());
        assertEquals(claim.toString(), ClaimPolicy.SAT_CANDIDATE,
                claim.get("claim").getAsString());
        return claim;
    }

    /** A composition whose one declared root states what it recorded. */
    private static JsonObject manifest() {
        JsonObject manifest = parse("{\"schemaVersion\":2,\"kind\":"
                + "\"CONCOLIC_COMPOSED_SMT\",\"state\":\"CANDIDATE_READY\","
                + "\"finalStatus\":\"FINAL_READY\",\"finalStatusRefusals\":[],"
                + "\"symbolicPropagationComplete\":true,\"gaps\":[],"
                + "\"casePathConditionDependencies\":[],"
                + "\"guardedReadModelComplete\":true}");
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, parseArray(
                "[{\"solverTerm\":\"" + BASE_TERM + "\",\"sourceId\":\""
                + BASE_SOURCE + "\",\"siteId\":\"" + BASE_FIELD + "\","
                + "\"recordedValue\":\"false\",\"wallClock\":false}]"));
        // The anchor's attested path, as the composer publishes it: this
        // recording observed the arm the failure needs, which is what
        // HDFS-17960's own artifact states.
        manifest.add(ComposedManifest.TARGET_REACH_LEDGER,
                ledger(false));
        return manifest;
    }

    /** One attested path at the anchor, with the outcome it observed. */
    private static JsonArray ledger(boolean observed) {
        return parseArray("[{\"kind\":\"TARGET_REACH_EVENT\","
                + "\"attestationRole\":\"REQUIRED_TARGET_REACH_EVENT\","
                + "\"outcome\":" + observed + ",\"caseGuard\":\"\","
                + "\"sourceObservedOutcome\":" + observed + "}]");
    }

    private static JsonObject reach() {
        JsonObject reach = parse("{\"schemaVersion\":4,\"kind\":"
                + "\"ROOT_VALUATION_REPORT\",\"state\":\"CANDIDATE_READY\","
                + "\"unsatClosureComplete\":true,\"gaps\":[],"
                + "\"reachability\":\"REACHABLE\",\"valuations\":["
                + "{\"values\":[false],\"status\":\"sat\"},"
                + "{\"values\":[true],\"status\":\"unsat\"}]}");
        reach.add("roots", parse("{\"existentialInputs\":[],"
                + "\"booleanInputs\":[{\"inputKind\":\"CONFIGURED_SOURCE_"
                + "FIELD\",\"sourceId\":\"" + BASE_SOURCE + "\","
                + "\"fieldSignature\":\"" + BASE_FIELD + "\","
                + "\"javaTypeDescriptor\":\"Z\",\"solverTerm\":\""
                + BASE_TERM + "\"}]}"));
        return reach;
    }

    private static JsonObject markerManifest() {
        JsonObject manifest = manifest();
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, parseArray(
                "[{\"solverTerm\":\"manual__fault\",\"recordedValue\":"
                + "\"false\",\"wallClock\":false}]"));
        manifest.add(ClockRootPhysics.MANIFEST_FIELD, parse(
                "{\"schemaVersion\":1,\"kind\":\"CLOCK_ROOT_PHYSICS\","
                + "\"clockSkewMillis\":300000,\"clockReads\":[]}"));
        return manifest;
    }

    /**
     * One declared marker, both polarities satisfiable, and the polarity
     * with no fault explained only by a clock moved by {@code skewMillis};
     * the perturbation probe keeps TARGET_UNCONSTRAINED_BY_ROOTS from
     * firing instead.
     */
    private static JsonObject markerReach(String skewMillis) {
        JsonObject reach = reach();
        reach.add("existentialRootProbe", parse("{\"authority\":\"SOLVER_"
                + "WITNESS_NEIGHBOR_PERTURBATION_V1\",\"constrainsRootSpace\":"
                + "true,\"perturbations\":[{\"sourceIdentity\":"
                + "\"MANUAL.clock\",\"portId\":\"REGION.nn0.in.now\","
                + "\"witnessValue\":\"9\",\"perturbedValue\":\"8\","
                + "\"status\":\"unsat\"}]}"));
        reach.add("roots", parse("{\"existentialInputs\":[],\"booleanInputs\":"
                + "[{\"inputKind\":\"REGION_SYMBOLIC_INPUT\","
                + "\"sourceIdentity\":\"MANUAL.fault\",\"portId\":"
                + "\"REGION.sendRpcRequest.in.fault\",\"occurrenceId\":"
                + "\"hdfs/dn0#epoch0/region/REGION.x#1\","
                + "\"javaTypeDescriptor\":\"Z\",\"solverTerm\":"
                + "\"manual__fault\"}]}"));
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"sat\",\"witnessMechanisms\":"
                + "[{\"kind\":\"CLOCK_SKEW\",\"skewMillis\":" + skewMillis
                + ",\"siteId\":\"BlockTokenSecretManager.updateKeys()#u28\","
                + "\"sourceKey\":\"hdfs/nn0#epoch0\"}]},"
                + "{\"values\":[true],\"status\":\"sat\",\"witnessMechanisms\":"
                + "[{\"kind\":\"MARKER_FLIPPED\",\"siteId\":"
                + "\"Client$Connection.sendRpcRequest#u17\"}]}]"));
        reach.add(RootValuationSolver.MECHANISM_NECESSITY, parse(
                "{\"schemaVersion\":1,\"kind\":\"WITNESS_MECHANISM_NECESSITY\","
                + "\"authority\":\"RECORDED_ROOT_PIN_V1\",\"mechanisms\":"
                + "[{\"marker\":\"\",\"sourceIdentity\":\"\",\"polarity\":true,"
                + "\"valuationOrdinal\":0,\"mechanism\":\"CLOCK_SKEW\","
                + "\"pinnedRoots\":1,\"status\":\"unsat\",\"necessary\":true}]"
                + "}"));
        return reach;
    }

    private static final String ORDERED_FIELD = "<org.apache.hadoop.hdfs"
            + ".server.namenode.snapshot.SnapshotManager:"
            + " boolean snapshotDeletionOrdered>";
    private static final String ORDERED_SOURCE =
            "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED";
    private static final String ORDERED_OCCURRENCE = "hdfs-17960/nn0#epoch1"
            + "/region/REGION.9492ec77#1#a1";
    private static final String ORDERED_TERM = "sym__ordered__1";

    private static JsonObject orderedManifest() {
        JsonObject manifest = markerManifest();
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, new JsonArray());
        manifest.add(ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                parseArray("[{\"kind\":\"" + ComposedManifest
                        .CONFIGURED_SOURCE_MATERIALIZATION_KIND + "\","
                + "\"sourceKey\":\"hdfs-17960/nn0#epoch1\",\"sourceId\":\""
                + ORDERED_SOURCE + "\",\"sourceOccurrenceId\":\""
                + ORDERED_OCCURRENCE + "\",\"fieldSignature\":\""
                + ORDERED_FIELD + "\",\"javaTypeDescriptor\":\"Z\","
                + "\"sort\":\"BOOL\",\"" + ComposedManifest
                        .RECORDED_SOURCE_VALUE + "\":\"false\","
                + "\"solverTerm\":\"" + ORDERED_TERM + "\"}]"));
        return manifest;
    }

    private static JsonObject orderedReach(String atFalse, String atTrue) {
        JsonObject reach = reach();
        reach.add("roots", parse("{\"existentialInputs\":[],\"booleanInputs\":"
                + "[{\"inputKind\":\"CONFIGURED_SOURCE_FIELD\",\"sourceKey\":"
                + "\"hdfs-17960/nn0#epoch1\",\"sourceId\":\"" + ORDERED_SOURCE
                + "\",\"sourceOccurrenceId\":\"" + ORDERED_OCCURRENCE
                + "\",\"fieldSignature\":\"" + ORDERED_FIELD + "\","
                + "\"javaTypeDescriptor\":\"Z\",\"solverTerm\":\""
                + ORDERED_TERM + "\"}]}"));
        reach.add("valuations", parseArray(
                "[{\"values\":[false],\"status\":\"" + atFalse + "\"},"
                + "{\"values\":[true],\"status\":\"" + atTrue + "\"}]"));
        return reach;
    }

    private static JsonObject markerRow(JsonObject claim) {
        return claim.getAsJsonObject("rootSpace")
                .getAsJsonObject("faultMarkers").getAsJsonArray("markers")
                .get(0).getAsJsonObject();
    }

    private static JsonObject witnessFinding(JsonObject claim, int ordinal) {
        return claim.getAsJsonArray(WitnessLegitimacy.FINDINGS)
                .get(ordinal).getAsJsonObject();
    }

    private static JsonObject blocker(JsonObject claim, String code) {
        return named(claim.getAsJsonArray("blockers"), code);
    }

    private static JsonObject named(JsonArray rows, String code) {
        for (JsonElement element : rows) {
            JsonObject row = element.getAsJsonObject();
            if (code.equals(row.get("code").getAsString())) return row;
        }
        throw new AssertionError("no row named " + code + " in " + rows);
    }

    private static JsonObject parse(String json) {
        return JsonParser.parseString(json).getAsJsonObject();
    }

    private static JsonArray parseArray(String json) {
        return JsonParser.parseString(json).getAsJsonArray();
    }
}
