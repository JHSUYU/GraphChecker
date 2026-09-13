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
        reach.getAsJsonObject("reachCondition").addProperty("reachability",
                "UNKNOWN");

        JsonObject claim = ClaimPolicy.decide(manifest(), reach, noFlows());

        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL, claim.get("claim")
                .getAsString());
        assertEquals(codes(ClaimPolicy.NO_EXACT_REACHABILITY), codes(claim));
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
        manifest.add(ComposedManifest.WIRE_FLOW_BINDINGS, ledger);
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
        assertEquals(WitnessLegitimacy.ROTATION_RACE,
                witnessFinding(claim, 0).get(WitnessLegitimacy.FINDING_KIND)
                        .getAsString());
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
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, parseArray(
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
        reach.add(BooleanReachConditionExtractor.MECHANISM_NECESSITY,
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

    private static final String DEK_FIELD =
            "org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey"
            + "#keyId";

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
        manifest.add(ComposedManifest.WIRE_FLOW_BINDINGS, bindings);
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
