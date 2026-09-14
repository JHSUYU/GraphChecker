package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.TargetAnchorEvidence;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import org.junit.Assume;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
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
 * The merge, on three recordings small enough to read.
 *
 * <p>One root, one anchored target, and paths that differ only in what the
 * root made their fatal predicate: the disjunction must be satisfiable
 * exactly where some path's own condition is, and the gates must refuse
 * rather than guess where a value is missing.</p>
 */
public class PathMergeComposerTest {
    private static final String SITE =
            "<com.example.Service: void serve()>#u17";
    private static final String PHASE = "SOURCE_PHASE.example";
    private static final String SOURCE = "EXAMPLE.ROOT";
    private static final String FIELD_SIGNATURE =
            "<com.example.Service: boolean enabled>";
    private static final String RAW_ROOT = "M_Z_field_"
            + SymbolicSourceEvidence.engineLabelForPhase(PHASE, SOURCE)
            + "_com/example/Service";
    private static final String ROOT_TERM = "sym__EXAMPLE_ROOT__1";
    private static final String SERIAL_PHASE = "SOURCE_PHASE.serial";
    private static final String SERIAL_SOURCE = "EXAMPLE.SERIAL";
    private static final String SERIAL_SIGNATURE =
            "<com.example.Service: int serial>";
    private static final String RAW_SERIAL = "M_I_field_"
            + SymbolicSourceEvidence.engineLabelForPhase(SERIAL_PHASE,
            SERIAL_SOURCE) + "_com/example/Service";
    private static final String SERIAL_TERM = "sym__EXAMPLE_SERIAL__1";
    private static final String CLOCK_SIGNATURE =
            "<com.example.Service: long now>";
    private static final String RAW_CLOCK = "M_J_field_"
            + SymbolicSourceEvidence.engineLabelForPhase("SOURCE_PHASE.now",
            "EXAMPLE.NOW") + "_com/example/Service";
    private static final String CLOCK_TERM = "sym__EXAMPLE_NOW__1";
    private static final String CLOCK_CALLEE =
            "<org.apache.hadoop.util.Timer: long now()>";
    private static final String CLOCK_PORT = "REGION.example.in.clock";
    private static final String CLOCK_SITE =
            "<com.example.Service: void serve()>#u4";
    private static final String CLOCK_OCCURRENCE =
            "node0/region/REGION.example#1#a1";
    private static final String CLOCK_RAW = "M_J_clock_example";
    private static final long CLOCK_READING = 1700000000000L;

    /**
     * Two replays of one site: the seed the root kept healthy and the flip
     * the root made fatal.  Only the flipped path's root valuation may
     * satisfy the disjunction.
     */
    @Test
    public void disjunctionIsSatisfiableOnlyOnTheFlippedPath()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-flip");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(1))));
        query.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        assertEquals("CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertEquals(2, merge.getAsJsonArray("paths").size());
        assertEquals(2, result.manifest.getAsJsonArray(
                "caseSelectorPartitions").get(0).getAsJsonArray().size());
        assertTrue(result.smtLib.contains(ROOT_TERM));

        // The root must be free, and free only where the flip put it.
        assertEquals("sat", solve(result.smtLib));
        assertEquals("sat", solve(result.smtLib
                + "(assert (= " + ROOT_TERM + " false))\n(check-sat)\n"));
        assertEquals("unsat", solve(result.smtLib
                + "(assert (= " + ROOT_TERM + " true))\n(check-sat)\n"));
    }

    /**
     * The healthy recording alone.  The site executed, so the target is
     * reached and nothing is refused; the failure simply is not reachable
     * from what that one replay showed.
     */
    @Test
    public void healthyPathAloneReachesTheTargetAndIsNotFatal()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-healthy");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(2), constant(2))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        assertEquals(1, result.manifest.getAsJsonArray(
                "targetReachLedger").size());
        assertTrue(merge.getAsJsonArray("paths").get(0).getAsJsonObject()
                .get("admitted").getAsBoolean());
        assertEquals("unsat", solve(result.smtLib));
    }

    /**
     * A predicate the replay published already concrete, at an activation
     * whose slice declares carriers and on a path that depends on no root:
     * the value was owed as an expression and arrived as a literal, which is
     * the cut.
     *
     * <p>The path condition matters.  A concrete phi on a path whose pi
     * flips a root is the HDFS-17960 shape -- the root reaches the target by
     * control flow and the pair of paths is the evidence -- and that is
     * admitted, not cut.  What is left here is a path on which nothing at
     * all depends on a root and whose predicate over declared carriers is
     * still a literal: there the propagation did drop a value.</p>
     */
    @Test
    public void literalPredicateOverDeclaredCarriersIsAPropagationCut()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-cut");
        JsonObject query = query();
        JsonObject path = path("seed", "GROUP.SEED",
                notEqual(constant(2), constant(3)),
                notEqual(constant(1), constant(0)));
        JsonArray carriers = new JsonArray();
        carriers.add("INSTANCE_FIELD/2#24");
        path.getAsJsonObject(TargetAnchorEvidence.FIELD)
                .add(TargetAnchorEvidence.CARRIERS, carriers);
        query.getAsJsonArray("paths").add(path);
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        JsonArray gates = merge.getAsJsonArray("gates");
        assertFalse(gates.size() == 0);
        assertEquals(PathMergeComposer.PROPAGATION_CUT,
                gates.get(0).getAsJsonObject().get("kind").getAsString());
        assertFalse(merge.getAsJsonArray("paths").get(0).getAsJsonObject()
                .get("admitted").getAsBoolean());
        assertEquals("FINAL_REFUSED", result.manifest.get(
                ComposedManifest.FINAL_STATUS).getAsString());
    }

    /**
     * The recording minted a root and the merged formula does not mention it.
     *
     * <p>Then the solver is answering about constants.  The composition is
     * refused here rather than letting a SAT over no root travel to SOLVE and
     * come back as a statement about the finding.</p>
     */
    @Test
    public void aMintedRootOnNoPathRefusesTheComposition() throws Exception {
        Path directory = Files.createTempDirectory("path-merge-no-root");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                notEqual(constant(1), constant(0)),
                notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        JsonArray gates = merge.getAsJsonArray("gates");
        assertEquals(1, gates.size());
        assertEquals(PathMergeComposer.ROOT_NOT_ON_ANY_PATH,
                gates.get(0).getAsJsonObject().get("kind").getAsString());
        assertTrue(gates.get(0).getAsJsonObject().get("detail").getAsString()
                .contains(FIELD_SIGNATURE));
        assertEquals(0, merge.getAsJsonArray("roots").size());
        assertEquals("FINAL_REFUSED", result.manifest.get(
                ComposedManifest.FINAL_STATUS).getAsString());
    }

    /**
     * A clock read is windowed by the case's bound, and the ledger says so.
     *
     * <p>A cell minted through the clock hook is a wall-clock read by
     * construction -- the hook's declaration names the callee -- so the
     * mint row states it and the merge needs no site heuristic.  With the
     * ledger empty every clock was pinned to the one reading some replay
     * happened to take, which is exactly what a clock is not: bug3's nine
     * wall-clock cells were pinned that way and eleven of its twelve paths
     * came back unsatisfiable at every valuation, with the clock probe
     * refusing to look at all ({@code NO_CLOCK_ROOT}).</p>
     */
    @Test
    public void aTimerNowMintIsAClockReadWithTheCaseBound() throws Exception {
        Path directory = Files.createTempDirectory("path-merge-clock");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(clockSymbol(), longConstant(0L))));
        PathMergeComposer.Result result = compose(directory, query,
                clockSummary(), new String[]{"GROUP.SEED"},
                "--clock-skew-ms", "900000");

        JsonObject physics = result.manifest.getAsJsonObject(
                ClockRootPhysics.MANIFEST_FIELD);
        assertEquals(900000L,
                physics.get("clockSkewMillis").getAsLong());
        JsonArray reads = physics.getAsJsonArray("clockReads");
        assertEquals(1, reads.size());
        JsonObject read = reads.get(0).getAsJsonObject();
        assertEquals(CLOCK_PORT, read.get("portId").getAsString());
        assertEquals(CLOCK_OCCURRENCE,
                read.get("occurrenceId").getAsString());
        assertEquals(CLOCK_SITE, read.get("siteId").getAsString());
        assertEquals(CLOCK_READING, read.get("recordedValue").getAsLong());
        assertEquals("node0", read.get("sourceKey").getAsString());
        String term = read.get("solverTerm").getAsString();
        assertFalse(term.isEmpty());
        assertEquals(ClockRootPhysics.window(term, CLOCK_READING, 900000L),
                read.get("windowAssertion").getAsString());

        // The formula lets it move within that window centred on what THIS
        // execution read at the mint (observedValue), not on the recording's
        // reading the ledger states; the Boolean root beside it is still
        // exactly what the recording read.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(>= " + term + " " + (CLOCK_READING + 666L - 900000L) + ")"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(<= " + term + " " + (CLOCK_READING + 666L + 900000L) + ")"));

        boolean sawClock = false;
        for (com.google.gson.JsonElement element
                : result.manifest.getAsJsonArray(
                        ComposedManifest.RECORDED_ROOT_VALUES)) {
            JsonObject row = element.getAsJsonObject();
            if (!CLOCK_PORT.equals(row.get("portId").getAsString())) {
                assertFalse("only a clock read is a wall clock",
                        row.get("wallClock").getAsBoolean());
                continue;
            }
            sawClock = true;
            assertTrue("the clock read says it is one",
                    row.get("wallClock").getAsBoolean());
            assertEquals(Long.toString(CLOCK_READING),
                    row.get("recordedValue").getAsString());
        }
        assertTrue("the clock root is published", sawClock);
    }

    /** One replay's summary naming a wall-clock read it minted. */
    private static JsonObject clockSummary() {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", "GROUP.SEED");
        summary.addProperty("sourceKey", "node0");
        List<JsonObject> events = new ArrayList<>();
        events.add(SymbolicSourceEvidence.manualEvent(CLOCK_PORT,
                CLOCK_OCCURRENCE, "", "J", CLOCK_RAW,
                "MANUAL.clock-example", CLOCK_CALLEE, CLOCK_SITE, 42L,
                Long.toString(CLOCK_READING),
                Long.toString(CLOCK_READING + 666L)));
        SymbolicSourceEvidence.writeTo(summary, events);
        return summary;
    }

    private static JsonObject clockSymbol() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "J");
        symbol.addProperty("_exp", CLOCK_RAW);
        return symbol;
    }

    private static JsonObject longConstant(long value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", "J");
        node.addProperty("_exp", "Y_J_" + value);
        return node;
    }

    /** A root the path condition mentions is on a path, and nothing refuses. */
    @Test
    public void aRootOnOnePathConditionIsNotRefused() throws Exception {
        Path directory = Files.createTempDirectory("path-merge-root-on");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        assertEquals(1, merge.getAsJsonArray("roots").size());
    }

    // ------------------------------------------------------------------
    // Fixtures.
    // ------------------------------------------------------------------

    /**
     * The decision is in one region and the anchor in another, one replay.
     *
     * <p>A path condition is the replay's, not a region's.  HDFS-17960's one
     * root-dependent decision is taken inside {@code deleteSnapshot} and its
     * anchor is inside {@code serializeSnapshotSection}: two regions, two
     * activations, one replay.  Reading only the anchor region's conditions
     * left the root out of every pi_p and the formula constrained nothing.
     */
    @Test
    public void aDecisionInAnotherRegionOfTheReplayIsInThisPathCondition()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-cross");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                notEqual(constant(1), constant(0)),
                notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query,
                decision("GROUP.SEED", rootIs(true)));

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        assertEquals(1, merge.getAsJsonArray("roots").size());
        JsonObject path = merge.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertTrue(result.smtLib.contains(ROOT_TERM));

        // The same query without that activation: the root is in no path
        // condition at all, and the composition says so rather than
        // answering about constants.
        JsonObject bare = query();
        bare.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                notEqual(constant(1), constant(0)),
                notEqual(constant(1), constant(0))));
        PathMergeComposer.Result alone = compose(
                Files.createTempDirectory("path-merge-cross-alone"), bare);
        JsonObject withoutIt = alone.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, withoutIt.getAsJsonArray("roots").size());
        assertTrue(path.get("pathConditionTerms").getAsInt()
                > withoutIt.getAsJsonArray("paths").get(0).getAsJsonObject()
                .get("pathConditionTerms").getAsInt());
    }

    /**
     * A root no source states a value for is refused, not composed over.
     *
     * <p>The recording is what says what the program held there.  Where
     * neither the replay that minted the root nor the plan's symbolize row
     * says it, the run has a free variable and no value to call its
     * recorded one, and every statement about "the marker flipped" would be
     * measured against nothing.</p>
     */
    @Test
    public void aRootNoSourceStatesAValueForIsRefused() throws Exception {
        Path directory = Files.createTempDirectory("path-merge-unstated");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query, null,
                "GROUP.FLIP");

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        JsonArray gates = merge.getAsJsonArray("gates");
        assertEquals(1, gates.size());
        assertEquals(PathMergeComposer.RECORDED_ROOT_VALUE_UNSTATED,
                gates.get(0).getAsJsonObject().get("kind").getAsString());
        assertEquals("", merge.getAsJsonArray("roots").get(0)
                .getAsJsonObject().get("recordedValue").getAsString());
    }

    /**
     * A root exactly one replay stated is stated, and nothing is refused.
     *
     * <p>A flip replay is handed a model assignment and states no recorded
     * value; the seed that minted it does.  One reading is not a conflict,
     * and the conflict member is a list of the readings that disagreed --
     * empty here.  Publishing a boolean flag there instead made a run with
     * no conflict state "false" as a reading of its own.</p>
     */
    @Test
    public void oneReplayStatingTheValueIsEnoughAndIsNotAConflict()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-stated");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(1))));
        query.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        JsonObject root = merge.getAsJsonArray("roots").get(0)
                .getAsJsonObject();
        assertEquals("true", root.get("recordedValue").getAsString());
        assertEquals("", root.get("recordedValueConflict").getAsString());
    }

    /** One other activation of a replay, with one decision of its own. */
    private static JsonObject decision(String group, JsonObject condition) {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", group);
        summary.addProperty("regionId", "REGION.other");
        summary.addProperty("occurrenceId",
                "node0/region/REGION.other#1#a1");
        JsonArray conditions = new JsonArray();
        conditions.add(condition);
        summary.add("pathCondition", conditions);
        return summary;
    }

    /**
     * The laneBF shape: two anchored occurrences of the target, and one of
     * them whose path worklist never closed, so EXPLORE published no exact
     * reach query for it at all.  That anchor has no path, which is
     * TARGET_NOT_REACHED about that occurrence; it is not a reason for the
     * run to fail, and the sibling occurrence's own composition is
     * untouched by it.
     */
    @Test
    public void anAnchorWithNoReachQueryIsRefusedNotFailed()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-no-query");
        Path summaries = directory.resolve("summaries.jsonl");
        write(summaries, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(summary("GROUP.SEED"))) + "\n");
        Path absent = directory.resolve("reach_query.jsonl");
        assertFalse("the fixture must not publish a reach query",
                Files.exists(absent));
        PathMergeComposer.Arguments arguments =
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", absent.toString(),
                        "--summaries", summaries.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString(),
                        "--occurrence-id",
                        "node0/region/REGION.example#2"});
        PathMergeComposer.Result result =
                PathMergeComposer.compose(arguments);
        assertEquals("FINAL_REFUSED", JsonFields.optionalString(
                result.manifest, ComposedManifest.FINAL_STATUS));
        List<String> refusals = new ArrayList<>();
        for (com.google.gson.JsonElement row
                : result.manifest.getAsJsonArray("finalStatusRefusals")) {
            refusals.add(JsonFields.optionalString(
                    row.getAsJsonObject(), "kind"));
        }
        assertEquals(java.util.Collections.singletonList(
                PathMergeComposer.TARGET_NOT_REACHED), refusals);
    }

    /**
     * HDFS-17960's shape: the root reaches the target by control flow only.
     *
     * <p>The target branch is {@code i != sm.getNumSnapshots()} -- two
     * concrete ints, no symbol in it -- and the root reaches it only through
     * control dependence: on the ordered arm an early return skips the
     * decrement, so the count differs.  The evidence is therefore the pair of
     * paths, not a symbolic predicate: the seed holds the root at its
     * recorded value and its phi is false; the flip negates the root and its
     * phi is true.  Both phis are constants, and the replay declares tracked
     * carriers, which is the case a literal-over-carriers cut used to refuse.
     * A path whose pi depends on a root is admissible whatever its phi is
     * made of, and the disjunction must be satisfiable exactly where the
     * root is flipped.</p>
     */
    @Test
    public void aConcreteFatalPredicateOnARootDependentPathIsAdmitted()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-concrete-phi");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(carrierPath("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(1))));
        query.getAsJsonArray("paths").add(carrierPath("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(2))));

        PathMergeComposer.Result result = compose(directory, query);

        JsonArray paths = result.manifest.getAsJsonObject("pathMerge")
                .getAsJsonArray("paths");
        assertEquals(2, paths.size());
        for (com.google.gson.JsonElement row : paths) {
            JsonObject path = row.getAsJsonObject();
            assertTrue("a root-dependent path with a concrete phi was cut: "
                            + path,
                    JsonFields.optionalBool(path, "admitted", false));
        }
        assertEquals("FINAL_READY", JsonFields.optionalString(
                result.manifest, ComposedManifest.FINAL_STATUS));
        assertEquals("the flipped root must satisfy the disjunction",
                "sat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                        + " false))\n(check-sat)\n"));
        assertEquals("the recorded root must not satisfy it",
                "unsat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                        + " true))\n(check-sat)\n"));
    }

    /** A path whose replay declared tracked carriers, as a real one does. */
    private static JsonObject carrierPath(String caseId, String group,
                                          JsonObject pathCondition,
                                          JsonObject fatalPredicate) {
        JsonObject path = new JsonObject();
        path.addProperty(LocalCaseIdentity.FIELD, "LOCAL_CASE." + caseId);
        path.addProperty("replayGroupId", group);
        path.addProperty("occurrenceId",
                "node0/region/REGION.example#1#a1");
        path.addProperty("topologyEpoch", "iteration-0000");
        path.addProperty("pathSetClosed", true);
        JsonArray constraints = new JsonArray();
        constraints.add(pathCondition);
        constraints.add(fatalPredicate);
        path.add("constraints", constraints);
        path.add(TargetAnchorEvidence.FIELD, TargetAnchorEvidence.build(
                SITE, 1, "node0", "REGION.example",
                "node0/region/REGION.example#1#a1", "iteration-0000",
                false, false, constraints, new JsonObject(),
                new ArrayList<JsonObject>(),
                Arrays.asList("INSTANCE_FIELD\n9\n56")));
        return path;
    }

    private static final String HANDOFF_SYMBOL =
            PathMergeComposer.HANDOFF_SYMBOL_MARK + "PORT_KEY_1";

    /**
     * A value that crossed a wire is a free variable joined at the handoff.
     *
     * <p>The consumer's fatal predicate is over {@code v_H}, not over the
     * producer's term inlined into it, so a consumer flip needed no producer
     * replay.  What ties {@code v_H} to the world is the family published at
     * that one handoff occurrence: two producer replays delivered there,
     * each with its own root-dependent prefix, and the formula says the
     * received value is one of them under the conditions that produced it.
     * The whole thing is satisfiable exactly where the root is flipped --
     * the producer that delivers the fatal value is the one whose prefix
     * needs the flip.</p>
     */
    @Test
    public void aHandoffValueIsJoinedByItsFamilyNotByInlining()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-handoff");
        JsonObject query = query();
        // The consumer decided the anchor both ways, over v_H alone.
        // Each path accepts the delivery its own replay made: the seed
        // received 9 and its predicate is false there, the flip received 7
        // and its predicate is true there.
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));
        query.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));

        JsonObject producerSeed = summary("GROUP.SEED");
        producerSeed.add("vmHandoffEvents",
                handoffEvents(constant(9), 11L, 12L));
        JsonObject producerFlip = summary("GROUP.FLIP");
        producerFlip.add("vmHandoffEvents",
                handoffEvents(constant(7), 21L, 22L));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(producerSeed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(producerFlip)) + "\n");
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));
        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);

        JsonArray families = merge.getAsJsonArray("handoffFamilies");
        assertEquals(1, families.size());
        assertEquals(HANDOFF_SYMBOL, families.get(0).getAsJsonObject()
                .get("handoffSymbol").getAsString());
        for (com.google.gson.JsonElement row : merge.getAsJsonArray("paths")) {
            assertTrue("a path over a handoff value was cut: " + row,
                    JsonFields.optionalBool(row.getAsJsonObject(),
                            "admitted", false));
        }
        // The row declares the variable: its Java type says how to lower it
        // (one variable, one sort) and its recorded value travels with it,
        // so nothing meets an undeclared free symbol and cuts.
        JsonArray declared = result.manifest.getAsJsonArray(
                ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        boolean found = false;
        for (com.google.gson.JsonElement row : declared) {
            if (HANDOFF_SYMBOL.equals(JsonFields.optionalString(
                    row.getAsJsonObject(), "rawSymbol"))) {
                found = true;
                assertEquals("I", JsonFields.optionalString(
                        row.getAsJsonObject(), "javaType"));
            }
        }
        assertTrue("the handoff variable must be declared", found);
        assertEquals("the family must let the fatal delivery through",
                "sat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                        + " false))\n(check-sat)\n"));
    }

    /**
     * A delivery is available only under the valuation that produced it.
     *
     * <p>Two producer replays deliver different values at one handoff: the
     * seed ran with the marker at its recorded polarity and delivered 9, the
     * flip replay ran with the marker moved and delivered 7.  The consumer's
     * fatal predicate is over v_H alone, so without the guard the family is
     * a menu and the recorded polarity can help itself to the flip replay's
     * delivery.  With each arm carrying the valuation its replay ran under,
     * the recorded polarity has only its own delivery available.</p>
     */
    @Test
    public void aDeliveryIsAvailableOnlyUnderTheValuationThatProducedIt()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-guard");
        JsonObject query = query();
        // The consumer's predicate is false on the seed's delivery (9) and
        // true on the flip replay's (7), so the failure is reachable only
        // where that delivery is available.
        // The fatal path is the flip replay's: it ran with the marker
        // moved and received the delivery its consumer fails on.
        query.getAsJsonArray("paths").add(path("only", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));

        JsonObject seed = ranAt("GROUP.SEED", "true");
        seed.add("vmHandoffEvents", handoffEvents(constant(9), 11L, 12L));
        JsonObject flip = ranAt("GROUP.FLIP", "false");
        flip.add("vmHandoffEvents", handoffEvents(constant(7), 21L, 22L));

        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(seed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(flip)) + "\n");
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));

        // The seed replay states the marker at true, the flip at false, so
        // each arm is guarded by the polarity that produced its delivery.
        assertTrue("the family must carry the delivering valuation",
                result.smtLib.contains(ROOT_TERM));
        // At the recorded polarity only the seed's own delivery is
        // available, and the consumer does not fail on it.
        assertEquals("the recorded polarity must not reach the failure",
                "unsat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                        + " true))\n(check-sat)\n"));
        // Move the marker and the flip replay's delivery becomes available,
        // which is the delivery the consumer fails on.
        assertEquals("the flipped polarity reaches it",
                "sat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                        + " false))\n(check-sat)\n"));
    }

    /**
     * A delivery is unavailable at a root the delivering replay moved, even
     * when that root is not a fault marker.
     *
     * <p>The two replays ran at different serial numbers, and only the one
     * that ran at the flipped serial delivered the value the consumer fails
     * on.  A domain pins that root to what the recording read, so the arm
     * guard must carry the delivering replay's own value of it: without
     * that conjunct the fatal delivery is available at the recorded
     * valuation and the composition claims a failure no execution made.</p>
     */
    @Test
    public void aDeliveryUnderAFlippedConfiguredRootIsUnavailable()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-serial");
        JsonObject query = query();
        // The consumer fails only on the 7 the flipped replay delivered.
        query.getAsJsonArray("paths").add(path("only", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));

        // Recorded first: the inventory's recorded value, and the domain,
        // are the seed's 119982.
        assertEquals("the fatal delivery was made at a serial the domain"
                        + " does not allow", "unsat",
                solve(serialComposition(directory, queryFile,
                        "119982", "119981").smtLib));
        // The same shapes with nothing varied: the delivery is available,
        // so the guard, not the fixture, is what refused it above.
        assertEquals("with no varied root the delivery is available", "sat",
                solve(serialComposition(directory, queryFile,
                        "119982", "119982").smtLib));
    }

    /**
     * A replay's own reading counts wherever the runtime publishes it.
     *
     * <p>Mint evidence carries the seeding activation's reading alone: a
     * replay that only re-read the root publishes it as a manual symbolic
     * input observation.  Judging variation from the mint member alone said
     * "one value" about a root two replays read two ways, and the valuation
     * guard -- whose whole filter is that judgement -- then constrained
     * nothing.</p>
     */
    @Test
    public void aReadingPublishedAsAManualObservationStillVaries()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-manual");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("only", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));

        JsonObject seed = ranWithSerial("GROUP.SEED", "119982");
        seed.add("vmHandoffEvents", handoffEvents(constant(9), 11L, 12L));
        // The flip replay states its serial only on the manual member.
        JsonObject flip = new JsonObject();
        flip.addProperty("replayGroupId", "GROUP.FLIP");
        flip.addProperty("summaryId", "GROUP.FLIP");
        flip.add("vmHandoffEvents", handoffEvents(constant(7), 21L, 22L));
        JsonArray observations = new JsonArray();
        JsonObject observed = SymbolicSourceEvidence.manualEvent(
                "PORT.serial", "node0/region/REGION.source#1#a1",
                SERIAL_SIGNATURE, "I", RAW_SERIAL, SERIAL_TERM);
        observed.addProperty("recordedValue", "119981");
        observations.add(observed);
        flip.add("manualSymbolicInputObservations", observations);

        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(seed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(flip)) + "\n");
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));
        assertEquals("the delivery was made at a serial the domain does not"
                + " allow", "unsat", solve(result.smtLib));
    }

    /**
     * A clock read is carried as this execution's window, not as a value.
     *
     * <p>Every execution reads the wall clock fresh, so a clock cell is not
     * an assignment its replay ran under and pinning it to one reading
     * contradicts every other replay's decisions over it.  What a path owes
     * is the case's declared skew around the instant THIS execution read.
     * Keyed on the mint row's own declaration -- the callee the hook named
     * -- and on nothing about the site.</p>
     */
    @Test
    public void aClockReadIsCarriedAsThisExecutionsWindow() {
        JsonObject summary = ranWithSerial("GROUP.FLIP", "119981");
        Map<String, JsonObject> declared = new LinkedHashMap<>();
        declared.put(RAW_SERIAL, SymbolicSourceEvidence.eventsOf(summary)
                .get(0));
        PathMergeComposer.RootInventory roots =
                PathMergeComposer.RootInventory.of(Arrays.asList(
                        ranWithSerial("GROUP.SEED", "119982"), summary));
        PathMergeLowering lowering = new PathMergeLowering(declared);

        List<String> valued = PathMergeComposer.deliveringValuation(
                summary, declared, lowering, roots, 300000L);
        assertEquals("a root no hook calls a clock is one equality",
                1, valued.size());
        assertTrue("and it is an equality: " + valued.get(0),
                valued.get(0).contains("=")
                        && !valued.get(0).contains(">="));

        JsonObject clock = clockReading("1789361019285");
        JsonObject clocked = new JsonObject();
        clocked.addProperty("replayGroupId", "GROUP.FLIP");
        clocked.addProperty("summaryId", "GROUP.FLIP");
        JsonArray rows = new JsonArray();
        rows.add(clock);
        clocked.add("manualSymbolicInputObservations", rows);
        Map<String, JsonObject> withClock = new LinkedHashMap<>();
        withClock.put(RAW_CLOCK, clock);
        List<String> windowed = PathMergeComposer.deliveringValuation(
                clocked, withClock, new PathMergeLowering(withClock),
                null, 300000L);
        assertEquals("a declared clock read is one window",
                1, windowed.size());
        assertTrue("centred on what THIS execution read, +/- the skew: "
                        + windowed.get(0),
                windowed.get(0).contains(" 1789360719285)")
                        && windowed.get(0).contains(" 1789361319285))")
                        && windowed.get(0).startsWith("(and (>= "));
    }

    /**
     * A path that contradicts its own execution is named, not composed.
     *
     * <p>The invariant: a path must be satisfiable as the execution that
     * made it -- that replay's roots as it read them, its clock cells in its
     * own window, the deliveries it received.  One that is not says the
     * composition has mis-stated that execution, so every answer it
     * contributes is about the mis-statement; it is refused by name with the
     * conjunct that closes it.</p>
     */
    @Test
    public void aPathThatContradictsItsOwnReplayIsRefusedByName()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-self");
        JsonObject query = query();
        // The replay read the marker false; this path's own condition says
        // it was true.
        query.getAsJsonArray("paths").add(path("self", "GROUP.FLIP",
                rootIs(true), notEqual(constant(1), constant(0))));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(ranAt("GROUP.SEED", "true")))
                + "\n" + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(ranAt("GROUP.FLIP", "false")))
                + "\n");
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--z3", "z3",
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertTrue("the refusal names the invariant",
                merge.getAsJsonArray("gates").toString()
                        .contains(PathMergeComposer.PATH_NOT_SELF_CONSISTENT));
        assertFalse("and the path is not composed",
                merge.getAsJsonArray("paths").get(0).getAsJsonObject()
                        .get("admitted").getAsBoolean());
    }

    /**
     * A handoff variable is not a root, and its family says what it is.
     *
     * <p>Two things the artifact must state for a witness to be read
     * through the family rather than against one replay's delivery: the
     * variable carries its handoff phase, so no reader mistakes it for a
     * root with a recorded value; and each arm names the replay that
     * delivered it and the valuation that replay ran under, which is the
     * mechanism behind taking that arm.</p>
     */
    @Test
    public void aHandoffVariableCarriesItsPhaseAndItsArmsTheirReplays()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-arms");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("only", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));
        JsonObject seed = ranAt("GROUP.SEED", "true");
        seed.add("vmHandoffEvents", handoffEvents(constant(9), 11L, 12L));
        JsonObject flip = ranAt("GROUP.FLIP", "false");
        flip.add("vmHandoffEvents", handoffEvents(constant(7), 21L, 22L));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(seed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(flip)) + "\n");
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));

        boolean phased = false;
        for (com.google.gson.JsonElement row : result.manifest
                .getAsJsonArray(ComposedManifest
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD)) {
            if (!HANDOFF_SYMBOL.equals(JsonFields.optionalString(
                    row.getAsJsonObject(), "rawSymbol"))) {
                continue;
            }
            phased = !JsonFields.optionalString(row.getAsJsonObject(),
                    InSessionReadResolver.HANDOFF_PHASE_ID).isEmpty();
        }
        assertTrue("the handoff variable carries its phase, so no reader"
                + " measures it against a recorded value", phased);
        JsonObject family = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD)
                .getAsJsonArray("handoffFamilies").get(0).getAsJsonObject();
        assertFalse("the family names the variable it constrains",
                JsonFields.optionalString(family, "handoffSolverTerm")
                        .isEmpty());
        JsonArray arms = family.getAsJsonArray("arms");
        assertEquals("one arm per delivering replay", 2, arms.size());
        for (com.google.gson.JsonElement element : arms) {
            JsonObject arm = element.getAsJsonObject();
            assertFalse("an arm names its replay",
                    JsonFields.optionalString(arm, "replayGroupId")
                            .isEmpty());
            assertEquals("and the valuation that replay ran under", 1,
                    arm.getAsJsonArray("valuation").size());
        }
    }

    /**
     * The mint row is the declaration, so the root row states what it says.
     *
     * <p>A clock cell's mint row carries the port it was read on, the callee
     * the hook declared and the instant this execution read. The composer
     * used to rebuild a declaration from a few of its members and install
     * that over the row, which dropped the port and the callee -- so every
     * clock root came out {@code wallClock false} and no composition listed
     * a clock read at all.</p>
     */
    @Test
    public void aClockMintRowDeclaresItsRootPortAndCallee() throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-decl");
        JsonObject query = query();
        JsonObject clock = new JsonObject();
        clock.addProperty("_type", "SymbolExpression");
        clock.addProperty("_java_type", "J");
        clock.addProperty("_exp", RAW_CLOCK);
        query.getAsJsonArray("paths").add(path("clock", "GROUP.FLIP",
                notEqual(clock, constant(0)),
                notEqual(constant(1), constant(0))));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));

        JsonObject seed = summary("GROUP.SEED");
        JsonObject flip = summary("GROUP.FLIP");
        JsonArray rows = new JsonArray();
        rows.add(clockReading("1789361019285"));
        flip.add("manualSymbolicInputObservations", rows);
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(seed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(flip)) + "\n");

        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--clock-skew-ms", "300000",
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));

        JsonObject root = null;
        for (com.google.gson.JsonElement row : result.manifest
                .getAsJsonArray(ComposedManifest
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD)) {
            if (RAW_CLOCK.equals(JsonFields.optionalString(
                    row.getAsJsonObject(), "rawSymbol"))) {
                root = row.getAsJsonObject();
            }
        }
        assertTrue("the clock root is materialized", root != null);
        assertEquals("PORT.now",
                JsonFields.optionalString(root, "portId"));
        assertEquals("<org.apache.hadoop.util.Timer: long now()>",
                JsonFields.optionalString(root,
                        SymbolicSourceEvidence.DECLARED_CALLEE));
        JsonObject physics = result.manifest.getAsJsonObject(
                ClockRootPhysics.MANIFEST_FIELD);
        assertEquals("and the manifest lists it as a clock read", 1,
                physics.getAsJsonArray("clockReads").size());
        assertTrue("the formula windows it around this reading",
                result.smtLib.contains("1789360719285")
                        && result.smtLib.contains("1789361319285"));
    }

    /** One replay's reading of a cell the clock hook minted. */
    private static JsonObject clockReading(String reading) {
        JsonObject row = SymbolicSourceEvidence.manualEvent("PORT.now",
                "node0/region/REGION.source#1#a1", CLOCK_SIGNATURE, "J",
                RAW_CLOCK, CLOCK_TERM,
                "<org.apache.hadoop.util.Timer: long now()>",
                "<com.example.Service: void serve()>#u3", 11L, reading,
                reading);
        return row;
    }

    /**
     * Membership is read off the base the VM walked, not left to the solver.
     *
     * <p>An INITIAL publishes the container it began from as
     * {@code SNAPSHOT_BASE} with one {@code PUT} per entry it walked, so
     * whether the map held a key is a recorded fact and the read's answer
     * follows from the chain.  A chain that reaches no such base states no
     * membership: lowering that as a free "does this opaque state hold the
     * key" let a witness decide it, so it is refused instead.</p>
     */
    @Test
    public void membershipComesFromTheWalkedBaseOrIsRefused()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-base");
        JsonObject walked = query();
        walked.getAsJsonArray("paths").add(path("base", "GROUP.FLIP",
                rootIs(false),
                notEqual(mapRead(reconstructedMap(), 119980), constant(0))));
        PathMergeComposer.Result decided = compose(directory, walked);
        assertEquals("a membership the base decides is no gate", 0,
                decided.manifest.getAsJsonObject(
                        PathMergeComposer.MANIFEST_FIELD)
                        .getAsJsonArray("gates").size());

        Path other = Files.createTempDirectory("path-merge-nobase");
        JsonObject unwalked = query();
        unwalked.getAsJsonArray("paths").add(path("nobase", "GROUP.FLIP",
                rootIs(false),
                notEqual(mapRead(mapState(), 119980), constant(0))));
        PathMergeComposer.Result refused = compose(other, unwalked);
        assertTrue("a membership nothing decides is refused by name",
                refused.manifest.getAsJsonObject(
                        PathMergeComposer.MANIFEST_FIELD)
                        .getAsJsonArray("gates").toString()
                        .contains("CONTAINER_BASE_UNSTATED"));
    }

    /**
     * A symbolic PUT key makes the key it equals present.
     *
     * <p>Membership is the assoc model's answer over the whole chain, not a
     * list of the chain's constant keys.  bug3's block-key map is put with
     * the received key's own id -- a symbolic key -- so a syntactic list
     * declared 119982 absent while the chain, under any model where that id
     * is 119982, holds it, and every execution that read it there became
     * unstatable.</p>
     */
    @Test
    public void aSymbolicPutKeyMakesTheKeyItEqualsPresent()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-symkey");
        JsonObject query = query();
        // The map's only entry is put under the value that arrived, and the
        // read asks for that same value.
        JsonObject base = containerRelation("SNAPSHOT_BASE", mapState());
        JsonObject put = containerRelation("PUT", base);
        put.getAsJsonArray("arguments").add(handoff());
        put.getAsJsonArray("arguments").add(constant(5));
        query.getAsJsonArray("paths").add(path("symkey", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(mapReadAtHandoff(put), constant(5))));
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        JsonObject seed = ranAt("GROUP.SEED", "true");
        seed.add("vmHandoffEvents", handoffEvents(constant(9), 11L, 12L));
        JsonObject flip = ranAt("GROUP.FLIP", "false");
        flip.add("vmHandoffEvents", handoffEvents(constant(7), 21L, 22L));
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(seed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(flip)) + "\n");
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()}));

        assertFalse("no absent-key default survives",
                result.smtLib.contains("absent_key_default"));
        // The read asks the map for the very value the PUT stored under, so
        // it answers 5 and the fatal predicate -- "it is not 5" -- cannot
        // hold.  A syntactic key list would have called the key absent, the
        // read null, and this satisfiable.
        assertEquals("the symbolic key is present, so the read is not null",
                "unsat", solve(result.smtLib));
    }

    /** A read of {@code chain} at the value that arrived over the wire. */
    private static JsonObject mapReadAtHandoff(JsonObject chain) {
        JsonObject read = containerRelation("READ", chain);
        read.addProperty("_java_type", "I");
        read.getAsJsonArray("arguments").add(handoff());
        return read;
    }

    /** The map as the VM's INITIAL publishes it: a base and its entries. */
    private static JsonObject reconstructedMap() {
        JsonObject base = containerRelation("SNAPSHOT_BASE", mapState());
        JsonObject first = containerRelation("PUT", base);
        first.getAsJsonArray("arguments").add(constant(119981));
        first.getAsJsonArray("arguments").add(constant(7));
        JsonObject second = containerRelation("PUT", first);
        second.getAsJsonArray("arguments").add(constant(119980));
        second.getAsJsonArray("arguments").add(constant(9));
        return second;
    }

    /** The same map with nothing stating what it began with. */
    private static JsonObject mapState() {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "java/util/Map");
        identity.addProperty("_exp", "MAP_STATE.v1.example");
        return containerRelation("STATE", identity);
    }

    private static JsonObject mapRead(JsonObject chain, int key) {
        JsonObject read = containerRelation("READ", chain);
        read.addProperty("_java_type", "I");
        read.getAsJsonArray("arguments").add(constant(key));
        return read;
    }

    private static JsonObject containerRelation(String operation,
                                                JsonObject receiver) {
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", "ContainerRelation");
        relation.addProperty("_java_type", "L");
        relation.addProperty("shape", "ASSOCIATIVE");
        relation.addProperty("operation", operation);
        relation.add("receiver", receiver);
        relation.add("arguments", new JsonArray());
        return relation;
    }

    /** Two replays of one handoff, each stating the serial it ran at. */
    private static PathMergeComposer.Result serialComposition(
            Path directory, Path queryFile, String seedSerial,
            String flipSerial) throws IOException {
        JsonObject seed = ranWithSerial("GROUP.SEED", seedSerial);
        seed.add("vmHandoffEvents", handoffEvents(constant(9), 11L, 12L));
        JsonObject flip = ranWithSerial("GROUP.FLIP", flipSerial);
        flip.add("vmHandoffEvents", handoffEvents(constant(7), 21L, 22L));
        Path summaryFile = directory.resolve(
                "summaries-" + seedSerial + "-" + flipSerial + ".jsonl");
        write(summaryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(seed)) + "\n"
                + JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(flip)) + "\n");
        return PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output", directory.resolve(
                                "candidate-" + seedSerial + "-" + flipSerial
                                        + ".smt2").toString(),
                        "--manifest", directory.resolve(
                                "manifest-" + seedSerial + "-" + flipSerial
                                        + ".json").toString()}));
    }

    /** One replay's summary, stating the serial number it ran under. */
    private static JsonObject ranWithSerial(String group, String serial) {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", group);
        summary.addProperty("summaryId", group);
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", RAW_SERIAL);
        List<JsonObject> events = new ArrayList<>();
        events.add(SymbolicSourceEvidence.event(SERIAL_PHASE, SERIAL_SOURCE,
                "node0/region/REGION.source#1#a1", SERIAL_SIGNATURE,
                symbol, 1, false, SERIAL_TERM, serial));
        SymbolicSourceEvidence.writeTo(summary, events);
        return summary;
    }

    /** One replay's summary, stating the marker polarity it ran under. */
    private static JsonObject ranAt(String group, String polarity) {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", group);
        List<JsonObject> events = new ArrayList<>();
        events.add(SymbolicSourceEvidence.event(PHASE, SOURCE,
                "node0/region/REGION.source#1#a1", FIELD_SIGNATURE,
                rootSymbol(), 1, false, ROOT_TERM, polarity));
        SymbolicSourceEvidence.writeTo(summary, events);
        return summary;
    }

    /** The solver term the composition gave the handoff variable. */
    private static String handoffTerm(PathMergeComposer.Result result) {
        for (com.google.gson.JsonElement row : result.manifest
                .getAsJsonArray(ComposedManifest
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD)) {
            if (HANDOFF_SYMBOL.equals(JsonFields.optionalString(
                    row.getAsJsonObject(), "rawSymbol"))) {
                return JsonFields.optionalString(row.getAsJsonObject(),
                        "solverTerm");
            }
        }
        throw new IllegalStateException("no handoff materialization");
    }

    /** The consumer's view of the value that arrived: one free variable. */
    private static JsonObject handoff() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", HANDOFF_SYMBOL);
        return symbol;
    }

    /** One replay's row at the one handoff occurrence, with what it sent. */
    private static JsonArray handoffEvents(JsonObject delivered,
                                           long export, long attach) {
        JsonObject event = new JsonObject();
        event.addProperty("kind", "VM_HANDOFF_EVENT");
        event.addProperty("portId", "PORT.key");
        event.addProperty("exportEventId", export);
        event.addProperty("attachEventId", attach);
        event.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID,
                "HANDOFF_PHASE.key");
        event.addProperty(InSessionReadResolver.HANDOFF_SYMBOL,
                HANDOFF_SYMBOL);
        event.addProperty("javaType", "I");
        event.addProperty("recordedValue", "9");
        event.add("expression", delivered);
        JsonArray events = new JsonArray();
        events.add(event);
        return events;
    }

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query)
            throws IOException {
        return compose(directory, query, null);
    }

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query,
                                                    JsonObject extra)
            throws IOException {
        return compose(directory, query, extra, "GROUP.SEED", "GROUP.FLIP");
    }

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query,
                                                    JsonObject extra,
                                                    String... groups)
            throws IOException {
        return compose(directory, query, extra, groups, new String[0]);
    }

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query,
                                                    JsonObject extra,
                                                    String[] groups,
                                                    String... extraArguments)
            throws IOException {
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        Path summaries = directory.resolve("summaries.jsonl");
        StringBuilder rows = new StringBuilder();
        for (String group : groups) {
            rows.append(JsonFields.WRITER.toJson(
                    SharedExpressionTable.compact(summary(group))))
                    .append('\n');
        }
        if (extra != null) {
            rows.append(JsonFields.WRITER.toJson(
                    SharedExpressionTable.compact(extra))).append('\n');
        }
        write(summaries, rows.toString());
        List<String> line = new ArrayList<>(Arrays.asList(
                "--fatal-query", queryFile.toString(),
                "--summaries", summaries.toString(),
                "--output", directory.resolve("candidate.smt2").toString(),
                "--manifest", directory.resolve("manifest.json").toString()));
        line.addAll(Arrays.asList(extraArguments));
        return PathMergeComposer.compose(PathMergeComposer.Arguments.parse(
                line.toArray(new String[0])));
    }

    private static JsonObject query() {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 2);
        query.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        query.addProperty("regionId", "REGION.example");
        query.addProperty("occurrenceId", "node0/region/REGION.example#1");
        query.addProperty("sourceKey", "node0");
        query.addProperty("targetSiteId", SITE);
        query.addProperty("targetOccurrence", 1);
        query.addProperty("requiredTakenOutcome", false);
        query.add("paths", new JsonArray());
        return query;
    }

    /** One replay's row: its path condition and its fatal predicate. */
    private static JsonObject path(String caseId, String group,
                                   JsonObject pathCondition,
                                   JsonObject fatalPredicate) {
        JsonObject path = new JsonObject();
        path.addProperty(LocalCaseIdentity.FIELD, "LOCAL_CASE." + caseId);
        path.addProperty("replayGroupId", group);
        path.addProperty("occurrenceId",
                "node0/region/REGION.example#1#a1");
        path.addProperty("topologyEpoch", "iteration-0000");
        path.addProperty("pathSetClosed", true);
        JsonArray constraints = new JsonArray();
        constraints.add(pathCondition);
        constraints.add(fatalPredicate);
        path.add("constraints", constraints);
        path.add(TargetAnchorEvidence.FIELD, TargetAnchorEvidence.build(
                SITE, 1, "node0", "REGION.example",
                "node0/region/REGION.example#1#a1", "iteration-0000",
                false, false, constraints, new JsonObject(),
                new ArrayList<JsonObject>(), new ArrayList<String>()));
        return path;
    }

    /** One replay's summary: the root inventory and what it recorded. */
    private static JsonObject summary(String group) {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", group);
        List<JsonObject> events = new ArrayList<>();
        events.add(SymbolicSourceEvidence.event(PHASE, SOURCE,
                "node0/region/REGION.source#1#a1", FIELD_SIGNATURE,
                rootSymbol(), 1, false, ROOT_TERM,
                "GROUP.SEED".equals(group) ? "true" : null));
        SymbolicSourceEvidence.writeTo(summary, events);
        return summary;
    }

    private static JsonObject rootSymbol() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Z");
        symbol.addProperty("_exp", RAW_ROOT);
        return symbol;
    }

    private static JsonObject rootIs(boolean value) {
        JsonObject symbol = rootSymbol();
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", "Z");
        constant.addProperty("_exp", value ? "Y_Z_1" : "Y_Z_0");
        return binary("==", symbol, constant);
    }

    private static JsonObject notEqual(JsonObject left, JsonObject right) {
        return binary("!=", left, right);
    }

    private static JsonObject binary(String operator, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", operator);
        node.add("_left", left);
        node.add("_right", right);
        return node;
    }

    private static JsonObject constant(int value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", "I");
        node.addProperty("_exp", "Y_I_" + value);
        return node;
    }

    private static void write(Path path, String body) throws IOException {
        Files.write(path, body.getBytes(StandardCharsets.UTF_8));
    }

    // ------------------------------------------------------------------
    // z3.
    // ------------------------------------------------------------------

    private static String solve(String query) throws Exception {
        Process process = new ProcessBuilder("z3", "-in", "-smt2")
                .redirectErrorStream(true).start();
        try (Writer input = new OutputStreamWriter(
                process.getOutputStream(), StandardCharsets.UTF_8)) {
            input.write(query);
        }
        String last = "";
        try (BufferedReader output = new BufferedReader(
                new InputStreamReader(process.getInputStream(),
                        StandardCharsets.UTF_8))) {
            String line;
            while ((line = output.readLine()) != null) {
                if (!line.trim().isEmpty()) last = line.trim();
            }
        }
        process.waitFor();
        return last;
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor()
                    == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
