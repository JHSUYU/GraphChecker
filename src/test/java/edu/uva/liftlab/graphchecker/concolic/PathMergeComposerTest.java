package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.TargetAnchorEvidence;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

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
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * The merge, on three recordings small enough to read.
 *
 * <p>One root, one anchored target, paths differing only in what the root
 * made their fatal predicate: the disjunction is satisfiable exactly where
 * some path is, and the gates refuse rather than guess.</p>
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
    private static final String HANDOFF_SYMBOL =
            PathMergeComposer.HANDOFF_SYMBOL_MARK + "PORT_KEY_1";
    private static final String LOOP_OCCURRENCE =
            "app/nn0#epoch0/region/REGION.a#1";
    private static final String LOOP_SITE = "<C: void m()>#u7";

    /**
     * Fatal_T is OR_p (pi_p AND phi_p): satisfiable exactly where some path's
     * own condition is, and nowhere else.
     *
     * <p>Two replays of one site: the seed the root kept healthy and the flip
     * the root made fatal.  The second row is HDFS-17960's shape -- the root
     * reaches the target by control flow, so both fatal predicates are
     * concrete and carriers are declared: a path whose pi depends on a root
     * is admissible whatever its phi is made of.</p>
     */
    @Test
    public void theDisjunctionIsSatisfiableExactlyWhereSomePathIs()
            throws Exception {
        // One notion, one implementation: the composer and the path-flip
        // solver lower a recorded VM expression through the same core, so
        // the arms where they once disagreed cannot come back.
        assertSame(VmLoweringCore.class,
                PathMergeLowering.class.getSuperclass());
        assertSame(VmLoweringCore.class, Class.forName(
                "edu.uva.liftlab.graphchecker.concolic"
                        + ".ConcolicConstraintSolver$Encoder").getSuperclass());
        Assume.assumeTrue(z3Available());
        JsonObject plain = query();
        plain.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(1))));
        plain.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(0))));
        List<String> carriers = Arrays.asList("INSTANCE_FIELD\n9\n56");
        JsonObject concrete = query();
        concrete.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(1)), carriers));
        concrete.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(2)), carriers));

        for (JsonObject merged : Arrays.asList(plain, concrete)) {
            PathMergeComposer.Result result = compose(
                    Files.createTempDirectory("path-merge-flip"), merged);
            assertEquals(2, paths(result).size());
            for (JsonElement row : paths(result)) {
                assertTrue("a root-dependent path was cut: " + row,
                        JsonFields.optionalBool(row.getAsJsonObject(),
                                "admitted", false));
            }
            assertEquals("FINAL_READY", JsonFields.optionalString(
                    result.manifest, ComposedManifest.FINAL_STATUS));
            assertTrue(result.smtLib.contains(ROOT_TERM));

            // The root must be free, and free only where the flip put it.
            assertEquals("sat", solve(result.smtLib));
            assertEquals("the flipped root must satisfy the disjunction",
                    "sat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                            + " false))\n(check-sat)\n"));
            assertEquals("the recorded root must not satisfy it",
                    "unsat", solve(result.smtLib + "(assert (= " + ROOT_TERM
                            + " true))\n(check-sat)\n"));
        }

        // The healthy recording alone: the site executed, so the target is
        // reached, and the failure is not reachable from what it showed.
        JsonObject healthy = query();
        healthy.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(2), constant(2))));
        PathMergeComposer.Result alone = compose(
                Files.createTempDirectory("path-merge-healthy"), healthy);

        assertEquals(0, gates(alone).size());
        assertEquals(1, alone.manifest.getAsJsonArray(
                "targetReachLedger").size());
        assertTrue(paths(alone).get(0).getAsJsonObject()
                .get("admitted").getAsBoolean());
        assertEquals("unsat", solve(alone.smtLib));
    }

    /**
     * Where a value is missing the composition names it; where the evidence
     * is there, nothing is refused.
     *
     * <p>Each row is a gate the merge owes the stages after it -- a root no
     * path mentions, a root no source values, a literal predicate, a
     * membership no walked base decides, an undeclared loop -- each beside
     * the same shape with the evidence present.</p>
     */
    @Test
    public void aMissingValueIsNamedRatherThanComposedOver() throws Exception {
        JsonObject offPath = path("seed", "GROUP.SEED",
                notEqual(constant(1), constant(0)),
                notEqual(constant(1), constant(0)));
        PathMergeComposer.Result minted =
                composed("path-merge-no-root", offPath);
        JsonArray refused = gates(minted);
        assertEquals(1, refused.size());
        assertEquals(PathMergeComposer.ROOT_NOT_ON_ANY_PATH,
                refused.get(0).getAsJsonObject().get("kind").getAsString());
        assertTrue(refused.get(0).getAsJsonObject().get("detail")
                .getAsString().contains(FIELD_SIGNATURE));
        assertEquals(0, roots(minted).size());
        assertEquals("FINAL_REFUSED", minted.manifest.get(
                ComposedManifest.FINAL_STATUS).getAsString());
        // The same path, plus one decision the replay took in another region
        // of the same execution: a path condition is the replay's, not a
        // region's, and reading only the anchor region's conditions left
        // HDFS-17960's root out of every pi.
        PathMergeComposer.Result across = composed("path-merge-cross",
                path("seed", "GROUP.SEED",
                        notEqual(constant(1), constant(0)),
                        notEqual(constant(1), constant(0))),
                decision("GROUP.SEED", rootIs(true)));
        assertEquals(0, gates(across).size());
        assertEquals(1, roots(across).size());
        assertTrue(across.smtLib.contains(ROOT_TERM));
        // A root no source states a value for is refused, not composed over.
        PathMergeComposer.Result unstated = composed("path-merge-unstated",
                path("flip", "GROUP.FLIP", rootIs(false),
                        notEqual(constant(1), constant(0))),
                null, "GROUP.FLIP");
        assertEquals(1, gates(unstated).size());
        assertEquals(PathMergeComposer.RECORDED_ROOT_VALUE_UNSTATED,
                gates(unstated).get(0).getAsJsonObject().get("kind")
                        .getAsString());
        assertEquals("", roots(unstated).get(0).getAsJsonObject()
                .get("recordedValue").getAsString());

        // A predicate published already concrete, at an activation whose
        // slice declares carriers and on a path that depends on no root.
        JsonObject cut = path("seed", "GROUP.SEED",
                notEqual(constant(2), constant(3)),
                notEqual(constant(1), constant(0)));
        JsonArray declared = new JsonArray();
        declared.add("INSTANCE_FIELD/2#24");
        cut.getAsJsonObject(TargetAnchorEvidence.FIELD)
                .add(TargetAnchorEvidence.CARRIERS, declared);
        PathMergeComposer.Result literal = composed("path-merge-cut", cut);
        assertFalse(gates(literal).size() == 0);
        assertEquals(PathMergeComposer.PROPAGATION_CUT,
                gates(literal).get(0).getAsJsonObject().get("kind")
                        .getAsString());
        assertFalse(paths(literal).get(0).getAsJsonObject()
                .get("admitted").getAsBoolean());
        assertEquals("FINAL_REFUSED", literal.manifest.get(
                ComposedManifest.FINAL_STATUS).getAsString());

        // An INITIAL publishes the container it began from as SNAPSHOT_BASE
        // with one PUT per entry walked, so membership is a recorded fact.
        PathMergeComposer.Result walked = composed("path-merge-base",
                path("base", "GROUP.FLIP", rootIs(false),
                        notEqual(mapRead(reconstructedMap(), 119980),
                                constant(0))));
        assertEquals("a membership the base decides is no gate", 0,
                gates(walked).size());
        PathMergeComposer.Result unwalked = composed("path-merge-nobase",
                path("nobase", "GROUP.FLIP", rootIs(false),
                        notEqual(mapRead(mapState(), 119980), constant(0))));
        assertTrue("a membership nothing decides is refused by name",
                gates(unwalked).toString()
                        .contains("CONTAINER_BASE_UNSTATED"));

        // The same rule one model down: with no declaration in scope the
        // bounded-loop model published an empty set and no gaps, so a replay
        // that traversed the loop read like one that never entered it.
        BoundedLoopComposition traversed = BoundedLoopComposition.ofPlanRows(
                Collections.emptyList(), Collections.emptyList());
        traversed.observeCase(LOOP_OCCURRENCE + "#a1", observedCase(5));
        assertEquals(0, traversed.manifest().getAsJsonArray("boundedLoops")
                .size());
        assertEquals(1, traversed.compositionGaps().size());
        JsonObject gap = traversed.compositionGaps().get(0);
        // The composition copy is stamped with its own reason as kind: the
        // acceptance gate names a refusal by that member.
        assertEquals(BoundedLoopComposition.LOOP_OBSERVED_UNDECLARED,
                gap.get("kind").getAsString());
        assertEquals(BoundedLoopComposition.LOOP_OBSERVED_UNDECLARED,
                gap.get("reason").getAsString());
        assertEquals(BoundedLoopComposition.GAP_KIND,
                traversed.manifest().getAsJsonArray("gaps").get(0)
                        .getAsJsonObject().get("kind").getAsString());
        assertTrue(gap.get("subject").getAsString()
                .startsWith(LOOP_OCCURRENCE));

        // A loop the case never entered needs no declaration to be sound.
        BoundedLoopComposition unentered = BoundedLoopComposition.ofPlanRows(
                Collections.emptyList(), Collections.emptyList());
        unentered.observeCase(LOOP_OCCURRENCE + "#a1", observedCase(0));
        assertTrue(unentered.compositionGaps().isEmpty());
    }

    /**
     * An anchored occurrence whose path worklist never closed has no reach
     * query at all.  That anchor has no path, which is TARGET_NOT_REACHED
     * about that occurrence; it is not a reason for the run to fail, and the
     * sibling occurrence's own composition is untouched by it.
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
        PathMergeComposer.Result result = PathMergeComposer.compose(
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", absent.toString(),
                        "--summaries", summaries.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString(),
                        "--occurrence-id",
                        "node0/region/REGION.example#2"}));
        assertEquals("FINAL_REFUSED", JsonFields.optionalString(
                result.manifest, ComposedManifest.FINAL_STATUS));
        List<String> refusals = new ArrayList<>();
        for (JsonElement row
                : result.manifest.getAsJsonArray("finalStatusRefusals")) {
            refusals.add(JsonFields.optionalString(
                    row.getAsJsonObject(), "kind"));
        }
        assertEquals(Collections.singletonList(
                PathMergeComposer.TARGET_NOT_REACHED), refusals);
    }

    /**
     * A path that contradicts its own execution is named, not composed.
     *
     * <p>A path must be satisfiable as the execution that made it: that
     * replay's roots as it read them, its clocks in its own window, the
     * values it READ at its handoffs.</p>
     */
    @Test
    public void aPathIsSatisfiableAsTheExecutionThatMadeIt()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-self");
        JsonObject query = query();
        // The replay read the marker false; this path's own condition says
        // it was true.
        query.getAsJsonArray("paths").add(path("self", "GROUP.FLIP",
                rootIs(true), notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = run(directory, query,
                Arrays.asList(ranAt("GROUP.SEED", "true"),
                        ranAt("GROUP.FLIP", "false")), "--z3", "z3");

        assertTrue("the refusal names the invariant",
                gates(result).toString()
                        .contains(PathMergeComposer.PATH_NOT_SELF_CONSISTENT));
        assertFalse("and the path is not composed",
                paths(result).get(0).getAsJsonObject()
                        .get("admitted").getAsBoolean());
    }

    /**
     * A value that crossed a wire is a free variable joined at the handoff,
     * and a delivery is available only under the valuation that produced it.
     *
     * <p>The consumer's fatal predicate is over {@code v_H}, so a consumer
     * flip needs no producer replay.  What ties {@code v_H} to the world is
     * the family published at that handoff occurrence, each arm guarded by
     * the valuation its replay ran under -- without the guard the family is
     * a menu.</p>
     */
    @Test
    public void aHandoffValueIsJoinedByItsFamilyNotByInlining()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-handoff");
        JsonObject query = query();
        // The fatal path is the flip replay's: it received the delivery
        // its consumer fails on and decided the anchor over v_H alone.
        query.getAsJsonArray("paths").add(path("only", "GROUP.FLIP",
                notEqual(handoff(), constant(0)),
                notEqual(handoff(), constant(9))));
        JsonObject seed = ranAt("GROUP.SEED", "true");
        seed.add("vmHandoffEvents", handoffEvents(constant(9), 11L, 12L));
        JsonObject flip = ranAt("GROUP.FLIP", "false");
        flip.add("vmHandoffEvents", handoffEvents(constant(7), 21L, 22L));
        PathMergeComposer.Result armed =
                run(directory, query, Arrays.asList(seed, flip));
        assertEquals("one family, joined at the handoff occurrence", 1,
                armed.manifest.getAsJsonObject(
                        PathMergeComposer.MANIFEST_FIELD)
                        .getAsJsonArray("handoffFamilies").size());
        for (JsonElement row : paths(armed)) {
            assertTrue("a path over a handoff value was cut: " + row,
                    JsonFields.optionalBool(row.getAsJsonObject(),
                            "admitted", false));
        }
        assertTrue("the family must carry the delivering valuation",
                armed.smtLib.contains(ROOT_TERM));
        // At the recorded polarity only the seed's own delivery is
        // available, and the consumer does not fail on it.
        assertEquals("the recorded polarity must not reach the failure",
                "unsat", solve(armed.smtLib + "(assert (= " + ROOT_TERM
                        + " true))\n(check-sat)\n"));
        // Move the marker and the flip replay's delivery becomes available,
        // which is the delivery the consumer fails on.
        assertEquals("the flipped polarity reaches it",
                "sat", solve(armed.smtLib + "(assert (= " + ROOT_TERM
                        + " false))\n(check-sat)\n"));

        // An arm is a delivery some producer path made; a value an
        // obligation answered is that path's own control and never an arm,
        // so the bind stays the wire and the answer is stated beside it.
        JsonArray answered = handoffEvents(constant(7), 21L, 22L);
        answered.get(0).getAsJsonObject().addProperty(
                VmHandoffEvidence.ANSWERED_VALUE, "0");
        JsonObject answeredFlip = ranAt("GROUP.FLIP", "false");
        answeredFlip.add("vmHandoffEvents", answered);
        JsonArray arms = run(directory, query,
                Arrays.asList(seed, answeredFlip)).manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD)
                .getAsJsonArray("handoffFamilies").get(0).getAsJsonObject()
                .getAsJsonArray("arms");
        JsonObject arm = arms.get(arms.size() - 1).getAsJsonObject();
        assertEquals("9", arm.get("deliveredValue").getAsString());
        assertEquals("0", arm.get(VmHandoffEvidence.ANSWERED_VALUE)
                .getAsString());
    }

    /**
     * A clock read is carried as this execution's window, not as a value.
     *
     * <p>Every execution reads the wall clock fresh, so a clock cell is not
     * an assignment its replay ran under, and pinning it to one reading
     * contradicts every other replay's decisions over it.  What a path owes
     * is the case's declared skew around the instant THIS execution read,
     * keyed on the callee the hook named and on nothing about the site.</p>
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

        // The window brackets the recorded value rather than pinning it, and
        // it survives a recorded value below the skew without underflowing.
        assertEquals("(and (>= now 1699999700000) (<= now 1700000300000))",
                ClockRootPhysics.window("now", 1700000000000L, 300000L));
        assertEquals("(and (>= now (- 299900)) (<= now 300100))",
                ClockRootPhysics.window("now", 100L, 300000L));
        // A zero skew is a legitimate configuration: pin to the recording.
        assertEquals("(and (>= now 42) (<= now 42))",
                ClockRootPhysics.window("now", 42L, 0L));

        // A cell is a wall-clock read because the hook's declaration names
        // the callee, never because of anything about its site.
        assertTrue(ClockRootPhysics.clockCallee(
                "<org.apache.hadoop.util.Timer: long now()>"));
        assertTrue(ClockRootPhysics.clockCallee(
                "<java.lang.System: long currentTimeMillis()>"));
        assertTrue(!ClockRootPhysics.clockCallee(
                "<org.apache.hadoop.hdfs.security.token.block.BlockKey:"
                        + " int getKeyId()>"));
        assertTrue(!ClockRootPhysics.clockCallee(null));

        // A root the case declares a domain for is free inside it: pinning
        // it to what the recording read answers the case's own question.
        JsonObject interval = JsonParser.parseString("{'solverTerm':'iv',"
                + "'recordedValue':'600000','declaredDomainMin':'60000',"
                + "'declaredDomainMax':'86400000'}").getAsJsonObject();
        assertEquals("(and (>= iv 60000) (<= iv 86400000))",
                PathMergeComposer.rootDomain(interval, null));
        interval.remove(PathMergeComposer.DECLARED_DOMAIN_MIN);
        assertEquals("a root with no declared domain is the value it read",
                "(= iv 600000)",
                PathMergeComposer.rootDomain(interval, null));

        // And such a root is a term arithmetic composes with, so a producer
        // that adds two of them lowers into the family arm it delivers.
        Map<String, JsonObject> intervals = new LinkedHashMap<>();
        intervals.put("M_J_iv", interval);
        String sum = new PathMergeLowering(intervals).condition(
                JsonParser.parseString("{'_type':'BinaryExpression','_op':"
                        + "'>','_left':{'_type':'BinaryExpression','_op':"
                        + "'+','_java_type':'J','_left':{'_type':"
                        + "'SymbolExpression','_java_type':'J','_exp':"
                        + "'M_J_iv'},'_right':{'_type':'ConstExpr',"
                        + "'_java_type':'J','_exp':'Y_J_5'}},'_right':"
                        + "{'_type':'ConstExpr','_java_type':'J','_exp':"
                        + "'Y_J_7'}}"), "interval:arithmetic");
        assertTrue(sum, sum.contains("+") && sum.contains(">"));
    }

    // ------------------------------------------------------------------
    // Fixtures.
    // ------------------------------------------------------------------

    private static JsonArray gates(PathMergeComposer.Result result) {
        return result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD).getAsJsonArray("gates");
    }

    private static JsonArray paths(PathMergeComposer.Result result) {
        return result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD).getAsJsonArray("paths");
    }

    private static JsonArray roots(PathMergeComposer.Result result) {
        return result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD).getAsJsonArray("roots");
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

    /** The consumer's view of the value that arrived: one free variable. */
    private static JsonObject handoff() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", HANDOFF_SYMBOL);
        return symbol;
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

    /** One replay's reading of a cell the clock hook minted. */
    private static JsonObject clockReading(String reading) {
        return SymbolicSourceEvidence.manualEvent("PORT.now",
                "node0/region/REGION.source#1#a1", CLOCK_SIGNATURE, "J",
                RAW_CLOCK, CLOCK_TERM,
                "<org.apache.hadoop.util.Timer: long now()>",
                "<com.example.Service: void serve()>#u3", 11L, reading,
                reading);
    }

    /** One case's loop counts, as the replay published them. */
    private static JsonObject observedCase(int bodyCount) {
        JsonObject count = new JsonObject();
        count.addProperty(LoopBoundPolicy.LOOP_SITE_ID, LOOP_SITE);
        count.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
        count.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, bodyCount > 0);
        count.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
        count.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED);
        JsonArray counts = new JsonArray();
        counts.add(count);

        JsonObject item = new JsonObject();
        item.addProperty("caseId", "LOCAL_CASE.test");
        item.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        return item;
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

    /** One path against the standard pair of replay summaries. */
    private static PathMergeComposer.Result composed(String name,
                                                     JsonObject path)
            throws IOException {
        return composed(name, path, null, "GROUP.SEED", "GROUP.FLIP");
    }

    private static PathMergeComposer.Result composed(String name,
                                                     JsonObject path,
                                                     JsonObject extra,
                                                     String... groups)
            throws IOException {
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path);
        return compose(Files.createTempDirectory(name), query, extra,
                groups.length == 0
                        ? new String[]{"GROUP.SEED", "GROUP.FLIP"} : groups);
    }

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query)
            throws IOException {
        return compose(directory, query, null, "GROUP.SEED", "GROUP.FLIP");
    }

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query,
                                                    JsonObject extra,
                                                    String... groups)
            throws IOException {
        List<JsonObject> rows = new ArrayList<>();
        for (String group : groups) rows.add(summary(group));
        if (extra != null) rows.add(extra);
        return run(directory, query, rows);
    }

    /** One query and the replay summaries it is composed against. */
    private static PathMergeComposer.Result run(Path directory,
                                                JsonObject query,
                                                List<JsonObject> summaries,
                                                String... extra)
            throws IOException {
        StringBuilder body = new StringBuilder();
        for (JsonObject row : summaries) {
            body.append(JsonFields.WRITER.toJson(
                    SharedExpressionTable.compact(row))).append('\n');
        }
        Path summaryFile = directory.resolve("summaries.jsonl");
        write(summaryFile, body.toString());
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        List<String> line = new ArrayList<>(Arrays.asList(
                "--fatal-query", queryFile.toString(),
                "--summaries", summaryFile.toString(),
                "--output", directory.resolve("candidate.smt2").toString(),
                "--manifest",
                directory.resolve("manifest.json").toString()));
        line.addAll(Arrays.asList(extra));
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
        return path(caseId, group, pathCondition, fatalPredicate,
                new ArrayList<String>());
    }

    /** The same row as a replay that declared tracked carriers makes it. */
    private static JsonObject path(String caseId, String group,
                                   JsonObject pathCondition,
                                   JsonObject fatalPredicate,
                                   List<String> carriers) {
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
                new ArrayList<JsonObject>(), carriers));
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
