package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Which planned occurrences still replay, and why the rest do not.
 *
 * <p>The plan is HDFS-17960 in miniature: one declared root, one carrier
 * the root's guarded case writes, and a heavy occurrence -- the fsimage
 * loader -- that reads and writes only what no root can move.  A campaign
 * must replay the target, every root site, every write the failing read
 * consumes and whatever a root reaches over a carrier flow or a wire, and
 * nothing else.</p>
 */
public class ReplayTaskSliceTest {

    private static final String ROOT_REGION = "REGION.root";
    private static final String ROOT = "<S: boolean snapshotDeletionOrdered>";
    private static final String GUARD_LOCAL = "<S: void deleteSnapshot()>::$z0";
    private static final String CARRIER = "<S: int snapshotCounter>";
    private static final String CARRIER_KEY = "S#snapshotCounter";
    private static final String UNRELATED = "<L: long layoutVersion>";
    private static final String UNRELATED_KEY = "L#layoutVersion";
    private static final String FATAL_READ = "<T: void save()>::$i0";

    private static final String TARGET = occurrence("REGION.target");
    private static final String ROOT_SITE = occurrence(ROOT_REGION);
    private static final String WRITER = occurrence("REGION.writer");
    private static final String LOADER = occurrence("REGION.loader");
    private static final String WIRE_CONSUMER = occurrence("REGION.wire");
    private static final String WIRE_SINK = occurrence("REGION.wiresink");
    private static final String COLLECTOR = occurrence("REGION.collector");
    private static final String DEAD_WIRE = occurrence("REGION.deadwire");
    private static final String HOOK_PHASE = occurrence("REGION.phase");
    private static final String FAULT = occurrence("REGION.fault");

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /** One declaration file per seeded selection this test builds. */
    private int selections;

    @Test
    public void replayTaskSliceRules() throws Exception {
        keepsOnlyWhatCanCarryARootTowardTheTarget();
        aCarrierWriterNoRootReachesIsARecordedConstant();
        theFatalReadsBackwardSliceNarrowsTheCaredLocations();
        everySiblingOfOneProvenanceIsReplayed();
        FlippedFaultPathReplayPrefixTest t0 =
                new FlippedFaultPathReplayPrefixTest();
        t0.flippedFaultPathReplayPrefixRules();
    }

    private void keepsOnlyWhatCanCarryARootTowardTheTarget()
            throws Exception {
        ReplayTaskSlice slice = decide(plans(), seeded());

        assertTrue(slice.applied());
        assertEquals(reasons(ReplayTaskSlice.TARGET_REACH,
                ReplayTaskSlice.ROOT_DEPENDENT_FLOW), slice.reasons(TARGET));
        assertEquals(reasons(ReplayTaskSlice.ROOT_SITE),
                slice.reasons(ROOT_SITE));
        assertEquals("the failing read consumes this write directly",
                reasons(ReplayTaskSlice.FATAL_READ_WRITER),
                slice.reasons(WRITER));
        assertEquals("a wire whose producer is a root site carries it",
                reasons(ReplayTaskSlice.ROOT_DEPENDENT_FLOW),
                slice.reasons(WIRE_CONSUMER));
        assertEquals("the hook published the root inside this activation",
                reasons(ReplayTaskSlice.ROOT_SITE), slice.reasons(HOOK_PHASE));
        assertEquals("a workload fault marker is a root",
                reasons(ReplayTaskSlice.ROOT_SITE), slice.reasons(FAULT));
        assertFalse("the loader writes a location no root reaches",
                slice.keeps(LOADER));
        assertFalse("a wire from a non-root-dependent producer carries nothing",
                slice.keeps(DEAD_WIRE));
    }

    /**
     * Writing a location a root reaches is not itself a root: the value the
     * recording fixed is the value every arm writes.  Before this rule a
     * carrier writer seeded the forward closure, which is why every per-key
     * {@code convert} of a key rotation "carried the root".
     */
    private void aCarrierWriterNoRootReachesIsARecordedConstant()
            throws Exception {
        List<RegionInstancePlan> plans = new ArrayList<>();
        String sink = occurrence("REGION.sink");
        String writer = occurrence("REGION.lonewriter");
        plans.add(plan(TARGET, "TARGET_REACH_CLOSURE", actions(), edges()));
        plans.add(plan(ROOT_SITE, "REGION_PATH_CLOSURE",
                actions(fieldRead(ROOT)), edges()));
        // The writer's own location is on the root's forward slice, but no
        // root reaches the writer, and the target never reads what it wrote.
        plans.add(plan(writer, "REGION_PATH_CLOSURE", actions(),
                edges(sharedFlow(writer, sink, CARRIER, CARRIER_KEY))));
        plans.add(plan(sink, "REGION_PATH_CLOSURE", actions(), edges()));

        ReplayTaskSlice slice = decide(plans, seeded());

        assertFalse("a writer is a keep reason, never a root",
                slice.keeps(writer));
        assertFalse(slice.keeps(sink));
        assertTrue(slice.keeps(ROOT_SITE));
    }

    /**
     * The root's forward slice says what can move; the fatal read's backward
     * slice says what the failure ever looks at.  A location on the first and
     * not the second is a constant for this failure.
     */
    private void theFatalReadsBackwardSliceNarrowsTheCaredLocations()
            throws Exception {
        List<RegionInstancePlan> plans = new ArrayList<>();
        String bystander = occurrence("REGION.bystander");
        String consumer = occurrence("REGION.consumer");
        plans.add(targetPlan(TARGET, edges()));
        plans.add(plan(ROOT_SITE, "REGION_PATH_CLOSURE",
                actions(fieldRead(ROOT)),
                edges(sharedFlow(ROOT_SITE, bystander, CARRIER, CARRIER_KEY),
                        sharedFlow(ROOT_SITE, consumer, ROOT, "S#"
                                + "snapshotDeletionOrdered"))));
        // Both reach the failing read the same way, so the only thing that
        // can separate them is the location the root reached them over.
        plans.add(plan(bystander, "REGION_PATH_CLOSURE", actions(),
                edges(wire(bystander, COLLECTOR))));
        plans.add(plan(consumer, "REGION_PATH_CLOSURE", actions(),
                edges(wire(consumer, COLLECTOR))));
        plans.add(plan(COLLECTOR, "REGION_PATH_CLOSURE", actions(),
                edges(wire(COLLECTOR, TARGET))));

        // CARRIER is reachable from the root but nothing carries it into the
        // fatal read; the root's own field is read by the failing branch.
        ReplayTaskSlice slice = ReplayTaskSlice.decide(plans, seeded(),
                Arrays.asList(edge(ROOT, FATAL_READ, "HEAP_READ"),
                        edge(ROOT, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, CARRIER, "GUARD")));

        assertTrue(slice.keeps(ROOT_SITE));
        assertTrue("the root's own field reaches the failing branch",
                slice.keeps(consumer));
        assertFalse("the fatal read never consults the counter",
                slice.keeps(bystander));
    }

    /**
     * Repetition is not interchangeability: every sibling replays.
     *
     * <p>A key rotation plans one occurrence of the converting region per
     * element and every one of them carries the same producer's root
     * provenance, so a fold that told arms apart by provenance saw one arm
     * where there were five.  They are not one arm: an occurrence reaches
     * this point only by being root-dependent, and root-dependent siblings
     * write different derived values -- one key of the rotation and its
     * successor -- so dropping four of the five dropped four of the
     * failure's own attach points.  On hdfs-17899-bug3 that left one
     * per-key convert per DataNode and every other block-key consumer
     * family bound to nothing.</p>
     *
     * <p>The slice narrows by root dependence and by the fatal read's
     * backward slice, and by nothing else; what survives both is replayed,
     * however many siblings share its shape.</p>
     */
    private void everySiblingOfOneProvenanceIsReplayed() throws Exception {
        List<RegionInstancePlan> plans = new ArrayList<>();
        JsonArray deliveries = new JsonArray();
        for (int index = 1; index <= 5; index++) {
            deliveries.add(wire(ROOT_SITE, element(index)));
        }
        plans.add(plan(TARGET, "TARGET_REACH_CLOSURE", actions(), edges()));
        plans.add(plan(ROOT_SITE, "REGION_PATH_CLOSURE",
                actions(fieldRead(ROOT)), deliveries));
        for (int index = 1; index <= 5; index++) {
            plans.add(plan(element(index), "REGION_PATH_CLOSURE", actions(),
                    edges(sharedFlow(element(index), COLLECTOR, CARRIER,
                            CARRIER_KEY))));
        }
        plans.add(plan(COLLECTOR, "REGION_PATH_CLOSURE", actions(),
                edges(wire(COLLECTOR, TARGET))));

        ReplayTaskSlice slice = decide(plans, seeded());

        List<String> cohort = new ArrayList<>();
        for (int index = 1; index <= 5; index++) {
            cohort.add(element(index));
            assertTrue("sibling " + index + " carries its own element",
                    slice.keeps(element(index)));
            assertEquals(reasons(ReplayTaskSlice.ROOT_DEPENDENT_FLOW,
                            ReplayTaskSlice.CARRIER_WRITER),
                    slice.reasons(element(index)));
        }
        JsonObject telemetry = slice.telemetry(cohort);
        assertEquals(5, telemetry.get("keptOccurrenceCount").getAsInt());
        assertEquals(0, telemetry.get("prunedOccurrenceCount").getAsInt());
        // Nothing in the artifact says an occurrence stands for another.
        for (JsonObject row : slice.rows(cohort)) {
            assertFalse(row.has("foldedInto"));
        }
    }

    // --- fixture -----------------------------------------------------------

    private static ReplayTaskSlice decide(
            List<RegionInstancePlan> plans,
            ConcolicScheduler.SymbolicInputSelection selection) {
        return ReplayTaskSlice.decide(plans, selection,
                Collections.<JsonObject>emptyList());
    }

    /**
     * target <-carrier- writer; target <-unrelated- loader;
     * root -wire-> wireConsumer; loader -wire-> deadWire; plus a hook-phase
     * occurrence and a fault-marker occurrence with no edges at all.
     */
    private static List<RegionInstancePlan> plans() {
        List<RegionInstancePlan> plans = new ArrayList<>();
        plans.add(plan(TARGET, "TARGET_REACH_CLOSURE", actions(),
                edges(sharedFlow(WRITER, TARGET, CARRIER, CARRIER_KEY),
                        sharedFlow(LOADER, TARGET, UNRELATED, UNRELATED_KEY))));
        plans.add(plan(ROOT_SITE, "REGION_PATH_CLOSURE",
                actions(fieldRead(ROOT)), edges(wire(ROOT_SITE, WIRE_CONSUMER))));
        plans.add(plan(WRITER, "REGION_PATH_CLOSURE", actions(), edges()));
        plans.add(plan(LOADER, "REGION_PATH_CLOSURE",
                actions(fieldRead(UNRELATED)), edges(wire(LOADER, DEAD_WIRE))));
        // The wire carries the root on to a write the target reads, so the
        // consumer is on the forward slice and the backward one at once.
        plans.add(plan(WIRE_CONSUMER, "REGION_PATH_CLOSURE", actions(),
                edges(wire(WIRE_CONSUMER, WIRE_SINK))));
        plans.add(plan(WIRE_SINK, "REGION_PATH_CLOSURE", actions(),
                edges(sharedFlow(WIRE_SINK, TARGET, CARRIER, CARRIER_KEY))));
        plans.add(plan(DEAD_WIRE, "REGION_PATH_CLOSURE", actions(), edges()));
        // The hook published the root inside this activation, which the plan
        // states as a configured source phase rather than as an action.
        String hookMethod = "<S: boolean isSnapshotDeletionOrdered()>";
        JsonArray declared = new JsonArray();
        declared.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "HDFS.CONFIG.ORDERED", ROOT, hookMethod, 1));
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(declared).get(0);
        JsonObject phase = ConfiguredSourcePhaseContract.occurrence(
                declaration, HOOK_PHASE, 1, 10L, 9L, 10L, hookMethod,
                Collections.singletonList(9L));
        RegionInstancePlan hook = plan(HOOK_PHASE, "REGION_PATH_CLOSURE",
                actions(), edges());
        JsonObject withPhase = hook.json().deepCopy();
        JsonArray phases = new JsonArray();
        phases.add(phase);
        withPhase.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        plans.add(RegionInstancePlan.decode(withPhase));
        JsonObject marker = base("EXPLICIT_SYMBOLIC_FAULT");
        marker.addProperty("cell", "<C: boolean rpcFails>");
        plans.add(plan(FAULT, "REGION_PATH_CLOSURE", actions(marker), edges()));
        return plans;
    }

    private ConcolicScheduler.SymbolicInputSelection seeded()
            throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection = selection();
        selection.seedCarrierSlice(Arrays.asList(
                edge(ROOT, GUARD_LOCAL, "HEAP_READ"),
                edge(GUARD_LOCAL, CARRIER, "GUARD"),
                edge("<X: int other>", UNRELATED, "HEAP_WRITE")),
                proposals(fieldRead(ROOT)));
        return selection;
    }

    private ConcolicScheduler.SymbolicInputSelection selection()
            throws IOException {
        Path declarations = folder.newFile("symbolic-inputs-"
                + (selections++) + ".jsonl").toPath();
        Files.write(declarations, ("{\"regionId\":\"" + ROOT_REGION
                + "\",\"fieldSignatures\":[\"" + ROOT + "\"]}\n")
                .getBytes(StandardCharsets.UTF_8));
        JsonObject region = new JsonObject();
        region.addProperty("regionId", ROOT_REGION);
        return ConcolicScheduler.SymbolicInputSelection.read(declarations,
                Collections.singletonList(region),
                        java.util.Collections.<edu.uva.liftlab.graphchecker.contract.RegionInstancePlan>emptyList());
    }

    private static List<Map.Entry<String, JsonArray>> proposals(
            JsonObject... proposed) {
        List<Map.Entry<String, JsonArray>> rows = new ArrayList<>();
        rows.add(new AbstractMap.SimpleImmutableEntry<>(ROOT_REGION,
                actions(proposed)));
        return rows;
    }

    private static String occurrence(String region) {
        return "test/nn0#epoch1/region/" + region + "#1";
    }

    /** One element of the per-element cohort, all of one region. */
    private static String element(int index) {
        return "test/nn0#epoch1/region/REGION.element#" + index;
    }

    private static String regionOf(String occurrence) {
        String tail = occurrence.substring(
                occurrence.lastIndexOf("/region/") + "/region/".length());
        return tail.substring(0, tail.lastIndexOf('#'));
    }

    private static RegionInstancePlan targetPlan(String occurrence,
                                                 JsonArray edgeBindings) {
        JsonObject branch = new JsonObject();
        branch.addProperty("failureTarget", true);
        JsonArray operands = new JsonArray();
        operands.add(FATAL_READ);
        branch.add("operandCells", operands);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        JsonObject plan = plan(occurrence, "TARGET_REACH_CLOSURE", actions(),
                edgeBindings).json().deepCopy();
        plan.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .add("branches", branches);
        return RegionInstancePlan.decode(plan);
    }

    private static RegionInstancePlan plan(String occurrence, String kind,
                                           JsonArray symbolize,
                                           JsonArray edgeBindings) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL." + occurrence);
        goal.addProperty("kind", kind);
        goal.add("symbolize", symbolize);
        goal.add("runtimeDefinitionMethods", new JsonArray());
        goal.add("edgeBindings", edgeBindings);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        JsonObject plan = new JsonObject();
        plan.addProperty("sourceKey", "test/nn0#epoch1");
        plan.addProperty("occurrenceId", occurrence);
        plan.addProperty("requestKey", "test/nn0#epoch1/request/save#1");
        plan.addProperty("relationKey", "RELATION." + regionOf(occurrence));
        plan.addProperty("regionId", regionOf(occurrence));
        plan.addProperty("targetMethod", "<M: void " + regionOf(occurrence)
                + "()>");
        plan.add("closureGoals", goals);
        return RegionInstancePlan.decode(plan);
    }

    private static JsonObject sharedFlow(String from, String to,
                                         String field, String key) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("edgeId", "SF." + from + "->" + to + ":" + key);
        edge.addProperty("authority", SharedFieldFlow.LOCATION_MATCH_AUTHORITY);
        edge.addProperty("fromOccurrenceId", from);
        edge.addProperty("toOccurrenceId", to);
        edge.addProperty("fromOutputPort", regionOf(from) + ".out.1");
        edge.addProperty("toInputPort", regionOf(to) + ".in.1");
        edge.addProperty(SharedFieldFlow.EDGE_LOCATION, key);
        JsonArray declarations = new JsonArray();
        declarations.add(field);
        edge.add("fieldPathDeclarations", declarations);
        return edge;
    }

    private static JsonObject wire(String from, String to) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", AutomaticRegionEdge.RUNTIME_PROTOCOL_EDGE_KIND);
        edge.addProperty("edgeId", "XCH." + from + "->" + to);
        edge.addProperty("authority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        edge.addProperty("fromOccurrenceId", from);
        edge.addProperty("toOccurrenceId", to);
        edge.addProperty("fromOutputPort", "XCH.1.req.key-id");
        edge.addProperty("toInputPort", "XCH.1.req.key-id");
        return edge;
    }

    private static JsonArray edges(JsonObject... rows) {
        JsonArray edges = new JsonArray();
        for (JsonObject row : rows) edges.add(row);
        return edges;
    }

    private static JsonArray actions(JsonObject... proposed) {
        JsonArray actions = new JsonArray();
        for (JsonObject action : proposed) actions.add(action.deepCopy());
        return actions;
    }

    /**
     * The refined graph's spelling of "this value decides whether that
     * location is mutated": a GUARD edge into the mutated location, naming
     * the guard site and the mutating site it controls.
     */
    private static JsonObject guardOfMutation(String guard, String location) {
        JsonObject row = edge(guard, location, "GUARD");
        row.addProperty("kind", "heap_mutation_path_guard");
        row.addProperty("guardSiteId", "<S: void sweep()>#u7");
        row.addProperty("guardedMutationSiteId", "<S: void sweep()>#u16");
        JsonObject mutation = new JsonObject();
        mutation.addProperty("guardSiteId", "<S: void sweep()>#u7");
        mutation.addProperty("guardedMutationSiteId", "<S: void sweep()>#u16");
        mutation.addProperty("guardedMutationUnit", "remove(k)");
        JsonArray mutations = new JsonArray();
        mutations.add(mutation);
        row.add("guardedMutations", mutations);
        return row;
    }

    private static Set<String> singleton(String value) {
        return new LinkedHashSet<>(Collections.singletonList(value));
    }

    private static JsonObject edge(String from, String to, String kind) {
        JsonObject row = new JsonObject();
        row.addProperty("fromCell", from);
        row.addProperty("toCell", to);
        row.addProperty("transferKind", kind);
        return row;
    }

    /** A root every region owns: a marker the workload wrote itself. */
    private static JsonObject faultMarker() {
        JsonObject marker = base("EXPLICIT_SYMBOLIC_FAULT");
        marker.addProperty("cell", "<C: boolean rpcFails>");
        return marker;
    }

    private static JsonObject fieldRead(String field) {
        JsonObject action = base("ACTIVATION_FIELD_RECEIVER");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("cell", field);
        return action;
    }

    private static JsonObject base(String sourceKind) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("sourceKind", sourceKind);
        action.addProperty("siteId", "<C: void m()>#u1");
        action.addProperty("symbol", "port." + sourceKind);
        return action;
    }

    private static Set<String> reasons(String... values) {
        return new LinkedHashSet<>(Arrays.asList(values));
    }

    /**
     * A flipped fault path is admitted on the prefix up to the flip, and the
     * recorded work after the flip is not required to happen again.
     *
     * <p>The transcript is the hdfs-17899 heartbeat, reduced to its two source
     * decisions.  The recorded run answers the fault marker {@code false} at
     * {@code SITE.HEARTBEAT#1} and then, the request having succeeded, takes a
     * branch inside {@code addKeys} at {@code SITE.ADDKEYS#1}.  Flipping the
     * marker sends the request into its catch path, so {@code addKeys} never
     * runs and {@code SITE.ADDKEYS#1} never happens.  Requiring it anyway would
     * refuse exactly the replay the flip was scheduled to produce.</p>
     *
     * <p>These cases pin the boundary in both directions, because the two
     * mistakes are symmetric: demanding decisions recorded after the flip
     * refuses every fault replay, and dropping decisions recorded before it
     * would admit a replay that reached the flipped branch by a different
     * route.</p>
     */
    static final class FlippedFaultPathReplayPrefixTest {
        private static final String HEARTBEAT = "SITE.HEARTBEAT";
        private static final String ADD_KEYS = "SITE.ADDKEYS";
        private static final String SEND_REQUEST = "SITE.SENDREQUEST";
        private static final String LOOP_EXIT = "SITE.REMOVEEXPIREDKEYS#u7";
        private static final String EXPIRED_KEY = "SITE.REMOVEEXPIREDKEYS#u15";

        /** Recorded: heartbeat then addKeys. Flipped: heartbeat then catch. */
        public void flippedFaultPathReplayPrefixRules() throws Exception {
            workRecordedAfterTheFlipIsNotRequiredOfTheFlippedReplay();
            theFlippedDecisionInALoopIsAdmittedByItsFlippedOutcome();
            theRecordedOutcomeAtTheFlippedSiteIsRefusedByName();
            aLaterTurnOfTheFlippedSiteIsNotPartOfTheContract();
        }

        private void workRecordedAfterTheFlipIsNotRequiredOfTheFlippedReplay() {
            BranchReplayContract.RuntimeSchedule schedule = schedule(
                    transcript(), HEARTBEAT, 1);

            // The contract is cut at the flipped decision, so the addKeys branch
            // is not in it at all -- not an event the replay is excused, an event
            // it was never asked for.
            assertEquals(0, contract(transcript(), HEARTBEAT, 1).toJson()
                    .getAsJsonArray("runtimePrefix").size());

            BranchReplayContract.ReplayProgress replay =
                    new BranchReplayContract.ReplayProgress(schedule);
            // true is the flipped outcome: the recorded run answered false.
            assertTrue(replay.observeBinary(HEARTBEAT, 1, true));
            assertTrue(replay.complete());
            assertFalse(replay.failed());
            assertEquals("", replay.failure());
        }

        /**
         * Lane VM10: the flipped decision is inside a retained loop.
         *
         * <p>{@code removeExpiredKeys()#u7} is the loop exit and
         * {@code #u15} is a decision inside its body carrying propagated
         * symbolic support.  Six obligations were refused there as "prefix not
         * yet complete: observed 2 of 3, still waiting for ...#u15#1 (the
         * flipped source decision)" while the site had executed all along: the
         * source event was addressed by the support digest the SEED recorded at
         * it, and a support digest is a hash over a fresh JVM's own symbols --
         * two flip replays of one planned occurrence published
         * BRANCH_SUPPORT.v1.ce0d0b14... and BRANCH_SUPPORT.v1.ba9e60ac... at
         * that same site.  So the prefix ends before the flip, and the flipped
         * decision is addressed by its occurrence and honoured by its
         * outcome.</p>
         */
        private void theFlippedDecisionInALoopIsAdmittedByItsFlippedOutcome() {
            BranchReplayContract.RuntimeSchedule schedule = schedule(
                    loopTranscript(), EXPIRED_KEY, 1, retainedLoop());
            BranchReplayContract.ReplayProgress replay =
                    new BranchReplayContract.ReplayProgress(schedule);

            // 1..n-1 as recorded: the loop's first exit test, which is the whole
            // prefix, with this run's own support digest rather than the seed's.
            assertFalse(replay.observeBinary(LOOP_EXIT, 1, false, "SUPPORT.run"));
            assertFalse("the prefix alone does not complete the contract",
                    replay.complete());

            // n flipped: the recorded run took true here.
            assertTrue("the flipped outcome consumes the source event",
                    replay.observeBinary(EXPIRED_KEY, 1, false, "SUPPORT.run"));
            assertTrue(replay.complete());
            assertFalse(replay.failed());
            assertEquals("", replay.failure());
        }

        /** The recorded outcome at the flipped site is the flip not honoured. */
        private void theRecordedOutcomeAtTheFlippedSiteIsRefusedByName() {
            BranchReplayContract.RuntimeSchedule schedule = schedule(
                    loopTranscript(), EXPIRED_KEY, 1, retainedLoop());
            BranchReplayContract.ReplayProgress replay =
                    new BranchReplayContract.ReplayProgress(schedule);

            assertFalse(replay.observeBinary(LOOP_EXIT, 1, false, "SUPPORT.run"));
            assertFalse("the recorded outcome does not consume the source",
                    replay.observeBinary(EXPIRED_KEY, 1, true, "SUPPORT.run"));

            assertFalse(replay.complete());
            assertTrue("a flip that was not honoured is a refusal, not a wait",
                    replay.failed());
            assertTrue(replay.failure(),
                    replay.failure().startsWith("wrong decision at "
                            + EXPIRED_KEY + "#1"));
        }

        /**
         * Lane VM12: a later turn of the flipped loop is not the contract.
         *
         * <p>The flip at {@code #u15#1} changes what the rest of that loop does
         * -- that is what a flip is for -- so {@code #u15#2} is an execution the
         * recording never had. It was being compared: a prefix event inside a
         * bounded loop is addressed by the propagated value of the element it
         * tested, and the same element decided again on a later turn carries the
         * same digest, so the later turn matched an earlier expectation and was
         * refused on its outcome. Nine obligations on lane VM12 died that way,
         * each of them a flip working.</p>
         */
        private void aLaterTurnOfTheFlippedSiteIsNotPartOfTheContract() {
            BranchReplayContract.RuntimeSchedule schedule = schedule(
                    loopTranscript(), EXPIRED_KEY, 1, retainedLoop());
            BranchReplayContract.ReplayProgress replay =
                    new BranchReplayContract.ReplayProgress(schedule);

            assertFalse(replay.observeBinary(LOOP_EXIT, 1, false, "SUPPORT.run"));
            assertTrue("the flip is honoured at its own occurrence",
                    replay.observeBinary(EXPIRED_KEY, 1, false, "SUPPORT.run"));

            // The loop runs on, and the same element decides again with the
            // recorded outcome.  It is not a prefix event and refuses nothing.
            assertFalse(replay.observeBinary(EXPIRED_KEY, 2, true,
                    "SUPPORT.run"));
            assertFalse(replay.observeBinary(LOOP_EXIT, 2, true, "SUPPORT.run"));

            assertTrue(replay.complete());
            assertFalse(replay.failed());
            assertEquals("", replay.failure());
        }

        /** One activation of the key-expiry loop, as the summary records it. */
        private static JsonObject loopTranscript() {
            JsonObject exitTest = binary(variable("I_index"), "<",
                    integer(2));
            JsonObject expired = binary(variable("J_expiryDate"), "<",
                    integer(7));
            JsonArray path = new JsonArray();
            path.add(exitTest);
            path.add(expired);

            JsonObject normalization = new JsonObject();
            normalization.addProperty("predicateNormalization",
                    BranchWitness.IDENTITY_NORMALIZATION);
            JsonArray mappings = new JsonArray();
            mappings.add(SummaryBranchMapping.witnessed(
                    BranchWitness.vmPcImmutable(LOOP_EXIT, "removeExpiredKeys",
                            7, 1, false, exitTest, 0, normalization), 0,
                    SummaryBranchMapping.Policy.EXPLORE).toJson());
            mappings.add(SummaryBranchMapping.witnessed(
                    BranchWitness.vmPcImmutable(EXPIRED_KEY, "removeExpiredKeys",
                            15, 1, true, expired, 1, normalization), 1,
                    SummaryBranchMapping.Policy.EXPLORE).toJson());

            JsonObject summary = new JsonObject();
            summary.add("pathCondition", path);
            summary.add("branchMappings", mappings);
            return summary;
        }

        /** The retained loop #u15 sits in, with #u7 as its exit decision. */
        private static JsonArray retainedLoop() {
            JsonObject loop = new JsonObject();
            loop.addProperty("kind", "RETAINED_LOOP");
            loop.addProperty("runtimeLoopId", LOOP_EXIT + "#loop:u6");
            JsonArray members = new JsonArray();
            members.add(LOOP_EXIT);
            members.add(EXPIRED_KEY);
            loop.add("loopInnermostBranchSiteIds", members);
            JsonObject exit = new JsonObject();
            exit.addProperty("siteId", LOOP_EXIT);
            exit.addProperty("decisionToken",
                    "{\"branchKind\":\"BINARY\",\"sourceTakenOutcome\":true}");
            JsonArray exits = new JsonArray();
            exits.add(exit);
            loop.add("loopExitDecisions", exits);
            JsonArray loops = new JsonArray();
            loops.add(loop);
            return loops;
        }

        private static BranchReplayContract.RuntimeSchedule schedule(
                JsonObject summary, String siteId, int occurrence,
                JsonArray retainedLoops) {
            return BranchReplayContract.runtimeScheduleFromJson(
                    contract(summary, siteId, occurrence).toJson(),
                    retainedLoops);
        }

        /**
         * One heartbeat activation as the summary records it.
         *
         * <p>Two source-level decisions in path-condition order: the fault
         * marker, then the branch inside {@code addKeys} that only runs because
         * the marker answered false.</p>
         */
        private static JsonObject transcript() {
            JsonObject marker = binary(variable("Z_hadoopIpcRequestFails"),
                    "==", integer(0));
            JsonObject keyPresent = binary(variable("I_keyId"), "==",
                    integer(3));
            JsonArray path = new JsonArray();
            path.add(marker);
            path.add(keyPresent);

            JsonObject normalization = new JsonObject();
            normalization.addProperty("predicateNormalization",
                    BranchWitness.IDENTITY_NORMALIZATION);
            JsonArray mappings = new JsonArray();
            mappings.add(SummaryBranchMapping.witnessed(
                    BranchWitness.vmPcImmutable(HEARTBEAT, SEND_REQUEST, 11, 1,
                            false, marker, 0, normalization), 0,
                    SummaryBranchMapping.Policy.EXPLORE).toJson());
            mappings.add(SummaryBranchMapping.witnessed(
                    BranchWitness.vmPcImmutable(ADD_KEYS, "addKeys", 21, 1,
                            false, keyPresent, 1, normalization), 1,
                    SummaryBranchMapping.Policy.EXPLORE).toJson());

            JsonObject summary = new JsonObject();
            summary.add("pathCondition", path);
            summary.add("branchMappings", mappings);
            return summary;
        }

        private static BranchReplayContract contract(JsonObject summary,
                                                     String siteId,
                                                     int occurrence) {
            return BranchReplayContract.fromSummary(summary, siteId, occurrence);
        }

        private static BranchReplayContract.RuntimeSchedule schedule(
                JsonObject summary, String siteId, int occurrence) {
            // Through JSON on purpose: this is the decoder the replay JVM runs.
            return BranchReplayContract.runtimeScheduleFromJson(
                    contract(summary, siteId, occurrence).toJson());
        }

        private static JsonObject variable(String name) {
            JsonObject result = new JsonObject();
            result.addProperty("_type", "SymbolExpression");
            result.addProperty("_java_type", "I");
            result.addProperty("_exp", name);
            return result;
        }

        private static JsonObject integer(int value) {
            JsonObject result = new JsonObject();
            result.addProperty("_type", "ConstExpr");
            result.addProperty("_java_type", "I");
            result.addProperty("_exp", "Y_I_" + value);
            return result;
        }

        private static JsonObject binary(JsonObject left, String operator,
                                         JsonObject right) {
            JsonObject result = new JsonObject();
            result.addProperty("_type", "BinaryExpression");
            result.addProperty("_java_type", "Z");
            result.addProperty("_op", operator);
            result.add("_left", left);
            result.add("_right", right);
            return result;
        }
    }

}
