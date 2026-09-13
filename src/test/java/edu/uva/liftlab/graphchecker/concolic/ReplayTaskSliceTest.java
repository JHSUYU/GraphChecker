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
    public void keepsOnlyWhatCanCarryARootTowardTheTarget()
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
    @Test
    public void aCarrierWriterNoRootReachesIsARecordedConstant()
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
    @Test
    public void theFatalReadsBackwardSliceNarrowsTheCaredLocations()
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
                        edge(GUARD_LOCAL, CARRIER, "GUARD")), 0);

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
    @Test
    public void everySiblingOfOneProvenanceIsReplayed() throws Exception {
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

    /**
     * A value that decides whether a container is mutated is on the chain of
     * every read of that container.
     *
     * <p>The graph is {@code removeExpiredKeys} in miniature: a root moves
     * {@code v}; {@code if (v &lt; c) container.remove(k)} states the guard
     * as an edge from {@code v} to the container's own location -- which is
     * how the refined graph spells {@code heap_mutation_path_guard} -- and
     * the failing branch reads {@code container.get(k)}.  No value edge runs
     * from {@code v} to the fatal read: the only path is the guard.  The
     * occurrence that writes {@code v}, and the one that reads it, must both
     * replay, or the arms of the fatal read cannot say whether the removal
     * happened.</p>
     */
    @Test
    public void aGuardOfAContainerMutationIsOnTheSlice() throws Exception {
        String guarded = "<S: java.util.Map container>";
        String guardedKey = "S#container";
        String decided = "<S: void sweep()>::$z1";
        String writer = occurrence("REGION.expiry");
        String reader = occurrence("REGION.sweep");
        List<JsonObject> graph = Arrays.asList(
                // root -> v, and v decides the remove on the container.
                edge(ROOT, CARRIER, "HEAP_WRITE"),
                edge(CARRIER, decided, "HEAP_READ"),
                guardOfMutation(decided, guarded),
                // the fatal read is a lookup on that same container.
                edge(guarded, FATAL_READ, "HEAP_READ"));
        List<RegionInstancePlan> plans = new ArrayList<>();
        plans.add(targetPlan(TARGET, edges()));
        plans.add(plan(ROOT_SITE, "REGION_PATH_CLOSURE",
                actions(fieldRead(ROOT)),
                edges(wire(ROOT_SITE, writer))));
        // The occurrence that writes v: its own read is the guard value, and
        // the plan gives it one shared-location flow onward.
        plans.add(plan(writer, "REGION_PATH_CLOSURE",
                actions(fieldRead(CARRIER)),
                edges(sharedFlow(writer, reader, CARRIER, CARRIER_KEY))));
        // The occurrence that mutates the container under the guard.  No
        // plan edge points into it -- the delivery was attributed elsewhere
        // -- so only the refined graph can say it carries the root.
        plans.add(plan(reader, "REGION_PATH_CLOSURE",
                actions(fieldRead(CARRIER)),
                edges(sharedFlow(reader, TARGET, guarded, guardedKey))));

        ConcolicScheduler.SymbolicInputSelection selection = selection();
        selection.seedCarrierSlice(graph, proposals(fieldRead(ROOT)));
        ReplayTaskSlice slice = ReplayTaskSlice.decide(plans, selection,
                graph, 0);

        assertTrue("the guard reaches the fatal read over the mutation it "
                + "decides", selection.carrierSlice()
                .reachingFatalRead(graph, singleton(FATAL_READ))
                .reachesLocation(guardedKey, null));
        assertTrue("the guard value is on the slice",
                selection.carrierSlice()
                        .reachingFatalRead(graph, singleton(FATAL_READ))
                        .reachesLocation(CARRIER_KEY, null));
        assertTrue("the writer of the guard value replays",
                slice.keeps(writer));
        assertTrue("so does the occurrence whose mutation it decides",
                slice.keeps(reader));
        assertEquals(reasons(ReplayTaskSlice.ROOT_DEPENDENT_FLOW,
                        ReplayTaskSlice.CARRIER_WRITER),
                slice.reasons(writer));
        assertEquals(reasons(ReplayTaskSlice.ROOT_DEPENDENT_FLOW,
                        ReplayTaskSlice.FATAL_READ_WRITER,
                        ReplayTaskSlice.CARRIER_WRITER),
                slice.reasons(reader));
    }

    /**
     * The expected-shape hint is read against, never enforced: a schedule
     * over it is published in full, because a campaign bigger than its
     * author expected is a fact to read, not tasks to drop at random.
     */
    @Test
    public void theBudgetIsTelemetryAndNeverACap() throws Exception {
        ReplayTaskSlice narrow = ReplayTaskSlice.decide(plans(), seeded(),
                Collections.<JsonObject>emptyList(), 1);

        List<String> selected = Arrays.asList(TARGET, ROOT_SITE, LOADER);
        JsonObject telemetry = narrow.telemetry(selected);
        assertEquals(2, telemetry.get("keptOccurrenceCount").getAsInt());
        assertEquals(1, telemetry.get("replayTaskBudget").getAsInt());
        assertEquals(ReplayTaskSlice.BUDGET_EXCEEDED,
                telemetry.get("replayTaskBudgetStatus").getAsString());
        assertTrue("no task is dropped to meet the hint",
                narrow.keeps(TARGET) && narrow.keeps(ROOT_SITE));

        JsonObject roomy = ReplayTaskSlice.decide(plans(), seeded(),
                Collections.<JsonObject>emptyList(), 8).telemetry(selected);
        assertEquals("REPLAY_TASK_IN_BUDGET",
                roomy.get("replayTaskBudgetStatus").getAsString());
        assertFalse("an unstated hint judges nothing",
                decide(plans(), seeded()).telemetry(selected)
                        .has("replayTaskBudgetStatus"));
    }

    @Test
    public void aWithheldCarrierSliceNarrowsNothing() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = selection();
        // No graph edge names the root, so the carrier slice is withheld.
        selection.seedCarrierSlice(Collections.<JsonObject>emptyList(),
                proposals(fieldRead(ROOT)));

        ReplayTaskSlice slice = decide(plans(), selection);

        assertFalse(slice.applied());
        assertTrue(slice.keeps(LOADER));
        assertTrue(slice.keeps(DEAD_WIRE));
        List<JsonObject> rows = slice.rows(Arrays.asList(LOADER, TARGET));
        assertEquals(ReplayTaskSlice.WITHHELD,
                rows.get(1).get("reason").getAsString());
        assertEquals(0, rows.get(0).get("prunedOccurrenceCount").getAsInt());
    }

    @Test
    public void theArtifactNamesEveryPrunedOccurrenceWithItsReason()
            throws Exception {
        ReplayTaskSlice slice = decide(plans(), seeded());

        List<JsonObject> rows = slice.rows(
                Arrays.asList(TARGET, LOADER, WRITER));

        JsonObject telemetry = rows.get(0);
        assertEquals(ReplayTaskSlice.TELEMETRY,
                telemetry.get("kind").getAsString());
        assertEquals(3, telemetry.get("selectedOccurrenceCount").getAsInt());
        assertEquals(2, telemetry.get("keptOccurrenceCount").getAsInt());
        assertEquals(1, telemetry.get("prunedOccurrenceCount").getAsInt());
        JsonObject loader = rows.get(2);
        assertEquals(ReplayTaskSlice.DECISION, loader.get("kind").getAsString());
        assertEquals(LOADER, loader.get("occurrenceId").getAsString());
        assertEquals("PRUNE", loader.get("decision").getAsString());
        assertEquals(ReplayTaskSlice.PRUNED, loader.get("reason").getAsString());
        assertEquals(0, loader.getAsJsonArray("keepReasons").size());
        assertEquals(ReplayTaskSlice.KEPT,
                rows.get(3).get("reason").getAsString());
    }

    @Test
    public void anOccurrenceThePlanNeverNamedIsNotItsToDrop()
            throws Exception {
        ReplayTaskSlice slice = decide(plans(), seeded());

        assertTrue(slice.keeps(occurrence("REGION.unplanned")));
    }

    // --- fixture -----------------------------------------------------------

    private static ReplayTaskSlice decide(
            List<RegionInstancePlan> plans,
            ConcolicScheduler.SymbolicInputSelection selection) {
        return ReplayTaskSlice.decide(plans, selection,
                Collections.<JsonObject>emptyList(), 0);
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
                Collections.singletonList(region));
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
}
