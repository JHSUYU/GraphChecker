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
 * must replay the target, every root site, every writer of a carrier and
 * whatever those reach over a carrier flow or a wire, and nothing else.</p>
 */
public class ReplayTaskSliceTest {

    private static final String ROOT_REGION = "REGION.root";
    private static final String ROOT = "<S: boolean snapshotDeletionOrdered>";
    private static final String GUARD_LOCAL = "<S: void deleteSnapshot()>::$z0";
    private static final String CARRIER = "<S: int snapshotCounter>";
    private static final String CARRIER_KEY = "S#snapshotCounter";
    private static final String UNRELATED = "<L: long layoutVersion>";
    private static final String UNRELATED_KEY = "L#layoutVersion";

    private static final String TARGET = occurrence("REGION.target");
    private static final String ROOT_SITE = occurrence(ROOT_REGION);
    private static final String WRITER = occurrence("REGION.writer");
    private static final String LOADER = occurrence("REGION.loader");
    private static final String WIRE_CONSUMER = occurrence("REGION.wire");
    private static final String DEAD_WIRE = occurrence("REGION.deadwire");
    private static final String HOOK_PHASE = occurrence("REGION.phase");
    private static final String FAULT = occurrence("REGION.fault");

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void keepsOnlyWhatCanCarryARootTowardTheTarget()
            throws Exception {
        ReplayTaskSlice slice = ReplayTaskSlice.decide(plans(), seeded());

        assertTrue(slice.applied());
        assertEquals(reasons(ReplayTaskSlice.TARGET_REACH,
                ReplayTaskSlice.ROOT_DEPENDENT_FLOW), slice.reasons(TARGET));
        assertEquals(reasons(ReplayTaskSlice.ROOT_SITE),
                slice.reasons(ROOT_SITE));
        assertEquals("the carrier flow into the target names its writer",
                reasons(ReplayTaskSlice.CARRIER_WRITER), slice.reasons(WRITER));
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

    @Test
    public void aWithheldCarrierSliceNarrowsNothing() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = selection();
        // No graph edge names the root, so the carrier slice is withheld.
        selection.seedCarrierSlice(Collections.<JsonObject>emptyList(),
                proposals(fieldRead(ROOT)));

        ReplayTaskSlice slice = ReplayTaskSlice.decide(plans(), selection);

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
        ReplayTaskSlice slice = ReplayTaskSlice.decide(plans(), seeded());

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
        ReplayTaskSlice slice = ReplayTaskSlice.decide(plans(), seeded());

        assertTrue(slice.keeps(occurrence("REGION.unplanned")));
    }

    // --- fixture -----------------------------------------------------------

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
        plans.add(plan(WIRE_CONSUMER, "REGION_PATH_CLOSURE", actions(),
                edges()));
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
        Path declarations = folder.newFile("symbolic-inputs.jsonl").toPath();
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

    private static String regionOf(String occurrence) {
        String tail = occurrence.substring(
                occurrence.lastIndexOf("/region/") + "/region/".length());
        return tail.substring(0, tail.lastIndexOf('#'));
    }

    private static RegionInstancePlan plan(String occurrence, String kind,
                                           JsonArray symbolize,
                                           JsonArray edgeBindings) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL." + regionOf(occurrence));
        goal.addProperty("kind", kind);
        goal.add("symbolize", symbolize);
        goal.add("runtimeDefinitionMethods", new JsonArray());
        goal.add("edgeBindings", edgeBindings);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        JsonObject plan = new JsonObject();
        plan.addProperty("sourceKey", "test/nn0#epoch1");
        plan.addProperty("occurrenceId", occurrence);
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

    private static JsonObject edge(String from, String to, String kind) {
        JsonObject row = new JsonObject();
        row.addProperty("fromCell", from);
        row.addProperty("toCell", to);
        row.addProperty("transferKind", kind);
        return row;
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
