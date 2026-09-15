package edu.uva.liftlab.graphchecker.d3.plan;


import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Which locations a campaign tracks, and why tracking is not a declaration: a
 * carrier is a shared location this campaign's roots can still change, and one
 * forward closure from the root cells -- over value edges and {@code GUARD}
 * edges alike -- finds them.  The root set alone stays manual.
 */
public class RootDependentCarrierTest {

    private static final String NN = "REGION.nn";
    private static final String ORDERED = "<S: boolean snapshotDeletionOrdered>";
    private static final String GUARD_LOCAL = "<S: void deleteSnapshot()>::$z0";
    private static final String COUNTER = "<S: java.util.List snapshotsByNames>";
    private static final String UNRELATED = "<T: long heartbeatTime>";
    private static final String BLOCK_KEY = "org.apache.hadoop.hdfs"
            + ".security.token.block.BlockKey";
    /** bug3's own location: the reference whose writers a root decides. */
    private static final String CURRENT_KEY = "<S: " + BLOCK_KEY + " currentKey>";
    /** hdfs-17960's counter: the declared cell, its carrier and its store. */
    private static final String ATOMIC_VALUE =
            "<java.util.concurrent.atomic.AtomicInteger: int value>";
    private static final String NUM_SNAPSHOTS =
            "<S: java.util.concurrent.atomic.AtomicInteger numSnapshots>";
    private static final String DECREMENT = "<java.util.concurrent.atomic"
            + ".AtomicInteger: int getAndDecrement()>";
    private static final String DELETE = "<S: void deleteSnapshot()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * A branch the recording never took still carries the root.
     *
     * <p>The refined graph is the static candidate graph annotated with
     * what one execution bound, not filtered by it: a site the run never
     * reached keeps its edges, stamped {@code runtimeObserved: false}.</p>
     */
    @Test
    public void anEdgeTheRecordingNeverExecutedStillCarriesTheRoot()
            throws Exception {
        // The only path from the root to the counter is the arm this run skipped.
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                Arrays.asList(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, COUNTER, "GUARD")),
                fieldRead(COUNTER), fieldRead(UNRELATED));
        JsonArray selected = selection.select(NN,
                actions(fieldRead(COUNTER), fieldRead(UNRELATED)));
        assertEquals("an unexecuted branch is still a branch the root moves",
                "SYMBOLIC", member(selected, 0, "mode"));
        assertEquals("and nothing else is admitted along with it",
                "CONCRETE", member(selected, 1, "mode"));
        assertEquals("a location no root reaches is a constant for this run",
                ConcolicScheduler.SymbolicInputSelection.NOT_ROOT_DEPENDENT,
                member(selected, 1, "symbolicDemand"));
        assertTrue("the location is on the slice for every later stage",
                selection.carrierSlice().reachesLocation("S#snapshotsByNames", null));

        // And the write side of a DECLARED cell: the VM retains a location
        // by value, so the stores of the snapshot counter publish nothing
        // until the location is observed, and the graph already names those
        // stores as field_mutation edges carrying the callee that performed
        // them.  Selection only -- which sites the replay observes.
        JsonObject mutation = json("{\"kind\":\"field_mutation\","
                + "\"transferKind\":\"HEAP_WRITE\",\"fromCell\":\""
                + DELETE + "#u35\",\"toCell\":\"" + NUM_SNAPSHOTS
                + "\",\"method\":\"" + DELETE + "\",\"siteId\":\""
                + DELETE + "#u35\",\"unitIndex\":35,\"invoke\":\""
                + DECREMENT + "\"}");
        JsonArray sites = ConcolicScheduler.observedWriteSites(
                Collections.singletonList(mutation),
                Collections.singleton(ATOMIC_VALUE));
        assertEquals("one write site of the declared cell", 1, sites.size());
        assertEquals(DELETE + "#u35", member(sites, 0, "siteId"));
        assertEquals(ATOMIC_VALUE, member(sites, 0, "cell"));
        assertEquals("no declared cell, no observation", 0,
                ConcolicScheduler.observedWriteSites(
                        Collections.singletonList(mutation),
                        Collections.singleton(COUNTER)).size());
        assertTrue("the declared cell is read off the declared action alone",
                ConcolicScheduler.declaredInputCells(null).isEmpty());
    }

    /**
     * An in-slice object reference is tracked as an identity carrier.
     *
     * <p>bug3's {@code BlockKey currentKey}: the value of such a location is
     * an <em>identity</em> the version store records, so the port is admitted
     * with the reference demand: tracked at its getfield, never minted.</p>
     */
    @Test
    public void anInSliceReferenceIsTrackedAsAnIdentityCarrier() {
        JsonObject port = structureCarrier(CURRENT_KEY, BLOCK_KEY);
        ConcolicScheduler.RootDependenceSlice slice =
                ConcolicScheduler.RootDependenceSlice.forward(
                        Arrays.asList(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                                edge(GUARD_LOCAL, CURRENT_KEY, "GUARD")),
                        Collections.singleton(ORDERED));
        JsonArray planned = ConcolicScheduler.materializationPlan(goal(port),
                actions(port), ConcolicScheduler.DefinitionIndex.from(
                        Collections.<JsonObject>emptyList()),
                Collections.<String>emptySet(), new JsonArray(), slice);
        assertEquals("SYMBOLIC", member(planned, 0, "mode"));
        assertEquals(ConcolicScheduler.REFERENCE_CARRIER_DEMAND,
                member(planned, 0, "symbolicDemand"));
        assertTrue(planned.get(0).getAsJsonObject()
                .get("rootDependentStructureCarrier").getAsBoolean());
    }

    /** A selection with no declarations, seeded from one hook-owned root. */
    private ConcolicScheduler.SymbolicInputSelection seeded(
            List<JsonObject> graph, JsonObject... proposed) throws IOException {
        Path path = folder.newFolder().toPath().resolve("symbolic-inputs.jsonl");
        Files.write(path, ("{\"regionId\":\"" + NN + "\",\"fieldSignatures\":[\""
                + ORDERED + "\"]}\n").getBytes(StandardCharsets.UTF_8));
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(path,
                        Collections.singletonList(json("{\"regionId\":\"" + NN + "\"}")),
                        Collections.<RegionInstancePlan>emptyList());
        selection.seedCarrierSlice(graph,
                Collections.<Map.Entry<String, JsonArray>>singletonList(
                        new AbstractMap.SimpleImmutableEntry<>(NN, actions(proposed))));
        return selection;
    }

    private static JsonArray actions(JsonObject... proposed) {
        JsonArray actions = new JsonArray();
        for (JsonObject action : proposed) actions.add(action.deepCopy());
        return actions;
    }

    /** One edge, as the refinement stamps a site the run never reached. */
    private static JsonObject edge(String from, String to, String transfer) {
        return json("{\"fromCell\":\"" + from + "\",\"toCell\":\"" + to
                + "\",\"transferKind\":\"" + transfer + "\",\"graphKind\":"
                + "\"RUNTIME_REFINED_DATAFLOW\",\"runtimeObserved\":false}");
    }

    private static JsonObject fieldRead(String field) {
        return json("{\"mode\":\"SYMBOLIC\",\"sourceKind\":"
                + "\"ACTIVATION_FIELD_RECEIVER\",\"siteId\":\"<C: void m()>#u1\","
                + "\"symbol\":\"port.ACTIVATION_FIELD_RECEIVER\","
                + "\"accessFieldSignature\":\"" + field + "\",\"cell\":\""
                + field + "\"}");
    }

    /** A heap field read the refinement called a structural owner. */
    private static JsonObject structureCarrier(String field, String javaType) {
        return json("{\"mode\":\"SYMBOLIC\",\"sourceKind\":"
                + "\"ACTIVATION_FIELD_RECEIVER\",\"siteId\":\"<C: void m()>#u1\","
                + "\"symbol\":\"port." + field + "\",\"location\":"
                + "\"HEAP_OBJECT_FIELD\",\"javaType\":\"" + javaType
                + "\",\"dependencyRole\":\"" + DependencyRole
                .CONCRETE_STRUCTURE_CARRIER + "\",\"accessFieldSignature\":\""
                + field + "\",\"leafFieldSignature\":\"" + field
                + "\",\"cell\":\"" + field + "\",\"fieldPathDeclarations\":[\""
                + field + "\"],\"fieldPaths\":[[\""
                + FieldPathSpec.declaredField(field).name() + "\"]]}");
    }

    /** The region plan {@code materializationPlan} reads a root selector
     *  from, declaring this port's location as a shared carrier. */
    private static RegionInstancePlan.Goal goal(JsonObject port) {
        FieldPathSpec.DeclaredField field = FieldPathSpec.declaredField(CURRENT_KEY);
        JsonObject plan = json("{\"sourceKey\":\"test/nn0#epoch1\",\"occurrenceId\":"
                + "\"test/nn0#epoch1/region/" + NN + "#1\",\"relationKey\":"
                + "\"RELATION.1\",\"regionId\":\"" + NN + "\",\"closureGoals\":[{"
                + "\"goalId\":\"GOAL.1\",\"kind\":\"REGION_PATH_CLOSURE\","
                + "\"runtimeDefinitionMethods\":[],\"sharedCarriers\":[{\"kind\":"
                + "\"DECLARED_FIELD\",\"declaringClass\":\"" + field.owner()
                + "\",\"fieldName\":\"" + field.name() + "\"}]}]}");
        plan.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .add("symbolize", actions(port));
        return RegionInstancePlan.decode(plan).goals().get(0);
    }

    private static String member(JsonArray rows, int index, String name) {
        JsonObject row = rows.get(index).getAsJsonObject();
        return row.has(name) ? row.get(name).getAsString() : "";
    }

    private static JsonObject json(String row) {
        return JsonParser.parseString(row).getAsJsonObject();
    }
}
