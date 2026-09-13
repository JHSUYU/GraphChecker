package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
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
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Which shared carriers a scheduled task keeps declaring.
 *
 * <p>HDFS-17960 in miniature: the root {@code snapshotDeletionOrdered}
 * guards a write of {@code snapshotCounter}; the counter's Atomic leaf is
 * read through an accessor whose value lands in a local the root reaches;
 * the fsimage loader's {@code layoutVersion} is written by nothing a root
 * moves.  The planner declared all of them on every task.</p>
 */
public class SharedCarrierSliceTest {

    private static final String ROOT_REGION = "REGION.root";
    private static final String ROOT = "<S: boolean snapshotDeletionOrdered>";
    private static final String GUARD_LOCAL = "<S: void deleteSnapshot()>::$z0";
    private static final String COUNTER = "<S: int snapshotCounter>";
    private static final String NUM_SNAPSHOTS =
            "<S: java.util.concurrent.atomic.AtomicInteger numSnapshots>";
    private static final String ACCESSOR_LOCAL = "<S: int getNumSnapshots()>::$i0";
    private static final String ATOMIC_VALUE =
            "<java.util.concurrent.atomic.AtomicInteger: int value>";
    private static final String UNRELATED = "<L: long layoutVersion>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void keepsOnlyTheCarriersARootCanReach() throws Exception {
        ExecutionTask task = task("REGION.target#1",
                carrier("S", "snapshotDeletionOrdered", "Z"),
                carrier("S", "snapshotCounter", "I"),
                carrier("java.util.concurrent.atomic.AtomicInteger", "value",
                        "I"),
                carrier("L", "layoutVersion", "J"));

        SharedCarrierSlice slice = SharedCarrierSlice.apply(
                Collections.singletonList(task), seeded());

        assertTrue(slice.applied());
        assertEquals(Arrays.asList("S#snapshotDeletionOrdered",
                "S#snapshotCounter",
                "java.util.concurrent.atomic.AtomicInteger#value"),
                locations(task));
        assertEquals(3, slice.keptCarrierCount());
        assertEquals(1, slice.droppedCarrierCount());
        assertEquals(Collections.singleton("L#layoutVersion"),
                slice.droppedLocations());
    }

    // --- fixture -----------------------------------------------------------

    /**
     * root -> guard local -GUARD-> counter; counter -> the accessor's local
     * (numSnapshots.get()); nothing reaches layoutVersion.
     */
    private ConcolicScheduler.SymbolicInputSelection seeded()
            throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection = selection();
        selection.seedCarrierSlice(Arrays.asList(
                edge(ROOT, GUARD_LOCAL, "HEAP_READ"),
                edge(GUARD_LOCAL, COUNTER, "GUARD"),
                edge(COUNTER, NUM_SNAPSHOTS, "HEAP_WRITE"),
                edge(NUM_SNAPSHOTS, ACCESSOR_LOCAL, "CALL_RETURN"),
                edge("<X: int other>", UNRELATED, "HEAP_WRITE")),
                proposals(fieldRead(ROOT), fieldRead(UNRELATED),
                        accessorRead(ATOMIC_VALUE, ACCESSOR_LOCAL)));
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
        JsonArray actions = new JsonArray();
        for (JsonObject action : proposed) actions.add(action.deepCopy());
        List<Map.Entry<String, JsonArray>> rows = new ArrayList<>();
        rows.add(new AbstractMap.SimpleImmutableEntry<>(ROOT_REGION,
                actions));
        return rows;
    }

    private static ExecutionTask task(String occurrence,
                                      JsonObject... carriers) {
        JsonObject task = new JsonObject();
        task.addProperty("sourceKey", "test/nn0#epoch1");
        task.addProperty("occurrenceId", occurrence(occurrence));
        task.addProperty("relationKey", "RELATION." + occurrence);
        task.addProperty("regionId",
                occurrence.substring(0, occurrence.indexOf('#')));
        task.addProperty("taskId", "TASK." + occurrence);
        task.addProperty("goalId", "GOAL." + occurrence);
        task.add("inputActions", new JsonArray());
        JsonArray declared = new JsonArray();
        for (JsonObject carrier : carriers) declared.add(carrier);
        task.add(ExecutionTask.SHARED_CARRIERS, declared);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        return ExecutionTask.decode(task);
    }

    private static String occurrence(String region) {
        return "test/nn0#epoch1/region/" + region;
    }

    private static JsonObject carrier(String owner, String field,
                                      String descriptor) {
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "DECLARED_FIELD");
        carrier.addProperty("declaringClass", owner);
        carrier.addProperty("fieldName", field);
        carrier.addProperty("descriptor", descriptor);
        carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        carrier.add("fieldPath", new JsonArray());
        return carrier;
    }

    private static List<String> locations(ExecutionTask task) {
        List<String> keys = new ArrayList<>();
        for (com.google.gson.JsonElement element : task.sharedCarriers()) {
            keys.add(SharedCarrierSlice.location(element.getAsJsonObject()));
        }
        return keys;
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

    private static JsonObject accessorRead(String field, String returnLocal) {
        JsonObject action = base("ACCESSOR_RETURN");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("leafFieldSignature", field);
        action.addProperty("cell", field);
        JsonArray dependency = new JsonArray();
        dependency.add(returnLocal);
        action.add("dependencyCells", dependency);
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
}
