package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * OCC-1 must respect the loop bound: a LOOP_BODY_ROOT region unrolls its
 * captured occurrence set at most K_L times, and further iterations are a
 * bounded cut that runs concretely without capture.
 *
 * <p>Without the cap the DN {@code offerService} region published one
 * occurrence per heartbeat -- ~128 -- and every iteration paid for full
 * symbolic capture, ballooning REPLAY past an hour.  The concrete workload
 * still runs every heartbeat; capture stops after K_L.</p>
 */
public class ConcolicRegionRuntimeLoopBoundOccurrenceCapTest {
    private static final String TASK = "TASK.loop-body";
    private static final String SOURCE_KEY = "test/loop#epoch0";
    private static final String OCCURRENCE =
            SOURCE_KEY + "/region/SERVICE#1";
    private static final String ROOT = "<example.Service: void run()>";
    private static final int K_L = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;
    private Path results;

    @Before
    public void rememberProperties() {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    /**
     * A loop-body region admitting K_L+3 activations publishes exactly K_L
     * occurrences and one bounded-cut marker.
     */
    @Test
    public void aLoopBodyRegionCapsItsOccurrenceSetAtKL() throws Exception {
        load(true);

        int published = ConcolicRegionRuntime.simulateAdmissionsForTests(
                TASK, K_L + 3);
        assertEquals(K_L, published);

        List<JsonObject> markers = markerRows();
        assertEquals(markers.toString(), 1, markers.size());
        JsonObject marker = markers.get(0);
        assertEquals(TASK, marker.get("taskId").getAsString());
        assertEquals("LOOP_OCCURRENCES_BOUNDED",
                marker.get("skipKind").getAsString());
        assertEquals(OCCURRENCE,
                marker.get("plannedOccurrenceId").getAsString());
        assertEquals(K_L, marker.get("boundedAt").getAsInt());
    }

    /** A non-loop-body region is uncapped, exactly as OCC-1 admits it now. */
    @Test
    public void aNonLoopBodyRegionIsUncapped() throws Exception {
        load(false);

        int published = ConcolicRegionRuntime.simulateAdmissionsForTests(
                TASK, K_L + 5);
        assertEquals(K_L + 5, published);
        assertTrue(markerRows().toString(), markerRows().isEmpty());
    }

    private List<JsonObject> markerRows() throws Exception {
        List<JsonObject> rows = new ArrayList<>();
        if (!Files.exists(results)) return rows;
        for (String line : Files.readAllLines(results,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = new JsonParser().parse(line).getAsJsonObject();
            if ("CONCOLIC_REGION_SKIPPED".equals(
                    row.get("event").getAsString())
                    && "LOOP_OCCURRENCES_BOUNDED".equals(
                    row.get("skipKind").getAsString())) {
                rows.add(row);
            }
        }
        return rows;
    }

    /**
     * The occurrence cap is the ROOT loop's own K_L, not the region's global
     * max.  The DN {@code offerService} region declares its root loop at K_L=8
     * while an inner {@code allKeys}-walk declares 24; the occurrence set must
     * unroll 8 times (the root loop), not 24 -- each extra occurrence
     * re-snapshots the growing map and, under the 600-min lifetime, explodes
     * the symbolic session.
     */
    @Test
    public void theCapIsTheRootLoopBoundNotTheRegionMax() throws Exception {
        loadWithBounds();

        int published = ConcolicRegionRuntime.simulateAdmissionsForTests(
                TASK, 24 + 3);
        assertEquals("capped at the root loop's K_L=3, not the region max 24",
                3, published);

        List<JsonObject> markers = markerRows();
        assertEquals(markers.toString(), 1, markers.size());
        assertEquals(3, markers.get(0).get("boundedAt").getAsInt());
    }

    private void loadWithBounds() throws Exception {
        Path plan = folder.newFile("rootbound-plan.jsonl").toPath();
        JsonObject task = task(true);
        // Root loop declares K_L=3; an inner loop declares 24 (region max).
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put("ROOT#u1", 3);
        declared.put("INNER#u9", 24);
        LoopBoundPolicy.cfgBackedges(K_L, declared).writeTo(task);
        task.getAsJsonObject("rootLoop").addProperty("loopSiteId", "ROOT#u1");
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        results = folder.getRoot().toPath().resolve("rootbound-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(1,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private void load(boolean loopBody) throws Exception {
        Path plan = folder.newFile((loopBody ? "loop" : "flat")
                + "-plan.jsonl").toPath();
        Files.write(plan, (task(loopBody) + "\n")
                .getBytes(StandardCharsets.UTF_8));
        results = folder.getRoot().toPath().resolve(
                (loopBody ? "loop" : "flat") + "-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(1,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private static JsonObject task(boolean loopBody) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL." + TASK);
        task.addProperty("sourceKey", SOURCE_KEY);
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.SERVICE");
        task.addProperty("regionId", "SERVICE");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", SOURCE_KEY);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        task.add("edgeBindings", new JsonArray());
        if (loopBody) {
            task.addProperty("rootAuthority", "LOOP_BODY_ROOT");
            JsonObject rootLoop = new JsonObject();
            rootLoop.addProperty("rootLoopMethod", ROOT);
            rootLoop.addProperty("headerUnitIndex", 1);
            task.add("rootLoop", rootLoop);
        }
        LoopBoundPolicy.cfgBackedges(K_L).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
