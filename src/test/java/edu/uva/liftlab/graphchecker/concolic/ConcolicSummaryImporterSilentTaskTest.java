package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A planned task the run left no row for at all must be named.
 *
 * <p>Without this the selected case set is short one region in silence, and
 * a later stage meets the hole as an unresolvable writer case -- a guarded
 * read whose {@code exactlyOne} cannot cover its candidates -- rather than
 * as a coverage gap naming the region that never ran.</p>
 */
public final class ConcolicSummaryImporterSilentTaskTest {
    private static final String CODE = "REGION_TASK_NO_PUBLISHED_ACTIVATION";
    private static final String RAN = "TASK.SEED.ran";
    private static final String SILENT = "TASK.SEED.silent";
    private static final String SKIPPED = "TASK.SEED.skipped";
    private static final String SILENT_OCCURRENCE =
            "app/dn0#epoch0/region/REGION.silent#1";

    @Rule public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void plannedTaskWithNoRowAtAllIsNamedWhileSkipAndRunAreNot()
            throws Exception {
        List<JsonObject> plan = new ArrayList<>();
        plan.add(task(RAN, "app/dn0#epoch0/region/REGION.ran#1",
                "REGION.ran"));
        plan.add(task(SILENT, SILENT_OCCURRENCE, "REGION.silent"));
        plan.add(task(SKIPPED, "app/dn0#epoch0/region/REGION.skipped#1",
                "REGION.skipped"));

        List<JsonObject> results = new ArrayList<>();
        results.add(regionResult(RAN, "REGION.ran"));
        // A skipped region still publishes a row, so it answers for itself
        // through that row's own diagnostic and must not be named here too.
        results.add(skippedResult(SKIPPED, "REGION.skipped"));

        List<String> diagnostics = diagnostics(plan, results);

        List<String> silent = withCode(diagnostics, CODE);
        assertEquals(diagnostics.toString(), 1, silent.size());
        assertTrue(silent.toString(), silent.get(0).contains(SILENT));
        assertTrue("the gap must name the anchor the region never answered: "
                + silent, silent.get(0).contains(SILENT_OCCURRENCE));
        assertFalse(silent.toString(), silent.get(0).contains(RAN));
        assertFalse(silent.toString(), silent.get(0).contains(SKIPPED));
    }

    @Test
    public void everyPlannedTaskPublishingLeavesNoSilentTaskGap()
            throws Exception {
        List<JsonObject> plan = Collections.singletonList(
                task(RAN, "app/dn0#epoch0/region/REGION.ran#1", "REGION.ran"));
        List<JsonObject> results = Collections.singletonList(
                regionResult(RAN, "REGION.ran"));

        assertTrue(withCode(diagnostics(plan, results), CODE).isEmpty());
    }

    private List<String> diagnostics(List<JsonObject> plan,
                                     List<JsonObject> results)
            throws IOException {
        Path planFile = write("task-plan.jsonl", plan);
        Path resultFile = write("results.jsonl", results);
        Path output = folder.getRoot().toPath().resolve("summaries.jsonl");
        Path diagnosticFile =
                folder.getRoot().toPath().resolve("diagnostics.jsonl");
        Path deltaFile = folder.getRoot().toPath().resolve("delta.jsonl");

        ConcolicSummaryImporter.importSummaries(resultFile, planFile,
                Collections.<String>emptySet(), output, diagnosticFile,
                deltaFile, "iteration-0");

        return Files.exists(diagnosticFile)
                ? Files.readAllLines(diagnosticFile, StandardCharsets.UTF_8)
                : Collections.<String>emptyList();
    }

    private static List<String> withCode(List<String> rows, String code) {
        List<String> matched = new ArrayList<>();
        for (String row : rows) {
            if (row.contains("\"" + code + "\"")) matched.add(row);
        }
        return matched;
    }

    private Path write(String name, List<JsonObject> rows)
            throws IOException {
        Path path = folder.getRoot().toPath().resolve(name);
        List<String> lines = new ArrayList<>();
        for (JsonObject row : rows) lines.add(row.toString());
        Files.write(path, lines, StandardCharsets.UTF_8);
        return path;
    }

    private static JsonObject task(String taskId, String occurrence,
                                   String regionId) {
        JsonObject task = new JsonObject();
        task.addProperty("sourceKey", "app/dn0#epoch0");
        task.addProperty("occurrenceId", occurrence);
        task.addProperty("relationKey", "relation");
        task.addProperty("regionId", regionId);
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL." + taskId);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        task.add("inputActions", new JsonArray());
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(task);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        return task;
    }

    private static JsonObject regionResult(String taskId, String regionId) {
        JsonObject row = new JsonObject();
        row.addProperty("event", "CONCOLIC_REGION_RESULT");
        row.addProperty("taskId", taskId);
        row.addProperty("regionId", regionId);
        row.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        return row;
    }

    private static JsonObject skippedResult(String taskId, String regionId) {
        JsonObject row = new JsonObject();
        row.addProperty("event", "CONCOLIC_REGION_SKIPPED");
        row.addProperty("taskId", taskId);
        row.addProperty("regionId", regionId);
        row.addProperty("reason", "prefix not yet complete");
        return row;
    }
}
