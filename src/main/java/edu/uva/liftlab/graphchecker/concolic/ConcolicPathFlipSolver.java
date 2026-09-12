package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner.number;
import static edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner.options;
import static edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner.requiredPath;
import static edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner.requiredValue;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Solves exactly one canonical path-flip query and emits its replay task.
 * Each invocation is intentionally process-local so independent
 * tasks can be run by separate workers.
 */
public final class ConcolicPathFlipSolver {
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicPathFlipSolver() {
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> options = options(argv);
        String queryKey = requiredValue(options, "query-key");
        if (!ConcolicConstraintSolver.canonicalQueryKey(queryKey)) {
            throw new IllegalArgumentException(
                    "--query-key must be lowercase SHA-256");
        }
        JsonObject task = ArtifactIO.uniqueIndex(ArtifactIO.readJsonl(
                requiredPath(options, "worklist")), "queryKey").get(queryKey);
        if (task == null) {
            throw new IOException("Path task not found: " + queryKey);
        }
        try {
            task = SharedExpressionTable.expand(task);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Path task has an invalid shared expression "
                    + "table", malformed);
        }
        List<JsonObject> taskRows = ArtifactIO.readJsonl(
                requiredPath(options, "task-plan"));
        Map<String, JsonObject> taskById = ArtifactIO.uniqueIndex(
                taskRows, "taskId");
        JsonObject bundle;
        try {
            bundle = LinkedReplayBundle.decode(task);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Path task has an invalid linked bundle", malformed);
        }
        String sourceId = LinkedReplayBundle.primarySourceTaskId(bundle);
        if (!sourceId.equals(string(task, "sourceTaskId"))) {
            throw new IOException("Path task and linked primary differ");
        }
        JsonObject source = taskById.get(sourceId);
        if (source == null) {
            throw new IOException("Source execution task not found: "
                    + sourceId);
        }
        List<JsonObject> linkedSources;
        try {
            // Solver workers receive the task plan as an external artifact.
            // Decode the full task contract here instead of trusting the
            // worklist's sourceTaskId alone; this includes exact configured
            // source-phase sequencing and occurrence ownership.
            ExecutionTask.decode(source);
            linkedSources = LinkedReplayBundle.sourceTasks(bundle, taskById);
            for (JsonObject linked : linkedSources) {
                ExecutionTask.decode(linked);
            }
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Source execution task is malformed: "
                    + sourceId, malformed);
        }

        ConcolicConstraintSolver.Result solved =
                ConcolicConstraintSolver.solve(task, linkedSources, source,
                        Paths.get(firstNonBlank(options.get("z3"), "z3")),
                        number(options, "solver-timeout-ms", 20_000L));
        String status = string(solved.record, "status");
        List<JsonObject> replay = "SAT_MODEL_READY".equals(status)
                ? PathReplayTaskFactory.createLinked(task, taskById,
                solved.modelAssignments, array(solved.record,
                        ExecutionTask.GUARDED_READ_ASSIGNMENTS),
                solved.replayContract)
                : Collections.<JsonObject>emptyList();
        solved.record.addProperty("primarySourceTaskId", sourceId);
        solved.record.addProperty("regionId", string(task, "regionId"));
        solved.record.addProperty("goalId", string(task, "goalId"));
        solved.record.addProperty("sourceSummaryId",
                string(task, "sourceSummaryId"));
        solved.record.addProperty("sourcePathKey",
                string(task, "sourcePathKey"));
        solved.record.addProperty("sourceActivationOccurrenceId",
                string(task, "sourceActivationOccurrenceId"));
        solved.record.addProperty(LinkedReplayBundle.FAMILY_DIGEST_FIELD,
                string(bundle, LinkedReplayBundle.FAMILY_DIGEST_FIELD));
        solved.record.addProperty(LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD,
                string(bundle, LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD));
        Path directory = requiredPath(options, "output-dir");
        String record = PRETTY.toJson(solved.record);
        ArtifactIO.replace(directory.resolve("path_flip_solver_result.json"),
                record + System.lineSeparator());
        ArtifactIO.replace(directory.resolve("path_flip_query.smt2"),
                solved.smtLib);
        ArtifactIO.replaceJsonl(directory.resolve("execution_task_plan.jsonl"),
                replay);
        System.out.println(record);

        // UNSUPPORTED and MATERIALIZATION_GAP are recorded terminal
        // exploration outcomes, not process failures: the caller closes over
        // either as a named exploration gap and the pipeline proceeds to
        // candidates/compose.  Only a solver that reached no verdict at all
        // still fails the process.
        if (!terminalExplorationOutcome(status)) {
            System.exit(2);
        }
    }

    /** True for a status the caller can record and move past. */
    static boolean terminalExplorationOutcome(String status) {
        return "SAT_MODEL_READY".equals(status)
                || "UNSAT".equals(status)
                || "UNSUPPORTED".equals(status)
                || "MATERIALIZATION_GAP".equals(status);
    }
}
