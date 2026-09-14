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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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
        // The bundle is the one authority on which member is primary; the
        // worklist's sourceTaskId is the same planner's copy of it.
        String sourceId = LinkedReplayBundle.primarySourceTaskId(bundle);
        JsonObject source = taskById.get(sourceId);
        if (source == null) {
            throw new IOException("Source execution task not found: "
                    + sourceId);
        }
        List<JsonObject> linkedSources;
        try {
            // Solver workers receive the task plan as an external artifact.
            // Decode the full task contract here - exact configured
            // source-phase sequencing and occurrence ownership included -
            // and hand the decoded closure to the replay factory, which
            // therefore never decodes a task or the bundle again.
            linkedSources = LinkedReplayBundle.sourceTasks(bundle, taskById);
            for (JsonObject linked : linkedSources) {
                ExecutionTask.decode(linked);
            }
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Source execution task is malformed: "
                    + sourceId, malformed);
        }

        // What this one obligation cost, start to verdict: encoding the
        // query and running the solver on it.  Until this was recorded the
        // only per-query timings a campaign kept were the final extractor's
        // own attempt rows, so an EXPLORE stage could spend ten minutes
        // without saying on what.
        long startedAtMillis = System.currentTimeMillis();
        long startedAtNanos = System.nanoTime();
        ConcolicConstraintSolver.Result solved =
                ConcolicConstraintSolver.solve(task, linkedSources, source,
                        Paths.get(firstNonBlank(options.get("z3"), "z3")),
                        number(options, "solver-timeout-ms", 20_000L),
                        number(options, "clock-skew-ms",
                                ClockRootPhysics.DEFAULT_SKEW_MILLIS));
        long elapsedMillis = Math.max(0L,
                (System.nanoTime() - startedAtNanos) / 1_000_000L);
        String status = optionalString(solved.record, "status");
        if (isSolverTimeout(status,
                optionalString(solved.record, "reason"))) {
            // A flip query the solver could not decide inside its budget is
            // an unexplored sibling path, not a broken solver: README keeps
            // an unobserved sibling as coverage telemetry, which blocks only
            // a closed UNSAT conclusion.  Promote it to a first-class
            // exploration status so the caller records it like any other
            // named gap instead of aborting the campaign.
            status = SOLVER_TIMEOUT;
            solved.record.addProperty("status", status);
        }
        List<JsonObject> replay = "SAT_MODEL_READY".equals(status)
                ? PathReplayTaskFactory.createLinked(task, bundle,
                linkedSources, solved.modelAssignments,
                array(solved.record,
                        ExecutionTask.GUARDED_READ_ASSIGNMENTS),
                solved.replayContract)
                : Collections.<JsonObject>emptyList();
        solved.record.addProperty("startedAtMillis", startedAtMillis);
        solved.record.addProperty("elapsedMillis", elapsedMillis);
        solved.record.addProperty("primarySourceTaskId", sourceId);
        solved.record.addProperty("regionId", optionalString(task, "regionId"));
        solved.record.addProperty("goalId", optionalString(task, "goalId"));
        solved.record.addProperty("sourceSummaryId",
                optionalString(task, "sourceSummaryId"));
        solved.record.addProperty("sourcePathKey",
                optionalString(task, "sourcePathKey"));
        solved.record.addProperty("sourceActivationOccurrenceId",
                optionalString(task, "sourceActivationOccurrenceId"));
        solved.record.addProperty(LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD,
                optionalString(bundle, LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD));
        Path directory = requiredPath(options, "output-dir");
        String record = PRETTY.toJson(solved.record);
        ArtifactIO.replace(directory.resolve("path_flip_solver_result.json"),
                record + System.lineSeparator());
        // Always written, whatever the verdict.  An UNSAT obligation is the
        // one a reader most needs to see the query for -- what a flip
        // asserted that contradicts negating its decision is not derivable
        // from the verdict -- and an obligation that never reached an
        // encoding says that in the file rather than leaving none.
        ArtifactIO.replace(directory.resolve("path_flip_query.smt2"),
                solved.smtLib.isEmpty()
                        ? "; no query was encoded: "
                        + firstNonBlank(optionalString(solved.record,
                        "status"), "UNKNOWN") + " "
                        + optionalString(solved.record, "reason")
                        + System.lineSeparator()
                        : solved.smtLib);
        ArtifactIO.replaceJsonl(directory.resolve("execution_task_plan.jsonl"),
                replay);
        System.out.println(record);

        // UNSUPPORTED, MATERIALIZATION_GAP and SOLVER_TIMEOUT are recorded
        // terminal exploration outcomes, not process failures: the caller
        // closes over each as a named exploration gap and the pipeline
        // proceeds to candidates/compose.  Only a solver that failed
        // outright - crashed, or rejected the query - still fails the
        // process.
        if (!terminalExplorationOutcome(status)) {
            System.exit(2);
        }
    }

    /** Exploration status of a flip query the solver could not decide in
     *  its configured budget. */
    static final String SOLVER_TIMEOUT = "SOLVER_TIMEOUT";

    /** True when the constraint solver's own verdict was "no verdict in
     *  time", as opposed to a crashed or rejected query. */
    static boolean isSolverTimeout(String status, String reason) {
        return "SOLVER_ERROR".equals(status) && SOLVER_TIMEOUT.equals(reason);
    }

    /** True for a status the caller can record and move past. */
    static boolean terminalExplorationOutcome(String status) {
        return "SAT_MODEL_READY".equals(status)
                || "UNSAT".equals(status)
                || "UNSUPPORTED".equals(status)
                || "MATERIALIZATION_GAP".equals(status)
                || SOLVER_TIMEOUT.equals(status);
    }
}
