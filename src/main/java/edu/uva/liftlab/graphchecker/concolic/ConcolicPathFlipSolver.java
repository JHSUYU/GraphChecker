package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
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
        Arguments arguments = Arguments.parse(argv);
        Result result = solve(arguments);
        System.out.println(writeOutputs(arguments.outputDirectory, result));
        String status = string(result.solve.record, "status");
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

    static Result solve(Arguments arguments) throws Exception {
        JsonObject task = exactTask(ArtifactIO.readJsonl(arguments.worklist),
                arguments.queryKey);
        Map<String, JsonObject> executionTasks = ArtifactIO.uniqueIndex(
                ArtifactIO.readJsonl(arguments.executionTasks), "taskId");
        String sourceId = string(task, "sourceTaskId");
        JsonObject source = executionTasks.get(sourceId);
        if (source == null) {
            throw new IOException("Source execution task not found: "
                    + sourceId);
        }

        ConcolicConstraintSolver.Result solved =
                ConcolicConstraintSolver.solve(task, source, arguments.z3,
                        arguments.solverTimeoutMillis);
        JsonObject replay = "SAT_MODEL_READY".equals(string(solved.record,
                "status"))
                ? PathReplayTaskFactory.create(task, source,
                solved.modelAssignments, solved.replayContract) : null;
        return new Result(solved, replay);
    }

    static String writeOutputs(Path directory, Result result)
            throws IOException {
        String record = PRETTY.toJson(result.solve.record);
        ArtifactIO.replace(directory.resolve("path_flip_solver_result.json"),
                record + System.lineSeparator());
        ArtifactIO.replace(directory.resolve("path_flip_query.smt2"),
                result.solve.smtLib);
        List<JsonObject> replayRows = result.replayTask == null
                ? Collections.<JsonObject>emptyList()
                : Collections.singletonList(result.replayTask);
        ArtifactIO.replaceJsonl(directory.resolve("execution_task_plan.jsonl"),
                replayRows);
        return record;
    }

    private static JsonObject exactTask(List<JsonObject> tasks,
                                        String queryKey) throws IOException {
        JsonObject selected = ArtifactIO.uniqueIndex(tasks, "queryKey")
                .get(queryKey);
        if (selected == null) {
            throw new IOException("Path task not found: " + queryKey);
        }
        return selected;
    }

    static final class Arguments {
        private final Path worklist;
        private final Path executionTasks;
        private final String queryKey;
        private final Path outputDirectory;
        private final Path z3;
        private final long solverTimeoutMillis;

        private Arguments(Path worklist, Path executionTasks, String queryKey,
                          Path outputDirectory, Path z3,
                          long solverTimeoutMillis) {
            this.worklist = worklist;
            this.executionTasks = executionTasks;
            this.queryKey = queryKey;
            this.outputDirectory = outputDirectory;
            this.z3 = z3;
            this.solverTimeoutMillis = solverTimeoutMillis;
        }

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String option = argv[index];
                if (!option.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --name value, got " + option);
                }
                values.put(option.substring(2), argv[++index]);
            }
            String queryKey = requiredValue(values, "query-key");
            if (!ConcolicConstraintSolver.canonicalQueryKey(queryKey)) {
                throw new IllegalArgumentException(
                        "--query-key must be lowercase SHA-256");
            }
            return new Arguments(required(values, "worklist"),
                    required(values, "task-plan"), queryKey,
                    required(values, "output-dir"),
                    Paths.get(firstNonBlank(values.get("z3"), "z3")),
                    longValue(values, "solver-timeout-ms", 20_000L));
        }

        private static Path required(Map<String, String> values,
                                     String name) {
            return Paths.get(requiredValue(values, name));
        }

        private static String requiredValue(Map<String, String> values,
                                            String name) {
            String value = values.get(name);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return value;
        }

        private static long longValue(Map<String, String> values, String name,
                                      long fallback) {
            String value = values.get(name);
            return value == null || value.trim().isEmpty()
                    ? fallback : Long.parseLong(value);
        }
    }

    static final class Result {
        final ConcolicConstraintSolver.Result solve;
        final JsonObject replayTask;

        private Result(ConcolicConstraintSolver.Result solve,
                       JsonObject replayTask) {
            this.solve = solve;
            this.replayTask = replayTask;
        }
    }
}
