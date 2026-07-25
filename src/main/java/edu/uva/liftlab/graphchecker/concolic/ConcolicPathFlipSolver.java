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
        writeOutputs(arguments.outputDirectory, result);
        System.out.println(PRETTY.toJson(result.solve.record));
        String status = string(result.solve.record, "status");
        if (!"SAT_MODEL_READY".equals(status) && !"UNSAT".equals(status)) {
            System.exit(2);
        }
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
                solved.modelAssignments) : null;
        return new Result(task, solved, replay);
    }

    static void writeOutputs(Path directory, Result result)
            throws IOException {
        ArtifactIO.replace(directory.resolve("path_flip_solver_result.json"),
                PRETTY.toJson(result.solve.record) + System.lineSeparator());
        ArtifactIO.replace(directory.resolve("path_flip_query.smt2"),
                result.solve.smtLib);
        List<JsonObject> replayRows = result.replayTask == null
                ? Collections.<JsonObject>emptyList()
                : Collections.singletonList(result.replayTask);
        ArtifactIO.replaceJsonl(directory.resolve("execution_task_plan.jsonl"),
                replayRows);
        JsonObject validation = result.replayTask == null
                ? unavailableValidation(result.solve.record)
                : PathReplayTaskFactory.validationPlan(result.task,
                result.solve.modelAssignments);
        ArtifactIO.replace(directory.resolve("replay_validation_plan.json"),
                PRETTY.toJson(validation) + System.lineSeparator());
    }

    private static JsonObject unavailableValidation(JsonObject solverRecord) {
        JsonObject result = new JsonObject();
        result.addProperty("ready", false);
        result.addProperty("reason", string(solverRecord, "status"));
        result.addProperty("queryKey", string(solverRecord, "queryKey"));
        return result;
    }

    private static JsonObject exactTask(List<JsonObject> tasks,
                                        String queryKey) throws IOException {
        JsonObject selected = null;
        int count = 0;
        for (JsonObject task : tasks) {
            if (!queryKey.equals(string(task, "queryKey"))) continue;
            selected = task;
            count++;
        }
        if (count != 1) {
            throw new IOException("Expected exactly one path task for "
                    + queryKey + ", found " + count);
        }
        return selected.deepCopy();
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
            if (!queryKey.matches("[0-9a-f]{64}")) {
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
        final JsonObject task;
        final ConcolicConstraintSolver.Result solve;
        final JsonObject replayTask;

        private Result(JsonObject task,
                       ConcolicConstraintSolver.Result solve,
                       JsonObject replayTask) {
            this.task = task.deepCopy();
            this.solve = solve;
            this.replayTask = replayTask == null
                    ? null : replayTask.deepCopy();
        }
    }

    private static String firstNonBlank(String first, String second) {
        return first != null && !first.trim().isEmpty() ? first : second;
    }
}
