package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Solves exactly one canonical path-flip task and emits its singleton replay
 * activation. Each invocation is intentionally process-local so independent
 * tasks can be run by separate workers.
 */
public final class ConcolicPathFlipSolver {
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();
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
        JsonObject task = exactTask(readJsonl(arguments.worklist),
                arguments.queryKey);
        Map<String, JsonObject> activations = uniqueIndex(
                readJsonl(arguments.activations), "activationId");
        String sourceId = string(task, "sourceActivationId");
        JsonObject source = activations.get(sourceId);
        if (source == null) {
            throw new IOException("Source activation not found: " + sourceId);
        }

        ConcolicConstraintSolver.Result solved =
                ConcolicConstraintSolver.solve(task, source, arguments.z3,
                        arguments.solverTimeoutMillis);
        JsonObject replay = "SAT_MODEL_READY".equals(string(solved.record,
                "status"))
                ? ReplayActivationFactory.create(task, source,
                solved.modelAssignments) : null;
        return new Result(task, solved, replay);
    }

    static void writeOutputs(Path directory, Result result)
            throws IOException {
        ArtifactIO.replace(directory.resolve("path_flip_solver_result.json"),
                PRETTY.toJson(result.solve.record) + System.lineSeparator());
        ArtifactIO.replace(directory.resolve("path_flip_query.smt2"),
                result.solve.smtLib);
        List<JsonObject> replayRows = result.replayActivation == null
                ? Collections.<JsonObject>emptyList()
                : Collections.singletonList(result.replayActivation);
        writeJsonl(directory.resolve("activation_plan.jsonl"), replayRows);
        JsonObject validation = result.replayActivation == null
                ? unavailableValidation(result.solve.record)
                : ReplayActivationFactory.validationPlan(result.task,
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

    private static Map<String, JsonObject> uniqueIndex(
            List<JsonObject> rows, String field) throws IOException {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            String key = string(row, field);
            if (key.isEmpty()) continue;
            JsonObject previous = result.put(key, row);
            if (previous != null && !previous.equals(row)) {
                throw new IOException("Conflicting duplicate " + field
                        + ": " + key);
            }
        }
        return result;
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        return ArtifactIO.readJsonl(path, "Malformed JSONL %1$s:%2$d",
                "Non-object JSONL row %1$s:%2$d");
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder content = new StringBuilder();
        for (JsonObject row : rows) {
            content.append(JSON.toJson(row)).append(System.lineSeparator());
        }
        ArtifactIO.replace(path, content.toString());
    }

    private static String string(JsonObject object, String field) {
        if (object == null) return "";
        JsonElement value = object.get(field);
        try {
            return value != null && value.isJsonPrimitive()
                    ? value.getAsString() : "";
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    static final class Arguments {
        private final Path worklist;
        private final Path activations;
        private final String queryKey;
        private final Path outputDirectory;
        private final Path z3;
        private final long solverTimeoutMillis;

        private Arguments(Path worklist, Path activations, String queryKey,
                          Path outputDirectory, Path z3,
                          long solverTimeoutMillis) {
            this.worklist = worklist;
            this.activations = activations;
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
                    required(values, "activations"), queryKey,
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
        final JsonObject replayActivation;

        private Result(JsonObject task,
                       ConcolicConstraintSolver.Result solve,
                       JsonObject replayActivation) {
            this.task = task.deepCopy();
            this.solve = solve;
            this.replayActivation = replayActivation == null
                    ? null : replayActivation.deepCopy();
        }
    }

    private static String firstNonBlank(String first, String second) {
        return first != null && !first.trim().isEmpty() ? first : second;
    }
}
