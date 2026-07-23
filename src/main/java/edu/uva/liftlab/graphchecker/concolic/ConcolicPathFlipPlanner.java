package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Plans and solves one already-captured upstream region path flip without
 * rerunning static instrumentation.
 *
 * <p>The emitted activation plan is consumed directly by the existing
 * {@code replay-concolic} command.  It contains only solver model input
 * assignments and an observation-only target branch; it never contains a
 * forced branch or a replayed method result.</p>
 */
public final class ConcolicPathFlipPlanner {
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicPathFlipPlanner() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = plan(arguments);
        writeOutputs(arguments.outputDirectory, result);
        System.out.println(PRETTY.toJson(result.manifest));
        if (!bool(result.manifest, "complete", false)) {
            System.exit(2);
        }
    }

    static Result plan(Arguments arguments) throws Exception {
        List<JsonObject> allActivations = readJsonl(arguments.activations);
        List<JsonObject> allSummaries = readJsonl(arguments.summaries);
        List<JsonObject> records = arguments.records == null
                ? Collections.<JsonObject>emptyList()
                : readJsonl(arguments.records);

        List<JsonObject> activations = filterActivations(allActivations,
                arguments);
        Map<String, JsonObject> activationById = uniqueIndex(activations,
                "activationId");
        List<JsonObject> summaries = filterSummaries(allSummaries,
                activationById, arguments);
        RegionPathWorklist.Result worklist = RegionPathWorklist.plan(
                summaries, activations, records, arguments.pathBounds);

        List<JsonObject> candidates = new ArrayList<>();
        for (JsonObject task : worklist.tasks) {
            if (!matchesTask(task, arguments)) continue;
            candidates.add(task.deepCopy());
        }

        JsonObject manifest = baseManifest(arguments, worklist, activations,
                summaries, candidates);
        manifest.add("inputSummaries", sourceArtifact(arguments.summaries));
        manifest.add("inputActivations", sourceArtifact(
                arguments.activations));
        if (arguments.records != null) {
            manifest.add("inputExplorationRecords", sourceArtifact(
                    arguments.records));
        }
        if (candidates.size() != 1) {
            manifest.addProperty("status", candidates.isEmpty()
                    ? "NO_MATCHING_PATH_FLIP" : "AMBIGUOUS_PATH_FLIP");
            manifest.addProperty("complete", false);
            manifest.addProperty("reason",
                    "EXACTLY_ONE_PATH_FLIP_MUST_MATCH_SELECTION");
            return new Result(worklist.tasks, worklist.manifest, candidates,
                    null, null, null, manifest);
        }

        JsonObject task = candidates.get(0);
        String sourceId = string(task, "sourceActivationId");
        JsonObject source = activationById.get(sourceId);
        if (source == null) {
            manifest.addProperty("status", "SOURCE_ACTIVATION_NOT_FOUND");
            manifest.addProperty("complete", false);
            manifest.addProperty("sourceActivationId", sourceId);
            return new Result(worklist.tasks, worklist.manifest, candidates,
                    task, null, null, manifest);
        }

        ConcolicConstraintSolver.Result solve =
                ConcolicConstraintSolver.solve(task, source, arguments.z3,
                        arguments.solverTimeoutMillis);
        manifest.addProperty("solverStatus", string(solve.record,
                "status"));
        manifest.addProperty("queryKey", string(task, "queryKey"));
        manifest.addProperty("sourceActivationId", sourceId);
        manifest.addProperty("sourceSummaryId", string(task,
                "sourceSummaryId"));
        manifest.addProperty("regionId", string(task, "regionId"));
        BranchReplayContract replayContract = replayContract(task);
        manifest.addProperty("flipSite",
                replayContract.source().siteId());
        manifest.addProperty("flipOccurrence",
                replayContract.source().occurrence());
        manifest.addProperty("desiredOutcome",
                replayContract.requiredTakenOutcome());
        if (!"SAT_MODEL_READY".equals(string(solve.record, "status"))) {
            manifest.addProperty("status", "PATH_FLIP_NOT_REPLAYABLE");
            manifest.addProperty("complete", false);
            manifest.addProperty("reason", firstNonBlank(string(
                    solve.record, "reason"), string(solve.record,
                    "status")));
            return new Result(worklist.tasks, worklist.manifest, candidates,
                    task, solve, null, manifest);
        }

        JsonObject replay = ReplayActivationFactory.create(task,
                source, solve.modelAssignments);
        manifest.addProperty("status", "PATH_FLIP_REPLAY_READY");
        manifest.addProperty("complete", true);
        manifest.addProperty("replayActivationId", string(replay,
                "activationId"));
        manifest.addProperty("replayScheduleId", string(replay,
                "scheduleId"));
        manifest.addProperty("modelAssignmentCount",
                solve.modelAssignments.size());
        return new Result(worklist.tasks, worklist.manifest, candidates,
                task, solve, replay, manifest);
    }

    static void writeOutputs(Path directory, Result result)
            throws IOException {
        Files.createDirectories(directory);
        writeJsonl(directory.resolve("region_path_worklist.jsonl"),
                result.worklistTasks);
        writeJson(directory.resolve("region_path_manifest.json"),
                result.worklistManifest);
        writeJsonl(directory.resolve("selected_path_flip.jsonl"),
                result.selectedTasks);
        writeJson(directory.resolve("path_flip_solver_result.json"),
                result.solve == null ? new JsonObject()
                        : result.solve.record);
        writeText(directory.resolve("path_flip_query.smt2"),
                result.solve == null ? "" : result.solve.smtLib);
        if (result.replayActivation != null) {
            writeJsonl(directory.resolve("activation_plan.jsonl"),
                    Collections.singletonList(result.replayActivation));
            writeJson(directory.resolve("replay_validation_plan.json"),
                    ReplayActivationFactory.validationPlan(
                            result.selectedTask,
                            result.solve.modelAssignments));
        } else {
            // Always replace these fixed-name products.  A failed re-plan in
            // a reused output directory must not leave an older executable
            // activation plan behind.
            writeJsonl(directory.resolve("activation_plan.jsonl"),
                    Collections.<JsonObject>emptyList());
            JsonObject unavailable = new JsonObject();
            unavailable.addProperty("ready", false);
            unavailable.addProperty("reason", string(result.manifest,
                    "status"));
            writeJson(directory.resolve("replay_validation_plan.json"),
                    unavailable);
        }

        JsonObject manifest = result.manifest.deepCopy();
        addArtifact(manifest, directory, "regionPathWorklist",
                "region_path_worklist.jsonl");
        addArtifact(manifest, directory, "regionPathManifest",
                "region_path_manifest.json");
        addArtifact(manifest, directory, "selectedPathFlip",
                "selected_path_flip.jsonl");
        addArtifact(manifest, directory, "solverResult",
                "path_flip_solver_result.json");
        addArtifact(manifest, directory, "solverQuery",
                "path_flip_query.smt2");
        addArtifact(manifest, directory, "activationPlan",
                "activation_plan.jsonl");
        addArtifact(manifest, directory, "replayValidationPlan",
                "replay_validation_plan.json");
        writeJson(directory.resolve("path_flip_plan_manifest.json"),
                manifest);
        result.manifest = manifest;
    }

    private static JsonObject baseManifest(Arguments arguments,
                                           RegionPathWorklist.Result worklist,
                                           List<JsonObject> activations,
                                           List<JsonObject> summaries,
                                           List<JsonObject> candidates) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "CONCOLIC_SINGLE_PATH_FLIP_PLAN");
        result.addProperty("scope", "ONE_RUNTIME_CAPTURED_UPSTREAM_REGION");
        result.addProperty("activationCandidateCount", activations.size());
        result.addProperty("summaryCandidateCount", summaries.size());
        result.addProperty("worklistTaskCount", worklist.tasks.size());
        result.addProperty("selectedTaskCount", candidates.size());
        result.addProperty("activationIdSelector", arguments.activationId);
        result.addProperty("regionIdSelector", arguments.regionId);
        result.addProperty("flipSiteSelector", arguments.flipSite);
        result.addProperty("flipOccurrenceSelector",
                arguments.flipOccurrence);
        result.addProperty("queryKeySelector", arguments.queryKey);
        result.addProperty("solverTimeoutMillis",
                arguments.solverTimeoutMillis);
        result.addProperty("complete", false);
        return result;
    }

    private static List<JsonObject> filterActivations(
            List<JsonObject> source, Arguments arguments) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject activation : source) {
            if (!arguments.activationId.isEmpty()
                    && !arguments.activationId.equals(string(activation,
                    "activationId"))) continue;
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(string(activation,
                    "regionId"))) continue;
            result.add(activation.deepCopy());
        }
        return result;
    }

    private static List<JsonObject> filterSummaries(List<JsonObject> source,
                                                    Map<String, JsonObject>
                                                            activations,
                                                    Arguments arguments) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject summary : source) {
            String activationId = string(summary, "activationId");
            if (!activations.containsKey(activationId)) continue;
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(string(summary,
                    "regionId"))) continue;
            result.add(summary.deepCopy());
        }
        return result;
    }

    private static boolean matchesTask(JsonObject task,
                                       Arguments arguments) {
        BranchReplayContract contract = replayContract(task);
        String site = contract.source().siteId();
        int occurrence = contract.source().occurrence();
        return (arguments.queryKey.isEmpty()
                || arguments.queryKey.equals(string(task, "queryKey")))
                && (arguments.flipSite.isEmpty()
                || arguments.flipSite.equals(site))
                && (arguments.flipOccurrence < 1
                || arguments.flipOccurrence == occurrence);
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        JsonElement encoded = task == null ? null
                : task.get("replayContract");
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "canonical path task requires replayContract");
        }
        return BranchReplayContract.fromJson(encoded.getAsJsonObject());
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
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int number = 0;
            while ((line = reader.readLine()) != null) {
                number++;
                if (line.trim().isEmpty()) continue;
                JsonElement parsed;
                try {
                    parsed = JsonParser.parseString(line);
                } catch (RuntimeException exception) {
                    throw new IOException("Malformed JSONL " + path + ":"
                            + number, exception);
                }
                if (!parsed.isJsonObject()) {
                    throw new IOException("Non-object JSONL row " + path
                            + ":" + number);
                }
                result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder content = new StringBuilder();
        for (JsonObject row : rows) {
            content.append(JSON.toJson(row)).append(System.lineSeparator());
        }
        writeText(path, content.toString());
    }

    private static void writeJson(Path path, JsonObject value)
            throws IOException {
        writeText(path, PRETTY.toJson(value) + System.lineSeparator());
    }

    private static void writeText(Path path, String value)
            throws IOException {
        Files.createDirectories(path.toAbsolutePath().normalize().getParent());
        Path temporary = path.resolveSibling(path.getFileName() + ".tmp."
                + java.util.UUID.randomUUID());
        Files.write(temporary, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
        try {
            Files.move(temporary, path, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } catch (AtomicMoveNotSupportedException exception) {
            Files.move(temporary, path, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static void addArtifact(JsonObject manifest, Path directory,
                                    String name, String file)
            throws IOException {
        Path path = directory.resolve(file);
        JsonObject artifact = new JsonObject();
        artifact.addProperty("file", file);
        artifact.addProperty("sha256", sha256(path));
        artifact.addProperty("sizeBytes", Files.size(path));
        manifest.add(name, artifact);
    }

    private static JsonObject sourceArtifact(Path path) throws IOException {
        JsonObject artifact = new JsonObject();
        artifact.addProperty("file", path.toAbsolutePath().normalize()
                .toString());
        artifact.addProperty("sha256", sha256(path));
        artifact.addProperty("sizeBytes", Files.size(path));
        return artifact;
    }

    private static String sha256(Path path) throws IOException {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] buffer = new byte[8192];
            try (java.io.InputStream input = Files.newInputStream(path)) {
                int read;
                while ((read = input.read(buffer)) >= 0) {
                    if (read > 0) digest.update(buffer, 0, read);
                }
            }
            StringBuilder result = new StringBuilder();
            for (byte current : digest.digest()) {
                result.append(String.format("%02x", current & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
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

    private static boolean bool(JsonObject object, String field,
                                boolean fallback) {
        try {
            JsonElement value = object == null ? null : object.get(field);
            return value != null && value.isJsonPrimitive()
                    ? value.getAsBoolean() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String first, String second) {
        return first != null && !first.trim().isEmpty() ? first
                : second == null ? "" : second;
    }

    static final class Arguments {
        private final Path summaries;
        private final Path activations;
        private final Path records;
        private final Path outputDirectory;
        private final Path z3;
        private final long solverTimeoutMillis;
        private final RegionPathWorklist.Bounds pathBounds;
        private final String activationId;
        private final String regionId;
        private final String flipSite;
        private final int flipOccurrence;
        private final String queryKey;

        private Arguments(Path summaries, Path activations, Path records,
                          Path outputDirectory, Path z3,
                          long solverTimeoutMillis,
                          RegionPathWorklist.Bounds pathBounds,
                          String activationId, String regionId,
                          String flipSite, int flipOccurrence,
                          String queryKey) {
            this.summaries = summaries;
            this.activations = activations;
            this.records = records;
            this.outputDirectory = outputDirectory;
            this.z3 = z3;
            this.solverTimeoutMillis = solverTimeoutMillis;
            this.pathBounds = pathBounds;
            this.activationId = activationId;
            this.regionId = regionId;
            this.flipSite = flipSite;
            this.flipOccurrence = flipOccurrence;
            this.queryKey = queryKey;
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
            Path summaries = required(values, "summaries");
            Path activations = required(values, "activations");
            Path output = required(values, "output-dir");
            Path records = optionalPath(values.get("records"));
            Path z3 = Paths.get(firstNonBlank(values.get("z3"), "z3"));
            long timeout = longValue(values, "solver-timeout-ms", 20_000L);
            RegionPathWorklist.Bounds defaults =
                    RegionPathWorklist.Bounds.defaults();
            RegionPathWorklist.Bounds bounds =
                    new RegionPathWorklist.Bounds(
                            intValue(values, "max-paths-per-region",
                                    defaults.maxPathsPerRegion),
                            intValue(values, "max-flips-per-path",
                                    defaults.maxFlipsPerPath),
                            intValue(values, "max-tasks",
                                    defaults.maxTasks),
                            longValue(values, "max-wall-clock-ms",
                                    defaults.maxWallClockMillis));
            return new Arguments(summaries, activations, records, output, z3,
                    timeout, bounds, value(values, "activation-id"),
                    value(values, "region-id"), value(values, "flip-site"),
                    intValue(values, "flip-occurrence", -1),
                    value(values, "query-key"));
        }

        private static Path required(Map<String, String> values,
                                     String name) {
            String value = values.get(name);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return Paths.get(value);
        }

        private static Path optionalPath(String value) {
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }

        private static String value(Map<String, String> values,
                                    String name) {
            String result = values.get(name);
            return result == null ? "" : result;
        }

        private static int intValue(Map<String, String> values, String name,
                                    int fallback) {
            String value = values.get(name);
            return value == null || value.trim().isEmpty()
                    ? fallback : Integer.parseInt(value);
        }

        private static long longValue(Map<String, String> values,
                                      String name, long fallback) {
            String value = values.get(name);
            return value == null || value.trim().isEmpty()
                    ? fallback : Long.parseLong(value);
        }
    }

    static final class Result {
        final List<JsonObject> worklistTasks;
        final JsonObject worklistManifest;
        final List<JsonObject> selectedTasks;
        final JsonObject selectedTask;
        final ConcolicConstraintSolver.Result solve;
        final JsonObject replayActivation;
        JsonObject manifest;

        private Result(List<JsonObject> worklistTasks,
                       JsonObject worklistManifest,
                       List<JsonObject> selectedTasks,
                       JsonObject selectedTask,
                       ConcolicConstraintSolver.Result solve,
                       JsonObject replayActivation,
                       JsonObject manifest) {
            this.worklistTasks = new ArrayList<>(worklistTasks);
            this.worklistManifest = worklistManifest.deepCopy();
            this.selectedTasks = new ArrayList<>(selectedTasks);
            this.selectedTask = selectedTask == null
                    ? null : selectedTask.deepCopy();
            this.solve = solve;
            this.replayActivation = replayActivation == null
                    ? null : replayActivation.deepCopy();
            this.manifest = manifest;
        }
    }
}
