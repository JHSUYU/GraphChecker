package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** Runs a concrete unit test once per selected concolic activation. */
public final class ConcolicReplayRunner {
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();

    private ConcolicReplayRunner() {
    }

    public static void main(String[] args) throws Exception {
        Arguments parsed = Arguments.parse(args);
        ReplayResult result = replay(parsed);
        System.out.println(GSON.toJson(result.toJson()));
        if (result.failed > 0) {
            System.exit(1);
        }
    }

    public static ReplayResult replay(Arguments arguments)
            throws IOException, InterruptedException {
        if (arguments.command.isEmpty()) {
            throw new IllegalArgumentException(
                    "Missing replay command after --, for example -- ./mvnw -Dtest=... test");
        }
        if (!Files.isRegularFile(arguments.activationPlan)) {
            throw new IOException("Activation plan not found: "
                    + arguments.activationPlan);
        }
        if (!Files.isDirectory(arguments.javaHome)) {
            throw new IOException("Concolic JAVA_HOME not found: "
                    + arguments.javaHome);
        }

        List<Activation> activations = readActivations(arguments.activationPlan,
                arguments.selectedActivation);
        Path resultParent = arguments.results.toAbsolutePath().getParent();
        if (resultParent != null) {
            Files.createDirectories(resultParent);
        }
        if (!arguments.appendResults) {
            Files.deleteIfExists(arguments.results);
            Files.deleteIfExists(arguments.manifest);
        }

        ReplayResult result = new ReplayResult(activations.size());
        for (Activation activation : activations) {
            if (!activation.replayable) {
                result.skipped++;
                appendManifest(arguments.manifest, activation, -1,
                        "SKIPPED_NOT_REPLAYABLE", 0L, arguments.command);
                continue;
            }
            if (!activation.schedulerReady) {
                result.skipped++;
                appendManifest(arguments.manifest, activation, -1,
                        "SKIPPED_NOT_SCHEDULER_READY", 0L, arguments.command);
                continue;
            }
            if (arguments.dryRun) {
                result.skipped++;
                appendManifest(arguments.manifest, activation, -1,
                        "DRY_RUN", 0L, arguments.command);
                continue;
            }

            ProcessBuilder builder = new ProcessBuilder(arguments.command);
            builder.directory(arguments.workDirectory.toFile());
            builder.inheritIO();
            Map<String, String> environment = builder.environment();
            environment.put("JAVA_HOME", arguments.javaHome.toAbsolutePath().toString());
            environment.put("PATH", arguments.javaHome.resolve("bin").toAbsolutePath()
                    + System.getProperty("path.separator")
                    + firstNonBlank(environment.get("PATH"), ""));
            String options = firstNonBlank(environment.get("JAVA_TOOL_OPTIONS"), "");
            options = appendOption(options, "causynth.concolic.activation.plan",
                    arguments.activationPlan.toAbsolutePath().toString());
            options = appendOption(options, "causynth.concolic.activation.id",
                    activation.activationId);
            options = appendOption(options, "causynth.concolic.results",
                    arguments.results.toAbsolutePath().toString());
            options = appendOption(options, "causynth.trace.test", activation.test);
            environment.put("JAVA_TOOL_OPTIONS", options);

            long start = System.nanoTime();
            int exit = builder.start().waitFor();
            long duration = System.nanoTime() - start;
            if (exit == 0) {
                result.succeeded++;
            } else {
                result.failed++;
            }
            appendManifest(arguments.manifest, activation, exit,
                    exit == 0 ? "SUCCEEDED" : "FAILED", duration,
                    arguments.command);
            if (exit != 0 && arguments.failFast) {
                break;
            }
        }
        return result;
    }

    private static List<Activation> readActivations(Path path, String selected)
            throws IOException {
        List<Activation> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonElement parsed = JsonParser.parseString(line);
                if (!parsed.isJsonObject()) {
                    continue;
                }
                Activation activation = new Activation(parsed.getAsJsonObject());
                if (selected.isEmpty() || selected.equals(activation.activationId)) {
                    result.add(activation);
                }
            }
        }
        return result;
    }

    private static void appendManifest(Path manifest, Activation activation,
                                       int exitCode, String status,
                                       long durationNanos,
                                       List<String> command) throws IOException {
        JsonObject row = new JsonObject();
        row.addProperty("activationId", activation.activationId);
        row.addProperty("regionId", activation.regionId);
        row.addProperty("test", activation.test);
        row.addProperty("status", status);
        row.addProperty("exitCode", exitCode);
        row.addProperty("durationNanos", durationNanos);
        row.addProperty("timestamp", Instant.now().toString());
        row.add("command", GSON.toJsonTree(command));
        Path parent = manifest.toAbsolutePath().getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        Files.write(manifest,
                (GSON.toJson(row) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.APPEND);
    }

    private static String appendOption(String existing, String key, String value) {
        String escaped = value == null ? "" : value
                .replace("\\", "\\\\").replace("\"", "\\\"");
        return (existing.isEmpty() ? "" : existing + " ")
                + "-D" + key + "=\"" + escaped + "\"";
    }

    private static String string(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value == null || value.isJsonNull() ? "" : value.getAsString();
    }

    private static boolean strictTrue(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                && value.getAsBoolean();
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }

    private static final class Activation {
        private final String activationId;
        private final String regionId;
        private final String test;
        private final boolean replayable;
        private final boolean schedulerReady;

        private Activation(JsonObject row) {
            this.activationId = string(row, "activationId");
            this.regionId = string(row, "regionId");
            this.test = string(row, "test");
            this.replayable = strictTrue(row, "replayable");
            this.schedulerReady = strictTrue(row, "schedulerReady");
        }
    }

    public static final class ReplayResult {
        public final int selected;
        public int succeeded;
        public int failed;
        public int skipped;

        private ReplayResult(int selected) {
            this.selected = selected;
        }

        private JsonObject toJson() {
            JsonObject value = new JsonObject();
            value.addProperty("selected", selected);
            value.addProperty("succeeded", succeeded);
            value.addProperty("failed", failed);
            value.addProperty("skipped", skipped);
            return value;
        }
    }

    public static final class Arguments {
        public final Path activationPlan;
        public final Path javaHome;
        public final Path results;
        public final Path manifest;
        public final Path workDirectory;
        public final String selectedActivation;
        public final boolean appendResults;
        public final boolean failFast;
        public final boolean dryRun;
        public final List<String> command;

        private Arguments(Path activationPlan, Path javaHome, Path results,
                          Path manifest, Path workDirectory,
                          String selectedActivation, boolean appendResults,
                          boolean failFast, boolean dryRun,
                          List<String> command) {
            this.activationPlan = activationPlan;
            this.javaHome = javaHome;
            this.results = results;
            this.manifest = manifest;
            this.workDirectory = workDirectory;
            this.selectedActivation = selectedActivation;
            this.appendResults = appendResults;
            this.failFast = failFast;
            this.dryRun = dryRun;
            this.command = command;
        }

        public static Arguments parse(String[] args) {
            Map<String, String> options = new LinkedHashMap<>();
            List<String> command = new ArrayList<>();
            boolean commandMode = false;
            for (int index = 0; args != null && index < args.length; index++) {
                String value = args[index];
                if (commandMode) {
                    command.add(value);
                    continue;
                }
                if ("--".equals(value)) {
                    commandMode = true;
                    continue;
                }
                if (value.startsWith("--")) {
                    String key = value.substring(2);
                    String next = index + 1 < args.length ? args[index + 1] : "";
                    if (!next.startsWith("--")) {
                        options.put(key, next);
                        index++;
                    } else {
                        options.put(key, "true");
                    }
                }
            }
            Path activation = path(options, "activation-plan", null);
            Path javaHome = path(options, "java-home", null);
            if (activation == null || javaHome == null) {
                throw new IllegalArgumentException(
                        "Both --activation-plan and --java-home are required");
            }
            Path results = path(options, "results",
                    sibling(activation, "concolic_region_results.jsonl"));
            Path manifest = path(options, "manifest",
                    sibling(activation, "concolic_replay_manifest.jsonl"));
            Path workdir = path(options, "workdir", Paths.get("."));
            return new Arguments(activation, javaHome, results, manifest, workdir,
                    firstNonBlank(options.get("activation-id"), ""),
                    Boolean.parseBoolean(options.get("append")),
                    Boolean.parseBoolean(firstNonBlank(options.get("fail-fast"),
                            "true")),
                    Boolean.parseBoolean(options.get("dry-run")), command);
        }

        private static Path path(Map<String, String> options, String key,
                                 Path fallback) {
            String value = options.get(key);
            return value == null || value.trim().isEmpty()
                    ? fallback : Paths.get(value);
        }

        private static Path sibling(Path path, String file) {
            Path parent = path.toAbsolutePath().getParent();
            return (parent == null ? Paths.get(".") : parent).resolve(file);
        }
    }
}
