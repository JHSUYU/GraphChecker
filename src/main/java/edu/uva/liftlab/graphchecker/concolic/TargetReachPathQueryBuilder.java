package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Builds one solver query from all closed concolic paths which reached the
 * exact annotated exception type in the consumer target region.
 */
public final class TargetReachPathQueryBuilder {
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private TargetReachPathQueryBuilder() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject result = build(arguments);
        ArtifactIO.replace(arguments.output,
                JSON.toJson(result) + System.lineSeparator());
        System.out.println(JSON.toJson(result));
    }

    static JsonObject build(Arguments arguments) throws IOException {
        JsonObject manifest = ArtifactIO.readObject(arguments.pathManifest);
        if (!"CLOSED".equals(string(manifest, "state"))
                || integer(manifest, "pendingTaskCount", -1) != 0
                || array(manifest, "gaps").size() != 0
                || !"TARGET_BRANCH".equals(string(manifest,
                "captureGoal"))) {
            throw new IOException(
                    "target path worklist is not completely closed");
        }

        List<JsonObject> seeds = ArtifactIO.readJsonl(arguments.seedQuery,
                "Malformed target seed query %1$s:%2$d",
                "Non-object target seed query %1$s:%2$d");
        if (seeds.size() != 1
                || !"TARGET_BRANCH_SOLVER_QUERY".equals(
                string(seeds.get(0), "kind"))
                || !bool(seeds.get(0), "readyForSolver", false)) {
            throw new IOException(
                    "exactly one solver-ready target seed query is required");
        }
        JsonObject seed = seeds.get(0);
        String region = string(seed, "regionId");
        String instance = string(seed, "regionInstanceId");
        if (!region.equals(string(manifest, "regionId"))
                || region.isEmpty() || instance.isEmpty()) {
            throw new IOException(
                    "target seed and closed path scope do not match");
        }

        Map<String, JsonObject> pathsByKey = new LinkedHashMap<>();
        List<JsonObject> summaries = ArtifactIO.readJsonl(arguments.summaries,
                "Malformed target summary %1$s:%2$d",
                "Non-object target summary %1$s:%2$d");
        for (JsonObject summary : summaries) {
            if (!region.equals(string(summary, "regionId"))
                    || !instance.equals(string(summary,
                    "regionInstanceId"))
                    || !RegionCaptureGoal.from(summary).isTargetBranch()
                    || !bool(summary, "relationallyComplete", false)) {
                continue;
            }
            // Parsing is the schema/admission boundary for branch-owned
            // predicates. The importer already normalized the PC; this check
            // prevents a malformed mapping row from entering the path set.
            List<SummaryBranchMapping> mappings;
            try {
                mappings = SummaryBranchMapping.fromSummary(summary);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed target branch mapping: "
                        + malformed.getMessage(), malformed);
            }
            if (bool(summary, "normalExit", true)
                    || !arguments.exceptionType.equals(string(summary,
                    "exceptionType"))) {
                continue;
            }

            JsonObject path = new JsonObject();
            String pathKey = RegionPathWorklist.stablePathKey(summary);
            path.addProperty("pathKey", pathKey);
            path.addProperty("summaryId", string(summary, "summaryId"));
            path.add("constraints",
                    array(summary, "pathCondition").deepCopy());
            path.add("engineArrayInputBindings",
                    array(summary, "engineArrayInputBindings").deepCopy());
            JsonArray placeholderBindings = array(summary,
                    "vmIntrinsicPlaceholderBindings");
            JsonArray placeholderRequirements = array(summary,
                    "unforcedEnvironmentValidationRequirements");
            if (placeholderBindings.size() > 0
                    || placeholderRequirements.size() > 0) {
                path.add("vmIntrinsicPlaceholderBindings",
                        placeholderBindings.deepCopy());
                path.add("unforcedEnvironmentValidationRequirements",
                        placeholderRequirements.deepCopy());
            }
            requireUniqueWitnessPositions(mappings);
            JsonObject previous = pathsByKey.put(pathKey, path);
            if (previous != null && !previous.equals(path)) {
                throw new IOException(
                        "conflicting reached target path: " + pathKey);
            }
        }

        List<JsonObject> paths = new ArrayList<>(pathsByKey.values());
        paths.sort(Comparator.comparing(value -> string(value, "pathKey")));
        JsonArray encodedPaths = new JsonArray();
        for (JsonObject path : paths) encodedPaths.add(path);

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        result.addProperty("activationId", string(seed, "activationId"));
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", instance);
        result.addProperty("exceptionType", arguments.exceptionType);
        result.addProperty("pathClosureState", "CLOSED");
        result.addProperty("observedPathCount",
                integer(manifest, "observedPathCount", 0));
        result.addProperty("reachedPathCount", paths.size());
        result.add("paths", encodedPaths);
        result.add("seedReplayContract",
                object(seed, "replayContract").deepCopy());
        result.add("symbolicContext",
                object(seed, "symbolicContext").deepCopy());
        result.addProperty("readyForSolver", true);
        result.addProperty("constraintAuthority",
                "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1");
        return result;
    }

    private static void requireUniqueWitnessPositions(
            List<SummaryBranchMapping> mappings) {
        Set<Integer> positions = new LinkedHashSet<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (!mapping.isWitnessed()) continue;
            if (!positions.add(mapping.summaryPcIndex())) {
                throw new IllegalArgumentException(
                        "duplicate witnessed target PC position");
            }
        }
    }

    static final class Arguments {
        private final Path summaries;
        private final Path pathManifest;
        private final Path seedQuery;
        private final String exceptionType;
        private final Path output;

        private Arguments(Path summaries, Path pathManifest,
                          Path seedQuery, String exceptionType,
                          Path output) {
            this.summaries = summaries;
            this.pathManifest = pathManifest;
            this.seedQuery = seedQuery;
            this.exceptionType = exceptionType;
            this.output = output;
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
            return new Arguments(requiredPath(values, "summaries"),
                    requiredPath(values, "path-manifest"),
                    requiredPath(values, "seed-query"),
                    required(values, "exception-type"),
                    requiredPath(values, "output"));
        }

        private static Path requiredPath(Map<String, String> values,
                                         String name) {
            return Paths.get(required(values, name));
        }

        private static String required(Map<String, String> values,
                                       String name) {
            String value = values.get(name);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return value.trim();
        }
    }
}
