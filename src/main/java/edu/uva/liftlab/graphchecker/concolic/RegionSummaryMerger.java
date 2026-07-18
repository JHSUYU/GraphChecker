package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
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
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Merges validated executions of the same requested region output into one
 * guarded, project-independent relation IR.
 */
public final class RegionSummaryMerger {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private RegionSummaryMerger() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        List<JsonObject> summaries = new ArrayList<>();
        for (Path input : arguments.inputs) summaries.addAll(readJsonl(input));
        JsonObject pathManifest = readJson(arguments.pathManifest);
        Result result = merge(summaries, pathManifest);
        writeJsonl(arguments.output, result.summaries);
        Files.write(arguments.manifest,
                (GSON.toJson(result.manifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
        System.out.println(GSON.toJson(result.manifest));
    }

    public static Result merge(List<JsonObject> summaries,
                               JsonObject pathManifest) {
        Map<String, List<JsonObject>> groups = new LinkedHashMap<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        for (JsonObject summary : safe(summaries)) {
            if (!bool(summary, "valid", true)
                    || !RegionCaptureGoal.from(summary).isOutputClosure()) {
                continue;
            }
            String region = string(summary, "regionId");
            JsonObject output = object(summary, "requestedOutput");
            if (region.isEmpty() || output.size() == 0) {
                diagnostics.add(gap(region, "MISSING_REQUESTED_OUTPUT"));
                continue;
            }
            String key = region + "\n" + canonical(output);
            List<JsonObject> values = groups.get(key);
            if (values == null) {
                values = new ArrayList<>();
                groups.put(key, values);
            }
            values.add(summary);
        }

        List<JsonObject> merged = new ArrayList<>();
        for (List<JsonObject> values : groups.values()) {
            merged.add(mergeGroup(values, pathManifest, diagnostics));
        }
        Collections.sort(merged, Comparator.comparing(value ->
                string(value, "regionId") + "\n"
                        + canonical(value.get("requestedOutput"))));
        if (merged.isEmpty()) {
            diagnostics.add(gap("", "NO_VALID_OUTPUT_CLOSURE_RELATIONS"));
        }

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "REGION_RELATION_MERGE_MANIFEST");
        manifest.addProperty("inputSummaryCount", safe(summaries).size());
        manifest.addProperty("mergedRelationCount", merged.size());
        int caseCount = 0;
        boolean complete = bool(pathManifest, "complete", false)
                && diagnostics.isEmpty()
                && !merged.isEmpty();
        for (JsonObject summary : merged) {
            JsonObject relation = object(summary, "regionRelation");
            caseCount += integer(relation, "caseCount", 0);
            complete &= bool(relation, "complete", false);
        }
        manifest.addProperty("guardedCaseCount", caseCount);
        manifest.addProperty("pathWorklistStatus", string(pathManifest,
                "status"));
        manifest.addProperty("diagnosticCount", diagnostics.size());
        manifest.add("diagnostics", GSON.toJsonTree(diagnostics));
        manifest.addProperty("complete", complete);
        manifest.addProperty("status", complete
                ? "COMPLETE_GUARDED_REGION_RELATIONS"
                : "REGION_RELATIONS_WITH_EXPLICIT_GAPS");
        manifest.addProperty("semanticAuthority",
                "RUNTIME_CONCOLIC_PATHS_ONLY");
        manifest.addProperty("domainSemanticAdapterAllowed", false);
        return new Result(merged, manifest);
    }

    private static JsonObject mergeGroup(List<JsonObject> source,
                                         JsonObject pathManifest,
                                         List<JsonObject> diagnostics) {
        List<JsonObject> values = new ArrayList<>(source);
        Collections.sort(values, Comparator.comparing(
                RegionPathWorklist::stablePathKey));
        JsonObject first = values.get(0);
        String region = string(first, "regionId");
        Set<String> pathKeys = new LinkedHashSet<>();
        JsonArray cases = new JsonArray();
        boolean casesComplete = true;
        for (JsonObject summary : values) {
            String pathKey = RegionPathWorklist.stablePathKey(summary);
            if (!pathKeys.add(pathKey)) continue;
            JsonObject item = new JsonObject();
            String caseId = "CASE." + pathKey.substring(0, 16);
            item.addProperty("caseId", caseId);
            item.addProperty("pathKey", pathKey);
            // Engine-local ids are recycled by every concolic JVM.  Preserve a
            // deterministic case namespace in the relation so the SMT emitter
            // never mistakes equal raw counters from two reruns for one value.
            item.addProperty("symbolScope", "region:" + region
                    + "/case:" + caseId);
            JsonObject guard = new JsonObject();
            guard.addProperty("kind", "PATH_CONDITION");
            guard.add("conditions", array(summary,
                    "pathCondition").deepCopy());
            item.add("guard", guard);
            item.add("outputExpressions", object(summary,
                    "outputExpressions").deepCopy());
            item.add("heapStateInitializers", array(summary,
                    "heapStateInitializers").deepCopy());
            item.add("heapObservations", array(summary,
                    "heapObservations").deepCopy());
            item.add("finiteMapSnapshots", array(summary,
                    "finiteMapSnapshots").deepCopy());
            // Occurrence-specific field symbols are scoped to this execution
            // case.  Preserve them inside the case and never union them at the
            // merged-summary root, where equal ids from separate JVM runs
            // could otherwise be mistaken for one object instance.
            item.add("dynamicFieldBindings", array(summary,
                    "dynamicFieldBindings").deepCopy());
            item.add("engineArrayInputBindings", array(summary,
                    "engineArrayInputBindings").deepCopy());
            item.add("vmIntrinsicPlaceholderBindings", array(summary,
                    "vmIntrinsicPlaceholderBindings").deepCopy());
            item.add("unforcedEnvironmentValidationRequirements",
                    array(summary,
                            "unforcedEnvironmentValidationRequirements")
                            .deepCopy());
            copyIfPresent(summary, item,
                    "inputMaterializationAdmission");
            copyIfPresent(summary, item,
                    "vmIntrinsicPlaceholderBindingAdmission");
            item.add("heapEffects", array(summary,
                    "heapEffects").deepCopy());
            item.add("heapEffectModel", object(summary,
                    "heapEffectModel").deepCopy());
            item.addProperty("relationallyComplete", bool(summary,
                    "relationallyComplete", false));
            item.addProperty("normalExit", bool(summary,
                    "normalExit", false));
            item.addProperty("exceptionType", string(summary,
                    "exceptionType"));
            item.addProperty("sourceSummaryId", string(summary,
                    "summaryId"));
            item.addProperty("sourceActivationId", string(summary,
                    "activationId"));
            item.addProperty("admissionAuthority",
                    "VALIDATED_UNFORCED_CONCOLIC_REPLAY_OR_SEED_PATH");
            cases.add(item);
            if (!bool(summary, "relationallyComplete", false)) {
                casesComplete = false;
                diagnostics.add(gap(region,
                        "INCOMPLETE_PATH_TRANSFORMER:" + pathKey));
            }
        }

        boolean pathClosed = bool(pathManifest, "complete", false);
        if (!pathClosed) diagnostics.add(gap(region,
                "PATH_WORKLIST_NOT_CLOSED:" + string(pathManifest,
                        "status")));
        boolean complete = pathClosed && casesComplete && cases.size() > 0;
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.addProperty("caseCount", cases.size());
        relation.add("cases", cases);
        relation.addProperty("guardSemantics",
                "EXACT_NORMALIZED_PATH_CONDITION");
        relation.addProperty("mergeSemantics",
                "GUARDED_OUTPUT_AND_STATE_TRANSFORMERS");
        relation.addProperty("coverageSemantics",
                "SOLVER_CLOSED_RELEVANT_BRANCH_FLIPS_WITHIN_BOUNDS");
        relation.addProperty("pathClosureStatus", string(pathManifest,
                "status"));
        relation.addProperty("complete", complete);
        relation.addProperty("authority",
                "RUNTIME_CONCOLIC_MULTI_PATH_SUMMARIES");

        String relationHash = sha256(region + "\n"
                + canonical(first.get("requestedOutput")) + "\n"
                + canonical(cases));
        Set<String> sourceInstances = new TreeSet<>();
        Map<String, JsonObject> bindingsByKey = new LinkedHashMap<>();
        for (JsonObject summary : values) {
            String instance = string(summary, "regionInstanceId");
            if (!instance.isEmpty()) sourceInstances.add(instance);
            for (JsonElement element : firstArray(summary,
                    "edgeBindings", "producerBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                String sourceInstance = firstNonBlank(string(binding,
                        "fromRegionInstance"), string(binding,
                        "producerRegionInstance"));
                if (!sourceInstance.isEmpty()) {
                    sourceInstances.add(sourceInstance);
                }
                bindingsByKey.put(canonical(binding), binding.deepCopy());
            }
        }
        JsonArray mergedBindings = new JsonArray();
        List<String> bindingKeys = new ArrayList<>(bindingsByKey.keySet());
        Collections.sort(bindingKeys);
        for (String key : bindingKeys) {
            mergedBindings.add(bindingsByKey.get(key));
        }
        JsonObject merged = new JsonObject();
        merged.addProperty("schemaVersion", 1);
        merged.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        merged.addProperty("summaryId", "SUMMARY." + region
                + ".MERGED." + relationHash.substring(0, 12));
        merged.addProperty("cacheKey", relationHash);
        merged.addProperty("activationId", "MERGED_PATHS");
        merged.addProperty("regionId", region);
        merged.add("sourceRegionInstanceIds",
                GSON.toJsonTree(sourceInstances));
        merged.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        merged.add("requestedOutput", object(first,
                "requestedOutput").deepCopy());
        merged.add("requestedOutputSlice", object(first,
                "requestedOutputSlice").deepCopy());
        merged.add("edgeBindings", mergedBindings);
        merged.add("pathCondition", new JsonArray());
        merged.add("outputExpressions", new JsonObject());
        merged.add("heapStateInitializers", new JsonArray());
        merged.add("heapObservations", new JsonArray());
        merged.add("finiteMapSnapshots", new JsonArray());
        merged.add("dynamicFieldBindings", new JsonArray());
        merged.add("engineArrayInputBindings", new JsonArray());
        merged.add("vmIntrinsicPlaceholderBindings", new JsonArray());
        merged.add("unforcedEnvironmentValidationRequirements",
                new JsonArray());
        merged.add("heapEffects", new JsonArray());
        merged.add("regionRelation", relation);
        merged.addProperty("relationallyComplete", complete);
        merged.addProperty("valid", cases.size() > 0);
        merged.addProperty("confidence", "RUNTIME_CONCOLIC_MERGED");
        return merged;
    }

    private static void copyIfPresent(JsonObject source, JsonObject target,
                                      String field) {
        JsonElement value = source == null ? null : source.get(field);
        if (value != null && !value.isJsonNull()) {
            target.add(field, value.deepCopy());
        }
    }

    private static JsonObject gap(String region, String reason) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", region);
        result.addProperty("reason", reason);
        return result;
    }

    public static final class Result {
        public final List<JsonObject> summaries;
        public final JsonObject manifest;

        private Result(List<JsonObject> summaries, JsonObject manifest) {
            this.summaries = summaries;
            this.manifest = manifest;
        }
    }

    private static final class Arguments {
        private final List<Path> inputs = new ArrayList<>();
        private Path pathManifest;
        private Path output;
        private Path manifest;

        private static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String key = argv[index];
                if (index + 1 >= argv.length) throw new IllegalArgumentException(
                        "Expected --key value, got " + key);
                String value = argv[++index];
                if ("--summaries".equals(key)) result.inputs.add(
                        Paths.get(value));
                else if ("--path-manifest".equals(key)) {
                    result.pathManifest = Paths.get(value);
                } else if ("--output".equals(key)) {
                    result.output = Paths.get(value);
                } else if ("--manifest".equals(key)) {
                    result.manifest = Paths.get(value);
                } else throw new IllegalArgumentException("Unknown " + key);
            }
            if (result.inputs.isEmpty() || result.pathManifest == null
                    || result.output == null) throw new IllegalArgumentException(
                    "--summaries, --path-manifest, and --output are required");
            if (result.manifest == null) result.manifest = result.output
                    .resolveSibling("region_relation_merge_manifest.json");
            return result;
        }
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement value = JsonParser.parseString(line);
                if (value.isJsonObject()) result.add(value.getAsJsonObject());
            }
        }
        return result;
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement value = JsonParser.parseString(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        return value.isJsonObject() ? value.getAsJsonObject()
                : new JsonObject();
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(GSON.toJson(row))
                .append(System.lineSeparator());
        Files.write(path, value.toString().getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
    }

    private static String canonical(JsonElement value) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) return GSON.toJson(value);
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(canonical(element));
            }
            return result.append(']').toString();
        }
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(value.getAsJsonObject().keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':')
                    .append(canonical(value.getAsJsonObject().get(key)));
        }
        return result.append('}').toString();
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value.getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) result.append(String.format("%02x",
                    item & 0xff));
            return result.toString();
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static List<JsonObject> safe(List<JsonObject> values) {
        return values == null ? Collections.<JsonObject>emptyList() : values;
    }

    private static JsonObject object(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray array(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonArray firstArray(JsonObject owner, String... fields) {
        for (String field : fields) {
            JsonElement value = owner == null ? null : owner.get(field);
            if (value != null && value.isJsonArray()) {
                return value.getAsJsonArray();
            }
        }
        return new JsonArray();
    }

    private static String string(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static String firstNonBlank(String... values) {
        if (values == null) return "";
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }

    private static boolean bool(JsonObject owner, String field,
                                boolean fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject owner, String field,
                               int fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }
}
