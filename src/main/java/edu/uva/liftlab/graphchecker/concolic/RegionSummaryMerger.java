package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

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
        if (arguments.manifest != null) {
            Files.write(arguments.manifest,
                    (GSON.toJson(result.manifest) + System.lineSeparator())
                            .getBytes(StandardCharsets.UTF_8),
                    StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING,
                    StandardOpenOption.WRITE);
        }
        System.out.println(GSON.toJson(result.manifest));
    }

    public static Result merge(List<JsonObject> summaries,
                               JsonObject pathManifest) {
        Map<String, List<MergeInput>> groups = new LinkedHashMap<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        for (JsonObject summary : safe(summaries)) {
            if (!RegionCaptureGoal.from(summary).isOutputClosure()) {
                continue;
            }
            MergeInput input;
            try {
                input = MergeInput.from(summary);
            } catch (IllegalArgumentException malformed) {
                diagnostics.add(gap(string(summary, "regionId"),
                        "INVALID_OUTPUT_CLOSURE:"
                                + firstNonBlank(malformed.getMessage(),
                                "UNKNOWN")));
                continue;
            }
            if (input == null) {
                diagnostics.add(gap(string(summary, "regionId"),
                        "MISSING_REQUESTED_OUTPUT"));
                continue;
            }
            List<MergeInput> values = groups.get(input.groupKey);
            if (values == null) {
                values = new ArrayList<>();
                groups.put(input.groupKey, values);
            }
            values.add(input);
        }

        List<JsonObject> merged = new ArrayList<>();
        for (List<MergeInput> values : groups.values()) {
            merged.add(mergeGroup(values, pathManifest, diagnostics));
        }
        Collections.sort(merged, Comparator.comparing(value ->
                string(value, "regionId") + "\n"
                        + outputIdentity(value)));
        if (merged.isEmpty()) {
            diagnostics.add(gap("", "NO_VALID_OUTPUT_CLOSURE_RELATIONS"));
        }

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "REGION_RELATION_MERGE_MANIFEST");
        manifest.addProperty("inputSummaryCount", safe(summaries).size());
        manifest.addProperty("mergedRelationCount", merged.size());
        int caseCount = 0;
        boolean complete = diagnostics.isEmpty() && !merged.isEmpty();
        for (JsonObject summary : merged) {
            JsonObject relation = object(summary, "regionRelation");
            caseCount += integer(relation, "caseCount", 0);
            complete &= bool(relation, "complete", false);
        }
        manifest.addProperty("guardedCaseCount", caseCount);
        manifest.addProperty("pathWorklistState", string(pathManifest,
                "state"));
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

    private static JsonObject mergeGroup(List<MergeInput> source,
                                         JsonObject pathManifest,
                                         List<JsonObject> diagnostics) {
        List<MergeInput> values = new ArrayList<>(source);
        Collections.sort(values, Comparator.comparing(
                value -> value.pathKey));
        MergeInput firstInput = values.get(0);
        JsonObject first = firstInput.summary;
        String region = string(first, "regionId");
        Map<String, String> payloadByPath = new LinkedHashMap<>();
        JsonArray cases = new JsonArray();
        boolean casesComplete = true;
        for (MergeInput input : values) {
            JsonObject summary = input.summary;
            String pathKey = input.pathKey;
            String payload = stableCasePayload(summary);
            String previous = payloadByPath.putIfAbsent(pathKey, payload);
            if (previous != null) {
                if (!previous.equals(payload)) {
                    casesComplete = false;
                    diagnostics.add(gap(region,
                            "CONFLICTING_DUPLICATE_PATH_PAYLOAD:"
                                    + pathKey));
                }
                continue;
            }
            if (input.joint()
                    && !exactOutputExpressions(summary,
                    input.contract.outputPorts())) {
                casesComplete = false;
                diagnostics.add(gap(region,
                        "JOINT_OUTPUT_EXPRESSION_SET_MISMATCH:"
                                + pathKey));
                continue;
            }
            cases.add(pathCase(summary, region, pathKey));
            if (!bool(summary, "relationallyComplete", false)) {
                casesComplete = false;
                diagnostics.add(gap(region,
                        "INCOMPLETE_PATH_TRANSFORMER:" + pathKey));
            }
        }

        String pathState = string(pathManifest, "state");
        String pathRegion = string(pathManifest, "regionId");
        boolean hasObservedPath = integer(pathManifest,
                "observedPathCount", 0) > 0;
        boolean pathClosed = RegionPathWorklist.State.CLOSED.name().equals(
                pathState) && hasObservedPath && region.equals(pathRegion);
        boolean outputScopeMatches = true;
        if (!region.equals(pathRegion)) {
            diagnostics.add(gap(region,
                    "PATH_WORKLIST_REGION_MISMATCH:" + pathRegion));
        } else if (!hasObservedPath) {
            diagnostics.add(gap(region,
                    "PATH_WORKLIST_HAS_NO_OBSERVED_PATH"));
        } else if (!pathClosed) {
            diagnostics.add(gap(region,
                    "PATH_WORKLIST_NOT_CLOSED:" + pathState));
        }
        if (firstInput.contract != null) {
            String demand = string(pathManifest, "outputDemandKey");
            String fingerprint = string(pathManifest,
                    "outputClosureFingerprint");
            if (!firstInput.contract.demandKey().equals(demand)) {
                outputScopeMatches = false;
                diagnostics.add(gap(region,
                        "PATH_WORKLIST_OUTPUT_DEMAND_MISMATCH:"
                                + firstNonBlank(demand, "MISSING")));
            }
            if (!firstInput.contract.closureFingerprint().equals(
                    fingerprint)) {
                outputScopeMatches = false;
                diagnostics.add(gap(region,
                        "PATH_WORKLIST_OUTPUT_CLOSURE_FINGERPRINT_MISMATCH:"
                                + firstNonBlank(fingerprint, "MISSING")));
            }
        }
        boolean complete = pathClosed && outputScopeMatches
                && casesComplete && cases.size() > 0;
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
        relation.addProperty("pathClosureState", pathState);
        relation.addProperty("complete", complete);
        relation.addProperty("authority",
                "RUNTIME_CONCOLIC_MULTI_PATH_SUMMARIES");

        String relationHash = sha256(region + "\n"
                + firstInput.outputIdentity + "\n"
                + canonical(cases));
        Set<String> sourceInstances = new TreeSet<>();
        Map<String, JsonObject> bindingsByKey = new LinkedHashMap<>();
        for (MergeInput input : values) {
            JsonObject summary = input.summary;
            String instance = string(summary, "regionInstanceId");
            if (!instance.isEmpty()) sourceInstances.add(instance);
            for (JsonElement element : array(summary, "edgeBindings")) {
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
                + ".MERGED." + relationHash);
        merged.addProperty("activationId", "MERGED_PATHS");
        merged.addProperty("regionId", region);
        merged.add("sourceRegionInstanceIds",
                GSON.toJsonTree(sourceInstances));
        merged.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        if (firstInput.contract == null) {
            merged.add("requestedOutput", object(first,
                    "requestedOutput").deepCopy());
            merged.add("requestedOutputSlice", object(first,
                    "requestedOutputSlice").deepCopy());
        } else {
            OutputClosureContract.Producer producer =
                    firstInput.contract.producer();
            merged.addProperty("regionInstanceId",
                    producer.regionInstanceId());
            merged.addProperty("rootCallId", producer.rootCallId());
            OutputClosureCodec.writeTo(merged, firstInput.contract);
        }
        merged.add("edgeBindings", mergedBindings);
        merged.add("regionRelation", relation);
        merged.addProperty("relationallyComplete", complete);
        return merged;
    }

    private static JsonObject pathCase(JsonObject summary, String region,
                                       String pathKey) {
        JsonObject item = new JsonObject();
        String caseId = "CASE." + pathKey.substring(0, 16);
        item.addProperty("caseId", caseId);
        item.addProperty("pathKey", pathKey);
        // Engine-local ids are recycled by every concolic JVM. Preserve a
        // deterministic namespace per case.
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
        // Occurrence-specific symbols stay inside their source case and are
        // never unioned at the merged root.
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
        item.add("heapEffects", array(summary,
                "heapEffects").deepCopy());
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
        return item;
    }

    /**
     * stablePathKey already covers the normalized guard, outputs, heap
     * effects, and runtime bindings. These remaining case certificates must
     * also agree before two observations with that key may collapse.
     */
    private static String stableCasePayload(JsonObject summary) {
        JsonObject stable = new JsonObject();
        stable.add("heapStateInitializers", array(summary,
                "heapStateInitializers").deepCopy());
        stable.add("heapObservations", array(summary,
                "heapObservations").deepCopy());
        stable.add("finiteMapSnapshots", array(summary,
                "finiteMapSnapshots").deepCopy());
        stable.add("vmIntrinsicPlaceholderBindings", array(summary,
                "vmIntrinsicPlaceholderBindings").deepCopy());
        stable.add("unforcedEnvironmentValidationRequirements",
                array(summary,
                        "unforcedEnvironmentValidationRequirements")
                        .deepCopy());
        stable.addProperty("relationallyComplete", bool(summary,
                "relationallyComplete", false));
        stable.addProperty("normalExit", bool(summary,
                "normalExit", false));
        stable.addProperty("exceptionType", string(summary,
                "exceptionType"));
        return canonical(stable);
    }

    private static boolean exactOutputExpressions(
            JsonObject summary, Set<String> outputPorts) {
        JsonElement encoded = summary.get("outputExpressions");
        return encoded != null && encoded.isJsonObject()
                && new TreeSet<>(encoded.getAsJsonObject().keySet())
                .equals(new TreeSet<>(outputPorts));
    }

    private static String outputIdentity(JsonObject summary) {
        JsonElement closure = summary.get(OutputClosureContract.FIELD);
        return closure != null
                ? canonical(closure)
                : canonical(summary.get("requestedOutput"));
    }

    private static final class MergeInput {
        private final JsonObject summary;
        private final OutputClosureContract contract;
        private final String groupKey;
        private final String outputIdentity;
        private final String pathKey;

        private MergeInput(JsonObject summary,
                           OutputClosureContract contract,
                           String groupKey, String outputIdentity) {
            this.summary = summary;
            this.contract = contract;
            this.groupKey = groupKey;
            this.outputIdentity = outputIdentity;
            this.pathKey = RegionPathWorklist.stablePathKey(summary);
        }

        private static MergeInput from(JsonObject summary) {
            if (summary.has(OutputClosureContract.FIELD)) {
                OutputClosureContract contract =
                        OutputClosureCodec.decode(summary);
                OutputClosureContract.Producer producer =
                        contract.producer();
                String key = "OUTPUT_CLOSURE_V1\n"
                        + producer.regionId() + "\n"
                        + producer.regionInstanceId() + "\n"
                        + producer.rootCallId() + "\n"
                        + contract.demandKey() + "\n"
                        + contract.closureFingerprint();
                return new MergeInput(summary, contract, key,
                        canonical(contract.toJson()));
            }
            String region = string(summary, "regionId");
            JsonObject output = object(summary, "requestedOutput");
            if (region.isEmpty() || output.size() == 0) return null;
            String identity = canonical(output);
            return new MergeInput(summary, null,
                    "LEGACY_SINGLETON\n" + region + "\n" + identity,
                    identity);
        }

        private boolean joint() {
            return contract != null && contract.members().size() > 1;
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
