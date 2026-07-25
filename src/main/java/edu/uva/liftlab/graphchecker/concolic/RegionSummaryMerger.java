package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.CanonicalJson.render;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

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
        boolean complete = diagnostics.isEmpty() && !merged.isEmpty();
        for (JsonObject summary : merged) {
            complete &= bool(summary, "relationallyComplete", false);
        }
        manifest.add("diagnostics", GSON.toJsonTree(diagnostics));
        manifest.addProperty("complete", complete);
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
            if (input.contract.members().size() > 1
                    && !exactOutputExpressions(summary,
                    input.contract.outputPorts())) {
                casesComplete = false;
                diagnostics.add(gap(region,
                        "JOINT_OUTPUT_EXPRESSION_SET_MISMATCH:"
                                + pathKey));
                continue;
            }
            cases.add(pathCase(summary, pathKey));
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
        OutputClosureContract pathContract = null;
        try {
            pathContract = OutputClosureCodec.decode(pathManifest);
        } catch (IllegalArgumentException malformed) {
            outputScopeMatches = false;
            diagnostics.add(gap(region,
                    "INVALID_PATH_WORKLIST_OUTPUT_CLOSURE:"
                            + firstNonBlank(malformed.getMessage(),
                            "MISSING")));
        }
        if (pathContract != null
                && (!firstInput.contract.demandKey().equals(
                pathContract.demandKey())
                || !firstInput.contract.closureFingerprint().equals(
                pathContract.closureFingerprint()))) {
            outputScopeMatches = false;
            diagnostics.add(gap(region,
                    "PATH_WORKLIST_OUTPUT_CLOSURE_MISMATCH"));
        }
        boolean complete = pathClosed && outputScopeMatches
                && casesComplete && cases.size() > 0;
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.add("cases", cases);

        String relationHash = sha256(region + "\n"
                + firstInput.outputIdentity + "\n"
                + render(cases));
        Map<String, JsonObject> bindingsByKey = new LinkedHashMap<>();
        for (MergeInput input : values) {
            JsonObject summary = input.summary;
            for (JsonElement element : array(summary, "edgeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                bindingsByKey.put(render(binding), binding.deepCopy());
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
        merged.addProperty("regionId", region);
        merged.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        OutputClosureCodec.writeTo(merged, firstInput.contract);
        merged.add("edgeBindings", mergedBindings);
        merged.add("regionRelation", relation);
        merged.addProperty("relationallyComplete", complete);
        return merged;
    }

    private static JsonObject pathCase(JsonObject summary, String pathKey) {
        JsonObject item = new JsonObject();
        String caseId = "CASE." + pathKey;
        item.addProperty("caseId", caseId);
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
        stable.addProperty("normalExit", bool(summary,
                "normalExit", false));
        stable.addProperty("exceptionType", string(summary,
                "exceptionType"));
        return render(stable);
    }

    private static boolean exactOutputExpressions(
            JsonObject summary, Set<String> outputPorts) {
        JsonElement encoded = summary.get("outputExpressions");
        return encoded != null && encoded.isJsonObject()
                && new TreeSet<>(encoded.getAsJsonObject().keySet())
                .equals(new TreeSet<>(outputPorts));
    }

    private static String outputIdentity(JsonObject summary) {
        return render(summary.get(OutputClosureContract.FIELD));
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
            if (!summary.has(OutputClosureContract.FIELD)) {
                throw new IllegalArgumentException(
                        "canonical outputClosure is required");
            }
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
                    render(contract.toJson()));
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
        return ArtifactIO.readJsonl(path);
    }

    private static JsonObject readJson(Path path) throws IOException {
        return ArtifactIO.readObject(path);
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        ArtifactIO.replaceJsonl(path, rows);
    }

    private static List<JsonObject> safe(List<JsonObject> values) {
        return values == null ? Collections.<JsonObject>emptyList() : values;
    }

    private static String firstNonBlank(String... values) {
        if (values == null) return "";
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }

}
