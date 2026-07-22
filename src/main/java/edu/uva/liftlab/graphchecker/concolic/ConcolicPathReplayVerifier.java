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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

/**
 * Standalone, fail-closed admission gate for one solver path-flip replay.
 *
 * <p>The activation plan is part of the boundary: the replay task alone
 * identifies the seed activation, whereas the plan identifies the fresh
 * replay activation which must occur exactly once in both the raw results and
 * imported summaries.  The existing {@link ConcolicReplayValidator} remains
 * the authority for assignment, prefix, flip, and requested-output checks.</p>
 */
public final class ConcolicPathReplayVerifier {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();

    private ConcolicPathReplayVerifier() {
    }

    public static void main(String[] argv) throws Exception {
        int status = run(argv);
        if (status != 0) System.exit(status);
    }

    static int run(String[] argv) throws IOException {
        Arguments arguments = Arguments.parse(argv);
        JsonObject report = verify(arguments);
        writeNew(arguments.output, GSON.toJson(report)
                + System.lineSeparator());
        System.out.println(GSON.toJson(report));
        return bool(report, "valid", false) ? 0 : 2;
    }

    static JsonObject verify(Arguments arguments) throws IOException {
        requireFile(arguments.task, "path replay validation task");
        requireFile(arguments.activationPlan, "path replay activation plan");
        requireFile(arguments.results, "path replay raw results");
        requireFile(arguments.summary, "path replay imported summaries");

        JsonObject task = readObject(arguments.task);
        BranchReplayContract replayContract = replayContract(task,
                "task");
        List<JsonObject> activations = readJsonl(arguments.activationPlan);
        List<JsonObject> rawRows = readJsonl(arguments.results);
        List<JsonObject> summaryRows = readJsonl(arguments.summary);
        JsonArray failures = new JsonArray();

        JsonObject report = new JsonObject();
        report.addProperty("schemaVersion", 1);
        report.addProperty("kind",
                "CONCOLIC_PATH_REPLAY_VERIFICATION_MANIFEST");
        report.add("taskArtifact", sourceArtifact(arguments.task, 1));
        report.add("activationPlanArtifact", sourceArtifact(
                arguments.activationPlan, activations.size()));
        report.add("rawResultsArtifact", sourceArtifact(arguments.results,
                rawRows.size()));
        report.add("importedSummariesArtifact", sourceArtifact(
                arguments.summary, summaryRows.size()));

        require(failures, "TASK_IS_NOT_REGION_PATH_FLIP",
                "REGION_PATH_FLIP".equals(string(task, "kind")));
        require(failures, "TASK_IS_NOT_OUTPUT_CLOSURE",
                RegionCaptureGoal.from(task).isOutputClosure());
        require(failures, "TASK_QUERY_KEY_MISSING",
                !string(task, "queryKey").isEmpty());
        require(failures, "TASK_QUERY_KEY_IS_NOT_LOWERCASE_SHA256",
                string(task, "queryKey").matches("[0-9a-f]{64}"));
        require(failures, "TASK_REGION_ID_MISSING",
                !string(task, "regionId").isEmpty());

        require(failures, "ACTIVATION_PLAN_ROW_COUNT_NOT_ONE",
                activations.size() == 1);
        JsonObject activation = activations.size() == 1
                ? activations.get(0) : new JsonObject();
        String activationId = string(activation, "activationId");
        String regionId = string(task, "regionId");
        String queryKey = string(task, "queryKey");
        report.addProperty("activationId", activationId);
        report.addProperty("regionId", regionId);
        report.addProperty("queryKey", queryKey);

        validateActivation(task, activation, replayContract, failures);

        require(failures, "RAW_RESULTS_FILE_ROW_COUNT_NOT_ONE",
                rawRows.size() == 1);
        require(failures, "IMPORTED_SUMMARIES_FILE_ROW_COUNT_NOT_ONE",
                summaryRows.size() == 1);
        List<JsonObject> matchingRaw = matchingActivation(rawRows,
                activationId);
        List<JsonObject> matchingSummaries = matchingActivation(summaryRows,
                activationId);
        report.addProperty("matchingRawResultCount", matchingRaw.size());
        report.addProperty("matchingImportedSummaryCount",
                matchingSummaries.size());
        require(failures, "RAW_RESULT_ACTIVATION_NOT_UNIQUE",
                !activationId.isEmpty() && matchingRaw.size() == 1);
        require(failures, "IMPORTED_SUMMARY_ACTIVATION_NOT_UNIQUE",
                !activationId.isEmpty() && matchingSummaries.size() == 1);

        JsonObject raw = matchingRaw.size() == 1
                ? matchingRaw.get(0) : new JsonObject();
        JsonObject summary = matchingSummaries.size() == 1
                ? matchingSummaries.get(0) : new JsonObject();
        if (matchingSummaries.size() == 1) {
            report.addProperty("observedPathKey",
                    RegionPathWorklist.stablePathKey(summary));
            report.addProperty("summaryId", string(summary, "summaryId"));
        }
        if (matchingRaw.size() == 1) {
            require(failures, "RAW_RESULT_REGION_ID_MISMATCH",
                    regionId.equals(string(raw, "regionId")));
            require(failures, "RAW_RESULT_EVENT_MISMATCH",
                    "CONCOLIC_REGION_RESULT".equals(string(raw, "event")));
            require(failures, "RAW_RESULT_EXECUTION_MODE_MISMATCH",
                    "SYMBOLIC_CONCOLIC".equals(string(raw,
                            "executionMode")));
            require(failures, "RAW_MODEL_ASSIGNMENT_COUNT_MISMATCH",
                    integer(raw, "modelAssignmentCount", -1)
                            == array(task, "modelAssignments").size());
        }
        if (matchingSummaries.size() == 1) {
            require(failures, "IMPORTED_SUMMARY_REGION_ID_MISMATCH",
                    regionId.equals(string(summary, "regionId")));
        }

        if (replayContract != null) {
            List<BranchWitness> observed = branchWitnesses(raw, failures);
            BranchReplayObservationValidator.Result observation =
                    BranchReplayObservationValidator.validate(
                            replayContract, observed);
            report.add("branchReplayObservation", observation.toJson());
            require(failures, "BRANCH_REPLAY_CONTRACT_NOT_SATISFIED",
                    observation.valid());
        } else {
            JsonObject scheduledTarget = exactScheduledTarget(task, raw);
            report.add("scheduledTargetValidation", scheduledTarget);
            require(failures, "SCHEDULED_FLIP_TARGET_NOT_EXACT",
                    bool(scheduledTarget, "valid", false));
            JsonObject orderedPrefix = exactOrderedPrefix(task, raw);
            report.add("orderedPrefixValidation", orderedPrefix);
            require(failures, "REPLAY_BRANCH_PREFIX_NOT_EXACT",
                    bool(orderedPrefix, "valid", false));
        }

        JsonObject replayValidation = ConcolicReplayValidator.validate(task,
                raw, summary);
        report.add("replayValidation", replayValidation);
        require(failures, "CONCOLIC_REPLAY_VALIDATOR_REJECTED",
                bool(replayValidation, "valid", false));

        report.add("failures", failures);
        int validatorFailures = integer(replayValidation, "failureCount", 0);
        report.addProperty("gateFailureCount", failures.size());
        report.addProperty("validatorFailureCount", validatorFailures);
        report.addProperty("failureCount", failures.size()
                + validatorFailures);
        boolean valid = failures.size() == 0
                && bool(replayValidation, "valid", false);
        report.addProperty("valid", valid);
        report.addProperty("status", valid
                ? "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
                : "PATH_FLIP_REPLAY_REJECTED");
        report.addProperty("admissionAuthority", valid
                ? "EXACT_REPLAY_ACTIVATION_AND_SCHEDULED_TARGET_PLUS_"
                + "CONCOLIC_REPLAY_VALIDATOR_V1" : "NONE");
        return report;
    }

    private static void validateActivation(JsonObject task,
                                           JsonObject activation,
                                           BranchReplayContract contract,
                                           JsonArray failures) {
        String activationId = string(activation, "activationId");
        String scheduleId = string(activation, "scheduleId");
        String pathId = shortHash(string(task, "queryKey"));
        require(failures, "REPLAY_ACTIVATION_ID_MISSING",
                !activationId.isEmpty());
        require(failures, "REPLAY_SCHEDULE_ID_MISSING",
                !scheduleId.isEmpty());
        require(failures, "REPLAY_ACTIVATION_ID_QUERY_HASH_MISMATCH",
                ("ACT.PATH." + pathId).equals(activationId));
        require(failures, "REPLAY_SCHEDULE_ID_QUERY_HASH_MISMATCH",
                ("SCHEDULE.PATH." + pathId).equals(scheduleId));
        require(failures, "WRONG_REPLAY_EXECUTION_PHASE",
                "REPLAY_OUTPUT_PATH_FLIP".equals(string(activation,
                        "executionPhase")));
        require(failures, "REPLAY_CAPTURE_GOAL_IS_NOT_OUTPUT_CLOSURE",
                RegionCaptureGoal.from(activation).isOutputClosure());
        require(failures, "REPLAY_REGION_ID_MISMATCH",
                string(task, "regionId").equals(string(activation,
                        "regionId")));
        require(failures, "REPLAY_QUERY_KEY_MISMATCH",
                string(task, "queryKey").equals(string(activation,
                        "pathQueryKey")));
        require(failures, "REPLAY_ACTIVATION_SELECTION_MISMATCH",
                activationId.equals(string(activation,
                        "activationSelectionRequired")));
        require(failures, "REPLAY_BUNDLE_ROOT_MISMATCH",
                activationId.equals(string(activation,
                        "activationBundleRootActivationId")));
        require(failures, "REPLAY_BUNDLE_SCHEDULE_MISMATCH",
                scheduleId.equals(string(activation,
                        "activationBundleScheduleId")));
        require(failures, "REPLAY_BUNDLE_IS_NOT_SINGLETON",
                integer(activation, "activationBundleSize", -1) == 1
                        && integer(activation, "activationBundleIndex", -1)
                        == 0);

        JsonArray taskAssignments = array(task, "modelAssignments");
        JsonArray activationAssignments = array(activation,
                "modelAssignments");
        require(failures, "EMPTY_REPLAY_MODEL_ASSIGNMENT_PLAN",
                taskAssignments.size() > 0);
        require(failures, "REPLAY_MODEL_ASSIGNMENT_PLAN_MISMATCH",
                canonical(taskAssignments).equals(canonical(
                        activationAssignments)));
        if (contract != null) {
            BranchReplayContract activationContract;
            try {
                activationContract = replayContract(activation,
                        "activation");
            } catch (IOException malformed) {
                activationContract = null;
            }
            require(failures, "REPLAY_CONTRACT_MISSING_OR_MISMATCHED",
                    activationContract != null && contract.contractId()
                            .equals(activationContract.contractId()));
        } else {
            require(failures, "TASK_EXPECTED_PREFIX_MISSING",
                    hasArray(task, "expectedBranchPrefix"));
            require(failures, "REPLAY_PREFIX_PLAN_MISMATCH",
                    canonical(array(task, "expectedBranchPrefix")).equals(
                            canonical(array(activation,
                                    "expectedBranchPrefix"))));

            JsonObject target = object(activation, "targetBranch");
            require(failures, "REPLAY_TARGET_SITE_MISMATCH",
                    string(task, "flipSite").equals(string(target,
                            "siteId")));
            require(failures, "REPLAY_TARGET_OCCURRENCE_MISMATCH",
                    integer(task, "flipOccurrence", -1)
                            == integer(target, "occurrence", -2));
            require(failures, "REPLAY_TARGET_OUTCOME_MISMATCH",
                    exactBoolean(target, "desiredOutcome",
                            bool(task, "desiredOutcome", false)));
            require(failures, "REPLAY_TARGET_IS_NOT_VALIDATION_ONLY",
                    exactBoolean(target, "validationOnly", true));
            require(failures, "REPLAY_TARGET_ALLOWS_BRANCH_OVERRIDE",
                    exactBoolean(target, "branchOverrideAllowed", false));
            require(failures, "REPLAY_PLAN_DOES_NOT_PROHIBIT_OVERRIDE",
                    exactBoolean(activation, "branchOverrideProhibited",
                            true));
        }
        require(failures, "REPLAY_PLAN_CONTAINS_FORCED_BRANCH",
                array(activation, "forcedBranches").size() == 0);
        require(failures, "REPLAY_PLAN_CONTAINS_NON_INPUT_MATERIALIZATION",
                array(activation, "replayMaterializations").size() == 0);
    }

    private static BranchReplayContract replayContract(
            JsonObject container, String label) throws IOException {
        JsonElement encoded = container == null ? null
                : container.get("replayContract");
        if (encoded == null) return null;
        if (!encoded.isJsonObject()) {
            throw new IOException(label + " replayContract is not an object");
        }
        try {
            return BranchReplayContract.fromJson(encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            throw new IOException(label + " replayContract is invalid: "
                    + malformed.getMessage(), malformed);
        }
    }

    private static List<BranchWitness> branchWitnesses(
            JsonObject raw, JsonArray failures) {
        List<BranchWitness> result = new ArrayList<>();
        int ordinal = 0;
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) {
                ordinal++;
                continue;
            }
            JsonElement encoded = element.getAsJsonObject().get("witness");
            if (encoded == null) {
                ordinal++;
                continue;
            }
            try {
                result.add(BranchWitness.fromJson(
                        encoded.getAsJsonObject()));
            } catch (RuntimeException malformed) {
                failures.add("MALFORMED_BRANCH_WITNESS_AT_" + ordinal);
            }
            ordinal++;
        }
        return result;
    }

    private static JsonObject exactScheduledTarget(JsonObject task,
                                                   JsonObject raw) {
        String site = string(task, "flipSite");
        int occurrence = integer(task, "flipOccurrence", -1);
        boolean desired = bool(task, "desiredOutcome", false);
        List<JsonObject> matches = new ArrayList<>();
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (site.equals(string(mapping, "siteId"))
                    && occurrence == integer(mapping, "occurrence", -2)) {
                matches.add(mapping);
            }
        }
        JsonObject result = new JsonObject();
        result.addProperty("siteId", site);
        result.addProperty("occurrence", occurrence);
        result.addProperty("desiredOutcome", desired);
        result.addProperty("matchCount", matches.size());
        JsonObject mapping = matches.size() == 1
                ? matches.get(0) : new JsonObject();
        boolean unique = matches.size() == 1;
        boolean scheduled = unique
                && exactBoolean(mapping, "scheduledTarget", true);
        boolean scheduledDesired = unique
                && exactBoolean(mapping, "scheduledDesiredOutcome", desired);
        boolean scheduledMatched = unique
                && exactBoolean(mapping, "scheduledOutcomeMatched", true);
        boolean observed = unique
                && exactBoolean(mapping, "observedOutcome", desired);
        boolean effective = unique
                && exactBoolean(mapping, "effectiveOutcome", desired);
        boolean unforced = unique
                && exactBoolean(mapping, "overrideApplied", false);
        result.addProperty("unique", unique);
        result.addProperty("scheduledTarget", scheduled);
        result.addProperty("scheduledDesiredOutcomeMatched",
                scheduledDesired);
        result.addProperty("scheduledOutcomeMatched", scheduledMatched);
        result.addProperty("observedOutcomeMatched", observed);
        result.addProperty("effectiveOutcomeMatched", effective);
        result.addProperty("overrideAbsent", unforced);
        result.addProperty("valid", unique && scheduled && scheduledDesired
                && scheduledMatched && observed && effective && unforced);
        return result;
    }

    private static JsonObject exactOrderedPrefix(JsonObject task,
                                                 JsonObject raw) {
        JsonArray expectedRows = array(task, "expectedBranchPrefix");
        JsonArray mappings = array(raw, "branchMappings");
        int previousCondition = -1;
        int previousPosition = -1;
        boolean conditionOrder = hasArray(task, "expectedBranchPrefix");
        boolean tupleUnique = true;
        boolean mappingUnique = true;
        boolean ordered = true;
        boolean outcomesMatch = true;
        java.util.Set<String> tuples = new java.util.LinkedHashSet<>();
        JsonArray positions = new JsonArray();
        int matched = 0;
        for (JsonElement element : expectedRows) {
            if (!element.isJsonObject()) {
                conditionOrder = false;
                mappingUnique = false;
                continue;
            }
            JsonObject expected = element.getAsJsonObject();
            String site = string(expected, "siteId");
            int occurrence = integer(expected, "occurrence", -1);
            int condition = integer(expected, "conditionIndex", -1);
            boolean exactOutcome = hasBoolean(expected, "outcome");
            boolean outcome = bool(expected, "outcome", false);
            conditionOrder &= !site.isEmpty() && occurrence > 0
                    && condition >= 0 && condition > previousCondition
                    && exactOutcome;
            previousCondition = condition;
            String tuple = site + "\u0000" + occurrence + "\u0000"
                    + condition + "\u0000" + outcome;
            tupleUnique &= tuples.add(tuple);

            List<Integer> matches = new ArrayList<>();
            for (int index = 0; index < mappings.size(); index++) {
                JsonElement candidate = mappings.get(index);
                if (!candidate.isJsonObject()) continue;
                JsonObject mapping = candidate.getAsJsonObject();
                if (site.equals(string(mapping, "siteId"))
                        && occurrence == integer(mapping, "occurrence", -2)) {
                    matches.add(index);
                }
            }
            if (matches.size() != 1) {
                mappingUnique = false;
                continue;
            }
            int position = matches.get(0);
            JsonObject mapping = mappings.get(position).getAsJsonObject();
            ordered &= position > previousPosition;
            previousPosition = position;
            boolean rowOutcome = exactBoolean(mapping, "observedOutcome",
                    outcome) && exactBoolean(mapping, "effectiveOutcome",
                    outcome) && exactBoolean(mapping, "overrideApplied",
                    false);
            outcomesMatch &= rowOutcome;
            matched++;
            positions.add(position);
        }

        String flipSite = string(task, "flipSite");
        int flipOccurrence = integer(task, "flipOccurrence", -1);
        List<Integer> targetPositions = new ArrayList<>();
        for (int index = 0; index < mappings.size(); index++) {
            JsonElement element = mappings.get(index);
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (flipSite.equals(string(mapping, "siteId"))
                    && flipOccurrence == integer(mapping, "occurrence", -2)) {
                targetPositions.add(index);
            }
        }
        boolean targetUnique = targetPositions.size() == 1;
        int targetPosition = targetUnique ? targetPositions.get(0) : -1;
        boolean beforeTarget = targetUnique
                && (expectedRows.size() == 0
                || previousPosition >= 0 && previousPosition < targetPosition);

        JsonObject result = new JsonObject();
        result.addProperty("expectedCount", expectedRows.size());
        result.addProperty("matchedCount", matched);
        result.addProperty("conditionIndicesStrictlyIncreasing",
                conditionOrder);
        result.addProperty("expectedTuplesUnique", tupleUnique);
        result.addProperty("runtimeMappingsUnique", mappingUnique);
        result.addProperty("runtimePositionsStrictlyIncreasing", ordered);
        result.addProperty("runtimeOutcomesExactAndUnforced",
                outcomesMatch);
        result.addProperty("targetMappingUnique", targetUnique);
        result.addProperty("targetPosition", targetPosition);
        result.add("runtimePositions", positions);
        result.addProperty("allPrefixMappingsBeforeTarget", beforeTarget);
        result.addProperty("valid", conditionOrder && tupleUnique
                && mappingUnique && matched == expectedRows.size()
                && ordered && outcomesMatch && beforeTarget);
        return result;
    }

    private static List<JsonObject> matchingActivation(
            List<JsonObject> rows, String activationId) {
        List<JsonObject> result = new ArrayList<>();
        if (activationId.isEmpty()) return result;
        for (JsonObject row : rows) {
            if (activationId.equals(string(row, "activationId"))) {
                result.add(row);
            }
        }
        return result;
    }

    private static JsonObject sourceArtifact(Path path, int rowCount)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("path", path.toAbsolutePath().normalize()
                .toString());
        result.addProperty("sha256", sha256(Files.readAllBytes(path)));
        result.addProperty("rowCount", rowCount);
        return result;
    }

    private static String sha256(byte[] value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value);
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static String shortHash(String value) {
        return sha256((value == null ? "" : value).getBytes(
                StandardCharsets.UTF_8)).substring(0, 16);
    }

    private static JsonObject readObject(Path path) throws IOException {
        JsonElement parsed;
        try {
            parsed = new JsonParser().parse(new String(
                    Files.readAllBytes(path), StandardCharsets.UTF_8));
        } catch (RuntimeException malformed) {
            throw new IOException("Malformed JSON object in " + path,
                    malformed);
        }
        if (!parsed.isJsonObject()) {
            throw new IOException("Expected one JSON object in " + path);
        }
        return parsed.getAsJsonObject();
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
                    parsed = new JsonParser().parse(line);
                } catch (RuntimeException malformed) {
                    throw new IOException("Malformed JSONL row " + number
                            + " in " + path, malformed);
                }
                if (!parsed.isJsonObject()) {
                    throw new IOException("Expected JSON object at row "
                            + number + " in " + path);
                }
                result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static void writeNew(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
    }

    private static void requireFile(Path path, String label)
            throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static void require(JsonArray failures, String code,
                                boolean condition) {
        if (!condition) failures.add(code);
    }

    private static JsonArray array(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static boolean hasArray(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonArray();
    }

    private static JsonObject object(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String member) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static int integer(JsonObject object, String member,
                               int fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean bool(JsonObject object, String member,
                                boolean fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean exactBoolean(JsonObject object, String member,
                                        boolean expected) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                && value.getAsBoolean() == expected;
    }

    private static boolean hasBoolean(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
    }

    private static String canonical(JsonElement value) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return GSON.toJson(value);
        }
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
        JsonObject object = value.getAsJsonObject();
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(object.keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':')
                    .append(canonical(object.get(key)));
        }
        return result.append('}').toString();
    }

    static final class Arguments {
        private Path task;
        private Path activationPlan;
        private Path results;
        private Path summary;
        private Path output;

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + argument);
                }
                String key = argument.substring(2);
                if (!("task".equals(key) || "activation-plan".equals(key)
                        || "results".equals(key) || "summary".equals(key)
                        || "output".equals(key))) {
                    throw new IllegalArgumentException("Unknown --" + key);
                }
                if (values.put(key, argv[++index]) != null) {
                    throw new IllegalArgumentException("Duplicate --" + key);
                }
            }
            Arguments result = new Arguments();
            result.task = path(values, "task");
            result.activationPlan = path(values, "activation-plan");
            result.results = path(values, "results");
            result.summary = path(values, "summary");
            result.output = path(values, "output");
            return result;
        }

        private static Path path(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }
    }
}
