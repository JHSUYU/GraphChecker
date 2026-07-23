package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import soot.SootClass;
import soot.SootFieldRef;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Activation-plan parsing and immutable instrumentation selections.
 *
 * <p>This class deliberately contains no Soot body mutation. It validates the
 * scheduler-owned plan and exposes only the exact sites that the pipeline may
 * instrument, keeping fail-closed plan semantics separate from bytecode
 * rewriting.</p>
 */
final class ConcolicInstrumentationSelections {
    private ConcolicInstrumentationSelections() {
    }

    static ConcolicMaterializationSelection
    materializationSelectionFromEnvironment() {
        String planValue = activationPlanValue();
        if (planValue.isEmpty()) {
            return new ConcolicMaterializationSelection();
        }
        try {
            return ConcolicMaterializationSelection.from(
                    Paths.get(planValue), selectedActivationValue());
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic materializations from "
                            + planValue, exception);
        }
    }

    static ConcolicOutputCaptureSelection
    outputCaptureSelectionFromEnvironment() {
        String planValue = activationPlanValue();
        if (planValue.isEmpty()) {
            return new ConcolicOutputCaptureSelection();
        }
        try {
            return ConcolicOutputCaptureSelection.from(
                    Paths.get(planValue), selectedActivationValue());
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic output captures from "
                            + planValue, exception);
        }
    }

    private static String activationPlanValue() {
        return stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_PLAN")));
    }

    private static String selectedActivationValue() {
        return stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.activation.id"),
                System.getenv("CAUSYNTH_CONCOLIC_ACTIVATION_ID")));
    }

    static Set<String> readRuntimeSelectedRoots(Path activationPlan,
                                                String selectedActivation)
            throws IOException {
        if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
            throw new IOException("Activation plan not found: " + activationPlan);
        }
        String selected = stringValue(firstNonBlank(selectedActivation));
        Set<String> roots = new LinkedHashSet<>();
        try (BufferedReader reader = Files.newBufferedReader(activationPlan,
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
                JsonObject row = parsed.getAsJsonObject();
                String activationId = jsonString(row, "activationId");
                if (!selected.isEmpty()
                        && "ALL".equals(jsonString(row,
                        "activationSelectionRequired"))
                        && selected.equals(activationId)) {
                    throw new IOException("Activation " + selected
                            + " belongs to a reachability bundle that "
                            + "requires ALL plan rows");
                }
                if (!selected.isEmpty() && !selected.equals(activationId)) {
                    continue;
                }
                if (!strictJsonBooleanEquals(row, "replayable", true)
                        || !strictJsonBooleanEquals(row,
                        "schedulerReady", true)) {
                    continue;
                }
                String root = jsonString(row, "rootMethod");
                if (!root.isEmpty()) {
                    roots.add(root);
                }
            }
        }
        return roots;
    }

    /**
     * Returns whether one exact scheduler-selected activation carries all of
     * the evidence needed to analyze only its bounded requested-output
     * closure.  This is deliberately stricter than root selection: older
     * discovery plans and branch-target plans must continue to require global
     * symbolic-region coverage.
     */
    static boolean selectedBoundedOutputClosureCoverageReady(
            Path activationPlan, String selectedActivation)
            throws IOException {
        if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
            return false;
        }
        String selected = stringValue(firstNonBlank(selectedActivation));
        if (selected.isEmpty()) {
            return false;
        }

        JsonObject selectedRow = null;
        int selectedRowCount = 0;
        try (BufferedReader reader = Files.newBufferedReader(activationPlan,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonElement parsed;
                try {
                    parsed = JsonParser.parseString(line);
                } catch (RuntimeException malformed) {
                    return false;
                }
                if (!parsed.isJsonObject()) {
                    return false;
                }
                JsonObject row = parsed.getAsJsonObject();
                if (!selected.equals(jsonString(row, "activationId"))) {
                    continue;
                }
                selectedRowCount++;
                selectedRow = row;
            }
        }
        if (selectedRowCount != 1 || selectedRow == null) {
            return false;
        }
        return boundedOutputClosureRowReady(selectedRow, selected);
    }

    private static boolean boundedOutputClosureRowReady(JsonObject row,
                                                        String selected) {
        JsonElement captureGoalElement = row.get("captureGoal");
        if (captureGoalElement == null || !captureGoalElement.isJsonObject()) {
            return false;
        }
        JsonObject captureGoal = captureGoalElement.getAsJsonObject();
        if (!"OUTPUT_CLOSURE".equals(jsonString(captureGoal, "kind"))
                || !"BOUNDED_OUTPUT_RELEVANT_PATHS".equals(
                jsonString(captureGoal, "scope"))
                || "TRANSITION_DISCOVERY_ONLY".equals(
                jsonString(captureGoal, "purpose"))) {
            return false;
        }

        String scheduleId = jsonString(row, "scheduleId");
        if (!selected.equals(jsonString(row, "activationId"))
                || !selected.equals(jsonString(row,
                "activationSelectionRequired"))
                || !selected.equals(jsonString(row,
                "activationBundleRootActivationId"))
                || scheduleId.isEmpty()
                || !scheduleId.equals(jsonString(row,
                "activationBundleScheduleId"))
                || !strictJsonIntEquals(row, "activationBundleSize", 1)
                || !strictJsonIntEquals(row, "activationBundleIndex", 0)
                || !"PRIMARY".equals(jsonString(row,
                "activationBundleMemberRole"))) {
            return false;
        }

        if (!strictJsonBooleanEquals(row, "replayable", true)
                || !strictJsonBooleanEquals(row, "boundaryReady", true)
                || !strictJsonBooleanEquals(row, "schedulerReady", true)
                || !strictJsonBooleanEquals(row,
                "runtimePathEvidenceComplete", true)
                || !strictJsonBooleanEquals(row,
                "requestedOutputCaptureComplete", true)
                || !strictJsonBooleanEquals(row,
                "pathSignatureTruncated", false)
                || !strictJsonBooleanEquals(row,
                "containedCallTreeTruncated", false)
                || !emptyJsonArray(row, "runtimeGaps")
                || row.has("transitionDiscovery")
                || row.has("transitionOutputRefinement")) {
            return false;
        }
        boolean seedReplay = "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY"
                .equals(jsonString(row, "replayMode"))
                && "CAPTURE_OUTPUT_PATH".equals(jsonString(row,
                        "executionPhase"))
                && absentOrEmptyJsonArray(row, "modelAssignments");
        boolean solverFlipReplay = solverOutputPathFlipReady(row, selected);
        if (!seedReplay && !solverFlipReplay) {
            return false;
        }

        JsonElement outputElement = row.get("requestedOutput");
        JsonElement sliceElement = row.get("requestedOutputSlice");
        if (outputElement == null || !outputElement.isJsonObject()
                || sliceElement == null || !sliceElement.isJsonObject()) {
            return false;
        }
        JsonObject output = outputElement.getAsJsonObject();
        JsonObject slice = sliceElement.getAsJsonObject();
        String outputPort = jsonString(output, "portId");
        String outputCell = jsonString(output, "cell");
        if (outputPort.isEmpty() || outputCell.isEmpty()
                || !outputPort.equals(jsonString(slice, "outputPort"))
                || !outputCell.equals(jsonString(slice, "outputCell"))
                || !strictJsonBooleanEquals(slice, "complete", true)
                || !strictJsonBooleanEquals(slice,
                "structuralComplete", true)
                || !strictJsonBooleanEquals(slice, "runtimeRefined", true)
                || !strictJsonBooleanEquals(slice,
                "runtimeRefinementComplete", true)
                || jsonString(slice, "runtimeRefinementAuthority").isEmpty()
                || !strictJsonBooleanEquals(slice,
                "unresolvedInputProvenanceComplete", true)
                || !strictJsonBooleanEquals(slice,
                "captureBindingsComplete", true)
                || !strictJsonBooleanEquals(slice,
                "methodBudgetTruncated", false)
                || !strictJsonBooleanEquals(slice,
                "causalCellBudgetTruncated", false)
                || !strictJsonBooleanEquals(slice,
                "regionTruncated", false)
                || !strictJsonBooleanEquals(slice, "truncated", false)) {
            return false;
        }
        if (!emptyJsonArray(slice, "unresolvedInputs")
                || !emptyJsonArray(slice, "unresolvedInputDetails")
                || !emptyJsonArray(slice, "truncationReasons")
                || !emptyJsonArray(slice, "captureBindingIssues")) {
            return false;
        }

        JsonElement outputs = row.get("outputs");
        int matchingOutputs = 0;
        if (outputs == null || !outputs.isJsonArray()) {
            return false;
        }
        for (JsonElement element : outputs.getAsJsonArray()) {
            if (element.isJsonObject()
                    && outputPort.equals(jsonString(element.getAsJsonObject(),
                    "symbol"))
                    && outputCell.equals(jsonString(element.getAsJsonObject(),
                    "cell"))) {
                matchingOutputs++;
            }
        }
        if (matchingOutputs != 1) {
            return false;
        }

        JsonElement captures = row.get("requestedOutputCapture");
        if (captures == null || !captures.isJsonArray()) {
            return false;
        }
        JsonElement captureRequiredElement = row.get(
                "requestedOutputCaptureRequired");
        if (captureRequiredElement == null
                || !captureRequiredElement.isJsonPrimitive()
                || !captureRequiredElement.getAsJsonPrimitive().isBoolean()) {
            return false;
        }
        boolean captureRequired = captureRequiredElement.getAsBoolean();
        if (captureRequired && captures.getAsJsonArray().size() == 0) {
            return false;
        }
        if (!captureRequired && captures.getAsJsonArray().size() != 0) {
            return false;
        }
        for (JsonElement element : captures.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || !outputPort.equals(jsonString(element.getAsJsonObject(),
                    "outputPort"))
                    || !outputCell.equals(jsonString(element.getAsJsonObject(),
                    "outputCell"))
                    || jsonString(element.getAsJsonObject(),
                    "captureBindingId").isEmpty()) {
                return false;
            }
        }
        if (!strictJsonBooleanEquals(slice,
                "captureBindingsRequired", captureRequired)) {
            return false;
        }
        if (!captureRequired
                && !heapEffectCaptureDischargeReady(row, slice, outputPort,
                outputCell)) {
            return false;
        }
        return true;
    }

    /**
     * Admits the one non-seed replay shape that can soundly reuse a bounded
     * requested-output closure: an input-model-only Z3 path flip.  The model
     * may change concrete program inputs at their real definitions, but the
     * branch remains an observation target and no edge is forced.
     */
    private static boolean solverOutputPathFlipReady(JsonObject row,
                                                     String selected) {
        if (!selected.startsWith("ACT.PATH.")
                || !"RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY".equals(
                strictJsonString(row, "replayMode"))
                || !"REPLAY_OUTPUT_PATH_FLIP".equals(
                strictJsonString(row, "executionPhase"))) {
            return false;
        }

        String queryKey = strictJsonString(row, "pathQueryKey");
        String pathId = shortSha256(queryKey, 16);
        if (!queryKey.matches("[0-9a-f]{64}")
                || !selected.equals("ACT.PATH." + pathId)
                || !("SCHEDULE.PATH." + pathId).equals(
                strictJsonString(row, "scheduleId"))) {
            return false;
        }

        JsonElement assignmentsElement = row.get("modelAssignments");
        if (assignmentsElement == null || !assignmentsElement.isJsonArray()
                || assignmentsElement.getAsJsonArray().size() == 0) {
            return false;
        }
        Set<String> engineSymbols = new LinkedHashSet<>();
        Set<String> solverSymbols = new LinkedHashSet<>();
        for (JsonElement element : assignmentsElement.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || !z3PathFlipAssignmentReady(element.getAsJsonObject(),
                    engineSymbols, solverSymbols)) {
                return false;
            }
        }

        JsonElement contractElement = row.get("replayContract");
        if (contractElement == null || !contractElement.isJsonObject()) {
            return false;
        }
        try {
            BranchReplayContract.fromJson(
                    contractElement.getAsJsonObject());
        } catch (RuntimeException malformed) {
            return false;
        }
        return true;
    }

    private static boolean z3PathFlipAssignmentReady(
            JsonObject assignment, Set<String> engineSymbols,
            Set<String> solverSymbols) {
        String engineSymbol = strictJsonString(assignment,
                "engineSymbol");
        String solverSymbol = strictJsonString(assignment,
                "solverSymbol");
        String inputSymbol = strictJsonString(assignment,
                "inputSymbol");
        String valueType = strictJsonString(assignment, "valueType");
        JsonElement value = assignment.get("value");
        JsonElement targetElement = assignment.get("target");
        if (engineSymbol.isEmpty() || solverSymbol.isEmpty()
                || inputSymbol.isEmpty()
                || !("BOOL".equals(valueType) || "INT".equals(valueType)
                || "REAL".equals(valueType)
                || "STRING".equals(valueType))
                || value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()
                || !"Z3_PATH_FLIP_MODEL".equals(strictJsonString(
                assignment, "authority"))
                || !strictJsonBooleanEquals(assignment,
                "materializeAtRealDefinition", true)
                || targetElement == null || !targetElement.isJsonObject()
                || !inputSymbol.equals(strictJsonString(
                targetElement.getAsJsonObject(), "symbol"))
                || !engineSymbols.add(engineSymbol)
                || !solverSymbols.add(solverSymbol)) {
            return false;
        }
        String modelValue = value.getAsString();
        return !"BOOL".equals(valueType)
                || "true".equals(modelValue) || "false".equals(modelValue);
    }

    private static String shortSha256(String value, int length) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value.getBytes(
                    StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.substring(0, length);
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static boolean heapEffectCaptureDischargeReady(
            JsonObject row, JsonObject slice, String outputPort,
            String outputCell) {
        String inputPort = jsonString(slice, "captureDischargeInputPort");
        if (!strictJsonBooleanEquals(slice,
                "captureDischargedByHeapEffectTransformer", true)
                || !"HEAP_EFFECT_STATE_TRANSFORMER".equals(jsonString(slice,
                "captureDischargeAuthority"))
                || inputPort.isEmpty()
                || !outputPort.equals(jsonString(slice,
                "captureDischargeOutputPort"))
                || !outputCell.equals(jsonString(slice,
                "captureDischargeOutputCell"))
                || !strictJsonBooleanEquals(slice,
                "requestedStateTransformerContractApplicable", true)
                || !strictJsonBooleanEquals(slice,
                "requestedStateTransformerContractComplete", true)
                || !strictJsonIntEquals(slice,
                "requestedStateTransformerContractVersion", 1)
                || jsonString(slice,
                "requestedStateTransformerContractAuthority").isEmpty()
                || !outputPort.equals(jsonString(slice,
                "requestedStateTransformerContractOutputPort"))
                || !outputCell.equals(jsonString(slice,
                "requestedStateTransformerContractOutputCell"))
                || !emptyJsonArray(slice,
                "requestedStateTransformerContractIssues")) {
            return false;
        }

        JsonElement obligations = slice.get(
                "requestedStateTransformerObligations");
        int obligationCount = strictJsonInt(slice,
                "requestedStateTransformerObligationCount", -1);
        if (obligations == null || !obligations.isJsonArray()
                || obligationCount <= 0
                || obligations.getAsJsonArray().size() != obligationCount) {
            return false;
        }
        for (JsonElement element : obligations.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || !outputCell.equals(jsonString(element.getAsJsonObject(),
                    "targetCell"))
                    || jsonString(element.getAsJsonObject(), "siteId").isEmpty()
                    || jsonString(element.getAsJsonObject(), "method").isEmpty()
                    || jsonString(element.getAsJsonObject(),
                    "authority").isEmpty()) {
                return false;
            }
        }

        JsonElement bindings = row.get("heapStateBindings");
        int matchingBindings = 0;
        if (bindings == null || !bindings.isJsonArray()) {
            return false;
        }
        for (JsonElement element : bindings.getAsJsonArray()) {
            if (element.isJsonObject()
                    && inputPort.equals(jsonString(element.getAsJsonObject(),
                    "inputPort"))
                    && outputPort.equals(jsonString(element.getAsJsonObject(),
                    "outputPort"))
                    && outputCell.equals(jsonString(element.getAsJsonObject(),
                    "cell"))) {
                matchingBindings++;
            }
        }
        return matchingBindings == 1;
    }

    private static boolean strictJsonBooleanEquals(JsonObject object,
                                                   String field,
                                                   boolean expected) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                && value.getAsBoolean() == expected;
    }

    private static boolean strictJsonBooleanPresent(JsonObject object,
                                                    String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
    }

    private static String strictJsonString(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    private static boolean strictJsonIntEquals(JsonObject object,
                                               String field, int expected) {
        return strictJsonInt(object, field, Integer.MIN_VALUE) == expected;
    }

    private static int strictJsonInt(JsonObject object, String field,
                                     int fallback) {
        JsonElement value = object.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            return fallback;
        }
        try {
            String encoded = value.getAsString();
            if (!encoded.matches("-?(0|[1-9][0-9]*)")) {
                return fallback;
            }
            return Integer.parseInt(encoded);
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    private static boolean emptyJsonArray(JsonObject object, String field) {
        JsonElement value = object.get(field);
        return value != null && value.isJsonArray()
                && value.getAsJsonArray().size() == 0;
    }

    private static boolean absentOrEmptyJsonArray(JsonObject object,
                                                  String field) {
        JsonElement value = object.get(field);
        return value == null || (value.isJsonArray()
                && value.getAsJsonArray().size() == 0);
    }

    static final class ConcolicBranchSelection {
        private final Map<String, Set<Integer>> unitsByMethod =
                new LinkedHashMap<>();

        static ConcolicBranchSelection from(
                List<Map<String, Object>> regions) {
            ConcolicBranchSelection result = new ConcolicBranchSelection();
            for (Map<String, Object> region : regions) {
                Object value = region.get("branchPolicies");
                if (!(value instanceof Collection)) {
                    continue;
                }
                for (Object item : (Collection<?>) value) {
                    if (!(item instanceof Map)) {
                        continue;
                    }
                    Map<?, ?> policy = (Map<?, ?>) item;
                    String method = stringValue(policy.get("method"));
                    int unit = intValue(policy.get("unitIndex"), -1);
                    if (!method.isEmpty() && unit >= 0) {
                        result.unitsByMethod.computeIfAbsent(method,
                                ignored -> new LinkedHashSet<>()).add(unit);
                    }
                }
            }
            return result;
        }

        Set<String> methods() {
            return unitsByMethod.keySet();
        }

        Set<Integer> units(String method) {
            Set<Integer> units = unitsByMethod.get(method);
            return units == null ? Collections.emptySet() : units;
        }
    }

    /**
     * Resolves the concrete field selected for a heap materialization hook.
     * Runtime field evidence is authoritative when available.  A cell such as
     * {@code <Owner: T method()>.return#field:x} names a projection from a
     * method result; {@code Owner} does not declare {@code x} and must not be
     * reused as the Soot field owner.
     */
    static String[] resolveConcolicFieldTarget(JsonObject action) {
        String cell = jsonString(action, "cell");
        String owner = jsonString(action, "accessOwnerClass");
        String name = jsonString(action, "accessField");
        JsonElement path = action.get("fieldPath");
        if (name.isEmpty() && path != null && path.isJsonArray()
                && path.getAsJsonArray().size() > 0) {
            name = path.getAsJsonArray().get(0).getAsString();
        }

        Matcher observed = ConcolicMaterializationSelection.FIELD.matcher(
                jsonString(action, "field"));
        if (observed.matches() && !isMethodMember(observed.group(3))) {
            owner = firstNonBlank(owner, observed.group(1));
            name = firstNonBlank(name, observed.group(3));
        }

        Matcher declared = ConcolicMaterializationSelection.FIELD.matcher(cell);
        if (declared.matches() && !isMethodMember(declared.group(3))) {
            owner = firstNonBlank(owner, declared.group(1));
            name = firstNonBlank(name, declared.group(3));
        } else {
            name = firstNonBlank(name,
                    ConcolicMaterializationSelection.projectedField(cell),
                    ConcolicMaterializationSelection.projectedField(
                            jsonString(action, "field")));
        }
        String normalizedOwner = firstNonBlank(owner);
        String normalizedName = firstNonBlank(name);
        return new String[]{normalizedOwner == null ? "" : normalizedOwner,
                normalizedName == null ? "" : normalizedName};
    }

    private static boolean isMethodMember(String member) {
        return member != null && member.indexOf('(') >= 0;
    }

    /**
     * The small set of concrete Jimple values that a scheduled activation
     * asks Soot to expose to the VM.  This is intentionally activation-plan
     * driven: the static region supplies candidates, while the runtime
     * instance decides which concrete local/heap owner is authoritative.
     */
    static final class ConcolicMaterializationSelection {
        private static final Pattern LOCAL = Pattern.compile(
                "^(<.+>)::([^#]+)(?:#.*)?$");
        static final Pattern FIELD = Pattern.compile(
                "^<([^:]+):\\s+(.+)\\s+([^\\s>]+)>(?:#field:([^#]+))?.*$");
        static final String CONSUMED_SITE_AUTHORITY =
                "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                        + "OWNER_WITHIN_REGION_INSTANCE_V1";
        static final String CONSUMED_OCCURRENCE_AUTHORITY =
                "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1";
        static final String DIRECT_ROOT_AUTHORITY =
                "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1";
        static final String ARGUMENT_ROOT_AUTHORITY =
                "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        static final String RECEIVER_ROOT_AUTHORITY =
                "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        static final String LOCAL_ROOT_AUTHORITY =
                "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY";
        static final String ACCESSOR_CALLSITE_AUTHORITY =
                "STATIC_UNIQUE_EXACT_DECLARED_FIELD_ACCESSOR_CALLSITE_V1";
        static final String ACCESSOR_IMPLEMENTATION_AUTHORITY =
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY";
        static final Set<String> EXACT_ACCESS_FIELD_AUTHORITIES =
                Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                        "RUNTIME_FIELD_ACCESS_DECLARATION",
                        "STATIC_CANONICAL_DECLARED_FIELD",
                        "STATIC_EXACT_CONTAINER_ELEMENT_FIELD_DECLARATION",
                        "STATIC_EXACT_CONTAINER_INPUT_FIELD_DECLARATION")));
        static final String CONTAINER_INPUT_OBSERVATION_MODE =
                "CONTAINER_INPUT_OBSERVATION";
        static final String MAP_STATE_INPUT_OBSERVATION_MODE =
                "MAP_STATE_INPUT_OBSERVATION";
        static final String FIRST_CONTAINER_OBSERVATION_AUTHORITY =
                "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1";

        private final Map<String, Map<String, Set<Integer>>> localsByMethod =
                new LinkedHashMap<>();
        private final List<FieldTarget> fields = new ArrayList<>();
        private final Map<String, AccessorCallTarget> accessorCallsBySite =
                new LinkedHashMap<>();
        private final List<String> unsupported = new ArrayList<>();

        static ConcolicMaterializationSelection from(
                Path activationPlan, String selectedActivation)
                throws IOException {
            if (activationPlan == null || !Files.isRegularFile(activationPlan)) {
                throw new IOException("Activation plan not found: "
                        + activationPlan);
            }
            ConcolicMaterializationSelection result =
                    new ConcolicMaterializationSelection();
            String selected = stringValue(firstNonBlank(selectedActivation));
            try (BufferedReader reader = Files.newBufferedReader(activationPlan,
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
                    JsonObject row = parsed.getAsJsonObject();
                    if (!selected.isEmpty()
                            && !selected.equals(jsonString(row,
                            "activationId"))) {
                        continue;
                    }
                    if (!strictJsonBooleanEquals(row, "replayable", true)
                            || !strictJsonBooleanEquals(row,
                            "schedulerReady", true)) {
                        continue;
                    }
                    String activationId = jsonString(row, "activationId");
                    JsonElement actions = row.get("materializations");
                    if (actions == null || !actions.isJsonArray()) {
                        throw new IOException("Replayable activation "
                                + activationId + " requires materializations "
                                + "to be a JSON array");
                    }
                    int actionIndex = 0;
                    for (JsonElement element : actions.getAsJsonArray()) {
                        if (!element.isJsonObject()) {
                            throw new IOException("Replayable activation "
                                    + activationId + " materializations["
                                    + actionIndex + "] must be a JSON object");
                        }
                        result.add(element.getAsJsonObject());
                        actionIndex++;
                    }
                }
            }
            if (!result.unsupported.isEmpty()) {
                throw new IOException("Unsupported concolic materialization: "
                        + result.unsupported);
            }
            return result;
        }

        void add(JsonObject action) {
            addAccessorCallTarget(action);
            String mode = jsonString(action, "bindingMode");
            String cell = jsonString(action, "cell");
            if ("LOCAL_DEFINITION".equals(mode)) {
                String method = jsonString(action, "method");
                String local = jsonString(action, "local");
                Matcher matcher = LOCAL.matcher(cell);
                if (matcher.matches()) {
                    method = firstNonBlank(method, matcher.group(1));
                    local = firstNonBlank(local, matcher.group(2));
                }
                if (!method.isEmpty() && !local.isEmpty()) {
                    Map<String, Set<Integer>> locals =
                            localsByMethod.computeIfAbsent(method,
                                    ignored -> new LinkedHashMap<>());
                    Set<Integer> sites = locals.computeIfAbsent(local,
                            ignored -> new LinkedHashSet<>());
                    JsonElement definitions = action.get("definitionSites");
                    if (definitions != null && definitions.isJsonArray()) {
                        for (JsonElement element
                                : definitions.getAsJsonArray()) {
                            if (element.isJsonObject()) {
                                int site = intJson(element.getAsJsonObject(),
                                        "unitIndex", -1);
                                if (site >= 0) {
                                    sites.add(site);
                                }
                            }
                        }
                    }
                }
                if (declaresArrayValue(action)
                        && !exactArrayFieldPath(action).isEmpty()) {
                    addExactArrayLeafTarget(action);
                }
                return;
            }
            String location = jsonString(action, "location");
            if (MAP_STATE_INPUT_OBSERVATION_MODE.equals(mode)) {
                if (!jsonBoolean(action, "mapStateObservationOnly", false)
                        || jsonBoolean(action, "modelControllable", true)
                        || !FIRST_CONTAINER_OBSERVATION_AUTHORITY.equals(
                        jsonString(action,
                                "containerObservationAuthority"))
                        || !declaresMapValue(action)
                        || !jsonString(action, "cell").equals(jsonString(
                        action, "mapStateInputCell"))
                        || !jsonString(action, "cell").equals(jsonString(
                        action, "mapStateRequestedOutputCell"))) {
                    unsupported.add("MAP_STATE_INPUT_OBSERVATION_REQUIRES_"
                            + "EXACT_BOUNDED_MAP_AUTHORITY:"
                            + jsonString(action, "symbol"));
                    return;
                }
                String[] target = resolveConcolicFieldTarget(action);
                if (target[0].isEmpty() || target[1].isEmpty()) {
                    unsupported.add("MAP_STATE_INPUT_OBSERVATION_REQUIRES_"
                            + "EXACT_DECLARED_FIELD:"
                            + jsonString(action, "symbol"));
                    return;
                }
                // Keep the ordinary getfield split.  Runtime consumes the
                // exact field value as an identity/snapshot observation and
                // deliberately does not invoke VM reference symbolization.
                fields.add(new FieldTarget(target[0], target[1]));
                return;
            }
            if (CONTAINER_INPUT_OBSERVATION_MODE.equals(mode)) {
                if (!jsonBoolean(action, "arrayFieldObservationOnly", false)
                        || !FIRST_CONTAINER_OBSERVATION_AUTHORITY.equals(
                        jsonString(action,
                                "containerObservationAuthority"))
                        || !declaresArrayValue(action)) {
                    unsupported.add("CONTAINER_INPUT_OBSERVATION_REQUIRES_"
                            + "EXPLICIT_ARRAY_AUTHORITY:"
                            + jsonString(action, "symbol"));
                    return;
                }
                String[] target = resolveConcolicFieldTarget(action);
                if (target[0].isEmpty() || target[1].isEmpty()) {
                    unsupported.add("CONTAINER_INPUT_OBSERVATION_REQUIRES_"
                            + "EXACT_DECLARED_FIELD:"
                            + jsonString(action, "symbol"));
                    return;
                }
                // Observation-only arrays deliberately use the declaration
                // as a field family.  Every concrete read is joined to its
                // actual post-getfield value by the existing split hook; the
                // runtime's explicit first-instance authority selects the
                // bounded container and treats later reads as aliases or
                // ignored outer-loop instances.
                fields.add(new FieldTarget(target[0], target[1]));
                return;
            }
            if (declaresArrayValue(action)) {
                List<String> fieldPath = exactArrayFieldPath(action);
                boolean fieldBacked = !fieldPath.isEmpty()
                        || "FIELD_ACCESS".equals(mode)
                        || "FIELD".equals(location)
                        || "HEAP_OBJECT_FIELD".equals(location)
                        || "RECEIVER_FIELD".equals(location)
                        || "ARGUMENT_FIELD".equals(location)
                        || "ARGUMENT_FIELD_PATH".equals(location);
                if (fieldBacked) {
                    addExactArrayLeafTarget(action);
                }
                // A field-backed ARRAY_VALUE action must be hooked at the
                // actual leaf getfield, never at an earlier object-valued
                // component of a nested path.  Direct array arguments and
                // call returns have no getfield and remain handled by their
                // existing boundary hooks.
                return;
            }
            if (!"FIELD_ACCESS".equals(mode)
                    && !"HEAP_OBJECT_FIELD".equals(location)) {
                return;
            }
            String[] target = resolveConcolicFieldTarget(action);
            if (!target[1].isEmpty()) {
                fields.add(new FieldTarget(target[0], target[1]));
            }
        }

        void addAccessorCallTarget(JsonObject action) {
            String caller = jsonString(action, "accessorCallerMethod");
            String site = jsonString(action, "accessorCallSiteId");
            int unitIndex = intJson(action, "accessorCallUnitIndex", -1);
            String callee = jsonString(action, "accessorDeclaredCallee");
            String authority = jsonString(action,
                    "accessorCallSiteAuthority");
            String implementation = jsonString(action,
                    "accessorImplementationMethod");
            String implementationAuthority = jsonString(action,
                    "accessorImplementationAuthority");
            boolean constrained = !caller.isEmpty() || !site.isEmpty()
                    || unitIndex >= 0 || !callee.isEmpty()
                    || !authority.isEmpty() || !implementation.isEmpty()
                    || !implementationAuthority.isEmpty();
            if (!constrained) return;
            if (caller.isEmpty() || unitIndex < 0 || callee.isEmpty()
                    || !site.equals(caller + "#u" + unitIndex)
                    || !ACCESSOR_CALLSITE_AUTHORITY.equals(authority)
                    || implementation.isEmpty()
                    || !ACCESSOR_IMPLEMENTATION_AUTHORITY.equals(
                    implementationAuthority)) {
                unsupported.add("ACCESSOR_CALL_CONTEXT_REQUIRES_EXACT_"
                        + "CALLSITE_METADATA:" + jsonString(action,
                        "symbol"));
                return;
            }

            String fieldSignature = jsonString(action,
                    "accessFieldSignature");
            String fieldOwner = jsonString(action, "accessOwnerClass");
            String fieldName = jsonString(action, "accessField");
            String fieldType = jsonString(action, "accessFieldType");
            String fieldAuthority = jsonString(action,
                    "accessFieldAuthority");
            Matcher declaredField = FIELD.matcher(fieldSignature);
            if (!declaredField.matches()
                    || isMethodMember(declaredField.group(3))
                    || fieldOwner.isEmpty()
                    || !fieldOwner.equals(declaredField.group(1))
                    || fieldName.isEmpty()
                    || !fieldName.equals(declaredField.group(3))
                    || !fieldType.isEmpty()
                    && !fieldType.equals(declaredField.group(2))
                    || !EXACT_ACCESS_FIELD_AUTHORITIES.contains(
                    fieldAuthority)) {
                unsupported.add("ACCESSOR_CALL_CONTEXT_REQUIRES_EXACT_"
                        + "DECLARED_FIELD_METADATA:" + jsonString(action,
                        "symbol"));
                return;
            }
            AccessorCallTarget target = new AccessorCallTarget(caller,
                    unitIndex, site, callee, implementation, fieldSignature,
                    fieldOwner, fieldName, fieldAuthority);
            AccessorCallTarget previous = accessorCallsBySite.get(
                    target.siteIdentity());
            if (previous != null && !previous.sameMaterialization(target)) {
                unsupported.add("ACCESSOR_CALL_CONTEXT_AMBIGUOUS_EXACT_"
                        + "MATERIALIZATION_METADATA:" + site);
                return;
            }
            if (previous == null) {
                accessorCallsBySite.put(target.siteIdentity(), target);
            }
        }

        void addExactArrayLeafTarget(JsonObject action) {
            FieldTarget leaf = exactArrayLeafTarget(action);
            if (leaf == null) {
                unsupported.add("ARRAY_VALUE_FIELD_REQUIRES_EXACT_LEAF_"
                        + "DECLARATION_AND_CONSUMED_SITE:"
                        + jsonString(action, "symbol"));
            } else {
                fields.add(leaf);
            }
        }

        static boolean declaresArrayValue(JsonObject action) {
            if (looksLikeArrayType(firstNonBlank(
                    jsonString(action, "javaType"),
                    jsonString(action, "inputJavaType")))) {
                return true;
            }
            for (String field : Arrays.asList(
                    jsonString(action, "leafFieldSignature"),
                    jsonString(action, "field"),
                    jsonString(action, "cell"))) {
                Matcher matcher = FIELD.matcher(field);
                if (matcher.matches() && looksLikeArrayType(matcher.group(2))) {
                    return true;
                }
            }
            JsonElement declarations = action.get(
                    "fieldPathLeafDeclarations");
            if (declarations != null && declarations.isJsonArray()) {
                for (JsonElement element : declarations.getAsJsonArray()) {
                    if (!element.isJsonObject()) continue;
                    Matcher matcher = FIELD.matcher(jsonString(
                            element.getAsJsonObject(), "fieldSignature"));
                    if (matcher.matches()
                            && looksLikeArrayType(matcher.group(2))) {
                        return true;
                    }
                }
            }
            return false;
        }

        static boolean declaresMapValue(JsonObject action) {
            for (String type : Arrays.asList(
                    jsonString(action, "javaType"),
                    jsonString(action, "inputJavaType"),
                    jsonString(action, "accessFieldType"))) {
                if (looksLikeMapType(type)) {
                    return true;
                }
            }
            for (String field : Arrays.asList(
                    jsonString(action, "leafFieldSignature"),
                    jsonString(action, "accessFieldSignature"),
                    jsonString(action, "field"),
                    jsonString(action, "cell"))) {
                Matcher matcher = FIELD.matcher(field);
                if (matcher.matches() && looksLikeMapType(matcher.group(2))) {
                    return true;
                }
            }
            return false;
        }

        static boolean looksLikeMapType(String type) {
            String candidate = stringValue(firstNonBlank(type)).trim();
            if (candidate.startsWith("L") && candidate.endsWith(";")) {
                candidate = candidate.substring(1, candidate.length() - 1)
                        .replace('/', '.');
            }
            if (candidate.isEmpty() || candidate.startsWith("[")
                    || candidate.endsWith("[]")) {
                return false;
            }
            try {
                ClassLoader loader = Thread.currentThread()
                        .getContextClassLoader();
                Class<?> declared = Class.forName(candidate, false,
                        loader == null ? ConcolicInstrumentationSelections.class
                                .getClassLoader() : loader);
                return Map.class.isAssignableFrom(declared);
            } catch (Throwable ignored) {
                return "java.util.Map".equals(candidate);
            }
        }

        static FieldTarget exactArrayLeafTarget(JsonObject action) {
            String consumedMethod = jsonString(action,
                    "consumedFieldMethod");
            int consumedUnit = intJson(action, "consumedFieldUnitIndex", -1);
            String consumedSite = jsonString(action, "consumedFieldSiteId");
            String consumedAuthority = jsonString(action,
                    "consumedFieldSiteAuthority");
            if (!jsonBoolean(action, "consumedFieldBindingComplete", false)
                    || intJson(action, "consumedFieldOccurrence", -1) != 1
                    || !CONSUMED_OCCURRENCE_AUTHORITY.equals(jsonString(
                    action, "consumedFieldOccurrenceAuthority"))
                    || consumedMethod.isEmpty() || consumedUnit < 0
                    || !consumedSite.equals(consumedMethod + "#u"
                    + consumedUnit)
                    || !CONSUMED_SITE_AUTHORITY.equals(consumedAuthority)) {
                return null;
            }
            List<String> exactPath = exactArrayFieldPath(action);
            String rootAuthority = jsonString(action,
                    "consumedFieldRootAuthority");
            String location = jsonString(action, "location");
            String bindingMode = jsonString(action, "bindingMode");
            boolean argumentRoot = "ARGUMENT_FIELD".equals(location)
                    || "ARGUMENT_FIELD_PATH".equals(location);
            boolean receiverRoot = "RECEIVER_FIELD".equals(location);
            boolean localRoot = "LOCAL_DEFINITION".equals(bindingMode);
            boolean fieldAccessRoot = !argumentRoot && !receiverRoot
                    && !localRoot && ("FIELD_ACCESS".equals(bindingMode)
                    || "FIELD".equals(location)
                    || "HEAP_OBJECT_FIELD".equals(location));
            // A generic HEAP_OBJECT_FIELD can still be proven to be rooted at
            // the region receiver by runtime object identity.  The Runtime
            // registers receiver-authority actions at enterRegion regardless
            // of their observational location.  A direct field root has no
            // such entry identity and is intentionally limited to one leaf.
            boolean rootAuthorityMatches = argumentRoot
                    ? ARGUMENT_ROOT_AUTHORITY.equals(rootAuthority)
                    : receiverRoot
                    ? RECEIVER_ROOT_AUTHORITY.equals(rootAuthority)
                    : localRoot
                    ? LOCAL_ROOT_AUTHORITY.equals(rootAuthority)
                    : fieldAccessRoot && (RECEIVER_ROOT_AUTHORITY.equals(
                    rootAuthority) || exactPath.size() == 1
                    && DIRECT_ROOT_AUTHORITY.equals(rootAuthority));
            boolean rootBindingComplete = !argumentRoot
                    || intJson(action, "index", -1) >= 0;
            if (localRoot) {
                rootBindingComplete = hasOneExactLocalDefinition(action);
            }
            if (exactPath.isEmpty() || !rootAuthorityMatches
                    || !rootBindingComplete) {
                return null;
            }
            String expectedLeaf = jsonString(action, "leafField");
            if (!exactPath.isEmpty()) {
                expectedLeaf = exactPath.get(exactPath.size() - 1);
            }

            Set<String> signatures = new LinkedHashSet<>();
            signatures.add(jsonString(action, "leafFieldSignature"));
            signatures.add(jsonString(action, "field"));
            signatures.add(jsonString(action, "cell"));
            signatures.add(jsonString(action, "accessFieldSignature"));
            JsonElement declarations = action.get("fieldPathLeafDeclarations");
            if (declarations != null && declarations.isJsonArray()) {
                for (JsonElement element : declarations.getAsJsonArray()) {
                    if (element.isJsonObject()) {
                        signatures.add(jsonString(element.getAsJsonObject(),
                                "fieldSignature"));
                    }
                }
            }

            FieldTarget selected = null;
            for (String signature : signatures) {
                Matcher matcher = FIELD.matcher(stringValue(
                        firstNonBlank(signature)));
                if (!matcher.matches() || isMethodMember(matcher.group(3))
                        || !looksLikeArrayType(matcher.group(2))
                        || !expectedLeaf.isEmpty()
                        && !expectedLeaf.equals(matcher.group(3))) {
                    continue;
                }
                FieldTarget candidate = new FieldTarget(matcher.group(1),
                        matcher.group(3), consumedMethod, consumedUnit, true);
                if (selected != null
                        && (!selected.owner.equals(candidate.owner)
                        || !selected.name.equals(candidate.name)
                        || !selected.method.equals(candidate.method)
                        || selected.unitIndex != candidate.unitIndex)) {
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        static boolean hasOneExactLocalDefinition(JsonObject action) {
            String method = jsonString(action, "method");
            String local = jsonString(action, "local");
            Matcher localCell = LOCAL.matcher(jsonString(action, "cell"));
            if (localCell.matches()) {
                method = firstNonBlank(method, localCell.group(1));
                local = firstNonBlank(local, localCell.group(2));
            }
            JsonElement definitions = action.get("definitionSites");
            return !method.isEmpty() && !local.isEmpty()
                    && definitions != null && definitions.isJsonArray()
                    && definitions.getAsJsonArray().size() == 1
                    && definitions.getAsJsonArray().get(0).isJsonObject()
                    && intJson(definitions.getAsJsonArray().get(0)
                    .getAsJsonObject(), "unitIndex", -1) >= 0;
        }

        static List<String> exactArrayFieldPath(JsonObject action) {
            List<String> path = new ArrayList<>();
            JsonElement direct = action.get("fieldPath");
            if (direct != null && direct.isJsonArray()) {
                for (JsonElement segment : direct.getAsJsonArray()) {
                    if (!segment.isJsonPrimitive()
                            || segment.getAsString().trim().isEmpty()) {
                        return Collections.emptyList();
                    }
                    path.add(segment.getAsString().trim());
                }
                if (!path.isEmpty()) return path;
            }
            JsonElement paths = action.get("fieldPaths");
            if (paths == null || !paths.isJsonArray()
                    || paths.getAsJsonArray().size() != 1
                    || !paths.getAsJsonArray().get(0).isJsonArray()) {
                return Collections.emptyList();
            }
            for (JsonElement segment : paths.getAsJsonArray().get(0)
                    .getAsJsonArray()) {
                if (!segment.isJsonPrimitive()
                        || segment.getAsString().trim().isEmpty()) {
                    return Collections.emptyList();
                }
                path.add(segment.getAsString().trim());
            }
            return path;
        }

        static boolean looksLikeArrayType(String javaType) {
            String normalized = firstNonBlank(javaType);
            return normalized != null && (normalized.startsWith("[")
                    || normalized.endsWith("[]"));
        }

        static String projectedField(String value) {
            if (value == null || value.isEmpty()) {
                return "";
            }
            int projection = value.indexOf("#field:");
            if (projection >= 0) {
                int end = value.indexOf('#', projection + 7);
                return value.substring(projection + 7,
                        end < 0 ? value.length() : end).trim();
            }
            Matcher matcher = FIELD.matcher(value);
            return matcher.matches() ? matcher.group(3) : "";
        }

        boolean isEmpty() {
            return localsByMethod.isEmpty() && fields.isEmpty()
                    && accessorCallsBySite.isEmpty();
        }

        Set<String> localMethods() {
            return localsByMethod.keySet();
        }

        Set<String> accessorCallerMethods() {
            Set<String> methods = new LinkedHashSet<>();
            for (AccessorCallTarget target : accessorCallsBySite.values()) {
                methods.add(target.callerMethod);
            }
            return methods;
        }

        Collection<AccessorCallTarget> accessorCalls() {
            return accessorCallsBySite.values();
        }

        boolean matches(String method, String local, int unitIndex) {
            Map<String, Set<Integer>> locals = localsByMethod.get(method);
            if (locals == null || !locals.containsKey(local)) {
                return false;
            }
            Set<Integer> sites = locals.get(local);
            return sites.isEmpty() || sites.contains(unitIndex);
        }

        static int intJson(JsonObject object, String field,
                                   int fallback) {
            JsonElement value = object.get(field);
            try {
                return value == null || value.isJsonNull()
                        ? fallback : value.getAsInt();
            } catch (RuntimeException ignored) {
                return fallback;
            }
        }

        boolean matches(String method, int unitIndex,
                                SootFieldRef field) {
            if (field == null) {
                return false;
            }
            SootClass declaringClass = field.declaringClass();
            String owner = declaringClass == null ? ""
                    : stringValue(declaringClass.getName());
            String fieldName = stringValue(field.name());
            for (FieldTarget target : fields) {
                if (target.name.equals(fieldName)
                        && (target.owner.isEmpty()
                        || target.owner.equals(owner))
                        && (!target.exactSite
                        || target.method.equals(method)
                        && target.unitIndex == unitIndex)) {
                    return true;
                }
            }
            return false;
        }
    }

    /** Exact activation-selected outbound argument sites. */
    static final class ConcolicOutputCaptureSelection {
        private final Map<String, OutputCaptureTarget> targetsByIdentity =
                new LinkedHashMap<>();

        static ConcolicOutputCaptureSelection from(
                Path activationPlan, String selectedActivation)
                throws IOException {
            if (activationPlan == null || !Files.isRegularFile(
                    activationPlan)) {
                throw new IOException("Activation plan not found: "
                        + activationPlan);
            }
            ConcolicOutputCaptureSelection result =
                    new ConcolicOutputCaptureSelection();
            String selected = stringValue(firstNonBlank(selectedActivation));
            try (BufferedReader reader = Files.newBufferedReader(
                    activationPlan, StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) continue;
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) continue;
                    JsonObject row = parsed.getAsJsonObject();
                    if (!selected.isEmpty() && !selected.equals(jsonString(
                            row, "activationId"))) continue;
                    if (!strictJsonBooleanEquals(row, "replayable", true)
                            || !strictJsonBooleanEquals(row,
                            "schedulerReady", true)) continue;
                    JsonElement captures = row.get(
                            "requestedOutputCapture");
                    if (captures == null || !captures.isJsonArray()) continue;
                    for (JsonElement element : captures.getAsJsonArray()) {
                        if (!element.isJsonObject()) continue;
                        OutputCaptureTarget target = new OutputCaptureTarget(
                                element.getAsJsonObject());
                        if (!target.valid()) continue;
                        result.targetsByIdentity.put(target.identity(), target);
                    }
                }
            }
            return result;
        }

        Set<String> methods() {
            Set<String> result = new LinkedHashSet<>();
            for (OutputCaptureTarget target : targetsByIdentity.values()) {
                result.add(target.instrumentedMethod());
            }
            return result;
        }

        Collection<OutputCaptureTarget> targets() {
            return targetsByIdentity.values();
        }
    }

    static final class OutputCaptureTarget {
        static final String CALL_ARGUMENT = "CALL_ARGUMENT";
        static final String FIELD_ASSIGNMENT_RHS =
                "FIELD_ASSIGNMENT_RHS";

        final String captureKind;
        final String captureBindingId;
        final String outputPort;
        final String outputCell;
        final String method;
        final String callerMethod;
        final int unitIndex;
        final String siteId;
        final String calleeMethod;
        final int argumentIndex;
        final String fieldSignature;
        final int occurrence;

        OutputCaptureTarget(JsonObject json) {
            this.captureKind = firstNonBlank(
                    jsonString(json, "captureKind"), CALL_ARGUMENT);
            this.captureBindingId = jsonString(json, "captureBindingId");
            this.outputPort = jsonString(json, "outputPort");
            this.outputCell = jsonString(json, "outputCell");
            this.callerMethod = jsonString(json, "callerMethod");
            this.method = stringValue(firstNonBlank(
                    jsonString(json, "method"), this.callerMethod));
            this.unitIndex = ConcolicMaterializationSelection.intJson(json,
                    "unitIndex", -1);
            this.siteId = jsonString(json, "siteId");
            this.calleeMethod = jsonString(json, "calleeMethod");
            this.argumentIndex = ConcolicMaterializationSelection.intJson(
                    json, "argumentIndex", -1);
            this.fieldSignature = stringValue(firstNonBlank(
                    jsonString(json, "fieldSignature"),
                    jsonString(json, "field")));
            this.occurrence = ConcolicMaterializationSelection.intJson(json,
                    "occurrence", 0);
        }

        boolean valid() {
            if (captureBindingId.isEmpty() || outputPort.isEmpty()
                    || outputCell.isEmpty() || unitIndex < 0
                    || siteId.isEmpty() || occurrence <= 0) {
                return false;
            }
            if (FIELD_ASSIGNMENT_RHS.equals(captureKind)) {
                return !method.isEmpty() && !fieldSignature.isEmpty();
            }
            return CALL_ARGUMENT.equals(captureKind)
                    && !callerMethod.isEmpty() && !calleeMethod.isEmpty()
                    && argumentIndex >= 0;
        }

        String identity() {
            return captureKind + "\n" + instrumentedMethod() + "\n"
                    + unitIndex + "\n" + siteId + "\n" + calleeMethod
                    + "\n" + argumentIndex + "\n" + fieldSignature + "\n"
                    + outputPort + "\n" + outputCell + "\n"
                    + captureBindingId + "\n" + occurrence;
        }

        boolean isFieldAssignmentRhs() {
            return FIELD_ASSIGNMENT_RHS.equals(captureKind);
        }

        String instrumentedMethod() {
            return isFieldAssignmentRhs() ? method : callerMethod;
        }
    }

    static final class AccessorCallTarget {
        final String callerMethod;
        final int callUnitIndex;
        final String callSiteId;
        final String declaredCallee;
        final String implementationMethod;
        final String fieldSignature;
        final String fieldOwner;
        final String fieldName;
        final String fieldAuthority;

        AccessorCallTarget(String callerMethod, int callUnitIndex,
                                   String callSiteId,
                                   String declaredCallee,
                                   String implementationMethod,
                                   String fieldSignature,
                                   String fieldOwner, String fieldName,
                                   String fieldAuthority) {
            this.callerMethod = callerMethod;
            this.callUnitIndex = callUnitIndex;
            this.callSiteId = callSiteId;
            this.declaredCallee = declaredCallee;
            this.implementationMethod = implementationMethod;
            this.fieldSignature = fieldSignature;
            this.fieldOwner = fieldOwner;
            this.fieldName = fieldName;
            this.fieldAuthority = fieldAuthority;
        }

        String siteIdentity() {
            return callerMethod + "#u" + callUnitIndex;
        }

        boolean sameMaterialization(AccessorCallTarget other) {
            return other != null
                    && declaredCallee.equals(other.declaredCallee)
                    && implementationMethod.equals(
                    other.implementationMethod)
                    && fieldSignature.equals(other.fieldSignature)
                    && fieldOwner.equals(other.fieldOwner)
                    && fieldName.equals(other.fieldName)
                    && fieldAuthority.equals(other.fieldAuthority);
        }
    }

    private static final class FieldTarget {
        final String owner;
        final String name;
        final String method;
        final int unitIndex;
        final boolean exactSite;

        FieldTarget(String owner, String name) {
            this(owner, name, "", -1, false);
        }

        FieldTarget(String owner, String name, String method,
                            int unitIndex, boolean exactSite) {
            String normalizedOwner = firstNonBlank(owner);
            String normalizedName = firstNonBlank(name);
            this.owner = normalizedOwner == null ? "" : normalizedOwner;
            this.name = normalizedName == null ? "" : normalizedName;
            String normalizedMethod = firstNonBlank(method);
            this.method = normalizedMethod == null ? "" : normalizedMethod;
            this.unitIndex = unitIndex;
            this.exactSite = exactSite;
        }
    }


    private static String jsonString(JsonObject object, String field) {
        if (object == null) return "";
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static JsonObject jsonObject(JsonObject object, String field) {
        if (object == null) return new JsonObject();
        JsonElement value = object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static boolean jsonBoolean(JsonObject object, String field,
                                       boolean fallback) {
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static int intValue(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(String.valueOf(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }
}
