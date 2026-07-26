package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.concolic.JsonFields;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import soot.SootClass;
import soot.SootFieldRef;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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
 * Execution-task parsing and immutable instrumentation selections.
 *
 * <p>This class deliberately contains no Soot body mutation. It validates the
 * scheduler-owned plan and exposes only the exact sites that the pipeline may
 * instrument, keeping fail-closed plan semantics separate from bytecode
 * rewriting.</p>
 */
final class ConcolicInstrumentationSelections {
    private ConcolicInstrumentationSelections() {
    }

    static InstrumentationPlan instrumentationPlanFromEnvironment() {
        String planValue = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.task.plan"),
                System.getenv("CAUSYNTH_CONCOLIC_TASK_PLAN")));
        String selectedTask = stringValue(firstNonBlank(
                System.getProperty("causynth.concolic.task.id"),
                System.getenv("CAUSYNTH_CONCOLIC_TASK_ID")));
        if (planValue.isEmpty() || selectedTask.isEmpty()) {
            throw new IllegalStateException(
                    "Concolic instrumentation requires a task plan "
                            + "and selected task id");
        }
        Path plan = Paths.get(planValue).toAbsolutePath().normalize();
        try {
            return InstrumentationPlan.from(plan, selectedTask);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic instrumentation plan from "
                            + plan, exception);
        }
    }

    /**
     * One immutable view of the scheduler-selected execution task. The
     * instrumentation pipeline builds this once and derives every selection
     * from it instead of reparsing the JSONL for each hook family.
     */
    static final class InstrumentationPlan {
        private final Set<String> roots;
        private final ConcolicMaterializationSelection materializations;
        private final List<OutputCaptureTarget> outputCaptures;
        private final boolean boundedOutputClosureCoverageReady;

        private InstrumentationPlan(
                JsonObject row, OutputClosureContract closure)
                throws IOException {
            this.roots = Collections.singleton(
                    jsonString(JsonFields.object(row, "rootSelector"),
                            "method"));
            this.materializations =
                    ConcolicMaterializationSelection.fromRow(row);
            this.outputCaptures = outputCaptureTargets(closure);
            this.boundedOutputClosureCoverageReady = closure != null
                    && boundedOutputClosureRowReady(row, closure);
        }

        static InstrumentationPlan from(Path taskPlan, String selectedTask)
                throws IOException {
            if (taskPlan == null || !Files.isRegularFile(taskPlan)) {
                throw new IOException("Task plan not found: " + taskPlan);
            }
            Path normalized = taskPlan.toAbsolutePath().normalize();
            String selected = stringValue(firstNonBlank(selectedTask));
            if (selected.isEmpty()) {
                throw new IOException("Selected task id is required");
            }
            JsonObject selectedRow = null;
            try (BufferedReader reader = Files.newBufferedReader(normalized,
                    StandardCharsets.UTF_8)) {
                String line;
                int lineNumber = 0;
                while ((line = reader.readLine()) != null) {
                    lineNumber++;
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    final JsonElement parsed;
                    try {
                        parsed = JsonParser.parseString(line);
                    } catch (RuntimeException malformed) {
                        throw new IOException("Malformed task plan row "
                                + lineNumber + " in " + normalized, malformed);
                    }
                    if (!parsed.isJsonObject()) {
                        throw new IOException("Task plan row "
                                + lineNumber + " is not a JSON object in "
                                + normalized);
                    }
                    JsonObject row = parsed.getAsJsonObject();
                    String taskId = jsonString(row, "taskId");
                    if (!selected.equals(taskId)) {
                        continue;
                    }
                    if (selectedRow != null) {
                        throw new IOException("Duplicate execution task "
                                + selected + " in "
                                + normalized);
                    }
                    selectedRow = row;
                }
            }
            if (selectedRow == null) {
                throw new IOException("Execution task " + selected
                        + " not found in " + normalized);
            }
            if (!admissionExecutable(selectedRow)) {
                throw new IOException("Execution task " + selected
                        + " is not executable");
            }
            String root = jsonString(JsonFields.object(selectedRow,
                    "rootSelector"), "method");
            if (root.isEmpty()) {
                throw new IOException("Execution task " + selected
                        + " has no root method");
            }
            OutputClosureContract closure = null;
            if (selectedRow.has(OutputClosureContract.FIELD)) {
                try {
                    closure = OutputClosureCodec.decode(selectedRow);
                } catch (RuntimeException malformed) {
                    throw new IOException("Malformed output closure for task "
                            + selected, malformed);
                }
            } else if (selectedRow.has("requestedOutput")
                    || selectedRow.has("requestedOutputSlice")
                    || selectedRow.has("requestedOutputCapture")
                    || selectedRow.has("requestedOutputCaptureRequired")
                    || selectedRow.has("requestedOutputCaptureComplete")) {
                throw new IOException("Execution task " + selected
                        + " uses retired singular output fields");
            }
            return new InstrumentationPlan(selectedRow, closure);
        }

        Set<String> roots() {
            return roots;
        }

        ConcolicMaterializationSelection materializations() {
            return materializations;
        }

        List<OutputCaptureTarget> outputCaptures() {
            return outputCaptures;
        }

        boolean boundedOutputClosureCoverageReady() {
            return boundedOutputClosureCoverageReady;
        }
    }

    private static boolean boundedOutputClosureRowReady(
            JsonObject row, OutputClosureContract closure) {
        if (!ClosureGoalKind.OUTPUT_RELATION_CLOSURE.name().equals(
                jsonString(row, ClosureGoalKind.TASK_FIELD))) {
            return false;
        }

        for (OutputClosureContract.Member member : closure.members()) {
            if (!boundedOutputMemberReady(row, member)) {
                return false;
            }
        }
        return true;
    }

    private static boolean boundedOutputMemberReady(
            JsonObject row, OutputClosureContract.Member member) {
        JsonObject slice = member.slice();
        if (!jsonBoolean(slice, "complete", false)
                || !member.captureComplete()) {
            return false;
        }
        if (!member.captureRequired()
                && !heapEffectCaptureDischargeReady(row, slice,
                member.portId(), member.cell())) {
            return false;
        }
        return true;
    }

    private static boolean heapEffectCaptureDischargeReady(
            JsonObject row, JsonObject slice, String outputPort,
            String outputCell) {
        String inputPort = jsonString(slice, "captureDischargeInputPort");
        if (!jsonBoolean(slice,
                "captureDischargedByHeapEffectTransformer", false)
                || !"HEAP_EFFECT_STATE_TRANSFORMER".equals(jsonString(slice,
                "captureDischargeAuthority"))
                || inputPort.isEmpty()
                || !jsonBoolean(slice,
                "requestedStateTransformerContractComplete", false)) {
            return false;
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
     * asks Soot to expose to the VM.  This is intentionally task-plan
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
        private boolean unsupported;

        private static ConcolicMaterializationSelection fromRow(
                JsonObject row) throws IOException {
            ConcolicMaterializationSelection result =
                    new ConcolicMaterializationSelection();
            String taskId = jsonString(row, "taskId");
            InputActionCatalog catalog;
            try {
                catalog = InputActionCatalog.decode(row);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Replayable execution task "
                        + taskId + " has invalid input actions: "
                        + malformed.getMessage(), malformed);
            }
            for (JsonElement element : catalog.symbolic()) {
                result.add(element.getAsJsonObject());
            }
            if (result.unsupported) {
                throw new IOException(
                        "Unsupported concolic materialization");
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
                    unsupported = true;
                    return;
                }
                String[] target = resolveConcolicFieldTarget(action);
                if (target[0].isEmpty() || target[1].isEmpty()) {
                    unsupported = true;
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
                    unsupported = true;
                    return;
                }
                String[] target = resolveConcolicFieldTarget(action);
                if (target[0].isEmpty() || target[1].isEmpty()) {
                    unsupported = true;
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
                unsupported = true;
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
                unsupported = true;
                return;
            }
            AccessorCallTarget target = new AccessorCallTarget(caller,
                    unitIndex, site, callee, implementation, fieldSignature,
                    fieldName);
            AccessorCallTarget previous = accessorCallsBySite.get(
                    target.callSiteId);
            if (previous != null && !previous.sameMaterialization(target)) {
                unsupported = true;
                return;
            }
            if (previous == null) {
                accessorCallsBySite.put(target.callSiteId, target);
            }
        }

        void addExactArrayLeafTarget(JsonObject action) {
            FieldTarget leaf = exactArrayLeafTarget(action);
            if (leaf == null) {
                unsupported = true;
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
            JsonElement direct = action.get("fieldPath");
            if (direct != null && (!direct.isJsonArray()
                    || direct.getAsJsonArray().size() > 0)) {
                return FieldPathSpec.stringArray(action, "fieldPath");
            }
            List<List<String>> paths = FieldPathSpec.paths(action,
                    "fieldPaths");
            return paths.size() == 1 ? paths.get(0)
                    : Collections.emptyList();
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
            return JsonFields.integer(object, field, fallback);
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

    private static List<OutputCaptureTarget> outputCaptureTargets(
            OutputClosureContract closure) throws IOException {
        if (closure == null) {
            return Collections.emptyList();
        }
        List<OutputCaptureTarget> result = new ArrayList<>();
        for (JsonElement element : OutputClosureCodec.captures(closure)) {
            OutputCaptureTarget target = new OutputCaptureTarget(
                    element.getAsJsonObject());
            if (target.occurrence <= 0) {
                throw new IOException("Output capture occurrence must "
                        + "be positive: " + target.captureBindingId);
            }
            result.add(target);
        }
        return Collections.unmodifiableList(result);
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
            this.captureKind = jsonString(json, "captureKind");
            this.captureBindingId = jsonString(json, "captureBindingId");
            this.outputPort = jsonString(json, "outputPort");
            this.outputCell = jsonString(json, "outputCell");
            this.callerMethod = jsonString(json, "callerMethod");
            this.method = jsonString(json, "method");
            this.unitIndex = ConcolicMaterializationSelection.intJson(json,
                    "unitIndex", -1);
            this.siteId = jsonString(json, "siteId");
            this.calleeMethod = jsonString(json, "calleeMethod");
            this.argumentIndex = ConcolicMaterializationSelection.intJson(
                    json, "argumentIndex", -1);
            this.fieldSignature = jsonString(json, "fieldSignature");
            this.occurrence = ConcolicMaterializationSelection.intJson(json,
                    "occurrence", 0);
        }

        String instrumentedMethod() {
            return FIELD_ASSIGNMENT_RHS.equals(captureKind) ? method
                    : callerMethod;
        }
    }

    static final class AccessorCallTarget {
        final String callerMethod;
        final int callUnitIndex;
        final String callSiteId;
        final String declaredCallee;
        final String implementationMethod;
        final String fieldSignature;
        final String fieldName;

        AccessorCallTarget(String callerMethod, int callUnitIndex,
                                   String callSiteId,
                                   String declaredCallee,
                                   String implementationMethod,
                                   String fieldSignature,
                                   String fieldName) {
            this.callerMethod = callerMethod;
            this.callUnitIndex = callUnitIndex;
            this.callSiteId = callSiteId;
            this.declaredCallee = declaredCallee;
            this.implementationMethod = implementationMethod;
            this.fieldSignature = fieldSignature;
            this.fieldName = fieldName;
        }

        boolean sameMaterialization(AccessorCallTarget other) {
            return other != null
                    && declaredCallee.equals(other.declaredCallee)
                    && implementationMethod.equals(
                    other.implementationMethod)
                    && fieldSignature.equals(other.fieldSignature)
                    && fieldName.equals(other.fieldName);
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
        return JsonFields.string(object, field);
    }

    private static boolean admissionExecutable(JsonObject row) {
        return "EXECUTABLE".equals(jsonString(
                JsonFields.object(row, "admission"), "state"));
    }

    private static boolean jsonBoolean(JsonObject object, String field,
                                       boolean fallback) {
        return JsonFields.bool(object, field, fallback);
    }

    static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    static int intValue(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(String.valueOf(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    static String firstNonBlank(String... values) {
        String value = JsonFields.firstNonBlank(values);
        return value.isEmpty() ? null : value;
    }
}
