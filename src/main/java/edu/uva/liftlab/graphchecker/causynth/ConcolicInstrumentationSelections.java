package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.JsonFields;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
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
        String planValue = stringValue(System.getProperty(
                "causynth.concolic.task.plan"));
        String selectedTask = stringValue(System.getProperty(
                "causynth.concolic.task.id"));
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
        private final String rootMethod;
        private final String receiverClass;
        private final ConcolicBranchSelection branches;
        private final LoopBoundPolicy loopBound;
        private final ConcolicMaterializationSelection materializations;
        private final List<RootedOutputCapture> outputCaptures;
        private final List<CallArgumentOutputCapture> callArgumentOutputs;
        private final List<ExactHeapOutputCapture> exactHeapOutputs;
        private final Set<String> instrumentationMethods;
        private final Set<String> replayAnchorMethods;
        private final boolean replayAnchorAllowed;
        private final String targetMethod;
        private final boolean outputRelation;

        private InstrumentationPlan(ExecutionTask task) throws IOException {
            if (!task.executable()) {
                throw new IOException("Execution task " + task.taskId()
                        + " is not executable");
            }
            rootMethod = task.rootMethod();
            if (rootMethod.isEmpty()) {
                throw new IOException("Execution task " + task.taskId()
                        + " has no root method");
            }
            receiverClass = jsonString(task.rootSelector(), "receiverClass");
            InputActionCatalog inputActions = task.inputActions();
            JsonArray symbolic = inputActions.symbolic();
            replayAnchorAllowed = !task.rootSelector().has("arguments")
                    && !hasRootArgumentSymbolicAction(symbolic);
            targetMethod = task.targetMethod();
            outputRelation = task.outputClosure() != null;
            branches = ConcolicBranchSelection.from(task.branches());
            loopBound = task.loopBound();
            materializations = ConcolicMaterializationSelection.from(symbolic);
            outputCaptures = rootedOutputCaptures(task.outputCaptures(),
                    inputActions.all());
            callArgumentOutputs = callArgumentOutputCaptures(
                    task.outputCaptures());
            exactHeapOutputs = exactHeapOutputCaptures(
                    task.outputCaptures());

            LinkedHashSet<String> anchorMethods = new LinkedHashSet<>();
            if (!task.targetMethod().isEmpty()) {
                anchorMethods.add(task.targetMethod());
            }

            LinkedHashSet<String> methods = new LinkedHashSet<>();
            methods.add(rootMethod);
            OutputClosureContract closure = task.outputClosure();
            if (closure != null) {
                methods.addAll(closure.executionScope().methods());
                anchorMethods.addAll(closure.executionScope().methods());
            } else {
                methods.addAll(branches.methods());
                anchorMethods.addAll(branches.methods());
            }
            for (CallArgumentOutputCapture capture : callArgumentOutputs) {
                methods.add(capture.method());
            }
            for (ExactHeapOutputCapture capture : exactHeapOutputs) {
                methods.add(capture.method());
            }
            instrumentationMethods = Collections.unmodifiableSet(methods);
            anchorMethods.remove(rootMethod);
            replayAnchorMethods = Collections.unmodifiableSet(anchorMethods);
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
            String encoded = null;
            try (BufferedReader reader = Files.newBufferedReader(normalized,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    if (encoded != null) {
                        throw new IOException("Concolic instrumentation "
                                + "requires a singleton execution task plan: "
                                + normalized);
                    }
                    encoded = line;
                }
            }
            if (encoded == null) {
                throw new IOException("Execution task plan is empty: "
                        + normalized);
            }
            try {
                JsonElement parsed = JsonParser.parseString(encoded);
                if (!parsed.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "execution task row must be an object");
                }
                ExecutionTask task = ExecutionTask.decode(
                        parsed.getAsJsonObject());
                if (!selected.equals(task.taskId())) {
                    throw new IllegalArgumentException(
                            "selected task id " + selected
                                    + " does not match singleton task "
                                    + task.taskId());
                }
                return new InstrumentationPlan(task);
            } catch (RuntimeException malformed) {
                throw new IOException("Malformed execution task "
                        + selected, malformed);
            }
        }

        String rootMethod() {
            return rootMethod;
        }

        String receiverClass() {
            return receiverClass;
        }

        ConcolicBranchSelection branches() {
            return branches;
        }

        LoopBoundPolicy loopBound() {
            return loopBound;
        }

        ConcolicMaterializationSelection materializations() {
            return materializations;
        }

        List<RootedOutputCapture> outputCaptures() {
            return outputCaptures;
        }

        List<CallArgumentOutputCapture> callArgumentOutputs() {
            return callArgumentOutputs;
        }

        List<ExactHeapOutputCapture> exactHeapOutputs() {
            return exactHeapOutputs;
        }

        Set<String> instrumentationMethods() {
            return instrumentationMethods;
        }

        Set<String> replayAnchorMethods() {
            return replayAnchorMethods;
        }

        boolean replayAnchorAllowed() {
            return replayAnchorAllowed;
        }

        String targetMethod() {
            return targetMethod;
        }

        boolean outputRelation() {
            return outputRelation;
        }

        private static boolean hasRootArgumentSymbolicAction(
                JsonArray symbolic) {
            for (JsonElement element : symbolic) {
                JsonObject action = element.getAsJsonObject();
                String location = jsonString(action, "location");
                if ("ARGUMENT".equals(location)
                        || "ARGUMENT_FIELD_PATH".equals(location)) {
                    return true;
                }
            }
            return false;
        }

        private static List<RootedOutputCapture> rootedOutputCaptures(
                List<OutputCaptureSpec> captures, JsonArray actions)
                throws IOException {
            List<RootedOutputCapture> rooted = new ArrayList<>();
            for (OutputCaptureSpec capture : captures) {
                if (!capture.capturesRegionExitField()) continue;
                JsonObject match = null;
                for (JsonElement element : actions) {
                    JsonObject action = element.getAsJsonObject();
                    if (!capture.accessRootInputPort().equals(
                            jsonString(action, "symbol"))) {
                        continue;
                    }
                    if (match != null) {
                        throw new IOException("Output capture "
                                + capture.captureBindingId()
                                + " has multiple access-root input actions");
                    }
                    match = action;
                }
                List<String> path = match == null
                        ? capture.fieldPath()
                        : FieldPathSpec.stringArray(match, "fieldPath");
                if (path.isEmpty()
                        || capture.fieldPath().size() != 1
                        || !capture.fieldPath().get(0).equals(
                        path.get(path.size() - 1))) {
                    throw new IOException("Output capture "
                            + capture.captureBindingId()
                            + " has no exact rooted field path");
                }
                // A nested heap owner is identified by the exact field-read
                // hook at runtime, not by inventing a path from the region
                // root receiver.  Runtime captures it from that observed
                // owner when the bounded activation finishes.
                if (match != null && "HEAP_OBJECT_FIELD".equals(
                        jsonString(match, "location"))) {
                    if (!"SYMBOLIC".equals(jsonString(match, "mode"))
                            || !"FIELD_ACCESS".equals(
                            jsonString(match, "bindingMode"))) {
                        throw new IOException("Output capture "
                                + capture.captureBindingId()
                                + " has no symbolic nested field owner");
                    }
                    continue;
                }
                rooted.add(new RootedOutputCapture(capture, path));
            }
            return Collections.unmodifiableList(rooted);
        }

        private static List<CallArgumentOutputCapture>
        callArgumentOutputCaptures(List<OutputCaptureSpec> captures) {
            List<CallArgumentOutputCapture> result = new ArrayList<>();
            for (OutputCaptureSpec capture : captures) {
                if (capture.capturesCallArgument()) {
                    result.add(new CallArgumentOutputCapture(capture));
                }
            }
            return Collections.unmodifiableList(result);
        }

        private static List<ExactHeapOutputCapture>
        exactHeapOutputCaptures(List<OutputCaptureSpec> captures) {
            List<ExactHeapOutputCapture> result = new ArrayList<>();
            for (OutputCaptureSpec capture : captures) {
                if (capture.capturesExactHeapWrite()) {
                    result.add(new ExactHeapOutputCapture(capture));
                }
            }
            return Collections.unmodifiableList(result);
        }
    }

    static final class ExactHeapOutputCapture {
        private final OutputCaptureSpec capture;

        private ExactHeapOutputCapture(OutputCaptureSpec capture) {
            this.capture = capture;
        }

        String captureBindingId() {
            return capture.captureBindingId();
        }

        String method() {
            return capture.definitionMethod();
        }

        int unitIndex() {
            return capture.definitionUnitIndex();
        }

        String declaredCallee() {
            return capture.declaredCallee();
        }

        String fieldSignature() {
            // The existing pipeline selector consumes this accessor to match
            // the concrete putfield.  For a nested leaf projection that is
            // the definition field, not the semantic output leaf.
            return capture.definitionFieldSignature();
        }

        String definitionFieldSignature() {
            return capture.definitionFieldSignature();
        }

        String leafFieldSignature() {
            return capture.leafFieldSignature();
        }

        List<String> fieldPath() {
            return capture.fieldPath();
        }

        boolean nestedFieldWriteState() {
            return capture.nestedFieldWriteState();
        }

        boolean mutationState() {
            return capture.capturesMutationState();
        }

        boolean atomicArithmeticMutationState() {
            return !capture.atomicArithmeticValueFieldSignature().isEmpty();
        }

        boolean definitionInvocationScoped() {
            return capture.definitionInvocationScoped();
        }

        boolean fieldWriteState() {
            return capture.capturesFieldWriteState();
        }
    }

    static final class CallArgumentOutputCapture {
        private final OutputCaptureSpec capture;

        private CallArgumentOutputCapture(OutputCaptureSpec capture) {
            this.capture = capture;
        }

        String captureBindingId() {
            return capture.captureBindingId();
        }

        String method() {
            return capture.definitionMethod();
        }

        int unitIndex() {
            return capture.definitionUnitIndex();
        }

        int argumentIndex() {
            return capture.argumentIndex();
        }

        String declaredCallee() {
            return capture.declaredCallee();
        }
    }

    static final class RootedOutputCapture {
        private final OutputCaptureSpec capture;
        private final List<String> fieldPath;

        private RootedOutputCapture(OutputCaptureSpec capture,
                                    List<String> fieldPath) {
            this.capture = capture;
            this.fieldPath = Collections.unmodifiableList(
                    new ArrayList<>(fieldPath));
        }

        String captureBindingId() {
            return capture.captureBindingId();
        }

        String fieldSignature() {
            return capture.fieldSignature();
        }

        List<String> fieldPath() {
            return fieldPath;
        }
    }

    static final class ConcolicBranchSelection {
        private static final Pattern SITE =
                Pattern.compile("^(<.*>)#u([0-9]+)$");
        private final Map<String, Set<Integer>> unitsByMethod =
                new LinkedHashMap<>();

        static ConcolicBranchSelection from(JsonArray branches) {
            ConcolicBranchSelection result = new ConcolicBranchSelection();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject branch = element.getAsJsonObject();
                String method = jsonString(branch, "method");
                int unit = JsonFields.integer(branch, "unitIndex", -1);
                Matcher site = SITE.matcher(jsonString(branch, "siteId"));
                if (site.matches()) {
                    method = site.group(1);
                    unit = Integer.parseInt(site.group(2));
                }
                if (!method.isEmpty() && unit >= 0) {
                    result.unitsByMethod.computeIfAbsent(method,
                            ignored -> new LinkedHashSet<>()).add(unit);
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

    private static FieldTarget concolicFieldTarget(JsonObject action) {
        DeclaredField field = FieldPathSpec.declaredField(
                jsonString(action, "accessFieldSignature"));
        return field == null ? null
                : new FieldTarget(field.owner(), field.name());
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
        private final Map<String, Map<String, Set<Integer>>> localsByMethod =
                new LinkedHashMap<>();
        private final Map<String, Set<Integer>> methodArguments =
                new LinkedHashMap<>();
        private final List<FieldTarget> fields = new ArrayList<>();
        private final Map<String, AccessorCallTarget> accessorCallsBySite =
                new LinkedHashMap<>();

        private static ConcolicMaterializationSelection from(
                JsonArray actions) throws IOException {
            ConcolicMaterializationSelection result =
                    new ConcolicMaterializationSelection();
            for (JsonElement element : actions) {
                result.add(element.getAsJsonObject());
            }
            return result;
        }

        void add(JsonObject action) throws IOException {
            addAccessorCallTarget(action);
            String mode = jsonString(action, "bindingMode");
            String cell = jsonString(action, "cell");
            if ("METHOD_ARGUMENT".equals(mode)) {
                String method = jsonString(action, "method");
                int index = intJson(action, "index", -1);
                if (method.isEmpty() || index < 0) {
                    throw unsupported(action);
                }
                methodArguments.computeIfAbsent(method,
                        ignored -> new LinkedHashSet<>()).add(index);
                return;
            }
            if ("LOCAL_DEFINITION".equals(mode)) {
                String method = jsonString(action, "method");
                String local = jsonString(action, "local");
                Matcher matcher = LOCAL.matcher(cell);
                if (matcher.matches()) {
                    method = firstNonBlank(method, matcher.group(1));
                    local = firstNonBlank(local, matcher.group(2));
                }
                if (!method.isEmpty() && !local.isEmpty()) {
                    JsonElement definitions = action.get("definitionSites");
                    if (definitions != null && definitions.isJsonArray()) {
                        for (JsonElement element
                                : definitions.getAsJsonArray()) {
                            if (element.isJsonObject()) {
                                int site = intJson(element.getAsJsonObject(),
                                        "unitIndex", -1);
                                if (site >= 0) {
                                    addLocal(method, local, site);
                                }
                            }
                        }
                    }
                    if (definitions == null
                            || !definitions.isJsonArray()
                            || definitions.getAsJsonArray().size() == 0) {
                        addLocal(method, local, -1);
                    }
                }
                return;
            }
            String location = jsonString(action, "location");
            if (!"FIELD_ACCESS".equals(mode)
                    && !"HEAP_OBJECT_FIELD".equals(location)) {
                return;
            }
            FieldTarget target = concolicFieldTarget(action);
            if (target != null) {
                fields.add(target);
            }
        }

        private void addLocal(String method, String local, int unitIndex) {
            Map<String, Set<Integer>> locals =
                    localsByMethod.computeIfAbsent(method,
                            ignored -> new LinkedHashMap<>());
            Set<Integer> sites = locals.computeIfAbsent(local,
                    ignored -> new LinkedHashSet<>());
            if (unitIndex >= 0) sites.add(unitIndex);
        }

        void addAccessorCallTarget(JsonObject action) throws IOException {
            String caller = jsonString(action, "accessorCallerMethod");
            int unitIndex = intJson(action, "accessorCallUnitIndex", -1);
            String callee = jsonString(action, "accessorDeclaredCallee");
            String implementation = jsonString(action,
                    "accessorImplementationMethod");
            boolean constrained = !caller.isEmpty() || unitIndex >= 0
                    || !callee.isEmpty() || !implementation.isEmpty();
            if (!constrained) return;
            if (caller.isEmpty() || unitIndex < 0 || callee.isEmpty()
                    || implementation.isEmpty()) {
                throw unsupported(action);
            }
            String site = caller + "#u" + unitIndex;

            String fieldSignature = jsonString(action,
                    "accessFieldSignature");
            DeclaredField declaredField =
                    FieldPathSpec.declaredField(fieldSignature);
            if (declaredField == null) {
                throw unsupported(action);
            }
            AccessorCallTarget target = new AccessorCallTarget(caller,
                    unitIndex, site, callee, implementation, fieldSignature,
                    declaredField.name());
            AccessorCallTarget previous = accessorCallsBySite.get(
                    target.callSiteId);
            if (previous != null && !previous.sameMaterialization(target)) {
                throw unsupported(action);
            }
            if (previous == null) {
                accessorCallsBySite.put(target.callSiteId, target);
            }
        }

        private static IOException unsupported(JsonObject action) {
            return new IOException("Unsupported concolic materialization "
                    + jsonString(action, "symbol"));
        }

        boolean isEmpty() {
            return localsByMethod.isEmpty() && methodArguments.isEmpty()
                    && fields.isEmpty()
                    && accessorCallsBySite.isEmpty();
        }

        Set<String> localMethods() {
            return localsByMethod.keySet();
        }

        Set<String> methodArgumentMethods() {
            return methodArguments.keySet();
        }

        Set<Integer> methodArguments(String method) {
            Set<Integer> indices = methodArguments.get(method);
            return indices == null ? Collections.<Integer>emptySet()
                    : indices;
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
            SootField declared = CausynthStaticFacts.declaredField(field);
            SootClass declaringClass = declared == null
                    ? field.declaringClass() : declared.getDeclaringClass();
            String owner = declaringClass == null ? ""
                    : stringValue(declaringClass.getName());
            String fieldName = stringValue(declared == null
                    ? field.name() : declared.getName());
            for (FieldTarget target : fields) {
                if (target.name.equals(fieldName)
                        && (target.owner.isEmpty()
                        || target.owner.equals(owner))) {
                    return true;
                }
            }
            return false;
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

        FieldTarget(String owner, String name) {
            String normalizedOwner = firstNonBlank(owner);
            String normalizedName = firstNonBlank(name);
            this.owner = normalizedOwner == null ? "" : normalizedOwner;
            this.name = normalizedName == null ? "" : normalizedName;
        }
    }


    private static String jsonString(JsonObject object, String field) {
        return JsonFields.string(object, field);
    }

    static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    static int intValue(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        if (value == null || String.valueOf(value).trim().isEmpty()
                || "null".equals(String.valueOf(value))) {
            return fallback;
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
