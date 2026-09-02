package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.JsonFields;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
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
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Execution-task parsing and immutable instrumentation selections. */
public final class ConcolicInstrumentationSelections {
    private ConcolicInstrumentationSelections() {
    }

    /** Whether this JVM was asked to rewrite a scheduled concolic campaign. */
    public static boolean instrumentationRequested() {
        return Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                "false"));
    }

    /** Declaring classes whose bodies the selected campaign may rewrite. */
    public static Set<String> applicationClassesFromEnvironment() {
        Set<String> classes = new LinkedHashSet<>();
        for (InstrumentationPlan plan
                : instrumentationCampaignFromEnvironment()) {
            for (String signature : plan.envelopeMethods()) {
                String owner = CausynthStaticFacts.methodOwner(signature);
                if (!owner.isEmpty()) classes.add(owner);
            }
        }
        if (classes.isEmpty()) {
            throw new IllegalStateException(
                    "Concolic instrumentation plan names no application "
                            + "classes");
        }
        return Collections.unmodifiableSet(classes);
    }

    /** How many tasks one instrumentation campaign may contain. */
    static final String MAX_TASKS_PROPERTY =
            "causynth.concolic.campaign.max.tasks";
    static final int DEFAULT_MAX_TASKS = 64;

    /** The campaign this instrumentation pass must cover, in plan order. */
    static List<InstrumentationPlan> instrumentationCampaignFromEnvironment() {
        String planValue = stringValue(System.getProperty(
                "causynth.concolic.task.plan"));
        String selectedTasks = stringValue(System.getProperty(
                "causynth.concolic.task.id"));
        if (planValue.isEmpty() || selectedTasks.isEmpty()) {
            throw new IllegalStateException(
                    "Concolic instrumentation requires a task plan "
                            + "and selected task id");
        }
        Path plan = Paths.get(planValue).toAbsolutePath().normalize();
        try {
            return InstrumentationPlan.campaign(plan, selectedTasks);
        } catch (IOException exception) {
            throw new IllegalStateException(
                    "Could not load concolic instrumentation plan from "
                            + plan, exception);
        }
    }

    /** One immutable view of the scheduler-selected execution task. */
    static final class InstrumentationPlan {
        /** Exact plan selector shared by a seed task and its replays. */
        private final String instrumentationSelector;
        private final String rootMethod;
        private final String receiverClass;
        private final ConcolicBranchSelection branches;
        private final LoopBoundPolicy loopBound;
        /** Array-indexed loops whose concrete cardinality is not a K_L. */
        private final Set<String> fixedCountLoopSites;
        /**
         * The loop body this region is rooted at, empty when the region keeps
         * its root method's own entry. Present only under
         * {@link LoopBoundPolicy#LOOP_BODY_ROOT}.
         */
        private final String rootLoopMethod;
        private final int rootLoopHeaderUnitIndex;
        private final Set<String> rootLoopControlSites;
        private final ConcolicMaterializationSelection materializations;
        private final List<RootedOutputCapture> outputCaptures;
        private final List<CallArgumentOutputCapture> callArgumentOutputs;
        private final List<CommunicationEffectCapture> communicationEffects;
        private final List<ExactHeapOutputCapture> exactHeapOutputs;
        /**
         * Where this occurrence hands a declared communication port to the VM,
         * or takes one from it.
         */
        private final List<CommunicationHandoffSpec> communicationHandoffs;
        /** Complete replay-call catalog, including unselected landmarks. */
        private final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        private final Set<String> instrumentationMethods;
        private final Set<String> replayAnchorMethods;
        private final String targetMethod;
        private final boolean dynamicAssociativeTarget;

        private InstrumentationPlan(ExecutionTask task) throws IOException {
            if (!task.executable()) {
                throw new IOException("Execution task " + task.taskId()
                        + " is not executable");
            }
            instrumentationSelector = task.instrumentationSelector();
            rootMethod = task.rootMethod();
            if (rootMethod.isEmpty()) {
                throw new IOException("Execution task " + task.taskId()
                        + " has no root method");
            }
            receiverClass = string(task.rootSelector(), "receiverClass");
            InputActionCatalog inputActions = task.inputActions();
            JsonArray symbolic = inputActions.symbolic();
            targetMethod = task.targetMethod();
            dynamicAssociativeTarget = declaresDynamicAssociativeTarget(
                    task.modelAssignments());
            branches = ConcolicBranchSelection.from(task.branches());
            loopBound = task.loopBound();
            fixedCountLoopSites = task.fixedCountLoopSites();
            rootLoopMethod = task.rootLoopMethod();
            rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            rootLoopControlSites = task.rootLoopControlSites();
            materializations = ConcolicMaterializationSelection.from(symbolic);
            materializations.addCapturePrerequisiteTargets(
                    task.outputClosure(), inputActions.all());
            materializations.addSharedCarrierTargets(
                    task.sharedCarriers(), inputActions.all());
            outputCaptures = rootedOutputCaptures(task.outputCaptures(),
                    inputActions.all());
            callArgumentOutputs = selectedCaptures(task.outputCaptures(),
                    OutputCaptureSpec::capturesCallArgument,
                    CallArgumentOutputCapture::new);
            communicationEffects = selectedCaptures(task.outputCaptures(),
                    OutputCaptureSpec::capturesCommunicationEffect,
                    CommunicationEffectCapture::new);
            exactHeapOutputs = selectedCaptures(task.outputCaptures(),
                    OutputCaptureSpec::capturesExactHeapWrite,
                    ExactHeapOutputCapture::new);
            communicationHandoffs = task.communicationHandoffs();
            configuredSourcePhases = task.configuredSourcePhases();

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
            addCaptureMethods(methods, callArgumentOutputs);
            addCaptureMethods(methods, communicationEffects);
            addCaptureMethods(methods, exactHeapOutputs);
            // A concrete shared-state carrier is not a fresh symbolic input,
            // but its exact read still needs the materialization hook which
            // admits the planner-selected producer version.
            methods.addAll(materializations.sharedCarrierAccessMethods());
            // A cut's own frame is where the port's value is presented and
            // received.
            for (CommunicationHandoffSpec site : communicationHandoffs) {
                methods.add(site.method());
            }
            // A declaration may live in a small helper called by the region
            // root.
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                methods.add(phase.declarationMethod());
            }
            instrumentationMethods = Collections.unmodifiableSet(methods);
            anchorMethods.remove(rootMethod);
            replayAnchorMethods = Collections.unmodifiableSet(anchorMethods);
        }

        static List<InstrumentationPlan> campaign(Path taskPlan,
                                                  String selectedTasks)
                throws IOException {
            if (taskPlan == null || !Files.isRegularFile(taskPlan)) {
                throw new IOException("Task plan not found: " + taskPlan);
            }
            Path normalized = taskPlan.toAbsolutePath().normalize();
            Set<String> selected = campaignTaskIds(selectedTasks);
            int maxTasks = maxCampaignTasks();
            List<InstrumentationPlan> campaign = new ArrayList<>();
            Set<String> covered = new LinkedHashSet<>();
            try (BufferedReader reader = Files.newBufferedReader(normalized,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    if (campaign.size() == maxTasks) {
                        throw new IOException("malformed plan: campaign in "
                                + normalized + " exceeds its bound of "
                                + maxTasks + " tasks");
                    }
                    ExecutionTask task = decodeRow(line, normalized);
                    if (!covered.add(task.taskId())) {
                        throw new IOException("malformed plan: duplicate "
                                + "execution task " + task.taskId() + " in "
                                + normalized);
                    }
                    if (!selected.contains(task.taskId())) {
                        throw new IOException("malformed plan: " + normalized
                                + " contains unselected task "
                                + task.taskId());
                    }
                    try {
                        campaign.add(new InstrumentationPlan(task));
                    } catch (RuntimeException malformed) {
                        throw new IOException("Malformed execution task "
                                + task.taskId(), malformed);
                    }
                }
            }
            if (campaign.isEmpty()) {
                throw new IOException("Execution task plan is empty: "
                        + normalized);
            }
            for (String taskId : selected) {
                if (!covered.contains(taskId)) {
                    throw new IOException("Selected execution task " + taskId
                            + " is absent in " + normalized);
                }
            }
            return Collections.unmodifiableList(campaign);
        }

        private static ExecutionTask decodeRow(String encoded, Path plan)
                throws IOException {
            try {
                JsonElement parsed = JsonParser.parseString(encoded);
                if (!parsed.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "execution task row must be an object");
                }
                return ExecutionTask.decode(parsed.getAsJsonObject());
            } catch (RuntimeException malformed) {
                throw new IOException("malformed plan: unreadable execution "
                        + "task row in " + plan, malformed);
            }
        }

        private static Set<String> campaignTaskIds(String selectedTasks)
                throws IOException {
            Set<String> ids = new LinkedHashSet<>();
            for (String value : stringValue(selectedTasks).split(",")) {
                String taskId = value.trim();
                if (taskId.isEmpty()) {
                    continue;
                }
                if (!ids.add(taskId)) {
                    throw new IOException("malformed plan: duplicate "
                            + "selected execution task " + taskId);
                }
            }
            if (ids.isEmpty()) {
                throw new IOException("Selected task id is required");
            }
            return ids;
        }

        private static int maxCampaignTasks() throws IOException {
            String configured = stringValue(System.getProperty(
                    MAX_TASKS_PROPERTY)).trim();
            if (configured.isEmpty()) {
                return DEFAULT_MAX_TASKS;
            }
            int value = intValue(configured, -1);
            if (value <= 0) {
                throw new IOException("malformed plan: " + MAX_TASKS_PROPERTY
                        + " must be a positive number");
            }
            return value;
        }

        String rootMethod() {
            return rootMethod;
        }

        String instrumentationSelector() {
            return instrumentationSelector;
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

        Set<String> fixedCountLoopSites() {
            return fixedCountLoopSites;
        }

        /** True when this region's activation is one loop iteration. */
        boolean loopBodyRoot() {
            return !rootLoopMethod.isEmpty();
        }

        /** The method holding the loop body this region is rooted at. */
        String rootLoopMethod() {
            return rootLoopMethod;
        }

        /** Original unit index of that loop's dominance-proved header. */
        int rootLoopHeaderUnitIndex() {
            return rootLoopHeaderUnitIndex;
        }

        /** Iteration-control sites the region's exits are installed on. */
        Set<String> rootLoopControlSites() {
            return rootLoopControlSites;
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

        List<CommunicationEffectCapture> communicationEffects() {
            return communicationEffects;
        }

        List<ExactHeapOutputCapture> exactHeapOutputs() {
            return exactHeapOutputs;
        }

        List<CommunicationHandoffSpec> communicationHandoffs() {
            return communicationHandoffs;
        }

        List<ConfiguredSourcePhaseContract.Occurrence>
        configuredSourcePhases() {
            return configuredSourcePhases;
        }

        Set<String> instrumentationMethods() {
            return instrumentationMethods;
        }

        /**
         * Whether this task's solver model selects a value by associative
         * access ordinal, and therefore needs an instrumented {@code Map} read
         * site to apply it.
         */
        boolean dynamicAssociativeTarget() {
            return dynamicAssociativeTarget;
        }

        /**
         * The methods this task's envelope may rewrite, before the replay
         * entry Soot selects is added to it. This is README section 1's per-
         * task envelope as the plan states it: the mandatory
         * target/region/RPC/SASL anchors, the closure the scheduler already
         * intersected with the seed trace and the current output closure, and
         * the exact alternative sites this task names.
         */
        Set<String> envelopeMethods() {
            Set<String> methods = replayDemandMethods();
            methods.add(rootMethod);
            methods.addAll(instrumentationMethods);
            if (!targetMethod.isEmpty()) methods.add(targetMethod);
            methods.addAll(replayAnchorMethods);
            methods.remove("");
            return methods;
        }

        /** The methods whose effects a delayed engine arm may not skip. */
        Set<String> replayDemandMethods() {
            Set<String> methods = new LinkedHashSet<>();
            methods.addAll(branches.methods());
            methods.addAll(materializations.localMethods());
            methods.addAll(materializations.methodArgumentMethods());
            methods.addAll(materializations.accessorCallerMethods());
            addCaptureMethods(methods, exactHeapOutputs);
            addCaptureMethods(methods, callArgumentOutputs);
            addCaptureMethods(methods, communicationEffects);
            for (CommunicationHandoffSpec handoff : communicationHandoffs) {
                methods.add(handoff.method());
            }
            methods.remove("");
            return methods;
        }

        private static boolean declaresDynamicAssociativeTarget(
                JsonArray modelAssignments) {
            for (JsonElement element : modelAssignments) {
                if (!element.isJsonObject()) continue;
                JsonElement encoded = element.getAsJsonObject()
                        .get("containerTarget");
                if (encoded == null || !encoded.isJsonObject()) continue;
                JsonObject container = encoded.getAsJsonObject();
                if ("ASSOCIATIVE".equals(string(container, "shape"))
                        && "ACCESS_ORDINAL".equals(
                        string(container, "selectorKind"))) {
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
                            string(action, "symbol"))) {
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
                // root receiver.
                if (match != null && "HEAP_OBJECT_FIELD".equals(
                        string(match, "location"))) {
                    if (!"SYMBOLIC".equals(string(match, "mode"))
                            || !"FIELD_ACCESS".equals(
                            string(match, "bindingMode"))) {
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

        private static void addCaptureMethods(Set<String> methods,
                Collection<? extends SpecCapture> captures) {
            for (SpecCapture capture : captures) {
                methods.add(capture.method());
            }
        }

        private static <T> List<T> selectedCaptures(
                List<OutputCaptureSpec> captures,
                Predicate<OutputCaptureSpec> selects,
                Function<OutputCaptureSpec, T> build) {
            List<T> result = new ArrayList<>();
            for (OutputCaptureSpec capture : captures) {
                if (selects.test(capture)) result.add(build.apply(capture));
            }
            return Collections.unmodifiableList(result);
        }
    }

    /** The accessors every {@link OutputCaptureSpec} view shares. */
    abstract static class SpecCapture {
        final OutputCaptureSpec capture;

        SpecCapture(OutputCaptureSpec capture) {
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
    }

    static final class ExactHeapOutputCapture extends SpecCapture {
        private ExactHeapOutputCapture(OutputCaptureSpec capture) {
            super(capture);
        }

        String fieldSignature() {
            return capture.fieldSignature();
        }

        List<String> fieldPath() {
            return capture.fieldPath();
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

    static final class CallArgumentOutputCapture extends SpecCapture {
        private CallArgumentOutputCapture(OutputCaptureSpec capture) {
            super(capture);
        }

        int argumentIndex() {
            return capture.argumentIndex();
        }
    }

    /** One semantic server method whose return emits a response event. */
    static final class CommunicationEffectCapture extends SpecCapture {
        private CommunicationEffectCapture(OutputCaptureSpec capture) {
            super(capture);
        }
    }

    static final class RootedOutputCapture extends SpecCapture {
        private final List<String> fieldPath;

        private RootedOutputCapture(OutputCaptureSpec capture,
                                    List<String> fieldPath) {
            super(capture);
            this.fieldPath = Collections.unmodifiableList(
                    new ArrayList<>(fieldPath));
        }

        String fieldSignature() {
            return capture.fieldSignature();
        }

        List<String> fieldPath() {
            return fieldPath;
        }
    }

    static final class ConcolicBranchSelection {
        private final Map<String, Set<Integer>> unitsByMethod =
                new LinkedHashMap<>();

        static ConcolicBranchSelection from(JsonArray branches) {
            ConcolicBranchSelection result = new ConcolicBranchSelection();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject branch = element.getAsJsonObject();
                String method = string(branch, "method");
                int unit = JsonFields.integer(branch, "unitIndex", -1);
                Matcher site = SITE_ID.matcher(
                        string(branch, "siteId"));
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

        /** Unions another task's branch sites into this one. */
        void mergeFrom(ConcolicBranchSelection other) {
            mergeSets(unitsByMethod, other.unitsByMethod);
        }

        int siteCount() {
            return totalSize(unitsByMethod);
        }
    }

    private static FieldTarget concolicFieldTarget(JsonObject action) {
        DeclaredField field = FieldPathSpec.declaredField(
                string(action, "accessFieldSignature"));
        return field == null ? null
                : new FieldTarget(field.owner(), field.name());
    }

    /**
     * The small set of concrete Jimple values that a scheduled activation asks
     * Soot to expose to the VM.
     */
    static final class ConcolicMaterializationSelection {
        private static final Pattern LOCAL = Pattern.compile(
                "^(<.+>)::([^#]+)(?:#.*)?$");
        private final Map<String, Map<String, Set<Integer>>> localsByMethod =
                new LinkedHashMap<>();
        private final Map<String, Set<Integer>> methodArguments =
                new LinkedHashMap<>();
        private final Map<String, FieldTarget> fields = new LinkedHashMap<>();
        /** Declarations whose writes publish selected shared-state versions. */
        private final Set<String> sharedCarrierFields =
                new LinkedHashSet<>();
        /** Exact read sites required only to admit concrete shared carriers. */
        private final Map<String, Map<Integer, Set<String>>>
                sharedCarrierFieldsBySite = new LinkedHashMap<>();
        private final Map<String, AccessorCallTarget> accessorCallsBySite =
                new LinkedHashMap<>();
        private boolean associativeContainerState;

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
            associativeContainerState |= "BOUNDED_CONTAINER_STATE".equals(
                    string(action, "symbolicDemand"))
                    && JavaContainerTypes.shape(string(action, "javaType"))
                    == JavaContainerTypes.Shape.ASSOCIATIVE;
            addAccessorCallTarget(action);
            String mode = string(action, "bindingMode");
            String cell = string(action, "cell");
            if ("METHOD_ARGUMENT".equals(mode)) {
                String method = string(action, "method");
                int index = integer(action, "index", -1);
                if (method.isEmpty() || index < 0) {
                    throw unsupported(action);
                }
                methodArguments.computeIfAbsent(method,
                        ignored -> new LinkedHashSet<>()).add(index);
                return;
            }
            if ("LOCAL_DEFINITION".equals(mode)) {
                String method = string(action, "method");
                String local = string(action, "local");
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
                                int site = integer(element.getAsJsonObject(),
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
            String location = string(action, "location");
            if (!"FIELD_ACCESS".equals(mode)
                    && !"HEAP_OBJECT_FIELD".equals(location)) {
                return;
            }
            FieldTarget target = concolicFieldTarget(action);
            if (target != null) {
                fields.put(target.owner + "|" + target.name, target);
            }
        }

        /**
         * A concrete input remains concrete, but an exact output capture that
         * names it as its anchor still needs the action's observation hook.
         * Select only those explicitly referenced anchors; unrelated concrete
         * inputs remain outside the instrumentation surface.
         */
        void addCapturePrerequisiteTargets(OutputClosureContract closure,
                                           JsonArray actions)
                throws IOException {
            if (closure == null) return;
            Set<String> anchors = new LinkedHashSet<>();
            for (OutputClosureContract.Member member : closure.members()) {
                collectCaptureAnchors(member.slice(), anchors);
            }
            if (anchors.isEmpty()) return;
            Set<String> found = new LinkedHashSet<>();
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                String symbol = string(action, "symbol");
                if (anchors.contains(symbol)) {
                    add(action);
                    found.add(symbol);
                }
            }
            anchors.removeAll(found);
            if (!anchors.isEmpty()) {
                throw new IOException("Output capture anchor has no input "
                        + "action: " + anchors.iterator().next());
            }
        }

        private static void collectCaptureAnchors(
                JsonObject slice, Set<String> anchors) {
            String anchor = string(slice, "captureAnchorPort");
            if (!anchor.isEmpty()) anchors.add(anchor);
            for (JsonElement element : JsonFields.array(
                    slice, "boundedVersionScopes")) {
                if (element.isJsonObject()) {
                    collectCaptureAnchors(element.getAsJsonObject(), anchors);
                }
            }
        }

        /**
         * Access-owner shared carriers use the same exact getfield hooks as a
         * heap materialization, but they are not themselves new symbolic
         * inputs.
         */
        void addSharedCarrierTargets(JsonArray carriers, JsonArray actions)
                throws IOException {
            Set<String> carrierFields = new LinkedHashSet<>();
            for (JsonElement element : carriers) {
                if (!element.isJsonObject()) continue;
                JsonObject carrier = element.getAsJsonObject();
                if (!"ACTIVATION_FIELD_RECEIVER".equals(
                        string(carrier, "sourceKind"))) {
                    continue;
                }
                String owner = string(carrier, "declaringClass");
                String name = string(carrier, "fieldName");
                if (owner.isEmpty() || name.isEmpty()) {
                    throw unsupported(carrier);
                }
                FieldTarget target = new FieldTarget(owner, name);
                String fieldKey = target.owner + "|" + target.name;
                carrierFields.add(fieldKey);
                sharedCarrierFields.add(fieldKey);
            }
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                FieldTarget target = concolicFieldTarget(action);
                if (target == null) continue;
                String fieldKey = target.owner + "|" + target.name;
                if (!carrierFields.contains(fieldKey)) continue;
                addSharedCarrierAccessSite(
                        string(action, "staticAccessSiteId"), fieldKey);
                addSharedCarrierAccessSite(
                        string(action, "siteId"), fieldKey);
                for (JsonElement site : JsonFields.array(
                        action, "accessSites")) {
                    if (site.isJsonPrimitive()) {
                        addSharedCarrierAccessSite(
                                site.getAsString(), fieldKey);
                    }
                }
            }
        }

        private void addSharedCarrierAccessSite(String encoded,
                                                String fieldKey) {
            Matcher site = SITE_ID.matcher(stringValue(encoded).trim());
            if (!site.matches()) return;
            int unit;
            try {
                unit = Integer.parseInt(site.group(2));
            } catch (RuntimeException malformed) {
                return;
            }
            sharedCarrierFieldsBySite
                    .computeIfAbsent(site.group(1),
                            ignored -> new LinkedHashMap<>())
                    .computeIfAbsent(unit, ignored -> new LinkedHashSet<>())
                    .add(fieldKey);
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
            String caller = string(action, "accessorCallerMethod");
            int unitIndex = integer(action, "accessorCallUnitIndex", -1);
            String callee = string(action, "accessorDeclaredCallee");
            String implementation = string(action,
                    "accessorImplementationMethod");
            boolean constrained = !caller.isEmpty() || unitIndex >= 0
                    || !callee.isEmpty() || !implementation.isEmpty();
            if (!constrained) return;
            if (caller.isEmpty() || unitIndex < 0 || callee.isEmpty()
                    || implementation.isEmpty()) {
                throw unsupported(action);
            }
            String site = CommunicationCatalogContract.siteId(caller,
                    unitIndex);

            String fieldSignature = string(action,
                    "accessFieldSignature");
            DeclaredField declaredField =
                    FieldPathSpec.declaredField(fieldSignature);
            if (declaredField == null) {
                throw unsupported(action);
            }
            AccessorCallTarget target = new AccessorCallTarget(caller,
                    unitIndex, site, callee, implementation, fieldSignature,
                    declaredField.name());
            if (conflicts(target)) {
                throw unsupported(action);
            }
        }

        /** Records {@code target}, or reports a conflicting holder. */
        private boolean conflicts(AccessorCallTarget target) {
            AccessorCallTarget previous = accessorCallsBySite.get(
                    target.callSiteId);
            if (previous != null) {
                return !previous.sameMaterialization(target);
            }
            accessorCallsBySite.put(target.callSiteId, target);
            return false;
        }

        private static IOException unsupported(JsonObject action) {
            return new IOException("Unsupported concolic materialization "
                    + string(action, "symbol"));
        }

        boolean isEmpty() {
            return localsByMethod.isEmpty() && methodArguments.isEmpty()
                    && fields.isEmpty()
                    && sharedCarrierFields.isEmpty()
                    && sharedCarrierFieldsBySite.isEmpty()
                    && accessorCallsBySite.isEmpty();
        }

        Set<String> sharedCarrierAccessMethods() {
            return sharedCarrierFieldsBySite.keySet();
        }

        boolean matchesWriteCarrier(SootFieldRef field) {
            return matchesSelectedField(field, true, "", -1);
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
            Set<Integer> sites = locals == null ? null : locals.get(local);
            return sites != null
                    && (sites.isEmpty() || sites.contains(unitIndex));
        }

        boolean matches(String method, int unitIndex, SootFieldRef field) {
            return matchesSelectedField(field, false, method, unitIndex);
        }

        private boolean matchesSelectedField(SootFieldRef field,
                                             boolean writeCarrier,
                                             String method, int unitIndex) {
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
            String fieldKey = owner + "|" + fieldName;
            Map<Integer, Set<String>> carrierSites = writeCarrier ? null
                    : sharedCarrierFieldsBySite.get(method);
            if (writeCarrier ? sharedCarrierFields.contains(fieldKey)
                    : carrierSites != null && carrierSites.getOrDefault(
                    unitIndex, Collections.emptySet()).contains(fieldKey)) {
                return true;
            }
            for (FieldTarget target : fields.values()) {
                if (target.name.equals(fieldName)
                        && (target.owner.isEmpty()
                        || target.owner.equals(owner))) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Unions another task's materialization selections into this one.
         *
         * <p>Every materialization hook the pipeline emits carries the site
         * it stands at - method, unit index, local or field - and no task id;
         * the runtime decides by which activation is admitted.  Two tasks
         * that name one site therefore want one rewrite, and instrumenting
         * per task inserted the same hook once per plan row.</p>
         */
        void mergeFrom(ConcolicMaterializationSelection other) {
            mergeNested(localsByMethod, other.localsByMethod);
            mergeSets(methodArguments, other.methodArguments);
            fields.putAll(other.fields);
            sharedCarrierFields.addAll(other.sharedCarrierFields);
            mergeNested(sharedCarrierFieldsBySite,
                    other.sharedCarrierFieldsBySite);
            associativeContainerState |= other.associativeContainerState;
            for (AccessorCallTarget target
                    : other.accessorCallsBySite.values()) {
                if (conflicts(target)) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_CAMPAIGN_CONFLICT: "
                                    + target.callSiteId);
                }
            }
        }

        /**
         * Whether this campaign named the exact bytecode site {@code
         * method#uUnit}. README section 1's first gate.
         */
        boolean selectedSite(String method, int unitIndex) {
            if (unitIndex < 0) return false;
            Map<String, Set<Integer>> locals = localsByMethod.get(method);
            if (locals != null) {
                for (Set<Integer> sites : locals.values()) {
                    if (sites.contains(unitIndex)) return true;
                }
            }
            return accessorCallsBySite.containsKey(
                    CommunicationCatalogContract.siteId(method, unitIndex));
        }

        boolean associativeContainerState() {
            return associativeContainerState;
        }

        /** Unique local-definition sites this campaign named. */
        int localSiteCount() {
            int sites = 0;
            for (Map<String, Set<Integer>> locals : localsByMethod.values()) {
                for (Set<Integer> units : locals.values()) {
                    sites += Math.max(1, units.size());
                }
            }
            return sites;
        }

        /** Unique method-argument slots this campaign named. */
        int methodArgumentCount() {
            return totalSize(methodArguments);
        }

        /** Unique declared fields this campaign named. */
        int fieldCount() {
            Set<String> selected = new LinkedHashSet<>(fields.keySet());
            selected.addAll(sharedCarrierFields);
            for (Map<Integer, Set<String>> sites
                    : sharedCarrierFieldsBySite.values()) {
                for (Set<String> fieldsAtSite : sites.values()) {
                    selected.addAll(fieldsAtSite);
                }
            }
            return selected.size();
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
            this.owner = JsonFields.firstNonBlank(owner);
            this.name = JsonFields.firstNonBlank(name);
        }
    }


    /** The project-wide {@code <method>#u<unitIndex>} site-id form. */
    private static final Pattern SITE_ID =
            Pattern.compile("^(<.*>)#u([0-9]+)$");

    private static int totalSize(Map<?, ? extends Collection<?>> byKey) {
        int total = 0;
        for (Collection<?> values : byKey.values()) {
            total += values.size();
        }
        return total;
    }

    private static <K, V> void mergeSets(Map<K, Set<V>> into,
                                         Map<K, Set<V>> from) {
        for (Map.Entry<K, Set<V>> entry : from.entrySet()) {
            into.computeIfAbsent(entry.getKey(),
                    ignored -> new LinkedHashSet<>())
                    .addAll(entry.getValue());
        }
    }

    private static <K, I, V> void mergeNested(Map<K, Map<I, Set<V>>> into,
                                              Map<K, Map<I, Set<V>>> from) {
        for (Map.Entry<K, Map<I, Set<V>>> entry : from.entrySet()) {
            mergeSets(into.computeIfAbsent(entry.getKey(),
                    ignored -> new LinkedHashMap<>()), entry.getValue());
        }
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
