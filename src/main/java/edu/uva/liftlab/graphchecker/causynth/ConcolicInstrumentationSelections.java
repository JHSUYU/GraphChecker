package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.JsonFields;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
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
public final class ConcolicInstrumentationSelections {
    private ConcolicInstrumentationSelections() {
    }

    /** Whether this JVM was asked to rewrite a scheduled concolic campaign. */
    public static boolean instrumentationRequested() {
        return Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                "false"));
    }

    /**
     * Declaring classes whose bodies the selected campaign may rewrite.
     *
     * <p>The full project roots remain on Soot's class path, but making every
     * class in those roots an application class forces Soot to load and emit
     * thousands of unrelated Hadoop classes.  The immutable task plan already
     * states the complete instrumentation envelope, so its declaring classes
     * are the narrow application set for this pass.</p>
     */
    public static Set<String> applicationClassesFromEnvironment() {
        Set<String> classes = new LinkedHashSet<>();
        for (InstrumentationPlan plan
                : instrumentationCampaignFromEnvironment()) {
            for (String signature : plan.envelopeMethods()) {
                String owner = declaringClass(signature);
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

    private static String declaringClass(String methodSignature) {
        String signature = stringValue(methodSignature).trim();
        if (!signature.startsWith("<")) return "";
        int colon = signature.indexOf(':');
        if (colon <= 1) return "";
        return signature.substring(1, colon).trim();
    }

    /**
     * How many tasks one instrumentation campaign may contain.  The bound
     * mirrors the runtime's: one pass instruments the union of the campaign's
     * regions, so an unbounded plan would rewrite an unbounded slice of the
     * program.
     */
    static final String MAX_TASKS_PROPERTY =
            "causynth.concolic.campaign.max.tasks";
    static final int DEFAULT_MAX_TASKS = 64;

    /**
     * The campaign this instrumentation pass must cover, in plan order.
     *
     * <p>One pass instruments the union of the campaign's regions, and each
     * task keeps its own selections: the runtime still admits an activation
     * per task by that task's own root predicate, so widening the
     * instrumentation does not widen selection.  A campaign of one is the
     * ordinary single-task run.</p>
     */
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

    /**
     * One immutable view of the scheduler-selected execution task. The
     * instrumentation pipeline builds this once and derives every selection
     * from it instead of reparsing the JSONL for each hook family.
     */
    static final class InstrumentationPlan {
        private final String taskId;
        /** Exact plan selector shared by a seed task and its replays. */
        private final String instrumentationSelector;
        private final String regionId;
        private final String rootMethod;
        private final String receiverClass;
        /** The region occurrence this plan is stated over. */
        private final String occurrenceId;
        private final ConcolicBranchSelection branches;
        private final LoopBoundPolicy loopBound;
        /** Array-indexed loops whose concrete cardinality is not a K_L. */
        private final Set<String> fixedCountLoopSites;
        private final ConcolicMaterializationSelection materializations;
        private final List<RootedOutputCapture> outputCaptures;
        private final List<CallArgumentOutputCapture> callArgumentOutputs;
        private final List<CommunicationEffectCapture> communicationEffects;
        private final List<ExactHeapOutputCapture> exactHeapOutputs;
        /**
         * Where this occurrence hands a declared communication port to the
         * VM, or takes one from it.  Both sites are the port's own static
         * declaration; the rewrite only puts the broker call there.
         */
        private final List<CommunicationHandoffSpec> communicationHandoffs;
        /** Complete replay-call catalog, including unselected landmarks. */
        private final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        private final Set<String> instrumentationMethods;
        private final Set<String> replayAnchorMethods;
        private final String targetMethod;
        private final boolean outputRelation;
        private final boolean dynamicAssociativeTarget;

        private InstrumentationPlan(ExecutionTask task) throws IOException {
            if (!task.executable()) {
                throw new IOException("Execution task " + task.taskId()
                        + " is not executable");
            }
            taskId = task.taskId();
            instrumentationSelector = task.instrumentationSelector();
            regionId = task.regionId();
            rootMethod = task.rootMethod();
            if (rootMethod.isEmpty()) {
                throw new IOException("Execution task " + task.taskId()
                        + " has no root method");
            }
            receiverClass = jsonString(task.rootSelector(), "receiverClass");
            occurrenceId = task.occurrenceId();
            InputActionCatalog inputActions = task.inputActions();
            JsonArray symbolic = inputActions.symbolic();
            targetMethod = task.targetMethod();
            outputRelation = task.outputClosure() != null;
            dynamicAssociativeTarget = declaresDynamicAssociativeTarget(
                    task.modelAssignments());
            branches = ConcolicBranchSelection.from(task.branches());
            loopBound = task.loopBound();
            fixedCountLoopSites = fixedCountLoopSites(task.json());
            materializations = ConcolicMaterializationSelection.from(symbolic);
            materializations.addSharedCarrierTargets(
                    task.sharedCarriers(), inputActions.all());
            outputCaptures = rootedOutputCaptures(task.outputCaptures(),
                    inputActions.all());
            callArgumentOutputs = callArgumentOutputCaptures(
                    task.outputCaptures());
            communicationEffects = communicationEffectCaptures(
                    task.outputCaptures());
            exactHeapOutputs = exactHeapOutputCaptures(
                    task.outputCaptures());
            communicationHandoffs = task.communicationHandoffs();
            configuredSourcePhases =
                    ConfiguredSourcePhaseContract.occurrencesOf(
                            task.json().get(
                                    ConfiguredSourcePhaseContract.PLAN_FIELD));

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
            for (CommunicationEffectCapture capture : communicationEffects) {
                methods.add(capture.method());
            }
            for (ExactHeapOutputCapture capture : exactHeapOutputs) {
                methods.add(capture.method());
            }
            // A concrete shared-state carrier is not a fresh symbolic input,
            // but its exact read still needs the materialization hook which
            // admits the planner-selected producer version.  The access site
            // comes from the frozen input action; adding only that method
            // keeps the instrumentation envelope bounded by the plan.
            methods.addAll(materializations.sharedCarrierAccessMethods());
            // A cut's own frame is where the port's value is presented and
            // received.  It is inside this occurrence by construction, so
            // selecting it adds the site and no transport frame.
            for (CommunicationHandoffSpec site : communicationHandoffs) {
                if (!site.manualCarrier()) methods.add(site.method());
            }
            // A declaration may live in a small helper called by the region
            // root. The replay validates the exact static hook site, so that
            // helper is part of the immutable instrumentation envelope even
            // when it is outside the producer's output slice. Unselected
            // phase rows remain no-op landmarks at runtime.
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

        String taskId() {
            return taskId;
        }

        String instrumentationSelector() {
            return instrumentationSelector;
        }

        String regionId() {
            return regionId;
        }

        String receiverClass() {
            return receiverClass;
        }

        /** The region occurrence this plan is stated over. */
        String occurrenceId() {
            return occurrenceId;
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

        Set<String> replayAnchorMethods() {
            return replayAnchorMethods;
        }


        String targetMethod() {
            return targetMethod;
        }

        boolean outputRelation() {
            return outputRelation;
        }

        /**
         * Whether this task's solver model selects a value by associative
         * access ordinal, and therefore needs an instrumented {@code Map}
         * read site to apply it.
         *
         * <p>The instrumenter uses this to decide whether a task with no
         * exact selected read site is a named coverage gap or simply a task
         * that never wanted one.  It is never permission to widen the
         * envelope: a task that wants a read site and names none stays a
         * reported gap.</p>
         */
        boolean dynamicAssociativeTarget() {
            return dynamicAssociativeTarget;
        }

        private static Set<String> fixedCountLoopSites(JsonObject task) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : JsonFields.array(
                    task, "retainedLoops")) {
                if (!element.isJsonObject()) continue;
                JsonObject loop = element.getAsJsonObject();
                if (!LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(
                        jsonString(loop,
                                LoopBoundPolicy.LOOP_CLASSIFICATION))) {
                    continue;
                }
                String primary = jsonString(
                        loop, LoopBoundPolicy.LOOP_SITE_ID);
                if (!primary.isEmpty()) result.add(primary);
                for (JsonElement site : JsonFields.array(
                        loop, LoopBoundPolicy.LOOP_CONTROL_SITE_IDS)) {
                    if (!site.isJsonPrimitive()) continue;
                    String value = site.getAsString().trim();
                    if (!value.isEmpty()) result.add(value);
                }
            }
            return Collections.unmodifiableSet(result);
        }

        /**
         * The methods this task's envelope may rewrite, before the replay
         * entry Soot selects is added to it.
         *
         * <p>This is README section 1's per-task envelope as the plan states
         * it: the mandatory target/region/RPC/SASL anchors, the closure the
         * scheduler already intersected with the seed trace and the current
         * output closure, and the exact alternative sites this task names.
         * Nothing else in the application belongs to it.</p>
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

        /**
         * The methods whose effects a delayed engine arm may not skip.
         *
         * <p>This is the envelope minus its anchors, and the distinction
         * matters: the arm selectors ask whether the declared target reaches
         * a demanded effect, and a set that contains the target itself
         * answers yes unconditionally - which would arm every output relation
         * at its target call rather than where its effects actually are.</p>
         */
        Set<String> replayDemandMethods() {
            Set<String> methods = new LinkedHashSet<>();
            methods.addAll(branches.methods());
            methods.addAll(materializations.localMethods());
            methods.addAll(materializations.methodArgumentMethods());
            methods.addAll(materializations.accessorCallerMethods());
            for (ExactHeapOutputCapture capture : exactHeapOutputs) {
                methods.add(capture.method());
            }
            for (CallArgumentOutputCapture capture : callArgumentOutputs) {
                methods.add(capture.method());
            }
            for (CommunicationEffectCapture capture : communicationEffects) {
                methods.add(capture.method());
            }
            for (CommunicationHandoffSpec handoff : communicationHandoffs) {
                if (!handoff.manualCarrier()) methods.add(handoff.method());
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
                if ("ASSOCIATIVE".equals(jsonString(container, "shape"))
                        && "ACCESS_ORDINAL".equals(
                        jsonString(container, "selectorKind"))) {
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

        private static List<CommunicationEffectCapture>
        communicationEffectCaptures(List<OutputCaptureSpec> captures) {
            List<CommunicationEffectCapture> result = new ArrayList<>();
            for (OutputCaptureSpec capture : captures) {
                if (capture.capturesCommunicationEffect()) {
                    result.add(new CommunicationEffectCapture(capture));
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

    /** One semantic server method whose return emits a response event. */
    static final class CommunicationEffectCapture {
        private final OutputCaptureSpec capture;

        private CommunicationEffectCapture(OutputCaptureSpec capture) {
            this.capture = capture;
        }

        String captureBindingId() {
            return capture.captureBindingId();
        }

        String method() {
            return capture.definitionMethod();
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

        /**
         * Unions another task's branch sites into this one.
         *
         * <p>A branch hook carries its method and unit, not a task id, so two
         * tasks naming the same site want one hook and not two.  Each task
         * still contributes only the exact alternative it named.</p>
         */
        void mergeFrom(ConcolicBranchSelection other) {
            for (Map.Entry<String, Set<Integer>> entry
                    : other.unitsByMethod.entrySet()) {
                unitsByMethod.computeIfAbsent(entry.getKey(),
                        ignored -> new LinkedHashSet<>())
                        .addAll(entry.getValue());
            }
        }

        int siteCount() {
            int sites = 0;
            for (Set<Integer> units : unitsByMethod.values()) {
                sites += units.size();
            }
            return sites;
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
        private static final Pattern FIELD_SITE = Pattern.compile(
                "^(<.+>)#u([0-9]+)$");
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
                fields.put(target.owner + "|" + target.name, target);
            }
        }

        /**
         * Access-owner shared carriers use the same exact getfield hooks as a
         * heap materialization, but they are not themselves new symbolic
         * inputs.  Register only their declared owner/name pair so Soot emits
         * the hook in this task's selected production methods; runtime
         * admission still decides whether the hook selects anything.
         */
        void addSharedCarrierTargets(JsonArray carriers, JsonArray actions)
                throws IOException {
            Set<String> carrierFields = new LinkedHashSet<>();
            for (JsonElement element : carriers) {
                if (!element.isJsonObject()) continue;
                JsonObject carrier = element.getAsJsonObject();
                if (!"ACTIVATION_FIELD_RECEIVER".equals(
                        jsonString(carrier, "sourceKind"))) {
                    continue;
                }
                String owner = jsonString(carrier, "declaringClass");
                String name = jsonString(carrier, "fieldName");
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
                        jsonString(action, "staticAccessSiteId"), fieldKey);
                addSharedCarrierAccessSite(
                        jsonString(action, "siteId"), fieldKey);
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
            Matcher site = FIELD_SITE.matcher(stringValue(encoded).trim());
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
                    && sharedCarrierFields.isEmpty()
                    && sharedCarrierFieldsBySite.isEmpty()
                    && accessorCallsBySite.isEmpty();
        }

        Set<String> sharedCarrierAccessMethods() {
            return sharedCarrierFieldsBySite.keySet();
        }

        boolean matchesSharedCarrierSite(String method, int unitIndex,
                                         String owner, String fieldName) {
            Map<Integer, Set<String>> sites =
                    sharedCarrierFieldsBySite.get(method);
            return sites != null
                    && sites.getOrDefault(unitIndex, Collections.emptySet())
                    .contains(stringValue(owner) + "|"
                            + stringValue(fieldName));
        }

        boolean selectsSharedCarrierDeclaration(String owner,
                                                 String fieldName) {
            return sharedCarrierFields.contains(stringValue(owner) + "|"
                    + stringValue(fieldName));
        }

        boolean matchesWriteCarrier(SootFieldRef field) {
            if (field == null) return false;
            SootField declared = CausynthStaticFacts.declaredField(field);
            SootClass declaringClass = declared == null
                    ? field.declaringClass() : declared.getDeclaringClass();
            String owner = declaringClass == null ? ""
                    : stringValue(declaringClass.getName());
            String fieldName = stringValue(declared == null
                    ? field.name() : declared.getName());
            if (sharedCarrierFields.contains(owner + "|" + fieldName)) {
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
            String fieldKey = owner + "|" + fieldName;
            Map<Integer, Set<String>> carrierSites =
                    sharedCarrierFieldsBySite.get(method);
            if (carrierSites != null
                    && carrierSites.getOrDefault(unitIndex,
                    Collections.emptySet()).contains(fieldKey)) {
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
            for (Map.Entry<String, Map<String, Set<Integer>>> method
                    : other.localsByMethod.entrySet()) {
                Map<String, Set<Integer>> locals = localsByMethod
                        .computeIfAbsent(method.getKey(),
                                ignored -> new LinkedHashMap<>());
                for (Map.Entry<String, Set<Integer>> local
                        : method.getValue().entrySet()) {
                    locals.computeIfAbsent(local.getKey(),
                            ignored -> new LinkedHashSet<>())
                            .addAll(local.getValue());
                }
            }
            for (Map.Entry<String, Set<Integer>> arguments
                    : other.methodArguments.entrySet()) {
                methodArguments.computeIfAbsent(arguments.getKey(),
                        ignored -> new LinkedHashSet<>())
                        .addAll(arguments.getValue());
            }
            fields.putAll(other.fields);
            sharedCarrierFields.addAll(other.sharedCarrierFields);
            for (Map.Entry<String, Map<Integer, Set<String>>> method
                    : other.sharedCarrierFieldsBySite.entrySet()) {
                Map<Integer, Set<String>> sites = sharedCarrierFieldsBySite
                        .computeIfAbsent(method.getKey(),
                                ignored -> new LinkedHashMap<>());
                for (Map.Entry<Integer, Set<String>> site
                        : method.getValue().entrySet()) {
                    sites.computeIfAbsent(site.getKey(),
                            ignored -> new LinkedHashSet<>())
                            .addAll(site.getValue());
                }
            }
            for (AccessorCallTarget target
                    : other.accessorCallsBySite.values()) {
                AccessorCallTarget previous = accessorCallsBySite.get(
                        target.callSiteId);
                if (previous != null
                        && !previous.sameMaterialization(target)) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_CAMPAIGN_CONFLICT: "
                                    + target.callSiteId);
                }
                if (previous == null) {
                    accessorCallsBySite.put(target.callSiteId, target);
                }
            }
        }

        /**
         * Whether this campaign named the exact bytecode site
         * {@code method#uUnit}.
         *
         * <p>README section 1's first gate.  A materialization that has no
         * declared owner - an associative read, whose hook takes only the
         * container and the key and so carries no site of its own - may be
         * emitted only where the plan already put a site.  A selected local
         * with no definition sites at all is deliberately not one: it names a
         * method, and a method is not a site.</p>
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
                    method + "#u" + unitIndex);
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
            int slots = 0;
            for (Set<Integer> indices : methodArguments.values()) {
                slots += indices.size();
            }
            return slots;
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
