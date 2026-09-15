package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import soot.PrimType;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethodRef;

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
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

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
        private final int rootLoopDemandedUnitIndex;
        private final Set<String> rootLoopControlSites;
        private final ConcolicMaterializationSelection materializations;
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
            InputActionCatalog inputActions = task.inputActions();
            JsonArray symbolic = inputActions.symbolic();
            targetMethod = task.targetMethod();
            branches = ConcolicBranchSelection.from(task.branches());
            branches.addLoopExitSites(task.retainedLoops());
            loopBound = task.loopBound();
            fixedCountLoopSites = task.fixedCountLoopSites();
            rootLoopMethod = task.rootLoopMethod();
            rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            rootLoopDemandedUnitIndex = task.rootLoopDemandedUnitIndex();
            rootLoopControlSites = task.rootLoopControlSites();
            materializations = ConcolicMaterializationSelection.from(symbolic);
            materializations.addObservedWriteSites(
                    task.observedWriteSites());
            communicationHandoffs = task.communicationHandoffs();
            configuredSourcePhases = task.configuredSourcePhases();

            LinkedHashSet<String> anchorMethods = new LinkedHashSet<>();
            if (!task.targetMethod().isEmpty()) {
                anchorMethods.add(task.targetMethod());
            }

            LinkedHashSet<String> methods = new LinkedHashSet<>();
            methods.add(rootMethod);
            methods.addAll(branches.methods());
            anchorMethods.addAll(branches.methods());
            // A cut's own frame is where the port's value is presented and
            // received.
            for (CommunicationHandoffSpec site : communicationHandoffs) {
                methods.add(site.method());
                // The frame is the one call that builds one instance of the
                // value the port belongs to; without its own body woven the
                // leaves inside it have nothing to be addressed within.
                if (!site.frameMethod().isEmpty()) {
                    methods.add(site.frameMethod());
                }
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
            // One bound, stated once: ConcolicTaskPlan owns the property
            // name, the default and the parse, and this pass bounds the
            // campaign it is about to rewrite by exactly the number the
            // replay JVM will bound the same plan by.  Two copies of the
            // same constant and the same parse is one place for them to
            // drift apart.
            int maxTasks = ExecutionTask.maxCampaignTasks();
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

        String rootMethod() {
            return rootMethod;
        }

        String instrumentationSelector() {
            return instrumentationSelector;
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

        /** Original unit the selected iteration must reach. */
        int rootLoopDemandedUnitIndex() {
            return rootLoopDemandedUnitIndex;
        }

        /** Iteration-control sites the region's exits are installed on. */
        Set<String> rootLoopControlSites() {
            return rootLoopControlSites;
        }

        ConcolicMaterializationSelection materializations() {
            return materializations;
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
         * The methods this task's envelope may rewrite, before the replay
         * entry Soot selects is added to it. This is README section 1's per-
         * task envelope as the plan states it: the mandatory target, region,
         * and communication anchors plus the exact sites this task names.
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
            for (CommunicationHandoffSpec handoff : communicationHandoffs) {
                methods.add(handoff.method());
            }
            methods.remove("");
            return methods;
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
                String method = optionalString(branch, "method");
                int unit = JsonFields.optionalInteger(branch, "unitIndex", -1);
                Matcher site = SITE_ID.matcher(
                        optionalString(branch, "siteId"));
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

        /** Loop exits are replay-address boundaries even when they add no SMT
         * predicate of their own. */
        private void addLoopExitSites(JsonArray retainedLoops) {
            for (JsonElement encodedLoop : retainedLoops) {
                if (encodedLoop == null || !encodedLoop.isJsonObject()) {
                    continue;
                }
                JsonElement encodedExits = encodedLoop.getAsJsonObject().get(
                        LoopBoundPolicy.LOOP_EXIT_DECISIONS);
                if (encodedExits == null || !encodedExits.isJsonArray()) {
                    continue;
                }
                for (JsonElement encodedExit : encodedExits.getAsJsonArray()) {
                    if (encodedExit == null || !encodedExit.isJsonObject()) {
                        continue;
                    }
                    Matcher site = SITE_ID.matcher(optionalString(
                            encodedExit.getAsJsonObject(), "siteId"));
                    if (site.matches()) {
                        unitsByMethod.computeIfAbsent(site.group(1),
                                ignored -> new LinkedHashSet<>()).add(
                                Integer.parseInt(site.group(2)));
                    }
                }
            }
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
    }

    private static FieldTarget concolicFieldTarget(JsonObject action) {
        DeclaredField field = FieldPathSpec.declaredField(
                optionalString(action, "accessFieldSignature"));
        return field == null ? null
                : new FieldTarget(field.owner(), field.name());
    }

    /**
     * The small set of concrete Jimple values that a scheduled activation asks
     * Soot to expose to the VM.
     */
    static final class ConcolicMaterializationSelection {
        /** Refusal verdict: a static final field is a replay-wide constant. */
        static final String STATIC_CONSTANT = "STATIC_CONSTANT";
        /** Refusal verdict: static shared state this pipeline cannot carry. */
        static final String STATIC_FIELD_UNSUPPORTED =
                "STATIC_FIELD_UNSUPPORTED";
        private static final Pattern LOCAL = Pattern.compile(
                "^(<.+>)::([^#]+)(?:#.*)?$");
        private final Map<String, Map<String, Set<Integer>>> localsByMethod =
                new LinkedHashMap<>();
        private final Map<String, Set<Integer>> methodArguments =
                new LinkedHashMap<>();
        private final Map<String, FieldTarget> fields = new LinkedHashMap<>();
        private final Map<String, AccessorCallTarget> accessorCallsBySite =
                new LinkedHashMap<>();
        /**
         * Stores of a declared input's cell the replay must observe, by site.
         *
         * <p>The plan decides these ({@code ExecutionTask
         * .observedWriteSites}); the pass rewrites each exactly once, and
         * the runtime hook is a no-op outside an active region.</p>
         */
        private final Map<String, ObservedWriteTarget> observedWritesBySite =
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
            FieldTarget fieldTarget = concolicFieldTarget(action);
            if (fieldTarget != null
                    && SharedFieldFlow.compilerSwitchDispatchField(
                    fieldTarget.name)) {
                // javac/ECJ rebuild their synthetic enum dispatch table at
                // class initialization. It is neither an application input
                // nor replay state, so emitting a field materializer would
                // incorrectly try to replace the compiler-owned int[].
                return;
            }
            addAccessorCallTarget(action);
            String mode = optionalString(action, "bindingMode");
            String cell = optionalString(action, "cell");
            if ("METHOD_ARGUMENT".equals(mode)) {
                String method = optionalString(action, "method");
                int index = optionalInteger(action, "index", -1);
                if (method.isEmpty() || index < 0) {
                    throw unsupported(action);
                }
                methodArguments.computeIfAbsent(method,
                        ignored -> new LinkedHashSet<>()).add(index);
                return;
            }
            if ("LOCAL_DEFINITION".equals(mode)) {
                String method = optionalString(action, "method");
                String local = optionalString(action, "local");
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
                                int site = optionalInteger(element.getAsJsonObject(),
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
            String location = optionalString(action, "location");
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
         * Registers the write sites the plan selected for observation.
         *
         * <p>A cell the VM retains by value has no version log until
         * something symbolic reaches it, so a store the plan selected
         * publishes nothing unless the location is observed first.  Each
         * entry names one bytecode site; a second task naming the same site
         * with a different cell is a plan the pass cannot execute and is
         * refused rather than silently merged.</p>
         */
        void addObservedWriteSites(JsonArray sites) throws IOException {
            for (JsonElement element : sites == null
                    ? new JsonArray() : sites) {
                if (!element.isJsonObject()) continue;
                JsonObject site = element.getAsJsonObject();
                String method = optionalString(site, "method");
                int unitIndex = optionalInteger(site, "unitIndex", -1);
                String siteId = optionalString(site, "siteId");
                String callee = optionalString(site, "declaredCallee");
                String cell = optionalString(site, "cell");
                if (method.isEmpty() || unitIndex < 0 || siteId.isEmpty()
                        || callee.isEmpty() || cell.isEmpty()
                        || !siteId.equals(SiteId.of(method, unitIndex))) {
                    throw unsupported(site);
                }
                ObservedWriteTarget target = new ObservedWriteTarget(method,
                        unitIndex, siteId, callee, cell);
                ObservedWriteTarget held =
                        observedWritesBySite.put(siteId, target);
                if (held != null && !held.sameObservation(target)) {
                    throw new IOException(
                            "OBSERVED_WRITE_SITE_CONFLICT: " + siteId);
                }
            }
        }

        /** The write sites this campaign observes, deduplicated. */
        Collection<ObservedWriteTarget> observedWrites() {
            return observedWritesBySite.values();
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
            String caller = optionalString(action, "accessorCallerMethod");
            int unitIndex = optionalInteger(action, "accessorCallUnitIndex", -1);
            String callee = optionalString(action, "accessorDeclaredCallee");
            String implementation = optionalString(action,
                    "accessorImplementationMethod");
            boolean constrained = !caller.isEmpty() || unitIndex >= 0
                    || !callee.isEmpty() || !implementation.isEmpty();
            if (!constrained) return;
            if (caller.isEmpty() || unitIndex < 0 || callee.isEmpty()
                    || implementation.isEmpty()) {
                throw unsupported(action);
            }
            String site = SiteId.of(caller,
                    unitIndex);

            String fieldSignature = optionalString(action,
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
                    + optionalString(action, "symbol"));
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
            Set<Integer> sites = locals == null ? null : locals.get(local);
            return sites != null
                    && (sites.isEmpty() || sites.contains(unitIndex));
        }

        boolean matches(String method, int unitIndex, SootFieldRef field) {
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
            boolean namedTarget = namedFieldTarget(owner, fieldName);
            if (field.isStatic()) {
                // A getstatic has no receiver object, so MATERIALIZE_FIELD
                // cannot stand at it: the only static read this pipeline can
                // materialize is the primitive round trip on the local that
                // consumed it. The rule governs BOTH authorities. Letting a
                // field named by a plan action through here handed
                // instrumentConsumedStaticPrimitiveFieldRead a site it could
                // only refuse, and the refusal killed the campaign -- it is
                // how a byte[] constant read reached the instrumenter at all.
                return field.type() instanceof PrimType && namedTarget;
            }
            return namedTarget;
        }

        /** Whether a plan action named this field, ignoring its shape. */
        private boolean namedFieldTarget(String owner, String fieldName) {
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
         * The verdict for one selected static field read the instrumenter
         * cannot materialize, or {@code ""} when there is nothing to refuse.
         *
         * <p>A {@code static final} field is a constant: nothing inside the
         * replayed process writes it, so it carries no shared state and
         * concretizing it deletes no evidence.  A static NON-final field is
         * shared state, and refusing it is a real coverage gap over the
         * dependency the plan selected it for -- so the two are reported
         * apart rather than under one "unsupported" name.</p>
         */
        String staticMaterializationRefusal(
                String method, int unitIndex, SootFieldRef field) {
            if (field == null || !field.isStatic()
                    || field.type() instanceof PrimType) {
                return "";
            }
            SootField declared = CausynthStaticFacts.declaredField(field);
            SootClass declaringClass = declared == null
                    ? field.declaringClass() : declared.getDeclaringClass();
            String owner = declaringClass == null ? ""
                    : stringValue(declaringClass.getName());
            String fieldName = stringValue(declared == null
                    ? field.name() : declared.getName());
            if (!namedFieldTarget(owner, fieldName)) {
                return "";
            }
            return declared != null && declared.isFinal()
                    ? STATIC_CONSTANT : STATIC_FIELD_UNSUPPORTED;
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
            for (ObservedWriteTarget target
                    : other.observedWritesBySite.values()) {
                ObservedWriteTarget held =
                        observedWritesBySite.put(target.siteId, target);
                if (held != null && !held.sameObservation(target)) {
                    throw new IllegalStateException(
                            "OBSERVED_WRITE_SITE_CAMPAIGN_CONFLICT: "
                                    + target.siteId);
                }
            }
            for (AccessorCallTarget target
                    : other.accessorCallsBySite.values()) {
                if (conflicts(target)) {
                    throw new IllegalStateException(
                            "ACCESSOR_CALLSITE_CAMPAIGN_CONFLICT: "
                                    + target.callSiteId);
                }
            }
        }
    }

    /** One store of a declared input's cell that the replay observes. */
    static final class ObservedWriteTarget {
        final String method;
        final int unitIndex;
        final String siteId;
        final String declaredCallee;
        final String cell;

        ObservedWriteTarget(String method, int unitIndex, String siteId,
                            String declaredCallee, String cell) {
            this.method = method;
            this.unitIndex = unitIndex;
            this.siteId = siteId;
            this.declaredCallee = declaredCallee;
            this.cell = cell;
        }

        boolean sameObservation(ObservedWriteTarget other) {
            return other != null && declaredCallee.equals(
                    other.declaredCallee) && cell.equals(other.cell);
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

    static String firstNonBlank(String... values) {
        String value = JsonFields.firstNonBlank(values);
        return value.isEmpty() ? null : value;
    }
}
