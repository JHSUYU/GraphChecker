package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import soot.PrimType;
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
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Execution-task parsing and immutable instrumentation selections. */
public final class ConcolicInstrumentationSelections {
    private ConcolicInstrumentationSelections() {
    }

    /** Whether this JVM was asked to rewrite a scheduled concolic campaign. */
    public static boolean instrumentationRequested() {
        return Boolean.parseBoolean(JsonFields.firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                "false"));
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
        /** The woven entry this task's region opens at
         *  ({@code ExecutionTask#rootHookGroup}). */
        private final String rootHookGroup;
        /** The enclosing entry a loop-body root's iterations are addressed
         *  under, else "" ({@code ExecutionTask#loopRootHookGroup}). */
        private final String loopRootHookGroup;
        private final String rootMethod;
        /** Methods whose conditional branches this task's weave covers. */
        private final Set<String> branchMethods;
        private final LoopBoundPolicy loopBound;
        /** Array-indexed loops whose concrete cardinality is not a K_L. */
        private final Set<String> fixedCountLoopSites;
        /**
         * The re-rooted loop body's method, or empty; see
         * {@link LoopBoundPolicy#LOOP_BODY_ROOT}.
         */
        private final String rootLoopMethod;
        private final int rootLoopHeaderUnitIndex;
        private final int rootLoopDemandedUnitIndex;
        private final Set<String> rootLoopControlSites;
        private final ConcolicMaterializationSelection materializations;
        /** Where this occurrence hands a port to the VM or takes one. */
        private final List<CommunicationHandoffSpec> communicationHandoffs;
        /** Complete replay-call catalog, including unselected landmarks. */
        private final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        private final Set<String> instrumentationMethods;
        private final String targetMethod;

        private InstrumentationPlan(ExecutionTask task) throws IOException {
            if (!task.executable()) {
                throw new IOException("Execution task " + task.taskId()
                        + " is not executable");
            }
            rootHookGroup = task.rootHookGroup();
            loopRootHookGroup = task.loopRootHookGroup();
            rootMethod = task.rootMethod();
            if (rootMethod.isEmpty()) {
                throw new IOException("Execution task " + task.taskId()
                        + " has no root method");
            }
            InputActionCatalog inputActions = task.inputActions();
            JsonArray symbolic = inputActions.symbolic();
            targetMethod = task.targetMethod();
            branchMethods = branchMethodsOf(task);
            loopBound = task.loopBound();
            fixedCountLoopSites = task.fixedCountLoopSites();
            rootLoopMethod = task.rootLoopMethod();
            rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            rootLoopDemandedUnitIndex = task.rootLoopDemandedUnitIndex();
            rootLoopControlSites = task.rootLoopControlSites();
            materializations = ConcolicMaterializationSelection.from(symbolic);
            materializations.addObservedSites(
                    task.observedSites());
            communicationHandoffs = task.communicationHandoffs();
            configuredSourcePhases = task.configuredSourcePhases();

            LinkedHashSet<String> methods = new LinkedHashSet<>();
            methods.add(rootMethod);
            methods.addAll(branchMethods);
            for (CommunicationHandoffSpec site : communicationHandoffs) {
                methods.add(site.method());
                // The frame is woven too: its leaves are addressed within it.
                if (!site.frameMethod().isEmpty()) {
                    methods.add(site.frameMethod());
                }
            }
            // A declaration may live in a helper the root calls.
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                methods.add(phase.declarationMethod());
            }
            instrumentationMethods = Collections.unmodifiableSet(methods);
        }

        static List<InstrumentationPlan> campaign(Path taskPlan,
                                                  String selectedTasks)
                throws IOException {
            if (taskPlan == null || !Files.isRegularFile(taskPlan)) {
                throw new IOException("Task plan not found: " + taskPlan);
            }
            Path normalized = taskPlan.toAbsolutePath().normalize();
            Set<String> selected = campaignTaskIds(selectedTasks);
            // The same bound the replay JVM applies; never a second copy.
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

        String rootHookGroup() {
            return rootHookGroup;
        }

        String loopRootHookGroup() {
            return loopRootHookGroup;
        }

        /**
         * The named branch methods plus every retained loop's exit-decision
         * owners (replay-address boundaries even without an SMT predicate).
         */
        private static Set<String> branchMethodsOf(ExecutionTask task) {
            Set<String> methods = new LinkedHashSet<>();
            for (JsonElement element : task.branchMethods()) {
                if (element.isJsonPrimitive()) {
                    methods.add(element.getAsString().trim());
                }
            }
            for (JsonElement encodedLoop : task.retainedLoops()) {
                if (encodedLoop == null || !encodedLoop.isJsonObject()) {
                    continue;
                }
                JsonElement encodedExits = encodedLoop.getAsJsonObject().get(
                        LoopBoundPolicy.LOOP_EXIT_DECISIONS);
                if (encodedExits == null || !encodedExits.isJsonArray()) {
                    continue;
                }
                for (JsonElement encodedExit
                        : encodedExits.getAsJsonArray()) {
                    if (encodedExit == null
                            || !encodedExit.isJsonObject()) {
                        continue;
                    }
                    methods.add(SiteId.methodOf(optionalString(
                            encodedExit.getAsJsonObject(), "siteId")));
                }
            }
            methods.remove("");
            return Collections.unmodifiableSet(methods);
        }

        LoopBoundPolicy loopBound() {
            return loopBound;
        }

        Set<String> fixedCountLoopSites() {
            return fixedCountLoopSites;
        }

        boolean loopBodyRoot() {
            return !rootLoopMethod.isEmpty();
        }

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
         * The per-task envelope, before the replay entry: the
         * methods whose effects a delayed engine arm may not skip, then the
         * root, the instrumented methods and the target.
         */
        Set<String> envelopeMethods() {
            Set<String> methods = new LinkedHashSet<>(branchMethods);
            methods.addAll(materializations.localMethods());
            methods.addAll(materializations.methodArgumentMethods());
            methods.addAll(materializations.accessorCallerMethods());
            for (CommunicationHandoffSpec handoff : communicationHandoffs) {
                methods.add(handoff.method());
            }
            methods.add(rootMethod);
            methods.addAll(instrumentationMethods);
            if (!targetMethod.isEmpty()) methods.add(targetMethod);
            methods.remove("");
            return methods;
        }

    }

    private static FieldTarget concolicFieldTarget(JsonObject action) {
        DeclaredField field = FieldPathSpec.declaredField(
                optionalString(action, "accessFieldSignature"));
        return field == null ? null
                : new FieldTarget(field.owner(), field.name());
    }

    /** The concrete Jimple values a scheduled activation exposes to the VM. */
    static final class ConcolicMaterializationSelection {
        private static final Pattern LOCAL = Pattern.compile(
                "^(<.+>)::([^#]+)(?:#.*)?$");
        private final Map<String, Map<String, Set<Integer>>> localsByMethod =
                new LinkedHashMap<>();
        private final Map<String, Set<Integer>> methodArguments =
                new LinkedHashMap<>();
        private final Map<String, FieldTarget> fields = new LinkedHashMap<>();
        private final Map<String, AccessorCallTarget> accessorCallsBySite =
                new LinkedHashMap<>();
        /** Planned observed stores of a declared input's cell, by site. */
        private final Map<String, ObservedSite> observedSitesBySite =
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

        private void add(JsonObject action) throws IOException {
            FieldTarget fieldTarget = concolicFieldTarget(action);
            if (fieldTarget != null
                    && SharedFieldFlow.compilerSwitchDispatchField(
                    fieldTarget.name)) {
                // A compiler switch-map table is neither input nor state.
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
                    method = JsonFields.firstNonBlank(method, matcher.group(1));
                    local = JsonFields.firstNonBlank(local, matcher.group(2));
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
            if (fieldTarget != null) {
                fields.put(fieldTarget.owner + "|" + fieldTarget.name,
                        fieldTarget);
            }
        }

        /**
         * Registers the planned observed sites of tracked cells (a by-value
         * cell has no version log until observed): a call storing into an
         * atomic's value, a {@code putfield} ({@code declaredCallee} empty),
         * or a {@code getfield} ({@code read}), each observing its cell
         * ({@code field}); and a read of a cell holding a container or a
         * container mutation through one, observing that container's state
         * ({@code container}).  One site naming two cells is refused, and so
         * is a row observing nothing.
         */
        private void addObservedSites(JsonArray sites)
                throws IOException {
            for (JsonElement element : sites == null
                    ? new JsonArray() : sites) {
                if (!element.isJsonObject()) continue;
                JsonObject site = element.getAsJsonObject();
                String method = optionalString(site, "method");
                int unitIndex = optionalInteger(site, "unitIndex", -1);
                String siteId = optionalString(site, "siteId");
                String callee = optionalString(site, "declaredCallee");
                String cell = optionalString(site, "cell");
                boolean read = site.has("read")
                        && site.get("read").getAsBoolean();
                boolean staticField = site.has("static")
                        && site.get("static").getAsBoolean();
                boolean field = site.has("field")
                        && site.get("field").getAsBoolean();
                boolean container = site.has("container")
                        && site.get("container").getAsBoolean();
                if (method.isEmpty() || unitIndex < 0 || siteId.isEmpty()
                        || cell.isEmpty() || !field && !container
                        || !siteId.equals(SiteId.of(method, unitIndex))) {
                    throw unsupported(site);
                }
                if (conflicts(new ObservedSite(method, unitIndex,
                        siteId, callee, cell, read, staticField, field,
                        container))) {
                    throw new IOException(
                            "OBSERVED_SITE_CONFLICT: " + siteId);
                }
            }
        }

        /** Records {@code target}; true when a different one holds its site. */
        private boolean conflicts(ObservedSite target) {
            ObservedSite held = observedSitesBySite.putIfAbsent(
                    target.siteId, target);
            return held != null && !held.sameObservation(target);
        }

        Collection<ObservedSite> observedSites() {
            return observedSitesBySite.values();
        }

        private void addLocal(String method, String local, int unitIndex) {
            Map<String, Set<Integer>> locals =
                    localsByMethod.computeIfAbsent(method,
                            ignored -> new LinkedHashMap<>());
            // ANY_SITE is a member, not an empty set: a union with one
            // site must not narrow "any" to it.
            locals.computeIfAbsent(local, ignored -> new LinkedHashSet<>())
                    .add(unitIndex >= 0 ? unitIndex : ANY_SITE);
        }

        /** A local selected at every definition site. */
        private static final int ANY_SITE = -1;

        private void addAccessorCallTarget(JsonObject action)
                throws IOException {
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

        /** Records {@code target}; true when a different one holds its site. */
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
                    && (sites.contains(ANY_SITE) || sites.contains(unitIndex));
        }

        /**
         * Whether a plan action named this field, by the class declaring it,
         * in a shape a hook can carry.  A getstatic has no receiver: only a
         * primitive static read is materializable (on its consuming local);
         * any other stays concrete, not refused, or it would kill the whole
         * campaign.
         */
        boolean matches(SootFieldRef field) {
            if (field.isStatic() && !(field.type() instanceof PrimType)) {
                return false;
            }
            SootField declared = CausynthStaticFacts.declaredField(field);
            SootClass declaringClass = declared == null
                    ? field.declaringClass() : declared.getDeclaringClass();
            String owner = declaringClass == null ? ""
                    : stringValue(declaringClass.getName());
            String fieldName = stringValue(declared == null
                    ? field.name() : declared.getName());
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
         * Unions another task's selections: hooks are keyed by site, not task,
         * so two tasks naming one site want one rewrite.
         */
        void mergeFrom(ConcolicMaterializationSelection other) {
            mergeNested(localsByMethod, other.localsByMethod);
            mergeSets(methodArguments, other.methodArguments);
            fields.putAll(other.fields);
            for (ObservedSite target
                    : other.observedSitesBySite.values()) {
                if (conflicts(target)) {
                    throw new IllegalStateException(
                            "OBSERVED_SITE_CAMPAIGN_CONFLICT: "
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

    /** One access of a tracked cell that the replay observes. */
    static final class ObservedSite {
        final String method;
        final int unitIndex;
        final String siteId;
        final String declaredCallee;
        final String cell;
        /** A read ({@code getfield}/{@code getstatic}) rather than a store. */
        final boolean read;
        /** A static cell: observed on its declaring class's mirror. */
        final boolean staticField;
        /** The cell, on its holder, before the access. */
        final boolean field;
        /** The state of the container the access reaches: after a read, on
         *  its referent; before a mutator call, on its receiver. */
        final boolean container;

        ObservedSite(String method, int unitIndex, String siteId,
                     String declaredCallee, String cell, boolean read,
                     boolean staticField, boolean field, boolean container) {
            this.method = method;
            this.unitIndex = unitIndex;
            this.siteId = siteId;
            this.declaredCallee = declaredCallee;
            this.cell = cell;
            this.read = read;
            this.staticField = staticField;
            this.field = field;
            this.container = container;
        }

        boolean sameObservation(ObservedSite other) {
            return other != null && declaredCallee.equals(
                    other.declaredCallee) && cell.equals(other.cell)
                    && read == other.read
                    && staticField == other.staticField
                    && field == other.field && container == other.container;
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

}
