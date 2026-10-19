package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
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
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
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

public final class ConcolicInstrumentationSelections {
    private ConcolicInstrumentationSelections() {
    }

    public static boolean instrumentationRequested() {
        return Boolean.parseBoolean(JsonFields.firstNonBlank(
                System.getProperty("causynth.instrument.concolic"),
                "false"));
    }

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

    static String weaveKeyFromEnvironment() {
        MessageDigest digest = ArtifactIO.sha256Digest();
        Set<String> seen = new LinkedHashSet<>();
        for (InstrumentationPlan plan
                : instrumentationCampaignFromEnvironment()) {
            StringBuilder value = new StringBuilder();
            canonical(plan, value);
            byte[] encoded = value.append('\n').toString()
                    .getBytes(StandardCharsets.UTF_8);
            if (seen.add(ArtifactIO.hex(ArtifactIO.sha256Digest()
                    .digest(encoded)))) {
                digest.update(encoded);
            }
        }
        return ArtifactIO.hex(digest.digest());
    }

    static void canonical(Object value, StringBuilder out) {
        if (value == null) {
            out.append("null");
        } else if (value instanceof CharSequence) {
            out.append(new JsonPrimitive(value.toString()));
        } else if (value instanceof Number || value instanceof Boolean
                || value instanceof Character) {
            out.append(value.getClass().getName()).append(':').append(value);
        } else if (value instanceof Enum) {
            out.append(((Enum<?>) value).getDeclaringClass().getName())
                    .append(':').append(((Enum<?>) value).name());
        } else if (value instanceof JsonElement) {
            out.append(value);
        } else if (value instanceof Map) {
            out.append('{');
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                canonical(entry.getKey(), out);
                out.append(':');
                canonical(entry.getValue(), out);
                out.append(',');
            }
            out.append('}');
        } else if (value instanceof Collection) {
            out.append('[');
            for (Object element : (Collection<?>) value) {
                canonical(element, out);
                out.append(',');
            }
            out.append(']');
        } else {
            Class<?> type = value.getClass();
            if (!type.getName().startsWith("edu.uva.liftlab.graphchecker.")) {
                throw new IllegalStateException("WEAVE_KEY_UNVOUCHED: a "
                        + "plan value of " + type.getName()
                        + " is no engine value the key can read");
            }
            List<Field> fields = new ArrayList<>();
            for (Class<?> owner = type; owner != Object.class;
                 owner = owner.getSuperclass()) {
                for (Field field : owner.getDeclaredFields()) {
                    if (!Modifier.isStatic(field.getModifiers())
                            && !field.isSynthetic()) {
                        fields.add(field);
                    }
                }
            }
            fields.sort(Comparator.comparing((Field field) ->
                    field.getDeclaringClass().getName() + "#"
                            + field.getName()));
            out.append(type.getName()).append('{');
            for (Field field : fields) {
                field.setAccessible(true);
                out.append(field.getName()).append('=');
                try {
                    canonical(field.get(value), out);
                } catch (IllegalAccessException unreadable) {
                    throw new IllegalStateException(unreadable);
                }
                out.append(';');
            }
            out.append('}');
        }
    }

    static final class InstrumentationPlan {
        private final String rootHookGroup;
        private final String loopRootHookGroup;
        private final String rootMethod;
        private final Set<String> branchMethods;
        private final LoopBoundPolicy loopBound;
        private final Set<String> fixedCountLoopSites;
        private final String rootLoopMethod;
        private final int rootLoopHeaderUnitIndex;
        private final int rootLoopDemandedUnitIndex;
        private final Set<String> rootLoopControlSites;
        private final ConcolicMaterializationSelection materializations;
        private final List<CommunicationHandoffSpec> communicationHandoffs;
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
            communicationHandoffs = task.communicationHandoffs();
            configuredSourcePhases = task.configuredSourcePhases();

            LinkedHashSet<String> methods = new LinkedHashSet<>();
            methods.add(rootMethod);
            methods.addAll(branchMethods);
            for (CommunicationHandoffSpec site : communicationHandoffs) {
                methods.add(site.method());
            }
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

        int rootLoopHeaderUnitIndex() {
            return rootLoopHeaderUnitIndex;
        }

        int rootLoopDemandedUnitIndex() {
            return rootLoopDemandedUnitIndex;
        }

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
        private final Map<String, ObservedSite> observedSitesBySite =
                new LinkedHashMap<>();

        static ConcolicMaterializationSelection observed(JsonArray sites)
                throws IOException {
            ConcolicMaterializationSelection result =
                    new ConcolicMaterializationSelection();
            result.addObservedSites(sites);
            return result;
        }

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
                boolean provenance = site.has("provenance")
                        && site.get("provenance").getAsBoolean();
                if (method.isEmpty() || unitIndex < 0 || siteId.isEmpty()
                        || cell.isEmpty() || !field && !container
                        && !provenance
                        || !siteId.equals(SiteId.of(method, unitIndex))) {
                    throw unsupported(site);
                }
                if (conflicts(new ObservedSite(method, unitIndex,
                        siteId, callee, cell, read, staticField, field,
                        container, provenance))) {
                    throw new IOException(
                            "OBSERVED_SITE_CONFLICT: " + siteId);
                }
            }
        }

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
            locals.computeIfAbsent(local, ignored -> new LinkedHashSet<>())
                    .add(unitIndex >= 0 ? unitIndex : ANY_SITE);
        }

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

    static final class ObservedSite {
        final String method;
        final int unitIndex;
        final String siteId;
        final String declaredCallee;
        final String cell;
        final boolean read;
        final boolean staticField;
        final boolean field;
        final boolean container;
        final boolean provenance;

        ObservedSite(String method, int unitIndex, String siteId,
                     String declaredCallee, String cell, boolean read,
                     boolean staticField, boolean field, boolean container,
                     boolean provenance) {
            this.method = method;
            this.unitIndex = unitIndex;
            this.siteId = siteId;
            this.declaredCallee = declaredCallee;
            this.cell = cell;
            this.read = read;
            this.staticField = staticField;
            this.field = field;
            this.container = container;
            this.provenance = provenance;
        }

        boolean sameObservation(ObservedSite other) {
            return other != null && declaredCallee.equals(
                    other.declaredCallee) && cell.equals(other.cell)
                    && read == other.read
                    && staticField == other.staticField
                    && field == other.field && container == other.container
                    && provenance == other.provenance;
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
