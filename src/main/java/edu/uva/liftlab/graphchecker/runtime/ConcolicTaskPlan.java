package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.ForcingTable;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.taskUnanswered;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

final class ConcolicTaskPlan {
    private static final Object LOCK = new Object();
    private static volatile ConcolicTaskPlan plan;

    static ConcolicTaskPlan configuration() {
        ConcolicTaskPlan current = plan;
        if (current != null) {
            return current;
        }
        synchronized (LOCK) {
            if (plan == null) {
                plan = ConcolicTaskPlan.load();
            }
            return plan;
        }
    }

    final Path resultFile;
    final List<RuntimeTask> tasks;
    final boolean[] candidateLive;
    final boolean[] occurrenceClaimed;
    private final boolean[] answeredByShape;
    private final Map<RuntimeTask, Integer> slots =
            new IdentityHashMap<RuntimeTask, Integer>();
    private final Map<String, String> loopRoots =
            new HashMap<String, String>();
    final Map<String, List<String>> chainKeys =
            new HashMap<String, List<String>>();
    boolean unansweredAddressesPublished;

    ConfiguredSourcePhaseContract.Occurrence declaredPhase(String sourceId) {
        for (RuntimeTask task : tasks) {
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : task.configuredSourcePhases) {
                if (phase.sourceId().equals(sourceId)) return phase;
            }
        }
        return null;
    }

    ConcolicTaskPlan(Path resultFile, List<RuntimeTask> tasks) {
        this.resultFile = resultFile;
        this.tasks = Collections.unmodifiableList(tasks);
        for (RuntimeTask task : tasks) {
            loopRoots.put(task.rootHookGroup, task.loopRootHookGroup);
            if (task.contentKeys == null) continue;
            for (Map.Entry<String, List<String>> keyed
                    : task.contentKeys.entrySet()) {
                List<String> held = chainKeys.computeIfAbsent(
                        keyed.getKey(), slot -> new ArrayList<String>());
                for (String prefix : keyed.getValue()) {
                    if (!held.contains(prefix)) held.add(prefix);
                }
            }
        }
        this.candidateLive = new boolean[tasks.size()];
        this.occurrenceClaimed = new boolean[tasks.size()];
        this.answeredByShape = new boolean[tasks.size()];
        for (int index = 0; index < this.tasks.size(); index++) {
            this.slots.put(this.tasks.get(index), index);
        }
    }


    synchronized void releaseCandidate(RuntimeTask task) {
        Integer index = slots.get(task);
        if (index != null) candidateLive[index] = false;
    }

    void publishUnansweredAddresses() {
        List<RuntimeTask> unanswered = new ArrayList<RuntimeTask>();
        synchronized (this) {
            if (unansweredAddressesPublished) return;
            unansweredAddressesPublished = true;
            for (int index = 0; index < tasks.size(); index++) {
                if (occurrenceClaimed[index]) continue;
                unanswered.add(tasks.get(index));
            }
        }
        for (RuntimeTask task : unanswered) {
            if (task.unaddressedCandidates == 0) {
                taskUnanswered(task, "ROOT_NEVER_EXECUTED: the planned root"
                        + " did not execute in this replay: no compatible"
                        + " activation was offered for "
                        + task.occurrenceId);
                continue;
            }
            taskUnanswered(task, (task.rootContextSelector
                            .anchorSourceNeverExisted()
                            ? "ANCHOR_EPOCH_NOT_REACHED: "
                            : "OCCURRENCE_ANCHOR_UNMATCHED: ")
                    + task.unansweredAddress());
        }
    }

    static final class RefusedCandidate {
        private final String said;
        private final OccurrenceAddress observed;
        private final String attribution;
        private final String thread;

        private RefusedCandidate(String said, OccurrenceAddress observed,
                                 String attribution) {
            this.said = nonNull(said);
            this.observed = observed;
            this.attribution = nonNull(attribution);
            this.thread = Thread.currentThread().getName();
        }

        static RefusedCandidate onAddress(String said,
                                          OccurrenceAddress observed,
                                          SourceRef activationSource) {
            return new RefusedCandidate(said, observed,
                    attribution(activationSource == null ? ""
                            : activationSource.key()));
        }

        static RefusedCandidate stated(String said,
                                       SourceRef activationSource) {
            return new RefusedCandidate(said, null,
                    attribution(activationSource == null ? ""
                            : activationSource.key()));
        }

        String render(RuntimeTask task) {
            String stated = (observed == null ? said
                    : said + ": " + task.addressDifference(observed))
                    + attribution;
            return stated.trim() + " [thread=" + thread + "]";
        }

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof RefusedCandidate)) return false;
            RefusedCandidate other = (RefusedCandidate) value;
            return said.equals(other.said)
                    && thread.equals(other.thread)
                    && attribution.equals(other.attribution)
                    && (observed == null ? other.observed == null
                    : observed.equals(other.observed));
        }

        @Override
        public int hashCode() {
            return Objects.hash(said, thread, attribution, observed);
        }
    }

    synchronized boolean answeredByShape(RuntimeTask task) {
        Integer index = slots.get(task);
        return index != null && answeredByShape[index];
    }

    synchronized void markOccurrenceClaimed(RuntimeTask task) {
        Integer index = slots.get(task);
        if (index != null) occurrenceClaimed[index] = true;
    }

    String loopRootOf(String rootHookGroup) {
        String loopRoot = loopRoots.get(rootHookGroup);
        return loopRoot == null ? "" : loopRoot;
    }

    static final class LoopRootAdmission {
        final Set<String> admitted;
        final RuntimeTask answered;

        private LoopRootAdmission(Set<String> admitted, RuntimeTask answered) {
            this.admitted = Collections.unmodifiableSet(admitted);
            this.answered = answered;
        }
    }

    synchronized LoopRootAdmission addressLoopRootInvocation(
            String loopRootHookGroup, String rootMethod,
            Object receiver, Object[] rootArguments,
            long enclosingInvocationEvent) {
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);
        Set<String> admitted = new LinkedHashSet<>();
        if (!RecordingWindow.opened()) {
            return new LoopRootAdmission(admitted, null);
        }
        ObservedAddresses observedAddresses = new ObservedAddresses();
        Function<CausalContext, List<String>> shapes = AnswerOrder.shapes();
        RuntimeTask answering = null;
        RefusedCandidate answered = null;
        for (RuntimeTask task : tasks) {
            if (!task.loopBodyRoot
                    || !task.loopRootHookGroup.equals(
                    nonNull(loopRootHookGroup))) {
                continue;
            }
            RefusedCandidate refused = refusal(task, true, rootMethod,
                    task.enclosingRootArgumentSelector, receiver,
                    rootArguments, activationSource, observedAddresses);
            if (refused != null) {
                boolean shaped = task.answers(refused.observed, shapes);
                if (shaped && task.enclosingInvocationEvent() != 0L) {
                    task.noteUnaddressedCandidate(secondInvocation(task,
                            activationSource));
                    continue;
                }
                if (shaped && (answering == null
                        || AnswerOrder.earlier(task, answering))) {
                    if (answering != null) {
                        answering.noteUnaddressedCandidate(answered);
                    }
                    answering = task;
                    answered = refused;
                    continue;
                }
                task.noteUnaddressedCandidate(refused);
                continue;
            }
            if (!task.claimsEnclosingInvocation(enclosingInvocationEvent)) {
                task.noteUnaddressedCandidate(secondInvocation(task,
                        activationSource));
                continue;
            }
            admitted.add(task.taskId);
        }
        if (answering == null) return new LoopRootAdmission(admitted, null);
        if (!admitted.isEmpty() || !AnswerOrder.answeredHere(new Offered(
                answering.rootHookGroup, rootMethod, receiver, rootArguments,
                activationSource, observedAddresses), slots.get(answering),
                answered)) {
            if (!admitted.isEmpty()) {
                answering.noteUnaddressedCandidate(answered);
            }
            return new LoopRootAdmission(admitted, null);
        }
        answering.claimsEnclosingInvocation(enclosingInvocationEvent);
        admitted.add(answering.taskId);
        return new LoopRootAdmission(admitted, answering);
    }

    private static RefusedCandidate secondInvocation(
            RuntimeTask task, SourceRef activationSource) {
        return RefusedCandidate.stated("a second enclosing invocation of "
                + "this region: occurrence " + task.occurrenceId
                + " already runs the bodies of entry event "
                + task.enclosingInvocationEvent()
                + ", so this entry is another activation", activationSource);
    }

    synchronized RuntimeTask select(String rootHookGroupKey,
                                            String rootMethod,
                                            Object receiver,
                                            Object[] rootArguments) {
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);

        if (!RecordingWindow.opened()) return null;
        int index = AnswerOrder.select(new Offered(nonNull(rootHookGroupKey),
                rootMethod, receiver, rootArguments, activationSource,
                new ObservedAddresses()), AnswerOrder.shapes());
        return index < 0 ? null : tasks.get(index);
    }

    private final class Offered
            implements AnswerOrder.Offer<RefusedCandidate> {
        private final String rootHookGroupKey;
        private final String rootMethod;
        private final Object receiver;
        private final Object[] rootArguments;
        private final SourceRef activationSource;
        private final ObservedAddresses observedAddresses;

        private Offered(String rootHookGroupKey, String rootMethod,
                        Object receiver, Object[] rootArguments,
                        SourceRef activationSource,
                        ObservedAddresses observedAddresses) {
            this.rootHookGroupKey = rootHookGroupKey;
            this.rootMethod = rootMethod;
            this.receiver = receiver;
            this.rootArguments = rootArguments;
            this.activationSource = activationSource;
            this.observedAddresses = observedAddresses;
        }

        @Override
        public List<RuntimeTask> tasks() {
            return tasks;
        }

        @Override
        public boolean offered(int index) {
            RuntimeTask task = tasks.get(index);
            return task.rootHookGroup.equals(rootHookGroupKey)
                    && !task.completedGoalReserved;
        }

        @Override
        public RefusedCandidate refusal(int index) {
            RuntimeTask task = tasks.get(index);
            return task.loopBodyRoot
                    ? unenclosedBody(task, activationSource)
                    : ConcolicTaskPlan.refusal(task, false, rootMethod,
                            task.rootArgumentSelector, receiver,
                            rootArguments, activationSource,
                            observedAddresses);
        }

        @Override
        public OccurrenceAddress observed(RefusedCandidate refusal) {
            return refusal.observed;
        }

        @Override
        public boolean live(int index) {
            return candidateLive[index];
        }

        @Override
        public void take(int index, boolean byShape) {
            candidateLive[index] = true;
            answeredByShape[index] = byShape;
        }

        @Override
        public void unaddressed(int index, RefusedCandidate refusal) {
            tasks.get(index).noteUnaddressedCandidate(refusal);
        }

        @Override
        public void recordedHere(int index, RefusedCandidate refusal) {
            tasks.get(index).noteUnaddressedCandidate(
                    RefusedCandidate.onAddress("the recording opened this "
                            + "address itself, so the activation is that "
                            + "occurrence and answers no task by shape",
                            refusal.observed, activationSource));
        }

        @Override
        public boolean openedNone() {
            return Identity.openedNone();
        }
    }

    synchronized RuntimeTask selectNamed(OccurrenceAddress address,
                                         SourceRef activationSource) {
        if (!RecordingWindow.opened()) return null;
        RuntimeTask admitted = null;
        for (int index = 0; index < tasks.size(); index++) {
            RuntimeTask task = tasks.get(index);
            if (task.address == null
                    || !task.address.regionId().equals(address.regionId())) {
                continue;
            }
            if (!task.address.id().equals(address.id())) {
                task.noteUnaddressedCandidate(RefusedCandidate.onAddress(
                        "a hop named an occurrence of this region",
                        address, activationSource));
                continue;
            }
            if (admitted != null || candidateLive[index]
                    || task.completedGoalReserved) {
                continue;
            }
            candidateLive[index] = true;
            answeredByShape[index] = false;
            admitted = task;
        }
        return admitted;
    }

    private static RefusedCandidate unenclosedBody(RuntimeTask task,
                                                   SourceRef activationSource) {
        if (LoopAccounting.enclosingLoopRoot(task) != null) return null;
        return RefusedCandidate.stated("a body of this loop ran under no"
                + " enclosing invocation admitted for it: the enclosing root"
                + " hook " + task.loopRootHookGroup + " either did not"
                + " run on this thread or refused this task when it did",
                activationSource);
    }

    private static RefusedCandidate refusal(
            RuntimeTask task, boolean enclosing, String rootMethod,
            RootArgumentSelector arguments, Object receiver,
            Object[] rootArguments, SourceRef activationSource,
            ObservedAddresses observedAddresses) {
        if (!compatibleRoot(task.rootMethod, rootMethod,
                task.rootContextSelector, arguments, receiver,
                rootArguments)) {
            return RefusedCandidate.stated((enclosing
                    ? "an enclosing invocation of " + nonNull(rootMethod)
                    + " ran, and this task's enclosing root selector"
                    : "an invocation of " + nonNull(rootMethod) + " ran, and"
                    + " this task's root selector")
                    + " does not fit it: receiver " + describe(receiver)
                    + ", " + (rootArguments == null ? 0
                    : rootArguments.length) + " argument(s)",
                    activationSource);
        }
        OccurrenceAddress observed = observedAddresses.of(task,
                activationSource);
        return task.acceptsRootInvocation(observed) ? null
                : RefusedCandidate.onAddress(enclosing
                        ? "matching enclosing root" : "matching root",
                        observed, activationSource);
    }

    static final class ObservedAddresses {
        private final Map<String, OccurrenceAddress> byTarget =
                new LinkedHashMap<String, OccurrenceAddress>();

        OccurrenceAddress of(RuntimeTask task, SourceRef activationSource) {
            String node = activationSource.key();
            String target = node + "\n" + task.regionId;
            if (byTarget.containsKey(target)) return byTarget.get(target);
            OccurrenceAddress observed = task.observedAddress(node);
            byTarget.put(target, observed);
            return observed;
        }
    }

    static String attribution(String activationSourceKey) {
        String key = nonNull(activationSourceKey);
        if (key.isEmpty()
                || RuntimeRegionPlanner.UNREGISTERED_SOURCE.key().equals(key)) {
            return " (this run attributed the activation to no node, so it"
                    + " counts in the unregistered source)";
        }
        return " (attributed to " + key + ")";
    }

    static ConcolicTaskPlan load() {
        String planValue = nonNull(System.getProperty(
                FocusedReplay.PLAN_PROPERTY)).trim();
        String selectedTasks = nonNull(System.getProperty(
                "causynth.concolic.task.id")).trim();
        if (planValue.isEmpty()) {
            return new ConcolicTaskPlan(null,
                    Collections.<RuntimeTask>emptyList());
        }
        String resultValue = nonNull(System.getProperty(
                "causynth.concolic.results")).trim();
        if (selectedTasks.isEmpty() || resultValue.isEmpty()) {
            throw new IllegalStateException("Concolic runtime requires "
                    + "task id and result path with a task plan");
        }
        Path result = Paths.get(resultValue);
        Path plan = Paths.get(planValue);
        if (!Files.isRegularFile(plan)) {
            throw new IllegalStateException(
                    "Concolic task plan not found: " + plan);
        }
        Set<String> selected = campaignTaskIds(selectedTasks);
        List<RuntimeTask> tasks = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(plan,
                StandardCharsets.UTF_8)) {
            Set<String> taskIds = new LinkedHashSet<>();
            int maxTasks = ExecutionTask.maxCampaignTasks();
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement parsed = new JsonParser().parse(line);
                if (!parsed.isJsonObject()) {
                    throw new IllegalStateException("malformed plan: "
                            + "every task plan row must be an object");
                }
                if (tasks.size() == maxTasks) {
                    throw new IllegalStateException("malformed plan: "
                            + "campaign exceeds its bound of " + maxTasks
                            + " tasks");
                }
                ExecutionTask encoded = ExecutionTask.decode(
                        parsed.getAsJsonObject());
                RuntimeTask task = new RuntimeTask(encoded);
                if (!taskIds.add(task.taskId)) {
                    throw new IllegalStateException("malformed plan: "
                            + "duplicate execution task " + task.taskId);
                }
                tasks.add(task);
            }
        } catch (IOException | RuntimeException exception) {
            throw new IllegalStateException("Causynth rejected "
                    + "task plan " + plan + ": "
                    + exception.getMessage(), exception);
        }
        for (String taskId : selected) {
            boolean present = false;
            for (RuntimeTask task : tasks) {
                present |= task.taskId.equals(taskId);
            }
            if (!present) {
                throw new IllegalStateException("Selected execution task "
                        + taskId + " is absent in " + plan);
            }
        }
        return new ConcolicTaskPlan(result, tasks);
    }

    static Set<String> campaignTaskIds(String property) {
        Set<String> ids = new LinkedHashSet<>();
        for (String value : property.split(",")) {
            String taskId = nonNull(value).trim();
            if (taskId.isEmpty()) continue;
            if (!ids.add(taskId)) {
                throw new IllegalStateException("malformed plan: "
                        + "duplicate selected execution task " + taskId);
            }
        }
        if (ids.isEmpty()) {
            throw new IllegalStateException("malformed plan: "
                    + "no execution task is selected");
        }
        return ids;
    }

    static String describe(Object receiver) {
        return receiver == null ? "null" : receiver.getClass().getName();
    }

    static boolean compatibleRoot(
            String selectedMethod, String actualMethod,
            RootContextSelector context, RootArgumentSelector arguments,
            Object receiver, Object[] rootArguments) {
        if (!nonNull(selectedMethod).equals(nonNull(actualMethod))) {
            return false;
        }
        if (!context.matches(receiver)) {
            return false;
        }
        return !arguments.present || arguments.matches(rootArguments);
    }

    static final class RootContextSelector {
        private final String sourceKey;
        private final int invocationOrdinal;
        private final String receiverRuntimeClass;

        private RootContextSelector(String receiverRuntimeClass,
                                    String sourceKey,
                                    int invocationOrdinal) {
            this.sourceKey = nonNull(sourceKey);
            this.invocationOrdinal = invocationOrdinal;
            this.receiverRuntimeClass = nonNull(receiverRuntimeClass);
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = optionalString(selector, "kind");
            boolean global = "GLOBAL_INVOCATION".equals(kind);
            String receiverClass = optionalString(selector, "receiverClass");
            JsonObject anchor = object(selector, "causalAnchor");
            String sourceKey = optionalString(anchor, "sourceKey");
            int invocationOrdinal = optionalInteger(selector,
                    "invocationOrdinal", -1);
            String anchorKind = optionalString(anchor, "kind");
            boolean registeredSource = RuntimeRegionPlanner
                    .ANCHOR_REGISTERED_SOURCE.equals(anchorKind);
            boolean unregisteredSource = RuntimeRegionPlanner
                    .ANCHOR_UNREGISTERED_SOURCE.equals(anchorKind);
            boolean inheritedContext = RuntimeRegionPlanner
                    .ANCHOR_INHERITED_CONTEXT.equals(anchorKind);
            boolean sentinelSource = RuntimeRegionPlanner.UNREGISTERED_SOURCE
                    .key().equals(sourceKey);
            if (!global && (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || !"RECEIVER_CONTEXT".equals(kind))
                    || sourceKey.isEmpty()
                    || !sourceKey.equals(sourceKey.trim())
                    || invocationOrdinal < 1) {
                throw new IllegalArgumentException(
                        "rootSelector requires an exact receiver context and "
                                + "a causal anchor naming its source and a "
                                + "positive invocationOrdinal");
            }
            if (!registeredSource && !unregisteredSource && !inheritedContext
                    || unregisteredSource != sentinelSource) {
                throw new IllegalArgumentException(
                        "rootSelector causalAnchor.kind must be exactly "
                                + RuntimeRegionPlanner
                                .ANCHOR_REGISTERED_SOURCE + " or "
                                + RuntimeRegionPlanner
                                .ANCHOR_INHERITED_CONTEXT + " for a named "
                                + "source or " + RuntimeRegionPlanner
                                .ANCHOR_UNREGISTERED_SOURCE + " for "
                                + RuntimeRegionPlanner.UNREGISTERED_SOURCE
                                .key());
            }
            return new RootContextSelector(global ? "" : receiverClass,
                    sourceKey, invocationOrdinal);
        }

        private boolean matches(Object receiver) {
            return AnswerOrder.receiverFits(receiverRuntimeClass, receiver);
        }

        private String describe() {
            return sourceKey + "/invocation=" + invocationOrdinal;
        }

        private boolean anchorSourceNeverExisted() {
            return !OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(sourceKey)
                    && !RuntimeTraceContext.sourceIdentityRegistered(sourceKey);
        }

    }

    private static final class RootArgumentSelector {
        private final boolean present;
        private final List<RootArgumentTypePredicate> predicates;

        private RootArgumentSelector(boolean present,
                                     List<RootArgumentTypePredicate> predicates) {
            this.present = present;
            this.predicates = predicates;
        }

        private static RootArgumentSelector from(JsonObject rootSelector) {
            if (!rootSelector.has("arguments")) {
                return new RootArgumentSelector(false,
                        Collections.emptyList());
            }
            JsonElement raw = rootSelector.get("arguments");
            if (raw == null || !raw.isJsonObject()) {
                return invalid("rootSelector.arguments must be an object");
            }
            JsonObject json = raw.getAsJsonObject();
            JsonElement rawPredicates = json.get("predicates");
            if (rawPredicates == null || !rawPredicates.isJsonArray()
                    || rawPredicates.getAsJsonArray().size() == 0) {
                return invalid("predicates must be a non-empty array");
            }
            List<RootArgumentTypePredicate> predicates = new ArrayList<>();
            Set<Integer> indices = new LinkedHashSet<>();
            for (JsonElement rawPredicate
                    : rawPredicates.getAsJsonArray()) {
                if (rawPredicate == null || !rawPredicate.isJsonObject()) {
                    return invalid("each predicate must be an object");
                }
                JsonObject predicate = rawPredicate.getAsJsonObject();
                if (!"EXACT_RUNTIME_TYPE".equals(
                        optionalString(predicate, "kind"))) {
                    return invalid("predicate kind must be exact runtime type");
                }
                int index = optionalInteger(predicate, "argumentIndex", -1);
                String runtimeType = optionalString(predicate, "runtimeType");
                if (index < 0 || runtimeType.isEmpty()
                        || !runtimeType.equals(runtimeType.trim())
                        || !indices.add(index)) {
                    return invalid("predicate index/type is malformed or duplicate");
                }
                predicates.add(new RootArgumentTypePredicate(index,
                        runtimeType));
            }
            predicates.sort((left, right) -> Integer.compare(
                    left.argumentIndex, right.argumentIndex));
            return new RootArgumentSelector(true,
                    Collections.unmodifiableList(predicates));
        }

        private static RootArgumentSelector invalid(String error) {
            throw new IllegalArgumentException(error);
        }

        private boolean matches(Object[] rootArguments) {
            if (!present || rootArguments == null) return false;
            for (RootArgumentTypePredicate predicate : predicates) {
                if (predicate.argumentIndex >= rootArguments.length) {
                    return false;
                }
                Object value = rootArguments[predicate.argumentIndex];
                if (value == null || !predicate.runtimeType.equals(
                        value.getClass().getName())) {
                    return false;
                }
            }
            return true;
        }

    }

    private static final class RootArgumentTypePredicate {
        private final int argumentIndex;
        private final String runtimeType;

        private RootArgumentTypePredicate(int argumentIndex,
                                          String runtimeType) {
            this.argumentIndex = argumentIndex;
            this.runtimeType = runtimeType;
        }
    }

    static final class RuntimeTask implements AnswerOrder.Planned {
        final String taskId;
        final String rootHookGroup;
        final String loopRootHookGroup;
        final String regionId;
        final String sourceKey;
        final String occurrenceId;
        final OccurrenceAddress address;
        final List<String> shape;
        final Set<String> recordedBeside;
        final long recordedRootCall;
        final String rootMethod;
        final RootContextSelector rootContextSelector;
        final RootArgumentSelector enclosingRootArgumentSelector;
        final RootArgumentSelector rootArgumentSelector;
        final List<SymbolizeAction> symbolize;
        final LoopBoundPolicy loopBound;
        final boolean capturesTargetReach;
        final boolean readsTrackedState;
        final boolean doorsOnly;
        final Map<String, List<String>> contentKeys;
        volatile boolean completedGoalReserved;
        int publishedActivations;
        final boolean loopBodyRoot;
        final int loopOccurrenceBudget;
        private long enclosingInvocationEvent;
        boolean loopBoundCutRecorded;
        final String targetBranchSite;
        final int targetBranchOccurrence;
        final boolean targetBranchRequiredOutcome;
        final List<StaticScopeMap.Guard> targetDeciders;
        final Map<String, ForcingTable.Arm> forcedArms;
        final Map<String, Boolean> targetGuards = new LinkedHashMap<>();
        final Map<String, CommunicationHandoffSpec>
                attachSites = new LinkedHashMap<>();
        final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        int unaddressedCandidates;
        final Set<RefusedCandidate> unaddressedReasons = new LinkedHashSet<>();
        private static final int SHOWN_REFUSALS = 4;

        private static Map<String, List<String>> contentKeys(JsonObject row) {
            if (row == null || !row.has(ZkChain.CONTENT_KEYS)) return null;
            Map<String, List<String>> keys =
                    new LinkedHashMap<String, List<String>>();
            for (JsonElement element : array(row, ZkChain.CONTENT_KEYS)) {
                JsonObject key = element.getAsJsonObject();
                String slot = optionalString(key, "slot");
                keys.computeIfAbsent(slot.isEmpty()
                        ? optionalString(key, "location") : slot,
                        named -> new ArrayList<String>())
                        .add(optionalString(key, "pointer"));
            }
            return keys;
        }

        RuntimeTask(ExecutionTask task) {
            if (!task.executable()) {
                throw new IllegalArgumentException(
                        "runtime task must be executable");
            }
            JsonObject rootSelector = task.rootSelector();
            this.taskId = task.taskId();
            this.rootHookGroup = task.rootHookGroup();
            this.loopRootHookGroup = task.loopRootHookGroup();
            this.regionId = task.regionId();
            this.sourceKey = task.sourceKey();
            this.occurrenceId = task.occurrenceId();
            this.address = parseAddress(this.occurrenceId);
            List<String> shape = new ArrayList<String>();
            for (JsonElement hop : array(task.json(),
                    RuntimeSelectedRegionFinalizer.CONTEXT_SHAPE)) {
                shape.add(hop.getAsString());
            }
            this.shape = Collections.unmodifiableList(shape);
            Set<String> recorded = new LinkedHashSet<String>();
            for (JsonElement id : array(task.json(),
                    RuntimeSelectedRegionFinalizer.RECORDED_BESIDE)) {
                recorded.add(id.getAsString());
            }
            this.recordedBeside = Collections.unmodifiableSet(recorded);
            this.recordedRootCall = optionalLongInteger(task.json(),
                    DeclaredSiteCapture.ROOT_CALL_ID, -1L);
            this.rootMethod = task.rootMethod();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            this.enclosingRootArgumentSelector =
                    RootArgumentSelector.from(rootSelector);
            if (!this.sourceKey.equals(rootContextSelector.sourceKey)) {
                throw new IllegalArgumentException(
                        "rootSelector causal anchor names "
                                + rootContextSelector.sourceKey
                                + " instead of task source " + this.sourceKey);
            }
            this.rootArgumentSelector =
                    LoopBoundPolicy.LOOP_BODY_ROOT.equals(task.rootAuthority())
                            ? new RootArgumentSelector(false,
                            Collections.<RootArgumentTypePredicate>emptyList())
                            : RootArgumentSelector.from(rootSelector);
            this.symbolize = new ArrayList<>();
            this.loopBound = task.loopBound();
            this.loopBodyRoot = task.loopBodyRoot();
            if (this.loopBodyRoot && this.address == null) {
                throw new IllegalArgumentException(
                        "ROOT_LOOP_OCCURRENCE_UNADDRESSED: loop-body task "
                                + this.taskId + " plans occurrence "
                                + this.occurrenceId + ", which names no "
                                + "occurrence");
            }
            this.loopOccurrenceBudget = this.loopBound
                    .maxBackedgeTraversals(task.rootLoopSiteId());
            this.doorsOnly = optionalBool(task.json(),
                    RuntimeSelectedRegionFinalizer.DOORS_ONLY, false);
            this.contentKeys = contentKeys(task.json());
            this.readsTrackedState = !doorsOnly && optionalBool(task.json(),
                    ExecutionTask.READS_TRACKED_STATE, false);
            this.capturesTargetReach =
                    task.goalKind().capturesTargetReach();
            this.configuredSourcePhases = task.configuredSourcePhases();
            JsonObject targetBranch = object(task.json(), "targetBranch");
            this.targetBranchSite = optionalString(targetBranch, "siteId");
            this.targetBranchOccurrence = optionalInteger(targetBranch,
                    "occurrence", -1);
            this.targetBranchRequiredOutcome = targetRequiredOutcome(
                    targetBranch, targetBranchSite);
            this.targetDeciders = StaticScopeMap.guardsOf(
                    targetBranch.get("decidedBy"));
            this.forcedArms = ForcingTable.read(targetBranch.get("force"));
            for (JsonElement guard : array(targetBranch, "guards")) {
                JsonObject row = guard.getAsJsonObject();
                targetGuards.put(optionalString(row, "siteId"),
                        optionalBool(row, "requiredOutcome", false));
            }
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(encoded, "mode"))
                        && (!doorsOnly || !action.marker.isEmpty())) {
                    this.symbolize.add(action);
                }
            }
            for (CommunicationHandoffSpec site
                    : task.communicationHandoffs()) {
                if (!site.outgoing()) {
                    attachSites.putIfAbsent(nonNull(site.portId()), site);
                }
            }
        }

        CommunicationHandoffSpec attachSite(String portId) {
            return attachSites.get(nonNull(portId));
        }

        synchronized void noteUnaddressedCandidate(
                RefusedCandidate refusal) {
            unaddressedCandidates++;
            unaddressedReasons.add(refusal);
        }

        synchronized String unansweredAddress() {
            boolean neverExisted = rootContextSelector
                    .anchorSourceNeverExisted();
            List<String> said = new ArrayList<String>();
            for (RefusedCandidate refusal : unaddressedReasons) {
                if (said.size() == SHOWN_REFUSALS) break;
                said.add(refusal.render(this));
            }
            int unshown = unaddressedReasons.size() - said.size();
            return unaddressedCandidates + " compatible activation(s) did "
                    + "not answer the addressed occurrence; " + said
                    + (unshown > 0 ? " and " + unshown + " more" : "")
                    + (neverExisted
                    ? "; " + rootContextSelector.describe()
                    + " was never registered in this run" : "");
        }

        synchronized void claimActivation() {
            publishedActivations++;
        }

        synchronized boolean cutsBoundedLoopOccurrence() {
            if (!loopBodyRoot) return false;
            return publishedActivations >= loopOccurrenceBudget;
        }

        synchronized boolean claimsEnclosingInvocation(long entryEvent) {
            if (entryEvent <= 0L) return false;
            if (enclosingInvocationEvent == 0L) {
                enclosingInvocationEvent = entryEvent;
                return true;
            }
            return enclosingInvocationEvent == entryEvent;
        }

        synchronized long enclosingInvocationEvent() {
            return enclosingInvocationEvent;
        }

        synchronized boolean claimLoopBoundCutMarker() {
            if (loopBoundCutRecorded) return false;
            loopBoundCutRecorded = true;
            return true;
        }

        synchronized void releaseActivation() {
            if (publishedActivations > 0) publishedActivations--;
        }

        boolean declaresTargetBranch() {
            return !targetBranchSite.isEmpty();
        }

        OccurrenceAddress observedAddress(String node) {
            return Identity.occurrence(node, regionId, false);
        }

        private static OccurrenceAddress parseAddress(String occurrenceId) {
            String value = nonNull(occurrenceId);
            if (value.isEmpty()) return null;
            try {
                return OccurrenceAddress.parse(value);
            } catch (RuntimeException notAnAddress) {
                return null;
            }
        }

        boolean acceptsRootInvocation(OccurrenceAddress observed) {
            return address != null && observed != null
                    && address.id().equals(observed.id());
        }

        boolean answers(OccurrenceAddress observed,
                        Function<CausalContext, List<String>> shapes) {
            return AnswerOrder.answers(this, observed, shapes);
        }

        @Override
        public OccurrenceAddress address() {
            return address;
        }

        @Override
        public List<String> shape() {
            return shape;
        }

        @Override
        public Set<String> recordedBeside() {
            return recordedBeside;
        }

        @Override
        public long recordedRootCall() {
            return recordedRootCall;
        }

        @Override
        public String rootHookGroup() {
            return rootHookGroup;
        }

        String addressDifference(OccurrenceAddress observed) {
            if (address == null) return "the task plans no occurrence";
            if (observed == null) {
                return "the activation ran where this run cannot name it";
            }
            return difference(address, observed)
                    + "planned " + address.render() + anchorComponents(address)
                    + ", ran at " + observed.render()
                    + anchorComponents(observed);
        }

        private static String difference(OccurrenceAddress planned,
                OccurrenceAddress observed) {
            List<String> differ = new ArrayList<String>();
            if (!planned.node().equals(observed.node())) {
                differ.add("the node (planned " + planned.node().render()
                        + ", ran " + observed.node().render() + ")");
            }
            if (!planned.regionId().equals(observed.regionId())) {
                differ.add("the region (planned " + planned.regionId()
                        + ", ran " + observed.regionId() + ")");
            }
            if (!planned.context().equals(observed.context())) {
                differ.add(contextDifference(planned.context(),
                        observed.context()));
            }
            String index = indexDifference(planned.index(), observed.index());
            if (!index.isEmpty()) differ.add(index);
            if (differ.isEmpty()) {
                return "the two addresses do not differ; ";
            }
            StringBuilder said = new StringBuilder("differs in ");
            for (int at = 0; at < differ.size(); at++) {
                if (at > 0) said.append(at + 1 == differ.size()
                        ? " and " : ", ");
                said.append(differ.get(at));
            }
            return said.append("; ").toString();
        }

        private static String indexDifference(ExecutionIndex planned,
                ExecutionIndex observed) {
            List<Frame> plannedFrames = planned.frames();
            List<Frame> observedFrames = observed.frames();
            if (plannedFrames.size() != observedFrames.size()) {
                return "its execution index depth (planned "
                        + plannedFrames.size() + " frames, ran "
                        + observedFrames.size() + ")";
            }
            int first = -1;
            int differing = 0;
            for (int at = 0; at < plannedFrames.size(); at++) {
                if (plannedFrames.get(at).equals(observedFrames.get(at))) {
                    continue;
                }
                differing++;
                if (first < 0) first = at;
            }
            if (first < 0) return "";
            Frame plan = plannedFrames.get(first);
            Frame ran = observedFrames.get(first);
            String where = "frame " + first + " of " + plannedFrames.size();
            String said = plan.callSite().equals(ran.callSite())
                    ? where + ", " + plan.callSite() + ", at iteration "
                    + ran.iteration() + " and not the planned "
                    + plan.iteration()
                    : where + "'s call site (planned " + plan.callSite()
                    + ", ran " + ran.callSite() + ")";
            return differing == 1 ? said
                    : said + " (and " + (differing - 1) + " further frame"
                    + (differing == 2 ? "" : "s") + " below it)";
        }

        private static String contextDifference(CausalContext planned,
                CausalContext observed) {
            if (!(planned instanceof CausalContext.Anchor)
                    || !(observed instanceof CausalContext.Anchor)) {
                return "its causal context (planned " + planned.render()
                        + ", ran " + observed.render() + ")";
            }
            CausalContext.Anchor plan = (CausalContext.Anchor) planned;
            CausalContext.Anchor ran = (CausalContext.Anchor) observed;
            if (!plan.rpcSite().equals(ran.rpcSite())) {
                return "its anchor's transport site (planned "
                        + plan.rpcSite() + ", ran " + ran.rpcSite() + ")";
            }
            Endpoint plannedEnd = InteractionRefusals.endpoint(
                    plan.producerEndpointId());
            Endpoint ranEnd = InteractionRefusals.endpoint(ran.producerEndpointId());
            if (plannedEnd == null || ranEnd == null) {
                return "its causal anchor (planned "
                        + plan.producerEndpointId()
                        + (plannedEnd == null ? ", which no message of this "
                        + "run minted" : "") + "; ran "
                        + ran.producerEndpointId()
                        + (ranEnd == null ? ", which no message of this run "
                        + "minted" : "") + ")";
            }
            if (!plannedEnd.occurrence().equals(ranEnd.occurrence())) {
                return "its anchor's producer occurrence (planned "
                        + plannedEnd.occurrence().render() + ", ran "
                        + ranEnd.occurrence().render() + ")";
            }
            if (!plannedEnd.site().equals(ranEnd.site())) {
                return "its anchor's producer site (planned "
                        + plannedEnd.site() + ", ran " + ranEnd.site() + ")";
            }
            if (!plannedEnd.siteIndex().equals(ranEnd.siteIndex())) {
                return "its anchor's producer site index (planned "
                        + plannedEnd.siteIndex().render() + ", ran "
                        + ranEnd.siteIndex().render() + ")";
            }
            if (plannedEnd.attempt() != ranEnd.attempt()) {
                return "its anchor's producer attempt (planned "
                        + plannedEnd.attempt() + ", ran "
                        + ranEnd.attempt() + ")";
            }
            return "its causal anchor's digest over components that agree "
                    + "(planned " + plan.producerEndpointId() + ", ran "
                    + ran.producerEndpointId() + ")";
        }

        private static String anchorComponents(OccurrenceAddress address) {
            if (!(address.context() instanceof CausalContext.Anchor)) {
                return "";
            }
            String producer = ((CausalContext.Anchor) address.context())
                    .producerEndpointId();
            String components = InteractionRefusals.components(producer);
            return " [anchor " + producer + " = "
                    + (components.isEmpty()
                    ? "no message of this run minted it" : components) + "]";
        }


        void reserveCompletedEvidence() {
            if (!loopBodyRoot) completedGoalReserved = true;
        }

        boolean targetTest(String site) {
            return !targetBranchSite.isEmpty()
                    && (targetBranchSite.equals(site)
                    || targetGuards.containsKey(site));
        }

        boolean reachedRequiredTargetOutcome(JsonObject reach) {
            return declaresTargetBranch()
                    && reach != null
                    && targetBranchSite.equals(optionalString(reach, "siteId"))
                    && targetBranchOccurrence == optionalInteger(reach,
                    "occurrence", -1)
                    && reach.has("outcome")
                    && reach.get("outcome").isJsonPrimitive()
                    && reach.getAsJsonPrimitive("outcome").isBoolean()
                    && reach.get("outcome").getAsBoolean()
                    == targetBranchRequiredOutcome;
        }

        String targetBranchLabel() {
            return targetBranchSite + "#" + targetBranchOccurrence;
        }

        static boolean targetRequiredOutcome(JsonObject targetBranch,
                                             String targetSite) {
            if (nonNull(targetSite).isEmpty()) return false;
            JsonElement encoded = targetBranch == null ? null
                    : targetBranch.get("requiredOutcome");
            if (encoded == null || !encoded.isJsonPrimitive()
                    || !encoded.getAsJsonPrimitive().isBoolean()) {
                throw new IllegalArgumentException(
                        "target branch states no fatal arm: " + targetSite);
            }
            return encoded.getAsBoolean();
        }

    }
}
