package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.RootHookGroup;
import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.registerRunTotalsHook;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.taskUnanswered;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** The bounded campaign this JVM executes. */
final class ConcolicTaskPlan {
    private static final Object LOCK = new Object();
    private static volatile ConcolicTaskPlan plan;

    /** The plan this JVM executes, loaded on first use. */
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
    /**
     * Tasks with a candidate running now, and tasks whose candidate
     * published: every compatible root invocation is a candidate, one at a
     * time, until one is the addressed occurrence (README {@code OCC-1}).
     */
    final boolean[] candidateLive;
    final boolean[] occurrenceClaimed;
    /** Each task's slot in the two arrays above, by task identity. */
    private final Map<RuntimeTask, Integer> slots =
            new IdentityHashMap<RuntimeTask, Integer>();
    /**
     * Memo of {@link #rootHookGroup} per {@code (instrumentationSelector,
     * rootMethod)}; the plan is immutable, and scanning it at every woven
     * root entry blocked replay threads.
     */
    private final Map<String, RootHookGroup> rootHookGroups =
            new LinkedHashMap<String, RootHookGroup>();
    private final Map<String, RootHookGroup> loopRootHookGroups =
            new LinkedHashMap<String, RootHookGroup>();
    boolean unansweredAddressesPublished;

    ConcolicTaskPlan(Path resultFile, List<RuntimeTask> tasks) {
        this.resultFile = resultFile;
        this.tasks = Collections.unmodifiableList(tasks);
        this.candidateLive = new boolean[tasks.size()];
        this.occurrenceClaimed = new boolean[tasks.size()];
        for (int index = 0; index < this.tasks.size(); index++) {
            this.slots.put(this.tasks.get(index), index);
        }
    }


    /**
     * Releases the address of a candidate that ended without being the
     * occurrence, so the next compatible invocation may try for it.
     */
    synchronized void releaseCandidate(RuntimeTask task) {
        Integer index = slots.get(task);
        if (index != null) candidateLive[index] = false;
    }

    /**
     * States every address this run did not answer, once each, at run end:
     * only then are "never registered" and "several fit" decidable.
     */
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
        // Render outside the monitor: rendering digests addresses, and doing
        // it per comparison inside #select blocked every woven thread.
        for (RuntimeTask task : unanswered) {
            if (task.unaddressedCandidates == 0) {
                // Nothing compatible ran: not the same as "none matched".
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

    /**
     * One candidate that ran and was not the addressed occurrence, as facts
     * (prefix, observed address, attribution, thread); rendered once, at
     * {@code TASK_UNANSWERED}, because rendering is expensive.  The four
     * facts are the refusal's identity.
     */
    static final class RefusedCandidate {
        private final String said;
        /** The address the activation ran at, or null when {@code said} is
         * the whole reason. */
        private final OccurrenceAddress observed;
        /** The node this run attributed the candidate to, or {@code ""}. */
        private final String attribution;
        private final String thread;

        private RefusedCandidate(String said, OccurrenceAddress observed,
                                 String attribution) {
            this.said = safe(said);
            this.observed = observed;
            this.attribution = safe(attribution);
            this.thread = Thread.currentThread().getName();
        }

        /** A candidate refused on its address, stated against {@code said}. */
        static RefusedCandidate onAddress(String said,
                                          OccurrenceAddress observed,
                                          SourceRef activationSource) {
            return new RefusedCandidate(said, observed,
                    attribution(activationSource == null ? ""
                            : activationSource.key()));
        }

        /** A candidate refused on something that is not its address. */
        static RefusedCandidate stated(String said,
                                       SourceRef activationSource) {
            return new RefusedCandidate(said, null,
                    attribution(activationSource == null ? ""
                            : activationSource.key()));
        }

        /** The same, where the refusal itself names where it ran. */
        static RefusedCandidate stated(String said) {
            return new RefusedCandidate(said, null, "");
        }

        /**
         * One refused candidate as a sentence: always states the thread and
         * a difference ({@link #difference} says so when there is none).
         */
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

    /** Marks durable evidence without clearing a newer live candidate. */
    synchronized void markOccurrenceClaimed(RuntimeTask task) {
        Integer index = slots.get(task);
        if (index != null) occurrenceClaimed[index] = true;
    }

    /**
     * Resolves an occurrence-specific hook to the region entry shared by
     * every sibling hook at that Java method; memoized in
     * {@link #rootHookGroups}.
     */
    synchronized RootHookGroup rootHookGroup(
            String instrumentationSelector, String rootMethod) {
        return rootHookGroups.computeIfAbsent(safe(instrumentationSelector)
                + "\n" + safe(rootMethod), hook -> resolveRootHookGroup(
                        instrumentationSelector, rootMethod));
    }

    private RootHookGroup resolveRootHookGroup(
            String instrumentationSelector, String rootMethod) {
        RuntimeTask selected = null;
        for (RuntimeTask task : tasks) {
            if (!task.instrumentationSelector.equals(
                    safe(instrumentationSelector))
                    || !Objects.equals(task.rootMethod, rootMethod)) {
                continue;
            }
            if (selected != null && !selected.rootHookGroupKey().equals(
                    task.rootHookGroupKey())) {
                throw new IllegalStateException(
                        "instrumentation selector addresses multiple "
                                + "root hook groups: "
                                + safe(instrumentationSelector));
            }
            selected = task;
        }
        if (selected == null) {
            return new RootHookGroup("UNPLANNED\n"
                    + safe(instrumentationSelector) + "\n"
                    + safe(rootMethod), 1);
        }
        String key = selected.rootHookGroupKey();
        int hooks = 0;
        for (RuntimeTask task : tasks) {
            if (key.equals(task.rootHookGroupKey())) hooks++;
        }
        return new RootHookGroup(key, hooks);
    }

    /** Resolves one lightweight outer hook shared by loop-body tasks. */
    synchronized RootHookGroup loopRootHookGroup(
            String instrumentationSelector, String rootMethod) {
        return loopRootHookGroups.computeIfAbsent(
                safe(instrumentationSelector) + "\n" + safe(rootMethod),
                hook -> resolveLoopRootHookGroup(instrumentationSelector,
                        rootMethod));
    }

    private RootHookGroup resolveLoopRootHookGroup(
            String instrumentationSelector, String rootMethod) {
        RuntimeTask selected = null;
        for (RuntimeTask task : tasks) {
            if (!task.loopBodyRoot
                    || !task.instrumentationSelector.equals(
                    safe(instrumentationSelector))
                    || !Objects.equals(task.rootMethod, rootMethod)) {
                continue;
            }
            selected = task;
            break;
        }
        if (selected == null) {
            return new RootHookGroup("UNPLANNED_LOOP_ROOT\n"
                    + safe(rootMethod), 1);
        }
        String key = selected.loopRootHookGroupKey();
        int hooks = 0;
        for (RuntimeTask task : tasks) {
            if (task.loopBodyRoot
                    && key.equals(task.loopRootHookGroupKey())) hooks++;
        }
        return new RootHookGroup(key, hooks);
    }

    /**
     * Counts one real enclosing method entry and freezes which loop task
     * owns all body iterations executed by that invocation.
     */
    synchronized Set<String> addressLoopRootInvocation(
            String loopRootHookGroupKey, String rootMethod,
            Object receiver, Object[] rootArguments,
            long enclosingInvocationEvent) {
        SourceRef registeredReceiverSource =
                RuntimeTraceContext.sourceFor(receiver);
        // Where this activation ran, by the function the recorder and the
        // planner used.
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        Set<String> admitted = new LinkedHashSet<>();
        // Outside the recording window nothing has an ordinal, so nothing is
        // a candidate.
        if (!RecordingWindow.opened()) {
            return admitted;
        }
        ObservedAddresses observedAddresses = new ObservedAddresses();
        for (RuntimeTask task : tasks) {
            // Another region's enclosing root: silent, or every enclosing
            // invocation would file a refusal against every task.
            if (!task.loopBodyRoot
                    || !task.loopRootHookGroupKey().equals(
                    safe(loopRootHookGroupKey))) {
                continue;
            }
            // From here this task's own hook ran, so every refusal is stated;
            // a silent one is later misreported as ROOT_NEVER_EXECUTED.  The
            // whole address, nothing standing in for it: an enclosing loop
            // root decides which occurrence a whole sequence of bodies
            // belongs to.
            RefusedCandidate refused = refusal(task, true, rootMethod,
                    task.enclosingRootArgumentSelector, receiver,
                    rootArguments, registeredReceiverSource, context,
                    activationSource, observedAddresses);
            if (refused != null) {
                task.noteUnaddressedCandidate(refused);
                continue;
            }
            // One occurrence, one enclosing activation: a later invocation
            // is the next k and belongs to the task addressed there.
            if (!task.claimsEnclosingInvocation(enclosingInvocationEvent)) {
                task.noteUnaddressedCandidate(RefusedCandidate.stated(
                        "a second enclosing invocation of this region: "
                                + "occurrence " + task.occurrenceId
                                + " already runs the bodies of entry event "
                                + task.enclosingInvocationEvent()
                                + ", so this entry is another activation",
                        activationSource));
                continue;
            }
            admitted.add(task.taskId);
        }
        return admitted;
    }

    /** Claims at most one open task for this root invocation. */
    synchronized RuntimeTask select(String rootHookGroupKey,
                                            String rootMethod,
                                            Object receiver,
                                            Object[] rootArguments) {
        SourceRef registeredReceiverSource =
                RuntimeTraceContext.sourceFor(receiver);
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);
        RuntimeTraceContext.View context = RuntimeTraceContext.current();

        // Outside the recording window there is no candidate.
        if (!RecordingWindow.opened()) return null;
        ObservedAddresses observedAddresses = new ObservedAddresses();
        for (int index = 0; index < tasks.size(); index++) {
            RuntimeTask task = tasks.get(index);
            if (!task.rootHookGroupKey().equals(
                    safe(rootHookGroupKey))) continue;
            if (task.completedGoalReserved) continue;
            // Stated, or the run end reports ROOT_NEVER_EXECUTED.
            RefusedCandidate refused = task.loopBodyRoot
                    ? unenclosedBody(task, activationSource)
                    : refusal(task, false, rootMethod,
                            task.rootArgumentSelector, receiver,
                            rootArguments, registeredReceiverSource, context,
                            activationSource, observedAddresses);
            if (refused != null) {
                task.noteUnaddressedCandidate(refused);
                continue;
            }
            if (candidateLive[index]) continue;
            candidateLive[index] = true;
            return task;
        }
        return null;
    }

    /** Why a loop body ran under no enclosing invocation admitted for it,
     *  or null when one was. */
    private static RefusedCandidate unenclosedBody(RuntimeTask task,
                                                   SourceRef activationSource) {
        if (LoopAccounting.enclosingLoopRoot(task) != null) return null;
        return RefusedCandidate.stated("a body of this loop ran under no"
                + " enclosing invocation admitted for it: the enclosing root"
                + " hook " + task.loopRootHookGroupKey() + " either did not"
                + " run on this thread or refused this task when it did",
                activationSource);
    }

    /**
     * Why this root entry is not {@code task}'s occurrence, or null when it
     * is: the root selector, then the source this run attributed it to,
     * then the whole address.  {@code enclosing}: asked at the enclosing
     * invocation of a loop-body task.
     */
    private static RefusedCandidate refusal(
            RuntimeTask task, boolean enclosing, String rootMethod,
            RootArgumentSelector arguments, Object receiver,
            Object[] rootArguments, SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context, SourceRef activationSource,
            ObservedAddresses observedAddresses) {
        if (!compatibleRoot(task.rootMethod, rootMethod,
                task.rootContextSelector, arguments, receiver,
                rootArguments)) {
            return RefusedCandidate.stated((enclosing
                    ? "an enclosing invocation of " + safe(rootMethod)
                    + " ran, and this task's enclosing root selector"
                    : "an invocation of " + safe(rootMethod) + " ran, and"
                    + " this task's root selector")
                    + " does not fit it: receiver " + describe(receiver)
                    + ", " + (rootArguments == null ? 0
                    : rootArguments.length) + " argument(s)",
                    activationSource);
        }
        String mismatch = sourceMismatch(task, registeredReceiverSource,
                context);
        if (!mismatch.isEmpty()) {
            return RefusedCandidate.stated((enclosing
                    ? "an enclosing invocation of " + safe(rootMethod)
                    + " ran and this run attributed it elsewhere: "
                    : "a matching root ran and this run attributed it"
                    + " elsewhere: ") + mismatch, activationSource);
        }
        OccurrenceAddress observed = observedAddresses.of(task,
                activationSource);
        return task.acceptsRootInvocation(observed) ? null
                : RefusedCandidate.onAddress(enclosing
                        ? "matching enclosing root" : "matching root",
                        observed, activationSource);
    }

    /**
     * Why this run's evidence says the activation is another lifecycle
     * (epoch) of the planned node, or {@code ""}.
     *
     * <p>Needed because {@code sameSourceIdentity} strips {@code #epoch<n>}.
     * Only evidence naming the same node at a <em>different</em> epoch
     * refuses; unattributed is not another epoch.  Trap: "the planned epoch
     * is not registered" is a fact about a moment, not the run, and must not
     * refuse.</p>
     */
    static String lifecycleMismatch(String plannedSourceKey,
                                    Collection<String> attributed) {
        String planned = safe(plannedSourceKey);
        if (!RuntimeTraceContext.declaresEpoch(planned)) return "";
        if (attributed == null || attributed.contains(planned)) return "";
        for (String observed : attributed) {
            if (observed != null && !observed.equals(planned)
                    && RuntimeTraceContext.sameSourceIdentity(planned,
                    observed)) {
                return "matching root ran at " + observed + ", not at "
                        + planned;
            }
        }
        return "";
    }

    /**
     * The node and epoch this activation is counted in: {@link
     * RuntimeTraceContext#activationSource}, the same function the recorder
     * stamped {@code METHOD_ENTER} with and the planner counted by.  Read at
     * activation start from the registry {@link #lifecycleMismatch} and the
     * configured-source mint also read, so the three agree.
     */
    static String countedLifecycle(RuntimeTask task,
                                   SourceRef activationSource) {
        String planned = safe(task.sourceKey);
        if (!RuntimeTraceContext.declaresEpoch(planned)) return planned;
        // Never fall back to the planned node: an unattributed activation
        // counts in the unregistered source, as the planner counted it, or
        // it steals the planned node's k.
        return activationSource == null
                ? RuntimeRegionPlanner.UNREGISTERED_SOURCE.key()
                : activationSource.key();
    }

    /**
     * Per-entry memo of {@link RuntimeTask#observedAddress}, keyed by
     * (lifecycle, region): exactly what the answer depends on within one
     * entry, so it is a memo, not a narrowing.
     */
    static final class ObservedAddresses {
        private final Map<String, OccurrenceAddress> byTarget =
                new LinkedHashMap<String, OccurrenceAddress>();

        OccurrenceAddress of(RuntimeTask task, SourceRef activationSource) {
            String lifecycle = countedLifecycle(task, activationSource);
            String target = lifecycle + "\n" + task.regionId;
            if (byTarget.containsKey(target)) return byTarget.get(target);
            OccurrenceAddress observed = task.observedAddress(lifecycle);
            byTarget.put(target, observed);
            return observed;
        }
    }

    /**
     * What this run attributed the refused activation to, so an ordinal
     * refusal on the planned node reads differently from one on no node.
     */
    static String attribution(String activationSourceKey) {
        String key = safe(activationSourceKey);
        if (key.isEmpty()
                || RuntimeRegionPlanner.UNREGISTERED_SOURCE.key().equals(key)) {
            return " (this run attributed the activation to no node, so it"
                    + " counts in the unregistered source)";
        }
        return " (attributed to " + key + ")";
    }

    /** The source keys this run attributed to one live root entry. */
    static Set<String> attributedSourceKeys(
            SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        Set<String> keys = new LinkedHashSet<>();
        if (registeredReceiverSource != null) {
            keys.add(registeredReceiverSource.key());
        }
        if (context != null && context.source != null) {
            keys.add(context.source.key());
        }
        return keys;
    }

    /** Empty only when entry-time runtime evidence names this source. */
    static String sourceMismatch(
            RuntimeTask task, SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        SourceRef inherited = context.source;
        // Epoch first: the checks below ignore it.
        String lifecycle = lifecycleMismatch(task.sourceKey,
                attributedSourceKeys(registeredReceiverSource, context));
        if (!lifecycle.isEmpty()) return lifecycle;
        boolean receiverMatches = registeredReceiverSource != null
                && RuntimeTraceContext.sameSourceIdentity(task.sourceKey,
                registeredReceiverSource.key());
        if (OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
                task.sourceKey)) {
            return registeredReceiverSource == null && inherited == null
                    ? "" : "matching root carried a registered source "
                    + (registeredReceiverSource == null
                    ? inherited.key() : registeredReceiverSource.key())
                    + " instead of the unregistered source";
        }
        // One rule for every anchor kind: does this run's evidence name
        // ANOTHER source?  The receiver's own registration is authoritative.
        if (registeredReceiverSource != null) {
            return receiverMatches ? ""
                    : "matching root receiver belonged to "
                    + registeredReceiverSource.key() + " instead of "
                    + task.sourceKey;
        }
        // Without one there is no evidence of where it ran.  Trap: an
        // inherited context is not it -- on an RPC service it names the
        // CALLER -- so it must not refuse.
        return "";
    }

    static ConcolicTaskPlan load() {
        String planValue = safe(System.getProperty(
                FocusedReplay.PLAN_PROPERTY)).trim();
        String selectedTasks = safe(System.getProperty(
                "causynth.concolic.task.id")).trim();
        if (planValue.isEmpty()) {
            return new ConcolicTaskPlan(null,
                    Collections.<RuntimeTask>emptyList());
        }
        String resultValue = safe(System.getProperty(
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

    /** The selected campaign, in plan order. */
    static Set<String> campaignTaskIds(String property) {
        Set<String> ids = new LinkedHashSet<>();
        for (String value : property.split(",")) {
            String taskId = safe(value).trim();
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

    /**
     * A receiver's runtime class only: never {@code toString} a live
     * application object mid-workload (it may throw or observe state).
     */
    static String describe(Object receiver) {
        return receiver == null ? "null" : receiver.getClass().getName();
    }

    static boolean compatibleRoot(
            String selectedMethod, String actualMethod,
            RootContextSelector context, RootArgumentSelector arguments,
            Object receiver, Object[] rootArguments) {
        if (!safe(selectedMethod).equals(safe(actualMethod))) return false;
        if (!context.matches(receiver)) {
            return false;
        }
        return !arguments.present || arguments.matches(rootArguments);
    }

    static final class RootContextSelector {
        private final String sourceKey;
        /** One-based planner invocation ordinal; independent of the trace
         * occurrence id. */
        private final int invocationOrdinal;
        /**
         * The class a receiver-scoped root hook stands on, or {@code ""}.
         * A declared scope deciding which invocations are candidates, not a
         * matching rule: an occurrence IS its address (IDENTITY-V3 SS1).
         */
        private final String receiverRuntimeClass;

        private RootContextSelector(String receiverRuntimeClass,
                                    String sourceKey,
                                    int invocationOrdinal) {
            this.sourceKey = safe(sourceKey);
            this.invocationOrdinal = invocationOrdinal;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
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

        /** Whether this root invocation is a candidate for the occurrence. */
        private boolean matches(Object receiver) {
            return receiverRuntimeClass.isEmpty()
                    || receiver != null && receiverRuntimeClass.equals(
                            receiver.getClass().getName());
        }

        /**
         * Why the candidate that just ran is not the addressed occurrence, or
         * {@code ""} when it is.
         */
        String unconfirmed(Set<String> attributedSourceKeys) {
            if (attributedSourceKeys.isEmpty()) {
                // Unattributed is the UNREGISTERED source's occurrence,
                // never the planned node's next k.
                return OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
                        sourceKey) ? ""
                        : "occurrence ran on "
                        + OccurrenceBinding.UNREGISTERED_SOURCE_KEY
                        + " (nothing attributed it to any node), but its"
                        + " anchor names " + sourceKey;
            }
            boolean sameSource = false;
            for (String attributed : attributedSourceKeys) {
                if (RuntimeTraceContext.sameSourceIdentity(
                        sourceKey, attributed)) {
                    sameSource = true;
                    break;
                }
            }
            if (!sameSource) {
                return "occurrence ran on " + attributedSourceKeys
                        + ", but its anchor names " + sourceKey;
            }
            return "";
        }

        /** This address on one line, for a named gap. */
        private String describe() {
            return sourceKey + "/invocation=" + invocationOrdinal;
        }

        /**
         * Whether the anchored source was never registered in this run, which
         * makes the address unsatisfiable here rather than merely unmatched.
         */
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

        /** No argument predicate: every activation of the root is admitted. */
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

    static final class RuntimeTask {
        final String taskId;
        final String instrumentationSelector;
        final String regionId;
        /** The activation this task is. */
        final String sourceKey;
        final String occurrenceId;
        /** The one address this task plans; every admission compares it. */
        final OccurrenceAddress address;
        final String rootMethod;
        final RootContextSelector rootContextSelector;
        /** Argument predicates evaluated at the enclosing method entry. */
        final RootArgumentSelector enclosingRootArgumentSelector;
        final RootArgumentSelector rootArgumentSelector;
        /** Actions that execute directly at ordinary instrumentation hooks. */
        final List<SymbolizeAction> symbolize;
        final LoopBoundPolicy loopBound;
        final boolean capturesTargetReach;
        /** Whether the region reads a tracked cell (SYMBOL-SCOPE F2). */
        final boolean readsTrackedState;
        /**
         * Whether this non-loop address has completed its goal, which closes
         * its admission; loop-body roots are governed by K_L alone.
         */
        volatile boolean completedGoalReserved;
        /** Result rows this address has published in this replay. */
        int publishedActivations;
        /**
         * Whether this region is rooted on a bounded loop body: at most K_L
         * occurrences publish; later iterations run concretely.
         */
        final boolean loopBodyRoot;
        final String rootLoopMethod;
        final int rootLoopHeaderUnitIndex;
        /**
         * A loop-body region's occurrence budget: its ROOT loop's K_L.  Trap:
         * the region max includes inner loops unrolled within one occurrence
         * and would inflate the occurrence count.
         */
        final int loopOccurrenceBudget;
        /**
         * Entry event of the one enclosing invocation whose bodies ({@code
         * #k#aN}) this occurrence is, or {@code 0} before admission.
         */
        private long enclosingInvocationEvent;
        /** Whether the one bounded-cut marker for this region was written. */
        boolean loopBoundCutRecorded;
        /** The declared target branch event of a target-reach task. */
        final String targetBranchSite;
        final int targetBranchOccurrence;
        /** Solver-selected outcome that reaches the annotated failure. */
        final boolean targetBranchRequiredOutcome;
        /** The helper branch deciding the target branch when it tests the
         *  constant a helper returned ("" if none), and its fatal arm. */
        final String targetDeciderSite;
        final boolean targetDeciderOutcome;
        /** Every test of a disjunctive target guard and its fatal arm, the
         *  target branch first; empty for one guard. */
        final Map<String, Boolean> targetGuards = new LinkedHashMap<>();
        /** Declared communication ports handed to the VM, by port role. */
        final Map<String, CommunicationHandoffSpec>
                communicationHandoffs = new LinkedHashMap<>();
        /** Exact baseline hook executions, in recorded event order. */
        final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        /** Candidates refused for this address, and each distinct reason. */
        int unaddressedCandidates;
        final Set<RefusedCandidate> unaddressedReasons = new LinkedHashSet<>();
        /** How many refusals one unanswered row spells out. */
        private static final int SHOWN_REFUSALS = 4;

        RuntimeTask(ExecutionTask task) {
            if (!task.executable()) {
                throw new IllegalArgumentException(
                        "runtime task must be executable");
            }
            JsonObject rootSelector = task.rootSelector();
            this.taskId = task.taskId();
            this.instrumentationSelector = task.instrumentationSelector();
            this.regionId = task.regionId();
            this.sourceKey = task.sourceKey();
            this.occurrenceId = task.occurrenceId();
            this.address = parseAddress(this.occurrenceId);
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
            // A loop-body root binds no arguments, so an argument predicate
            // would silently refuse every iteration.
            this.rootArgumentSelector =
                    LoopBoundPolicy.LOOP_BODY_ROOT.equals(task.rootAuthority())
                            ? new RootArgumentSelector(false,
                            Collections.<RootArgumentTypePredicate>emptyList())
                            : RootArgumentSelector.from(rootSelector);
            this.symbolize = new ArrayList<>();
            this.loopBound = task.loopBound();
            this.loopBodyRoot = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                    task.rootAuthority());
            // A loop-body task must name its k; refused at the plan, not
            // guessed at replay.
            if (this.loopBodyRoot && this.address == null) {
                throw new IllegalArgumentException(
                        "ROOT_LOOP_OCCURRENCE_UNADDRESSED: loop-body task "
                                + this.taskId + " plans occurrence "
                                + this.occurrenceId + ", which names no "
                                + "occurrence");
            }
            this.rootLoopMethod = task.rootLoopMethod();
            this.rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            // An undeclared root loop site inherits the default K_L.
            this.loopOccurrenceBudget = this.loopBound
                    .maxBackedgeTraversals(task.rootLoopSiteId());
            this.readsTrackedState = optionalBool(task.json(),
                    ExecutionTask.READS_TRACKED_STATE, false);
            this.capturesTargetReach =
                    task.goalKind().capturesTargetReach();
            // Already validated when the plan row was decoded.
            this.configuredSourcePhases = task.configuredSourcePhases();
            JsonObject targetBranch = object(task.json(), "targetBranch");
            this.targetBranchSite = optionalString(targetBranch, "siteId");
            this.targetBranchOccurrence = optionalInteger(targetBranch,
                    "occurrence", -1);
            this.targetBranchRequiredOutcome = targetRequiredOutcome(
                    targetBranch, targetBranchSite);
            JsonObject decider = object(targetBranch, "decidedBy");
            this.targetDeciderSite = optionalString(decider, "siteId");
            this.targetDeciderOutcome = optionalBool(decider,
                    "requiredOutcome", false);
            for (JsonElement guard : array(targetBranch, "guards")) {
                JsonObject row = guard.getAsJsonObject();
                targetGuards.put(optionalString(row, "siteId"),
                        optionalBool(row, "requiredOutcome", false));
            }
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
            }
            for (CommunicationHandoffSpec site
                    : task.communicationHandoffs()) {
                // A region holding both sides of a cut declares a port once
                // per role.
                if (communicationHandoffs.put(handoffKey(site.portId(),
                        site.outgoing()), site) != null) {
                    throw new IllegalArgumentException(
                            "communication port declares two handoff sites "
                            + "in " + taskId + ": " + site.portId());
                }
            }
        }

        /** The declared handoff site of one communication port role. */
        CommunicationHandoffSpec communicationHandoff(
                String portId, boolean exporting) {
            return communicationHandoffs.get(handoffKey(portId, exporting));
        }


        static String handoffKey(String portId, boolean exporting) {
            return (exporting ? "EXPORT\n" : "ATTACH\n") + safe(portId);
        }

        /** Files one refused candidate's facts. */
        synchronized void noteUnaddressedCandidate(
                RefusedCandidate refusal) {
            unaddressedCandidates++;
            unaddressedReasons.add(refusal);
            registerRunTotalsHook();
        }

        /**
         * The run's one statement about an unanswered address, rendering
         * every filed {@link RefusedCandidate}.  Call with the plan's monitor
         * released.
         */
        synchronized String unansweredAddress() {
            boolean neverExisted = rootContextSelector
                    .anchorSourceNeverExisted();
            // A few refusals say why; all of them made one row 634 KB and a
            // campaign's gap file 2.5 GB, past what jq reads (v69).
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

        /**
         * Counts one activation against the loop-body occurrence budget; not
         * an identity (IDENTITY-V3: an occurrence IS its execution index).
         */
        synchronized void claimActivation() {
            publishedActivations++;
        }

        synchronized boolean cutsBoundedLoopOccurrence() {
            if (!loopBodyRoot) return false;
            return publishedActivations >= loopOccurrenceBudget;
        }

        /**
         * Binds this occurrence to its first admitted enclosing invocation,
         * for the whole replay (never released), and answers whether
         * {@code entryEvent} is it.
         */
        synchronized boolean claimsEnclosingInvocation(long entryEvent) {
            if (entryEvent <= 0L) return false;
            if (enclosingInvocationEvent == 0L) {
                enclosingInvocationEvent = entryEvent;
                return true;
            }
            return enclosingInvocationEvent == entryEvent;
        }

        /** The enclosing invocation this occurrence's bodies come from. */
        synchronized long enclosingInvocationEvent() {
            return enclosingInvocationEvent;
        }

        /** Claims the one bounded-cut marker write for this region. */
        synchronized boolean claimLoopBoundCutMarker() {
            if (loopBoundCutRecorded) return false;
            loopBoundCutRecorded = true;
            return true;
        }

        /** Gives back the count of an activation that published nothing. */
        synchronized void releaseActivation() {
            if (publishedActivations > 0) publishedActivations--;
        }

        boolean declaresTargetBranch() {
            return !targetBranchSite.isEmpty();
        }

        /** Every injected hook that belongs to one physical Java entry. */
        String rootHookGroupKey() {
            // No source here: sibling tasks for other sources share the hook.
            return (loopBodyRoot ? "LOOP\n" : "METHOD\n")
                    + regionId + "\n" + rootMethod
                    + (loopBodyRoot ? "\n" + rootLoopMethod + "\n"
                    + rootLoopHeaderUnitIndex : "");
        }

        /** All lightweight enclosing hooks physically share this method. */
        String loopRootHookGroupKey() {
            return loopBodyRoot ? rootMethod : "";
        }

        /**
         * The address this activation ran at, by {@code Identity.occurrence}
         * -- the function the recorder ran.  Unnamed outside the recording
         * window, and then it matches nothing.
         */
        OccurrenceAddress observedAddress(String lifecycle) {
            // open=false: the session publisher opens the region later, and
            // opening twice would move every endpoint's index base.
            return Identity.occurrence(
                    safe(lifecycle).isEmpty() ? sourceKey : lifecycle,
                    regionId, false);
        }

        /** The planned address, or null when the id names no occurrence. */
        private static OccurrenceAddress parseAddress(String occurrenceId) {
            String value = safe(occurrenceId);
            if (value.isEmpty()) return null;
            try {
                return OccurrenceAddress.parse(value);
            } catch (RuntimeException notAnAddress) {
                return null;
            }
        }

        /**
         * Whether this activation is the addressed occurrence: the whole
         * address, id against id, and nothing else -- an occurrence is its
         * address.  Trap: loosening this (e.g. ignoring an unreproducible
         * anchor digest) admits a sibling DataNode's activation; the fix for
         * such anchors belongs in the identity model, not here.
         */
        boolean acceptsRootInvocation(OccurrenceAddress observed) {
            return address != null && observed != null
                    && address.id().equals(observed.id());
        }

        /**
         * Why {@code observed} is not this task's occurrence: the differing
         * component ({@link #difference}), both whole addresses, and each
         * anchor's mint components ({@link InteractionRefusals#components}).
         */
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

        /**
         * Which components differ, outermost-first (node, region, context,
         * index), so the reader need not diff two long addresses.
         */
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
                // Refused on something other than the address.
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

        /** The frame the two indexes part at, or {@code ""} when equal. */
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

        /**
         * Which part of the causal context differs, over the mint's inputs
         * read back from the filed producer
         * ({@link InteractionRefusals#endpoint}).
         */
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

        /** The producer endpoint one address's anchor is a digest of. */
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


        /** Closes admission for a non-loop address after its first
         *  terminal result. */
        void reserveCompletedEvidence() {
            if (!loopBodyRoot) completedGoalReserved = true;
        }

        /** Whether a decision at {@code site} reaches the declared target:
         *  its branch, or any test of its disjunctive guard. */
        boolean targetTest(String site) {
            return !targetBranchSite.isEmpty()
                    && (targetBranchSite.equals(site)
                    || targetGuards.containsKey(site));
        }

        /** Whether this occurrence witnessed the selected failure outcome. */
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

        /** The declared target branch event, for a named coverage gap. */
        String targetBranchLabel() {
            return targetBranchSite + "#" + targetBranchOccurrence;
        }

        /**
         * The target branch arm that reaches the annotated throw, as computed
         * by {@code causynth.SiteControlDependence} and carried on
         * {@code targetBranch}; never recomputed here.
         */
        static boolean targetRequiredOutcome(JsonObject targetBranch,
                                             String targetSite) {
            if (safe(targetSite).isEmpty()) return false;
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
