package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Selects one target and its VM-observed linked replay scope. */
public final class RuntimeWorkflowDiscovery {
    private static final String EXPLICIT_FAULT_ENTRY =
            "EXPLICIT_FAULT_ENTRY";

    private RuntimeWorkflowDiscovery() {
    }

    static RankedWorkflow rankedWorkflow(List<RegionInstancePlan> plans)
            throws IOException {
        return rankedWorkflow(plans, Collections.<JsonObject>emptyList(),
                Scope.CANDIDATE);
    }

    /** The first replay activates the target's complete dynamic ancestry. */
    static RankedWorkflow seedReplayWorkflow(List<RegionInstancePlan> plans)
            throws IOException {
        return rankedWorkflow(plans, Collections.<JsonObject>emptyList(),
                Scope.SEED_VALUE);
    }

    /**
     * Selects the seed candidate scope, or its observed sub-closure
     * after the linked seed replay has published summaries.
     *
     * <p>The candidate graph remains the instrumentation frontier.  Once a
     * replay exists, only VM value evidence may turn one of those candidates
     * into a path-exploration member: an admitted RPC attach names its exact
     * producer task. A guarded field read names every retained writer case,
     * because each candidate keeps its own expression and PC. This does not
     * promote unrelated writers from the static candidate graph.</p>
     */
    static RankedWorkflow rankedWorkflow(
            List<RegionInstancePlan> plans,
            Collection<JsonObject> observedSummaries) throws IOException {
        return rankedWorkflow(plans, observedSummaries,
                observedSummaries == null || observedSummaries.isEmpty()
                        ? Scope.CANDIDATE : Scope.OBSERVED);
    }

    private static RankedWorkflow rankedWorkflow(
            List<RegionInstancePlan> plans,
            Collection<JsonObject> observedSummaries,
            Scope scope) throws IOException {
        if (plans == null || plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        Map<String, RegionInstancePlan> byOccurrence = new LinkedHashMap<>();
        Map<String, JsonObject> edges = new LinkedHashMap<>();
        List<Target> targets = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            String occurrence = PathObservation.plannedOccurrenceOf(
                    plan.occurrenceId());
            RegionInstancePlan prior = byOccurrence.putIfAbsent(
                    occurrence, plan);
            if (prior != null && prior != plan) {
                throw new IOException("duplicate planned region occurrence: "
                        + occurrence);
            }
            for (Goal goal : plan.goals()) {
                indexEdges(edges, goal.edgeBindings());
                if (goal.kind().capturesTargetReach() && goal.replayable()
                        && namesFailureSite(goal)) {
                    targets.add(new Target(plan, goal));
                }
            }
        }
        if (targets.isEmpty()) {
            throw new IOException("runtime region plan has no replayable target");
        }

        for (Target candidate : targets) {
            Set<String> topologyScope = topologyScope(
                    candidate.occurrenceId, byOccurrence, edges);
            candidate.rank(closureEdges(topologyScope, edges));
        }
        targets.sort(Target.ORDER);
        if (targets.size() > 1 && Target.EVIDENCE_ORDER.compare(
                targets.get(0), targets.get(1)) == 0) {
            throw new IOException("runtime evidence does not distinguish "
                    + "target occurrences: " + targets.get(0).context()
                    + "; " + targets.get(1).context());
        }
        Target target = targets.get(0);
        // A linked replay contains only the observed dynamic ancestry of the
        // target. Static demand still guides instrumentation and later
        // topology discovery; making an unrelated observed occurrence a
        // mandatory replay member can prevent the real causal chain from
        // executing at all.
        Set<String> candidateClosure = equivalentTargetTopologyScope(target,
                targets, byOccurrence, edges);
        Set<String> closure;
        if (scope == Scope.CANDIDATE) {
            closure = candidateClosure;
        } else if (scope == Scope.SEED_VALUE) {
            // A concrete object or container is still a carrier: its fields or
            // elements can hold expressions propagated by an upstream region.
            // DependencyRole classifies what this region computes; it cannot
            // safely prune the producer which populated that structure.  Use
            // the same confirmed dynamic ancestry as candidate ranking, while
            // leaving the graph's role limited to linked-replay scheduling.
            closure = candidateClosure;
        } else {
            closure = activeObservedScope(target, candidateClosure, edges,
                    observedSummaries == null
                            ? Collections.<JsonObject>emptyList()
                            : observedSummaries);
        }
        // An explicit fault occurrence controls whether an interaction takes
        // place; it need not produce the interaction's payload.  Keep such a
        // control root when (and only when) the selected target's runtime
        // candidate closure already contains that exact occurrence.  This
        // leaves unrelated marker occurrences in the instrumentation union
        // without forcing them into the linked replay.
        closure = new LinkedHashSet<>(closure);
        for (String occurrence : candidateClosure) {
            RegionInstancePlan plan = byOccurrence.get(occurrence);
            if (plan != null && explicitFaultEntry(plan)) {
                closure.add(occurrence);
            }
        }
        List<Selection> selections = new ArrayList<>();
        // Preserve the seed task's symbolic frontier and therefore its stable
        // task identity.  The exact replay closure narrows which occurrences
        // need path summaries; it does not rewrite the already executed
        // target task or the candidate edges retained for instrumentation.
        selections.add(Selection.target(target));

        List<RegionInstancePlan> dependencies = new ArrayList<>();
        for (String occurrence : closure) {
            if (occurrence.equals(target.occurrenceId)) continue;
            RegionInstancePlan plan = byOccurrence.get(occurrence);
            if (plan != null) dependencies.add(plan);
        }
        dependencies.sort(Comparator
                .comparing(RegionInstancePlan::regionId)
                .thenComparing(RegionInstancePlan::occurrenceId));
        for (RegionInstancePlan plan : dependencies) {
            Goal goal = onlyReplayableGoal(plan);
            if (goal != null) {
                selections.add(Selection.dependency(target.campaignId,
                        plan, goal));
            }
        }
        return new RankedWorkflow(target, selections);
    }

    /** All graph-connected occurrences of every execution of the same
     * failure site.  These edges schedule one JVM bundle only; they never
     * supply a symbolic value or a writer choice. */
    private static Set<String> equivalentTargetTopologyScope(
            Target selected, Collection<Target> targets,
            Map<String, RegionInstancePlan> plans,
            Map<String, JsonObject> edges) {
        Set<String> sites = failureSites(selected.goal);
        Set<String> result = new LinkedHashSet<>();
        for (Target target : targets) {
            if (sites.equals(failureSites(target.goal))) {
                result.addAll(topologyScope(target.occurrenceId,
                        plans, edges));
            }
        }
        return result;
    }

    private static Set<String> failureSites(Goal goal) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : goal.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (bool(branch, "failureTarget", false)
                    && !bool(branch, "loopControlGuard", false)
                    && bool(branch, "observed", false)
                    && branch.has("requiredOutcome")
                    && !branch.get("requiredOutcome").isJsonNull()) {
                String site = string(branch, "siteId");
                if (!site.isEmpty()) result.add(site);
            }
        }
        return result;
    }

    private static boolean explicitFaultEntry(RegionInstancePlan plan) {
        return EXPLICIT_FAULT_ENTRY.equals(string(plan.json(),
                "rootAuthority"));
    }

    private enum Scope {
        CANDIDATE,
        SEED_VALUE,
        OBSERVED
    }

    /**
     * Exact observed ancestry of the selected target.  Missing producer
     * summaries are deliberately not guessed into this set: the propagation
     * closure still sees their exact boundary reference and reports a
     * producer-case gap when that case is semantically required.
     */
    private static Set<String> activeObservedScope(
            Target target, Set<String> candidateClosure,
            Map<String, JsonObject> edges,
            Collection<JsonObject> summaries) throws IOException {
        Map<ObservedTaskKey, List<JsonObject>> byTask =
                new LinkedHashMap<>();
        List<JsonObject> targetRows = new ArrayList<>();
        for (JsonObject summary : summaries) {
            if (summary == null) continue;
            String task = string(summary, "taskId");
            if (!task.isEmpty()) {
                ObservedTaskKey key = new ObservedTaskKey(
                        string(summary, "boundarySessionScope"), task);
                byTask.computeIfAbsent(key, ignored -> new ArrayList<>())
                        .add(summary);
            }
            if (target.goal.goalId().equals(string(summary, "goalId"))
                    && target.plan.regionId().equals(
                    string(summary, "regionId"))
                    && target.occurrenceId.equals(plannedOccurrence(summary))) {
                targetRows.add(summary);
            }
        }
        BoundaryOwnerIndex boundaryOwners = BoundaryOwnerIndex.of(summaries);
        SymbolicRootOwnerIndex symbolicRootOwners =
                SymbolicRootOwnerIndex.of(summaries);

        Set<String> selected = new LinkedHashSet<>();
        selected.add(target.occurrenceId);
        Set<ObservedTaskKey> visitedTasks = new LinkedHashSet<>();
        Deque<ObservedTaskKey> work = new ArrayDeque<>();
        for (JsonObject row : targetRows) {
            String task = string(row, "taskId");
            ObservedTaskKey key = new ObservedTaskKey(
                    string(row, "boundarySessionScope"), task);
            if (!task.isEmpty() && visitedTasks.add(key)) {
                work.addLast(key);
            }
        }
        for (Map.Entry<String, Set<String>> entry
                : observedHandoffEndpointTasks(summaries,
                candidateClosure).entrySet()) {
            for (String task : entry.getValue()) {
                ObservedTaskKey key = new ObservedTaskKey(
                        entry.getKey(), task);
                if (byTask.containsKey(key) && visitedTasks.add(key)) {
                    work.addLast(key);
                }
            }
        }
        Map<String, Set<String>> forwardByScope =
                observedHandoffForwardScopes(summaries, candidateClosure,
                        edges);
        for (Set<String> occurrences : forwardByScope.values()) {
            selected.addAll(occurrences);
        }
        for (JsonObject summary : summaries) {
            if (summary == null) continue;
            String summaryScope = string(summary, "boundarySessionScope");
            String occurrence = plannedOccurrence(summary);
            if (!forwardByScope.getOrDefault(summaryScope,
                    Collections.emptySet()).contains(occurrence)) {
                continue;
            }
            String task = string(summary, "taskId");
            ObservedTaskKey key = new ObservedTaskKey(summaryScope, task);
            if (!task.isEmpty() && visitedTasks.add(key)) {
                work.addLast(key);
            }
        }
        while (!work.isEmpty()) {
            ObservedTaskKey task = work.removeFirst();
            for (JsonObject row : byTask.getOrDefault(task,
                    Collections.emptyList())) {
                String occurrence = plannedOccurrence(row);
                // Reaching this row through the worklist is itself exact VM
                // evidence: the target, an observed handoff endpoint, or a
                // guarded-read writer named this task in this replay scope.
                // Static ancestry can omit a shared-location writer (for
                // example a repeated RMW helper), so do not throw that
                // authoritative occurrence away merely because the static
                // candidate graph has no edge for it.  Physical #aN rows
                // collapse to their one planned task here; propagation still
                // joins every recorded writer activation to an exact case.
                if (!occurrence.isEmpty()) {
                    selected.add(occurrence);
                }
                Set<ObservedTaskKey> producers = observedProducerTasks(row,
                        boundaryOwners);
                symbolicRootOwners.addOwnerTasks(row, candidateClosure,
                        producers);
                for (ObservedTaskKey producer : producers) {
                    if (byTask.containsKey(producer)
                            && visitedTasks.add(producer)) {
                        work.addLast(producer);
                    }
                }
            }
        }
        return selected;
    }

    private static Map<String, Set<String>> observedHandoffForwardScopes(
            Collection<JsonObject> summaries,
            Set<String> candidateClosure,
            Map<String, JsonObject> edges) {
        Map<String, Set<String>> selected = new LinkedHashMap<>();
        Map<String, Deque<String>> work = new LinkedHashMap<>();
        for (ObservedHandoff handoff : observedHandoffs(summaries,
                candidateClosure)) {
            Set<String> occurrences = selected.computeIfAbsent(handoff.scope,
                    ignored -> new LinkedHashSet<>());
            if (occurrences.add(handoff.consumerOccurrence)) {
                work.computeIfAbsent(handoff.scope,
                        ignored -> new ArrayDeque<>()).addLast(
                        handoff.consumerOccurrence);
            }
        }
        Map<String, Set<String>> successors = new LinkedHashMap<>();
        for (JsonObject edge : edges.values()) {
            if (!AutomaticRegionEdge.summaryTraversalBinding(edge)) continue;
            String from = PathObservation.plannedOccurrenceOf(
                    string(edge, "fromOccurrenceId"));
            String to = PathObservation.plannedOccurrenceOf(
                    string(edge, "toOccurrenceId"));
            if (candidateClosure.contains(from)
                    && candidateClosure.contains(to)) {
                successors.computeIfAbsent(from,
                        ignored -> new LinkedHashSet<>()).add(to);
            }
        }
        for (Map.Entry<String, Deque<String>> entry : work.entrySet()) {
            Set<String> occurrences = selected.get(entry.getKey());
            Deque<String> pending = entry.getValue();
            while (!pending.isEmpty()) {
                for (String successor : successors.getOrDefault(
                        pending.removeFirst(), Collections.emptySet())) {
                    if (occurrences.add(successor)) pending.addLast(successor);
                }
            }
        }
        return selected;
    }


    /**
     * Tasks at both ends of an observed VM handoff inside the target's
     * candidate closure.  A later local materialization can intentionally
     * make the consumer expression an {@code INITIAL} state; that must not
     * discard the already observed communication which populated the state.
     * The handoff remains scheduling evidence only: value composition still
     * consumes the VM-propagated expression carried by each selected case.
     */
    static Map<String, Set<String>> observedHandoffEndpointTasks(
            Collection<JsonObject> summaries,
            Set<String> candidateClosure) {
        Map<String, Set<String>> result = new LinkedHashMap<>();
        for (ObservedHandoff handoff : observedHandoffs(summaries,
                candidateClosure)) {
            Set<String> tasks = result.computeIfAbsent(handoff.scope,
                    ignored -> new LinkedHashSet<>());
            tasks.add(handoff.producerTask);
            tasks.add(handoff.consumerTask);
        }
        return result;
    }

    private static List<ObservedHandoff> observedHandoffs(
            Collection<JsonObject> summaries,
            Set<String> candidateClosure) {
        List<ObservedHandoff> result = new ArrayList<>();
        if (summaries == null || candidateClosure == null
                || candidateClosure.isEmpty()) {
            return result;
        }
        for (JsonObject summary : summaries) {
            if (summary == null) continue;
            String scope = string(summary, "boundarySessionScope");
            String consumerTask = string(summary, "taskId");
            String summaryOccurrence = plannedOccurrence(summary);
            if (scope.isEmpty() || consumerTask.isEmpty()
                    || summaryOccurrence.isEmpty()) {
                continue;
            }
            for (JsonObject event : VmHandoffEvidence.eventsOf(summary)) {
                if (!scope.equals(string(event, "boundarySessionScope"))) {
                    continue;
                }
                String producerTask = string(event,
                        VmHandoffEvidence.PRODUCER_TASK_ID);
                String producerOccurrence = PathObservation
                        .plannedOccurrenceOf(string(event,
                                VmHandoffEvidence.PRODUCER_OCCURRENCE_ID));
                String consumerOccurrence = PathObservation
                        .plannedOccurrenceOf(string(event,
                                "consumerOccurrenceId"));
                if (producerTask.isEmpty()
                        || !summaryOccurrence.equals(consumerOccurrence)
                        || !candidateClosure.contains(producerOccurrence)
                        || !candidateClosure.contains(consumerOccurrence)) {
                    continue;
                }
                result.add(new ObservedHandoff(scope, producerTask,
                        consumerTask, consumerOccurrence));
            }
        }
        return result;
    }

    private static String plannedOccurrence(JsonObject row) {
        String planned = string(row, "plannedOccurrenceId");
        return planned.isEmpty() ? PathObservation.plannedOccurrenceOf(
                string(row, "occurrenceId")) : planned;
    }

    /** Producer tasks named by propagated handoffs and guarded field reads. */
    private static Set<ObservedTaskKey> observedProducerTasks(
            JsonObject summary, BoundaryOwnerIndex boundaryOwners) {
        Set<ObservedTaskKey> result = new LinkedHashSet<>();
        String summaryScope = string(summary, "boundarySessionScope");
        for (JsonObject event : VmHandoffEvidence.eventsOf(summary)) {
            String producer = string(event,
                    VmHandoffEvidence.PRODUCER_TASK_ID);
            if (!producer.isEmpty()) {
                result.add(new ObservedTaskKey(scopeOf(event, summaryScope),
                        producer));
            }
        }

        String readerTask = string(summary, "taskId");
        String readerOccurrence = string(summary, "occurrenceId");
        String readerRegion = string(summary, "regionId");
        JsonObject recorded = object(summary,
                SharedStateEvidence.RECORDED_FIELD);
        for (JsonElement encoded : array(recorded, "versions")) {
            if (!encoded.isJsonObject()) continue;
            JsonObject record = encoded.getAsJsonObject();
            if (!SharedStateEvidence.isVersionsRecord(record)) continue;
            JsonObject envelope = object(record, "envelope");
            boolean guardedRead = false;
            for (JsonElement readElement : array(envelope, "reads")) {
                if (!readElement.isJsonObject()) continue;
                JsonObject read = readElement.getAsJsonObject();
                if (!readerTask.equals(string(read, "taskId"))
                        || !readerOccurrence.equals(string(read,
                        SharedStateEvidence.READER_OCCURRENCE_ID))
                        || !readerRegion.equals(string(read, "regionId"))) {
                    continue;
                }
                // The VM ReadFromExpression payload is already validated by
                // SharedStateEvidence.  A matching reader address is the
                // authority; no derived resolution label is consulted.
                guardedRead = true;
            }
            if (!guardedRead) continue;
            // The guarded expression chooses among every retained writer.
            // A per-read count is not an ordering prefix and cannot select
            // which writers belong to the linked replay.
            for (JsonElement versionElement : array(envelope, "versions")) {
                if (!versionElement.isJsonObject()) continue;
                addGuardedWriterDependencies(
                        versionElement.getAsJsonObject(), summaryScope,
                        boundaryOwners, result);
            }
        }
        return result;
    }

    private static void addGuardedWriterDependencies(
            JsonObject version, String scope,
            BoundaryOwnerIndex boundaryOwners,
            Set<ObservedTaskKey> result) {
        if (version == null) return;
        if (!"INITIAL".equals(string(version, "versionKind"))) {
            String producerScope = scopeOf(version, scope);
            String producer = string(version, "taskId");
            if (!producer.isEmpty()) {
                result.add(new ObservedTaskKey(producerScope, producer));
            }
            // The writer's value is enabled by every selected activation that
            // physically enclosed the write.  Keep those tasks in the active
            // corpus so the propagation pass can resolve each exact #aN
            // address to its local case.  Task selection deliberately ignores
            // the activation suffix; the strict case join below remains the
            // authority for the physical occurrence.
            for (String task : observedWriterActivationTasks(version)) {
                result.add(new ObservedTaskKey(producerScope, task));
            }
        }
        boundaryOwners.addNestedOwnerTasks(
                version.get(VmExpressionIr.EXPRESSION), scope, result);
    }

    /** Tasks named by one complete VM-recorded writer activation stack. */
    static Set<String> observedWriterActivationTasks(JsonObject version) {
        Set<String> result = new LinkedHashSet<>();
        JsonObject closure = object(version,
                SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE);
        if (!SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE_AUTHORITY
                .equals(string(closure, "authority"))
                || !bool(closure, "complete", false)) {
            return result;
        }
        for (JsonElement encoded : array(closure, "cases")) {
            if (!encoded.isJsonObject()) continue;
            String task = string(encoded.getAsJsonObject(), "taskId");
            if (!task.isEmpty()) result.add(task);
        }
        return result;
    }

    private static String scopeOf(JsonObject evidence, String fallback) {
        String scope = string(evidence, "boundarySessionScope");
        return scope.isEmpty() ? fallback : scope;
    }

    /** Exact case that recorded each VM consumer-boundary event. */
    private static final class BoundaryOwnerIndex {
        private final Map<ObservedBoundaryKey, BoundaryOwner> owners =
                new LinkedHashMap<>();
        private final Set<ObservedBoundaryKey> ambiguous =
                new LinkedHashSet<>();

        private static BoundaryOwnerIndex of(
                Collection<JsonObject> summaries) {
            BoundaryOwnerIndex result = new BoundaryOwnerIndex();
            for (JsonObject summary : summaries) {
                if (summary == null) continue;
                String task = string(summary, "taskId");
                String occurrence = string(summary, "occurrenceId");
                String scope = string(summary, "boundarySessionScope");
                BoundaryOwner owner = new BoundaryOwner(task, occurrence);
                if (owner.task.isEmpty() || owner.occurrence.isEmpty()
                        || scope.isEmpty()) {
                    continue;
                }
                for (JsonObject event : VmHandoffEvidence.eventsOf(summary)) {
                    String eventScope = string(event,
                            "boundarySessionScope");
                    if (eventScope.isEmpty()) eventScope = scope;
                    result.put(new ObservedBoundaryKey(eventScope,
                            longInteger(event,
                                    VmHandoffEvidence.ATTACH_EVENT_ID, -1L)),
                            owner);
                }

                JsonObject recorded = object(summary,
                        SharedStateEvidence.RECORDED_FIELD);
                for (JsonElement encoded : array(recorded, "versions")) {
                    if (!encoded.isJsonObject()) continue;
                    JsonObject record = encoded.getAsJsonObject();
                    if (!SharedStateEvidence.isVersionsRecord(record)) {
                        continue;
                    }
                    for (JsonElement readElement : array(object(record,
                            "envelope"), "reads")) {
                        if (!readElement.isJsonObject()) continue;
                        JsonObject read = readElement.getAsJsonObject();
                        if (!task.equals(string(read, "taskId"))
                                || !occurrence.equals(string(read,
                                SharedStateEvidence.READER_OCCURRENCE_ID))
                                || !string(summary, "regionId").equals(
                                string(read, "regionId"))) {
                            continue;
                        }
                        result.put(new ObservedBoundaryKey(scope,
                                longInteger(read, "readEventId", -1L)),
                                owner);
                    }
                }
            }
            return result;
        }

        private void put(ObservedBoundaryKey key, BoundaryOwner owner) {
            if (key.event <= 0L || ambiguous.contains(key)) return;
            BoundaryOwner prior = owners.putIfAbsent(key, owner);
            if (prior != null && !prior.same(owner)) {
                owners.remove(key);
                ambiguous.add(key);
            }
        }

        private void addNestedOwnerTasks(JsonElement expression,
                                         String scope,
                                         Set<ObservedTaskKey> result) {
            if (expression == null || scope.isEmpty()) return;
            Deque<JsonElement> pending = new ArrayDeque<>();
            Set<ObservedBoundaryKey> visitedBoundaries =
                    new LinkedHashSet<>();
            Set<JsonElement> visitedNodes = Collections.newSetFromMap(
                    new IdentityHashMap<JsonElement, Boolean>());
            pending.push(expression);
            while (!pending.isEmpty()) {
                JsonElement current = pending.pop();
                if (current == null || current.isJsonNull()
                        || current.isJsonPrimitive()) {
                    continue;
                }
                if (!visitedNodes.add(current)) continue;
                if (current.isJsonArray()) {
                    for (JsonElement child : current.getAsJsonArray()) {
                        if (child != null) pending.push(child);
                    }
                    continue;
                }
                JsonObject node = current.getAsJsonObject();
                if (VmExpressionIr.isConsumerBoundary(node)
                        || VmExpressionIr.isConsumerBoundaryReference(node)) {
                    ObservedBoundaryKey key = new ObservedBoundaryKey(scope,
                            longInteger(node, VmExpressionIr.EVENT_ID, -1L));
                    if (visitedBoundaries.add(key)
                            && !ambiguous.contains(key)) {
                        BoundaryOwner owner = owners.get(key);
                        if (owner != null) {
                            result.add(new ObservedTaskKey(key.scope,
                                    owner.task));
                        }
                    }
                    JsonElement child = node.get(VmExpressionIr.EXPRESSION);
                    if (child != null) pending.push(child);
                    continue;
                }
                for (Map.Entry<String, JsonElement> field : node.entrySet()) {
                    if (field.getValue() != null) {
                        pending.push(field.getValue());
                    }
                }
            }
        }
    }

    /** Exact replay task which minted each propagated symbolic root. */
    private static final class SymbolicRootOwnerIndex {
        private final Map<ObservedSymbolKey, SymbolicRootOwner> owners =
                new LinkedHashMap<>();
        private final Set<ObservedSymbolKey> ambiguous =
                new LinkedHashSet<>();

        private static SymbolicRootOwnerIndex of(
                Collection<JsonObject> summaries) throws IOException {
            SymbolicRootOwnerIndex result = new SymbolicRootOwnerIndex();
            for (JsonObject summary : summaries) {
                if (summary == null) continue;
                String task = string(summary, "taskId");
                String occurrence = plannedOccurrence(summary);
                String scope = string(summary, "boundarySessionScope");
                if (task.isEmpty() || occurrence.isEmpty()
                        || scope.isEmpty()) {
                    continue;
                }
                for (JsonObject event
                        : SymbolicSourceEvidence.eventsOf(summary)) {
                    // A reuse observes an already-propagated root; replay must
                    // activate the earlier task which actually minted it.
                    if (SymbolicSourceEvidence.isReused(event)) continue;
                    String raw = string(event, "rawSymbol");
                    String sourceOccurrence = PathObservation
                            .plannedOccurrenceOf(string(event,
                                    "sourceOccurrenceId"));
                    if (!occurrence.equals(sourceOccurrence)) {
                        throw new IOException("symbolic source evidence owner "
                                + "differs from its summary occurrence: "
                                + raw);
                    }
                    result.put(new ObservedSymbolKey(scope, raw),
                            new SymbolicRootOwner(task, occurrence,
                                    SymbolicSourceEvidence.identity(event)));
                }
            }
            return result;
        }

        private void put(ObservedSymbolKey key, SymbolicRootOwner owner) {
            if (key.symbol.isEmpty() || ambiguous.contains(key)) return;
            SymbolicRootOwner prior = owners.putIfAbsent(key, owner);
            if (prior != null && !prior.same(owner)) {
                owners.remove(key);
                ambiguous.add(key);
            }
        }

        /**
         * Adds mint owners named by the executed control constraints of this
         * row. Recorded state and handoff evidence can also contain dormant
         * alternatives; their owners are selected from guarded reads and
         * propagated boundaries above.
         */
        private void addOwnerTasks(JsonObject summary,
                                   Set<String> candidateClosure,
                                   Set<ObservedTaskKey> result)
                throws IOException {
            String scope = string(summary, "boundarySessionScope");
            if (scope.isEmpty()) return;
            Deque<JsonElement> pending = new ArrayDeque<>();
            Set<JsonElement> visited = Collections.newSetFromMap(
                    new IdentityHashMap<JsonElement, Boolean>());
            addIfPresent(pending, summary.get("pathCondition"));
            addIfPresent(pending, summary.get("branchMappings"));
            addIfPresent(pending, summary.get("targetReach"));
            while (!pending.isEmpty()) {
                JsonElement current = pending.pop();
                if (current == null || current.isJsonNull()
                        || current.isJsonPrimitive()
                        || !visited.add(current)) {
                    continue;
                }
                if (current.isJsonArray()) {
                    for (JsonElement child : current.getAsJsonArray()) {
                        if (child != null) pending.push(child);
                    }
                    continue;
                }
                JsonObject node = current.getAsJsonObject();
                if ("SymbolExpression".equals(string(node, "_type"))) {
                    ObservedSymbolKey key = new ObservedSymbolKey(scope,
                            string(node, "_exp"));
                    if (ambiguous.contains(key)) {
                        throw new IOException("one replay scope has multiple "
                                + "mint owners for symbolic root: "
                                + key.symbol);
                    }
                    SymbolicRootOwner owner = owners.get(key);
                    if (owner != null && candidateClosure.contains(
                            owner.occurrence)) {
                        result.add(new ObservedTaskKey(key.scope,
                                owner.task));
                    }
                    continue;
                }
                for (Map.Entry<String, JsonElement> field : node.entrySet()) {
                    if (field.getValue() != null) {
                        pending.push(field.getValue());
                    }
                }
            }
        }

        private static void addIfPresent(Deque<JsonElement> pending,
                                         JsonElement value) {
            if (value != null && !value.isJsonNull()) pending.push(value);
        }
    }

    private static final class SymbolicRootOwner {
        private final String task;
        private final String occurrence;
        private final String identity;

        private SymbolicRootOwner(String task, String occurrence,
                                  String identity) {
            this.task = task == null ? "" : task;
            this.occurrence = occurrence == null ? "" : occurrence;
            this.identity = identity == null ? "" : identity;
        }

        private boolean same(SymbolicRootOwner other) {
            return other != null && task.equals(other.task)
                    && occurrence.equals(other.occurrence)
                    && identity.equals(other.identity);
        }
    }

    private static final class ObservedSymbolKey {
        private final String scope;
        private final String symbol;

        private ObservedSymbolKey(String scope, String symbol) {
            this.scope = scope == null ? "" : scope;
            this.symbol = symbol == null ? "" : symbol;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof ObservedSymbolKey)) return false;
            ObservedSymbolKey key = (ObservedSymbolKey) other;
            return scope.equals(key.scope) && symbol.equals(key.symbol);
        }

        @Override public int hashCode() {
            return 31 * scope.hashCode() + symbol.hashCode();
        }
    }

    /** A stable task id is replayed in many sessions; its observed ancestry
     * is meaningful only inside the session which produced the row. */
    private static final class ObservedTaskKey {
        private final String scope;
        private final String task;

        private ObservedTaskKey(String scope, String task) {
            this.scope = scope == null ? "" : scope;
            this.task = task == null ? "" : task;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof ObservedTaskKey)) return false;
            ObservedTaskKey key = (ObservedTaskKey) other;
            return scope.equals(key.scope) && task.equals(key.task);
        }

        @Override public int hashCode() {
            return 31 * scope.hashCode() + task.hashCode();
        }
    }

    private static final class ObservedHandoff {
        private final String scope;
        private final String producerTask;
        private final String consumerTask;
        private final String consumerOccurrence;

        private ObservedHandoff(String scope, String producerTask,
                                String consumerTask,
                                String consumerOccurrence) {
            this.scope = scope;
            this.producerTask = producerTask;
            this.consumerTask = consumerTask;
            this.consumerOccurrence = consumerOccurrence;
        }
    }

    private static final class BoundaryOwner {
        private final String task;
        private final String occurrence;

        private BoundaryOwner(String task, String occurrence) {
            this.task = task == null ? "" : task;
            this.occurrence = occurrence == null ? "" : occurrence;
        }

        private boolean same(BoundaryOwner other) {
            return other != null && task.equals(other.task)
                    && occurrence.equals(other.occurrence);
        }
    }

    private static final class ObservedBoundaryKey {
        private final String scope;
        private final long event;

        private ObservedBoundaryKey(String scope, long event) {
            this.scope = scope == null ? "" : scope;
            this.event = event;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof ObservedBoundaryKey)) return false;
            ObservedBoundaryKey key = (ObservedBoundaryKey) other;
            return scope.equals(key.scope) && event == key.event;
        }

        @Override public int hashCode() {
            return 31 * scope.hashCode() + Long.valueOf(event).hashCode();
        }
    }

    private static void indexEdges(Map<String, JsonObject> indexed,
                                   JsonArray candidates) throws IOException {
        for (JsonElement element : candidates) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (!AutomaticRegionEdge.summaryTraversalBinding(edge)) continue;
            String from = PathObservation.plannedOccurrenceOf(
                    string(edge, "fromOccurrenceId"));
            String to = PathObservation.plannedOccurrenceOf(
                    string(edge, "toOccurrenceId"));
            if (from.isEmpty() || to.isEmpty()) continue;
            String id = string(edge, "edgeId");
            if (id.isEmpty()) id = ArtifactIO.sha256(CanonicalJson.render(edge));
            JsonObject prior = indexed.putIfAbsent(id, edge.deepCopy());
            if (prior != null && !prior.equals(edge)) {
                throw new IOException("conflicting runtime edge: " + id);
            }
        }
    }

    private static Set<String> topologyScope(
            String target, Map<String, RegionInstancePlan> plans,
            Map<String, JsonObject> edges) {
        Set<String> selected = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>();
        selected.add(target);
        work.add(target);
        while (!work.isEmpty()) {
            String consumer = work.removeFirst();
            for (JsonObject edge : edges.values()) {
                String to = PathObservation.plannedOccurrenceOf(
                        string(edge, "toOccurrenceId"));
                String from = PathObservation.plannedOccurrenceOf(
                        string(edge, "fromOccurrenceId"));
                if (consumer.equals(to) && plans.containsKey(from)
                        && selected.add(from)) {
                    work.addLast(from);
                }
            }
        }
        return selected;
    }

    private static Map<String, JsonObject> closureEdges(
            Set<String> closure, Map<String, JsonObject> edges) {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (Map.Entry<String, JsonObject> entry : edges.entrySet()) {
            JsonObject edge = entry.getValue();
            String from = PathObservation.plannedOccurrenceOf(
                    string(edge, "fromOccurrenceId"));
            String to = PathObservation.plannedOccurrenceOf(
                    string(edge, "toOccurrenceId"));
            if (closure.contains(from) && closure.contains(to)) {
                result.put(entry.getKey(), edge.deepCopy());
            }
        }
        return result;
    }

    private static Goal onlyReplayableGoal(RegionInstancePlan plan)
            throws IOException {
        Goal selected = null;
        for (Goal goal : plan.goals()) {
            if (!goal.replayable()) continue;
            if (selected != null) {
                throw new IOException("region occurrence has multiple replayable "
                        + "goals: " + plan.occurrenceId());
            }
            selected = goal;
        }
        return selected;
    }

    private static boolean namesFailureSite(Goal goal) {
        for (JsonElement element : goal.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (bool(branch, "failureTarget", false)
                    && !bool(branch, "loopControlGuard", false)
                    && bool(branch, "observed", false)
                    && branch.has("requiredOutcome")
                    && !branch.get("requiredOutcome").isJsonNull()
                    && !string(branch, "siteId").isEmpty()) {
                return true;
            }
        }
        return false;
    }

    static final class RankedWorkflow {
        private final Target target;
        private final List<Selection> selections;

        private RankedWorkflow(Target target, List<Selection> selections) {
            this.target = target;
            this.selections = Collections.unmodifiableList(
                    new ArrayList<>(selections));
        }

        List<Selection> selections() { return selections; }

        int scheduledTaskCount() { return selections.size(); }

        JsonObject scheduleIndex(List<ExecutionTask> tasks,
                                 JsonObject regionPlanIdentity,
                                 JsonObject taskPlanIdentity)
                throws IOException {
            if (tasks.size() != selections.size()) {
                throw new IOException("region-path schedule emitted "
                        + tasks.size() + " tasks for " + selections.size()
                        + " selected occurrences");
            }
            Map<String, ExecutionTask> byGoal = new LinkedHashMap<>();
            for (ExecutionTask task : tasks) {
                ExecutionTask prior = byGoal.put(task.goalId(), task);
                if (prior != null) {
                    throw new IOException("duplicate scheduled goal: "
                            + task.goalId());
                }
            }
            JsonObject index = new JsonObject();
            index.addProperty("schemaVersion", 2);
            index.addProperty("kind", "RUNTIME_REGION_PATH_SCHEDULE_INDEX");
            index.addProperty("selectionAuthority",
                    "VM_OBSERVED_LINKED_REPLAY_SCOPE_V1");
            index.add("regionPlan", regionPlanIdentity.deepCopy());
            index.add("executionTaskPlan", taskPlanIdentity.deepCopy());
            JsonArray members = new JsonArray();
            JsonObject targetEntry = null;
            for (Selection selection : selections) {
                ExecutionTask task = byGoal.get(selection.goalId);
                if (task == null) {
                    throw new IOException("selected goal emitted no task: "
                            + selection.goalId);
                }
                JsonObject entry = selection.indexEntry(task.taskId());
                members.add(entry);
                if (selection.target) targetEntry = entry.deepCopy();
            }
            if (targetEntry == null) {
                throw new IOException("region-path schedule has no target");
            }
            index.add("target", targetEntry);
            index.add("members", members);
            return index;
        }
    }

    static final class Selection {
        final String campaignId;
        final String regionId;
        final String occurrenceId;
        final String goalId;
        final String relationKey;
        final boolean target;

        private Selection(String campaignId, RegionInstancePlan plan,
                          Goal goal, boolean target) {
            this.campaignId = campaignId;
            this.regionId = plan.regionId();
            this.occurrenceId = plan.occurrenceId();
            this.goalId = goal.goalId();
            this.relationKey = plan.relationKey();
            this.target = target;
        }

        static Selection target(Target target) {
            return new Selection(target.campaignId, target.plan, target.goal,
                    true);
        }

        static Selection dependency(String campaignId,
                                    RegionInstancePlan plan, Goal goal) {
            return new Selection(campaignId, plan, goal, false);
        }

        JsonObject indexEntry(String taskId) {
            JsonObject row = new JsonObject();
            row.addProperty("campaignId", campaignId);
            row.addProperty("regionId", regionId);
            row.addProperty("relationKey", relationKey);
            row.addProperty("occurrenceId", occurrenceId);
            row.addProperty("goalId", goalId);
            row.addProperty("taskId", taskId);
            row.addProperty("role", target ? "TARGET" : "DEPENDENCY");
            return row;
        }
    }

    private static final class Target {
        private static final Comparator<Target> EVIDENCE_ORDER =
                TargetRank.ORDER.thenComparing(
                        Comparator.comparingLong(
                                Target::observedFailureEvent).reversed());
        private static final Comparator<Target> ORDER = EVIDENCE_ORDER
                .thenComparing(value -> value.plan.regionId())
                .thenComparing(value -> value.plan.occurrenceId());

        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String occurrenceId;
        private final String campaignId;
        private TargetRank score = TargetRank.empty();

        private Target(RegionInstancePlan plan, Goal goal) {
            this.plan = plan;
            this.goal = goal;
            this.occurrenceId = PathObservation.plannedOccurrenceOf(
                    plan.occurrenceId());
            this.campaignId = "CAMPAIGN.REGION_PATH."
                    + ArtifactIO.sha256(plan.regionId() + "\n"
                    + occurrenceId + "\n" + goal.goalId());
        }

        private void rank(Map<String, JsonObject> topologyEdges) {
            score = TargetRank.of(this, topologyEdges.values());
        }

        /**
         * Distinguishes repeated executions of the target site after the
         * semantic rank ties. This event belongs to the target predicate
         * itself; it never selects a shared-state writer or a read-from edge.
         */
        private long observedFailureEvent() {
            long selected = -1L;
            for (JsonElement element : goal.branches()) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (bool(branch, "failureTarget", false)
                        && bool(branch, "observed", false)) {
                    selected = Math.max(selected, longInteger(branch,
                            "selectedRuntimeEventSeq", -1L));
                }
            }
            return selected;
        }

        private String context() {
            return occurrenceId + " rank=" + score;
        }

    }

    /** Evidence-only target rank; names, roles and application types do not
     * participate. */
    private static final class TargetRank {
        private static final Comparator<Target> ORDER = Comparator
                .comparing((Target value) ->
                        value.score.directProtocolInput).reversed()
                .thenComparing(value ->
                        value.score.allTargetInputsAnchored,
                        Comparator.reverseOrder())
                .thenComparing(Comparator.comparingInt(
                        (Target value) -> value.score.anchoredTargetInputs)
                        .reversed())
                .thenComparingInt(value ->
                        value.score.unresolvedTargetInputs)
                .thenComparingInt(value ->
                        value.score.unresolvedTopologyInputs);

        private final boolean directProtocolInput;
        private final boolean allTargetInputsAnchored;
        private final int anchoredTargetInputs;
        private final int unresolvedTargetInputs;
        private final int unresolvedTopologyInputs;

        private TargetRank(boolean directProtocolInput,
                           int anchoredTargetInputs,
                           int unresolvedTargetInputs,
                           int unresolvedTopologyInputs) {
            this.directProtocolInput = directProtocolInput;
            this.allTargetInputsAnchored = anchoredTargetInputs > 0
                    && unresolvedTargetInputs == 0;
            this.anchoredTargetInputs = anchoredTargetInputs;
            this.unresolvedTargetInputs = unresolvedTargetInputs;
            this.unresolvedTopologyInputs = unresolvedTopologyInputs;
        }

        private static TargetRank empty() {
            return new TargetRank(false, 0, Integer.MAX_VALUE,
                    Integer.MAX_VALUE);
        }

        private static TargetRank of(Target target,
                                     Iterable<JsonObject> topologyEdges) {
            Map<String, JsonObject> directProtocol = new LinkedHashMap<>();
            Set<String> unresolvedTopology = new LinkedHashSet<>();
            for (JsonObject edge : topologyEdges) {
                if (target.occurrenceId.equals(
                        PathObservation.plannedOccurrenceOf(
                                string(edge, "toOccurrenceId")))
                        && AutomaticRegionEdge.tracedExchangeCandidate(edge)) {
                    directProtocol.put(string(edge, "toInputPort"), edge);
                }
                if (unresolvedTopology(edge)) {
                    unresolvedTopology.add(
                            PathObservation.plannedOccurrenceOf(
                                    string(edge, "toOccurrenceId"))
                                    + "\n" + string(edge, "toInputPort"));
                }
            }
            Set<String> inputs = new LinkedHashSet<>();
            Set<String> proven = new LinkedHashSet<>();
            boolean direct = false;
            for (JsonElement element : target.goal.symbolize()) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                String input = firstInputName(action);
                if (input.isEmpty() || !inputs.add(input)) continue;
                if (directProtocol.containsKey(input)
                        || directProtocol.containsKey(
                        string(action, "portId"))) {
                    direct = true;
                    proven.add(input);
                } else if (exactRuntimeInput(target.occurrenceId, action)) {
                    proven.add(input);
                }
            }
            return new TargetRank(direct, proven.size(),
                    inputs.size() - proven.size(), unresolvedTopology.size());
        }

        private static String firstInputName(JsonObject action) {
            String symbol = string(action, "symbol");
            return symbol.isEmpty() ? string(action, "portId") : symbol;
        }

        private static boolean exactRuntimeInput(String occurrence,
                                                 JsonObject action) {
            if (!bool(action, "observed", false)) return false;
            for (JsonElement element : array(action, "runtimeAccesses")) {
                if (!element.isJsonObject()) continue;
                JsonObject access = element.getAsJsonObject();
                if (occurrence.equals(PathObservation.plannedOccurrenceOf(
                        string(access, "occurrenceId")))
                        && longInteger(access, "eventSeq", -1L) >= 0L) {
                    return true;
                }
            }
            return false;
        }

        private static boolean unresolvedTopology(JsonObject edge) {
            if ("RUNTIME_PROTOCOL_FLOW".equals(string(edge, "kind"))) {
                return !AutomaticRegionEdge.tracedExchangeCandidate(edge);
            }
            if ("RUNTIME_FIELD_FLOW".equals(string(edge, "kind"))) {
                return !AutomaticRegionEdge.sharedLocationCandidate(edge);
            }
            if (AutomaticRegionEdge.RUNTIME_REQUEST_CONTROL_EDGE_KIND.equals(
                    string(edge, "kind"))) {
                return !AutomaticRegionEdge.trustedRequestFaultControl(edge);
            }
            return true;
        }

        @Override
        public String toString() {
            return "{directProtocol=" + directProtocolInput
                    + ", targetInputs=" + anchoredTargetInputs + "/"
                    + (anchoredTargetInputs + unresolvedTargetInputs)
                    + ", unresolvedTopologyInputs="
                    + unresolvedTopologyInputs + "}";
        }
    }

}
