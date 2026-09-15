package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.Selector;
import edu.uva.liftlab.graphchecker.d3.plan.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.d3.plan.RegionInstancePlan.Goal;

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

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/** Selects one target and its VM-observed linked replay scope. */
public final class RuntimeWorkflowDiscovery {
    private static final String EXPLICIT_FAULT_ENTRY =
            "EXPLICIT_FAULT_ENTRY";

    private RuntimeWorkflowDiscovery() {
    }

    static RankedWorkflow candidateWorkflow(List<RegionInstancePlan> plans,
                                            String declaredOccurrence)
            throws IOException {
        return rankedWorkflow(plans, Collections.<JsonObject>emptyList(),
                Scope.CANDIDATE, declaredOccurrence);
    }

    /** The first replay activates the target's complete dynamic ancestry. */
    static RankedWorkflow seedReplayWorkflow(List<RegionInstancePlan> plans,
                                             String declaredOccurrence)
            throws IOException {
        return rankedWorkflow(plans, Collections.<JsonObject>emptyList(),
                Scope.SEED_VALUE, declaredOccurrence);
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
            Collection<JsonObject> observedSummaries,
            String declaredOccurrence) throws IOException {
        return rankedWorkflow(plans, observedSummaries,
                observedSummaries == null || observedSummaries.isEmpty()
                        ? Scope.CANDIDATE : Scope.OBSERVED,
                declaredOccurrence);
    }

    private static RankedWorkflow rankedWorkflow(
            List<RegionInstancePlan> plans,
            Collection<JsonObject> observedSummaries,
            Scope scope, String declaredOccurrence) throws IOException {
        if (plans == null || plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        Map<String, RegionInstancePlan> byOccurrence = new LinkedHashMap<>();
        Map<String, JsonObject> edges = new LinkedHashMap<>();
        List<Target> targets = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            String occurrence = plan.occurrenceId();
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
        // The occurrence(s) this campaign is about, decided before the
        // election so a declared target is the one elected: a case that
        // names which instance can fail has said which occurrence carries
        // the replay closure, and ranking is how the answer is found when
        // it did not.
        Set<String> anchors = anchorGoals(targets, declaredOccurrence);
        Target target = targets.get(0);
        for (Target candidate : targets) {
            if (anchors.contains(candidate.goal.goalId())) {
                target = candidate;
                break;
            }
        }
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
            closure = observedActivationScope(target, candidateClosure,
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
        // The occurrence(s) of the annotated site this campaign is about.
        // A campaign is target-directed: the anchor is the occurrence at
        // which the RECORDING took the fatal arm -- the annotated
        // exception's own occurrence -- or the one the case declares.
        // Every other occurrence reached the site healthily and carries no
        // verdict to state, so it is scheduled as a dependency and named
        // rather than composed and judged.  Downstream stages read this
        // flag for the reach query, the obligation wave and the claim.
        Set<String> targetReachGoals = anchors;
        List<Selection> selections = new ArrayList<>();
        // Preserve the seed task's symbolic frontier and therefore its stable
        // task identity.  The exact replay closure narrows which occurrences
        // need path summaries; it does not rewrite the already executed
        // target task or the candidate edges retained for instrumentation.
        selections.add(Selection.target(target,
                targetReachGoals.contains(target.goal.goalId())));

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
                        plan, goal,
                        targetReachGoals.contains(goal.goalId())));
            }
        }
        return new RankedWorkflow(selections);
    }

    /**
     * The goals of the occurrence(s) this campaign is about.
     *
     * <p>Two answers. The case's own declaration, when it states one --
     * "we know which target instance can fail" -- read as an occurrence
     * address, or as the request family and k when it names no region.
     * Otherwise every observed occurrence: a recording is the healthy path
     * by nature -- the fatal condition is what the composition builds --
     * so nothing in the corpus distinguishes one occurrence of the site
     * from another, and none is privileged.</p>
     */
    private static Set<String> anchorGoals(
            List<Target> targets, String declaredOccurrence) {
        Set<String> everyGoal = new LinkedHashSet<>();
        for (Target candidate : targets) {
            everyGoal.add(candidate.goal.goalId());
        }
        String declared = declaredOccurrence == null ? ""
                : declaredOccurrence.trim();
        if (!declared.isEmpty()) {
            Set<String> byDeclaration = new LinkedHashSet<>();
            for (Target candidate : targets) {
                if (declares(declared, candidate.occurrenceId)) {
                    byDeclaration.add(candidate.goal.goalId());
                }
            }
            // A declaration naming no observed occurrence keeps every
            // occurrence rather than selecting none: the composition then
            // states what the case declared beside what it observed.
            if (!byDeclaration.isEmpty()) return byDeclaration;
        }
        return everyGoal;
    }

    /**
     * Whether a declaration names this occurrence: the whole address, or
     * the request family and k when the declaration states no region.
     */
    static boolean declares(String declared, String occurrenceId) {
        String value = declared == null ? "" : declared.trim();
        if (value.isEmpty()) return false;
        if (value.equals(occurrenceId)) return true;
        final OccurrenceAddress address;
        final Selector selector;
        try {
            address = OccurrenceAddress.parse(occurrenceId);
            selector = OccurrenceAddress.parseSelector(value);
        } catch (RuntimeException unreadable) {
            // Neither a resolved id nor a selector this build can read.
            return false;
        }
        // The same rule SelectorResolution resolves by, minus the k: this
        // asks whether an occurrence is one of the declaration's candidates,
        // and which of them the campaign is about is resolved once, against
        // the seed session, where the order that makes k mean anything is.
        return selector.matches(address,
                SelectorResolution.apiOf(selector, address));
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
            if (optionalBool(branch, "failureTarget", false)
                    && !optionalBool(branch, "loopControlGuard", false)
                    && optionalBool(branch, "observed", false)
                    && branch.has("requiredOutcome")
                    && !branch.get("requiredOutcome").isJsonNull()) {
                String site = optionalString(branch, "siteId");
                if (!site.isEmpty()) result.add(site);
            }
        }
        return result;
    }

    private static boolean explicitFaultEntry(RegionInstancePlan plan) {
        return EXPLICIT_FAULT_ENTRY.equals(optionalString(plan.json(),
                "rootAuthority"));
    }

    private enum Scope {
        CANDIDATE,
        SEED_VALUE,
        OBSERVED
    }

    /**
     * The slice, restricted to the occurrences this recording actually ran.
     *
     * <p>Which occurrences are in scope is one decision, made once over the
     * region graph by root dependence: an occurrence is in the slice because
     * it reads a root, carries a root-dependent value, or is the target.
     * The only thing a recording adds is whether that occurrence
     * <em>activated</em> at all, which is why a planned occurrence with no
     * summary row is dropped here.</p>
     *
     * <p>What is deliberately not done is re-deriving the scope from
     * observed data flow.  A walk backwards from the target over the writes
     * this run happened to make keeps only the producers that produced
     * something -- and on a healthy recording the occurrence whose root flip
     * is the whole question is exactly the one that produced nothing.  A
     * counterfactual writer is invisible to a walk over what was written,
     * and narrowing the slice by that one occurrence is how a campaign comes
     * to explore nothing at all.</p>
     */
    private static Set<String> observedActivationScope(
            Target target, Set<String> candidateClosure,
            Collection<JsonObject> summaries) {
        Set<String> activated = new LinkedHashSet<>();
        for (JsonObject summary : summaries) {
            if (summary == null) continue;
            String occurrence = plannedOccurrence(summary);
            if (!occurrence.isEmpty()) activated.add(occurrence);
        }
        Set<String> selected = new LinkedHashSet<>();
        selected.add(target.occurrenceId);
        for (String occurrence : candidateClosure) {
            if (activated.contains(occurrence)) selected.add(occurrence);
        }
        return selected;
    }





    private static String plannedOccurrence(JsonObject row) {
        String planned = optionalString(row, "plannedOccurrenceId");
        return planned.isEmpty() ? optionalString(row, "occurrenceId") : planned;
    }













    private static void indexEdges(Map<String, JsonObject> indexed,
                                   JsonArray candidates) throws IOException {
        for (JsonElement element : candidates) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            if (!AutomaticRegionEdge.summaryTraversalBinding(edge)) continue;
            String from = optionalString(edge, "fromOccurrenceId");
            String to = optionalString(edge, "toOccurrenceId");
            if (from.isEmpty() || to.isEmpty()) continue;
            String id = optionalString(edge, "edgeId");
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
                String to = optionalString(edge, "toOccurrenceId");
                String from = optionalString(edge, "fromOccurrenceId");
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
            String from = optionalString(edge, "fromOccurrenceId");
            String to = optionalString(edge, "toOccurrenceId");
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
            if (optionalBool(branch, "failureTarget", false)
                    && !optionalBool(branch, "loopControlGuard", false)
                    && optionalBool(branch, "observed", false)
                    && branch.has("requiredOutcome")
                    && !branch.get("requiredOutcome").isJsonNull()
                    && !optionalString(branch, "siteId").isEmpty()) {
                return true;
            }
        }
        return false;
    }

    static final class RankedWorkflow {
        private final List<Selection> selections;

        private RankedWorkflow(List<Selection> selections) {
            this.selections = Collections.unmodifiableList(
                    new ArrayList<>(selections));
        }

        List<Selection> selections() { return selections; }

        int scheduledTaskCount() { return selections.size(); }

        /** This workflow without the dependencies {@code keep} refuses.
         *  The target is the workflow's reason to exist and is never
         *  refused. */
        RankedWorkflow retaining(
                java.util.function.Predicate<Selection> keep) {
            List<Selection> kept = new ArrayList<>();
            for (Selection selection : selections) {
                if (selection.target || keep.test(selection)) {
                    kept.add(selection);
                }
            }
            return new RankedWorkflow(kept);
        }

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
        /** Whether this member's goal captures the annotated target's reach.
         *  True for the elected target and for every other observed
         *  occurrence of the same annotated site. */
        final boolean targetReach;

        private Selection(String campaignId, RegionInstancePlan plan,
                          Goal goal, boolean target, boolean targetReach) {
            this.campaignId = campaignId;
            this.regionId = plan.regionId();
            this.occurrenceId = plan.occurrenceId();
            this.goalId = goal.goalId();
            this.relationKey = plan.relationKey();
            this.target = target;
            this.targetReach = targetReach;
        }

        static Selection target(Target target, boolean targetReach) {
            return new Selection(target.campaignId, target.plan, target.goal,
                    true, targetReach);
        }

        static Selection dependency(String campaignId,
                                    RegionInstancePlan plan, Goal goal,
                                    boolean targetReach) {
            return new Selection(campaignId, plan, goal, false, targetReach);
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
            row.addProperty("targetReachGoal", targetReach);
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
            this.occurrenceId = plan.occurrenceId();
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
                if (optionalBool(branch, "failureTarget", false)
                        && optionalBool(branch, "observed", false)) {
                    selected = Math.max(selected, optionalLongInteger(branch,
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
                if (target.occurrenceId.equals(optionalString(edge, "toOccurrenceId"))
                        && AutomaticRegionEdge.tracedExchangeCandidate(edge)) {
                    directProtocol.put(optionalString(edge, "toInputPort"), edge);
                }
                if (unresolvedTopology(edge)) {
                    unresolvedTopology.add(optionalString(edge, "toOccurrenceId")
                            + "\n" + optionalString(edge, "toInputPort"));
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
                        optionalString(action, "portId"))) {
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
            String symbol = optionalString(action, "symbol");
            return symbol.isEmpty() ? optionalString(action, "portId") : symbol;
        }

        private static boolean exactRuntimeInput(String occurrence,
                                                 JsonObject action) {
            if (!optionalBool(action, "observed", false)) return false;
            for (JsonElement element : array(action, "runtimeAccesses")) {
                if (!element.isJsonObject()) continue;
                JsonObject access = element.getAsJsonObject();
                if (occurrence.equals(optionalString(access, "occurrenceId"))
                        && optionalLongInteger(access, "eventSeq", -1L) >= 0L) {
                    return true;
                }
            }
            return false;
        }

        private static boolean unresolvedTopology(JsonObject edge) {
            if ("RUNTIME_PROTOCOL_FLOW".equals(optionalString(edge, "kind"))) {
                return !AutomaticRegionEdge.tracedExchangeCandidate(edge);
            }
            if ("RUNTIME_FIELD_FLOW".equals(optionalString(edge, "kind"))) {
                return !AutomaticRegionEdge.sharedLocationCandidate(edge);
            }
            if (AutomaticRegionEdge.RUNTIME_REQUEST_CONTROL_EDGE_KIND.equals(
                    optionalString(edge, "kind"))) {
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
