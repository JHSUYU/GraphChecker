package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Selector;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan.Goal;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Selects one target and its VM-observed linked replay scope. */
public final class RuntimeWorkflowDiscovery {
    private static final String EXPLICIT_FAULT_ENTRY =
            "EXPLICIT_FAULT_ENTRY";

    private RuntimeWorkflowDiscovery() {
    }

    /**
     * The candidate scope: the target and the candidate closure that replays
     * with it.
     *
     * <p>The candidate graph is the instrumentation frontier and the replay
     * scope both.  There used to be a third scope that narrowed it to the
     * occurrences a previous iteration's result envelope reported as
     * activated; the envelope is gone, and the narrowing was wrong anyway --
     * see the comment at the closure below.  With it went the last thing that
     * told a candidate schedule from a seed-replay one HERE: both asked for
     * the same closure, so this is one entry rather than two names for it,
     * and what a seed replay still varies is withSeedReplayGroup.</p>
     */
    static RankedWorkflow workflow(List<RegionInstancePlan> plans,
                                   String declaredOccurrence)
            throws IOException {
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

        // The occurrence this campaign is about is the one the case
        // DECLARED.  There is no election: ranking observed evidence to
        // decide which instance of the annotated site "matters" is a
        // decision outside the slice, and a case that declares nothing is
        // refused by name rather than answered by a heuristic.
        Set<String> anchors = anchorGoals(targets, declaredOccurrence);
        Target target = declaredTarget(targets, declaredOccurrence);
        // A linked replay contains only the observed dynamic ancestry of the
        // target. Static demand still guides instrumentation and later
        // topology discovery; making an unrelated observed occurrence a
        // mandatory replay member can prevent the real causal chain from
        // executing at all.
        Set<String> candidateClosure = equivalentTargetTopologyScope(target,
                targets, byOccurrence, edges);
        // Which occurrences are in scope is one decision, made once over the
        // region graph by root dependence: an occurrence is in the slice
        // because it reads a root, carries a root-dependent value, or is the
        // target.  A concrete object or container is still a carrier -- its
        // fields or elements can hold expressions propagated by an upstream
        // region -- so nothing prunes the producer that populated it.
        //
        // What is deliberately not re-derived is the scope, from observed
        // data flow.  A walk backwards from the target over the writes this
        // run happened to make keeps only the producers that produced
        // something -- and on a healthy recording the occurrence whose root
        // flip is the whole question is exactly the one that produced
        // nothing.  A counterfactual writer is invisible to a walk over what
        // was written, and narrowing the slice by that one occurrence is how
        // a campaign comes to explore nothing at all.  That narrowing was
        // the result envelope's last reader, and it is gone with it.
        Set<String> closure = candidateClosure;
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
     * The goals of the occurrences the case's declaration names.
     *
     * <p>The declaration is the whole answer: an occurrence address, or the
     * region and request family with a {@code k}.  Every occurrence it names
     * captures the annotated target's reach; the one the {@code k} selects
     * is the campaign's target.</p>
     */
    private static Set<String> anchorGoals(
            List<Target> targets, String declaredOccurrence) {
        Set<String> byDeclaration = new LinkedHashSet<>();
        for (Target candidate : targets) {
            if (declares(declaredOccurrence, candidate.occurrenceId)) {
                byDeclaration.add(candidate.goal.goalId());
            }
        }
        return byDeclaration;
    }

    /**
     * The target occurrence the case declared, in region-plan order.
     *
     * <p>The same rule {@link SelectorResolution} resolves a declaration by,
     * over the rows this stage has: the {@code k}-th occurrence the
     * declaration names, counted in the order the recording published them.
     * Seed order is the resolution order because that is what a case author
     * counted.  A declaration that names none of the observed target
     * occurrences is a named refusal, not a fallback to "every occurrence"
     * and not a rank.</p>
     */
    private static Target declaredTarget(List<Target> targets,
                                         String declaredOccurrence)
            throws IOException {
        String declared = declaredOccurrence == null ? ""
                : declaredOccurrence.trim();
        if (declared.isEmpty()) {
            List<String> observed = new ArrayList<>();
            for (Target candidate : targets) {
                observed.add(candidate.occurrenceId);
            }
            throw new IOException("DECLARED_TARGET_OCCURRENCE_MISSING: this "
                    + "campaign states no declared_target_occurrence, and "
                    + "which occurrence of the annotated site it is about is "
                    + "not a question runtime evidence may answer; observed "
                    + "target occurrences: " + observed);
        }
        int k = declaredK(declared);
        int matched = 0;
        for (Target candidate : targets) {
            if (declares(declared, candidate.occurrenceId)
                    && ++matched == k) {
                return candidate;
            }
        }
        throw new IOException("DECLARED_TARGET_OCCURRENCE_UNOBSERVED: "
                + declared + " names " + matched + " of the "
                + targets.size() + " observed target occurrence(s), and k="
                + k + " selects none of them");
    }

    /** The {@code k} of a declaration, or 1 for an already resolved id. */
    private static int declaredK(String declared) {
        try {
            return Math.max(1, OccurrenceAddress.parseSelector(declared).k());
        } catch (RuntimeException notASelector) {
            return 1;
        }
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

    /** The observed failure-target branch sites one goal names. */
    private static Set<String> failureSites(Goal goal) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : goal.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (optionalBool(branch, "failureTarget", false)
                    && optionalBool(branch, "observed", false)) {
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
        return !failureSites(goal).isEmpty();
    }

    static final class RankedWorkflow {
        private final List<Selection> selections;

        private RankedWorkflow(List<Selection> selections) {
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
            row.addProperty("occurrenceId", occurrenceId);
            row.addProperty("goalId", goalId);
            row.addProperty("taskId", taskId);
            row.addProperty("role", target ? "TARGET" : "DEPENDENCY");
            row.addProperty("targetReachGoal", targetReach);
            return row;
        }
    }

    /** One observed occurrence of the annotated target site. */
    private static final class Target {
        private final RegionInstancePlan plan;
        private final Goal goal;
        private final String occurrenceId;
        private final String campaignId;

        private Target(RegionInstancePlan plan, Goal goal) {
            this.plan = plan;
            this.goal = goal;
            this.occurrenceId = plan.occurrenceId();
            this.campaignId = "CAMPAIGN.REGION_PATH."
                    + ArtifactIO.sha256(plan.regionId() + "\n"
                    + occurrenceId + "\n" + goal.goalId());
        }
    }

}
