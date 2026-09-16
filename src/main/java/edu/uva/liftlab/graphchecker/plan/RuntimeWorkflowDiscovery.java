package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Selector;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan.Goal;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Selects the declared target and schedules the whole region plan with it. */
public final class RuntimeWorkflowDiscovery {

    private RuntimeWorkflowDiscovery() {
    }

    /**
     * The seed schedule: the declared target, then every other planned
     * occurrence the plan states is replayable.
     *
     * <p>PLAN owns no slice of its own.  The closure is EXPLORE's, computed
     * over the static scope map and the recorded rows (closure v2), so a
     * second scope here could only be a weaker copy of it -- and it was: the
     * walk this replaces started at the target and followed {@code
     * edgeBindings} backwards over the writes the recording happened to
     * make, keeping only producers that produced something.  On a healthy
     * recording the occurrence whose root flip is the whole question is
     * exactly the one that produced nothing.  hdfs-11741's {@code
     * removeExpiredKeys} reads the clock, decides an expiry and removes
     * nothing: six planned READY occurrences, no outgoing field flow, and so
     * no seed task at all under the old walk, which is a campaign that
     * explores everything except the thing the case declared.  A
     * counterfactual writer is invisible to a walk over what was written, so
     * there is no narrowing by observed flow here and no admission driven by
     * {@code edgeBindings}: every replayable occurrence of the region plan
     * is a seed task.</p>
     *
     * <p>What still decides anything here is fail-closed and about the plan,
     * not about flow: the case must declare which occurrence of the
     * annotated site the campaign is about ({@link #declaredTarget}), and an
     * occurrence that states two replayable goals is refused rather than
     * scheduled twice ({@link #onlyReplayableGoal}).  Order is the target
     * first and then the plan's own recorded order, which is the order the
     * recording published the activations in and therefore the order a case
     * author counted.</p>
     */
    static RankedWorkflow workflow(List<RegionInstancePlan> plans,
                                   String declaredOccurrence)
            throws IOException {
        if (plans == null || plans.isEmpty()) {
            throw new IOException("runtime region plan is empty");
        }
        Set<String> occurrences = new LinkedHashSet<>();
        List<Target> targets = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            String occurrence = plan.occurrenceId();
            if (!occurrences.add(occurrence)) {
                throw new IOException("duplicate planned region occurrence: "
                        + occurrence);
            }
            for (Goal goal : plan.goals()) {
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
        //
        // targetReach marks the occurrence(s) of the annotated site this
        // campaign is about.  Every other occurrence reached the site
        // healthily and carries no verdict to state, so it is scheduled as a
        // dependency and named rather than composed and judged.  Downstream
        // stages read this flag for the reach query, the obligation wave and
        // the claim.
        Set<String> targetReachGoals = anchorGoals(targets,
                declaredOccurrence);
        Target target = declaredTarget(targets, declaredOccurrence);
        List<Selection> selections = new ArrayList<>();
        selections.add(Selection.target(target,
                targetReachGoals.contains(target.goal.goalId())));
        for (RegionInstancePlan plan : plans) {
            if (plan.occurrenceId().equals(target.occurrenceId)) continue;
            // An occurrence the plan states no replayable goal for is not a
            // task: "READY" is the plan's own word for "this occurrence can
            // be replayed", and nothing here overrides it.
            Goal goal = onlyReplayableGoal(plan);
            if (goal == null) continue;
            selections.add(Selection.dependency(target.campaignId, plan,
                    goal, targetReachGoals.contains(goal.goalId())));
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

    /**
     * The {@code k} of a declaration, or 1 for an already resolved id.
     *
     * <p>Those are the only two readings.  Text that is neither a selector
     * nor an address is a declaration nothing can resolve, and answering
     * {@code k = 1} for it silently selected the FIRST observed target
     * occurrence of a campaign whose declaration this build cannot read.</p>
     */
    private static int declaredK(String declared) throws IOException {
        try {
            return Math.max(1, OccurrenceAddress.parseSelector(declared).k());
        } catch (RuntimeException notASelector) {
            try {
                OccurrenceAddress.parse(declared);
            } catch (RuntimeException notAnAddress) {
                throw new IOException(
                        "DECLARED_TARGET_OCCURRENCE_UNREADABLE: " + declared
                                + " is neither an occurrence selector ("
                                + notASelector.getMessage() + ") nor a "
                                + "resolved occurrence address ("
                                + notAnAddress.getMessage() + ")");
            }
            // A resolved address names one occurrence, so its k is 1.
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
        // Two different failures, and neither is "this occurrence does not
        // match": a plan row whose own occurrence id this build cannot read
        // is a corrupt plan, and a declaration it cannot read is a campaign
        // whose target nothing can resolve.  Both used to answer `false`,
        // which reads as "not the target" and left the refusal to
        // declaredTarget's count -- naming the wrong thing.
        final OccurrenceAddress address;
        try {
            address = OccurrenceAddress.parse(occurrenceId);
        } catch (RuntimeException unreadable) {
            throw new IllegalStateException("PLANNED_OCCURRENCE_UNREADABLE: "
                    + occurrenceId, unreadable);
        }
        final Selector selector;
        try {
            selector = OccurrenceAddress.parseSelector(value);
        } catch (RuntimeException notASelector) {
            throw new IllegalStateException(
                    "DECLARED_TARGET_OCCURRENCE_UNREADABLE: " + value,
                    notASelector);
        }
        // The same rule SelectorResolution resolves by, minus the k: this
        // asks whether an occurrence is one of the declaration's candidates,
        // and which of them the campaign is about is resolved once, against
        // the seed session, where the order that makes k mean anything is.
        return selector.matches(address,
                SelectorResolution.apiOf(selector, address));
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
