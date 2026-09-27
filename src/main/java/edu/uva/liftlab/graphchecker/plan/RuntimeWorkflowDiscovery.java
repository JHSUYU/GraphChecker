package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Selector;
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
     * The seed schedule: the declared target, then every other occurrence the
     * plan states is replayable, in recorded order.
     *
     * <p>No slice here: the closure is EXPLORE's. Trap: narrowing by observed
     * flow (walking {@code edgeBindings} back from the target) drops the
     * occurrence whose flip is the question, since a counterfactual writer
     * wrote nothing (hdfs-11741's {@code removeExpiredKeys}).</p>
     *
     * <p>Fail-closed on the plan only: the case must declare its target ({@link
     * #declaredTarget}).</p>
     */
    static Workflow workflow(List<RegionInstancePlan> plans,
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
            Goal goal = plan.goal();
            if (goal.kind().capturesTargetReach() && goal.replayable()
                    && !failureSites(goal).isEmpty()) {
                targets.add(new Target(plan, goal));
            }
        }
        if (targets.isEmpty()) {
            throw new IOException("runtime region plan has no replayable target");
        }

        // The target is the one the case DECLARED, never elected from evidence.
        // Other occurrences it names also carry targetReach (read by the reach
        // query, the obligation wave and the claim); the rest are dependencies.
        Set<String> targetReachGoals = anchorGoals(targets,
                declaredOccurrence);
        Target target = declaredTarget(targets, declaredOccurrence);
        List<Selection> selections = new ArrayList<>();
        selections.add(Selection.target(target,
                targetReachGoals.contains(target.goal.goalId())));
        for (RegionInstancePlan plan : plans) {
            if (plan.occurrenceId().equals(target.occurrenceId)) continue;
            // Not READY in the plan = not a task.
            Goal goal = plan.goal();
            if (!goal.replayable()) continue;
            selections.add(Selection.dependency(target.campaignId, plan,
                    goal, targetReachGoals.contains(goal.goalId())));
        }
        return new Workflow(selections);
    }

    /** Goals of every occurrence the declaration names (all capture target
     *  reach). */
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

    /** The k-th occurrence the declaration names, in recorded order (the {@link
     *  SelectorResolution} rule). No match is a named refusal, never a fallback
     *  or a rank. */
    private static Target declaredTarget(List<Target> targets,
                                         String declaredOccurrence)
            throws IOException {
        String declared = declaredOccurrence == null ? ""
                : declaredOccurrence.trim();
        List<String> observed = new ArrayList<>();
        for (Target candidate : targets) {
            observed.add(candidate.occurrenceId);
        }
        if (declared.isEmpty()) {
            throw new IOException("DECLARED_TARGET_OCCURRENCE_MISSING: this "
                    + "campaign states no declared_target_occurrence, and "
                    + "which occurrence of the annotated site it is about is "
                    + "not a question runtime evidence may answer; observed "
                    + "target occurrences: " + observed);
        }
        int k = declaredK(declared);
        Target named = SelectorResolution.kth(targets,
                candidate -> declares(declared, candidate.occurrenceId), k);
        if (named != null) return named;
        int matched = 0;
        for (Target candidate : targets) {
            if (declares(declared, candidate.occurrenceId)) matched++;
        }
        // The same listing as a missing declaration: a selector a region
        // change renamed is re-derived from it (tools/analysis/occurrences.py).
        throw new IOException("DECLARED_TARGET_OCCURRENCE_UNOBSERVED: "
                + declared + " names " + matched + " of the "
                + targets.size() + " observed target occurrence(s), and k="
                + k + " selects none of them; observed target occurrences: "
                + observed);
    }

    /** The {@code k} of a selector, or 1 for a resolved address. Anything else
     *  is refused: defaulting to 1 would silently pick the first observed
     *  target. */
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
            return 1;
        }
    }

    /** Whether a declaration names this occurrence (full address, or selector
     *  ignoring k). */
    static boolean declares(String declared, String occurrenceId) {
        String value = declared == null ? "" : declared.trim();
        if (value.isEmpty()) return false;
        if (value.equals(occurrenceId)) return true;
        // Unreadable plan id or declaration is a failure, not "no match".
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
        // SelectorResolution's rule minus k: k is resolved once, against the
        // seed.
        return SelectorResolution.names(selector, address);
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

    static final class Workflow {
        private final List<Selection> selections;

        private Workflow(List<Selection> selections) {
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
        /** Captures the annotated target's reach (the target and its sibling
         *  occurrences). */
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
