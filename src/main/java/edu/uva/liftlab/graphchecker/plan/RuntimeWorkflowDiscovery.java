package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
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
import java.util.TreeMap;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class RuntimeWorkflowDiscovery {

    private RuntimeWorkflowDiscovery() {
    }

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

        if (declaredOccurrence == null || declaredOccurrence.trim().isEmpty()) {
            throw new IOException("DECLARED_TARGET_OCCURRENCE_MISSING: this "
                    + "campaign states no declared_target_occurrence, and "
                    + "which occurrence of the declared target site it is "
                    + "about is not a question runtime evidence may answer");
        }
        Set<String> targetReachGoals = anchorGoals(targets,
                declaredOccurrence);
        Target target = declaredTarget(targets);
        List<Selection> selections = new ArrayList<>();
        selections.add(Selection.target(target,
                targetReachGoals.contains(target.goal.goalId())));
        for (RegionInstancePlan plan : plans) {
            if (plan.occurrenceId().equals(target.occurrenceId)) continue;
            Goal goal = plan.goal();
            if (!goal.replayable()) continue;
            selections.add(Selection.dependency(target.campaignId, plan,
                    goal, targetReachGoals.contains(goal.goalId())));
        }
        return new Workflow(selections);
    }

    private static Set<String> anchorGoals(
            List<Target> targets, String declaredOccurrence) {
        Set<String> byDeclaration = new LinkedHashSet<>();
        if (FIRST.equals(declaredOccurrence == null ? ""
                : declaredOccurrence.trim())) {
            byDeclaration.add(targets.get(0).goal.goalId());
            return byDeclaration;
        }
        for (Target candidate : targets) {
            if (declares(declaredOccurrence, candidate.occurrenceId)) {
                byDeclaration.add(candidate.goal.goalId());
            }
        }
        return byDeclaration;
    }

    public static final String FIRST = "first";

    public static String declaredOccurrence(List<String> observed,
            String declaredOccurrence,
            Function<String, List<String>> shapes) throws IOException {
        List<String> inWindow = new ArrayList<>();
        Map<String, List<String>> beforeWindow = new LinkedHashMap<>();
        for (String candidate : observed) {
            List<String> shape = shapes.apply(candidate);
            if (ContextShape.rootedInWindow(shape)) {
                inWindow.add(candidate);
            } else {
                beforeWindow.put(candidate, shape);
            }
        }
        if (inWindow.isEmpty()) {
            throw new IOException("DECLARED_TARGET_BEFORE_WINDOW: each of "
                    + "the " + observed.size() + " observed target "
                    + "occurrence(s) rests on a chain not known back to its "
                    + "root inside the window (a message sent before it, or "
                    + "one whose sender nothing names: a ? hop), which no "
                    + "replay holds; occurrence -> shape: " + beforeWindow);
        }
        String declared = declaredOccurrence == null ? ""
                : declaredOccurrence.trim();
        if (FIRST.equals(declared)) return inWindow.get(0);
        int k = declaredK(declared);
        String named = SelectorResolution.kth(inWindow,
                candidate -> declares(declared, candidate), k);
        if (named != null) return named;
        int matched = 0;
        for (String candidate : inWindow) {
            if (declares(declared, candidate)) matched++;
        }
        throw new IOException("DECLARED_TARGET_OCCURRENCE_UNOBSERVED: "
                + declared + " names " + matched + " of the "
                + inWindow.size() + " observed target occurrence(s) inside "
                + "the window, and k=" + k + " selects none of them; observed "
                + "target occurrences: " + inWindow + "; on a chain not "
                + "known back to its root (DECLARED_TARGET_BEFORE_WINDOW): "
                + beforeWindow.keySet());
    }

    private static Target declaredTarget(List<Target> targets)
            throws IOException {
        List<Target> marked = new ArrayList<>();
        for (Target candidate : targets) {
            if (optionalBool(candidate.plan.json(),
                    RuntimeSelectedRegionFinalizer.DECLARED_OCCURRENCE,
                    false)) {
                marked.add(candidate);
            }
        }
        if (marked.size() == 1) return marked.get(0);
        throw new IOException("DECLARED_TARGET_OCCURRENCE_UNPINNED: the "
                + "region plan marks " + marked.size() + " of its "
                + targets.size() + " target occurrence(s) as the declared "
                + "one; the seed's aggregation resolves the declaration "
                + "exactly once (RuntimeSelectedRegionFinalizer)");
    }

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

    private static boolean resolved(String declared) {
        try {
            OccurrenceAddress.parse(declared);
            return true;
        } catch (RuntimeException notAnAddress) {
            return false;
        }
    }

    static boolean declares(String declared, String occurrenceId) {
        String value = declared == null ? "" : declared.trim();
        if (value.isEmpty()) return false;
        if (value.equals(occurrenceId)) return true;
        if (FIRST.equals(value)) return false;
        if (resolved(value)) return false;
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
        return SelectorResolution.names(selector, address);
    }

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
        private final List<Selection> cut;
        private final int keptDepth;

        private Workflow(List<Selection> selections) {
            this(selections, Collections.<Selection>emptyList(), -1);
        }

        private Workflow(List<Selection> selections, List<Selection> cut,
                         int keptDepth) {
            this.selections = Collections.unmodifiableList(
                    new ArrayList<>(selections));
            this.cut = Collections.unmodifiableList(new ArrayList<>(cut));
            this.keptDepth = keptDepth;
        }

        List<Selection> selections() { return selections; }

        int scheduledTaskCount() { return selections.size(); }

        int cutCount() { return cut.size(); }

        int keptDepth() { return keptDepth; }

        Workflow nearest(int maxJobs) {
            if (selections.size() <= maxJobs) return this;
            TreeMap<Integer, Integer> byDepth = new TreeMap<>();
            for (Selection selection : selections) {
                byDepth.merge(selection.depth, 1, Integer::sum);
            }
            int kept = -1;
            int count = 0;
            for (Map.Entry<Integer, Integer> level : byDepth.entrySet()) {
                if (count + level.getValue() > maxJobs) break;
                count += level.getValue();
                kept = level.getKey();
            }
            if (kept < 0 || selections.get(0).depth > kept) return null;
            List<Selection> near = new ArrayList<>();
            List<Selection> far = new ArrayList<>();
            for (Selection selection : selections) {
                (selection.depth <= kept ? near : far).add(selection);
            }
            return new Workflow(near, far, kept);
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
            if (!cut.isEmpty()) {
                JsonObject closureCut = new JsonObject();
                closureCut.addProperty("keptDepth", keptDepth);
                closureCut.addProperty("occurrences", cut.size());
                TreeMap<Integer, Integer> byDepth = new TreeMap<>();
                for (Selection selection : cut) {
                    byDepth.merge(selection.depth, 1, Integer::sum);
                }
                JsonObject depths = new JsonObject();
                for (Map.Entry<Integer, Integer> level : byDepth.entrySet()) {
                    depths.addProperty(String.valueOf(level.getKey()),
                            level.getValue());
                }
                closureCut.add("byDepth", depths);
                index.add("closureCut", closureCut);
            }
            return index;
        }
    }

    static final class Selection {
        final String campaignId;
        final String regionId;
        final String occurrenceId;
        final String goalId;
        final boolean target;
        final boolean targetReach;
        final int depth;

        private Selection(String campaignId, RegionInstancePlan plan,
                          Goal goal, boolean target, boolean targetReach) {
            this.campaignId = campaignId;
            this.regionId = plan.regionId();
            this.occurrenceId = plan.occurrenceId();
            this.goalId = goal.goalId();
            this.target = target;
            this.targetReach = targetReach;
            this.depth = optionalInteger(plan.json(),
                    RuntimeSelectedRegionFinalizer.DEMAND_DEPTH, 0);
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
