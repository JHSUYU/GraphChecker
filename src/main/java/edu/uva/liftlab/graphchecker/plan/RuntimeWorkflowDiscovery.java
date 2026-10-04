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
     * <p>Fail-closed on the plan only: the case must declare its target, and
     * the seed resolved the declaration ({@link #declaredOccurrence}) onto one
     * of the plan's target rows ({@link #declaredTarget}).</p>
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

    /**
     * The first observed occurrence of the declared target site in THIS
     * recording that the window holds back to its root ({@link
     * #declaredOccurrence}), fixed at the seed like any declaration and
     * handed to every later stage as the address PLAN resolved it to: what a
     * case declares
     * whose failure is the target's first occurrence (solr-18406), and what
     * a case declaring none gets.  An address read off one recording need
     * not name anything in the next.
     */
    public static final String FIRST = "first";

    /**
     * The occurrence a declaration names among the observed target
     * occurrences the window holds back to their root, in recorded order:
     * {@link #FIRST}, the first; a resolved address, itself; a selector, its
     * k-th match (the {@link SelectorResolution} rule).  Resolved once, at
     * the seed ({@code causynth.RuntimeSelectedRegionFinalizer}, which plans
     * only the question's own {@code (r,c)} around it and marks it on its
     * plan row, {@link #declaredTarget}); every later stage reads that.  No
     * match is a named refusal, never a fallback or a rank.
     *
     * <p>An occurrence whose chain is not known back to its root ({@code
     * shapes}, {@link ContextShape#rootedInWindow}) rests on a message the
     * window's order does not hold: one sent before the window, which a
     * replay answers inside or before its own window as its timing falls,
     * or one whose sender nothing names.  Round HG2's hdfs-adhoc-19 declared
     * {@code first}: the DataNode's first block report, sent before the
     * window, was answered inside it in the recording and before it in the
     * replay, which then never ran the declared finalize command.  Such an
     * occurrence is never the question (it still seeds the closure walk);
     * none other observed is a refusal naming them with their shapes,
     * {@code DECLARED_TARGET_BEFORE_WINDOW}.</p>
     *
     * @param shapes an observed occurrence's context shape over the
     *        recording's senders
     */
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
        // A selector a region change renamed is re-derived from the listing
        // this refusal states.
        throw new IOException("DECLARED_TARGET_OCCURRENCE_UNOBSERVED: "
                + declared + " names " + matched + " of the "
                + inWindow.size() + " observed target occurrence(s) inside "
                + "the window, and k=" + k + " selects none of them; observed "
                + "target occurrences: " + inWindow + "; on a chain not "
                + "known back to its root (DECLARED_TARGET_BEFORE_WINDOW): "
                + beforeWindow.keySet());
    }

    /** The target row the seed marked as the declared occurrence ({@link
     *  #declaredOccurrence}); exactly one, or the plan is refused. */
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

    /** Whether a declaration is a resolved occurrence address. */
    private static boolean resolved(String declared) {
        try {
            OccurrenceAddress.parse(declared);
            return true;
        } catch (RuntimeException notAnAddress) {
            return false;
        }
    }

    /** Whether a declaration names this occurrence (full address, or selector
     *  ignoring k). */
    static boolean declares(String declared, String occurrenceId) {
        String value = declared == null ? "" : declared.trim();
        if (value.isEmpty()) return false;
        if (value.equals(occurrenceId)) return true;
        if (FIRST.equals(value)) return false;
        // A resolved address names the occurrence it spells and no other.
        if (resolved(value)) return false;
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
        /** The dependencies {@link #nearest} left out, in plan order. */
        private final List<Selection> cut;
        /** The deepest demand depth {@link #nearest} kept. */
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

        /** How many dependencies {@link #nearest} left out. */
        int cutCount() { return cut.size(); }

        int keptDepth() { return keptDepth; }

        /**
         * The nearest part of this closure that fits {@code maxJobs} tasks:
         * the target and every dependency whose demand depth (the hops of
         * the chain that admitted it, {@link
         * RuntimeSelectedRegionFinalizer#DEMAND_DEPTH}) is at most the
         * deepest level that fits whole.  Never part of a level: its
         * occurrences are equally near, and keeping some would be an
         * arbitrary choice.  This workflow when it fits; null when not even
         * the target's own level does.
         */
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
                // The closure PLAN did not plan (#nearest): the campaign
                // names it (run_engine.sh campaign_stream_truncation).
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
        /** Captures the declared target's reach (the target and its sibling
         *  occurrences). */
        final boolean targetReach;
        /** Demand hops from the target; a target occurrence states none. */
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

    /** One observed occurrence of the declared target site. */
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
