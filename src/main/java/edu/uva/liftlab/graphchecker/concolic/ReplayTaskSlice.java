package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Which planned occurrences a replay still has to execute symbolically.
 *
 * <p>The runtime plan admits every occurrence in the target's dynamic
 * ancestry, and each one costs a symbolic activation inside the replayed
 * workload.  An occurrence earns its replay only when it can carry a root's
 * influence <em>to the read that fails</em>, which is one question asked in
 * two directions.</p>
 *
 * <p><b>Bidirectional slice.</b>  A location matters only where the forward
 * closure of the root cells meets the backward closure of the fatal read,
 * taken over the refined dataflow graph and, between occurrences, over the
 * plan's shared-location, protocol and request-control edges.  A writer
 * outside that intersection is a recorded constant for this failure however
 * root-dependent its value is: either no root can move it, or nothing the
 * failing branch reads ever consults it.  Root dependence is therefore
 * seeded at {@link #ROOT_SITE} alone; writing a cared location is a keep
 * <em>reason</em> ({@link #CARRIER_WRITER}) and never a fresh source of
 * root influence, because a write whose value the recording fixed replays
 * that value on every arm.</p>
 *
 * <p>Repetition alone never narrows anything.  Two occurrences of one
 * region under one source and one request used to be read as a loop
 * stepping over the elements of a structure, whose arms differ only by
 * which root sites produced the value, and a cohort of three or more
 * replayed one occurrence per distinct root provenance.  But an occurrence
 * reaches this point only by being root-dependent, and root-dependent
 * siblings routinely write <em>different</em> derived values -- one key of
 * a rotation and its successor share a provenance exactly -- so provenance
 * could not tell the arms apart and the fold dropped evidence the failure
 * needed.  On hdfs-17899-bug3 it collapsed the nine per-key
 * {@code PBHelper.convert(BlockKeyProto)} deliveries to one per DataNode
 * and left every other block-key consumer family bound to nothing.  Every
 * occurrence the slice keeps is now replayed.</p>
 *
 * <p>Soundness is bounded by three rules the narrowing may never break: a
 * {@link #TARGET_REACH} occurrence, a {@link #ROOT_SITE} and an occurrence
 * whose write the fatal read itself consumes ({@link #FATAL_READ_WRITER})
 * are kept whatever else says, and a withheld carrier slice prunes nothing
 * at all -- a root the graph does not name cannot state what it reaches,
 * and neither can a fatal read the graph has no cell for.</p>
 *
 * <p>The kept count is published against an optional expected-shape hint
 * the experiment states ({@code replay_task_budget} in workflow.properties,
 * carried by {@code --replay-task-budget}).  Exceeding it is
 * {@link #BUDGET_EXCEEDED} telemetry and nothing else: the schedule is not
 * capped, truncated or silently accepted, because a campaign bigger than
 * its author expected is a fact to read, not a set of tasks to drop at
 * random.  No rule here names a workload, a class or a failure mechanism;
 * everything a single case needs beyond them belongs in that config.</p>
 */
final class ReplayTaskSlice {
    /** The artifact beside the task plan: one telemetry row, then one
     *  decision per selected occurrence. */
    static final String ARTIFACT = "replay_task_slice.jsonl";
    static final String TELEMETRY = "REPLAY_TASK_SLICE";
    static final String DECISION = "REPLAY_TASK_DECISION";
    /** Decision reason of an occurrence no root can reach. */
    static final String PRUNED = "REPLAY_TASK_PRUNED_NOT_ROOT_DEPENDENT";
    /** Decision reason of a replayed occurrence. */
    static final String KEPT = "REPLAY_TASK_KEPT";
    /** Decision reason when the slice narrowed nothing. */
    static final String WITHHELD = "REPLAY_TASK_SLICE_WITHHELD";
    /** Telemetry member: the kept count passed the expected-shape hint. */
    static final String BUDGET_EXCEEDED = "REPLAY_TASK_BUDGET_EXCEEDED";
    static final String TARGET_REACH = "TARGET_REACH";
    static final String ROOT_SITE = "ROOT_SITE";
    static final String CARRIER_WRITER = "CARRIER_WRITER";
    static final String ROOT_DEPENDENT_FLOW = "ROOT_DEPENDENT_FLOW";
    /** Keep reason of an occurrence the failing read consumes directly. */
    static final String FATAL_READ_WRITER = "FATAL_READ_WRITER";

    private final boolean applied;
    private final String sliceReason;
    /** Planned occurrence -> the region plan it names. */
    private final Map<String, RegionInstancePlan> plans;
    /** Planned occurrence -> why it is kept; empty means pruned. */
    private final Map<String, Set<String>> reasons;
    /** The expected kept count, or a non-positive number when unstated. */
    private final int budget;

    private ReplayTaskSlice(boolean applied, String sliceReason,
                            Map<String, RegionInstancePlan> plans,
                            Map<String, Set<String>> reasons, int budget) {
        this.applied = applied;
        this.sliceReason = sliceReason;
        this.plans = plans;
        this.reasons = reasons;
        this.budget = budget;
    }

    /**
     * Decides every plan row against the selection's carrier slice and the
     * backward slice of the fatal read.
     *
     * <p>The selection must already have seeded its slice; an unseeded one
     * is withheld and this slice then keeps everything, which is the sound
     * default rather than an error.</p>
     */
    static ReplayTaskSlice decide(
            List<RegionInstancePlan> regionPlans,
            ConcolicScheduler.SymbolicInputSelection selection,
            List<JsonObject> refinedGraph, int budget) {
        Map<String, RegionInstancePlan> plans = new LinkedHashMap<>();
        Map<String, Set<String>> reasons = new LinkedHashMap<>();
        Map<String, JsonObject> edges = new LinkedHashMap<>();
        // The cells the failing branch reads: the operands it decides on,
        // the throw it reaches, and the reads the target goal symbolizes.
        Set<String> fatalCells = new LinkedHashSet<>();
        for (RegionInstancePlan plan : regionPlans) {
            String occurrence = planned(plan.occurrenceId());
            plans.put(occurrence, plan);
            Set<String> why = reasons.computeIfAbsent(occurrence,
                    ignored -> new LinkedHashSet<>());
            if (array(plan.json(),
                    ConfiguredSourcePhaseContract.PLAN_FIELD).size() > 0) {
                why.add(ROOT_SITE);
            }
            for (Goal goal : plan.goals()) {
                boolean target = goal.kind().capturesTargetReach();
                if (target) {
                    why.add(TARGET_REACH);
                    fatalCells.addAll(fatalReadCells(goal));
                }
                for (JsonElement element : goal.symbolize()) {
                    if (!element.isJsonObject()) continue;
                    JsonObject action = element.getAsJsonObject();
                    if (target) {
                        fatalCells.addAll(
                                ConcolicScheduler.RootDependenceSlice
                                        .actionCells(action));
                    }
                    if (selection.rootAction(plan.regionId(), action)) {
                        why.add(ROOT_SITE);
                    }
                }
                for (JsonElement element : goal.edgeBindings()) {
                    if (!element.isJsonObject()) continue;
                    JsonObject edge = element.getAsJsonObject();
                    String id = optionalString(edge, "edgeId");
                    if (id.isEmpty()) {
                        id = ArtifactIO.sha256(CanonicalJson.render(edge));
                    }
                    edges.putIfAbsent(id, edge);
                }
            }
        }
        ConcolicScheduler.RootDependenceSlice slice =
                selection.carrierSlice().reachingFatalRead(
                        refinedGraph, fatalCells);
        if (!slice.usable()) {
            return new ReplayTaskSlice(false,
                    "NO_ROOT_CELL_IN_REFINED_GRAPH", plans, reasons,
                    budget);
        }
        Set<String> targets = new LinkedHashSet<>();
        for (Map.Entry<String, Set<String>> entry : reasons.entrySet()) {
            if (entry.getValue().contains(TARGET_REACH)) {
                targets.add(entry.getKey());
            }
        }
        Map<String, Set<String>> forward = new LinkedHashMap<>();
        Set<String> writers = new LinkedHashSet<>();
        for (JsonObject edge : edges.values()) {
            String from = planned(optionalString(edge, "fromOccurrenceId"));
            String to = planned(optionalString(edge, "toOccurrenceId"));
            if (!plans.containsKey(from) || !plans.containsKey(to)) continue;
            if (AutomaticRegionEdge.sharedLocationCandidate(edge)) {
                // A shared-location flow carries root dependence only where
                // the root's forward slice and the fatal read's backward
                // slice agree on the location; any other flow is a recorded
                // constant crossing between two occurrences.
                if (!slice.reachesLocation(
                        optionalString(edge, SharedFieldFlow.EDGE_LOCATION),
                        array(edge, "fieldPathDeclarations"))) {
                    continue;
                }
                writers.add(from);
            }
            // The fatal read consumes this write directly, so the arm it
            // takes is the arm the failure sees: never this slice's to drop.
            if (targets.contains(to) && !targets.contains(from)) {
                reasons.get(from).add(FATAL_READ_WRITER);
            }
            // A wire delivery or request-fault control carries whatever its
            // producer carries, so it is walked from a root-dependent
            // producer and never from anything else.
            forward.computeIfAbsent(from, ignored -> new LinkedHashSet<>())
                    .add(to);
        }
        // Only a root site seeds root dependence.  A writer of a cared
        // location earns the CARRIER_WRITER reason once a root reaches it,
        // and stays a recorded constant until then.
        Set<String> rootDependent = new LinkedHashSet<>();
        Deque<String> pending = new ArrayDeque<>();
        for (Map.Entry<String, Set<String>> entry : reasons.entrySet()) {
            if (entry.getValue().contains(ROOT_SITE)) {
                rootDependent.add(entry.getKey());
                pending.addLast(entry.getKey());
            }
        }
        while (!pending.isEmpty()) {
            for (String next : forward.getOrDefault(pending.removeFirst(),
                    Collections.<String>emptySet())) {
                if (rootDependent.add(next)) {
                    reasons.get(next).add(ROOT_DEPENDENT_FLOW);
                    pending.addLast(next);
                }
            }
        }
        for (String writer : writers) {
            if (rootDependent.contains(writer)) {
                reasons.get(writer).add(CARRIER_WRITER);
            }
        }
        // The other half of the bidirectional rule, at occurrence grain: a
        // root reaching an occurrence says the value can move, and reaching
        // the fatal read from it says the failing branch can see the move.
        // Only the two together buy an arm.  The reasons soundness names are
        // exempt: they are the failure's own occurrences, not inferences.
        Set<String> reachesFatalRead = backwardFrom(targets, forward);
        for (Map.Entry<String, Set<String>> entry : reasons.entrySet()) {
            Set<String> why = entry.getValue();
            if (why.isEmpty() || why.contains(TARGET_REACH)
                    || why.contains(ROOT_SITE)
                    || why.contains(FATAL_READ_WRITER)
                    || reachesFatalRead.contains(entry.getKey())) {
                continue;
            }
            why.clear();
        }
        return new ReplayTaskSlice(true, "ROOT_DEPENDENT_CARRIERS", plans,
                reasons, budget);
    }

    /**
     * Every occurrence a plan edge path leads from into {@code targets}.
     *
     * <p>The walk is over the same edges the forward closure used -- a
     * shared-location flow the slice cares about, a wire delivery, a
     * request-fault control -- so "can reach the failing read" is decided by
     * the same evidence as "a root can reach this".</p>
     */
    private static Set<String> backwardFrom(
            Set<String> targets, Map<String, Set<String>> forward) {
        Map<String, Set<String>> backward = new LinkedHashMap<>();
        for (Map.Entry<String, Set<String>> entry : forward.entrySet()) {
            for (String to : entry.getValue()) {
                backward.computeIfAbsent(to,
                        ignored -> new LinkedHashSet<>()).add(entry.getKey());
            }
        }
        Set<String> reaching = new LinkedHashSet<>(targets);
        Deque<String> pending = new ArrayDeque<>(targets);
        while (!pending.isEmpty()) {
            for (String next : backward.getOrDefault(pending.removeFirst(),
                    Collections.<String>emptySet())) {
                if (reaching.add(next)) pending.addLast(next);
            }
        }
        return reaching;
    }

    /** The cells the failing branch of one target goal decides on. */
    private static Set<String> fatalReadCells(Goal goal) {
        Set<String> cells = new LinkedHashSet<>();
        for (JsonElement element : goal.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!JsonFields.optionalBool(branch, "failureTarget", false)) {
                continue;
            }
            for (String member : new String[]{"operandCells",
                    "failureTargetCells", "guardCells"}) {
                for (JsonElement cell : array(branch, member)) {
                    if (!cell.isJsonPrimitive()) continue;
                    String value = cell.getAsString().trim();
                    if (!value.isEmpty()) cells.add(value);
                }
            }
        }
        return cells;
    }

    /** False when narrowing was withheld; then every occurrence is kept. */
    boolean applied() {
        return applied;
    }

    /** Whether this occurrence still replays. */
    boolean keeps(String occurrenceId) {
        if (!applied) return true;
        Set<String> why = reasons.get(planned(occurrenceId));
        // An occurrence the plan never named is not this slice's to drop.
        return why == null || !why.isEmpty();
    }

    /** The keep reasons of one occurrence, empty when it is pruned. */
    Set<String> reasons(String occurrenceId) {
        Set<String> why = reasons.get(planned(occurrenceId));
        return why == null ? Collections.<String>emptySet()
                : Collections.unmodifiableSet(why);
    }

    /**
     * The artifact rows: a telemetry summary, then one decision per
     * selected occurrence so "why did this task not replay" is answerable
     * from one file.
     */
    List<JsonObject> rows(Collection<String> selectedOccurrences) {
        List<JsonObject> decisions = new ArrayList<>();
        Map<String, Integer> keptByReason = new LinkedHashMap<>();
        int kept = 0;
        for (String occurrence : selectedOccurrences) {
            boolean keep = keeps(occurrence);
            if (keep) kept++;
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 2);
            row.addProperty("kind", DECISION);
            RegionInstancePlan plan = plans.get(planned(occurrence));
            row.addProperty("regionId",
                    plan == null ? "" : plan.regionId());
            row.addProperty("occurrenceId", occurrence);
            row.addProperty("targetMethod", plan == null ? ""
                    : optionalString(plan.json(), "targetMethod"));
            row.addProperty("decision", keep ? "KEEP" : "PRUNE");
            row.addProperty("reason", !applied ? WITHHELD
                    : keep ? KEPT : PRUNED);
            JsonArray why = new JsonArray();
            for (String reason : reasons(occurrence)) {
                why.add(reason);
                keptByReason.merge(reason, 1, Integer::sum);
            }
            row.add("keepReasons", why);
            decisions.add(row);
        }
        List<JsonObject> rows = new ArrayList<>();
        rows.add(telemetry(selectedOccurrences.size(), kept, keptByReason));
        rows.addAll(decisions);
        return rows;
    }

    /** The summary alone, for the schedule index. */
    JsonObject telemetry(Collection<String> selectedOccurrences) {
        Map<String, Integer> keptByReason = new LinkedHashMap<>();
        int kept = 0;
        for (String occurrence : selectedOccurrences) {
            if (keeps(occurrence)) kept++;
            for (String reason : reasons(occurrence)) {
                keptByReason.merge(reason, 1, Integer::sum);
            }
        }
        return telemetry(selectedOccurrences.size(), kept, keptByReason);
    }

    private JsonObject telemetry(int selected, int kept,
                                 Map<String, Integer> keptByReason) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 2);
        row.addProperty("kind", TELEMETRY);
        row.addProperty("replayTaskSliceApplied", applied);
        row.addProperty("replayTaskSliceReason", sliceReason);
        row.addProperty("selectedOccurrenceCount", selected);
        row.addProperty("keptOccurrenceCount", kept);
        row.addProperty("prunedOccurrenceCount", selected - kept);
        JsonObject byReason = new JsonObject();
        for (Map.Entry<String, Integer> entry : keptByReason.entrySet()) {
            byReason.addProperty(entry.getKey(), entry.getValue());
        }
        row.add("keptByReason", byReason);
        // The hint is an expectation to read against, never a cap: a kept
        // count over it is published and every one of those tasks still runs.
        row.addProperty("replayTaskBudget", budget);
        if (budget > 0) {
            row.addProperty("replayTaskBudgetStatus",
                    kept > budget ? BUDGET_EXCEEDED : "REPLAY_TASK_IN_BUDGET");
        }
        return row;
    }

    private static String planned(String occurrenceId) {
        return OccurrenceId.parse(occurrenceId).planned();
    }
}
