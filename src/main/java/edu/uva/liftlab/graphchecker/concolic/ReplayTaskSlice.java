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
 * workload; the HDFS-17960 fsimage loader alone is 93% of a replay and
 * feeds nothing the roots can move.  An occurrence earns its replay only
 * when it can carry a root's influence toward the target:</p>
 *
 * <ul>
 *   <li>{@link #TARGET_REACH} -- the occurrence decides the fatal branch;</li>
 *   <li>{@link #ROOT_SITE} -- it contains a root: a hook-owned or declared
 *   read, an {@code EXPLICIT_SYMBOLIC_FAULT} marker, or a configured
 *   source phase the hook published inside it;</li>
 *   <li>{@link #CARRIER_WRITER} -- it writes a shared location on the
 *   root-dependence slice ({@link ConcolicScheduler.RootDependenceSlice}),
 *   which already includes the case-controlled writers because the slice
 *   walks {@code GUARD} edges;</li>
 *   <li>{@link #ROOT_DEPENDENT_FLOW} -- a root site or carrier writer
 *   reaches it over the plan's own edges: a shared-location flow of a
 *   carrier, or a wire delivery / request-fault control whose producer is
 *   itself root-dependent.</li>
 * </ul>
 *
 * <p>Everything else replays only what the recording already observed:
 * every arm writes the recorded value, so the task is published as
 * {@link #PRUNED} rather than scheduled.  The slice is <b>withheld</b> --
 * nothing pruned -- whenever the carrier slice is, because a root the graph
 * does not name cannot state what it reaches.</p>
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
    static final String TARGET_REACH = "TARGET_REACH";
    static final String ROOT_SITE = "ROOT_SITE";
    static final String CARRIER_WRITER = "CARRIER_WRITER";
    static final String ROOT_DEPENDENT_FLOW = "ROOT_DEPENDENT_FLOW";

    private final boolean applied;
    private final String sliceReason;
    /** Planned occurrence -> the region plan it names. */
    private final Map<String, RegionInstancePlan> plans;
    /** Planned occurrence -> why it is kept; empty means pruned. */
    private final Map<String, Set<String>> reasons;

    private ReplayTaskSlice(boolean applied, String sliceReason,
                            Map<String, RegionInstancePlan> plans,
                            Map<String, Set<String>> reasons) {
        this.applied = applied;
        this.sliceReason = sliceReason;
        this.plans = plans;
        this.reasons = reasons;
    }

    /**
     * Decides every plan row against the selection's carrier slice.
     *
     * <p>The selection must already have seeded its slice; an unseeded one
     * is withheld and this slice then keeps everything, which is the
     * sound default rather than an error.</p>
     */
    static ReplayTaskSlice decide(
            List<RegionInstancePlan> regionPlans,
            ConcolicScheduler.SymbolicInputSelection selection) {
        ConcolicScheduler.RootDependenceSlice slice =
                selection.carrierSlice();
        Map<String, RegionInstancePlan> plans = new LinkedHashMap<>();
        Map<String, Set<String>> reasons = new LinkedHashMap<>();
        Map<String, JsonObject> edges = new LinkedHashMap<>();
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
                if (goal.kind().capturesTargetReach()) why.add(TARGET_REACH);
                for (JsonElement element : goal.symbolize()) {
                    if (element.isJsonObject() && selection.rootAction(
                            plan.regionId(), element.getAsJsonObject())) {
                        why.add(ROOT_SITE);
                        break;
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
        if (!slice.usable()) {
            return new ReplayTaskSlice(false,
                    "NO_ROOT_CELL_IN_REFINED_GRAPH", plans, reasons);
        }
        Map<String, Set<String>> forward = new LinkedHashMap<>();
        for (JsonObject edge : edges.values()) {
            String from = planned(optionalString(edge, "fromOccurrenceId"));
            String to = planned(optionalString(edge, "toOccurrenceId"));
            if (!plans.containsKey(from) || !plans.containsKey(to)) continue;
            if (AutomaticRegionEdge.sharedLocationCandidate(edge)) {
                // A shared-location flow carries root dependence only when
                // the location itself is on the slice; any other flow is a
                // recorded constant crossing between two occurrences.
                if (!slice.reachesLocation(
                        optionalString(edge, SharedFieldFlow.EDGE_LOCATION),
                        array(edge, "fieldPathDeclarations"))) {
                    continue;
                }
                reasons.get(from).add(CARRIER_WRITER);
            }
            // A wire delivery or request-fault control carries whatever its
            // producer carries, so it is walked from a root-dependent
            // producer and never from anything else.
            forward.computeIfAbsent(from, ignored -> new LinkedHashSet<>())
                    .add(to);
        }
        Deque<String> pending = new ArrayDeque<>();
        Set<String> reached = new LinkedHashSet<>();
        for (Map.Entry<String, Set<String>> entry : reasons.entrySet()) {
            if (entry.getValue().contains(ROOT_SITE)
                    || entry.getValue().contains(CARRIER_WRITER)) {
                reached.add(entry.getKey());
                pending.addLast(entry.getKey());
            }
        }
        while (!pending.isEmpty()) {
            for (String next : forward.getOrDefault(pending.removeFirst(),
                    Collections.<String>emptySet())) {
                if (reached.add(next)) {
                    reasons.get(next).add(ROOT_DEPENDENT_FLOW);
                    pending.addLast(next);
                }
            }
        }
        return new ReplayTaskSlice(true, "ROOT_DEPENDENT_CARRIERS", plans,
                reasons);
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
            row.addProperty("schemaVersion", 1);
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
        row.addProperty("schemaVersion", 1);
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
        return row;
    }

    private static String planned(String occurrenceId) {
        return OccurrenceId.parse(occurrenceId).planned();
    }
}
