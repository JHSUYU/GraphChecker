package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Compares one raw VM result with the frozen task that planned it and records
 * the normalized {@code topology_delta.jsonl} row.
 *
 * <p>README "Delta ownership is also singular" gives this comparison to
 * {@link ConcolicSummaryImporter}, while it imports the row and not as a
 * second pass over a second graph store.</p> */
public final class TopologyDelta {

    public static final int SCHEMA_VERSION = 1;
    public static final String ROW_KIND = "TOPOLOGY_DELTA";

    public static final String NEW_LOCAL_CASE = "NEW_LOCAL_CASE";
    public static final String NEW_EFFECT = "NEW_EFFECT";
    public static final String NEW_OCCURRENCE = "NEW_OCCURRENCE";
    public static final String NEW_CAUSAL_BINDING =
            "NEW_CAUSAL_BINDING";
    public static final String TOPOLOGY_DIVERGENCE = "TOPOLOGY_DIVERGENCE";
    public static final String COVERAGE_GAP = "COVERAGE_GAP";

    /** Default artifact name beside the imported summaries. */
    public static final String FILE_NAME = "topology_delta.jsonl";

    /** A planned task no raw result of this iteration ever named. */
    public static final String PLANNED_TASK_PRODUCED_NO_RESULT =
            "PLANNED_TASK_PRODUCED_NO_RESULT";
    private static final String[] IDENTITY_FIELDS = {
            "sourceKey", "occurrenceId", "relationKey", "regionId"
    };

    /** The schema member sets a new member of which is a topology change, and
     * the divergence field each is reported under. */
    private static final String[][] SCHEMA_SETS = {
            {"inputSymbols", "inputSchema"},
            // README Step 1: topology is judged at the RPC exchange event.
            // A (sender occurrence, receiver occurrence, port) triple the
            // frozen catalog never declared is the change that re-plans.
            {"exchangeEvents", "exchangeSchema"},
    };

    /** README "Results merge in the stable order ...; completion order is
     * never semantic." {@code deltaKind} only breaks the final tie so that
     * two rows of one case still have one order. */
    private static final Comparator<JsonObject> ROW_ORDER =
            new Comparator<JsonObject>() {
                @Override
                public int compare(JsonObject left, JsonObject right) {
                    for (String field : new String[]{"iterationId", "taskId",
                            "sourceKey", "occurrenceId"}) {
                        int order = string(left, field)
                                .compareTo(string(right, field));
                        if (order != 0) return order;
                    }
                    int order = string(left, "caseDigest")
                            .compareTo(string(right, "caseDigest"));
                    if (order != 0) return order;
                    return string(left, "deltaKind")
                            .compareTo(string(right, "deltaKind"));
                }
            };

    /** What one import attempt observed, carried back to the classifier. */
    public static final class Observation {
        /** The admitted summary, or {@code null} when the row was refused. */
        JsonObject summary;
        /** The named gap of a refused or incomplete row; never silent. */
        String gap = "";
        /** This execution attested an exact typed communication binding. */
        boolean binding;
        /** This execution recorded a shared-state version or transition. */
        boolean effect;
        /** The frozen plan does not contain this result's identity at all. */
        boolean unplanned;

        static Observation refused(String gap) {
            Observation result = new Observation();
            result.gap = gap;
            return result;
        }

        static Observation unplanned(String gap) {
            Observation result = refused(gap);
            result.unplanned = true;
            return result;
        }
    }

    private final String iterationId;
    private final List<JsonObject> rows = new ArrayList<>();
    private final Set<String> casedOccurrences = new LinkedHashSet<>();
    private final Set<String> observedLocalCases = new LinkedHashSet<>();
    private final Set<String> namedTasks = new LinkedHashSet<>();

    TopologyDelta(String iterationId) {
        if (iterationId == null || iterationId.trim().isEmpty()) {
            throw new IllegalArgumentException(
                    "topology delta iteration id must be non-blank");
        }
        this.iterationId = iterationId.trim();
    }

    /**
     * Classifies one decoded result against its frozen task.
     *
     * @param task the frozen task, or {@code null} when the frozen plan does
     *             not contain this result at all
     * @param row  the importer's one decode of the raw result
     */
    void classify(ExecutionTask task, ConcolicSummaryImporter.ResultRow row,
                  Observation observation) {
        JsonObject plannedIdentity = plannedIdentity(task);
        List<String> unobservedIdentity = new ArrayList<>();
        JsonObject observedIdentity = observedIdentity(plannedIdentity,
                unobservedIdentity);
        JsonObject plannedSchema = plannedSchema(task);
        List<String> unobservedSchema = new ArrayList<>();
        JsonObject observedSchema = observedSchema(task, row, observation,
                plannedSchema, unobservedSchema);
        JsonArray divergences = task == null || observation.unplanned
                ? notInFrozenPlan(row, plannedIdentity, observation.gap)
                : divergences(plannedIdentity, observedIdentity,
                plannedSchema, observedSchema);

        JsonObject base = new JsonObject();
        base.addProperty("schemaVersion", SCHEMA_VERSION);
        base.addProperty("kind", ROW_KIND);
        base.addProperty("iterationId", iterationId);
        base.addProperty("taskId", task == null
                ? row.taskId : task.taskId());
        for (String field : IDENTITY_FIELDS) {
            base.add(field, plannedIdentity.get(field));
        }
        // Imported summaries receive this verified identity exactly once in
        // ConcolicSummaryImporter.  Recomputing it here used to re-parse and
        // compare every branch predicate three more times per row.
        String localCaseId = observation.summary == null ? ""
                : string(observation.summary, LocalCaseIdentity.FIELD);
        if (observation.summary != null && localCaseId.isEmpty()) {
            throw new IllegalStateException(
                    "imported summary has no localCaseId");
        }
        base.addProperty("summaryId", observation.summary == null ? ""
                : string(observation.summary, "summaryId"));
        base.addProperty(LocalCaseIdentity.FIELD, localCaseId);
        base.addProperty("caseDigest", caseDigest(observation, localCaseId,
                observedIdentity, observedSchema));
        if (!unobservedIdentity.isEmpty()) {
            base.add("unobservedIdentityFields", strings(unobservedIdentity));
        }
        if (!unobservedSchema.isEmpty()) {
            base.add("unobservedSchemaFields", strings(unobservedSchema));
        }
        if (task != null) namedTasks.add(task.taskId());

        if (divergences.size() > 0) {
            // README Step 1: "a different cut, output schema, source,
            // occurrence, or loop slot may not" add a case.
            emit(base, TOPOLOGY_DIVERGENCE, "").add("divergences", divergences);
        } else if (observation.summary != null) {
            String occurrence = occurrenceKey(plannedIdentity);
            boolean firstOccurrence = casedOccurrences.add(occurrence);
            boolean firstLocalCase = observedLocalCases.add(occurrence + "\n"
                    + localCaseId);
            if (firstOccurrence) {
                emit(base, NEW_OCCURRENCE, "");
            } else if (firstLocalCase) {
                emit(base, NEW_LOCAL_CASE, "");
            }
            if (observation.binding) emit(base, NEW_CAUSAL_BINDING, "");
            if (observation.effect) emit(base, NEW_EFFECT, "");
        }
        // Import admission failures already have one authoritative diagnostic
        // row.
        if (PLANNED_TASK_PRODUCED_NO_RESULT.equals(observation.gap)) {
            emit(base, COVERAGE_GAP, observation.gap);
        }
    }

    /** Names every frozen task this iteration produced no result row for. */
    void classifyUnobservedTasks(Collection<ExecutionTask> planned) {
        for (ExecutionTask task : planned) {
            if (namedTasks.contains(task.taskId())) continue;
            classify(task, new ConcolicSummaryImporter.ResultRow(
                            new JsonObject(), -1),
                    Observation.refused(PLANNED_TASK_PRODUCED_NO_RESULT));
        }
    }

    /** The rows in the README's stable merge order. */
    List<JsonObject> rows() {
        List<JsonObject> ordered = new ArrayList<>(rows);
        Collections.sort(ordered, ROW_ORDER);
        return ordered;
    }

    private JsonObject emit(JsonObject base, String deltaKind, String gap) {
        JsonObject row = base.deepCopy();
        row.addProperty("deltaKind", deltaKind);
        row.addProperty("gap", gap);
        rows.add(row);
        return row;
    }

    private static String caseDigest(Observation observation,
                                     String localCaseId,
                                     JsonObject observedIdentity,
                                     JsonObject observedSchema) {
        if (observation.summary != null) {
            return CanonicalJson.sha256(localCaseId);
        }
        JsonArray evidence = new JsonArray();
        evidence.add(observedIdentity);
        evidence.add(observedSchema);
        evidence.add(observation.gap);
        return CanonicalJson.sha256(evidence);
    }

    private static String occurrenceKey(JsonObject identity) {
        return string(identity, "sourceKey") + "\n"
                + string(identity, "occurrenceId");
    }


    private static JsonObject plannedIdentity(ExecutionTask task) {
        JsonObject result = new JsonObject();
        result.addProperty("sourceKey", task == null ? "" : task.sourceKey());
        result.addProperty("occurrenceId",
                task == null ? "" : task.occurrenceId());
        result.addProperty("relationKey",
                task == null ? "" : task.relationKey());
        result.addProperty("regionId", task == null ? "" : task.regionId());
        return result;
    }

    /** The identity this execution actually stated. The VM echoes the region
     * occurrence through its own frame binding; it never restates the source,
     * relation or region, so those carry the planned value and are named as
     * unobserved rather than being silently reported as agreement. */
    private static JsonObject observedIdentity(JsonObject planned,
                                               List<String> unobserved) {
        JsonObject result = planned.deepCopy();
        unobserved.add("occurrenceId");
        unobserved.add("sourceKey");
        unobserved.add("relationKey");
        unobserved.add("regionId");
        return result;
    }


    private static JsonObject plannedSchema(ExecutionTask task) {
        JsonObject result = new JsonObject();
        if (task == null) {
            result.add("inputSymbols", new JsonArray());
            result.add("branchSites", new JsonArray());
            result.add("configuredSourcePhases", new JsonArray());
            result.add("exchangeEvents", new JsonArray());
            result.addProperty("loopBound", "");
            return result;
        }
        SortedSet<String> symbols = new TreeSet<>();
        for (JsonElement element : task.inputActions().all()) {
            if (!element.isJsonObject()) continue;
            String symbol = JsonFields.firstNonBlank(
                    string(element.getAsJsonObject(), "symbol"),
                    string(element.getAsJsonObject(), "portId"));
            if (!symbol.isEmpty()) symbols.add(symbol);
        }
        SortedSet<String> sites = new TreeSet<>();
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            String site = string(element.getAsJsonObject(), "siteId");
            if (!site.isEmpty()) sites.add(site);
        }
        result.add("inputSymbols", strings(symbols));
        result.add("branchSites", strings(sites));
        // The catalog of mint SITES is the frozen schema: an execution of a
        // site the plan never declared is the topology change, and which
        // site a value came from is decided at replay, not here.
        SortedSet<String> mintSites = new TreeSet<>();
        for (ConfiguredSourcePhaseContract.Occurrence phase
                : task.configuredSourcePhases()) {
            mintSites.add(phase.phaseId());
        }
        result.add("configuredSourcePhases", strings(mintSites));
        // One RPC exchange is one (sender occurrence, receiver occurrence,
        // port) triple.  Both port names of a declared edge are admitted so a
        // request/response naming difference is not read as a new exchange.
        SortedSet<String> exchanges = new TreeSet<>();
        for (JsonElement element : task.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            String from = string(edge, "fromOccurrenceId");
            String to = string(edge, "toOccurrenceId");
            for (String port : new String[]{string(edge, "toInputPort"),
                    string(edge, "fromOutputPort")}) {
                if (from.isEmpty() || to.isEmpty() || port.isEmpty()) continue;
                exchanges.add(exchangeKey(from, to, port));
            }
        }
        result.add("exchangeEvents", strings(exchanges));
        result.addProperty("loopBound", task.loopBound().identity());
        return result;
    }

    private static JsonObject observedSchema(
            ExecutionTask task, ConcolicSummaryImporter.ResultRow row,
            Observation observation, JsonObject planned,
            List<String> unobserved) {
        JsonObject result = planned.deepCopy();

        // An input the run left unresolved is not part of the schema this
        // execution actually carried.
        SortedSet<String> resolved = new TreeSet<>(
                textSet(array(planned, "inputSymbols")));
        String unresolved = row.unresolvedInputs.toString();
        for (String symbol : new ArrayList<>(resolved)) {
            if (unresolved.contains(symbol)) resolved.remove(symbol);
        }
        recordObservedSet(result, "inputSymbols", planned, resolved,
                unobserved);

        if (row.statesBranchEvidence) {
            result.add("branchSites", strings(row.observedBranchSites));
        } else {
            unobserved.add("branchSites");
        }

        // A VM value handoff names the sender occurrence and the port; the
        // receiver is this task's own occurrence.
        if (row.vmHandoffs != null) {
            SortedSet<String> observedExchanges = new TreeSet<>();
            for (JsonElement element : row.vmHandoffs) {
                if (!element.isJsonObject()) continue;
                JsonObject handoff = element.getAsJsonObject();
                String producer = string(handoff,
                        VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);
                String port = string(handoff, "portId");
                if (producer.isEmpty() || port.isEmpty() || task == null) {
                    continue;
                }
                observedExchanges.add(exchangeKey(producer,
                        task.occurrenceId(), port));
            }
            recordObservedSet(result, "exchangeEvents", planned,
                    observedExchanges, unobserved);
        } else if (array(planned, "exchangeEvents").size() > 0) {
            unobserved.add("exchangeEvents");
        }

        if (row.sourcePhaseObservations != null) {
            result.add("configuredSourcePhases",
                    strings(row.observedSourcePhases()));
        } else if (array(planned, "configuredSourcePhases").size() > 0) {
            unobserved.add("configuredSourcePhases");
        }

        String loopSite = boundedLoopSite(row);
        if (loopSite.isEmpty() || task == null) {
            unobserved.add("loopBound");
        } else {
            int observedMax = integer(row.pathCut,
                    "maxBackedgeTraversals", -1);
            if (observedMax != task.loopBound()
                    .maxBackedgeTraversals(loopSite)) {
                result.addProperty("loopBound",
                        loopSite + "=" + observedMax);
            }
        }

        return result;
    }

    /** Records one observed member set of the schema against its planned set.
     *
     * <p>README {@code GRAPH-1} starts the next immutable iteration on a new
     * "slot/schema", so only a member the frozen plan never declared is an
     * observed contradiction.</p> */
    private static void recordObservedSet(JsonObject result, String field,
                                          JsonObject planned,
                                          SortedSet<String> observed,
                                          List<String> unobserved) {
        Set<String> declared = textSet(array(planned, field));
        if (declared.containsAll(observed)) {
            // Nothing this execution stated is outside the frozen schema, so
            // only coverage can differ and the planned value stands.
            if (observed.size() < declared.size()) unobserved.add(field);
            return;
        }
        result.add(field, strings(observed));
    }

    /** The loop the VM cut this path at under the frozen backedge bound. */
    private static String boundedLoopSite(
            ConcolicSummaryImporter.ResultRow row) {
        return "LOOP_BOUND".equals(string(row.pathCut, "kind"))
                ? string(row.pathCut, "backedgeId") : "";
    }


    /** A result the frozen plan or its runtime regions do not contain. */
    private static JsonArray notInFrozenPlan(
            ConcolicSummaryImporter.ResultRow row,
            JsonObject plannedIdentity, String reason) {
        JsonArray result = new JsonArray();
        result.add(divergence(reason.isEmpty() ? "taskId" : reason,
                string(plannedIdentity, "regionId"), row.taskId));
        return result;
    }

    private JsonArray divergences(
            JsonObject plannedIdentity, JsonObject observedIdentity,
            JsonObject plannedSchema, JsonObject observedSchema) {
        JsonArray result = new JsonArray();
        for (String field : IDENTITY_FIELDS) {
            String planned = string(plannedIdentity, field);
            String observed = string(observedIdentity, field);
            if (!planned.equals(observed)) {
                result.add(divergence(field, planned, observed));
            }
        }
        // README GRAPH-1: a new "slot/schema" starts the next immutable
        // iteration.
        for (String[] set : SCHEMA_SETS) {
            Set<String> declared = textSet(array(plannedSchema, set[0]));
            for (String observed : textSet(array(observedSchema, set[0]))) {
                if (declared.contains(observed)) continue;
                result.add(divergence(set[1], "", observed));
            }
        }
        // Extra branch decisions are new guarded local cases.
        String plannedLoop = string(plannedSchema, "loopBound");
        String observedLoop = string(observedSchema, "loopBound");
        if (!plannedLoop.equals(observedLoop)) {
            result.add(divergence("loopBound", plannedLoop, observedLoop));
        }
        JsonArray plannedPhases = array(plannedSchema,
                "configuredSourcePhases");
        Set<String> declaredPhases = textSet(plannedPhases);
        for (String observed : textSet(array(observedSchema,
                "configuredSourcePhases"))) {
            if (declaredPhases.contains(observed)) continue;
            result.add(divergence("configuredSourcePhases",
                    CanonicalJson.render(plannedPhases), observed));
        }
        return result;
    }

    /** One RPC exchange event, as the frozen plan and the raw result both
     * name it: who sent, who received, and over which declared port.
     *
     * <p>OCC-1: both endpoints are named at their planned address.  The
     * frozen plan is a region plan and can only ever declare the address the
     * campaign scheduled; a VM handoff names the activation that ran, which
     * is that same address plus an ordinal minted at replay.  The exchange
     * README Step 1 judges topology at is the (sender occurrence, receiver
     * occurrence, port) triple, and the activation ordinal is no member of
     * it, so it is not part of the comparison
     * ({@link PathObservation#plannedOccurrenceOf} is the one rule for that,
     * shared with the target reach query and the scheduler).</p>
     *
     * <p>Comparing the raw activation string instead makes the comparison
     * unfalsifiable rather than strict: no plan can declare an ordinal that
     * does not exist until the run happens, so every declared exchange is
     * reported as a new member on every iteration and the campaign never
     * reaches a fixed point.  Nothing is suppressed by normalizing -- a
     * sender occurrence, a receiver occurrence or a port the plan did not
     * declare still differs after it, and is still reported.</p> */
    private static String exchangeKey(String fromOccurrenceId,
                                      String toOccurrenceId, String portId) {
        return PathObservation.plannedOccurrenceOf(fromOccurrenceId) + "\n"
                + PathObservation.plannedOccurrenceOf(toOccurrenceId) + "\n"
                + portId;
    }

    private static JsonObject divergence(String field, String planned,
                                         String observed) {
        JsonObject result = new JsonObject();
        result.addProperty("field", field);
        result.addProperty("planned", planned);
        result.addProperty("observed", observed);
        return result;
    }


    private static Set<String> textSet(JsonArray values) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : values) {
            if (element.isJsonPrimitive()) result.add(element.getAsString());
        }
        return result;
    }

    private static JsonArray strings(Collection<String> values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

}
