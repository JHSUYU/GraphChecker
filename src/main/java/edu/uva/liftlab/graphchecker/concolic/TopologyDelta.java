package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Compares one raw VM result with the frozen task that planned it and records
 * the normalized {@code topology_delta.jsonl} row.
 *
 * <p>README "Delta ownership is also singular" gives this comparison to
 * {@link ConcolicSummaryImporter}, while it imports the row and not as a
 * second pass over a second graph store.  This class is only the vocabulary,
 * the comparison and the deterministic order; it holds no evidence of its own
 * and never mutates or deletes a historical row.  "Failure to observe an old
 * relation" is therefore a {@link #COVERAGE_GAP} and never a removal.</p>
 *
 * <p>Both digest pairs are written so that equality is meaningful: a schema or
 * identity component the raw result does not state falls back to the planned
 * value and is named in {@code unobservedIdentityFields} /
 * {@code unobservedSchemaFields}, so a differing digest always means an
 * observed contradiction rather than a missing observation.  The classification
 * itself is decided by the explicit {@code divergences} list, never by digest
 * equality alone.</p>
 */
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
    /** A branch site the frozen plan declared and no execution decided. */
    public static final String PLANNED_BRANCH_EVENT_NOT_OBSERVED =
            "PLANNED_BRANCH_EVENT_NOT_OBSERVED";

    private static final String[] IDENTITY_FIELDS = {
            "sourceKey", "occurrenceId", "relationKey", "regionId"
    };

    /**
     * README "Results merge in the stable order ...; completion order is never
     * semantic."  {@code deltaKind} only breaks the final tie so that two rows
     * of one case still have one order.
     */
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
    private final String planDigest;
    private final List<JsonObject> rows = new ArrayList<>();
    private final Set<String> casedOccurrences = new LinkedHashSet<>();
    private final Set<String> namedTasks = new LinkedHashSet<>();

    TopologyDelta(String iterationId, String planDigest) {
        this.iterationId = iterationId == null ? "" : iterationId.trim();
        this.planDigest = planDigest == null ? "" : planDigest;
    }

    /** The frozen plan digest, in taskId order and independent of file order. */
    static String planDigest(Collection<ExecutionTask> tasks) {
        SortedMap<String, JsonObject> ordered = new TreeMap<>();
        for (ExecutionTask task : tasks) {
            ordered.put(task.taskId(), task.json());
        }
        JsonArray canonical = new JsonArray();
        for (JsonObject row : ordered.values()) canonical.add(row);
        return CanonicalJson.sha256(canonical);
    }

    String iterationId() { return iterationId; }

    String planDigest() { return planDigest; }

    /**
     * Classifies one raw result against its frozen task.
     *
     * @param task the frozen task, or {@code null} when the frozen plan does
     *             not contain this result at all
     * @param line zero-based result line, or negative when there is no result
     */
    void classify(ExecutionTask task, JsonObject raw, int line,
                  Observation observation) {
        JsonObject plannedIdentity = plannedIdentity(task);
        List<String> unobservedIdentity = new ArrayList<>();
        JsonObject observedIdentity = observedIdentity(raw, plannedIdentity,
                unobservedIdentity);
        JsonObject plannedSchema = plannedSchema(task);
        List<String> unobservedSchema = new ArrayList<>();
        JsonObject observedSchema = observedSchema(task, raw, observation,
                plannedSchema, unobservedSchema);
        JsonArray divergences = task == null || observation.unplanned
                ? notInFrozenPlan(raw, plannedIdentity, observation.gap)
                : divergences(raw, plannedIdentity, observedIdentity,
                plannedSchema, observedSchema);

        JsonObject base = new JsonObject();
        base.addProperty("schemaVersion", SCHEMA_VERSION);
        base.addProperty("kind", ROW_KIND);
        base.addProperty("iterationId", iterationId);
        base.addProperty("planDigest", planDigest);
        base.addProperty("taskId", task == null
                ? string(raw, "taskId") : task.taskId());
        for (String field : IDENTITY_FIELDS) {
            base.add(field, plannedIdentity.get(field));
        }
        base.addProperty("plannedIdentityDigest",
                CanonicalJson.sha256(plannedIdentity));
        base.addProperty("observedIdentityDigest",
                CanonicalJson.sha256(observedIdentity));
        base.addProperty("plannedSchemaDigest",
                CanonicalJson.sha256(plannedSchema));
        base.addProperty("observedSchemaDigest",
                CanonicalJson.sha256(observedSchema));
        base.addProperty("resultLine", line + 1);
        base.addProperty("summaryId", observation.summary == null ? ""
                : string(observation.summary, "summaryId"));
        base.addProperty("caseDigest", caseDigest(observation, observedIdentity,
                observedSchema));
        if (!unobservedIdentity.isEmpty()) {
            base.add("unobservedIdentityFields", strings(unobservedIdentity));
        }
        if (!unobservedSchema.isEmpty()) {
            base.add("unobservedSchemaFields", strings(unobservedSchema));
        }
        if (task != null) namedTasks.add(task.taskId());

        if (divergences.size() > 0) {
            // README Step 1: "a different cut, output schema, source,
            // occurrence, or loop slot may not" add a case.  The relation
            // belongs to the next iteration's plan, so no case is published
            // here and no obligation may be built across it.
            emit(base, TOPOLOGY_DIVERGENCE, "").add("divergences", divergences);
        } else if (observation.summary != null) {
            emit(base, casedOccurrences.add(occurrenceKey(plannedIdentity))
                    ? NEW_OCCURRENCE : NEW_LOCAL_CASE, "");
            if (observation.binding) emit(base, NEW_CAUSAL_BINDING, "");
            if (observation.effect) emit(base, NEW_EFFECT, "");
        }
        if (!observation.gap.isEmpty()) {
            emit(base, COVERAGE_GAP, observation.gap);
        }
        String unseen = line < 0 ? ""
                : unobservedPlannedEvents(raw, plannedSchema, observedSchema);
        if (!unseen.isEmpty()) emit(base, COVERAGE_GAP, unseen);
    }

    /** Names every frozen task this iteration produced no result row for. */
    void classifyUnobservedTasks(Collection<ExecutionTask> planned) {
        for (ExecutionTask task : planned) {
            if (namedTasks.contains(task.taskId())) continue;
            classify(task, new JsonObject(), -1,
                    Observation.refused(PLANNED_TASK_PRODUCED_NO_RESULT));
        }
    }

    /** The rows in the README's stable merge order. */
    List<JsonObject> rows() {
        List<JsonObject> ordered = new ArrayList<>(rows);
        Collections.sort(ordered, ROW_ORDER);
        return ordered;
    }

    /** Row counts by delta kind, for the iteration manifest. */
    SortedMap<String, Integer> countsByKind() {
        SortedMap<String, Integer> result = new TreeMap<>();
        for (String kind : new String[]{NEW_LOCAL_CASE, NEW_EFFECT,
                NEW_OCCURRENCE, NEW_CAUSAL_BINDING, TOPOLOGY_DIVERGENCE,
                COVERAGE_GAP}) {
            result.put(kind, Integer.valueOf(0));
        }
        for (JsonObject row : rows) {
            String kind = string(row, "deltaKind");
            result.put(kind, Integer.valueOf(result.get(kind).intValue() + 1));
        }
        return result;
    }

    private JsonObject emit(JsonObject base, String deltaKind, String gap) {
        JsonObject row = base.deepCopy();
        row.addProperty("deltaKind", deltaKind);
        row.addProperty("gap", gap);
        rows.add(row);
        return row;
    }

    private static String caseDigest(Observation observation,
                                     JsonObject observedIdentity,
                                     JsonObject observedSchema) {
        if (observation.summary != null) {
            return CanonicalJson.sha256(observation.summary);
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

    // ---------------------------------------------------------------- identity

    private static JsonObject plannedIdentity(ExecutionTask task) {
        JsonObject result = new JsonObject();
        JsonObject encoded = task == null ? new JsonObject() : task.json();
        result.addProperty("sourceKey", task == null ? "" : task.sourceKey());
        result.addProperty("occurrenceId",
                task == null ? "" : task.occurrenceId());
        result.addProperty("relationKey",
                task == null ? "" : task.relationKey());
        result.addProperty("regionId", task == null ? "" : task.regionId());
        return result;
    }

    /**
     * The identity this execution actually stated.  The VM echoes the region
     * occurrence through its own frame binding; it never restates the source,
     * relation or region, so those carry the planned value and are named as
     * unobserved rather than being silently reported as agreement.
     */
    private static JsonObject observedIdentity(JsonObject raw,
                                               JsonObject planned,
                                               List<String> unobserved) {
        JsonObject result = planned.deepCopy();
        JsonObject binding = object(raw, "regionFrameBinding");
        String occurrence = string(binding, "occurrenceId");
        if (occurrence.isEmpty()) {
            unobserved.add("occurrenceId");
        } else {
            result.addProperty("occurrenceId", occurrence);
        }
        unobserved.add("sourceKey");
        unobserved.add("relationKey");
        unobserved.add("regionId");
        return result;
    }

    // ------------------------------------------------------------------ schema

    private static JsonObject plannedSchema(ExecutionTask task) {
        JsonObject result = new JsonObject();
        if (task == null) {
            result.add("inputSymbols", new JsonArray());
            result.add("outputPorts", new JsonArray());
            result.add("captureBindings", new JsonArray());
            result.add("branchSites", new JsonArray());
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
        SortedSet<String> captures = new TreeSet<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            captures.add(spec.captureBindingId());
        }
        SortedSet<String> sites = new TreeSet<>();
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            String site = string(element.getAsJsonObject(), "siteId");
            if (!site.isEmpty()) sites.add(site);
        }
        result.add("inputSymbols", strings(symbols));
        result.add("outputPorts", strings(task.outputClosure() == null
                ? Collections.<String>emptySet()
                : task.outputClosure().outputPorts()));
        result.add("captureBindings", strings(captures));
        result.add("branchSites", strings(sites));
        result.addProperty("loopBound", task.loopBound().identity());
        return result;
    }

    private static JsonObject observedSchema(ExecutionTask task,
                                             JsonObject raw,
                                             Observation observation,
                                             JsonObject planned,
                                             List<String> unobserved) {
        JsonObject result = planned.deepCopy();

        // An input the run left unresolved is not part of the schema this
        // execution actually carried.
        SortedSet<String> resolved = new TreeSet<>(
                textSet(array(planned, "inputSymbols")));
        String unresolved = array(raw, "unresolvedInputs").toString();
        for (String symbol : new ArrayList<>(resolved)) {
            if (unresolved.contains(symbol)) resolved.remove(symbol);
        }
        result.add("inputSymbols", strings(resolved));

        if (observation.summary == null) {
            unobserved.add("outputPorts");
        } else {
            SortedSet<String> ports = new TreeSet<>(object(observation.summary,
                    "outputExpressions").keySet());
            result.add("outputPorts", strings(ports));
        }

        JsonArray captures = array(raw, "outputCaptures");
        if (captures.size() == 0 && array(planned, "captureBindings")
                .size() > 0 && observation.summary == null) {
            unobserved.add("captureBindings");
        } else {
            SortedSet<String> observedCaptures = new TreeSet<>();
            for (JsonElement element : captures) {
                if (!element.isJsonObject()) continue;
                String id = string(element.getAsJsonObject(),
                        "captureBindingId");
                if (!id.isEmpty()) observedCaptures.add(id);
            }
            result.add("captureBindings", strings(observedCaptures));
        }

        if (raw.has("branchMappings") || raw.has("concreteBranchWitnesses")) {
            result.add("branchSites", strings(observedBranchSites(raw)));
        } else {
            unobserved.add("branchSites");
        }

        String loopSite = boundedLoopSite(raw);
        if (loopSite.isEmpty() || task == null) {
            unobserved.add("loopBound");
        } else {
            int observedMax = integer(object(raw, "pathCut"),
                    "maxBackedgeTraversals", -1);
            if (observedMax != task.loopBound()
                    .maxBackedgeTraversals(loopSite)) {
                result.addProperty("loopBound",
                        loopSite + "=" + observedMax);
            }
        }

        return result;
    }

    private static SortedSet<String> observedBranchSites(JsonObject raw) {
        SortedSet<String> result = new TreeSet<>();
        for (String field : new String[]{"branchMappings",
                "concreteBranchWitnesses"}) {
            for (JsonElement element : array(raw, field)) {
                if (!element.isJsonObject()) continue;
                String site = string(element.getAsJsonObject(), "siteId");
                if (!site.isEmpty()) result.add(site);
            }
        }
        return result;
    }

    /** The loop the VM cut this path at under the frozen backedge bound. */
    private static String boundedLoopSite(JsonObject raw) {
        JsonObject cut = object(raw, "pathCut");
        return "LOOP_BOUND".equals(string(cut, "kind"))
                ? string(cut, "backedgeId") : "";
    }

    // ------------------------------------------------------------- comparison

    /** A result the frozen plan or its runtime regions do not contain. */
    private static JsonArray notInFrozenPlan(JsonObject raw,
                                             JsonObject plannedIdentity,
                                             String reason) {
        JsonArray result = new JsonArray();
        result.add(divergence(reason.isEmpty() ? "taskId" : reason,
                string(plannedIdentity, "regionId"), string(raw, "taskId")));
        return result;
    }

    private static JsonArray divergences(
            JsonObject raw, JsonObject plannedIdentity,
            JsonObject observedIdentity, JsonObject plannedSchema,
            JsonObject observedSchema) {
        JsonArray result = new JsonArray();
        for (String field : IDENTITY_FIELDS) {
            String planned = text(plannedIdentity, field);
            String observed = text(observedIdentity, field);
            if (!planned.equals(observed)) {
                result.add(divergence(field, planned, observed));
            }
        }
        // A capture the frozen closure never requested is a new output schema.
        Set<String> plannedCaptures =
                textSet(array(plannedSchema, "captureBindings"));
        for (String observed : textSet(array(observedSchema,
                "captureBindings"))) {
            if (!plannedCaptures.contains(observed)) {
                result.add(divergence("outputSchema", "", observed));
            }
        }
        // Extra branch decisions are new guarded local cases. They stay in
        // the admitted summary for branch exploration and supergraph
        // refinement; they do not change the task's stable identity, output
        // schema, or declared loop bound and therefore are not topology
        // divergences.
        String plannedLoop = string(plannedSchema, "loopBound");
        String observedLoop = string(observedSchema, "loopBound");
        if (!plannedLoop.equals(observedLoop)) {
            result.add(divergence("loopBound", plannedLoop, observedLoop));
        }
        return result;
    }

    /**
     * The planned branch events this execution never decided.
     *
     * <p>An activation cut at its declared bound never runs the tail of its
     * region, so the sites it did not reach are that bound and not a
     * coverage finding; every other unreached planned site is one.</p>
     */
    private static String unobservedPlannedEvents(JsonObject raw,
                                                  JsonObject plannedSchema,
                                                  JsonObject observedSchema) {
        if (ConcolicSummaryImporter.boundedPrefixExit(
                string(raw, "exitKind"))) {
            return "";
        }
        SortedSet<String> unseen = new TreeSet<>(
                textSet(array(plannedSchema, "branchSites")));
        unseen.removeAll(textSet(array(observedSchema, "branchSites")));
        return unseen.isEmpty() ? ""
                : PLANNED_BRANCH_EVENT_NOT_OBSERVED + ":" + join(unseen);
    }

    private static JsonObject divergence(String field, String planned,
                                         String observed) {
        JsonObject result = new JsonObject();
        result.addProperty("field", field);
        result.addProperty("planned", planned);
        result.addProperty("observed", observed);
        return result;
    }

    // ------------------------------------------------------------------ json

    private static String text(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value == null || !value.isJsonPrimitive() ? ""
                : value.getAsString();
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

    private static String join(Collection<String> values) {
        StringBuilder result = new StringBuilder();
        for (String value : values) {
            if (result.length() > 0) result.append(',');
            result.append(value);
        }
        return result.toString();
    }

    /** One machine-readable line naming what an iteration manifest records. */
    JsonObject manifestDigests(int summaryCount) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "CONCOLIC_IMPORT_DIGESTS");
        result.addProperty("iterationId", iterationId);
        result.addProperty("planDigest", planDigest);
        result.addProperty("summaryCount", summaryCount);
        result.addProperty("deltaRowCount", rows.size());
        JsonObject counts = new JsonObject();
        for (Map.Entry<String, Integer> entry : countsByKind().entrySet()) {
            counts.addProperty(entry.getKey(), entry.getValue());
        }
        result.add("deltaCounts", counts);
        return result;
    }
}
