package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Declared loop bounds plus the path-local count vector of each guarded case.
 * A replay path is already one complete transition relation, so counts
 * qualify that case rather than creating iteration-local ports, writer
 * instances or a second unrolling; different counts arrive as different
 * guarded cases and extend the bounded supergraph incrementally.
 */
public final class BoundedLoopComposition {
    public static final int SCHEMA_VERSION = 2;
    public static final String KIND = "PATH_LOCAL_LOOP_COUNTS";
    public static final String AUTHORITY =
            "DECLARED_BOUND_OBSERVED_PATH_COUNT_V1";
    public static final String MANIFEST_FIELD = "boundedLoopComposition";
    public static final String PLAN_FIELD = "retainedLoops";
    public static final String GAP_KIND = "BOUNDED_LOOP_COMPOSITION_GAP";
    public static final String GAP_AUTHORITY =
            "BOUNDED_LOOP_COMPOSITION_GAP_V1";

    public static final String LOOP_BODY_BOUND_DISAGREES =
            "BOUNDED_LOOP_BODY_BOUND_DISAGREES";
    public static final String LOOP_BODY_BOUND_UNDECLARED =
            "BOUNDED_LOOP_BODY_BOUND_UNDECLARED";
    public static final String LOOP_CLASSIFICATION_UNDECLARED =
            "BOUNDED_LOOP_CLASSIFICATION_UNDECLARED";
    public static final String LOOP_CLASSIFICATION_DISAGREES =
            "BOUNDED_LOOP_CLASSIFICATION_DISAGREES";

    private final List<BoundedLoop> loops = new ArrayList<>();
    private final List<JsonObject> gaps = new ArrayList<>();
    private final Set<String> gapKeys = new LinkedHashSet<>();

    private BoundedLoopComposition() {
    }

    public static BoundedLoopComposition empty() {
        return new BoundedLoopComposition();
    }

    /** Reads one declaration per {@code (occurrenceId, loopSiteId)}. */
    public static BoundedLoopComposition ofPlanRows(
            Collection<JsonObject> planRows,
            Collection<JsonObject> boundAuthorityRows) {
        BoundedLoopComposition model = new BoundedLoopComposition();
        Map<String, List<JsonObject>> declarations = new LinkedHashMap<>();
        Map<String, LoopBoundPolicy> policies = new LinkedHashMap<>();
        Set<String> conflictingPolicies = new LinkedHashSet<>();
        for (JsonObject authority : boundAuthorityRows == null
                ? Collections.<JsonObject>emptyList()
                : boundAuthorityRows) {
            if (authority == null
                    || !authority.has(LoopBoundPolicy.FIELD)
                    || !authority.get(LoopBoundPolicy.FIELD)
                    .isJsonObject()) {
                continue;
            }
            String occurrence = string(authority, "occurrenceId");
            if (occurrence.isEmpty()) continue;
            LoopBoundPolicy decoded = LoopBoundPolicy.decode(authority);
            LoopBoundPolicy held = policies.putIfAbsent(
                    occurrence, decoded);
            if (held != null && !held.identity().equals(
                    decoded.identity())) {
                conflictingPolicies.add(occurrence);
            }
        }
        if (planRows == null) return model;
        for (JsonObject plan : planRows) {
            if (plan == null) continue;
            String occurrence = string(plan, "occurrenceId");
            JsonArray retained = array(plan, PLAN_FIELD);
            // A plan with no retained loop requires no loop-bound authority.
            if (retained.size() == 0) continue;
            LoopBoundPolicy policy = policies.get(occurrence);
            boolean conflicting = conflictingPolicies.contains(occurrence);
            for (JsonElement element : retained) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject().deepCopy();
                String site = string(row, LoopBoundPolicy.LOOP_SITE_ID);
                if (site.isEmpty()) {
                    model.gap(LoopBoundPolicy.LOOP_SITE_UNDECLARED,
                            occurrence, "retained loop names no loopSiteId");
                    continue;
                }
                boolean demanded =
                        LoopBoundPolicy.failureRelevantLoop(row);
                if (policy == null || conflicting) {
                    // A loop whose trip count nothing the failure reads can
                    // observe states no bound obligation, so an absent
                    // authority for it is not a coverage gap.  A disagreement
                    // still is: two contradictory declarations are wrong
                    // about this loop whatever the failure reads.
                    if (conflicting || demanded) {
                        model.gap(policy == null
                                        ? LOOP_BODY_BOUND_UNDECLARED
                                        : LOOP_BODY_BOUND_DISAGREES,
                                occurrence + "\n" + site,
                                policy == null
                                        ? "selected occurrence has retained "
                                        + "loop but no task-derived loopBound "
                                        + "authority"
                                        : "selected summaries disagree on the "
                                        + "same occurrence loopBound "
                                        + "authority");
                    }
                    continue;
                }
                if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(string(row,
                        LoopBoundPolicy.LOOP_CLASSIFICATION))) {
                    // README LOOP-1: a retained condition loop that declares
                    // no K_L does not quietly run under the core default,
                    // which was never measured against it.  Named here;
                    // Composer refuses it through LOOP_AUTHORITY_REFUSALS
                    // when the loop lies inside the selected slice.
                    if (!policy.declaredBounds().containsKey(site)) {
                        if (demanded) {
                            model.gap(LOOP_BODY_BOUND_UNDECLARED,
                                    occurrence + "\n" + site,
                                    "retained condition loop inherits the "
                                            + "core default K_L="
                                            + LoopBoundPolicy
                                            .MAX_LOOP_BODY_ITERATIONS);
                        }
                        continue;
                    }
                    int effective = policy.maxBackedgeTraversals(site);
                    JsonElement stated = row.get(
                            LoopBoundPolicy.LOOP_BODY_BOUND);
                    if (stated != null && (!stated.isJsonPrimitive()
                            || !stated.getAsJsonPrimitive().isNumber()
                            || stated.getAsInt() != effective)) {
                        model.gap(LOOP_BODY_BOUND_DISAGREES,
                                occurrence + "\n" + site,
                                "retained row states K_L=" + stated
                                        + " but task loopBound states K_L="
                                        + effective);
                        continue;
                    }
                    // Only a declared K_L reaches this point, so the row's
                    // authority is the declaration itself and nothing else.
                    row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND,
                            effective);
                    row.addProperty(
                            LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                            LoopBoundPolicy.BOUND_FROM_DECLARATION);
                }
                row.addProperty("occurrenceId", occurrence);
                declarations.computeIfAbsent(occurrence + "\n" + site,
                        ignored -> new ArrayList<JsonObject>()).add(row);
            }
        }
        for (Map.Entry<String, List<JsonObject>> entry
                : declarations.entrySet()) {
            BoundedLoop loop = model.admit(entry.getKey(), entry.getValue());
            if (loop != null) model.loops.add(loop);
        }
        return model;
    }

    private BoundedLoop admit(String identity,
                              List<JsonObject> declarations) {
        JsonObject first = declarations.get(0);
        String site = string(first, LoopBoundPolicy.LOOP_SITE_ID);
        String kind = string(first, LoopBoundPolicy.LOOP_CLASSIFICATION);
        int bound = integer(first, LoopBoundPolicy.LOOP_BODY_BOUND, 0);
        for (JsonObject row : declarations) {
            if (!kind.equals(string(row,
                    LoopBoundPolicy.LOOP_CLASSIFICATION))) {
                gap(LOOP_CLASSIFICATION_DISAGREES, identity,
                        "one retained loop declares two classifications");
                return null;
            }
            if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(kind)
                    && bound != integer(row,
                    LoopBoundPolicy.LOOP_BODY_BOUND, 0)) {
                gap(LOOP_BODY_BOUND_DISAGREES, identity,
                        "one retained while declares two K_L values");
                return null;
            }
        }
        if (kind.isEmpty()) {
            gap(LOOP_CLASSIFICATION_UNDECLARED, identity,
                    "retained loop declares no classification");
        }
        if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(kind)
                && bound < 1) {
            gap(LOOP_BODY_BOUND_UNDECLARED, identity,
                    "condition-bounded loop declares no K_L");
        }
        return new BoundedLoop(string(first, "occurrenceId"), site, bound,
                string(first, LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY),
                kind,
                string(first,
                        LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY),
                array(first, LoopBoundPolicy.LOOP_CONTROL_SITE_IDS));
    }

    /**
     * Adds one guarded case's already-imported count vector to the audit
     * model. Missing evidence remains a coverage gap. A count beyond K_L is
     * named again defensively; the Importer normally refuses it first.
     */
    public void observeCase(String occurrenceId, JsonObject item) {
        Map<String, JsonObject> observed = new LinkedHashMap<>();
        for (JsonElement element : array(item,
                LoopBoundPolicy.PATH_LOOP_COUNTS)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            observed.put(string(row, LoopBoundPolicy.LOOP_SITE_ID), row);
        }
        String caseId = string(item, "caseId");
        for (BoundedLoop loop : loops) {
            if (!loop.occurrenceId.equals(occurrenceId)) continue;
            JsonObject row = observed.get(loop.loopSiteId);
            if (row == null) {
                gap(LoopBoundPolicy.PATH_LOOP_COUNT_MISSING,
                        loop.identity + "\n" + caseId,
                        "guarded case carries no path-local count for its "
                                + "retained loop");
                continue;
            }
            int count = integer(row, LoopBoundPolicy.LOOP_BODY_COUNT, -1);
            if (count < 0 || loop.conditionBounded()
                    && count > loop.bodyBound) {
                gap(LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                        loop.identity + "\n" + caseId,
                        "case count " + count + " is outside 0.."
                                + loop.bodyBound);
                continue;
            }
            // A coarse region may declare library loops this path returned
            // before reaching.  Their inferred zero body count is not a
            // dynamic N observation and needs no array cardinality, so the
            // importer must state reachability: assuming either answer would
            // invent one of two materially different path-local claims.
            JsonElement reached = row.get(
                    LoopBoundPolicy.PATH_LOOP_REACHED);
            if (reached == null || !reached.isJsonPrimitive()
                    || !reached.getAsJsonPrimitive().isBoolean()) {
                gap(LoopBoundPolicy.PATH_LOOP_REACHABILITY_MISSING,
                        loop.identity + "\n" + caseId,
                        "guarded case does not state whether the retained "
                                + "loop control was reached");
                loop.pathCounts.add(caseCount(caseId, row));
                continue;
            }
            boolean loopReached = reached.getAsBoolean();
            if (loop.fixedCount() && loopReached
                    && !exactCardinalities(row)) {
                gap(LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                        loop.identity + "\n" + caseId,
                        "fixed-count case carries no exact dynamic N");
            }
            loop.pathCounts.add(caseCount(caseId, row));
        }
        for (JsonElement element : array(item,
                LoopBoundPolicy.PATH_LOOP_COUNT_GAPS)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            gap(string(row, "reason"), string(row, "subject") + "\n"
                            + caseId,
                    string(row, "detail"));
        }
    }

    private static JsonObject caseCount(String caseId, JsonObject observed) {
        JsonObject row = observed.deepCopy();
        row.addProperty("caseId", caseId);
        return row;
    }

    private static boolean exactCardinalities(JsonObject observed) {
        JsonArray rows = array(observed,
                LoopBoundPolicy.LOOP_CARDINALITIES);
        if (rows.size() == 0) return false;
        Set<Integer> occurrences = new LinkedHashSet<>();
        for (JsonElement element : rows) {
            if (!element.isJsonObject()) return false;
            JsonObject row = element.getAsJsonObject();
            int occurrence = integer(row,
                    LoopBoundPolicy.DYNAMIC_OCCURRENCE, -1);
            int cardinality = integer(row,
                    LoopBoundPolicy.LOOP_CARDINALITY, -1);
            if (occurrence < 1 || cardinality < 0
                    || !occurrences.add(occurrence)
                    || !LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY.equals(
                    string(row, "cardinalityAuthority"))) {
                return false;
            }
        }
        return true;
    }

    public List<JsonObject> gaps() {
        return Collections.unmodifiableList(gaps);
    }

    public void gap(String reason, String subject, String detail) {
        String key = reason + "\n" + subject;
        if (!gapKeys.add(key)) return;
        JsonObject row = new JsonObject();
        row.addProperty("kind", GAP_KIND);
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("authority", GAP_AUTHORITY);
        row.addProperty("reason", reason);
        row.addProperty("subject", subject);
        row.addProperty("detail", detail);
        gaps.add(row);
    }

    public JsonObject manifest() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("authority", AUTHORITY);
        JsonArray rows = new JsonArray();
        for (BoundedLoop loop : loops) rows.add(loop.toJson());
        result.add("boundedLoops", rows);
        JsonArray gapRows = new JsonArray();
        for (JsonObject gap : gaps) gapRows.add(gap);
        result.add("gaps", gapRows);
        return result;
    }

    /** One declared retained loop and the guarded cases observed for it. */
    public static final class BoundedLoop {
        public final String occurrenceId;
        public final String loopSiteId;
        public final int bodyBound;
        public final String boundAuthority;
        public final String classification;
        public final String classificationAuthority;
        public final List<String> controlSiteIds;
        public final String identity;
        private final List<JsonObject> pathCounts = new ArrayList<>();

        private BoundedLoop(String occurrenceId, String loopSiteId,
                            int bodyBound, String boundAuthority,
                            String classification,
                            String classificationAuthority,
                            JsonArray controlSites) {
            this.occurrenceId = occurrenceId;
            this.loopSiteId = loopSiteId;
            this.bodyBound = bodyBound;
            this.boundAuthority = boundAuthority;
            this.classification = classification;
            this.classificationAuthority = classificationAuthority;
            List<String> sites = new ArrayList<>();
            for (JsonElement site : controlSites) {
                if (site.isJsonPrimitive()) sites.add(site.getAsString());
            }
            this.controlSiteIds = Collections.unmodifiableList(sites);
            this.identity = occurrenceId + "\n" + loopSiteId;
        }

        public boolean conditionBounded() {
            return LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                    classification);
        }

        public boolean fixedCount() {
            return LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(
                    classification);
        }

        public JsonObject toJson() {
            JsonObject row = new JsonObject();
            row.addProperty("kind", "PATH_LOCAL_LOOP_COUNT_SET");
            row.addProperty("occurrenceId", occurrenceId);
            row.addProperty(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
            row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, bodyBound);
            row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                    boundAuthority);
            row.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                    classification);
            row.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                    classificationAuthority);
            JsonArray counts = new JsonArray();
            for (JsonObject count : pathCounts) counts.add(count.deepCopy());
            row.add("caseCounts", counts);
            return row;
        }
    }
}
