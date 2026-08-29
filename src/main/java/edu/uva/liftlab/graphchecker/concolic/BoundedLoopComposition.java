package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
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
    /** Manifest mark for the retained loop that owns an OCC-1 address. */
    public static final String ROOT_LOOP_BODY_ADDRESS =
            "rootLoopBodyAddress";

    private final List<BoundedLoop> loops = new ArrayList<>();
    private final List<JsonObject> gaps = new ArrayList<>();
    private final Set<String> gapKeys = new LinkedHashSet<>();
    private final Set<String> occurrenceClosureRequiredLoops =
            new LinkedHashSet<>();

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
        Map<String, List<JsonObject>> relationCoverage =
                new LinkedHashMap<>();
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
            if (authority.has("pathCoverageState")) {
                relationCoverage.computeIfAbsent(occurrence,
                        ignored -> new ArrayList<JsonObject>()).add(authority);
            }
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
            JsonObject rootLoop = object(plan, LoopBoundPolicy.ROOT_LOOP);
            boolean loopBodyRoot = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                    string(plan, LoopBoundPolicy.ROOT_AUTHORITY))
                    && LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                    string(rootLoop, "authority"));
            String rootLoopSite = string(rootLoop,
                    LoopBoundPolicy.LOOP_SITE_ID);
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
                boolean rootLoopBodyAddress = loopBodyRoot
                        && site.equals(rootLoopSite);
                if (demanded || rootLoopBodyAddress) {
                    model.occurrenceClosureRequiredLoops.add(
                            occurrence + "\n" + site);
                }
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
                row.addProperty(ROOT_LOOP_BODY_ADDRESS,
                        rootLoopBodyAddress);
                row.addProperty("occurrenceId", occurrence);
                declarations.computeIfAbsent(occurrence + "\n" + site,
                        ignored -> new ArrayList<JsonObject>()).add(row);
            }
        }
        for (Map.Entry<String, List<JsonObject>> entry
                : declarations.entrySet()) {
            String occurrence = string(entry.getValue().get(0),
                    "occurrenceId");
            BoundedLoop loop = model.admit(entry.getKey(), entry.getValue(),
                    relationCoverage.get(occurrence));
            if (loop != null) model.loops.add(loop);
        }
        return model;
    }

    private BoundedLoop admit(String identity,
                              List<JsonObject> declarations,
                              List<JsonObject> relationCoverage) {
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
        return new BoundedLoop(string(first, "occurrenceId"), site,
                string(first, LoopBoundPolicy.RUNTIME_LOOP_ID), bound,
                string(first, LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY),
                kind,
                string(first,
                        LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY),
                array(first, LoopBoundPolicy.LOOP_CONTROL_SITE_IDS),
                bool(first, ROOT_LOOP_BODY_ADDRESS, false),
                LoopBoundPolicy.failureRelevantLoop(first),
                relationCoverage);
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
            loop.relationCaseCount++;
            JsonObject row = observed.get(loop.loopSiteId);
            if (row == null) {
                gap(LoopBoundPolicy.PATH_LOOP_COUNT_MISSING,
                        loop.identity + "\n" + caseId,
                        "guarded case carries no path-local count for its "
                                + "retained loop");
                loop.pathEvidenceGap = true;
                continue;
            }
            int count = integer(row, LoopBoundPolicy.LOOP_BODY_COUNT, -1);
            if (count < 0 || loop.conditionBounded()
                    && count > loop.bodyBound) {
                gap(LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                        loop.identity + "\n" + caseId,
                        "case count " + count + " is outside 0.."
                                + loop.bodyBound);
                loop.pathEvidenceGap = true;
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
                loop.pathEvidenceGap = true;
                loop.pathCounts.add(caseCount(caseId, row, item));
                continue;
            }
            boolean loopReached = reached.getAsBoolean();
            if (loop.fixedCount() && loopReached
                    && !exactCardinalities(row, count,
                    loop.runtimeLoopId)) {
                gap(LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                        loop.identity + "\n" + caseId,
                        "fixed-count case does not carry a dense exact "
                                + "dynamic cardinality vector covering its "
                                + "body count");
                loop.pathEvidenceGap = true;
            }
            loop.pathCounts.add(caseCount(caseId, row, item));
        }
        for (JsonElement element : array(item,
                LoopBoundPolicy.PATH_LOOP_COUNT_GAPS)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            gap(string(row, "reason"), string(row, "subject") + "\n"
                            + caseId,
                    string(row, "detail"));
            String subject = string(row, "subject");
            for (BoundedLoop loop : loops) {
                if (loop.occurrenceId.equals(occurrenceId)
                        && (loop.loopSiteId.equals(subject)
                        || loop.identity.equals(subject))) {
                    loop.pathEvidenceGap = true;
                }
            }
        }
    }

    private static JsonObject caseCount(String caseId, JsonObject observed,
                                        JsonObject item) {
        JsonObject row = observed.deepCopy();
        row.addProperty("caseId", caseId);
        row.addProperty("occurrenceId", string(item, "occurrenceId"));
        row.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                string(item, PathObservation.PLANNED_OCCURRENCE_ID));
        row.addProperty(PathObservation.ACTIVATION_ORDINAL,
                integer(item, PathObservation.ACTIVATION_ORDINAL, 0));
        row.addProperty("relationallyComplete",
                bool(item, "relationallyComplete", false));
        row.addProperty("terminalKind",
                string(object(item, "terminal"), "kind"));
        return row;
    }

    /**
     * Planned LOOP_BODY_ROOT addresses whose complete selected relation
     * enumerates exactly the declared {@code a1..aK} occurrence prefix.
     */
    public Set<String> closedOccurrenceAddresses() {
        Set<String> closed = new LinkedHashSet<>();
        Map<String, List<BoundedLoop>> byOccurrence = new LinkedHashMap<>();
        for (BoundedLoop loop : loops) {
            byOccurrence.computeIfAbsent(loop.occurrenceId,
                    ignored -> new ArrayList<BoundedLoop>()).add(loop);
        }
        for (Map.Entry<String, List<BoundedLoop>> entry
                : byOccurrence.entrySet()) {
            String occurrence = entry.getKey();
            for (BoundedLoop loop : entry.getValue()) {
                loop.occurrenceAxisClosed = false;
            }
            if (hasOccurrenceAuthorityGap(occurrence)) continue;
            BoundedLoop root = null;
            boolean ambiguousRoot = false;
            for (BoundedLoop loop : entry.getValue()) {
                if (!loop.rootLoopBodyAddress) continue;
                if (root == null) root = loop;
                else ambiguousRoot = true;
            }
            if (root == null || ambiguousRoot
                    || !root.closesOccurrenceAxis()) {
                continue;
            }
            Set<String> cases = root.caseKeys();
            boolean localLoopsComplete = true;
            for (BoundedLoop loop : entry.getValue()) {
                // The root's dense a1..aK rule is the occurrence census.  Its
                // body count is therefore checked there, not as an inner
                // condition loop (K=1 would otherwise require 1 < 1).
                if (loop == root || !loop.failureRelevant) continue;
                if (!loop.pathLocallyComplete(cases)) {
                    localLoopsComplete = false;
                    break;
                }
            }
            if (localLoopsComplete) {
                root.occurrenceAxisClosed = true;
                closed.add(occurrence);
            }
        }
        return Collections.unmodifiableSet(closed);
    }

    /** A loop-authority failure for this address cannot be repaired by a
     *  different retained loop at the same address. */
    private boolean hasOccurrenceAuthorityGap(String occurrence) {
        for (JsonObject row : gaps) {
            String subject = string(row, "subject");
            if (occurrence.equals(subject)) return true;
            for (String identity : occurrenceClosureRequiredLoops) {
                if (!identity.startsWith(occurrence + "\n")) continue;
                if (identity.equals(subject)
                        || subject.startsWith(identity + "\n")) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Exact dynamic fixed-loop cardinalities that cover the body count. */
    private static boolean exactCardinalities(JsonObject observed,
                                              int bodyCount,
                                              String expectedRuntimeLoopId) {
        JsonArray rows = array(observed,
                LoopBoundPolicy.LOOP_CARDINALITIES);
        if (rows.size() == 0) return false;
        Set<Integer> occurrences = new LinkedHashSet<>();
        if (expectedRuntimeLoopId.isEmpty()) return false;
        String observedRuntimeLoopId = string(observed,
                LoopBoundPolicy.RUNTIME_LOOP_ID);
        if (!observedRuntimeLoopId.isEmpty()
                && !expectedRuntimeLoopId.equals(observedRuntimeLoopId)) {
            return false;
        }
        int maximum = 0;
        long cardinalityTotal = 0L;
        for (JsonElement element : rows) {
            if (!element.isJsonObject()) return false;
            JsonObject row = element.getAsJsonObject();
            int occurrence = integer(row,
                    LoopBoundPolicy.DYNAMIC_OCCURRENCE, -1);
            int cardinality = integer(row,
                    LoopBoundPolicy.LOOP_CARDINALITY, -1);
            if (occurrence < 1 || cardinality < 0
                    || !occurrences.add(occurrence)
                    || !expectedRuntimeLoopId.equals(string(row,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))
                    || !LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY.equals(
                    string(row, "cardinalityAuthority"))) {
                return false;
            }
            maximum = Math.max(maximum, occurrence);
            cardinalityTotal += cardinality;
        }
        if (occurrences.size() != maximum) return false;
        for (int occurrence = 1; occurrence <= maximum; occurrence++) {
            if (!occurrences.contains(occurrence)) return false;
        }
        // A guarded path may leave an indexed loop early, so its executed
        // bodies can be fewer than the exact array extent, never greater.
        return bodyCount >= 0 && bodyCount <= cardinalityTotal;
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
        // Refresh the group-level mark before serializing individual rows.
        closedOccurrenceAddresses();
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
        public final String runtimeLoopId;
        public final int bodyBound;
        public final String boundAuthority;
        public final String classification;
        public final String classificationAuthority;
        public final List<String> controlSiteIds;
        public final String identity;
        public final boolean rootLoopBodyAddress;
        public final boolean failureRelevant;
        private final List<JsonObject> pathCounts = new ArrayList<>();
        private final int relationCoverageRows;
        private final boolean relationCoverageClosed;
        private final boolean relationEvidenceAdmitted;
        private int relationCaseCount;
        private boolean pathEvidenceGap;
        private boolean occurrenceAxisClosed;

        private BoundedLoop(String occurrenceId, String loopSiteId,
                            String runtimeLoopId,
                            int bodyBound, String boundAuthority,
                            String classification,
                            String classificationAuthority,
                            JsonArray controlSites,
                            boolean rootLoopBodyAddress,
                            boolean failureRelevant,
                            List<JsonObject> relationCoverage) {
            this.occurrenceId = occurrenceId;
            this.loopSiteId = loopSiteId;
            this.runtimeLoopId = runtimeLoopId;
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
            this.rootLoopBodyAddress = rootLoopBodyAddress;
            this.failureRelevant = failureRelevant;
            List<JsonObject> coverage = relationCoverage == null
                    ? Collections.<JsonObject>emptyList()
                    : relationCoverage;
            this.relationCoverageRows = coverage.size();
            this.relationCoverageClosed = coverage.size() == 1
                    && "CLOSED".equals(string(coverage.get(0),
                    "pathCoverageState"))
                    && bool(coverage.get(0), "relationallyComplete", false);
            String coverageState = coverage.size() == 1
                    ? string(coverage.get(0), "pathCoverageState") : "";
            this.relationEvidenceAdmitted = coverage.size() == 1
                    && bool(coverage.get(0), "relationallyComplete", false)
                    && ("CLOSED".equals(coverageState)
                    || "PARTIAL".equals(coverageState)
                    || "SEED_ONLY".equals(coverageState));
        }

        public boolean conditionBounded() {
            return LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                    classification);
        }

        public boolean fixedCount() {
            return LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(
                    classification);
        }

        private boolean closesOccurrenceAxis() {
            if (!rootLoopBodyAddress || !conditionBounded()
                    || bodyBound < 1
                    || !LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED
                    .equals(classificationAuthority)
                    || !LoopBoundPolicy.BOUND_FROM_DECLARATION.equals(
                    boundAuthority)
                    || relationCoverageRows != 1
                    || !relationEvidenceAdmitted
                    || pathEvidenceGap
                    || relationCaseCount != bodyBound
                    || pathCounts.size() != bodyBound) {
                return false;
            }
            Set<Integer> ordinals = new LinkedHashSet<>();
            for (JsonObject count : pathCounts) {
                int ordinal = integer(count,
                        PathObservation.ACTIVATION_ORDINAL, 0);
                if (ordinal < 1 || ordinal > bodyBound
                        || !occurrenceId.equals(string(count,
                        PathObservation.PLANNED_OCCURRENCE_ID))
                        || !(occurrenceId + "#a" + ordinal).equals(
                        string(count, "occurrenceId"))
                        || !bool(count, "relationallyComplete", false)
                        || !"NORMAL".equals(string(count, "terminalKind"))
                        || !loopSiteId.equals(string(count,
                        LoopBoundPolicy.LOOP_SITE_ID))
                        || !classification.equals(string(count,
                        LoopBoundPolicy.LOOP_CLASSIFICATION))
                        || !classificationAuthority.equals(string(count,
                        LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY))
                        || !bool(count,
                        LoopBoundPolicy.PATH_LOOP_REACHED, false)
                        || integer(count,
                        LoopBoundPolicy.LOOP_BODY_COUNT, -1) != 1
                        || integer(count,
                        LoopBoundPolicy.LOOP_BODY_BOUND, -1) != bodyBound
                        || !LoopBoundPolicy.BOUND_FROM_DECLARATION.equals(
                        string(count,
                                LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY))) {
                    return false;
                }
                ordinals.add(ordinal);
            }
            if (ordinals.size() != bodyBound) return false;
            for (int ordinal = 1; ordinal <= bodyBound; ordinal++) {
                if (!ordinals.contains(ordinal)) return false;
            }
            return true;
        }

        private Set<String> caseKeys() {
            Set<String> result = new LinkedHashSet<>();
            for (JsonObject count : pathCounts) {
                result.add(caseKey(count));
            }
            return result;
        }

        private static String caseKey(JsonObject count) {
            return string(count, "caseId") + "\n"
                    + string(count, "occurrenceId") + "\n"
                    + integer(count, PathObservation.ACTIVATION_ORDINAL, 0);
        }

        /**
         * Path-local completeness for one failure-relevant inner loop.  A
         * fixed loop is complete from its exact dynamic cardinality census;
         * a condition loop is complete only when it exits normally below K.
         */
        private boolean pathLocallyComplete(Set<String> expectedCases) {
            if (!relationEvidenceAdmitted || pathEvidenceGap
                    || relationCaseCount < 1
                    || pathCounts.size() != relationCaseCount
                    || caseKeys().size() != pathCounts.size()
                    || !caseKeys().equals(expectedCases)) {
                return false;
            }
            for (JsonObject count : pathCounts) {
                if (!bool(count, "relationallyComplete", false)
                        || !"NORMAL".equals(string(count, "terminalKind"))
                        || !loopSiteId.equals(string(count,
                        LoopBoundPolicy.LOOP_SITE_ID))
                        || !classification.equals(string(count,
                        LoopBoundPolicy.LOOP_CLASSIFICATION))
                        || !classificationAuthority.equals(string(count,
                        LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY))) {
                    return false;
                }
                int observedBodies = integer(count,
                        LoopBoundPolicy.LOOP_BODY_COUNT, -1);
                if (observedBodies < 0) return false;
                boolean reached = bool(count,
                        LoopBoundPolicy.PATH_LOOP_REACHED, false);
                if (!reached) {
                    if (observedBodies != 0) return false;
                    continue;
                }
                if (fixedCount()) {
                    if (!LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED.equals(
                            classificationAuthority)
                            || !exactCardinalities(count, observedBodies,
                            runtimeLoopId)) {
                        return false;
                    }
                } else if (conditionBounded()) {
                    if (bodyBound < 1 || observedBodies >= bodyBound
                            || !LoopBoundPolicy
                            .LOOP_CLASSIFIED_CONDITION_CONTROLLED.equals(
                                    classificationAuthority)
                            || integer(count,
                            LoopBoundPolicy.LOOP_BODY_BOUND, -1) != bodyBound
                            || !LoopBoundPolicy.BOUND_FROM_DECLARATION.equals(
                            string(count, LoopBoundPolicy
                                    .LOOP_BODY_BOUND_AUTHORITY))) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            return true;
        }

        public JsonObject toJson() {
            JsonObject row = new JsonObject();
            row.addProperty("kind", "PATH_LOCAL_LOOP_COUNT_SET");
            row.addProperty("occurrenceId", occurrenceId);
            row.addProperty(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
            row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, runtimeLoopId);
            row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, bodyBound);
            row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                    boundAuthority);
            row.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                    classification);
            row.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                    classificationAuthority);
            row.addProperty(ROOT_LOOP_BODY_ADDRESS, rootLoopBodyAddress);
            row.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT,
                    failureRelevant);
            row.addProperty("relationCoverageRows", relationCoverageRows);
            row.addProperty("relationCoverageClosed",
                    relationCoverageClosed);
            row.addProperty("relationEvidenceAdmitted",
                    relationEvidenceAdmitted);
            row.addProperty("occurrenceAxisClosed",
                    occurrenceAxisClosed);
            JsonArray counts = new JsonArray();
            for (JsonObject count : pathCounts) counts.add(count.deepCopy());
            row.add("caseCounts", counts);
            return row;
        }
    }
}
