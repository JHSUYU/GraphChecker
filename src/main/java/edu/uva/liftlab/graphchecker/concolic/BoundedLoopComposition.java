package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Checks the loop-count evidence carried by each region-local path case.
 *
 * <p>The concolic executor already runs a bounded loop as straight-line work
 * inside one region activation. Consequently, one case contributes one count
 * per retained loop. This model validates that count against the declared
 * bound (or exact indexed cardinality); it does not manufacture a second case
 * axis for individual loop iterations.</p>
 */
public final class BoundedLoopComposition {
    public static final int SCHEMA_VERSION = 3;
    public static final String KIND = "REGION_PATH_LOOP_COUNTS";
    public static final String AUTHORITY =
            "DECLARED_BOUND_OBSERVED_REGION_PATH_COUNT_V1";
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
    /**
     * A replayed case traversed a retained loop's backedge, and this model
     * admitted no bounded loop for it -- so nothing checked that traversal
     * against a declared bound.  Before this reason existed the model
     * published {@code {boundedLoops: [], gaps: []}} and read as closed.
     */
    public static final String LOOP_OBSERVED_UNDECLARED =
            "BOUNDED_LOOP_OBSERVED_UNDECLARED";

    private final List<BoundedLoop> loops = new ArrayList<>();
    private final List<JsonObject> gaps = new ArrayList<>();
    private final Set<String> gapKeys = new LinkedHashSet<>();

    private BoundedLoopComposition() {
    }

    /**
     * A retained loop belongs to the planned region that declares it, not to
     * one activation of that region.  Plan rows are already addressed that
     * way; bound authorities and observed cases arrive as activations of it.
     */
    private static String planned(JsonObject row) {
        return OccurrenceId.parse(optionalString(row, "occurrenceId"))
                .planned();
    }

    /** Reads one declaration per {@code (occurrenceId, loopSiteId)}. */
    public static BoundedLoopComposition ofPlanRows(
            Collection<JsonObject> planRows,
            Collection<JsonObject> boundAuthorityRows) {
        BoundedLoopComposition model = new BoundedLoopComposition();
        Map<String, LoopBoundPolicy> policies = new LinkedHashMap<>();
        Set<String> conflictingPolicies = new LinkedHashSet<>();
        for (JsonObject authority : safe(boundAuthorityRows)) {
            if (authority == null) continue;
            String occurrence = planned(authority);
            if (occurrence.isEmpty()) continue;
            if (!authority.has(LoopBoundPolicy.FIELD)
                    || !authority.get(LoopBoundPolicy.FIELD).isJsonObject()) {
                continue;
            }
            LoopBoundPolicy policy = LoopBoundPolicy.decode(authority);
            LoopBoundPolicy previous = policies.putIfAbsent(occurrence,
                    policy);
            if (previous != null
                    && !previous.identity().equals(policy.identity())) {
                conflictingPolicies.add(occurrence);
            }
        }

        Map<String, List<JsonObject>> declarations = new LinkedHashMap<>();
        for (JsonObject plan : safe(planRows)) {
            if (plan == null) continue;
            String occurrence = planned(plan);
            if (occurrence.isEmpty()) continue;
            LoopBoundPolicy policy = policies.get(occurrence);
            for (JsonElement element : array(plan, PLAN_FIELD)) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject().deepCopy();
                String site = optionalString(row, LoopBoundPolicy.LOOP_SITE_ID);
                if (site.isEmpty()) {
                    model.gap(LoopBoundPolicy.LOOP_SITE_UNDECLARED,
                            occurrence, "retained loop names no loopSiteId");
                    continue;
                }
                String classification = optionalString(row,
                        LoopBoundPolicy.LOOP_CLASSIFICATION);
                boolean required = LoopBoundPolicy.failureRelevantLoop(row);
                if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                        classification)) {
                    boolean conflict = conflictingPolicies.contains(
                            occurrence);
                    if (policy == null || conflict
                            || !policy.declaredBounds().containsKey(site)) {
                        if (required || conflict) {
                            model.gap(conflict
                                            ? LOOP_BODY_BOUND_DISAGREES
                                            : LOOP_BODY_BOUND_UNDECLARED,
                                    occurrence + "\n" + site,
                                    conflict
                                            ? "selected rows disagree on the "
                                            + "loop-bound policy"
                                            : "condition-controlled loop has "
                                            + "no declared bound");
                        }
                        continue;
                    }
                    int declared = policy.maxBackedgeTraversals(site);
                    JsonElement stated = row.get(
                            LoopBoundPolicy.LOOP_BODY_BOUND);
                    if (stated != null && (!stated.isJsonPrimitive()
                            || !stated.getAsJsonPrimitive().isNumber()
                            || stated.getAsInt() != declared)) {
                        model.gap(LOOP_BODY_BOUND_DISAGREES,
                                occurrence + "\n" + site,
                                "retained row disagrees with declared bound "
                                        + declared);
                        continue;
                    }
                    row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND,
                            declared);
                    row.addProperty(
                            LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                            LoopBoundPolicy.BOUND_FROM_DECLARATION);
                }
                row.addProperty("occurrenceId", occurrence);
                declarations.computeIfAbsent(occurrence + "\n" + site,
                        ignored -> new ArrayList<>()).add(row);
            }
        }

        for (Map.Entry<String, List<JsonObject>> declaration
                : declarations.entrySet()) {
            BoundedLoop loop = model.admit(declaration.getKey(),
                    declaration.getValue());
            if (loop != null) model.loops.add(loop);
        }
        return model;
    }

    private BoundedLoop admit(String identity,
                              List<JsonObject> declarations) {
        JsonObject first = declarations.get(0);
        String occurrence = optionalString(first, "occurrenceId");
        String site = optionalString(first, LoopBoundPolicy.LOOP_SITE_ID);
        String runtime = optionalString(first, LoopBoundPolicy.RUNTIME_LOOP_ID);
        String classification = optionalString(first,
                LoopBoundPolicy.LOOP_CLASSIFICATION);
        String classificationAuthority = optionalString(first,
                LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY);
        int bound = optionalInteger(first, LoopBoundPolicy.LOOP_BODY_BOUND, 0);
        boolean required = LoopBoundPolicy.failureRelevantLoop(first);

        if (!LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(classification)
                && !LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                classification)) {
            gap(LOOP_CLASSIFICATION_UNDECLARED, identity,
                    "retained loop has no supported classification");
            return null;
        }
        String expectedAuthority =
                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(
                        classification)
                        ? LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED
                        : LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED;
        if (!expectedAuthority.equals(classificationAuthority)) {
            gap(LOOP_CLASSIFICATION_DISAGREES, identity,
                    "classification authority does not match "
                            + classification);
            return null;
        }
        if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(classification)
                && (bound < 1 || !LoopBoundPolicy.BOUND_FROM_DECLARATION
                .equals(optionalString(first,
                        LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY)))) {
            gap(LOOP_BODY_BOUND_UNDECLARED, identity,
                    "condition-controlled loop has no declared bound");
            return null;
        }
        for (JsonObject row : declarations) {
            if (!classification.equals(optionalString(row,
                    LoopBoundPolicy.LOOP_CLASSIFICATION))
                    || !classificationAuthority.equals(optionalString(row,
                    LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY))
                    || !runtime.equals(optionalString(row,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))
                    || required != LoopBoundPolicy.failureRelevantLoop(row)) {
                gap(LOOP_CLASSIFICATION_DISAGREES, identity,
                        "duplicate declarations disagree");
                return null;
            }
            if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                    classification)
                    && bound != optionalInteger(row,
                    LoopBoundPolicy.LOOP_BODY_BOUND, 0)) {
                gap(LOOP_BODY_BOUND_DISAGREES, identity,
                        "duplicate declarations state different bounds");
                return null;
            }
        }
        return new BoundedLoop(occurrence, site, runtime, bound,
                optionalString(first, LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY),
                classification, classificationAuthority, required);
    }

    /** Adds one complete region-path count vector to the audit model. */
    public void observeCase(String occurrenceId, JsonObject item) {
        String occurrence = OccurrenceId.parse(occurrenceId).planned();
        Set<String> matched = new LinkedHashSet<>();
        Map<String, JsonObject> observed = new LinkedHashMap<>();
        Set<String> duplicates = new LinkedHashSet<>();
        for (JsonElement element : array(item,
                LoopBoundPolicy.PATH_LOOP_COUNTS)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String site = optionalString(row, LoopBoundPolicy.LOOP_SITE_ID);
            if (observed.putIfAbsent(site, row) != null) {
                duplicates.add(site);
            }
        }
        String caseId = optionalString(item, "caseId");
        for (BoundedLoop loop : loops) {
            if (!loop.occurrenceId.equals(occurrence)) continue;
            JsonObject row = observed.get(loop.loopSiteId);
            if (row == null) {
                fail(loop, LoopBoundPolicy.PATH_LOOP_COUNT_MISSING, caseId,
                        "region path carries no count for retained loop");
                continue;
            }
            if (duplicates.contains(loop.loopSiteId)) {
                fail(loop, LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS, caseId,
                        "region path carries more than one count for loop");
                continue;
            }
            matched.add(loop.loopSiteId);
            JsonObject countRow = caseCount(caseId, row, item);
            // One planned region can run several times, and each activation
            // reports the same region-local case.  Identical evidence is one
            // count, not one per activation.
            if (loop.pathCountKeys.add(CanonicalJson.render(countRow))) {
                loop.pathCounts.add(countRow);
            }
            if (!loop.classification.equals(optionalString(row,
                    LoopBoundPolicy.LOOP_CLASSIFICATION))
                    || !loop.classificationAuthority.equals(optionalString(row,
                    LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY))) {
                fail(loop, LOOP_CLASSIFICATION_DISAGREES, caseId,
                        "path count disagrees with retained loop metadata");
                continue;
            }
            int count = optionalInteger(row, LoopBoundPolicy.LOOP_BODY_COUNT, -1);
            if (count < 0 || loop.conditionBounded()
                    && count > loop.bodyBound) {
                fail(loop, LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                        caseId, "observed body count is outside the bound");
                continue;
            }
            JsonElement reached = row.get(
                    LoopBoundPolicy.PATH_LOOP_REACHED);
            if (reached == null || !reached.isJsonPrimitive()
                    || !reached.getAsJsonPrimitive().isBoolean()) {
                fail(loop, LoopBoundPolicy.PATH_LOOP_REACHABILITY_MISSING,
                        caseId, "path does not state whether loop control was "
                                + "reached");
                continue;
            }
            boolean loopReached = reached.getAsBoolean();
            if (!loopReached && count != 0) {
                fail(loop, LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                        caseId, "unreached loop has a nonzero body count");
                continue;
            }
            if (loop.fixedCount() && loopReached
                    && !exactCardinalities(row, count,
                    loop.runtimeLoopId)) {
                fail(loop, LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                        caseId, "indexed loop lacks a dense exact cardinality "
                                + "vector covering its body count");
                continue;
            }
            countRow.addProperty("loopCountComplete", true);
        }
        for (JsonElement element : array(item,
                LoopBoundPolicy.PATH_LOOP_COUNT_GAPS)) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            String subject = optionalString(row, "subject");
            gap(optionalString(row, "reason"), subject + "\n" + caseId,
                    optionalString(row, "detail"));
        }
        // A retained loop whose backedge this case actually traversed, with
        // no bounded loop admitted to check it against a declared bound.
        for (Map.Entry<String, JsonObject> observation : observed.entrySet()) {
            String site = observation.getKey();
            if (site.isEmpty() || matched.contains(site)) continue;
            if (optionalInteger(observation.getValue(),
                    LoopBoundPolicy.LOOP_BODY_COUNT, 0) < 1) {
                continue;
            }
            gap(LOOP_OBSERVED_UNDECLARED, occurrence + "\n" + site,
                    "replayed case traversed a retained loop that this"
                            + " composition declared no bound for");
        }
    }

    private void fail(BoundedLoop loop, String reason, String caseId,
                      String detail) {
        gap(reason, loop.identity + "\n" + caseId, detail);
    }

    private static JsonObject caseCount(String caseId, JsonObject observed,
                                        JsonObject item) {
        JsonObject row = observed.deepCopy();
        row.addProperty("caseId", caseId);
        row.addProperty("occurrenceId", optionalString(item, "occurrenceId"));
        row.addProperty("loopCountComplete", false);
        return row;
    }

    /** Exact indexed-loop cardinalities that cover this path's body count. */
    private static boolean exactCardinalities(JsonObject observed,
                                              int bodyCount,
                                              String expectedRuntimeLoopId) {
        JsonArray rows = array(observed,
                LoopBoundPolicy.LOOP_CARDINALITIES);
        if (rows.size() == 0 || expectedRuntimeLoopId.isEmpty()) return false;
        Set<Integer> occurrences = new LinkedHashSet<>();
        String observedRuntimeLoopId = optionalString(observed,
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
            int occurrence = optionalInteger(row,
                    LoopBoundPolicy.DYNAMIC_OCCURRENCE, -1);
            int cardinality = optionalInteger(row,
                    LoopBoundPolicy.LOOP_CARDINALITY, -1);
            if (occurrence < 1 || cardinality < 0
                    || !occurrences.add(occurrence)
                    || !expectedRuntimeLoopId.equals(optionalString(row,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))
                    || !LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY.equals(
                    optionalString(row, "cardinalityAuthority"))) {
                return false;
            }
            maximum = Math.max(maximum, occurrence);
            cardinalityTotal += cardinality;
        }
        if (occurrences.size() != maximum) return false;
        for (int occurrence = 1; occurrence <= maximum; occurrence++) {
            if (!occurrences.contains(occurrence)) return false;
        }
        return bodyCount <= cardinalityTotal;
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
        for (JsonObject gap : gaps) gapRows.add(gap.deepCopy());
        result.add("gaps", gapRows);
        return result;
    }

    /**
     * The gaps this model raised, for the composer's own gap stream.
     *
     * <p>A loop the replay traversed and this model could not check is a
     * property of the emitted candidate, not only coverage telemetry, so the
     * composer refuses on it rather than publishing it and moving on.</p>
     */
    public List<JsonObject> compositionGaps() {
        List<JsonObject> rows = new ArrayList<>();
        for (JsonObject gap : gaps) {
            if (LOOP_OBSERVED_UNDECLARED.equals(
                    optionalString(gap, "reason"))) {
                rows.add(gap.deepCopy());
            }
        }
        return rows;
    }

    private static Collection<JsonObject> safe(
            Collection<JsonObject> rows) {
        return rows == null ? Collections.emptyList() : rows;
    }

    /** One retained loop and the region-path counts observed for it. */
    public static final class BoundedLoop {
        public final String occurrenceId;
        public final String loopSiteId;
        public final String runtimeLoopId;
        public final int bodyBound;
        public final String boundAuthority;
        public final String classification;
        public final String classificationAuthority;
        public final String identity;
        public final boolean failureRelevant;
        private final List<JsonObject> pathCounts = new ArrayList<>();
        private final Set<String> pathCountKeys = new LinkedHashSet<>();

        private BoundedLoop(String occurrenceId, String loopSiteId,
                            String runtimeLoopId, int bodyBound,
                            String boundAuthority, String classification,
                            String classificationAuthority,
                            boolean failureRelevant) {
            this.occurrenceId = occurrenceId;
            this.loopSiteId = loopSiteId;
            this.runtimeLoopId = runtimeLoopId;
            this.bodyBound = bodyBound;
            this.boundAuthority = boundAuthority;
            this.classification = classification;
            this.classificationAuthority = classificationAuthority;
            this.identity = occurrenceId + "\n" + loopSiteId;
            this.failureRelevant = failureRelevant;
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
            row.addProperty("kind", "REGION_PATH_LOOP_COUNT_SET");
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
            row.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT,
                    failureRelevant);
            JsonArray counts = new JsonArray();
            for (JsonObject count : pathCounts) counts.add(count.deepCopy());
            row.add("caseCounts", counts);
            return row;
        }
    }
}
