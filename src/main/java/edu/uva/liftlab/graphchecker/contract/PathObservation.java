package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.d3.plan.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.d3.plan.LoopBoundPolicy;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.LocalCaseIdentity;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.exactText;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * Immutable, once-decoded view of one imported concolic path summary.  The
 * original summary is retained only as the attested replay payload.
 */
public final class PathObservation {
    private final JsonObject raw;
    private final Scope scope;
    private final List<SummaryBranchMapping> branchMappings;
    private final String branchMappingIssue;
    private final int activationOrdinal;
    private final String plannedOccurrenceId;
    private final String occurrenceId;
    private final String pathKey;
    private final List<Integer> pathConditionPositions;
    private final JsonArray pathCondition;

    private PathObservation(JsonObject summary, JsonObject task) {
        this.raw = summary;
        // The activation tuple is admitted once, by the importer's
        // resultShapeRefusal gate; a summary that reaches this decode has
        // already passed it.
        this.activationOrdinal = exactInteger(raw, ACTIVATION_ORDINAL, -1);
        this.plannedOccurrenceId = exactText(raw, PLANNED_OCCURRENCE_ID);
        this.occurrenceId = exactText(raw, "occurrenceId");
        this.scope = Scope.decode(raw, task);
        List<SummaryBranchMapping> decoded = Collections.emptyList();
        String issue = "";
        try {
            decoded = SummaryBranchMapping.fromSummary(raw);
        } catch (IllegalArgumentException malformed) {
            issue = firstNonBlank(malformed.getMessage(), "UNKNOWN");
        }
        this.branchMappings = Collections.unmodifiableList(decoded);
        this.branchMappingIssue = issue;
        this.pathKey = LocalCaseIdentity.stated(raw);
        JsonArray recorded = array(raw, "pathCondition");
        List<Integer> positions = new ArrayList<>();
        for (int index = 0; index < recorded.size(); index++) {
            positions.add(index);
        }
        this.pathConditionPositions = Collections.unmodifiableList(positions);
        this.pathCondition = recorded;
    }

    public static PathObservation decode(JsonObject summary, JsonObject task) {
        if (summary == null) {
            throw new IllegalArgumentException("summary is required");
        }
        return new PathObservation(summary, task);
    }

    public String regionId() { return optionalString(raw, "regionId"); }
    public String sourceTaskId() { return optionalString(raw, "taskId"); }
    public String occurrenceId() { return occurrenceId; }

    /**
     * OCC-1: one task's address may be entered several times, and every
     * compatible activation is published as its own occurrence rather than
     * one being answered and the rest reported as an ambiguous address.
     *
     * <p>These members travel together. Current summaries always name one
     * exact activation; an incomplete tuple is not a supported schema.</p>
     */
    public static final String ACTIVATION_ORDINAL = "activationOrdinal";
    /** The address the task planned, shared by every activation of it. */
    public static final String PLANNED_OCCURRENCE_ID = "plannedOccurrenceId";
    /** Whether this activation exited through the selected target throw. */
    public static final String TARGET_REACHED = "targetReached";

    /** The required planned address shared by this task's activations. */
    public String plannedOccurrenceId() {
        return plannedOccurrenceId;
    }

    public String sourceKey() { return optionalString(raw, "sourceKey"); }
    public Scope scope() { return scope; }
    public String pathKey() { return pathKey; }
    public List<SummaryBranchMapping> branchMappings() {
        return branchMappings;
    }
    public String branchMappingIssue() { return branchMappingIssue; }
    public JsonArray pathLoopCounts() {
        return array(raw, LoopBoundPolicy.PATH_LOOP_COUNTS);
    }
    /** Missing/ambiguous loop-count evidence; coverage, not a case rewrite. */
    public JsonArray pathLoopCountGaps() {
        return array(raw, LoopBoundPolicy.PATH_LOOP_COUNT_GAPS);
    }
    /** The complete region-local path condition recorded by this activation. */
    public JsonArray pathCondition() {
        return pathCondition;
    }
    /** Original positions of the complete local path condition. */
    public List<Integer> pathConditionPositions() {
        return pathConditionPositions;
    }
    public TargetReachEvent targetReachEvent() {
        JsonElement encoded = raw.get(TargetReachEvent.FIELD);
        return encoded == null ? null : TargetReachEvent.decode(encoded);
    }

    /** Canonical carrier for the runtime event that makes a target path
     *  eligible for composition.  Stricter than the generic accessors:
     *  target identity is an authority, so unknown members and coercions are
     *  schema errors. */
    public static final class TargetReachEvent {
        public static final String FIELD = "targetReach";
        public static final String KIND = "TARGET_REACH_EVENT";

        private final String siteId;
        private final int occurrence;
        private final boolean outcome;
        /**
         * The VM event sequence number at which the anchor was recorded, or
         * {@code 0} when this replay's VM assigned none.  It is the same
         * clock the branch-decision rows publish, so a composer can say which
         * decisions were taken before the anchor and order two activations'
         * decisions against each other; the other published positions
         * (unit index, path-condition index) are local to a method or to one
         * condition window and repeat across activations.
         */
        private final long vmEventId;

        private TargetReachEvent(String siteId, int occurrence,
                                 boolean outcome, long vmEventId) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.outcome = outcome;
            this.vmEventId = vmEventId;
        }

        public static TargetReachEvent decode(JsonElement encoded) {
            if (encoded == null || !encoded.isJsonObject()) {
                throw new IllegalArgumentException(
                        FIELD + " must be an object");
            }
            JsonObject event = encoded.getAsJsonObject();
            boolean clocked = event.has("vmEventId");
            if (event.size() != (clocked ? 5 : 4)
                    || !event.has("kind") || !event.has("siteId")
                    || !event.has("occurrence") || !event.has("outcome")) {
                throw new IllegalArgumentException(
                        FIELD + " must contain exactly kind, siteId, "
                                + "occurrence and outcome, and at most "
                                + "vmEventId");
            }
            JsonElement kind = event.get("kind");
            JsonElement site = event.get("siteId");
            JsonElement ordinal = event.get("occurrence");
            JsonElement taken = event.get("outcome");
            if (!kind.isJsonPrimitive()
                    || !kind.getAsJsonPrimitive().isString()
                    || !KIND.equals(kind.getAsString())) {
                throw new IllegalArgumentException(
                        FIELD + ".kind must be " + KIND);
            }
            if (!site.isJsonPrimitive()
                    || !site.getAsJsonPrimitive().isString()
                    || site.getAsString().trim().isEmpty()) {
                throw new IllegalArgumentException(
                        FIELD + ".siteId must be a nonempty string");
            }
            final int occurrence;
            try {
                if (!ordinal.isJsonPrimitive()
                        || !ordinal.getAsJsonPrimitive().isNumber()) {
                    throw new ArithmeticException("not a number");
                }
                occurrence = new BigDecimal(
                        ordinal.getAsString()).intValueExact();
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        FIELD + ".occurrence must be an exact integer",
                        malformed);
            }
            if (occurrence < 1) {
                throw new IllegalArgumentException(
                        FIELD + ".occurrence must be positive");
            }
            if (!taken.isJsonPrimitive()
                    || !taken.getAsJsonPrimitive().isBoolean()) {
                throw new IllegalArgumentException(
                        FIELD + ".outcome must be a boolean");
            }
            long vmEventId = 0L;
            if (clocked) {
                JsonElement clock = event.get("vmEventId");
                try {
                    if (!clock.isJsonPrimitive()
                            || !clock.getAsJsonPrimitive().isNumber()) {
                        throw new ArithmeticException("not a number");
                    }
                    vmEventId = new BigDecimal(
                            clock.getAsString()).longValueExact();
                } catch (RuntimeException malformed) {
                    throw new IllegalArgumentException(
                            FIELD + ".vmEventId must be an exact integer",
                            malformed);
                }
                if (vmEventId <= 0L) {
                    // A replay whose VM assigned no event states no field at
                    // all; a zero would order this anchor ahead of every
                    // decision the VM did number.
                    throw new IllegalArgumentException(
                            FIELD + ".vmEventId must be positive");
                }
            }
            return new TargetReachEvent(site.getAsString(), occurrence,
                    taken.getAsBoolean(), vmEventId);
        }

        public String siteId() { return siteId; }
        public int occurrence() { return occurrence; }
        public boolean outcome() { return outcome; }

        /** The VM event this anchor was recorded at, or 0 when unclocked. */
        public long vmEventId() { return vmEventId; }

        public boolean matches(String site, int ordinal, boolean taken) {
            return siteId.equals(site) && occurrence == ordinal
                    && outcome == taken;
        }

        public JsonObject toJson() {
            JsonObject event = toIdentityJson();
            if (vmEventId > 0L) event.addProperty("vmEventId", vmEventId);
            return event;
        }

        /**
         * The anchor without its clock, for identity digests.
         *
         * <p>Which VM event this anchor was recorded at is a fact about when
         * the path ran, not about which path it is.  Two replays of one path
         * number their events differently -- everything the process did
         * beforehand shifts them -- so folding the clock into a case identity
         * would make every re-exploration of a path a new case.</p>
         */
        public JsonObject toIdentityJson() {
            JsonObject event = new JsonObject();
            event.addProperty("kind", KIND);
            event.addProperty("siteId", siteId);
            event.addProperty("occurrence", occurrence);
            event.addProperty("outcome", outcome);
            return event;
        }
    }

    public String flipKey(SummaryBranchMapping mapping,
                          boolean desiredOutcome) {
        if (mapping == null || !mapping.isWitnessed()) {
            throw new IllegalArgumentException(
                    "semantic flip key requires a witnessed branch");
        }
        StringBuilder value = new StringBuilder();
        component(value, regionId());
        component(value, sourceKey());
        component(value, occurrenceId());
        component(value, scope.identity);

        int targetPosition = mapping.summaryPcIndex();
        java.util.Map<Integer, SummaryBranchMapping> witnessedByPosition =
                new java.util.TreeMap<>();
        for (SummaryBranchMapping candidate : branchMappings) {
            if (candidate.isWitnessed()
                    && candidate.summaryPcIndex() < targetPosition) {
                witnessedByPosition.put(candidate.summaryPcIndex(),
                        candidate);
            }
        }
        for (int index = 0; index < targetPosition; index++) {
            SummaryBranchMapping prefix = witnessedByPosition.get(index);
            if (prefix == null) {
                component(value, "AUXILIARY_PC");
                component(value, CanonicalJson.render(
                        LocalCaseIdentity.staticConditionToken(
                                pathCondition.get(index))));
            } else {
                appendControl(value, "ORDERED_PC", prefix);
            }
        }

        for (SummaryBranchMapping prefix : branchMappings) {
            if (prefix.decisionIdentity().equals(
                    mapping.decisionIdentity())) {
                break;
            }
            if (prefix.isConcreteObservation()
                    || !prefix.witness().isPcPredicateDecision()) {
                appendControl(value, "RUNTIME_PREFIX", prefix);
            }
        }

        component(value, mapping.siteId());
        component(value, String.valueOf(mapping.occurrence()));
        component(value, String.valueOf(mapping.decisionOrdinal()));
        component(value, String.valueOf(desiredOutcome));
        return CanonicalJson.sha256(value.toString());
    }

    private static void appendControl(StringBuilder value, String kind,
                                      SummaryBranchMapping mapping) {
        component(value, kind);
        component(value, mapping.siteId());
        component(value, String.valueOf(mapping.occurrence()));
        component(value, String.valueOf(mapping.decisionOrdinal()));
        component(value, mapping.exactDecisionToken());
    }

    public JsonObject replayPayload() { return raw; }
    public static final class Scope {
        private final ClosureGoalKind goalKind;
        private final String goalId;
        private final LoopBoundPolicy loopBound;
        private final Set<String> branchSites;
        private final String identity;

        private Scope(ClosureGoalKind goalKind, String goalId,
                      LoopBoundPolicy loopBound,
                      Set<String> branchSites, String identity) {
            this.goalKind = goalKind;
            this.goalId = goalId;
            this.loopBound = loopBound;
            this.branchSites = Collections.unmodifiableSet(branchSites);
            this.identity = identity;
        }

        public static Scope decode(JsonObject summary, JsonObject task) {
            JsonObject canonical = summary != null ? summary : task;
            if (canonical == null) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            ClosureGoalKind goalKind = ClosureGoalKind.fromTask(canonical);
            String goalId = optionalString(canonical, "goalId");
            if (goalId.isEmpty()) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            JsonObject loopBoundSource = canonical.has(
                    LoopBoundPolicy.FIELD) ? canonical : task;
            LoopBoundPolicy loopBound = LoopBoundPolicy.decode(
                    loopBoundSource);
            JsonObject source = task != null ? task : canonical;
            Set<String> sites = new TreeSet<>();
            for (JsonElement element : array(source, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!"EXPLORE".equals(optionalString(branch, "policy"))) continue;
                String site = optionalString(branch, "siteId");
                if (!site.isEmpty()) sites.add(site);
            }
            String region = firstNonBlank(optionalString(source, "regionId"),
                    optionalString(canonical, "regionId"));
            String occurrence = firstNonBlank(optionalString(source,
                    "occurrenceId"), optionalString(canonical, "occurrenceId"));
            String targetMethod = optionalString(source, "targetMethod");
            String kind = goalKind.capturesTargetReach()
                    ? "TARGET_REACH_CLOSURE_V2"
                    : "REGION_PATH_CLOSURE_V1";
            return new Scope(goalKind, goalId, loopBound, sites,
                    kind + "\n" + goalId + "\n" + region + "\n"
                            + occurrence + "\n" + targetMethod + "\n"
                            + String.join("\n", sites) + "\n"
                            + loopBound.identity());
        }

        public ClosureGoalKind goalKind() { return goalKind; }
        public String goalId() { return goalId; }
        public LoopBoundPolicy loopBound() { return loopBound; }
        public Set<String> branchSites() { return branchSites; }
        public String identity() { return identity; }
    }

    private static void component(StringBuilder output, String value) {
        String safe = value == null ? "" : value;
        output.append(safe.length()).append(':').append(safe).append('|');
    }

}
