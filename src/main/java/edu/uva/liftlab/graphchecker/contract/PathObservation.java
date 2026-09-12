package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.LocalCaseIdentity;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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

    private static String exactText(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString().trim() : "";
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

    /**
     * OCC-1: the planned address behind one occurrence id.
     *
     * <p>An activation occurrence is named {@code <plannedAddress>#a<ordinal>}.
     * A relation, a target reach query and a region plan are all keyed on the
     * planned address the campaign scheduled, so a match between one of them
     * and a per-activation summary is made on the address, not the activation.
     * A string that carries no activation suffix -- a pre-OCC-1 occurrence --
     * is returned unchanged.</p>
     */
    public static String plannedOccurrenceOf(String occurrenceId) {
        String value = occurrenceId == null ? "" : occurrenceId;
        int marker = value.lastIndexOf("#a");
        if (marker <= 0 || marker + 2 >= value.length()) return value;
        for (int index = marker + 2; index < value.length(); index++) {
            if (!Character.isDigit(value.charAt(index))) return value;
        }
        return value.substring(0, marker);
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
    public JsonArray edgeBindings() {
        return array(raw, "edgeBindings");
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

        private TargetReachEvent(String siteId, int occurrence,
                                 boolean outcome) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.outcome = outcome;
        }

        public static TargetReachEvent decode(JsonElement encoded) {
            if (encoded == null || !encoded.isJsonObject()) {
                throw new IllegalArgumentException(
                        FIELD + " must be an object");
            }
            JsonObject event = encoded.getAsJsonObject();
            if (event.size() != 4
                    || !event.has("kind") || !event.has("siteId")
                    || !event.has("occurrence") || !event.has("outcome")) {
                throw new IllegalArgumentException(
                        FIELD + " must contain exactly kind, siteId, "
                                + "occurrence and outcome");
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
            return new TargetReachEvent(site.getAsString(), occurrence,
                    taken.getAsBoolean());
        }

        public String siteId() { return siteId; }
        public int occurrence() { return occurrence; }
        public boolean outcome() { return outcome; }

        public boolean matches(String site, int ordinal, boolean taken) {
            return siteId.equals(site) && occurrence == ordinal
                    && outcome == taken;
        }

        public JsonObject toJson() {
            JsonObject event = new JsonObject();
            event.addProperty("kind", KIND);
            event.addProperty("siteId", siteId);
            event.addProperty("occurrence", occurrence);
            event.addProperty("outcome", outcome);
            return event;
        }
    }

    /** VM handoffs attached by this path, keyed by stable expression
     *  handles and case-local source anchors. */
    public java.util.List<JsonObject> vmHandoffEvents() {
        return VmHandoffEvidence.eventsOf(raw);
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
