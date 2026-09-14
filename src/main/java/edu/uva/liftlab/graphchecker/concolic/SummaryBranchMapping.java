package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredArray;

/**
 * Canonical typed branch row stored in a concolic summary.
 *
 * <p>A witnessed row contains only the immutable runtime witness, its one
 * summary-PC position, and scheduling policy.  A concrete row contains only
 * an immutable no-PC observation and policy.  All runtime protocol detail is
 * deliberately excluded from this summary boundary.</p>
 */
public final class SummaryBranchMapping {
    public enum Policy {
        EXPLORE,
        PATH_ASSUMPTION;

        public static Policy fromWire(String value) {
            try {
                return Policy.valueOf(value == null ? "" : value);
            } catch (IllegalArgumentException unsupported) {
                throw new IllegalArgumentException(
                        "unsupported branch policy: " + value);
            }
        }

        private static Policy parse(JsonObject json) {
            JsonElement encoded = json == null ? null : json.get("policy");
            if (encoded == null || !encoded.isJsonPrimitive()
                    || !encoded.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(
                        "branch policy must be a string");
            }
            return fromWire(encoded.getAsString());
        }
    }

    private final BranchWitness witness;
    private final ExactConcreteBranchObservation concreteObservation;
    private final int summaryPcIndex;
    private final Policy policy;
    /**
     * The session event sequence this decision was recorded at, or {@code 0}.
     *
     * <p>The one clock the whole replay is read on, and the same counter
     * that numbers field versions, reads and wire events -- so a composer
     * can ask which write of a field was live when this decision read it.
     * It rides the row rather than the witness because a concrete
     * observation is a decision too.  It is stated only when the VM assigned
     * one; a zero would order it ahead of everything the VM did number.</p>
     */
    /**
     * The member a branch decision publishes its VM event under.
     *
     * <p>Defined here, by the row that writes it: it used to be a constant on
     * the in-session read resolver, which is a reader of a different kind of
     * row entirely.</p>
     */
    public static final String SESSION_EVENT_ID = "eventId";

    private final long eventId;

    private SummaryBranchMapping(
            BranchWitness witness,
            ExactConcreteBranchObservation concreteObservation,
            int summaryPcIndex, Policy policy) {
        this(witness, concreteObservation, summaryPcIndex, policy, 0L);
    }

    private SummaryBranchMapping(
            BranchWitness witness,
            ExactConcreteBranchObservation concreteObservation,
            int summaryPcIndex, Policy policy, long eventId) {
        if ((witness == null) == (concreteObservation == null)) {
            throw new IllegalArgumentException(
                    "exactly one branch authority is required");
        }
        if (witness != null && summaryPcIndex < 0) {
            throw new IllegalArgumentException(
                    "summaryPcIndex must be nonnegative");
        }
        if (concreteObservation != null && summaryPcIndex != -1) {
            throw new IllegalArgumentException(
                    "a concrete observation has no summary PC");
        }
        if (policy == null) {
            throw new IllegalArgumentException("branch policy is required");
        }
        this.witness = witness;
        this.concreteObservation = concreteObservation;
        this.summaryPcIndex = summaryPcIndex;
        this.policy = policy;
        this.eventId = eventId;
    }

    /** The session event this decision was recorded at, or 0. */
    public long eventId() { return eventId; }

    /** The same decision, read on the replay's clock. */
    public SummaryBranchMapping at(long clock) {
        return clock == eventId ? this : new SummaryBranchMapping(
                witness, concreteObservation, summaryPcIndex, policy, clock);
    }

    public static SummaryBranchMapping witnessed(
            BranchWitness witness, int summaryPcIndex, Policy policy) {
        if (witness == null) {
            throw new IllegalArgumentException("branch witness is required");
        }
        return new SummaryBranchMapping(witness, null, summaryPcIndex,
                policy);
    }

    public static SummaryBranchMapping concrete(
            ExactConcreteBranchObservation observation, Policy policy) {
        if (observation == null) {
            throw new IllegalArgumentException(
                    "exact concrete branch observation is required");
        }
        return new SummaryBranchMapping(null, observation, -1, policy);
    }

    /** Decoder-owned view used while importing a shared expression DAG. */
    static SummaryBranchMapping fromImmutableJson(JsonObject json) {
        return fromJson(json, true);
    }

    private static SummaryBranchMapping fromJson(JsonObject json,
                                                 boolean immutablePredicate) {
        if (json == null) {
            throw new IllegalArgumentException(
                    "summary branch mapping is required");
        }
        boolean hasWitness = json.has("witness");
        boolean hasObservation = json.has("concreteObservation");
        if (hasWitness == hasObservation) {
            throw new IllegalArgumentException(
                    "summary branch mapping must have exactly one authority");
        }
        Policy policy = Policy.parse(json);
        if (hasWitness) {
            JsonElement encoded = json.get("witness");
            if (encoded == null || !encoded.isJsonObject()) {
                throw new IllegalArgumentException(
                        "witness must be an object");
            }
            BranchWitness witness = immutablePredicate
                    ? BranchWitness.fromImmutableJson(
                    encoded.getAsJsonObject())
                    : BranchWitness.fromJson(encoded.getAsJsonObject());
            return witnessed(witness,
                    integer(json, "summaryPcIndex"), policy)
                    .at(clock(json));
        }
        JsonElement encoded = json.get("concreteObservation");
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "concreteObservation must be an object");
        }
        return concrete(ExactConcreteBranchObservation.fromJson(
                encoded.getAsJsonObject()), policy).at(clock(json));
    }

    /** The replay clock this row states, or 0 when it states none. */
    private static long clock(JsonObject json) {
        JsonElement encoded = json.get(SESSION_EVENT_ID);
        if (encoded == null || encoded.isJsonNull()) return 0L;
        if (!encoded.isJsonPrimitive()
                || !encoded.getAsJsonPrimitive().isNumber()) {
            throw new IllegalArgumentException(
                    SESSION_EVENT_ID + " must be a number");
        }
        long value = encoded.getAsLong();
        if (value <= 0L) {
            throw new IllegalArgumentException(
                    SESSION_EVENT_ID + " must be positive");
        }
        return value;
    }

    /**
     * Strictly parses and validates every canonical row in one summary.
     * Malformed rows invalidate the whole collection so a replay prefix can
     * never be built after silently dropping evidence.
     */
    public static List<SummaryBranchMapping> fromSummary(
            JsonObject summary) {
        JsonArray path = requiredArray(summary, "pathCondition");
        JsonArray encoded = requiredArray(summary, "branchMappings");
        List<SummaryBranchMapping> result = new ArrayList<>();
        Set<Integer> positions = new LinkedHashSet<>();
        Set<String> events = new LinkedHashSet<>();
        int ordinal = 0;
        for (JsonElement element : encoded) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "branchMappings[" + ordinal
                                + "] must be an object");
            }
            SummaryBranchMapping mapping;
            try {
                mapping = fromJson(element.getAsJsonObject(), true);
            } catch (IllegalArgumentException malformed) {
                throw new IllegalArgumentException(
                        "branchMappings[" + ordinal + "]: "
                                + malformed.getMessage(), malformed);
            }
            String event = mapping.decisionIdentity();
            if (!events.add(event)) {
                throw new IllegalArgumentException(
                        "duplicate branch event " + mapping.siteId() + "#"
                                + mapping.occurrence());
            }
            if (mapping.isWitnessed()) {
                int position = mapping.summaryPcIndex();
                if (position >= path.size()
                        || !positions.add(position)
                        || !BranchPredicateAlgebra.equivalent(
                        mapping.witness().sourceSatisfiedPredicateView(),
                        path.get(position))) {
                    throw new IllegalArgumentException(
                            "branch witness does not own summary PC "
                                    + position);
                }
            }
            result.add(mapping);
            ordinal++;
        }
        return Collections.unmodifiableList(result);
    }

    public JsonObject toJson() {
        return toJson(true);
    }

    /** Artifact-builder view which preserves decoder-owned expression DAGs. */
    JsonObject toImmutableJsonView() {
        return toJson(false);
    }

    private JsonObject toJson(boolean defensivePredicate) {
        JsonObject result = new JsonObject();
        if (isWitnessed()) {
            result.add("witness", defensivePredicate
                    ? witness.toJson() : witness.toImmutableJsonView());
            result.addProperty("summaryPcIndex", summaryPcIndex);
        } else {
            result.add("concreteObservation",
                    concreteObservation.toJson());
        }
        result.addProperty("policy", policy.name());
        if (eventId > 0L) {
            result.addProperty(SESSION_EVENT_ID, eventId);
        }
        return defensivePredicate
                ? (JsonObject) CanonicalJson.copy(result) : result;
    }

    public boolean isWitnessed() { return witness != null; }

    public boolean isConcreteObservation() {
        return concreteObservation != null;
    }

    public BranchWitness witness() { return witness; }

    public ExactConcreteBranchObservation concreteObservation() {
        return concreteObservation;
    }

    public int summaryPcIndex() { return summaryPcIndex; }

    public Policy policy() { return policy; }

    public boolean isExplore() { return policy == Policy.EXPLORE; }

    public String siteId() {
        return witness != null
                ? witness.siteId() : concreteObservation.siteId();
    }

    public int occurrence() {
        return witness != null
                ? witness.occurrence() : concreteObservation.occurrence();
    }

    public boolean sourceTakenOutcome() {
        return witness != null
                ? witness.sourceTakenOutcome()
                : concreteObservation.sourceTakenOutcome();
    }

    /** Exact observed decision, including a switch's selected successor. */
    public String exactDecisionToken() {
        return witness != null
                ? ExactConcreteBranchObservation.binaryDecisionToken(
                witness.sourceTakenOutcome())
                : concreteObservation.exactDecisionToken();
    }

    public int decisionOrdinal() {
        return witness == null ? 0 : witness.decisionOrdinal();
    }

    public String decisionIdentity() {
        return witness == null
                ? siteId() + "\u0000" + occurrence() + "\u0000" + 0
                : witness.decisionIdentity();
    }

    private static int integer(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            throw new IllegalArgumentException(name + " must be an integer");
        }
        try {
            return new BigDecimal(value.getAsString()).intValueExact();
        } catch (RuntimeException malformed) {
            throw new IllegalArgumentException(
                    name + " must be an integer", malformed);
        }
    }

}
