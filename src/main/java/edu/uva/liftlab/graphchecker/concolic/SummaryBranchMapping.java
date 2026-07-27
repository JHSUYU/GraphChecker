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

    private SummaryBranchMapping(
            BranchWitness witness,
            ExactConcreteBranchObservation concreteObservation,
            int summaryPcIndex, Policy policy) {
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

    public static SummaryBranchMapping fromJson(JsonObject json) {
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
            return witnessed(BranchWitness.fromJson(
                    encoded.getAsJsonObject()),
                    integer(json, "summaryPcIndex"), policy);
        }
        JsonElement encoded = json.get("concreteObservation");
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "concreteObservation must be an object");
        }
        return concrete(ExactConcreteBranchObservation.fromJson(
                encoded.getAsJsonObject()), policy);
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
                mapping = fromJson(element.getAsJsonObject());
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
                        mapping.witness().sourceSatisfiedPredicate(),
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
        JsonObject result = new JsonObject();
        if (isWitnessed()) {
            result.add("witness", witness.toJson());
            result.addProperty("summaryPcIndex", summaryPcIndex);
        } else {
            result.add("concreteObservation",
                    concreteObservation.toJson());
        }
        result.addProperty("policy", policy.name());
        return (JsonObject) CanonicalJson.copy(result);
    }

    public boolean isWitnessed() {
        return witness != null;
    }

    public boolean isConcreteObservation() {
        return concreteObservation != null;
    }

    public BranchWitness witness() {
        return witness;
    }

    public int summaryPcIndex() {
        return summaryPcIndex;
    }

    public Policy policy() {
        return policy;
    }

    public boolean isExplore() {
        return policy == Policy.EXPLORE;
    }

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

    public int decisionOrdinal() {
        return witness == null ? 0 : witness.decisionOrdinal();
    }

    public String decisionIdentity() {
        return witness == null
                ? siteId() + "\u0000" + occurrence() + "\u0000" + 0
                : witness.decisionIdentity();
    }

    private static JsonArray requiredArray(JsonObject parent, String name) {
        JsonElement value = parent == null ? null : parent.get(name);
        if (value == null || !value.isJsonArray()) {
            throw new IllegalArgumentException(name
                    + " must be a JSON array");
        }
        return value.getAsJsonArray();
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
