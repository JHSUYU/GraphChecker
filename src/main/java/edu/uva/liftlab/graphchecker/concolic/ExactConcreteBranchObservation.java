package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requireText;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.textString;

/**
 * Immutable VM-attested branch event that added no symbolic path predicate.
 * Binary branches retain their original wire schema. A switch observation
 * additionally carries the complete static case-key domain and the exact
 * successor selected by the instrumented edge.
 */
public final class ExactConcreteBranchObservation {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND =
            "EXACT_CONCRETE_BINARY_BRANCH_OBSERVATION";
    public static final String SWITCH_KIND =
            "EXACT_CONCRETE_SWITCH_BRANCH_OBSERVATION";
    public static final String TABLE_SWITCH = "TABLE_SWITCH";
    public static final String LOOKUP_SWITCH = "LOOKUP_SWITCH";

    private final String siteId;
    private final String method;
    private final int unitIndex;
    private final int occurrence;
    private final boolean sourceTakenOutcome;
    private final String branchKind;
    private final List<Integer> caseKeys;
    private final int observedSuccessorIndex;

    private ExactConcreteBranchObservation(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome, String branchKind,
            List<Integer> caseKeys, int observedSuccessorIndex) {
        this.siteId = requireText(siteId, "siteId");
        this.method = requireText(method, "method");
        if (unitIndex < 0) {
            throw new IllegalArgumentException("unitIndex must be nonnegative");
        }
        if (occurrence <= 0) {
            throw new IllegalArgumentException("occurrence must be positive");
        }
        this.unitIndex = unitIndex;
        this.occurrence = occurrence;
        this.sourceTakenOutcome = sourceTakenOutcome;
        this.branchKind = branchKind == null ? "" : branchKind;
        this.caseKeys = Collections.unmodifiableList(
                new ArrayList<>(caseKeys == null
                        ? Collections.<Integer>emptyList() : caseKeys));
        this.observedSuccessorIndex = observedSuccessorIndex;
        if (this.branchKind.isEmpty()) {
            if (!this.caseKeys.isEmpty() || observedSuccessorIndex != -1) {
                throw new IllegalArgumentException(
                        "binary observation cannot carry switch evidence");
            }
        } else {
            validateSwitchDecision(this.branchKind, this.caseKeys,
                    observedSuccessorIndex);
            if (sourceTakenOutcome
                    != (observedSuccessorIndex < this.caseKeys.size())) {
                throw new IllegalArgumentException(
                        "switch outcome differs from exact successor");
            }
        }
    }

    /**
     * Creates the authority at the runtime point where exact VM attestation
     * has already succeeded and the binary branch added no symbolic PC.
     */
    public static ExactConcreteBranchObservation attested(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome) {
        return new ExactConcreteBranchObservation(siteId, method, unitIndex,
                occurrence, sourceTakenOutcome, "",
                Collections.<Integer>emptyList(), -1);
    }

    /** Creates an exact conditionless switch observation after VM/static
     * attestation has validated the switch shape and selected edge. */
    public static ExactConcreteBranchObservation attestedSwitch(
            String siteId, String method, int unitIndex, int occurrence,
            String branchKind, List<Integer> caseKeys,
            int observedSuccessorIndex) {
        int caseCount = caseKeys == null ? 0 : caseKeys.size();
        return new ExactConcreteBranchObservation(siteId, method, unitIndex,
                occurrence, observedSuccessorIndex < caseCount, branchKind,
                caseKeys, observedSuccessorIndex);
    }

    public static ExactConcreteBranchObservation fromJson(JsonObject json) {
        String kind = textString(json, "kind");
        if (exactInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !(KIND.equals(kind) || SWITCH_KIND.equals(kind))) {
            throw new IllegalArgumentException(
                    "unsupported exact concrete branch observation schema");
        }
        JsonObject site = requiredObject(json, "site");
        JsonElement outcome = json.get("sourceTakenOutcome");
        if (outcome == null || !outcome.isJsonPrimitive()
                || !outcome.getAsJsonPrimitive().isBoolean()) {
            throw new IllegalArgumentException(
                    "sourceTakenOutcome must be Boolean");
        }
        String siteId = textString(site, "siteId");
        String method = textString(site, "method");
        int unitIndex = exactInteger(site, "unitIndex", -1);
        int occurrence = exactInteger(site, "occurrence", -1);
        if (KIND.equals(kind)) {
            if (json.has("branchKind") || json.has("caseKeys")
                    || json.has("observedSuccessorIndex")) {
                throw new IllegalArgumentException(
                        "binary observation carries switch evidence");
            }
            return attested(siteId, method, unitIndex, occurrence,
                    outcome.getAsBoolean());
        }
        List<Integer> caseKeys = exactCaseKeys(json.get("caseKeys"));
        ExactConcreteBranchObservation result = attestedSwitch(
                siteId, method, unitIndex, occurrence,
                textString(json, "branchKind"), caseKeys,
                exactInteger(json, "observedSuccessorIndex", -1));
        if (result.sourceTakenOutcome != outcome.getAsBoolean()) {
            throw new IllegalArgumentException(
                    "switch outcome differs from exact successor");
        }
        return result;
    }

    public JsonObject toJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", isSwitchObservation() ? SWITCH_KIND : KIND);
        JsonObject site = new JsonObject();
        site.addProperty("siteId", siteId);
        site.addProperty("method", method);
        site.addProperty("unitIndex", unitIndex);
        site.addProperty("occurrence", occurrence);
        result.add("site", site);
        result.addProperty("sourceTakenOutcome", sourceTakenOutcome);
        if (isSwitchObservation()) {
            result.addProperty("branchKind", branchKind);
            JsonArray keys = new JsonArray();
            for (Integer key : caseKeys) keys.add(key);
            result.add("caseKeys", keys);
            result.addProperty("observedSuccessorIndex",
                    observedSuccessorIndex);
        }
        return (JsonObject) CanonicalJson.copy(result);
    }

    public String siteId() { return siteId; }

    public String method() { return method; }

    public int unitIndex() { return unitIndex; }

    public int occurrence() { return occurrence; }

    public boolean sourceTakenOutcome() { return sourceTakenOutcome; }

    public boolean isSwitchObservation() { return !branchKind.isEmpty(); }

    /** More than one case edge cannot be identified by case-vs-default. */
    public boolean isMultiwaySwitch() {
        return isSwitchObservation() && caseKeys.size() > 1;
    }

    public String branchKind() { return branchKind; }

    public List<Integer> caseKeys() { return caseKeys; }

    public int observedSuccessorIndex() { return observedSuccessorIndex; }

    /** Exact decision token used when comparing one observed execution. */
    public String exactDecisionToken() {
        return isSwitchObservation()
                ? switchDecisionToken(branchKind, caseKeys,
                observedSuccessorIndex)
                : binaryDecisionToken(sourceTakenOutcome);
    }

    public boolean sameDecision(ExactConcreteBranchObservation other) {
        return other != null && siteId.equals(other.siteId)
                && occurrence == other.occurrence
                && exactDecisionToken().equals(other.exactDecisionToken());
    }

    public static String binaryDecisionToken(boolean outcome) {
        JsonObject token = new JsonObject();
        token.addProperty("branchKind", "BINARY");
        token.addProperty("sourceTakenOutcome", outcome);
        return CanonicalJson.render(token);
    }

    public static String switchDecisionToken(
            String branchKind, List<Integer> caseKeys,
            int observedSuccessorIndex) {
        validateSwitchDecision(branchKind, caseKeys,
                observedSuccessorIndex);
        JsonObject token = new JsonObject();
        token.addProperty("branchKind", branchKind);
        JsonArray keys = new JsonArray();
        for (Integer key : caseKeys) keys.add(key);
        token.add("caseKeys", keys);
        token.addProperty("observedSuccessorIndex",
                observedSuccessorIndex);
        return CanonicalJson.render(token);
    }

    static List<Integer> exactCaseKeys(JsonElement encoded) {
        if (encoded == null || !encoded.isJsonArray()) {
            throw new IllegalArgumentException("caseKeys must be an array");
        }
        List<Integer> result = new ArrayList<>();
        int index = 0;
        for (JsonElement key : encoded.getAsJsonArray()) {
            if (key == null || !key.isJsonPrimitive()
                    || !key.getAsJsonPrimitive().isNumber()) {
                throw new IllegalArgumentException(
                        "caseKeys[" + index + "] must be an integer");
            }
            try {
                result.add(new BigDecimal(key.getAsString()).intValueExact());
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        "caseKeys[" + index + "] must be an integer",
                        malformed);
            }
            index++;
        }
        return result;
    }

    private static void validateSwitchDecision(
            String branchKind, List<Integer> caseKeys,
            int observedSuccessorIndex) {
        if (!(TABLE_SWITCH.equals(branchKind)
                || LOOKUP_SWITCH.equals(branchKind))) {
            throw new IllegalArgumentException(
                    "unsupported switch branchKind: " + branchKind);
        }
        if (caseKeys == null || caseKeys.isEmpty()) {
            throw new IllegalArgumentException(
                    "switch case-key domain must be nonempty");
        }
        if (observedSuccessorIndex < 0
                || observedSuccessorIndex > caseKeys.size()) {
            throw new IllegalArgumentException(
                    "observedSuccessorIndex is outside switch domain");
        }
        for (Integer key : caseKeys) {
            if (key == null) {
                throw new IllegalArgumentException(
                        "switch case-key domain contains null");
            }
        }
        if (TABLE_SWITCH.equals(branchKind)) {
            for (int index = 1; index < caseKeys.size(); index++) {
                if ((long) caseKeys.get(index - 1) + 1L
                        != (long) caseKeys.get(index)) {
                    throw new IllegalArgumentException(
                            "tableswitch keys are not dense/ordered");
                }
            }
        } else {
            Set<Integer> distinct = new LinkedHashSet<>(caseKeys);
            if (distinct.size() != caseKeys.size()) {
                throw new IllegalArgumentException(
                        "lookupswitch keys are not unique");
            }
        }
    }
}
