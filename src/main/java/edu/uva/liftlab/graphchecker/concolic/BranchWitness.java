package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveString;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requireText;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;

/**
 * Immutable authority for one observed binary branch.
 *
 * <p>A witness owns exactly one satisfied predicate, its VM path-condition
 * index, and the one normalization applied at capture.  An importer that adds
 * a summary path-condition index must place it beside, never inside, this
 * object.</p>
 */
public final class BranchWitness {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BINARY_BRANCH_WITNESS";
    public static final String IDENTITY_NORMALIZATION = "IDENTITY";
    public static final String CMP_NORMALIZATION =
            "JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE";
    public static final String PC_PREDICATE_NORMALIZATION =
            "PC_PREDICATE_IDENTITY";

    private final String siteId;
    private final String method;
    private final int unitIndex;
    private final int occurrence;
    private final boolean sourceTakenOutcome;
    private final JsonElement sourceSatisfiedPredicate;
    private final int vmPcIndex;
    private final String predicateNormalization;
    private final int decisionOrdinal;

    private BranchWitness(String siteId, String method, int unitIndex,
                          int occurrence, boolean sourceTakenOutcome,
                          JsonElement sourceSatisfiedPredicate,
                          int vmPcIndex, String predicateNormalization,
                          int decisionOrdinal) {
        this.siteId = requireText(siteId, "siteId");
        this.method = requireText(method, "method");
        if (unitIndex < 0) {
            throw new IllegalArgumentException("unitIndex must be nonnegative");
        }
        if (occurrence <= 0) {
            throw new IllegalArgumentException("occurrence must be positive");
        }
        if (sourceSatisfiedPredicate == null
                || sourceSatisfiedPredicate.isJsonNull()) {
            throw new IllegalArgumentException(
                    "sourceSatisfiedPredicate is required");
        }
        if (vmPcIndex < 0) {
            throw new IllegalArgumentException("vmPcIndex must be nonnegative");
        }
        if (!IDENTITY_NORMALIZATION.equals(predicateNormalization)
                && !CMP_NORMALIZATION.equals(predicateNormalization)
                && !PC_PREDICATE_NORMALIZATION.equals(
                predicateNormalization)) {
            throw new IllegalArgumentException(
                    "unsupported predicateNormalization: "
                            + predicateNormalization);
        }
        if (decisionOrdinal < 0
                || decisionOrdinal == 0
                && PC_PREDICATE_NORMALIZATION.equals(
                predicateNormalization)
                || decisionOrdinal > 0
                && !PC_PREDICATE_NORMALIZATION.equals(
                predicateNormalization)) {
            throw new IllegalArgumentException(
                    "PC predicate decision ordinal and normalization differ");
        }
        this.unitIndex = unitIndex;
        this.occurrence = occurrence;
        this.sourceTakenOutcome = sourceTakenOutcome;
        this.sourceSatisfiedPredicate = BranchPredicateAlgebra.canonical(
                sourceSatisfiedPredicate);
        this.vmPcIndex = vmPcIndex;
        this.predicateNormalization = predicateNormalization;
        this.decisionOrdinal = decisionOrdinal;
    }

    public static BranchWitness vmPc(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome, JsonElement sourceSatisfiedPredicate,
            int vmPcIndex, JsonObject predicateMetadata) {
        if (vmPcIndex < 0) {
            throw new IllegalArgumentException("vmPcIndex must be nonnegative");
        }
        if (predicateMetadata == null) {
            throw new IllegalArgumentException(
                    "predicateMetadata is required");
        }
        String normalization = primitiveString(predicateMetadata,
                "predicateNormalization");
        if (normalization.isEmpty()) normalization = IDENTITY_NORMALIZATION;
        return new BranchWitness(siteId, method, unitIndex, occurrence,
                sourceTakenOutcome, sourceSatisfiedPredicate, vmPcIndex,
                normalization, 0);
    }

    /**
     * A VM predicate emitted while evaluating one instrumented Jimple branch.
     * It is a solver decision even when the final Jimple boolean has no
     * one-to-one VM branch witness.
     */
    public static BranchWitness pcPredicate(
            String siteId, String method, int unitIndex, int occurrence,
            int decisionOrdinal, JsonElement sourceSatisfiedPredicate,
            int vmPcIndex) {
        if (decisionOrdinal <= 0) {
            throw new IllegalArgumentException(
                    "decisionOrdinal must be positive");
        }
        return new BranchWitness(siteId, method, unitIndex, occurrence,
                true, sourceSatisfiedPredicate, vmPcIndex,
                PC_PREDICATE_NORMALIZATION, decisionOrdinal);
    }

    public static BranchWitness fromJson(JsonObject json) {
        if (primitiveInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(primitiveString(json, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported binary branch witness schema");
        }
        JsonObject site = requiredObject(json, "site");
        JsonElement outcome = json.get("sourceTakenOutcome");
        if (outcome == null || !outcome.isJsonPrimitive()
                || !outcome.getAsJsonPrimitive().isBoolean()) {
            throw new IllegalArgumentException(
                    "sourceTakenOutcome must be Boolean");
        }
        JsonElement predicate = json.get("sourceSatisfiedPredicate");
        return new BranchWitness(primitiveString(site, "siteId"),
                primitiveString(site, "method"),
                primitiveInteger(site, "unitIndex", -1),
                primitiveInteger(site, "occurrence", -1),
                outcome.getAsBoolean(), predicate,
                primitiveInteger(json, "vmPcIndex", -1),
                primitiveString(json, "predicateNormalization"),
                primitiveInteger(json, "decisionOrdinal", 0));
    }

    public JsonObject toJson() { return coreJson(); }

    public String siteId() { return siteId; }

    public String method() { return method; }

    public int unitIndex() { return unitIndex; }

    public int occurrence() { return occurrence; }

    public boolean sourceTakenOutcome() { return sourceTakenOutcome; }

    public JsonElement sourceSatisfiedPredicate() {
        return CanonicalJson.copy(sourceSatisfiedPredicate);
    }

    public int vmPcIndex() { return vmPcIndex; }

    public int decisionOrdinal() { return decisionOrdinal; }

    public boolean isPcPredicateDecision() { return decisionOrdinal > 0; }

    BranchWitness atPcIndex(int pcIndex) {
        return new BranchWitness(siteId, method, unitIndex, occurrence,
                sourceTakenOutcome, sourceSatisfiedPredicate, pcIndex,
                predicateNormalization, decisionOrdinal);
    }

    public String decisionIdentity() {
        return siteId + "\u0000" + occurrence + "\u0000"
                + decisionOrdinal;
    }

    private JsonObject coreJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        JsonObject site = new JsonObject();
        site.addProperty("siteId", siteId);
        site.addProperty("method", method);
        site.addProperty("unitIndex", unitIndex);
        site.addProperty("occurrence", occurrence);
        result.add("site", site);
        result.addProperty("sourceTakenOutcome", sourceTakenOutcome);
        result.add("sourceSatisfiedPredicate",
                CanonicalJson.copy(sourceSatisfiedPredicate));
        result.addProperty("vmPcIndex", vmPcIndex);
        result.addProperty("predicateNormalization",
                predicateNormalization);
        if (decisionOrdinal > 0) {
            result.addProperty("decisionOrdinal", decisionOrdinal);
        }
        return (JsonObject) CanonicalJson.copy(result);
    }
}
