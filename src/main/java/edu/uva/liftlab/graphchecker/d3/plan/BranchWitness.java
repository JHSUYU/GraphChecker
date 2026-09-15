package edu.uva.liftlab.graphchecker.d3.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.primitiveString;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.requireText;

/**
 * Immutable authority for one observed binary branch.
 *
 * <p>A witness owns exactly one satisfied predicate, its VM path-condition
 * index, and the one normalization applied at capture.  An importer that adds
 * a summary path-condition index must place it beside, never inside, this
 * object.</p>
 */
public final class BranchWitness {
    public static final int SCHEMA_VERSION = 2;
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
    private final String symbolicSupportDigest;

    private BranchWitness(String siteId, String method, int unitIndex,
                          int occurrence, boolean sourceTakenOutcome,
                          JsonElement sourceSatisfiedPredicate,
                          int vmPcIndex, String predicateNormalization,
                          int decisionOrdinal, boolean immutablePredicate,
                          String capturedSupportDigest) {
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
        this.sourceSatisfiedPredicate = immutablePredicate
                ? BranchPredicateAlgebra.canonicalView(
                sourceSatisfiedPredicate)
                : BranchPredicateAlgebra.canonical(sourceSatisfiedPredicate);
        this.vmPcIndex = vmPcIndex;
        this.predicateNormalization = predicateNormalization;
        this.decisionOrdinal = decisionOrdinal;
        String captured = capturedSupportDigest == null ? ""
                : capturedSupportDigest.trim();
        if (!captured.isEmpty()
                && !BranchPredicateAlgebra.validSymbolicSupportDigest(
                captured)) {
            throw new IllegalArgumentException(
                    "symbolic support digest is malformed");
        }
        // Capture owns this identity. Offline merging may deliberately widen
        // the expression later; recomputing from that union would lose which
        // concrete loop element produced the witness.
        this.symbolicSupportDigest = captured.isEmpty()
                ? BranchPredicateAlgebra.symbolicSupportDigest(
                this.sourceSatisfiedPredicate) : captured;
    }

    /** Runtime capture path for an immutable decoder-owned predicate DAG. */
    public static BranchWitness vmPcImmutable(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome, JsonElement sourceSatisfiedPredicate,
            int vmPcIndex, JsonObject predicateMetadata) {
        if (vmPcIndex < 0 || predicateMetadata == null) {
            throw new IllegalArgumentException(
                    "VM predicate index and metadata are required");
        }
        String normalization = primitiveString(predicateMetadata,
                "predicateNormalization");
        if (normalization.isEmpty()) normalization = IDENTITY_NORMALIZATION;
        return new BranchWitness(siteId, method, unitIndex, occurrence,
                sourceTakenOutcome, sourceSatisfiedPredicate, vmPcIndex,
                normalization, 0, true, "");
    }

    /**
     * A VM predicate emitted while evaluating one instrumented Jimple branch.
     * It is a solver decision even when the final Jimple boolean has no
     * one-to-one VM branch witness.
     */
    /** Runtime capture path for an immutable decoder-owned switch predicate. */
    public static BranchWitness pcPredicateImmutable(
            String siteId, String method, int unitIndex, int occurrence,
            int decisionOrdinal, JsonElement sourceSatisfiedPredicate,
            int vmPcIndex) {
        if (decisionOrdinal <= 0) {
            throw new IllegalArgumentException(
                    "decisionOrdinal must be positive");
        }
        return new BranchWitness(siteId, method, unitIndex, occurrence,
                true, sourceSatisfiedPredicate, vmPcIndex,
                PC_PREDICATE_NORMALIZATION, decisionOrdinal, true, "");
    }

    /**
     * Runtime artifact view for a predicate obtained from the immutable VM
     * decoder.  Existing public accessors remain defensive; callers of this
     * explicitly named method must preserve the expression-table immutability
     * contract.
     */
    public JsonObject toImmutableJsonView() { return coreJson(false); }

    private JsonObject coreJson(boolean defensivePredicate) {
        JsonObject result = new JsonObject();
        // Insert in canonical key order.  The predicate was canonicalized in
        // the constructor, so another recursive sort here only repeats work
        // on what can be a large propagated container expression.
        if (decisionOrdinal > 0) {
            result.addProperty("decisionOrdinal", decisionOrdinal);
        }
        result.addProperty("kind", KIND);
        result.addProperty("predicateNormalization",
                predicateNormalization);
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        JsonObject site = new JsonObject();
        site.addProperty("method", method);
        site.addProperty("occurrence", occurrence);
        site.addProperty("siteId", siteId);
        site.addProperty("unitIndex", unitIndex);
        result.add("site", site);
        result.add("sourceSatisfiedPredicate", defensivePredicate
                ? BranchPredicateAlgebra.canonical(sourceSatisfiedPredicate)
                : sourceSatisfiedPredicate);
        result.addProperty("sourceTakenOutcome", sourceTakenOutcome);
        if (!symbolicSupportDigest.isEmpty()) {
            result.addProperty("symbolicSupportDigest",
                    symbolicSupportDigest);
        }
        result.addProperty("vmPcIndex", vmPcIndex);
        return result;
    }
}
