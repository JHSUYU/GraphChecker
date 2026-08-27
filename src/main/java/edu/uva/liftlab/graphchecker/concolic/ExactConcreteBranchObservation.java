package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requireText;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.textString;

/**
 * Immutable VM-attested binary branch event that added no symbolic path
 * predicate.
 */
public final class ExactConcreteBranchObservation {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND =
            "EXACT_CONCRETE_BINARY_BRANCH_OBSERVATION";

    private final String siteId;
    private final String method;
    private final int unitIndex;
    private final int occurrence;
    private final boolean sourceTakenOutcome;

    private ExactConcreteBranchObservation(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome) {
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
    }

    /**
     * Creates the authority at the runtime point where exact VM attestation
     * has already succeeded and the binary branch added no symbolic PC.
     */
    public static ExactConcreteBranchObservation attested(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome) {
        return new ExactConcreteBranchObservation(siteId, method, unitIndex,
                occurrence, sourceTakenOutcome);
    }

    public static ExactConcreteBranchObservation fromJson(JsonObject json) {
        if (exactInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(textString(json, "kind"))) {
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
        return new ExactConcreteBranchObservation(
                textString(site, "siteId"), textString(site, "method"),
                exactInteger(site, "unitIndex", -1),
                exactInteger(site, "occurrence", -1),
                outcome.getAsBoolean());
    }

    public JsonObject toJson() {
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
        return (JsonObject) CanonicalJson.copy(result);
    }

    public String siteId() { return siteId; }

    public String method() { return method; }

    public int unitIndex() { return unitIndex; }

    public int occurrence() { return occurrence; }

    public boolean sourceTakenOutcome() { return sourceTakenOutcome; }
}
