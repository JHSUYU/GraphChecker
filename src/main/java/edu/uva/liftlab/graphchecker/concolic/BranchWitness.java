package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Immutable authority for one observed binary branch.
 *
 * <p>A witness owns exactly one satisfied predicate and one evidence variant.
 * VM path-condition indices remain in the VM namespace; an importer that adds
 * a summary path-condition index must place it beside, never inside, this
 * object.</p>
 */
public final class BranchWitness {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BINARY_BRANCH_WITNESS";
    public static final String VM_PC = "VM_PC";
    private static final String ID_PREFIX = "BRANCH.WITNESS.";

    private final String siteId;
    private final String method;
    private final int unitIndex;
    private final int occurrence;
    private final boolean sourceTakenOutcome;
    private final JsonElement sourceSatisfiedPredicate;
    private final JsonObject evidence;
    private final String witnessId;

    private BranchWitness(String siteId, String method, int unitIndex,
                          int occurrence, boolean sourceTakenOutcome,
                          JsonElement sourceSatisfiedPredicate,
                          JsonObject evidence) {
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
        this.unitIndex = unitIndex;
        this.occurrence = occurrence;
        this.sourceTakenOutcome = sourceTakenOutcome;
        this.sourceSatisfiedPredicate = BranchPredicateAlgebra.canonical(
                sourceSatisfiedPredicate);
        this.evidence = validateEvidence(evidence);
        this.witnessId = ID_PREFIX + CanonicalJson.sha256(coreJson());
    }

    public static BranchWitness vmPc(
            String siteId, String method, int unitIndex, int occurrence,
            boolean sourceTakenOutcome, JsonElement sourceSatisfiedPredicate,
            int vmPcIndex, JsonObject vmEvent) {
        if (vmPcIndex < 0) {
            throw new IllegalArgumentException("vmPcIndex must be nonnegative");
        }
        if (vmEvent == null || vmEvent.size() == 0) {
            throw new IllegalArgumentException("vmEvent is required");
        }
        JsonObject evidence = new JsonObject();
        evidence.addProperty("kind", VM_PC);
        evidence.addProperty("vmPcIndex", vmPcIndex);
        evidence.add("vmEvent", CanonicalJson.copy(vmEvent));
        return new BranchWitness(siteId, method, unitIndex, occurrence,
                sourceTakenOutcome, sourceSatisfiedPredicate, evidence);
    }

    public static BranchWitness fromJson(JsonObject json) {
        requireExactKeys(json, "branch witness", "schemaVersion", "kind",
                "witnessId", "site", "sourceTakenOutcome",
                "sourceSatisfiedPredicate", "evidence");
        if (integer(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(json, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported binary branch witness schema");
        }
        JsonObject site = object(json, "site");
        requireExactKeys(site, "branch witness site", "siteId", "method",
                "unitIndex", "occurrence");
        JsonElement outcome = json.get("sourceTakenOutcome");
        if (outcome == null || !outcome.isJsonPrimitive()
                || !outcome.getAsJsonPrimitive().isBoolean()) {
            throw new IllegalArgumentException(
                    "sourceTakenOutcome must be Boolean");
        }
        JsonElement predicate = json.get("sourceSatisfiedPredicate");
        JsonObject evidence = object(json, "evidence");
        BranchWitness result = new BranchWitness(string(site, "siteId"),
                string(site, "method"), integer(site, "unitIndex", -1),
                integer(site, "occurrence", -1), outcome.getAsBoolean(),
                predicate, evidence);
        if (!result.witnessId.equals(string(json, "witnessId"))) {
            throw new IllegalArgumentException(
                    "branch witness content hash does not match witnessId");
        }
        return result;
    }

    public static BranchWitness fromMapping(JsonObject mapping) {
        return fromJson(object(mapping, "witness"));
    }

    public JsonObject toJson() {
        JsonObject result = coreJson();
        result.addProperty("witnessId", witnessId);
        return (JsonObject) CanonicalJson.copy(result);
    }

    public String witnessId() {
        return witnessId;
    }

    public String siteId() {
        return siteId;
    }

    public String method() {
        return method;
    }

    public int unitIndex() {
        return unitIndex;
    }

    public int occurrence() {
        return occurrence;
    }

    public boolean sourceTakenOutcome() {
        return sourceTakenOutcome;
    }

    public JsonElement sourceSatisfiedPredicate() {
        return CanonicalJson.copy(sourceSatisfiedPredicate);
    }

    public String evidenceKind() {
        return string(evidence, "kind");
    }

    public int vmPcIndex() {
        return VM_PC.equals(evidenceKind())
                ? integer(evidence, "vmPcIndex", -1) : -1;
    }

    public JsonObject evidence() {
        return (JsonObject) CanonicalJson.copy(evidence);
    }

    public boolean sameBranchEvent(BranchWitness other) {
        return other != null && siteId.equals(other.siteId)
                && occurrence == other.occurrence;
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
        result.add("evidence", CanonicalJson.copy(evidence));
        return (JsonObject) CanonicalJson.copy(result);
    }

    private static JsonObject validateEvidence(JsonObject source) {
        if (source == null) {
            throw new IllegalArgumentException("branch evidence is required");
        }
        String kind = string(source, "kind");
        if (VM_PC.equals(kind)) {
            requireExactKeys(source, "VM_PC evidence", "kind", "vmPcIndex",
                    "vmEvent");
            if (integer(source, "vmPcIndex", -1) < 0
                    || object(source, "vmEvent").size() == 0) {
                throw new IllegalArgumentException(
                        "VM_PC evidence requires an index and event");
            }
        } else {
            throw new IllegalArgumentException(
                    "unknown branch evidence kind: " + kind);
        }
        return (JsonObject) CanonicalJson.copy(source);
    }

    private static void requireExactKeys(JsonObject object, String label,
                                         String... allowed) {
        if (object == null) {
            throw new IllegalArgumentException(label + " is required");
        }
        Set<String> expected = new LinkedHashSet<>(Arrays.asList(allowed));
        Set<String> actual = new LinkedHashSet<>();
        for (java.util.Map.Entry<String, JsonElement> entry
                : object.entrySet()) {
            actual.add(entry.getKey());
        }
        if (!actual.equals(expected)) {
            throw new IllegalArgumentException(label + " keys must be "
                    + expected + " but were " + actual);
        }
    }

    private static JsonObject object(JsonObject parent, String name) {
        JsonElement value = parent == null ? null : parent.get(name);
        if (value == null || !value.isJsonObject()) {
            throw new IllegalArgumentException(name + " must be an object");
        }
        return value.getAsJsonObject();
    }

    private static int integer(JsonObject object, String name,
                               int fallback) {
        JsonElement value = object == null ? null : object.get(name);
        try {
            return value == null || !value.isJsonPrimitive()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    private static String string(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
    }

    private static String requireText(String value, String name) {
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException(name + " is required");
        }
        return value;
    }
}
