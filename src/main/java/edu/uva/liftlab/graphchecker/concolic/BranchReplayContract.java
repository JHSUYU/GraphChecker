package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/** Immutable natural replay request derived from one source branch witness. */
public final class BranchReplayContract {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BINARY_BRANCH_REPLAY_CONTRACT";
    public static final String DROP_SOURCE_SUFFIX = "DROP_SOURCE_SUFFIX";
    private static final String ID_PREFIX = "BRANCH.REPLAY.";

    private final List<BranchWitness> orderedPrefix;
    private final BranchWitness source;
    private final boolean requiredTakenOutcome;
    private final JsonElement requiredSatisfiedPredicate;
    private final String contractId;

    private BranchReplayContract(List<BranchWitness> orderedPrefix,
                                 BranchWitness source) {
        if (source == null) {
            throw new IllegalArgumentException("source witness is required");
        }
        List<BranchWitness> prefixCopy = new ArrayList<>();
        Set<String> identities = new LinkedHashSet<>();
        Set<String> events = new LinkedHashSet<>();
        if (orderedPrefix != null) {
            for (BranchWitness witness : orderedPrefix) {
                if (witness == null
                        || !identities.add(witness.witnessId())) {
                    throw new IllegalArgumentException(
                            "ordered prefix contains a missing or duplicate witness");
                }
                if (!events.add(eventIdentity(witness))) {
                    throw new IllegalArgumentException(
                            "ordered prefix contains a duplicate branch event");
                }
                prefixCopy.add(witness);
            }
        }
        if (!identities.add(source.witnessId())) {
            throw new IllegalArgumentException(
                    "source witness must not appear in ordered prefix");
        }
        if (!events.add(eventIdentity(source))) {
            throw new IllegalArgumentException(
                    "source branch event must not appear in ordered prefix");
        }
        this.orderedPrefix = Collections.unmodifiableList(prefixCopy);
        this.source = source;
        this.requiredTakenOutcome = !source.sourceTakenOutcome();
        this.requiredSatisfiedPredicate = BranchPredicateAlgebra.complement(
                source.sourceSatisfiedPredicate());
        this.contractId = ID_PREFIX + CanonicalJson.sha256(coreJson());
    }

    /** The only operation in the protocol that derives opposite polarity. */
    public static BranchReplayContract flip(List<BranchWitness> orderedPrefix,
                                            BranchWitness source) {
        return new BranchReplayContract(orderedPrefix, source);
    }

    public static BranchReplayContract fromJson(JsonObject json) {
        requireExactKeys(json, "branch replay contract", "schemaVersion",
                "kind", "contractId", "orderedPrefix", "source",
                "required", "suffixPolicy");
        if (integer(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(json, "kind"))
                || !DROP_SOURCE_SUFFIX.equals(string(json,
                "suffixPolicy"))) {
            throw new IllegalArgumentException(
                    "unsupported binary branch replay contract schema");
        }
        JsonElement prefixElement = json.get("orderedPrefix");
        if (prefixElement == null || !prefixElement.isJsonArray()) {
            throw new IllegalArgumentException(
                    "orderedPrefix must be an array");
        }
        List<BranchWitness> prefix = new ArrayList<>();
        for (JsonElement element : prefixElement.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "orderedPrefix entries must be witnesses");
            }
            prefix.add(BranchWitness.fromJson(element.getAsJsonObject()));
        }
        BranchWitness source = BranchWitness.fromJson(object(json,
                "source"));
        BranchReplayContract result = flip(prefix, source);
        JsonObject required = object(json, "required");
        requireExactKeys(required, "required replay branch", "takenOutcome",
                "satisfiedPredicate");
        JsonElement outcome = required.get("takenOutcome");
        if (outcome == null || !outcome.isJsonPrimitive()
                || !outcome.getAsJsonPrimitive().isBoolean()
                || outcome.getAsBoolean() != result.requiredTakenOutcome
                || !BranchPredicateAlgebra.equivalent(
                required.get("satisfiedPredicate"),
                result.requiredSatisfiedPredicate)) {
            throw new IllegalArgumentException(
                    "required branch is not the exact source-witness flip");
        }
        if (!result.contractId.equals(string(json, "contractId"))) {
            throw new IllegalArgumentException(
                    "branch replay content hash does not match contractId");
        }
        return result;
    }

    public JsonObject toJson() {
        JsonObject result = coreJson();
        result.addProperty("contractId", contractId);
        return (JsonObject) CanonicalJson.copy(result);
    }

    public String contractId() {
        return contractId;
    }

    public List<BranchWitness> orderedPrefix() {
        return orderedPrefix;
    }

    public BranchWitness source() {
        return source;
    }

    public boolean requiredTakenOutcome() {
        return requiredTakenOutcome;
    }

    public JsonElement requiredSatisfiedPredicate() {
        return CanonicalJson.copy(requiredSatisfiedPredicate);
    }

    public JsonArray requiredPathPredicates() {
        JsonArray result = new JsonArray();
        for (BranchWitness witness : orderedPrefix) {
            result.add(witness.sourceSatisfiedPredicate());
        }
        result.add(requiredSatisfiedPredicate());
        return result;
    }

    private JsonObject coreJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        JsonArray prefix = new JsonArray();
        for (BranchWitness witness : orderedPrefix) {
            prefix.add(witness.toJson());
        }
        result.add("orderedPrefix", prefix);
        result.add("source", source.toJson());
        JsonObject required = new JsonObject();
        required.addProperty("takenOutcome", requiredTakenOutcome);
        required.add("satisfiedPredicate",
                CanonicalJson.copy(requiredSatisfiedPredicate));
        result.add("required", required);
        result.addProperty("suffixPolicy", DROP_SOURCE_SUFFIX);
        return (JsonObject) CanonicalJson.copy(result);
    }

    private static String eventIdentity(BranchWitness witness) {
        return witness.siteId() + "\u0000" + witness.occurrence();
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
}
