package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveString;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;

/** Immutable natural replay request derived from one source branch witness. */
public final class BranchReplayContract {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BINARY_BRANCH_REPLAY_CONTRACT";
    public static final String DROP_SOURCE_SUFFIX = "DROP_SOURCE_SUFFIX";

    private final List<BranchWitness> orderedPrefix;
    private final BranchWitness source;
    private final boolean requiredTakenOutcome;
    private final JsonElement requiredSatisfiedPredicate;

    private BranchReplayContract(List<BranchWitness> orderedPrefix,
                                 BranchWitness source) {
        if (source == null) {
            throw new IllegalArgumentException("source witness is required");
        }
        List<BranchWitness> prefixCopy = new ArrayList<>();
        Set<String> events = new LinkedHashSet<>();
        if (orderedPrefix != null) {
            for (BranchWitness witness : orderedPrefix) {
                if (witness == null) {
                    throw new IllegalArgumentException(
                            "ordered prefix contains a missing witness");
                }
                if (!events.add(eventIdentity(witness))) {
                    throw new IllegalArgumentException(
                            "ordered prefix contains a duplicate branch event");
                }
                prefixCopy.add(witness);
            }
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
    }

    /** The only operation in the protocol that derives opposite polarity. */
    public static BranchReplayContract flip(List<BranchWitness> orderedPrefix,
                                            BranchWitness source) {
        return new BranchReplayContract(orderedPrefix, source);
    }

    public static BranchReplayContract fromJson(JsonObject json) {
        if (primitiveInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(primitiveString(json, "kind"))
                || !DROP_SOURCE_SUFFIX.equals(primitiveString(json,
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
        BranchWitness source = BranchWitness.fromJson(requiredObject(json,
                "source"));
        return flip(prefix, source);
    }

    public JsonObject toJson() {
        return coreJson();
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

    public boolean sameContent(BranchReplayContract other) {
        if (other == null
                || orderedPrefix.size() != other.orderedPrefix.size()
                || !source.sameContent(other.source)) {
            return false;
        }
        for (int index = 0; index < orderedPrefix.size(); index++) {
            if (!orderedPrefix.get(index).sameContent(
                    other.orderedPrefix.get(index))) {
                return false;
            }
        }
        return true;
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
        result.addProperty("suffixPolicy", DROP_SOURCE_SUFFIX);
        return (JsonObject) CanonicalJson.copy(result);
    }

    private static String eventIdentity(BranchWitness witness) {
        return witness.siteId() + "\u0000" + witness.occurrence();
    }

}
