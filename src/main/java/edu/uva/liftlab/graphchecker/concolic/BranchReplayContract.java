package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.primitiveString;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.requiredObject;

/** Immutable natural replay request derived from one source branch witness. */
public final class BranchReplayContract {
    public static final int SCHEMA_VERSION = 2;
    public static final String KIND = "BINARY_BRANCH_REPLAY_CONTRACT";

    private final List<BranchWitness> orderedPrefix;
    private final BranchWitness source;
    private final SolverPathContext solverPathContext;

    private BranchReplayContract(List<BranchWitness> orderedPrefix,
                                 BranchWitness source,
                                 SolverPathContext solverPathContext) {
        if (source == null) {
            throw new IllegalArgumentException("source witness is required");
        }
        if (orderedPrefix == null) {
            throw new IllegalArgumentException("ordered prefix is required");
        }
        List<BranchWitness> prefixCopy = new ArrayList<>(orderedPrefix);
        Set<String> events = new LinkedHashSet<>();
        for (BranchWitness witness : prefixCopy) {
            if (witness == null || !events.add(eventIdentity(witness))) {
                throw new IllegalArgumentException(
                        "ordered prefix contains a missing or duplicate event");
            }
        }
        if (!events.add(eventIdentity(source))) {
            throw new IllegalArgumentException(
                    "source branch event must not appear in ordered prefix");
        }
        this.orderedPrefix = Collections.unmodifiableList(prefixCopy);
        this.source = source;
        this.solverPathContext = solverPathContext;
    }

    /** The only operation in the protocol that derives opposite polarity. */
    public static BranchReplayContract flip(List<BranchWitness> orderedPrefix,
                                            BranchWitness source) {
        return new BranchReplayContract(orderedPrefix, source, null);
    }

    public static BranchReplayContract fromSummary(
            JsonObject summary, String siteId, int occurrence) {
        List<SummaryBranchMapping> mappings =
                SummaryBranchMapping.fromSummary(summary);
        for (SummaryBranchMapping mapping : mappings) {
            if (siteId.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()) {
                return fromSummary(summary, mappings, mapping);
            }
        }
        throw new IllegalArgumentException("target branch mapping is missing");
    }

    static BranchReplayContract fromSummary(
            JsonObject summary, List<SummaryBranchMapping> mappings,
            SummaryBranchMapping selected) {
        if (selected == null || !selected.isWitnessed()) {
            throw new IllegalArgumentException(
                    "target branch has no immutable witness");
        }
        int targetPosition = selected.summaryPcIndex();
        Map<Integer, BranchWitness> prefixByPosition = new TreeMap<>();
        for (SummaryBranchMapping mapping : mappings) {
            if (mapping.isWitnessed()
                    && mapping.summaryPcIndex() < targetPosition) {
                prefixByPosition.put(mapping.summaryPcIndex(),
                        mapping.witness());
            }
        }
        SolverPathContext context = SolverPathContext.fromPath(
                summary.getAsJsonArray("pathCondition"),
                prefixByPosition.keySet(),
                targetPosition);
        return new BranchReplayContract(
                new ArrayList<>(prefixByPosition.values()),
                selected.witness(), context);
    }

    public static BranchReplayContract fromJson(JsonObject json) {
        if (primitiveInteger(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(primitiveString(json, "kind"))) {
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
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        JsonArray prefix = new JsonArray();
        for (BranchWitness witness : orderedPrefix) {
            prefix.add(witness.toJson());
        }
        result.add("orderedPrefix", prefix);
        result.add("source", source.toJson());
        return (JsonObject) CanonicalJson.copy(result);
    }

    public void addTo(JsonObject target) {
        if (solverPathContext == null) {
            throw new IllegalStateException(
                    "solver context is unavailable for parsed contract");
        }
        target.add("replayContract", toJson());
        target.add("solverPathContext", solverPathContext.toJson());
    }

    public List<BranchWitness> orderedPrefix() {
        return orderedPrefix;
    }

    public BranchWitness source() {
        return source;
    }

    public boolean requiredTakenOutcome() {
        return !source.sourceTakenOutcome();
    }

    public JsonElement requiredSatisfiedPredicate() {
        return BranchPredicateAlgebra.complement(
                source.sourceSatisfiedPredicate());
    }

    public JsonArray requiredPathPredicates() {
        JsonArray result = new JsonArray();
        for (BranchWitness witness : orderedPrefix) {
            result.add(witness.sourceSatisfiedPredicate());
        }
        result.add(requiredSatisfiedPredicate());
        return result;
    }

    private static String eventIdentity(BranchWitness witness) {
        return witness.decisionIdentity();
    }

}
