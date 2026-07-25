package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Validates one observed witness stream against one immutable replay contract. */
public final class BranchReplayObservationValidator {
    private BranchReplayObservationValidator() {
    }

    static List<String> validateEncoded(JsonElement encoded,
                                        JsonArray rawMappings) {
        if (encoded == null) {
            return Collections.singletonList(
                    "BRANCH_REPLAY_CONTRACT_MISSING");
        }
        if (!encoded.isJsonObject()) {
            return Collections.singletonList("REPLAY_CONTRACT_MALFORMED");
        }
        final BranchReplayContract contract;
        try {
            contract = BranchReplayContract.fromJson(
                    encoded.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            return Collections.singletonList("REPLAY_CONTRACT_MALFORMED:"
                    + malformed.getMessage());
        }
        List<BranchWitness> observed = new ArrayList<>();
        for (JsonElement element : rawMappings) {
            if (!element.isJsonObject()) continue;
            JsonElement witness = element.getAsJsonObject().get("witness");
            if (witness == null || !witness.isJsonObject()) continue;
            try {
                observed.add(BranchWitness.fromJson(
                        witness.getAsJsonObject()));
            } catch (IllegalArgumentException ignored) {
                // Malformed rows cannot satisfy a required replay event.
            }
        }
        List<String> failures = validate(contract, observed);
        List<String> prefixed = new ArrayList<>();
        for (String failure : failures) {
            prefixed.add("BRANCH_REPLAY_CONTRACT:" + failure);
        }
        return prefixed;
    }

    public static List<String> validate(BranchReplayContract contract,
                                        List<BranchWitness> observed) {
        List<String> failures = new ArrayList<>();
        if (contract == null) {
            failures.add("CONTRACT_MISSING");
            return failures;
        }
        List<BranchWitness> stream = observed == null
                ? Collections.<BranchWitness>emptyList() : observed;
        Map<String, Integer> positions = new LinkedHashMap<>();
        Set<String> duplicates = new LinkedHashSet<>();
        for (int index = 0; index < stream.size(); index++) {
            String event = event(stream.get(index));
            if (positions.put(event, index) != null) duplicates.add(event);
        }
        int previousPosition = -1;
        for (BranchWitness expected : contract.orderedPrefix()) {
            previousPosition = validateEvent(expected,
                    expected.sourceTakenOutcome(),
                    expected.sourceSatisfiedPredicate(), previousPosition,
                    true, stream, positions, duplicates, failures);
        }
        BranchWitness source = contract.source();
        validateEvent(source, contract.requiredTakenOutcome(),
                contract.requiredSatisfiedPredicate(), previousPosition,
                false, stream, positions, duplicates, failures);
        return failures;
    }

    private static int validateEvent(
            BranchWitness expected, boolean outcome, JsonElement predicate,
            int previous, boolean prefix, List<BranchWitness> stream,
            Map<String, Integer> positions, Set<String> duplicates,
            List<String> failures) {
        String event = event(expected);
        Integer position = positions.get(event);
        String id = expected.siteId() + "#" + expected.occurrence();
        String role = prefix ? "PREFIX" : "TARGET";
        if (position == null || duplicates.contains(event)) {
            failures.add(id + ":" + role + "_EVENT_NOT_UNIQUE");
            return previous;
        }
        BranchWitness actual = stream.get(position);
        if (position <= previous) {
            failures.add(id + ":" + (prefix
                    ? "PREFIX_OUT_OF_ORDER" : "TARGET_BEFORE_PREFIX"));
        }
        if (actual.sourceTakenOutcome() != outcome) {
            failures.add(id + ":" + role + "_OUTCOME_MISMATCH");
        }
        if (!BranchPredicateAlgebra.replayEquivalent(
                actual.sourceSatisfiedPredicate(), predicate)) {
            failures.add(id + ":" + role + "_PREDICATE_MISMATCH");
        }
        return position;
    }

    private static String event(BranchWitness witness) {
        return witness.siteId() + "\u0000" + witness.occurrence();
    }
}
