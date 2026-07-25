package edu.uva.liftlab.graphchecker.concolic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Validates one observed witness stream against one immutable replay contract. */
public final class BranchReplayObservationValidator {
    private BranchReplayObservationValidator() {
    }

    public static Result validate(BranchReplayContract contract,
                                  List<BranchWitness> observed) {
        if (contract == null) {
            return Result.notRequested();
        }
        List<BranchWitness> stream = observed == null
                ? Collections.<BranchWitness>emptyList() : observed;
        List<String> failures = new ArrayList<>();
        int previousPosition = -1;
        for (BranchWitness expected : contract.orderedPrefix()) {
            List<Integer> positions = positions(stream, expected.siteId(),
                    expected.occurrence());
            if (positions.size() != 1) {
                failures.add(expected.siteId() + "#"
                        + expected.occurrence()
                        + ":PREFIX_EVENT_COUNT=" + positions.size());
                continue;
            }
            int position = positions.get(0);
            BranchWitness actual = stream.get(position);
            if (position <= previousPosition) {
                failures.add(expected.siteId() + "#"
                        + expected.occurrence() + ":PREFIX_OUT_OF_ORDER");
            }
            if (actual.sourceTakenOutcome()
                    != expected.sourceTakenOutcome()) {
                failures.add(expected.siteId() + "#"
                        + expected.occurrence() + ":PREFIX_OUTCOME_MISMATCH");
            }
            if (!BranchPredicateAlgebra.replayEquivalent(
                    actual.sourceSatisfiedPredicate(),
                    expected.sourceSatisfiedPredicate())) {
                failures.add(expected.siteId() + "#"
                        + expected.occurrence()
                        + ":PREFIX_PREDICATE_MISMATCH");
            }
            previousPosition = position;
        }

        BranchWitness source = contract.source();
        List<Integer> targetPositions = positions(stream, source.siteId(),
                source.occurrence());
        int targetPosition = targetPositions.size() == 1
                ? targetPositions.get(0) : -1;
        if (targetPositions.size() != 1) {
            failures.add(source.siteId() + "#" + source.occurrence()
                    + ":TARGET_EVENT_COUNT=" + targetPositions.size());
        } else {
            BranchWitness target = stream.get(targetPosition);
            if (targetPosition <= previousPosition) {
                failures.add(source.siteId() + "#" + source.occurrence()
                        + ":TARGET_BEFORE_PREFIX");
            }
            if (target.sourceTakenOutcome()
                    != contract.requiredTakenOutcome()) {
                failures.add(source.siteId() + "#" + source.occurrence()
                        + ":TARGET_OUTCOME_MISMATCH");
            }
            if (!BranchPredicateAlgebra.replayEquivalent(
                    target.sourceSatisfiedPredicate(),
                    contract.requiredSatisfiedPredicate())) {
                failures.add(source.siteId() + "#" + source.occurrence()
                        + ":TARGET_PREDICATE_MISMATCH");
            }
        }
        return new Result(failures.isEmpty(), failures);
    }

    private static List<Integer> positions(List<BranchWitness> stream,
                                           String siteId,
                                           int occurrence) {
        List<Integer> result = new ArrayList<>();
        for (int index = 0; index < stream.size(); index++) {
            BranchWitness witness = stream.get(index);
            if (siteId.equals(witness.siteId())
                    && occurrence == witness.occurrence()) {
                result.add(index);
            }
        }
        return result;
    }

    public static final class Result {
        private final boolean valid;
        private final List<String> failures;

        private Result(boolean valid, List<String> failures) {
            this.valid = valid;
            this.failures = Collections.unmodifiableList(
                    new ArrayList<>(failures));
        }

        private static Result notRequested() {
            return new Result(true, Collections.<String>emptyList());
        }

        public boolean valid() {
            return valid;
        }

        public List<String> failures() {
            return failures;
        }
    }
}
