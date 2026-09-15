package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Immutable authority for the one satisfied predicate of one observed branch.
 *
 * <p>Phi and nothing else.  The decision row this witness travels on already
 * states the site, the occurrence, the VM event and the arm, and a second
 * copy of those inside the witness is a second answer to one question -- it
 * is what {@code RowPublication} joins on (the row's own siteId and
 * occurrence), never what the witness repeats.  Two readers take something
 * from a witness: the target row takes this predicate as the fatal arm's phi,
 * and the session's expression table interns the expressions inside it.</p>
 */
public final class BranchWitness {
    /** The one member a witness publishes. */
    private static final String PREDICATE = "sourceSatisfiedPredicate";

    private final JsonElement sourceSatisfiedPredicate;

    private BranchWitness(JsonElement sourceSatisfiedPredicate) {
        if (sourceSatisfiedPredicate == null
                || sourceSatisfiedPredicate.isJsonNull()) {
            throw new IllegalArgumentException(
                    "sourceSatisfiedPredicate is required");
        }
        this.sourceSatisfiedPredicate = BranchPredicateAlgebra.canonicalView(
                sourceSatisfiedPredicate);
    }

    /**
     * Runtime capture path for an immutable decoder-owned predicate DAG.
     *
     * <p>Copy-on-write: every untouched expression keeps its decoder anchor,
     * which is what lets a propagated container predicate hundreds of nodes
     * deep be captured without being rebuilt.</p>
     */
    public static BranchWitness immutablePredicate(JsonElement predicate) {
        return new BranchWitness(predicate);
    }

    /** The witness as the branch mapping carries it. */
    public JsonObject toImmutableJsonView() {
        JsonObject result = new JsonObject();
        result.add(PREDICATE, sourceSatisfiedPredicate);
        return result;
    }
}
