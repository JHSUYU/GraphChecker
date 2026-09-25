package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * The one satisfied predicate (phi) of one observed branch, nothing else.
 *
 * <p>Site, occurrence, event and arm live on the decision row; repeating them
 * here would be a second answer. Readers: the target row (fatal arm's phi) and
 * the session expression table.</p>
 */
public final class BranchWitness {
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

    /** Copy-on-write capture: untouched nodes keep their decoder anchor, so
     *  deep predicates are not rebuilt. */
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
