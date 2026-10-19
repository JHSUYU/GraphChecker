package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Map;

public final class BranchWitness {
    private static final String PREDICATE = "sourceSatisfiedPredicate";

    private final JsonElement sourceSatisfiedPredicate;

    private BranchWitness(JsonElement sourceSatisfiedPredicate,
                          Map<JsonElement, JsonElement> views) {
        if (sourceSatisfiedPredicate == null
                || sourceSatisfiedPredicate.isJsonNull()) {
            throw new IllegalArgumentException(
                    "sourceSatisfiedPredicate is required");
        }
        this.sourceSatisfiedPredicate = BranchPredicateAlgebra.canonicalView(
                sourceSatisfiedPredicate, views);
    }

    public static BranchWitness immutablePredicate(
            JsonElement predicate, Map<JsonElement, JsonElement> views) {
        return new BranchWitness(predicate, views);
    }

    public JsonObject toImmutableJsonView() {
        JsonObject result = new JsonObject();
        result.add(PREDICATE, sourceSatisfiedPredicate);
        return result;
    }
}
