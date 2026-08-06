package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Canonical fixed bounds for bounded concolic execution. */
public final class LoopBoundPolicy {
    public static final String FIELD = "loopBound";
    /** No {@code for}, {@code while}, or {@code do-while} body may run more. */
    public static final int MAX_LOOP_BODY_ITERATIONS = 8;
    /** Maximum failure-relevant cells retained for one symbolic container. */
    public static final int SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY = 8;
    // A guarded body-entry hook denies body nine after eight bodies have run.
    // The encoded field name is historical; the value is a body bound.
    private static final int SCHEMA_VERSION = 1;
    private static final String KIND = "CFG_BACKEDGE";
    private static final String SCOPE = "ALL_EXECUTION_SCOPE_LOOPS";
    private static final String ON_LIMIT = "CUT_PATH";

    private final int maxBackedgeTraversals;

    private LoopBoundPolicy(int maxBackedgeTraversals) {
        if (maxBackedgeTraversals != MAX_LOOP_BODY_ITERATIONS) {
            throw new IllegalArgumentException(
                    "loop body bound is fixed at "
                            + MAX_LOOP_BODY_ITERATIONS + " iterations");
        }
        this.maxBackedgeTraversals = maxBackedgeTraversals;
    }

    public static LoopBoundPolicy cfgBackedges(int maxTraversals) {
        return new LoopBoundPolicy(maxTraversals);
    }

    public static LoopBoundPolicy decode(JsonObject owner) {
        JsonElement raw = owner == null ? null : owner.get(FIELD);
        if (raw == null || !raw.isJsonObject()) {
            throw new IllegalArgumentException(
                    "execution task requires a loopBound contract");
        }
        JsonObject encoded = raw.getAsJsonObject();
        if (integer(encoded, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(encoded, "kind"))
                || !SCOPE.equals(string(encoded, "scope"))
                || !ON_LIMIT.equals(string(encoded, "onLimit"))) {
            throw new IllegalArgumentException(
                    "unsupported loopBound contract");
        }
        return cfgBackedges(integer(encoded,
                "maxBackedgeTraversals", -1));
    }

    public int maxBackedgeTraversals() {
        return maxBackedgeTraversals;
    }

    public String identity() {
        return KIND + ':' + maxBackedgeTraversals + ':' + ON_LIMIT;
    }

    public JsonObject toJson() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("schemaVersion", SCHEMA_VERSION);
        encoded.addProperty("kind", KIND);
        encoded.addProperty("scope", SCOPE);
        encoded.addProperty("maxBackedgeTraversals",
                maxBackedgeTraversals);
        encoded.addProperty("onLimit", ON_LIMIT);
        return encoded;
    }

    public void writeTo(JsonObject owner) {
        owner.add(FIELD, toJson());
    }
}
