package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Canonical execution-wide bound applied to every CFG backedge. */
public final class LoopBoundPolicy {
    public static final String FIELD = "loopBound";
    public static final int DEFAULT_MAX_BACKEDGE_TRAVERSALS = 8;
    private static final int SCHEMA_VERSION = 1;
    private static final String KIND = "CFG_BACKEDGE";
    private static final String SCOPE = "ALL_EXECUTION_SCOPE_LOOPS";
    private static final String ON_LIMIT = "CUT_PATH";

    private final int maxBackedgeTraversals;

    private LoopBoundPolicy(int maxBackedgeTraversals) {
        if (maxBackedgeTraversals < 1) {
            throw new IllegalArgumentException(
                    "loop bound must allow at least one backedge traversal");
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
