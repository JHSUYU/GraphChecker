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
    /**
     * Maximum failure-relevant cells retained for one symbolic container.
     *
     * <p>A resource default, not a modeled collection length.  HDFS-11741
     * demands the balancer's {@code DataEncryptionKey.encryptionKey}, and
     * that key is a {@code byte[20]}: the failure is precisely a mismatch of
     * those bytes, so a cap below twenty could only refuse the slice the
     * failure is stated over.</p>
     */
    public static final int SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY = 32;
    /**
     * Maximum number of restartable state transitions composed into one
     * single-writer history.
     *
     * <p>This is deliberately a third ledger.  It is neither the symbolic
     * CFG backedge bound nor the amount of concrete work one replay may do.
     * A VM summary admitted to this history denotes one exact activation-
     * boundary transition; composition may alpha-rename that transition this
     * many times.</p>
     */
    public static final int MAX_STATE_TIMELINE_TRANSITIONS = 8;
    /**
     * Body entries one execution-scope loop may run in one activation before
     * the replay is cut.
     *
     * <p>Independent of {@link #MAX_LOOP_BODY_ITERATIONS}.  The unroll bound
     * caps the <em>path space</em> a solver must reason about, so only a
     * symbolically decided continuation spends it.  This cap answers a
     * different question - how much work one replay may do before it is
     * declared unable to finish - and every loop body spends it, concrete
     * guards included.  A slice loop walks recorded data, so it is given room
     * for the collection sizes a real slice carries.</p>
     */
    public static final int MAX_EXECUTION_SCOPE_LOOP_BODIES = 2048;
    /**
     * Body entries one replay-path loop outside the execution scope may run
     * in one activation before the replay is cut.
     *
     * <p>These are the service loops a long-lived root spins in between the
     * calls the slice is stated over - a heartbeat, a retry, a poll.  Each
     * turn re-enters library code that adds symbolic conditions the replay
     * must then re-read at every later branch, so an unbounded count is what
     * turns a slow activation into one that never ends.  The slice's own
     * calls happen within the first few turns, so tens of them is room.</p>
     */
    public static final int MAX_REPLAY_PATH_LOOP_BODIES = 32;
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

    /**
     * Body entries one loop may run before the replay is cut, given whether
     * the loop's own method belongs to the task's execution scope.
     */
    public static int maxLoopBodies(boolean executionScopeLoop) {
        return executionScopeLoop
                ? MAX_EXECUTION_SCOPE_LOOP_BODIES
                : MAX_REPLAY_PATH_LOOP_BODIES;
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
