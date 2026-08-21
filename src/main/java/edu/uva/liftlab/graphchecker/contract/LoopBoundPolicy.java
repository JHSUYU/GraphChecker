package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Canonical bounds for bounded concolic execution, and the loop vocabulary
 * every stage states a retained loop with.
 *
 * <p>Loop identity is independent of any communication structure. A retained
 * condition loop declares {@code K_L}; each complete replay case carries its
 * observed body count. A fixed indexed loop instead carries the exact array
 * cardinality of each dynamic occurrence.</p>
 */
public final class LoopBoundPolicy {
    public static final String FIELD = "loopBound";

    // ------------------------------------------------------------------
    // Loop row vocabulary
    // ------------------------------------------------------------------

    /** The retained loop an operation is a body execution of. */
    public static final String LOOP_SITE_ID = "loopSiteId";
    /** Declared {@code K_L} for a retained condition loop. */
    public static final String LOOP_BODY_BOUND = "loopBodyBound";
    /** Which declaration supplied {@code K_L}. */
    public static final String LOOP_BODY_BOUND_AUTHORITY =
            "loopBodyBoundAuthority";
    /** Loop-control branch sites naming the retained loop. */
    public static final String LOOP_CONTROL_SITE_IDS = "loopControlSiteIds";
    /**
     * {@link #LOOP_FIXED_COUNT_INDEXED} or {@link #LOOP_CONDITION_BOUNDED}.
     *
     * <p>Loop kind is plan metadata, not a consumer heuristic.  It is stated
     * where the loop control sites are known and every later stage validates
     * and consumes it.</p>
     */
    public static final String LOOP_CLASSIFICATION = "loopClassification";
    /** Which rule classified the loop. */
    public static final String LOOP_CLASSIFICATION_AUTHORITY =
            "loopClassificationAuthority";
    /**
     * True when a {@link #LOOP_CONDITION_BOUNDED} loop ran a body past
     * {@code K_L}: {@code BOUND_EXHAUSTED(L)} observed.
     */
    public static final String LOOP_BOUND_EXHAUSTED = "loopBoundExhausted";
    /** Path-local loop-count vector imported from one completed replay. */
    public static final String PATH_LOOP_COUNTS = "pathLoopCounts";
    /** Number of bodies this replay path executed for one retained loop. */
    public static final String LOOP_BODY_COUNT = "loopBodyCount";
    /** Exact array cardinality for one dynamic fixed-count occurrence. */
    public static final String LOOP_CARDINALITY = "loopCardinality";
    /** Exact cardinality observations published by one completed path. */
    public static final String LOOP_CARDINALITIES = "loopCardinalities";
    /** Named runtime gaps in exact cardinality observation. */
    public static final String LOOP_CARDINALITY_GAPS =
            "loopCardinalityGaps";
    /** Per-runtime-loop invocation ordinal of an exact cardinality row. */
    public static final String DYNAMIC_OCCURRENCE = "dynamicOccurrence";
    /** Runtime loop id whose counter supplied this path-local observation. */
    public static final String RUNTIME_LOOP_ID = "runtimeLoopId";
    /** Authority carried by an observed replay body count. */
    public static final String PATH_BODY_COUNT_AUTHORITY =
            "RUNTIME_REPLAY_LOOP_BODY_COUNT_V1";
    /** Authority carried by an observed dynamic array cardinality. */
    public static final String PATH_CARDINALITY_AUTHORITY =
            "RUNTIME_ARRAY_CARDINALITY_V1";
    /** Named coverage rows for missing or ambiguous path-local loop counts. */
    public static final String PATH_LOOP_COUNT_GAPS = "pathLoopCountGaps";
    public static final String PATH_LOOP_COUNT_MISSING =
            "PATH_LOCAL_LOOP_COUNT_MISSING";
    public static final String PATH_LOOP_COUNT_AMBIGUOUS =
            "PATH_LOCAL_LOOP_COUNT_AMBIGUOUS";
    public static final String PATH_LOOP_COUNT_OUT_OF_BOUND =
            "PATH_LOCAL_LOOP_COUNT_OUT_OF_BOUND";
    public static final String PATH_ARRAY_CARDINALITY_MISSING =
            "PATH_LOCAL_ARRAY_CARDINALITY_MISSING";

    /**
     * An array-backed indexed {@code for}. A local early exit is a guarded
     * path effect; it does not replace the array cardinality with a semantic
     * unroll bound.
     */
    public static final String LOOP_FIXED_COUNT_INDEXED =
            "FIXED_COUNT_INDEXED";
    /** A {@code while} or other data/control-dependent loop, bounded by
     *  {@code K_L}. */
    public static final String LOOP_CONDITION_BOUNDED = "CONDITION_BOUNDED";
    /** The sole loop exit tests an array length. */
    public static final String LOOP_CLASSIFIED_ARRAY_INDEXED =
            "STATIC_ARRAY_INDEXED_FOR_V1";
    /** Anything else the loop CFG retained. */
    public static final String LOOP_CLASSIFIED_CONDITION_CONTROLLED =
            "STATIC_CONDITION_CONTROLLED_V1";

    /** {@code K_L} came from this loop's own declaration. */
    public static final String BOUND_FROM_DECLARATION =
            "LOOP_DECLARED_LOOP_BODY_BOUND";
    /** The loop declared no {@code K_L} and inherited the workload default. */
    public static final String BOUND_FROM_POLICY =
            "WORKLOAD_DECLARED_LOOP_BODY_BOUND";

    /**
     * A row states a bounded loop and names no loop control site.
     */
    public static final String LOOP_SITE_UNDECLARED =
            "BOUNDED_LOOP_SITE_UNDECLARED";
    /**
     * One nest's loop control sites do not all classify the same way, so the
     * nest has no single kind.  Published as the weaker
     * {@link #LOOP_CONDITION_BOUNDED} and named.
     */
    public static final String GAP_LOOP_CLASSIFICATION_INCONSISTENT =
            "BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT";
    /**
     * {@code K_L} of a retained loop that declares none of its own.
     *
     * <p>README section 5 makes {@code K_L} per loop.  This is the value a
     * loop inherits when it declares nothing, and nothing more: it is no
     * longer the one bound every loop runs under, and it is no longer the
     * ceiling a declaration is checked against.  See {@link
     * #MAX_DECLARED_LOOP_BODY_ITERATIONS} for that.</p>
     */
    public static final int MAX_LOOP_BODY_ITERATIONS = 8;
    /**
     * The per-loop ceiling: the largest {@code K_L} any loop may declare.
     *
     * <p>The experiment owns the bounds; this only bounds what a declaration
     * may say.  It is deliberately not open-ended: a declaration above it is
     * refused by name rather than clamped, because clamping would state a
     * prefix nobody declared.</p>
     */
    public static final int MAX_DECLARED_LOOP_BODY_ITERATIONS = 64;
    /** A declared {@code K_L} outside {@code 1..MAX_DECLARED}. */
    public static final String DECLARED_BOUND_OUT_OF_RANGE =
            "BOUNDED_LOOP_BODY_BOUND_OUT_OF_RANGE";
    /** A declared {@code K_L} that names no retained loop. */
    public static final String DECLARED_BOUND_SITE_UNDECLARED =
            "BOUNDED_LOOP_BODY_BOUND_SITE_UNDECLARED";
    /**
     * An encoded contract whose executor limit is not the one its own
     * declarations demand.
     *
     * <p>The limit is derived, never stated independently: a row that states
     * a different one was written against another rule, and honouring it
     * would either cut a prefix the model holds or claim an executor the run
     * did not use.</p>
     */
    public static final String EXECUTOR_LIMIT_MISMATCH =
            "BOUNDED_LOOP_EXECUTOR_LIMIT_MISMATCH";
    /**
     * Maximum failure-relevant cells retained for one symbolic container.
     *
     * <p>A resource default, not a modeled collection length.  When a target
     * condition is stated over the elements of one fixed-length array or
     * container, every one of those elements belongs to the slice; a cap
     * below the demanded length could only refuse the slice the target is
     * stated over.</p>
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
    // A guarded body-entry hook denies body K+1 after K bodies have run.
    // The encoded field name is historical; the value is a body bound.
    private static final int SCHEMA_VERSION = 1;
    private static final String KIND = "CFG_BACKEDGE";
    private static final String SCOPE = "ALL_EXECUTION_SCOPE_LOOPS";
    private static final String ON_LIMIT = "CUT_PATH";
    /** Per-loop {@code K_L}, keyed by loop control site. */
    private static final String DECLARED_FIELD = "loopBodyBounds";
    /** {@code K_L} of a loop this contract names no bound for. */
    private static final String DEFAULT_FIELD = "defaultBackedgeTraversals";

    private final int defaultBackedgeTraversals;
    private final SortedMap<String, Integer> declared;
    private final int maxBackedgeTraversals;

    private LoopBoundPolicy(int defaultBackedgeTraversals,
                            Map<String, Integer> declared) {
        if (defaultBackedgeTraversals != MAX_LOOP_BODY_ITERATIONS) {
            throw new IllegalArgumentException(
                    "the inherited loop body bound is fixed at "
                            + MAX_LOOP_BODY_ITERATIONS + " iterations");
        }
        // Sorted, so one set of declarations has one identity and one
        // encoding whatever order a producer walked its loops in.  README
        // section 1 forbids resolving identity by call order, and a contract
        // hash that changed with iteration order would do exactly that.
        SortedMap<String, Integer> bounds = new TreeMap<String, Integer>();
        int limit = defaultBackedgeTraversals;
        if (declared != null) {
            for (Map.Entry<String, Integer> entry : declared.entrySet()) {
                String loopSiteId = entry.getKey() == null ? ""
                        : entry.getKey().trim();
                if (loopSiteId.isEmpty()) {
                    throw new IllegalArgumentException(
                            DECLARED_BOUND_SITE_UNDECLARED + ":"
                                    + entry.getValue());
                }
                int bound = entry.getValue() == null ? 0
                        : entry.getValue().intValue();
                if (bound < 1
                        || bound > MAX_DECLARED_LOOP_BODY_ITERATIONS) {
                    throw new IllegalArgumentException(
                            DECLARED_BOUND_OUT_OF_RANGE + ":" + loopSiteId
                                    + ":" + bound);
                }
                bounds.put(loopSiteId, Integer.valueOf(bound));
                if (bound > limit) limit = bound;
            }
        }
        this.defaultBackedgeTraversals = defaultBackedgeTraversals;
        this.declared = Collections.unmodifiableSortedMap(bounds);
        this.maxBackedgeTraversals = limit;
    }

    /** A contract in which every retained loop inherits the default. */
    public static LoopBoundPolicy cfgBackedges(int maxTraversals) {
        return new LoopBoundPolicy(maxTraversals,
                Collections.<String, Integer>emptyMap());
    }

    /**
     * A contract in which the named loops declare their own {@code K_L}.
     *
     * @param maxTraversals the bound a loop that declares none inherits
     * @param declared      {@code K_L} keyed by the loop control site id
     *                      {@link #loopSiteId(java.util.Collection)} names,
     *                      each in
     *                      {@code 1..MAX_DECLARED_LOOP_BODY_ITERATIONS}
     */
    public static LoopBoundPolicy cfgBackedges(
            int maxTraversals, Map<String, Integer> declared) {
        return new LoopBoundPolicy(maxTraversals, declared);
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
        int limit = integer(encoded, "maxBackedgeTraversals", -1);
        JsonObject bounds = object(encoded, DECLARED_FIELD);
        Map<String, Integer> declared = new TreeMap<String, Integer>();
        for (Map.Entry<String, JsonElement> entry : bounds.entrySet()) {
            declared.put(entry.getKey(),
                    Integer.valueOf(integer(bounds, entry.getKey(), -1)));
        }
        // A row written before per-loop bounds existed states the limit and
        // nothing else, and its limit is the default.
        LoopBoundPolicy policy = new LoopBoundPolicy(
                integer(encoded, DEFAULT_FIELD, limit), declared);
        if (policy.maxBackedgeTraversals != limit) {
            throw new IllegalArgumentException(EXECUTOR_LIMIT_MISMATCH + ":"
                    + limit + " != " + policy.maxBackedgeTraversals);
        }
        return policy;
    }

    /**
     * The backedge limit the executor runs an unnarrowed loop under.
     *
     * <p>Derived and never stated: it is the largest {@code K_L} this
     * contract holds, so it can never be below a bound the model states.
     * README section 5 has GraphChecker translate {@code K_L} "to the
     * executor's internal backedge limit", and an instrumenter that cannot
     * narrow a loop stamps this - honouring every declaration at the cost of
     * letting a narrower loop run past the slots its own prefix holds, which
     * the model then refuses by name.  An instrumenter that can narrow uses
     * {@link #maxBackedgeTraversals(String)} instead.</p>
     */
    public int maxBackedgeTraversals() {
        return maxBackedgeTraversals;
    }

    /**
     * {@code K_L} for one retained loop: its own declaration, or the default.
     *
     * @param loopSiteId the loop control site id of the retained loop
     */
    public int maxBackedgeTraversals(String loopSiteId) {
        Integer bound = loopSiteId == null ? null : declared.get(loopSiteId);
        return bound == null ? defaultBackedgeTraversals : bound.intValue();
    }

    /**
     * Checks the bound stamped on one CFG hook against this task contract.
     *
     * <p>The instrumenter resolves a natural loop's local {@code K_L} from
     * its control sites and stamps that value on its latch hooks. Runtime
     * execution and summary import use this same range check; import must not
     * compare a loop's local {@code K_L} with the unrelated maximum over
     * every loop in the task.</p>
     */
    public boolean acceptsInstrumentedBound(
            String encodedLoopId, int instrumentedBound) {
        if (instrumentedBound < 1
                || instrumentedBound > maxBackedgeTraversals) {
            return false;
        }
        return true;
    }

    /** {@code K_L} of a retained loop that declares none. */
    public int defaultBackedgeTraversals() {
        return defaultBackedgeTraversals;
    }

    /** The declared {@code K_L} of this contract, keyed by loop site. */
    public Map<String, Integer> declaredBounds() {
        return declared;
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
        StringBuilder identity = new StringBuilder(KIND)
                .append(':').append(maxBackedgeTraversals)
                .append(':').append(ON_LIMIT);
        // Appended only when a loop declares something, so a campaign with no
        // declaration keeps the identity every artifact in this tree carries.
        for (Map.Entry<String, Integer> entry : declared.entrySet()) {
            identity.append(':').append(entry.getKey())
                    .append('=').append(entry.getValue());
        }
        return identity.toString();
    }

    public JsonObject toJson() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("schemaVersion", SCHEMA_VERSION);
        encoded.addProperty("kind", KIND);
        encoded.addProperty("scope", SCOPE);
        encoded.addProperty("maxBackedgeTraversals",
                maxBackedgeTraversals);
        encoded.addProperty("onLimit", ON_LIMIT);
        if (!declared.isEmpty()) {
            encoded.addProperty(DEFAULT_FIELD, defaultBackedgeTraversals);
            JsonObject bounds = new JsonObject();
            for (Map.Entry<String, Integer> entry : declared.entrySet()) {
                bounds.addProperty(entry.getKey(), entry.getValue());
            }
            encoded.add(DECLARED_FIELD, bounds);
        }
        return encoded;
    }

    public void writeTo(JsonObject owner) {
        owner.add(FIELD, toJson());
    }

    // ------------------------------------------------------------------
    // Retained loop identity
    // ------------------------------------------------------------------

    /**
     * The retained loop one set of declared loop control sites names.
     *
     * <p>One site is the loop.  Several are one loop nest the operation is
     * inside, and the composite is built from the sorted site ids so it is a
     * fact about the CFG rather than about the order a reader happened to
     * walk them in.</p>
     *
     * @return the loop site, or {@code ""} when nothing declared one
     */
    public static String loopSiteId(java.util.Collection<?> controlSiteIds) {
        if (controlSiteIds == null || controlSiteIds.isEmpty()) return "";
        java.util.List<String> sites = new java.util.ArrayList<String>();
        for (Object site : controlSiteIds) {
            String text = site == null ? "" : String.valueOf(site);
            if (!text.isEmpty() && !sites.contains(text)) sites.add(text);
        }
        if (sites.isEmpty()) return "";
        if (sites.size() == 1) return sites.get(0);
        Collections.sort(sites);
        StringBuilder composite = new StringBuilder("L(");
        for (int index = 0; index < sites.size(); index++) {
            if (index > 0) composite.append('+');
            composite.append(sites.get(index));
        }
        return composite.append(')').toString();
    }

    /**
     * {@code K_L} for one retained loop, from its own declaration or, absent
     * one, from the bound an undeclared loop inherits.
     *
     * @param declared the row's {@link #LOOP_BODY_BOUND}, or {@code null}
     * @throws IllegalArgumentException naming
     *                                  {@link #DECLARED_BOUND_OUT_OF_RANGE}
     *                                  when a declared bound is outside
     *                                  {@code 1..MAX_DECLARED}
     */
    public static int bodyBound(Object declared) {
        if (declared == null) return MAX_LOOP_BODY_ITERATIONS;
        int bound;
        if (declared instanceof Number) {
            bound = ((Number) declared).intValue();
        } else {
            try {
                bound = Integer.parseInt(String.valueOf(declared).trim());
            } catch (NumberFormatException malformed) {
                throw new IllegalArgumentException(DECLARED_BOUND_OUT_OF_RANGE
                        + ":" + declared);
            }
        }
        if (bound < 1 || bound > MAX_DECLARED_LOOP_BODY_ITERATIONS) {
            throw new IllegalArgumentException(DECLARED_BOUND_OUT_OF_RANGE
                    + ":" + bound);
        }
        return bound;
    }

    /** Which declaration {@link #bodyBound(Object)} answered from. */
    public static String boundAuthority(Object declared) {
        return declared == null ? BOUND_FROM_POLICY : BOUND_FROM_DECLARATION;
    }

}
