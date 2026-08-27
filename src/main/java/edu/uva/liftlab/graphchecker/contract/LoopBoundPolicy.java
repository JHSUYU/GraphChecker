package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;

/**
 * Canonical bounds for bounded concolic execution, and the loop vocabulary
 * every stage states a retained loop with.
 */
public final class LoopBoundPolicy {
    public static final String FIELD = "loopBound";

    public static final String LOOP_SITE_ID = "loopSiteId";
    public static final String LOOP_BODY_BOUND = "loopBodyBound";
    public static final String LOOP_BODY_BOUND_AUTHORITY =
            "loopBodyBoundAuthority";
    public static final String LOOP_CONTROL_SITE_IDS = "loopControlSiteIds";
    /** Largest original unit index among the loop's latches: the body's last unit. */
    public static final String LOOP_LATCH_UNIT_INDEX = "loopLatchUnitIndex";
    /** {@link #LOOP_FIXED_COUNT_INDEXED} or {@link #LOOP_CONDITION_BOUNDED};
     *  plan metadata, never a consumer heuristic. */
    public static final String LOOP_CLASSIFICATION = "loopClassification";
    public static final String LOOP_CLASSIFICATION_AUTHORITY =
            "loopClassificationAuthority";
    public static final String PATH_LOOP_COUNTS = "pathLoopCounts";
    public static final String LOOP_BODY_COUNT = "loopBodyCount";
    public static final String PATH_LOOP_REACHED = "pathLoopReached";
    public static final String LOOP_CARDINALITY = "loopCardinality";
    public static final String LOOP_CARDINALITIES = "loopCardinalities";
    public static final String LOOP_CARDINALITY_GAPS =
            "loopCardinalityGaps";
    public static final String DYNAMIC_OCCURRENCE = "dynamicOccurrence";
    public static final String RUNTIME_LOOP_ID = "runtimeLoopId";
    /** Region-row member naming which activation a region is rooted on. */
    public static final String ROOT_AUTHORITY = "rootAuthority";
    /** {@link #ROOT_AUTHORITY} of a region re-rooted at a loop body. */
    public static final String LOOP_BODY_ROOT = "LOOP_BODY_ROOT";
    /** Region-row member naming the loop body such a region is rooted at. */
    public static final String ROOT_LOOP = "rootLoop";
    /** {@link #ROOT_LOOP} member naming the method holding that loop. */
    public static final String ROOT_LOOP_METHOD = "rootLoopMethod";
    /** {@link #ROOT_LOOP} member naming the loop header's original unit. */
    public static final String HEADER_UNIT_INDEX = "headerUnitIndex";
    public static final String PATH_CARDINALITY_AUTHORITY =
            "RUNTIME_ARRAY_CARDINALITY_V1";
    public static final String PATH_LOOP_COUNT_GAPS = "pathLoopCountGaps";
    /** Retained-loop member stating whether this loop's trip count can reach
     *  anything the failure reads.  Absent means required: a declaration
     *  that says nothing has not been decided, and silence never relaxes a
     *  soundness device. */
    public static final String LOOP_FAILURE_RELEVANT = "failureRelevant";
    /** {@link #LOOP_FAILURE_RELEVANT}'s authority, so a reader can tell a
     *  decided declaration from an old one that predates the decision. */
    public static final String LOOP_RELEVANCE_AUTHORITY =
            "loopRelevanceAuthority";
    /** The one rule that decides {@link #LOOP_FAILURE_RELEVANT}. */
    public static final String FAILURE_DEMANDED_LOOP_SCOPE =
            "FAILURE_DEMANDED_LOOP_SCOPE_V1";
    public static final String PATH_LOOP_COUNT_MISSING =
            "PATH_LOCAL_LOOP_COUNT_MISSING";
    public static final String PATH_LOOP_COUNT_AMBIGUOUS =
            "PATH_LOCAL_LOOP_COUNT_AMBIGUOUS";
    public static final String PATH_LOOP_COUNT_OUT_OF_BOUND =
            "PATH_LOCAL_LOOP_COUNT_OUT_OF_BOUND";
    public static final String PATH_LOOP_REACHABILITY_MISSING =
            "PATH_LOCAL_LOOP_REACHABILITY_MISSING";
    public static final String PATH_ARRAY_CARDINALITY_MISSING =
            "PATH_LOCAL_ARRAY_CARDINALITY_MISSING";

    /** An array-backed indexed {@code for}; a local early exit is a guarded
     *  path effect, not a semantic unroll bound. */
    public static final String LOOP_FIXED_COUNT_INDEXED =
            "FIXED_COUNT_INDEXED";
    /** A {@code while} or other data-dependent loop, bounded by {@code K_L}. */
    public static final String LOOP_CONDITION_BOUNDED = "CONDITION_BOUNDED";
    public static final String LOOP_CLASSIFIED_ARRAY_INDEXED =
            "STATIC_ARRAY_INDEXED_FOR_V1";
    public static final String LOOP_CLASSIFIED_CONDITION_CONTROLLED =
            "STATIC_CONDITION_CONTROLLED_V1";

    public static final String BOUND_FROM_DECLARATION =
            "LOOP_DECLARED_LOOP_BODY_BOUND";
    public static final String LOOP_SITE_UNDECLARED =
            "BOUNDED_LOOP_SITE_UNDECLARED";
    /** One nest's control sites do not all classify alike, so the nest has no
     *  single kind: published as the weaker CONDITION_BOUNDED, and named. */
    public static final String GAP_LOOP_CLASSIFICATION_INCONSISTENT =
            "BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT";
    /** The executor's backedge ceiling for a loop no declaration narrows: a
     *  resource limit, never a modeled {@code K_L}.  README {@code LOOP-1}
     *  forbids a retained condition loop inheriting a core default. */
    public static final int MAX_LOOP_BODY_ITERATIONS = 8;
    /** What {@link #bodyBound(Object)} answers when nothing was declared. */
    public static final int NO_DECLARED_BOUND = 0;
    /** The largest {@code K_L} any loop may declare; a declaration above it is
     *  refused by name rather than clamped. */
    public static final int MAX_DECLARED_LOOP_BODY_ITERATIONS = 64;
    /** A declared {@code K_L} outside {@code 1..MAX_DECLARED}. */
    public static final String DECLARED_BOUND_OUT_OF_RANGE =
            "BOUNDED_LOOP_BODY_BOUND_OUT_OF_RANGE";
    /** A declared {@code K_L} that names no retained loop. */
    public static final String DECLARED_BOUND_SITE_UNDECLARED =
            "BOUNDED_LOOP_BODY_BOUND_SITE_UNDECLARED";
    /** An encoded contract whose executor limit is not the one its own
     *  declarations demand; the limit is derived, never stated. */
    public static final String EXECUTOR_LIMIT_MISMATCH =
            "BOUNDED_LOOP_EXECUTOR_LIMIT_MISMATCH";
    /** Maximum failure-relevant cells retained for one symbolic container. */
    public static final int SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY = 32;
    /** Maximum restartable state transitions in one single-writer history:
     *  a third ledger, neither the backedge bound nor one replay's work. */
    public static final int MAX_STATE_TIMELINE_TRANSITIONS = 8;
    /** Body entries one execution-scope loop may run in one activation.
     *  Independent of {@link #MAX_LOOP_BODY_ITERATIONS}: that caps the path
     *  space a solver reasons about, this caps the work one replay may do. */
    public static final int MAX_EXECUTION_SCOPE_LOOP_BODIES = 2048;
    /** Body entries one replay-path loop outside the execution scope may run:
     *  the service loops a long-lived root spins between the slice's calls,
     *  where an unbounded count is what makes an activation endless. */
    public static final int MAX_REPLAY_PATH_LOOP_BODIES = 32;
    private static final int SCHEMA_VERSION = 1;
    /** Vocabulary of {@link #identity()}, never a wire member: one kind, one
     *  scope and one limit action are all this contract has ever had, so
     *  stating them per row said nothing a reader could act on. */
    private static final String KIND = "CFG_BACKEDGE";
    private static final String ON_LIMIT = "CUT_PATH";
    /** Per-loop {@code K_L}, keyed by loop control site. */
    private static final String DECLARED_FIELD = "loopBodyBounds";

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
        // Sorted, so one set of declarations has one identity whatever order
        // a producer walked its loops in (README section 1).
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
                int bound = bodyBound(entry.getValue() == null
                        ? Integer.valueOf(0) : entry.getValue());
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

    /** A contract in which the named loops declare their own {@code K_L},
     *  keyed by loop control site id; the rest inherit {@code maxTraversals}. */
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
        if (integer(encoded, "schemaVersion", -1) != SCHEMA_VERSION) {
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
        // The inherited bound is fixed at MAX_LOOP_BODY_ITERATIONS by the
        // constructor, so a row never states it; only the declarations and
        // the limit they derive are contract.
        LoopBoundPolicy policy = new LoopBoundPolicy(
                MAX_LOOP_BODY_ITERATIONS, declared);
        if (policy.maxBackedgeTraversals != limit) {
            throw new IllegalArgumentException(EXECUTOR_LIMIT_MISMATCH + ":"
                    + limit + " != " + policy.maxBackedgeTraversals);
        }
        return policy;
    }

    /** The backedge limit an unnarrowed loop runs under: derived, never
     *  stated, so it is never below a bound the model states. */
    public int maxBackedgeTraversals() { return maxBackedgeTraversals; }

    /** {@code K_L} for one retained loop: its own declaration, or the executor
     *  ceiling - a resource limit only - a loop no declaration narrows runs at. */
    public int maxBackedgeTraversals(String loopSiteId) {
        Integer bound = loopSiteId == null ? null : declared.get(loopSiteId);
        return bound == null ? defaultBackedgeTraversals : bound.intValue();
    }

    /** Checks one CFG hook's stamped bound against this contract; import must
     *  not compare a loop's local {@code K_L} with the task-wide maximum. */
    public boolean acceptsInstrumentedBound(int instrumentedBound) {
        return instrumentedBound >= 1
                && instrumentedBound <= maxBackedgeTraversals;
    }

    public int defaultBackedgeTraversals() {
        return defaultBackedgeTraversals;
    }

    public Map<String, Integer> declaredBounds() {
        return declared;
    }

    public static int maxLoopBodies(boolean executionScopeLoop) {
        return executionScopeLoop
                ? MAX_EXECUTION_SCOPE_LOOP_BODIES
                : MAX_REPLAY_PATH_LOOP_BODIES;
    }

    public String identity() {
        StringBuilder identity = new StringBuilder(KIND)
                .append(':').append(maxBackedgeTraversals)
                .append(':').append(ON_LIMIT);
        // Appended only when a loop declares something.
        for (Map.Entry<String, Integer> entry : declared.entrySet()) {
            identity.append(':').append(entry.getKey())
                    .append('=').append(entry.getValue());
        }
        return identity.toString();
    }

    public JsonObject toJson() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("schemaVersion", SCHEMA_VERSION);
        encoded.addProperty("maxBackedgeTraversals",
                maxBackedgeTraversals);
        if (!declared.isEmpty()) {
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

    /** The retained loop one set of declared control sites names, built from
     *  the sorted ids so it is a fact about the CFG and not about the order a
     *  reader walked them in. */
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
     * {@code K_L} from one retained loop's own declaration only.  Silence
     * answers {@link #NO_DECLARED_BOUND} and never the core default: reading
     * {@link #MAX_LOOP_BODY_ITERATIONS} out of an absent field is the step
     * that turned an undeclared loop into an accepted one.
     */
    public static int bodyBound(Object declared) {
        if (declared == null) return NO_DECLARED_BOUND;
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

    /**
     * The method signatures one site id names.
     *
     * <p>A site id is {@code <method>#uN} and a nest is
     * {@code L(site+site+...)}.  A Java signature never contains {@code '+'},
     * so the parts split exactly, which a regular expression over
     * {@code <...>} cannot do: {@code void <init>(..)} nests angle brackets
     * and any such scan reads the constructor marker as the whole method.</p>
     *
     * <p>Returns empty when the id names no method, which every caller reads
     * as "unknown", never as "no method is involved".</p>
     */
    public static java.util.Set<String> siteMethods(String siteId) {
        java.util.Set<String> methods =
                new java.util.LinkedHashSet<String>();
        String text = siteId == null ? "" : siteId.trim();
        if (text.startsWith("L(") && text.endsWith(")")) {
            text = text.substring(2, text.length() - 1);
        }
        for (String part : text.split("\\+")) {
            String site = part.trim();
            int marker = site.lastIndexOf("#u");
            if (marker > 0) site = site.substring(0, marker);
            if (site.length() > 1 && site.charAt(0) == '<'
                    && site.charAt(site.length() - 1) == '>') {
                methods.add(site);
            }
        }
        return methods;
    }

    /**
     * Whether one retained-loop declaration's trip count is still demanded.
     *
     * <p>Fail-closed: a declaration that carries no decision, or one decided
     * under an authority this build does not know, is required.  Only an
     * explicit {@code false} under {@link #FAILURE_DEMANDED_LOOP_SCOPE}
     * relaxes the bound obligation, and only for the undeclared-bound gap --
     * a declared {@code K_L}, the path-local count and every out-of-bound
     * refusal are unaffected by this answer.</p>
     */
    public static boolean failureRelevantLoop(JsonObject declaration) {
        if (declaration == null) return true;
        JsonElement decided = declaration.get(LOOP_FAILURE_RELEVANT);
        if (decided == null || !decided.isJsonPrimitive()
                || !decided.getAsJsonPrimitive().isBoolean()) {
            return true;
        }
        JsonElement authority = declaration.get(LOOP_RELEVANCE_AUTHORITY);
        if (authority == null || !authority.isJsonPrimitive()
                || !FAILURE_DEMANDED_LOOP_SCOPE.equals(
                authority.getAsString())) {
            return true;
        }
        return decided.getAsBoolean();
    }
}
