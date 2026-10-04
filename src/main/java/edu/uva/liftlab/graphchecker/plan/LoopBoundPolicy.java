package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;

/**
 * Canonical bounds for bounded concolic execution, and the loop vocabulary
 * every stage states a retained loop with.
 */
public final class LoopBoundPolicy {

    private static final String FIELD = "loopBound";

    public static final String LOOP_SITE_ID = "loopSiteId";
    public static final String LOOP_BODY_BOUND = "loopBodyBound";
    public static final String LOOP_CONTROL_SITE_IDS = "loopControlSiteIds";
    /** Branch sites the CFG analysis assigns to this innermost natural loop
     *  (not a lexical unit range). */
    public static final String LOOP_INNERMOST_BRANCH_SITE_IDS =
            "loopInnermostBranchSiteIds";
    /** Branch decisions that leave one dynamic invocation. */
    public static final String LOOP_EXIT_DECISIONS = "loopExitDecisions";
    /** Largest latch unit index: the body's last unit. */
    public static final String LOOP_LATCH_UNIT_INDEX = "loopLatchUnitIndex";
    /** {@link #LOOP_FIXED_COUNT_INDEXED} or {@link #LOOP_CONDITION_BOUNDED};
     *  plan metadata, not a heuristic. */
    public static final String LOOP_CLASSIFICATION = "loopClassification";
    public static final String LOOP_CLASSIFICATION_AUTHORITY =
            "loopClassificationAuthority";
    public static final String RUNTIME_LOOP_ID = "runtimeLoopId";
    /** Which activation a region is rooted on. */
    public static final String ROOT_AUTHORITY = "rootAuthority";
    public static final String LOOP_BODY_ROOT = "LOOP_BODY_ROOT";
    /** The loop body a {@link #LOOP_BODY_ROOT} region is rooted at. */
    public static final String ROOT_LOOP = "rootLoop";
    public static final String ROOT_LOOP_METHOD = "rootLoopMethod";
    public static final String HEADER_UNIT_INDEX = "headerUnitIndex";
    /** {@link #ROOT_LOOP} member naming the original unit this region needs. */
    public static final String DEMANDED_UNIT_INDEX = "demandedUnitIndex";
    /**
     * Retained-loop row member: the call units of the loop at which an
     * iteration frame can open ({@code causynth.CfgLoopControl#bodyEntry}),
     * the only demanded units a {@link #LOOP_BODY_ROOT} may name.  A row
     * stating none places none.
     */
    public static final String BODY_ENTRY_CALL_UNITS = "bodyEntryCallUnits";

    /** Array-backed indexed {@code for}; an early exit is a path effect, not an
     *  unroll bound. */
    public static final String LOOP_FIXED_COUNT_INDEXED =
            "FIXED_COUNT_INDEXED";
    /** Data-dependent loop, bounded by {@code K_L}. */
    public static final String LOOP_CONDITION_BOUNDED = "CONDITION_BOUNDED";
    public static final String LOOP_CLASSIFIED_ARRAY_INDEXED =
            "STATIC_ARRAY_INDEXED_FOR_V1";
    public static final String LOOP_CLASSIFIED_CONDITION_CONTROLLED =
            "STATIC_CONDITION_CONTROLLED_V1";

    /** Declared backedge ceiling for retained loops the case did not narrow
     *  ({@code causynth_loop_default_bound} via {@code run_engine.sh}). Never a
     *  silent constant (PIPELINE §0); each inheritance is published
     *  as an {@code INHERITED_K_L_<n>} gap, and an undeclared campaign is
     *  refused. */
    public static final String DEFAULT_BOUND_PROPERTY =
            "causynth.loop.default.bound";
    private static final String DEFAULT_FIELD = "defaultBackedgeTraversals";
    /** {@link #bodyBound(Object)} when nothing was declared. */
    public static final int NO_DECLARED_BOUND = 0;
    /** Largest declarable {@code K_L}; above it is refused, not clamped. */
    public static final int MAX_DECLARED_LOOP_BODY_ITERATIONS = 64;
    public static final String DECLARED_BOUND_OUT_OF_RANGE =
            "BOUNDED_LOOP_BODY_BOUND_OUT_OF_RANGE";
    public static final String DECLARED_BOUND_SITE_UNDECLARED =
            "BOUNDED_LOOP_BODY_BOUND_SITE_UNDECLARED";
    public static final String PLAN_FIELD = "retainedLoops";
    public static final String LOOP_BODY_BOUND_DISAGREES =
            "BOUNDED_LOOP_BODY_BOUND_DISAGREES";
    /** Body entries one replay-path loop may run per activation (stops endless
     *  service loops). Caps replay work; {@link #declaredDefault()} caps the
     *  path space. */
    public static final int MAX_REPLAY_PATH_LOOP_BODIES = 32;
    private static final int SCHEMA_VERSION = 1;
    private static final String DECLARED_FIELD = "loopBodyBounds";

    private final int defaultBackedgeTraversals;
    private final SortedMap<String, Integer> declared;
    private final int maxBackedgeTraversals;

    private LoopBoundPolicy(int defaultBackedgeTraversals,
                            Map<String, Integer> declared) {
        if (defaultBackedgeTraversals < 1) {
            throw new IllegalArgumentException(
                    "the inherited loop body bound must be at least one body "
                            + "execution, not " + defaultBackedgeTraversals);
        }
        // Sorted: one declaration set, one encoding.
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

    /** Named loops declare their own {@code K_L}; the rest inherit {@code
     *  maxTraversals}. */
    public static LoopBoundPolicy cfgBackedges(
            int maxTraversals, Map<String, Integer> declared) {
        return new LoopBoundPolicy(maxTraversals, declared);
    }

    /**
     * The one policy of a tree woven for plans that state these two: every
     * loop either declares, under the same inherited default.  A loop the two
     * bound differently, or two defaults, is a conflict by name -- a subset is
     * not (a region GROW added states its own loops beside the seed's).
     */
    public LoopBoundPolicy union(LoopBoundPolicy other) {
        if (other.defaultBackedgeTraversals != defaultBackedgeTraversals) {
            throw new IllegalStateException("CAMPAIGN_LOOP_BOUND_CONFLICT: "
                    + "inherited K_L " + defaultBackedgeTraversals + " and "
                    + other.defaultBackedgeTraversals);
        }
        SortedMap<String, Integer> merged =
                new TreeMap<String, Integer>(declared);
        for (Map.Entry<String, Integer> entry : other.declared.entrySet()) {
            Integer held = merged.put(entry.getKey(), entry.getValue());
            if (held != null && !held.equals(entry.getValue())) {
                throw new IllegalStateException(
                        "CAMPAIGN_LOOP_BOUND_CONFLICT: loop " + entry.getKey()
                                + " under K_L=" + held + " and K_L="
                                + entry.getValue());
            }
        }
        return new LoopBoundPolicy(defaultBackedgeTraversals, merged);
    }

    /** The inherited bound this campaign declared; missing or non-positive is
     *  refused by name. */
    public static int declaredDefault() {
        String declared = System.getProperty(DEFAULT_BOUND_PROPERTY);
        String value = declared == null ? "" : declared.trim();
        int bound;
        try {
            bound = Integer.parseInt(value);
        } catch (NumberFormatException malformed) {
            throw new IllegalStateException("the campaign declared no -D"
                    + DEFAULT_BOUND_PROPERTY + " (causynth_loop_default_bound)"
                    + ", so no loop may inherit a bound: got \"" + value
                    + "\"", malformed);
        }
        if (bound < 1) {
            throw new IllegalStateException(DEFAULT_BOUND_PROPERTY
                    + " must be at least one body execution, not " + bound);
        }
        return bound;
    }

    public static LoopBoundPolicy decode(JsonObject owner) {
        JsonElement raw = owner == null ? null : owner.get(FIELD);
        if (raw == null || !raw.isJsonObject()) {
            throw new IllegalArgumentException(
                    "execution task requires a loopBound contract");
        }
        JsonObject encoded = raw.getAsJsonObject();
        if (optionalInteger(encoded, "schemaVersion", -1) != SCHEMA_VERSION) {
            throw new IllegalArgumentException(
                    "unsupported loopBound contract");
        }
        JsonObject bounds = object(encoded, DECLARED_FIELD);
        Map<String, Integer> declared = new TreeMap<String, Integer>();
        for (Map.Entry<String, JsonElement> entry : bounds.entrySet()) {
            declared.put(entry.getKey(),
                    Integer.valueOf(optionalInteger(bounds, entry.getKey(), -1)));
        }
        // The declared default travels in the frozen contract, so a replay
        // needs no property; the executor limit is re-derived, never read back.
        return new LoopBoundPolicy(
                optionalInteger(encoded, DEFAULT_FIELD, 0), declared);
    }

    /** Backedge limit: derived, so never below a bound the model states. */
    public int maxBackedgeTraversals() { return maxBackedgeTraversals; }

    /** {@code K_L} of one loop: its declaration, else the inherited default. */
    public int maxBackedgeTraversals(String loopSiteId) {
        Integer bound = loopSiteId == null ? null : declared.get(loopSiteId);
        return bound == null ? defaultBackedgeTraversals : bound.intValue();
    }

    /** Checks a CFG hook's stamped bound against the task-wide maximum. */
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

    public JsonObject toJson() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("schemaVersion", SCHEMA_VERSION);
        encoded.addProperty(DEFAULT_FIELD, defaultBackedgeTraversals);
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

    /** The loop a set of control sites names; sorted, so order-independent. */
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

    /** {@code K_L} from one loop's own declaration only; silence is {@link
     *  #NO_DECLARED_BOUND}, never the inherited default (which would turn an
     *  undeclared loop into an accepted one). */
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

}
