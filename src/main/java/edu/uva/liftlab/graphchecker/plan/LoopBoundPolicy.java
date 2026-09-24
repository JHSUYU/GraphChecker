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

    /** Task member carrying this contract; read only through this class. */
    private static final String FIELD = "loopBound";

    public static final String LOOP_SITE_ID = "loopSiteId";
    public static final String LOOP_BODY_BOUND = "loopBodyBound";
    public static final String LOOP_CONTROL_SITE_IDS = "loopControlSiteIds";
    /** Branch sites assigned by the CFG analysis to this exact innermost
     * natural loop.  Replay uses this membership instead of treating unit
     * indices between a header and latch as a lexical loop body. */
    public static final String LOOP_INNERMOST_BRANCH_SITE_IDS =
            "loopInnermostBranchSiteIds";
    /** Exact branch decisions which leave one dynamic invocation. */
    public static final String LOOP_EXIT_DECISIONS = "loopExitDecisions";
    /** Largest original unit index among the loop's latches: the body's last unit. */
    public static final String LOOP_LATCH_UNIT_INDEX = "loopLatchUnitIndex";
    /** {@link #LOOP_FIXED_COUNT_INDEXED} or {@link #LOOP_CONDITION_BOUNDED};
     *  plan metadata, never a consumer heuristic. */
    public static final String LOOP_CLASSIFICATION = "loopClassification";
    public static final String LOOP_CLASSIFICATION_AUTHORITY =
            "loopClassificationAuthority";
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
    /** {@link #ROOT_LOOP} member naming the original unit this region needs. */
    public static final String DEMANDED_UNIT_INDEX = "demandedUnitIndex";

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

    /**
     * The one declared key stating the backedge ceiling a retained loop the
     * case did not narrow runs under.
     *
     * <p>It used to be a constant, {@code MAX_LOOP_BODY_ITERATIONS = 8},
     * applied silently: on the accepted 17960 run 54 retained loops inherited
     * it, which README {@code LOOP-1} forbids a retained condition loop doing.
     * The number is now the case's own statement --
     * {@code causynth_loop_default_bound} in its {@code workflow.properties},
     * passed as this property by {@code run_engine.sh} -- and every inherited
     * application is still published as the DIAGNOSTIC gap row the catalog
     * raises ({@code INHERITED_K_L_<n>}).  A campaign that states no bound is
     * refused by name rather than given one.</p>
     */
    public static final String DEFAULT_BOUND_PROPERTY =
            "causynth.loop.default.bound";
    /** Member stating the inherited bound one frozen contract was built on. */
    private static final String DEFAULT_FIELD = "defaultBackedgeTraversals";
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
    /** Task/plan member carrying the retained loops of one occurrence. */
    public static final String PLAN_FIELD = "retainedLoops";
    /** Two declarations state different {@code K_L} for one loop. */
    public static final String LOOP_BODY_BOUND_DISAGREES =
            "BOUNDED_LOOP_BODY_BOUND_DISAGREES";
    /** Body entries one replay-path loop may run in one activation: the
     *  service loops a long-lived root spins between the slice's calls,
     *  where an unbounded count is what makes an activation endless.
     *  Independent of {@link #declaredDefault()}: that caps the path
     *  space a solver reasons about, this caps the work one replay may do. */
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
        if (defaultBackedgeTraversals < 1) {
            throw new IllegalArgumentException(
                    "the inherited loop body bound must be at least one body "
                            + "execution, not " + defaultBackedgeTraversals);
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

    /** A contract in which the named loops declare their own {@code K_L},
     *  keyed by loop control site id; the rest inherit {@code maxTraversals}. */
    public static LoopBoundPolicy cfgBackedges(
            int maxTraversals, Map<String, Integer> declared) {
        return new LoopBoundPolicy(maxTraversals, declared);
    }

    /**
     * The inherited bound this campaign declared.
     *
     * <p>Absent, blank or not a positive integer is refused by name: a
     * campaign whose declaration did not arrive would model a prefix nobody
     * stated and report nothing about it.</p>
     */
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
        // The inherited bound the campaign declared travels IN the frozen
        // contract, so a replay honours the number the plan was built on and
        // needs no property of its own.  The executor limit is derived from
        // the declarations here exactly as the encoder derived the value it
        // stated, so the stated member is read by humans and never compared
        // with its own derivation.
        return new LoopBoundPolicy(
                optionalInteger(encoded, DEFAULT_FIELD, 0), declared);
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
     * answers {@link #NO_DECLARED_BOUND} and never the inherited bound:
     * reading the campaign's default out of an absent field is the step that
     * turned an undeclared loop into an accepted one.
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

}
