package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;

public final class LoopBoundPolicy {

    private static final String FIELD = "loopBound";

    public static final String LOOP_SITE_ID = "loopSiteId";
    public static final String LOOP_BODY_BOUND = "loopBodyBound";
    public static final String LOOP_CONTROL_SITE_IDS = "loopControlSiteIds";
    public static final String LOOP_INNERMOST_BRANCH_SITE_IDS =
            "loopInnermostBranchSiteIds";
    public static final String LOOP_EXIT_DECISIONS = "loopExitDecisions";
    public static final String LOOP_LATCH_UNIT_INDEX = "loopLatchUnitIndex";
    public static final String LOOP_CLASSIFICATION = "loopClassification";
    public static final String LOOP_CLASSIFICATION_AUTHORITY =
            "loopClassificationAuthority";
    public static final String RUNTIME_LOOP_ID = "runtimeLoopId";
    public static final String ROOT_AUTHORITY = "rootAuthority";
    public static final String LOOP_BODY_ROOT = "LOOP_BODY_ROOT";
    public static final String ROOT_LOOP = "rootLoop";
    public static final String ROOT_LOOP_METHOD = "rootLoopMethod";
    public static final String HEADER_UNIT_INDEX = "headerUnitIndex";
    public static final String DEMANDED_UNIT_INDEX = "demandedUnitIndex";
    public static final String BODY_ENTRY_CALL_UNITS = "bodyEntryCallUnits";

    public static final String LOOP_FIXED_COUNT_INDEXED =
            "FIXED_COUNT_INDEXED";
    public static final String LOOP_CONDITION_BOUNDED = "CONDITION_BOUNDED";
    public static final String LOOP_CLASSIFIED_ARRAY_INDEXED =
            "STATIC_ARRAY_INDEXED_FOR_V1";
    public static final String LOOP_CLASSIFIED_CONDITION_CONTROLLED =
            "STATIC_CONDITION_CONTROLLED_V1";

    public static final String DEFAULT_BOUND_PROPERTY =
            "causynth.loop.default.bound";
    private static final String DEFAULT_FIELD = "defaultBackedgeTraversals";
    public static final int NO_DECLARED_BOUND = 0;
    public static final int MAX_DECLARED_LOOP_BODY_ITERATIONS = 64;
    public static final String DECLARED_BOUND_OUT_OF_RANGE =
            "BOUNDED_LOOP_BODY_BOUND_OUT_OF_RANGE";
    public static final String DECLARED_BOUND_SITE_UNDECLARED =
            "BOUNDED_LOOP_BODY_BOUND_SITE_UNDECLARED";
    public static final String PLAN_FIELD = "retainedLoops";
    public static final String LOOP_BODY_BOUND_DISAGREES =
            "BOUNDED_LOOP_BODY_BOUND_DISAGREES";
    public static final int MAX_REPLAY_PATH_LOOP_BODIES = 32;
    public static final String K_L_REACHED = "MAX_LOOP_BODY_ITERATIONS_REACHED";
    public static final String WORK_CAP_REACHED = "REPLAY_LOOP_RESOURCE_CAP";
    public static final List<String> BOUND_REACHED = Collections
            .unmodifiableList(Arrays.asList(K_L_REACHED, WORK_CAP_REACHED));
    private static final int SCHEMA_VERSION = 1;
    private static final String DECLARED_FIELD = "loopBodyBounds";

    private final int defaultBackedgeTraversals;
    private final SortedMap<String, Integer> declared;
    private final int maxBackedgeTraversals;

    public static int workCap(int bound) {
        return Math.max(MAX_REPLAY_PATH_LOOP_BODIES, bound);
    }

    private LoopBoundPolicy(int defaultBackedgeTraversals,
                            Map<String, Integer> declared) {
        if (defaultBackedgeTraversals < 1) {
            throw new IllegalArgumentException(
                    "the inherited loop body bound must be at least one body "
                            + "execution, not " + defaultBackedgeTraversals);
        }
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

    public static LoopBoundPolicy cfgBackedges(
            int maxTraversals, Map<String, Integer> declared) {
        return new LoopBoundPolicy(maxTraversals, declared);
    }

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
        return new LoopBoundPolicy(
                optionalInteger(encoded, DEFAULT_FIELD, 0), declared);
    }

    public int maxBackedgeTraversals() { return maxBackedgeTraversals; }

    public int maxBackedgeTraversals(String loopSiteId) {
        Integer bound = loopSiteId == null ? null : declared.get(loopSiteId);
        return bound == null ? defaultBackedgeTraversals : bound.intValue();
    }

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
