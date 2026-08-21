package edu.uva.liftlab.graphchecker.runtime;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Mints the one dynamic activation identity of the pipeline and stamps it onto
 * the rows a recorded trace call named.
 *
 * <p>{@code occurrenceId} is {@code sourceKey/region/<regionId>#<ordinal>}.
 * The prefix is the <em>semantic</em> source of the activation: for a target
 * region that is the source of the event the selected failure branch was
 * observed on, which may differ from the source current when the root method
 * was entered.  The ordinal is counted over the <em>root</em> source instead,
 * which is the one both pipeline stages that mint this identity can read from
 * the same seed list.  Those two sources are deliberately different inputs; do
 * not collapse them.</p>
 *
 * <p>This ordinal is an identity inside one frozen plan and never a replay
 * address.  Replay addresses an occurrence by the stable selected source,
 * region root and incoming causal anchor its plan row carries; an ordinal
 * names a position in a sequence of activations, and a flipped branch that
 * adds or removes an earlier activation moves every position after it.</p>
 *
 * <p>An ordinal is reserved for every observed activation of a region, not
 * only for the ones a later failure closure retains: at replay every observed
 * root entry happens again, so a discarded activation still consumes its
 * position in the count.  Reservation is therefore independent of retention,
 * which is what lets the region finalizer and the region planner mint the same
 * identity from the same seed list at two different pipeline stages.</p>
 *
 * <p>Both stages hold their own minter over the same ordered activation seeds.
 * Ordinals are scoped by region, so a region only one stage knows about can
 * never shift another region's count.</p>
 */
public final class OccurrenceMinter {
    /**
     * Logical source of a workload whose tracing never registered one.  An
     * activation row that carries no source key was recorded under exactly
     * this declared default, never under an inferred one.
     */
    public static final String UNREGISTERED_SOURCE_KEY =
            RuntimeRegionPlanner.UNREGISTERED_SOURCE.key();

    private final Map<String, Integer> ordinals = new LinkedHashMap<>();
    private final Set<String> mintedActivations = new LinkedHashSet<>();
    private final Set<String> mintedOccurrences = new LinkedHashSet<>();

    /**
     * Reserves this activation's ordinal inside its root-source scope.  Call
     * it once per observed activation, in the recorded seed order, before any
     * retention decision is applied.
     *
     * <p>The counter is scoped by source and region and by nothing else,
     * which is the same pair {@link #occurrenceId} names.  An occurrence is
     * one dynamic activation of one region on one source; the plan defines no
     * per-request layer under that, so a request scope in the counter would
     * restart the count inside one source and mint one identity twice.</p>
     */
    public int reserveOrdinal(String rootSourceKey, String regionId) {
        return ordinals.merge(safe(rootSourceKey) + "\n" + safe(regionId), 1,
                Integer::sum);
    }

    /**
     * Mints the activation identity.  Two seeds naming one observed
     * activation, or two activations minting one occurrence, would corrupt
     * identity at the boundary where trace evidence is consumed; both fail
     * closed here.
     */
    public String mint(String regionId, long rootCallId,
                       String semanticSourceKey, int ordinal) {
        String occurrenceId = occurrenceId(semanticSourceKey, regionId,
                ordinal);
        if (!mintedActivations.add(safe(regionId) + "\n" + rootCallId)
                || !mintedOccurrences.add(occurrenceId)) {
            throw new IllegalArgumentException("duplicate runtime activation: "
                    + regionId + "#call" + rootCallId);
        }
        return occurrenceId;
    }

    /** The identity string, with no reservation or duplicate bookkeeping. */
    public static String occurrenceId(String semanticSourceKey,
                                      String regionId, int ordinal) {
        return safe(semanticSourceKey) + "/region/" + safe(regionId)
                + "#" + ordinal;
    }

    /**
     * Stamps a freshly minted occurrence onto every row the recorded root
     * call named for this activation: ports on both directions, the concrete
     * accesses they retain, and the boundary-scalar gaps observed inside it.
     *
     * <p>This is the one place a recorded trace call id selects rows.  After
     * it runs, an activation is addressed by {@code occurrenceId} alone, so
     * no later port, edge, slice, or demand decision can distinguish two
     * activations by a transient trace id.</p>
     */
    public static void bindOccurrence(Map<String, Object> region,
                                      long rootCallId, String occurrenceId) {
        if (region == null) return;
        bindPorts(rows(region.get("symbolicInputs")), rootCallId,
                occurrenceId);
        bindPorts(rows(region.get("outputs")), rootCallId, occurrenceId);
    }

    /** Stamps the occurrence onto the ports and accesses it owns. */
    public static void bindPorts(List<Map<String, Object>> ports,
                                 long rootCallId, String occurrenceId) {
        for (Map<String, Object> port : ports) {
            boolean owned = false;
            if (longNumber(port.get("rootCallId"), -1L) == rootCallId) {
                port.put("occurrenceId", occurrenceId);
                owned = true;
            }
            if (longNumber(port.get("toRootCallId"), -1L) == rootCallId) {
                port.put("toOccurrenceId", occurrenceId);
                owned = true;
            }
            if (longNumber(port.get("fromRootCallId"), -1L) == rootCallId) {
                port.put("fromOccurrenceId", occurrenceId);
                owned = true;
            }
            if (!owned) continue;
            // A retained access inherits the port's occurrence unless it
            // recorded a different activation of its own.
            for (Map<String, Object> access
                    : rows(port.get("runtimeAccesses"))) {
                if (!(access.get("rootCallId") instanceof Number)
                        || longNumber(access.get("rootCallId"), -1L)
                        == rootCallId) {
                    access.put("occurrenceId", occurrenceId);
                }
            }
        }
    }

    /**
     * Stamps the same occurrence onto the endpoints of every observed flow
     * that named this activation, so an edge resolves its producer and
     * consumer occurrences without ever looking up a trace call id.
     */
    public static void bindEdges(Collection<Map<String, Object>> regionEdges,
                                 String regionId, long rootCallId,
                                 String occurrenceId) {
        for (Map<String, Object> edge : regionEdges) {
            if (regionId.equals(text(edge.get("fromRegion")))
                    && longNumber(edge.get("fromRootCallId"), -1L)
                    == rootCallId) {
                edge.put("fromOccurrenceId", occurrenceId);
            }
            if (regionId.equals(text(edge.get("toRegion")))
                    && longNumber(edge.get("toRootCallId"), -1L)
                    == rootCallId) {
                edge.put("toOccurrenceId", occurrenceId);
            }
        }
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map<?, ?>) {
                    result.add((Map<String, Object>) item);
                }
            }
        }
        return result;
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static String text(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }
}
