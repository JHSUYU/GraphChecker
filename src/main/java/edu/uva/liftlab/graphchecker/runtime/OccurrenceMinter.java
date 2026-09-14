package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
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
 * <p>{@code occurrenceId} is {@code sourceKey/region/<regionId>#<ordinal>},
 * where the prefix is the <em>semantic</em> source of the activation (for a
 * target region, the source of the event the selected failure branch was
 * observed on) and the ordinal counts over that same source.  It is an
 * identity inside one frozen plan and never a replay address: replay addresses
 * an occurrence by the stable source, region root and causal anchor its plan
 * row carries.  An ordinal is reserved for every observed activation, retained
 * or not, so retention never renumbers the activations that survive it.</p>
 */
public final class OccurrenceMinter {
    /** Declared source of a workload whose tracing registered none. */
    public static final String UNREGISTERED_SOURCE_KEY =
            RuntimeRegionPlanner.UNREGISTERED_SOURCE.key();

    private final Map<String, Integer> ordinals = new LinkedHashMap<>();
    private final Set<String> mintedActivations = new LinkedHashSet<>();
    private final Set<String> mintedOccurrences = new LinkedHashSet<>();

    /**
     * Reserves this activation's ordinal, once per observed activation, in
     * recorded activation order and before any retention decision.  The
     * counter is scoped by source and region and by nothing else - the same pair
     * {@link #occurrenceId} names - because a narrower scope would restart the
     * count inside one source and mint one identity twice.
     */
    public int reserveOrdinal(String semanticSourceKey, String regionId,
                              String requestFamily) {
        return ordinals.merge(MapFields.safe(semanticSourceKey) + "\n"
                        + MapFields.safe(regionId) + "\n"
                        + MapFields.safe(requestFamily), 1,
                Integer::sum);
    }

    /**
     * Mints the activation identity.  Two records naming one observed
     * activation, or two activations minting one occurrence, would corrupt
     * identity at the boundary where trace evidence is consumed; both fail
     * closed here.
     */
    public String mint(String regionId, long rootCallId,
                       String semanticSourceKey, String requestFamily,
                       int ordinal) {
        String occurrenceId = occurrenceId(semanticSourceKey, regionId,
                requestFamily, ordinal);
        if (!mintedActivations.add(MapFields.safe(regionId) + "\n" + rootCallId)
                || !mintedOccurrences.add(occurrenceId)) {
            throw new IllegalArgumentException("duplicate runtime activation: "
                    + regionId + "#call" + rootCallId);
        }
        return occurrenceId;
    }

    /**
     * The identity string, with no reservation or duplicate bookkeeping.
     *
     * <p>Rendered by {@link OccurrenceAddress} itself rather than
     * concatenated here, so the one place that knows the grammar -- including
     * whether a request family is written at all -- is the address.</p>
     */
    public static String occurrenceId(String semanticSourceKey,
                                      String regionId, String requestFamily,
                                      int ordinal) {
        return OccurrenceAddress.of(MapFields.safe(semanticSourceKey),
                MapFields.safe(regionId), MapFields.safe(requestFamily),
                ordinal).render();
    }

    /**
     * Stamps a freshly minted occurrence onto every row the recorded root call
     * named.  This is the one place a trace call id selects rows: afterwards
     * an activation is addressed by {@code occurrenceId} alone.
     */
    public static void bindOccurrence(Map<String, Object> region,
                                      long rootCallId, String occurrenceId) {
        if (region == null) return;
        bindPorts(MapFields.rows(region.get("symbolicInputs")), rootCallId,
                occurrenceId);
        bindPorts(MapFields.rows(region.get("outputs")), rootCallId, occurrenceId);
    }

    /** Stamps the occurrence onto the ports and accesses it owns. */
    public static void bindPorts(List<Map<String, Object>> ports,
                                 long rootCallId, String occurrenceId) {
        for (Map<String, Object> port : ports) {
            boolean owned = false;
            if (MapFields.longNumber(port.get("rootCallId"), -1L) == rootCallId) {
                port.put("occurrenceId", occurrenceId);
                owned = true;
            }
            if (MapFields.longNumber(port.get("toRootCallId"), -1L) == rootCallId) {
                port.put("toOccurrenceId", occurrenceId);
                owned = true;
            }
            if (MapFields.longNumber(port.get("fromRootCallId"), -1L) == rootCallId) {
                port.put("fromOccurrenceId", occurrenceId);
                owned = true;
            }
            if (!owned) continue;
            // A retained access inherits the port's occurrence unless it
            // recorded a different activation of its own.
            for (Map<String, Object> access
                    : MapFields.rows(port.get("runtimeAccesses"))) {
                if (!(access.get("rootCallId") instanceof Number)
                        || MapFields.longNumber(access.get("rootCallId"), -1L)
                        == rootCallId) {
                    access.put("occurrenceId", occurrenceId);
                }
            }
        }
    }

    /** Stamps the occurrence onto the endpoints of the flows it named. */
    public static void bindEdges(Collection<Map<String, Object>> regionEdges,
                                 String regionId, long rootCallId,
                                 String occurrenceId) {
        for (Map<String, Object> edge : regionEdges) {
            if (regionId.equals(MapFields.stringValue(edge.get("fromRegion")))
                    && MapFields.longNumber(edge.get("fromRootCallId"), -1L)
                    == rootCallId) {
                edge.put("fromOccurrenceId", occurrenceId);
            }
            if (regionId.equals(MapFields.stringValue(edge.get("toRegion")))
                    && MapFields.longNumber(edge.get("toRootCallId"), -1L)
                    == rootCallId) {
                edge.put("toOccurrenceId", occurrenceId);
            }
        }
    }

}
