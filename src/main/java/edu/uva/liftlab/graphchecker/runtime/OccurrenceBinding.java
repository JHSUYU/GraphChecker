package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import java.util.List;
import java.util.Map;

/**
 * Stamps the occurrence a recorded root call belongs to onto the rows it
 * named.
 *
 * <p>It computes no identity.  An occurrence address is computed exactly
 * once, by {@link Identity#occurrence}, at the entry where the activation
 * ran -- on the stock JDK for the recording and on the custom VM for every
 * replay -- and every later pass reads that string.  This class is the one
 * place a trace call id selects rows; afterwards an activation is addressed
 * by {@code occurrenceId} alone.</p>
 */
public final class OccurrenceBinding {
    /** Declared source of a workload whose tracing registered none. */
    public static final String UNREGISTERED_SOURCE_KEY =
            RuntimeRegionPlanner.UNREGISTERED_SOURCE.key();

    private OccurrenceBinding() {
    }

    /** Stamps one occurrence onto the ports of the region it activated. */
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

}
