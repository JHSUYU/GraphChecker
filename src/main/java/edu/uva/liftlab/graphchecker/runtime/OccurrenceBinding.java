package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import java.util.List;
import java.util.Map;

/**
 * Stamps a recorded root call's occurrence onto the rows it named.
 *
 * <p>Computes no identity: {@link Identity#occurrence} computes it once, at
 * entry.  The one place a trace call id selects rows; afterwards an
 * activation is addressed by {@code occurrenceId} alone.</p>
 */
public final class OccurrenceBinding {
    public static final String UNREGISTERED_SOURCE_KEY =
            RuntimeRegionPlanner.UNREGISTERED_SOURCE.key();

    private OccurrenceBinding() {
    }

    public static void bindOccurrence(Map<String, Object> region,
                                      long rootCallId, String occurrenceId) {
        if (region == null) return;
        bindPorts(MapFields.rows(region.get("symbolicInputs")), rootCallId,
                occurrenceId);
        bindPorts(MapFields.rows(region.get("outputs")), rootCallId, occurrenceId);
    }

    /** Stamps the occurrence onto the ports it owns. */
    private static void bindPorts(List<Map<String, Object>> ports,
                                  long rootCallId, String occurrenceId) {
        for (Map<String, Object> port : ports) {
            if (MapFields.longNumber(port.get("rootCallId"), -1L)
                    == rootCallId) {
                port.put("occurrenceId", occurrenceId);
            }
        }
    }
}
