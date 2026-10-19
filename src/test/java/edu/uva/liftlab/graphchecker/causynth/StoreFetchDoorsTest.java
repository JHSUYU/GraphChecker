package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.DoorsOnlyRoots;
import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class StoreFetchDoorsTest {
    @Test
    public void aDoorOccurrenceIsPlannedDoorsOnly() {
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        String[][] rows = {{"cp", "CONTROL_PRODUCER_V1"},
                {"fetch", "STORE_FETCH_V1"},
                {"writer", "SHARED_LOCATION_DEMAND_V1"},
                {"item", "STORE_ITEM_PRODUCER_V1"},
                {"wire", "WIRE_PRODUCER_V1"},
                {"root", "ROOT_RELEVANT_V1"}, {"target", ""},
                {"heavy", "SHARED_LOCATION_DEMAND_V1"},
                {"heavyTarget", ""}};
        for (String[] row : rows) {
            Map<String, Object> activation = new LinkedHashMap<>();
            if (!row[1].isEmpty()) {
                activation.put(RuntimeSelectedRegionFinalizer.ADMISSION_BASIS,
                        row[1]);
            }
            activation.put("regionId", row[0].startsWith("heavy")
                    ? "REGION.heavy" : "REGION." + row[0]);
            if (row[0].equals("heavyTarget")) {
                activation.put(
                        RuntimeSelectedRegionFinalizer.FAILURE_TARGET_OCCURRENCE,
                        true);
            }
            instances.put(row[0], activation);
        }
        assertEquals(3, RuntimeSelectedRegionFinalizer.stateDoorsOnly(
                instances, instances.keySet(),
                region -> region.equals("REGION.heavy") ? "<a.Core: void create()>"
                        : "<a.Other: void run()>",
                DoorsOnlyRoots.of("<a.Core: void create()>|<b.X: void y()>")));
        for (String[] row : rows) {
            boolean heavy = row[0].equals("heavy");
            assertEquals(row[0], row[1].equals("CONTROL_PRODUCER_V1")
                    || row[1].equals("STORE_FETCH_V1") || heavy,
                    instances.get(row[0]).containsKey(
                            RuntimeSelectedRegionFinalizer.DOORS_ONLY));
            assertEquals(row[0], heavy, instances.get(row[0]).containsKey(
                    RuntimeSelectedRegionFinalizer.DOORS_ONLY_DECLARED));
        }
    }
}
