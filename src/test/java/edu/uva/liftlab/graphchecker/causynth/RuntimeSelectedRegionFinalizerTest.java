package edu.uva.liftlab.graphchecker.causynth;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class RuntimeSelectedRegionFinalizerTest {
    @Test
    public void aClientsReadOrWritePairsAcrossNodesByObjectAlone() {
        Object[][] table = {
            {"auto0/master0#epoch0", "auto0/master0#epoch0", false, false, true},
            {"auto0/master0#epoch0", "auto0/rs0#epoch0", false, false, false},
            {"auto0/client0#epoch0", "auto0/master0#epoch0", true, false, true},
            {"auto0/master0#epoch0", "auto0/client0#epoch0", false, true, true},
            {"auto0/client0#epoch0", "auto1/client0#epoch0", true, true, true},
        };
        for (Object[] row : table) {
            assertEquals(row[0] + " read, " + row[1] + " wrote",
                    row[4], RuntimeSelectedRegionFinalizer.pairs(
                            (String) row[0], (String) row[1],
                            (Boolean) row[2], (Boolean) row[3]));
        }
    }
}
