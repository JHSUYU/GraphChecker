package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

/** OCC-1 grammar: one address, optionally the activation that ran it. */
public class OccurrenceIdTest {
    private static final String ADDRESS =
            "hdfs-17960/nn0#epoch1/region/REGION.3cdc7049#1";

    @Test
    public void activationSuffixSplitsOffTheAddressAndRendersBack() {
        OccurrenceId parsed = OccurrenceId.parse(ADDRESS + "#a7");

        assertEquals(ADDRESS, parsed.planned());
        assertEquals(ADDRESS + "#a7", parsed.render());
    }

    @Test
    public void plannedDropsTheActivationAndWithActivationRestoresOne() {
        OccurrenceId parsed = OccurrenceId.parse(ADDRESS + "#a3");

        assertEquals(ADDRESS + "#a1",
                parsed.withActivation(1).render());
        assertEquals(ADDRESS + "#a12",
                OccurrenceId.parse(ADDRESS).withActivation(12).render());
    }
}
