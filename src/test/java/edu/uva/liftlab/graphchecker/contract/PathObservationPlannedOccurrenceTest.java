package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * OCC-1: a target address publishes one summary per activation, named
 * {@code <address>#a<ordinal>}.  The scheduler's seed selection and the
 * reach-query builder's scope test both match a per-activation summary against
 * the planned address, so the suffix is stripped to the address the campaign
 * scheduled.  A pre-OCC-1 occurrence, which carries no activation suffix, is
 * returned unchanged so single-occurrence rows compose exactly as before.
 */
public class PathObservationPlannedOccurrenceTest {

    private static final String ADDRESS =
            "cluster0/dn1#epoch1/region/REGION.d842447f#9";

    @Test
    public void anActivationSuffixIsStrippedToThePlannedAddress() {
        assertEquals(ADDRESS,
                PathObservation.plannedOccurrenceOf(ADDRESS + "#a1"));
        assertEquals(ADDRESS,
                PathObservation.plannedOccurrenceOf(ADDRESS + "#a3"));
        assertEquals(ADDRESS,
                PathObservation.plannedOccurrenceOf(ADDRESS + "#a46"));
    }

    @Test
    public void aPreOccOneOccurrenceIsUnchanged() {
        assertEquals(ADDRESS, PathObservation.plannedOccurrenceOf(ADDRESS));
        assertEquals("", PathObservation.plannedOccurrenceOf(""));
        assertEquals("", PathObservation.plannedOccurrenceOf(null));
    }

    @Test
    public void onlyATrailingIntegerActivationSuffixIsStripped() {
        // The region index "#9" is not an activation suffix.
        assertEquals(ADDRESS, PathObservation.plannedOccurrenceOf(ADDRESS));
        // "#a" with no ordinal, or a non-numeric ordinal, is not a suffix
        // this helper invented, so the string stands.
        assertEquals(ADDRESS + "#a",
                PathObservation.plannedOccurrenceOf(ADDRESS + "#a"));
        assertEquals(ADDRESS + "#ax",
                PathObservation.plannedOccurrenceOf(ADDRESS + "#ax"));
        // Only the last activation suffix is removed; a producer occurrence
        // id embedded earlier is left intact.
        assertEquals(ADDRESS + "#a2/child",
                PathObservation.plannedOccurrenceOf(ADDRESS + "#a2/child"));
    }
}
