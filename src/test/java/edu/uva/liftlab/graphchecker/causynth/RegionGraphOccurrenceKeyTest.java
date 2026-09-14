package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * The region graph joins on an address, and refuses anything else.
 *
 * <p>These joins decide which rows belong to one occurrence.  They did it by
 * string equality on {@code occurrenceId}, which is correct exactly while
 * every id they see is a planned address, and silently merges two activations
 * the moment one carries an {@code #a<n>} suffix -- the address drops the
 * suffix and the string does not.  Refusing is the point: a merge here is
 * invisible, and a graph that cannot be built says so.</p>
 */
public class RegionGraphOccurrenceKeyTest {
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#1";

    /** A planned address keys as itself: the migration is byte-neutral. */
    @Test
    public void aPlannedAddressKeysAsItself() {
        assertEquals(PLANNED,
                RuntimeSelectedRegionFinalizer.occurrenceKey(PLANNED));
    }

    /** An absent id is still absent, so the callers' early returns stand. */
    @Test
    public void anAbsentIdIsNotAnError() {
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(null));
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(""));
    }

    /** A per-activation id is refused rather than merged onto its address. */
    @Test
    public void anActivationSuffixIsRefused() {
        refuses(PLANNED + "#a1");
    }

    /** So is anything that does not spell an address at all. */
    @Test
    public void anUnreadableIdIsRefused() {
        refuses("REGION.9492ec77");
        refuses("hdfs-17960/nn0#epoch1/region/REGION.1");
        refuses("hdfs-17960/nn0#epoch1/region/REGION.1#0");
    }

    private static void refuses(String occurrenceId) {
        try {
            RuntimeSelectedRegionFinalizer.occurrenceKey(occurrenceId);
            fail("expected a refusal for " + occurrenceId);
        } catch (IllegalArgumentException refused) {
            assertEquals(true, refused.getMessage().contains(occurrenceId));
        }
    }
}
