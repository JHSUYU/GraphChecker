package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The plan stage measures every demanded branch replay stream against the
 * campaign's own {@code K_L}, and it has to derive that bound from the
 * declarations the planned rows already carry.
 *
 * <p>The rows here are the shape {@code RuntimeSelectedRegionFinalizer}
 * copies off a skeleton: a {@code retainedLoops} list whose entries carry
 * {@code loopControlSiteIds} and, when the campaign declared one, a
 * {@code loopBodyBound}.  A plan built from rows declaring {@code K_L=16}
 * that measured against {@link LoopBoundPolicy#MAX_LOOP_BODY_ITERATIONS}
 * would refuse a fifteen-event stream the campaign explicitly admitted.</p>
 */
public class PlanLoopBoundPolicyTest {
    private static final String ADD_KEYS =
            "<example.KeyStore: void addKeys(example.Exported)>#u20";
    private static final String NEST_A = "<example.Actor: void serve()>#u39";
    private static final String NEST_B = "<example.Actor: void serve()>#u189";

    private static Map<String, Object> loop(Object bound, String... sites) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, Arrays.asList(sites));
        if (bound != null) {
            row.put(LoopBoundPolicy.LOOP_BODY_BOUND, bound);
        }
        return row;
    }

    private static Map<String, Object> region(
            List<Map<String, Object>> loops) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(RuntimeSelectedRegionFinalizer.RETAINED_LOOPS, loops);
        return row;
    }

    /**
     * The declaration reaches the bound the plan stage measures against.
     * Without it every stream is measured at the inherited default, which is
     * what silently refused a region whose own campaign declared more.
     */
    @Test
    public void theCampaignBoundComesFromTheRowsBeingPlanned() {
        LoopBoundPolicy policy = RuntimeRegionPlanner.declaredLoopBounds(
                Arrays.asList(
                        region(Collections.singletonList(
                                loop(Integer.valueOf(16), ADD_KEYS))),
                        region(Collections.singletonList(
                                loop(Integer.valueOf(4), NEST_A, NEST_B)))));

        assertEquals(16, policy.maxBackedgeTraversals());
        assertEquals(16, policy.maxBackedgeTraversals(ADD_KEYS));
        assertEquals(4, policy.maxBackedgeTraversals(
                LoopBoundPolicy.loopSiteId(Arrays.asList(NEST_A, NEST_B))));
    }

    /**
     * A run that declares nothing states exactly that.  Rows without a
     * {@code loopBodyBound} declare nothing, so reading the inherited
     * default out of them would turn silence into a declaration.
     *
     * <p>What the contract then holds for those sites is nothing at all.
     * README {@code LOOP-1} accepts no retained condition loop running under
     * the core default, so the executor ceiling the run still enforces is not
     * an authority any case may be qualified by: the composition asks
     * {@link LoopBoundPolicy#declaredBounds()}, finds neither site, and names
     * both loops undeclared.</p>
     */
    @Test
    public void rowsThatDeclareNothingDeclareNothing() {
        LoopBoundPolicy policy = RuntimeRegionPlanner.declaredLoopBounds(
                Collections.singletonList(region(Arrays.asList(
                        loop(null, ADD_KEYS), loop(null, NEST_A)))));

        assertTrue(policy.declaredBounds().toString(),
                policy.declaredBounds().isEmpty());
        assertFalse(policy.declaredBounds().containsKey(ADD_KEYS));
        assertFalse(policy.declaredBounds().containsKey(NEST_A));
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals());
    }

    /**
     * A declared bound equal to the inherited one survives as a declaration.
     *
     * <p>The plan stage used to drop it as redundant.  Once an undeclared
     * condition loop is refused rather than run under the core default, that
     * drop is what refuses it: HDFS-11741's {@code offerService} nest
     * declares exactly {@link LoopBoundPolicy#MAX_LOOP_BODY_ITERATIONS}, and
     * a contract that forgot the declaration cannot tell it from silence.</p>
     */
    @Test
    public void aDeclaredBoundEqualToTheInheritedOneIsStillDeclared() {
        int inherited = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
        LoopBoundPolicy policy = RuntimeRegionPlanner.declaredLoopBounds(
                Collections.singletonList(region(Arrays.asList(
                        loop(Integer.valueOf(inherited), ADD_KEYS),
                        loop(Integer.valueOf(inherited), NEST_A, NEST_B)))));

        String nest = LoopBoundPolicy.loopSiteId(
                Arrays.asList(NEST_A, NEST_B));
        assertEquals(2, policy.declaredBounds().size());
        assertEquals(Integer.valueOf(inherited),
                policy.declaredBounds().get(ADD_KEYS));
        assertEquals(Integer.valueOf(inherited),
                policy.declaredBounds().get(nest));
        assertEquals(inherited, policy.maxBackedgeTraversals());
    }

    /**
     * One loop has one prefix.  Two rows declaring different bounds for one
     * site are refused rather than settled by which row was walked first.
     */
    @Test
    public void oneLoopDeclaredTwoWaysIsRefused() {
        try {
            RuntimeRegionPlanner.declaredLoopBounds(Arrays.asList(
                    region(Collections.singletonList(
                            loop(Integer.valueOf(16), ADD_KEYS))),
                    region(Collections.singletonList(
                            loop(Integer.valueOf(4), ADD_KEYS)))));
            org.junit.Assert.fail("expected the disagreement to be refused");
        } catch (IllegalStateException expected) {
            org.junit.Assert.assertTrue(expected.getMessage(),
                    expected.getMessage().contains(ADD_KEYS));
        }
    }
}
