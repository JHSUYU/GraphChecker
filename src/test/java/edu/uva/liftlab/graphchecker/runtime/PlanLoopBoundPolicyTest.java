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
     */
    @Test
    public void rowsThatDeclareNothingInheritTheDefault() {
        LoopBoundPolicy policy = RuntimeRegionPlanner.declaredLoopBounds(
                Collections.singletonList(region(Arrays.asList(
                        loop(null, ADD_KEYS), loop(null, NEST_A)))));

        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals());
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals(ADD_KEYS));
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
