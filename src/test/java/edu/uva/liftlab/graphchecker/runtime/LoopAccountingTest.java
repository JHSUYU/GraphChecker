package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * Loop bounds (PIPELINE §2): {@code K_L} counts the iterations of a loop
 * call that recorded a decision with a term -- the flips the loop offers --
 * and every iteration is work, cut past the resource cap (32 bodies, or a
 * declared {@code K_L} above it).  solr-adhoc-19 SG2b: CloudDescriptor's
 * loop over a core's properties, every decision concrete, cut the CREATE at
 * its 9th body, before the throw it declares.
 */
public class LoopAccountingTest {
    private static final String LOOP = "L#loop:u4";

    @Test
    public void kLCountsTheIterationsThatDecidedOnASymbol() {
        int cap = LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES;
        Object[][] rows = {
                // {why, K_L, termed decisions per iteration, traversal cut
                //  at (0: none), its reason}
                {"every iteration decides on a symbol: cut at K_L", 8,
                        ones(20), 8, "MAX_LOOP_BODY_ITERATIONS_REACHED"},
                {"no iteration decides on one: only the work cap", 8,
                        zeros(cap + 5), cap, "REPLAY_LOOP_RESOURCE_CAP"},
                {"12 concrete bodies, K_L 8: the loop runs whole", 8,
                        zeros(12), 0, ""},
                {"the first counts, then only the termed ones", 3,
                        new int[]{0, 0, 1, 0, 0, 1, 0}, 6,
                        "MAX_LOOP_BODY_ITERATIONS_REACHED"},
                {"a declared K_L above the cap raises it", 40, zeros(45), 40,
                        "REPLAY_LOOP_RESOURCE_CAP"}};
        for (Object[] row : rows) {
            LoopAccounting.LoopBackedgeBudget budget =
                    new LoopAccounting.LoopBackedgeBudget();
            int[] termed = (int[]) row[2];
            int total = 0;
            int cutAt = 0;
            String reason = "";
            for (int traversal = 1; traversal <= termed.length; traversal++) {
                total += termed[traversal - 1];
                Error cut = budget.traverse(LOOP, "key", total,
                        (Integer) row[1]);
                if (cut != null) {
                    cutAt = traversal;
                    reason = cut.getMessage().substring(0,
                            cut.getMessage().indexOf(' '));
                    break;
                }
            }
            assertEquals((String) row[0], row[3], cutAt);
            assertEquals((String) row[0], row[4], reason);
        }
    }

    /** A fixed-count loop's bodies take the same work cap a backedge's
     *  traversals do ({@link LoopBoundPolicy#workCap}): raised by a
     *  declared {@code K_L} above it, both cut at the same body. */
    @Test
    public void bothKindsOfLoopTakeOneWorkCap() {
        int[] bounds = {8, 40};
        for (int bound : bounds) {
            LoopAccounting.LoopBackedgeBudget budget =
                    new LoopAccounting.LoopBackedgeBudget();
            int bodyCut = 0;
            int traversalCut = 0;
            for (int body = 1; body <= 64 && bodyCut == 0; body++) {
                if (budget.body(LOOP, "fixed", bound) != null) bodyCut = body;
            }
            for (int traversal = 1; traversal <= 64 && traversalCut == 0;
                 traversal++) {
                // Traversal k enters body k + 1.
                if (budget.traverse(LOOP, "edge", 0, bound) != null) {
                    traversalCut = traversal + 1;
                }
            }
            assertEquals("K_L " + bound, LoopBoundPolicy.workCap(bound) + 1,
                    bodyCut);
            assertEquals("K_L " + bound, bodyCut, traversalCut);
        }
    }

    private static int[] ones(int n) {
        int[] values = new int[n];
        java.util.Arrays.fill(values, 1);
        return values;
    }

    private static int[] zeros(int n) {
        return new int[n];
    }
}
