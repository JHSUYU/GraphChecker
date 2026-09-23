package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * The window rule for root k: a TURN begun before the recording window is
 * the set-up's and stands at 0 inside it; a request the workload opened
 * before its window keeps its k.
 */
public class LineageWindowTest {
    @Before
    public void reset() {
        Lineage.resetForTests();
    }

    @After
    public void tearDown() {
        Lineage.resetForTests();
    }

    @Test
    public void aTurnBegunBeforeTheWindowIsNotTheWindowsFirstTurn() {
        Role actor = Role.of("BP_SERVICE_ACTOR");
        long before = Lineage.pushRoot("hdfs/dn0", actor, "");
        assertEquals("before the window it is the loop's first turn", 1,
                Lineage.rootWindowIndex());
        Lineage.openWindow();
        assertEquals("inside the window it is the set-up's turn", 0,
                Lineage.rootWindowIndex());
        Lineage.pop(before);
        long first = Lineage.pushRoot("hdfs/dn0", actor, "");
        assertEquals("the window's own first turn is #1", 1,
                Lineage.rootWindowIndex());
        Lineage.pop(first);
    }

    @Test
    public void aRequestOpenedBeforeTheWindowKeepsItsK() {
        long request = Lineage.push("hdfs/balancer", Role.CLIENT,
                "balance-block");
        Lineage.openWindow();
        assertEquals("the workload decides how many requests it opens", 1,
                Lineage.rootWindowIndex());
        Lineage.pop(request);
    }
}
