package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class DependencyRoleTest {
    @Test
    public void onlyValueFrontierExtendsSymbolicCausalClosure() {
        assertTrue(DependencyRole.causalFollow(
                DependencyRole.VALUE_FRONTIER));
        assertFalse(DependencyRole.causalFollow(
                DependencyRole.CONCRETE_STRUCTURE_CARRIER));
        assertTrue(DependencyRole.valueFrontier(
                DependencyRole.VALUE_FRONTIER));
        assertEquals(DependencyRole.VALUE_FRONTIER,
                DependencyRole.merge(
                        DependencyRole.CONCRETE_STRUCTURE_CARRIER,
                        DependencyRole.VALUE_FRONTIER));
    }

    @Test
    public void missingAndUnknownRolesFailClosed() {
        assertRejected(null);
        assertRejected("");
        assertRejected("VALUE");
    }

    private static void assertRejected(Object value) {
        try {
            DependencyRole.normalize(value);
            fail("role must be rejected: " + value);
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("dependencyRole"));
        }
    }
}
