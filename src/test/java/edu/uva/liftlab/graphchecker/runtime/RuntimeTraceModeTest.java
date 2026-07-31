package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.After;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

public class RuntimeTraceModeTest {
    private static final String PROPERTY = "causynth.trace.mode";

    private String previousProperty;

    @Before
    public void saveProperty() {
        previousProperty = System.getProperty(PROPERTY);
        System.clearProperty(PROPERTY);
    }

    @After
    public void restoreProperty() {
        if (previousProperty == null) {
            System.clearProperty(PROPERTY);
        } else {
            System.setProperty(PROPERTY, previousProperty);
        }
    }

    @Test
    public void defaultsToFull() {
        String environment = System.getenv("CAUSYNTH_TRACE_MODE");
        Assume.assumeTrue(environment == null || environment.trim().isEmpty());
        assertEquals(RuntimeTraceMode.FULL, RuntimeTraceMode.configured());
    }

    @Test
    public void systemPropertySelectsMode() {
        System.setProperty(PROPERTY, "region-skeleton");
        assertEquals(RuntimeTraceMode.REGION_SKELETON,
                RuntimeTraceMode.configured());
    }

    @Test
    public void recognizesAliases() {
        assertAlias("skeleton", RuntimeTraceMode.REGION_SKELETON);
        assertAlias("REGION_SKELETON", RuntimeTraceMode.REGION_SKELETON);
        assertAlias("state", RuntimeTraceMode.REGION_STATE);
        assertAlias("inventory", RuntimeTraceMode.REGION_STATE);
        assertAlias("region_state", RuntimeTraceMode.REGION_STATE);
        assertAlias("rich", RuntimeTraceMode.FULL);
    }

    @Test
    public void rejectsUnknownMode() {
        System.setProperty(PROPERTY, "unexpected");
        try {
            RuntimeTraceMode.configured();
            fail("expected an unknown trace mode to be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("unexpected"));
        }
    }

    private static void assertAlias(String value, RuntimeTraceMode expected) {
        System.setProperty(PROPERTY, value);
        assertEquals(expected, RuntimeTraceMode.configured());
    }
}
