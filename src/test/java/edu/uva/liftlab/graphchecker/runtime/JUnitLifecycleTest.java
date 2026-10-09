package edu.uva.liftlab.graphchecker.runtime;

import com.carrotsearch.randomizedtesting.annotations.TestMethodProviders;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/** Which method the adapter may run as the named test. */
public class JUnitLifecycleTest {
    /** A provider of JUnit 3 style methods, by its name. */
    public static final class FakeJUnit3MethodProvider {
    }

    /** Lucene's base: its runner takes public test*() methods. */
    @TestMethodProviders({FakeJUnit3MethodProvider.class})
    public static class Base {
    }

    public static class Junit3 extends Base {
        public void testAddDocs() {
        }

        public void helper() {
        }
    }

    public static class Plain {
        public void testAddDocs() {
        }

        @Test
        public void marked() {
        }
    }

    /** {test class, method, accepted}. */
    @Test
    public void aTestMethodIsWhatTheClassRunnerTakes() throws Exception {
        Object[][] rows = {
                {Junit3.class, "testAddDocs", true},
                {Junit3.class, "helper", false},
                {Plain.class, "testAddDocs", false},
                {Plain.class, "marked", true},
        };
        for (Object[] row : rows) {
            String detail = ((Class<?>) row[0]).getSimpleName() + "#" + row[1];
            try {
                assertEquals(detail, row[1], JUnitLifecycle.testMethod(
                        (Class<?>) row[0], (String) row[1]).getName());
                if (!(Boolean) row[2]) fail(detail + " was taken as a test");
            } catch (NoSuchMethodException refused) {
                if ((Boolean) row[2]) fail(detail + " was refused: " + refused);
            }
        }
    }
}
