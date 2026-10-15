package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.carrotsearch.randomizedtesting.annotations.TestMethodProviders;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

import edu.uva.liftlab.graphchecker.contract.RowCodec;
import org.junit.Test;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.TestInfo;
import org.junit.jupiter.params.Parameter;
import org.junit.jupiter.params.ParameterizedClass;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.EnumSource;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * The one invocation of a parameterized test a case names, {@code m[k]}
 * ({@link JUnitInvocation}), run by the workload runner: which arguments
 * reach the method, the constructor and the {@code @Parameter} fields, and
 * what is refused by name before anything of the test runs; and which
 * method the adapter may run as the named test ({@link JUnitLifecycle}).
 */
public class JUnitInvocationTest {
    private static final List<String> LOG = new ArrayList<>();

    private static final Object[][] RUNS = {
            {Methods.class, "resolver[1]", "beforeEach", "resolver:null"},
            {Methods.class, "resolver[2]", "beforeEach", "resolver:trusted"},
            {Methods.class, "pair[2]", "beforeEach", "2two:[2] 2, two"},
            {Methods.class, "value[3]", "beforeEach", "value:7"},
            {Methods.class, "mode[2]", "beforeEach", "mode:BATCH"},
            {Methods.class, "plain", "beforeEach", "plain"},
            {Constructed.class, "simple[2]", "async:true"},
            {Constructed.class, "both[1][2]", "false:y"},
            {Injected.class, "fsck[2]", "provider:q"},
    };

    private static final Object[][] REFUSALS = {
            {Methods.class, "resolver", "names 0 invocation(s), but the test"
                    + " is parameterized at 1 level(s)"},
            {Methods.class, "plain[1]", "names 1 invocation(s), but the test"
                    + " is parameterized at 0 level(s)"},
            {Constructed.class, "simple", "parameterized at 1 level(s)"},
            {Methods.class, "resolver[0]", "not a test method name"},
            {Methods.class, "resolver[3]", "yield 2 invocation(s): there is"
                    + " no [3]"},
            {Methods.class, "empty[1]", "yield no invocation"},
            {Methods.class, "broken[1]", "threw"},
            {Methods.class, "csv[1]", "argument source @CsvSource"},
            {Methods.class, "converted[1]", "converts no argument"},
    };

    @Test
    public void theNamedInvocationRunsWithItsArguments() throws Exception {
        for (Object[] row : RUNS) {
            LOG.clear();
            run((Class<?>) row[0], (String) row[1]);
            assertEquals(row[1].toString(), Arrays.asList(row)
                    .subList(2, row.length), LOG);
        }
    }

    @Test
    public void anInvocationNotResolvedIsRefusedBeforeTheTestRuns() {
        for (Object[] row : REFUSALS) {
            LOG.clear();
            try {
                run((Class<?>) row[0], (String) row[1]);
                fail(row[1] + " must be refused");
            } catch (Exception refused) {
                assertTrue(row[1] + ": " + refused.getMessage(),
                        refused.getMessage().contains((String) row[2]));
            }
            assertEquals(row[1] + " ran nothing", Collections.emptyList(),
                    LOG);
        }
    }

    /** A replay held to a run of another invocation is refused by name; one
     *  of the same invocation runs. */
    @Test
    public void aReplayRunsTheInvocationItsRunRan() throws Exception {
        Path order = Files.createTempFile("schedule_prefix", ".jsonl");
        String before = System.getProperty(ScheduleLog.PREFIX_PROPERTY);
        try {
            System.setProperty(ScheduleLog.PREFIX_PROPERTY, order.toString());
            RowCodec.writeJsonl(order, Collections.singletonList(
                    RowCodec.writeScheduleInvocation("resolver[1](null)")));
            LOG.clear();
            run(Methods.class, "resolver[1]");
            assertEquals(Arrays.asList("beforeEach", "resolver:null"), LOG);
            LOG.clear();
            try {
                run(Methods.class, "resolver[2]");
                fail("another invocation than its run's must be refused");
            } catch (IllegalStateException refused) {
                assertTrue(refused.getMessage(), refused.getMessage().contains(
                        "runs invocation resolver[2](trusted)"));
            }
            assertEquals(Collections.emptyList(), LOG);
        } finally {
            if (before == null) {
                System.clearProperty(ScheduleLog.PREFIX_PROPERTY);
            } else {
                System.setProperty(ScheduleLog.PREFIX_PROPERTY, before);
            }
            Files.delete(order);
            ScheduleLog.resetForTests();
        }
    }

    /** An argument without a toString of its own renders by its class, not
     *  by an identity hash no other run shares. */
    @Test
    public void argumentsRenderAlikeInEveryRun() {
        assertEquals("null, 2, [1, 2], " + Methods.class.getName(),
                JUnitInvocation.rendered(new Object[] {null, 2,
                        new int[] {1, 2}, new Methods()}));
    }

    /** {test class, method, accepted}: Lucene's runner takes public
     *  test*() methods, JUnit 4's the marked ones. */
    @Test
    public void aTestMethodIsWhatTheClassRunnerTakes() throws Exception {
        Object[][] rows = {
            {Junit3.class, "testAddDocs", true},
            {Junit3.class, "helper", false},
            {Plain.class, "testAddDocs", false},
            {Plain.class, "marked", true}};
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

    /** A provider of JUnit 3 style methods, by its name. */
    public static final class FakeJUnit3MethodProvider {
    }

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

    private static void run(Class<?> workload, String name) throws Exception {
        JUnitLifecycle.run(new String[] {workload.getName(), name});
    }

    private static class Methods {
        enum Mode { SYNC, ASYNC, BATCH }

        static Collection<Object[]> data() {
            return Arrays.asList(new Object[] {null},
                    new Object[] {"trusted"});
        }

        static Stream<Arguments> pairs() {
            return Stream.of(Arguments.of(1, "one"), Arguments.of(2, "two"));
        }

        static List<String> none() {
            return Collections.emptyList();
        }

        static List<String> broken() {
            throw new IllegalStateException("the factory is down");
        }

        @BeforeEach
        void beforeEach() {
            LOG.add("beforeEach");
        }

        @ParameterizedTest
        @MethodSource("data")
        void resolver(String resolver) {
            LOG.add("resolver:" + resolver);
        }

        @ParameterizedTest
        @MethodSource("pairs")
        void pair(int number, String name, TestInfo info) {
            LOG.add(number + name + ":" + info.getDisplayName());
        }

        @ParameterizedTest
        @ValueSource(ints = {3, 5})
        @ValueSource(ints = 7)
        void value(int value) {
            LOG.add("value:" + value);
        }

        @ParameterizedTest
        @EnumSource(names = {"ASYNC", "BATCH"})
        void mode(Mode mode) {
            LOG.add("mode:" + mode);
        }

        @ParameterizedTest
        @MethodSource("none")
        void empty(String value) {
            LOG.add("empty");
        }

        @ParameterizedTest
        @MethodSource("broken")
        void broken(String value) {
            LOG.add("broken");
        }

        @ParameterizedTest
        @CsvSource("a,b")
        void csv(String first, String second) {
            LOG.add("csv");
        }

        @ParameterizedTest
        @ValueSource(strings = "7")
        void converted(int value) {
            LOG.add("converted");
        }

        @org.junit.jupiter.api.Test
        void plain() {
            LOG.add("plain");
        }
    }

    @ParameterizedClass
    @MethodSource("flags")
    private static class Constructed {
        private final Boolean async;

        Constructed(Boolean async) {
            this.async = async;
        }

        static Collection<Object[]> flags() {
            return Arrays.asList(new Object[] {Boolean.FALSE},
                    new Object[] {Boolean.TRUE});
        }

        @org.junit.jupiter.api.Test
        void simple() {
            LOG.add("async:" + async);
        }

        @ParameterizedTest
        @ValueSource(strings = {"x", "y"})
        void both(String value) {
            LOG.add(async + ":" + value);
        }
    }

    @ParameterizedClass
    @ValueSource(strings = {"p", "q"})
    private static class Injected {
        @Parameter(0)
        private String provider;

        @org.junit.jupiter.api.Test
        void fsck() {
            LOG.add("provider:" + provider);
        }
    }
}
