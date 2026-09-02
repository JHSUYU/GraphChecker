package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class JUnitMethodRunnerTest {
    private static final List<String> EVENTS = new ArrayList<>();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * The runner owns the workload's symbolic lifetime: it opens the session
     * before the JUnit method and closes it after. A stock JDK remains valid
     * for an unplanned seed run, while a configured replay fails before the
     * workload starts unless the complete current VM broker is present.
     * Closing while unwinding a failing workload must not replace the
     * workload's own failure, and a forced exit still stops leaked threads
     * with the status the workload earned.
     */
    @Test
    public void theRunnerOwnsTheWorkloadSessionWithoutChangingItsOutcome()
            throws Exception {
        String previous = System.getProperty(
                "causynth.junit.ignore.timeout");
        EVENTS.clear();
        try {
            System.setProperty("causynth.junit.ignore.timeout", "true");
            JUnitMethodRunner.main(new String[]{Fixture.class.getName(),
                    "workload"});
            assertEquals(Arrays.asList("before", "workload", "after"),
                    EVENTS);

            // A replay plan is the boundary where the complete current VM
            // broker becomes mandatory.
            EVENTS.clear();
            Path plan = folder.newFile().toPath();
            Files.write(plan, campaignTask("TASK.1").getBytes(
                    StandardCharsets.UTF_8));
            System.setProperty("causynth.concolic.task.plan",
                    plan.toString());
            System.setProperty("causynth.concolic.task.id", "TASK.1");
            System.setProperty("causynth.concolic.results",
                    folder.newFile().toPath().toString());
            ConcolicRegionRuntime.resetForTests();
            try {
                try {
                    JUnitMethodRunner.main(new String[]{
                            Fixture.class.getName(), "workload"});
                    fail("a stock JDK must refuse a configured replay");
                } catch (IllegalStateException failure) {
                    assertTrue(failure.getMessage(), failure.getMessage()
                            .contains("current custom VM broker capabilities"));
                }
                assertTrue(EVENTS.isEmpty());
            } finally {
                System.clearProperty("causynth.concolic.task.plan");
                System.clearProperty("causynth.concolic.task.id");
                System.clearProperty("causynth.concolic.results");
                ConcolicRegionRuntime.resetForTests();
            }

            EVENTS.clear();
            try {
                JUnitMethodRunner.main(new String[]{
                        LeakyFixture.class.getName(), "leaksAndFails"});
                fail("the workload failure must reach the caller");
            } catch (Throwable failure) {
                assertEquals("expected child failure", failure.getMessage());
            }
        } finally {
            if (previous == null) {
                System.clearProperty("causynth.junit.ignore.timeout");
            } else {
                System.setProperty("causynth.junit.ignore.timeout",
                        previous);
            }
            EVENTS.clear();
        }

        assertEquals(0, forcedProcess("leaksAndReturns"));
        assertEquals(1, forcedProcess("leaksAndFails"));
    }

    /** One minimal executable campaign row. */
    private static String campaignTask(String taskId) {
        return "{\"taskId\":\"" + taskId + "\",\"goalId\":\"GOAL." + taskId
                + "\",\"sourceKey\":\"TEST_DRIVER/test#epoch0\","
                + "\"occurrenceId\":"
                + "\"TEST_DRIVER/test#epoch0/region/REGION.1#1\","
                + "\"relationKey\":\"test/relation/" + taskId + "\","
                + "\"regionId\":\"REGION.1\","
                + "\"goalKind\":\"TARGET_REACH_CLOSURE\","
                + "\"rootSelector\":{\"kind\":\"RECEIVER_CONTEXT\","
                + "\"method\":\"<test.Worker: void run()>\","
                + "\"receiverClass\":\"java.lang.Object\","
                + "\"causalAnchor\":{"
                + "\"sourceKey\":\"TEST_DRIVER/test#epoch0\","
                + "\"kind\":\"REGISTERED_SOURCE\"}},"
                + "\"inputActions\":[],\"branches\":[],"
                + "\"loopBound\":{\"schemaVersion\":1,"
                + "\"kind\":\"CFG_BACKEDGE\","
                + "\"scope\":\"ALL_EXECUTION_SCOPE_LOOPS\","
                + "\"maxBackedgeTraversals\":8,\"onLimit\":\"CUT_PATH\"},"
                + "\"admission\":{\"state\":\"EXECUTABLE\"}}\n";
    }

    private static int forcedProcess(String method) throws Exception {
        String java = System.getProperty("java.home") + File.separator
                + "bin" + File.separator + "java";
        Process process = new ProcessBuilder(java,
                "-Dcausynth.junit.ignore.timeout=true",
                "-Dcausynth.junit.exit.after.run=true",
                "-cp", System.getProperty("java.class.path"),
                JUnitMethodRunner.class.getName(),
                LeakyFixture.class.getName(), method)
                .redirectErrorStream(true).start();
        if (!process.waitFor(10, TimeUnit.SECONDS)) {
            process.destroyForcibly();
            process.waitFor();
            fail("forced JUnit child did not exit");
        }
        return process.exitValue();
    }

    public static class Fixture {
        @Before
        public void before() {
            EVENTS.add("before");
        }

        public void workload() {
            EVENTS.add("workload");
        }

        @After
        public void after() {
            EVENTS.add("after");
        }
    }

    public static class LeakyFixture {
        public void leaksAndReturns() {
            leakThread();
        }

        public void leaksAndFails() {
            leakThread();
            throw new AssertionError("expected child failure");
        }

        private static void leakThread() {
            Thread thread = new Thread(() -> {
                try {
                    Thread.sleep(Long.MAX_VALUE);
                } catch (InterruptedException ignored) {
                    Thread.currentThread().interrupt();
                }
            }, "junit-runner-leak-fixture");
            thread.start();
        }
    }
}
