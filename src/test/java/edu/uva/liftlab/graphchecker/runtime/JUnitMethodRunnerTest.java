package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class JUnitMethodRunnerTest {
    private static final List<String> EVENTS = new ArrayList<>();

    @Test
    public void directModeKeepsJUnitLifecycleWithoutTimeoutRunner()
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
        } finally {
            if (previous == null) {
                System.clearProperty("causynth.junit.ignore.timeout");
            } else {
                System.setProperty("causynth.junit.ignore.timeout",
                        previous);
            }
            EVENTS.clear();
        }
    }

    @Test
    public void forcedProcessExitStopsLeakedThreadsOnSuccessAndFailure()
            throws Exception {
        assertEquals(0, forcedProcess("leaksAndReturns"));
        assertEquals(1, forcedProcess("leaksAndFails"));
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
