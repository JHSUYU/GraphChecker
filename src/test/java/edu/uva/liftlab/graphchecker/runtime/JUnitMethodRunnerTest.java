package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

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
}
