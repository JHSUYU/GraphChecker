package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.fixtures.MixedTypeThreeThreadRpcWorkload;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The acceptance criterion is the trace, not the test's verdict, so these
 * tests deliberately cross the two: a failing JUnit method with usable
 * evidence, and a passing one with none.
 */
public class TargetOutcomeCaptureTest {

    private static final String CLOSED =
            "{\"schemaVersion\":1,\"kind\":\"STREAMING_RUNTIME_TRACE\","
                    + "\"status\":\"CLOSED\"}";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private WorkloadTarget target;
    private Path traceDir;
    private String targetMethod;

    @Before
    public void setUp() throws Exception {
        Path fixtures = Paths.get(MixedTypeThreeThreadRpcWorkload.class
                        .getProtectionDomain().getCodeSource().getLocation()
                        .toURI())
                .resolve("edu/uva/liftlab/graphchecker/fixtures");
        target = WorkloadTarget.resolve("multitype",
                Collections.singletonList(fixtures));
        targetMethod = "<" + target.site().className()
                + ": void executeWorker()>";
        traceDir = folder.newFolder("runtime").toPath();
    }

    @Test
    public void aFailingJUnitMethodWithAClosedTraceIsStillAUsableRun()
            throws Exception {
        writeManifest(CLOSED);
        writeTrace(
                row("METHOD_ENTER", "<other.Class: void run()>", ""),
                row("METHOD_ENTER", targetMethod, ""),
                row("METHOD_EXIT_THROW", targetMethod,
                        target.site().exceptionClass()));
        // A distributed workload logs throwables it recovered from long
        // before it fails, and keeps logging after the failure is printed.
        // What the record has to name is the last trace, and only when its
        // own header sits directly above it: reaching past the intervening
        // log lines to an earlier header would pair a stack with the wrong
        // failure.  The shape below is the real one - Hadoop's wrapped remote
        // exception, whose server-side frames are separated from the client's
        // by a blank line.
        Path output = writeOutput(WorkloadJvm.OUTPUT_FILE_NAME,
                "2026-01-01 INFO  retrying",
                "java.lang.IllegalStateException: an earlier, recovered fault",
                "\tat org.apache.hadoop.ipc.Client.call(Client.java:1433)",
                "2026-01-01 INFO  DataNode metrics system shutdown complete",
                "org.apache.hadoop.ipc.RemoteException(java.io.IOException): "
                        + "File /tmp.txt could only be replicated to 0 nodes",
                "\tat org.apache.hadoop.hdfs.BlockManager.choose(BM.java:2009)",
                "\tat org.apache.hadoop.ipc.Server$Handler.run(S.java:2659)",
                "",
                "\tat org.apache.hadoop.hdfs.DataStreamer.run(DS.java:734)");

        TargetOutcome outcome = TargetOutcomeCapture.capture(traceDir, target,
                "encrypted-balancer", 1, output);

        assertTrue(outcome.usable());
        assertNull(outcome.diagnostic());
        assertFalse(outcome.junitPassed());
        assertEquals(1, outcome.junitExitCode());
        assertTrue(outcome.targetMethodReached());
        assertTrue(outcome.targetExceptionObserved());
        assertEquals(3, outcome.traceRecords());
        assertEquals(2, outcome.targetMethodRecords());
        assertEquals(1, outcome.targetThrowRecords());
        assertEquals(output.toString(), outcome.workloadOutput());
        assertEquals("org.apache.hadoop.ipc.RemoteException",
                outcome.junitFailure().exceptionClass());
        assertEquals("File /tmp.txt could only be replicated to 0 nodes",
                outcome.junitFailure().message());
        assertEquals(2, outcome.junitFailure().frames().size());
        assertTrue(outcome.junitFailure().frames().get(0)
                .contains("BlockManager.choose"));
        assertTrue(outcome.toJson().contains("\"junitFailure\":{"));
        assertTrue(gapsMention(outcome,
                "exited 1 with org.apache.hadoop.ipc.RemoteException"));

        // A cause is printed under the throwable that wrapped it, and the
        // wrapper is what left the method.
        assertEquals("java.io.IOException",
                TargetOutcomeCapture.readFailure(writeOutput("wrapped.log",
                        "java.io.IOException: all datanodes are bad",
                        "\tat org.apache.hadoop.hdfs.DataStreamer.run(D:7)",
                        "Caused by: java.lang.IllegalStateException: none",
                        "\tat org.apache.hadoop.hdfs.BlockManager.c(B:12)",
                        "\t... 4 more")).exceptionClass());

        // A stack with no readable header of its own is a gap, not a guess.
        assertNull(TargetOutcomeCapture.readFailure(writeOutput("bare.log",
                "2026-01-01 INFO  a thread dump, not a throwable",
                "\tat org.apache.hadoop.ipc.Server$Handler.run(S.java:1)")));

        writeManifest(CLOSED);
        writeTrace(row("METHOD_ENTER", "<other.Class: void run()>", ""));

        TargetOutcome passing = TargetOutcomeCapture.capture(traceDir, target,
                "encrypted-balancer", 0, output);

        assertTrue(passing.junitPassed());
        assertNull(passing.junitFailure());
        assertFalse(passing.usable());
        assertEquals(LauncherDiagnostic.TARGET_NOT_REACHED,
                passing.diagnostic());
        assertTrue(gapsMention(passing, target.methodKey()));
    }

    private static boolean gapsMention(TargetOutcome outcome,
                                       String fragment) {
        for (String gap : outcome.gaps()) {
            if (gap.contains(fragment)) {
                return true;
            }
        }
        return false;
    }

    private void writeManifest(String json) throws IOException {
        Files.write(traceDir.resolve(
                        TargetOutcomeCapture.MANIFEST_FILE_NAME),
                json.getBytes(StandardCharsets.UTF_8));
    }

    private Path writeOutput(String name, String... lines)
            throws IOException {
        Path output = folder.getRoot().toPath().resolve(name);
        Files.write(output, (String.join("\n", lines) + "\n")
                .getBytes(StandardCharsets.UTF_8));
        return output;
    }

    private void writeTrace(String... lines) throws IOException {
        Files.write(traceDir.resolve(TargetOutcomeCapture.TRACE_FILE_NAME),
                (String.join("\n", lines) + "\n")
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static String row(String event, String method,
                              String runtimeType) {
        return "{\"schemaVersion\":3,\"event\":\"" + event
                + "\",\"seq\":1,\"method\":\"" + method
                + "\",\"runtimeType\":\"" + runtimeType + "\"}";
    }
}
