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
        Path output = writeOutput(WorkloadJvm.OUTPUT_FILE_NAME,
                "2026-01-01 INFO  retrying",
                "org.apache.hadoop.ipc.RemoteException(java.io.IOException): "
                        + "File /tmp.txt could only be replicated to 0 nodes");

        TargetOutcome outcome = TargetOutcome.capture(traceDir, target,
                "encrypted-balancer", 1, output);

        assertTrue(outcome.usable());
        assertNull(outcome.diagnostic());
        assertEquals(1, outcome.junitExitCode());
        assertTrue(outcome.targetMethodReached());
        assertEquals(3, outcome.traceRecords());
        assertEquals(2, outcome.targetMethodRecords());
        assertEquals(1, outcome.targetThrowRecords());
        assertEquals(output.toString(), outcome.workloadOutput());
        assertTrue(gapsMention(outcome, "exited 1"));

        writeManifest(CLOSED);
        writeTrace(row("METHOD_ENTER", "<other.Class: void run()>", ""));

        TargetOutcome passing = TargetOutcome.capture(traceDir, target,
                "encrypted-balancer", 0, output);

        assertEquals(0, passing.junitExitCode());
        assertFalse(passing.usable());
        assertEquals(LauncherDiagnostic.TARGET_NOT_REACHED,
                passing.diagnostic());
        assertTrue(gapsMention(passing, target.methodKey()));
    }

    /**
     * A concolic replay's trace carries region and RPC rows and no method
     * envelope at all, because the union tree installs region hooks rather
     * than trace-recorder hooks. Whether the target ran is then not a
     * question this file can answer, and reporting it as
     * {@code TARGET_NOT_REACHED} is a false negative: campaign-takeover-10's
     * replay executed the target fifty times and was reported as never
     * reaching it.
     */
    @Test
    public void aTraceWithNoMethodEnvelopeCannotAnswerTheReachQuestion()
            throws Exception {
        writeManifest(CLOSED);
        writeTrace(
                "{\"schemaVersion\":3,\"event\":\"SOURCE_REGISTER\","
                        + "\"seq\":1,\"sourceKey\":\"cluster0/dn0#epoch0\"}",
                "{\"schemaVersion\":3,\"event\":\"RPC_SEND\",\"seq\":2}",
                row("CALL_SITE_ENTER", "<other.Class: void hook()>", ""));

        TargetOutcome outcome = TargetOutcome.capture(traceDir, target,
                "encrypted-balancer", 0, null);

        assertEquals(3, outcome.traceRecords());
        assertEquals(0, outcome.methodEnvelopeRecords());
        assertFalse(outcome.recordsMethodEnvelopes());
        assertFalse(outcome.targetMethodReached());
        assertEquals(LauncherDiagnostic.TARGET_REACH_UNRECORDED,
                outcome.diagnostic());
        assertTrue(gapsMention(outcome, "cannot say whether"));
        assertTrue(gapsMention(outcome, "region results"));
        // ... and the run is not unusable for it: the launcher would exit 1
        // and report a correct concolic replay as a failed pass.
        assertTrue(outcome.usable());
        assertTrue(outcome.toJson()
                .contains("\"kind\":\"SOURCE_FIRST_LAUNCHER_OUTCOME\""));

        // A pass that did record envelopes still answers the question, and
        // still answers it "no" when no row belongs to the target.
        writeManifest(CLOSED);
        writeTrace(row("METHOD_ENTER", "<other.Class: void run()>", ""));

        TargetOutcome observed = TargetOutcome.capture(traceDir, target,
                "encrypted-balancer", 0, null);

        assertEquals(1, observed.methodEnvelopeRecords());
        assertTrue(observed.recordsMethodEnvelopes());
        assertEquals(LauncherDiagnostic.TARGET_NOT_REACHED,
                observed.diagnostic());
        assertTrue(gapsMention(observed, "did observe the question"));
        assertFalse(observed.usable());
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
                        TargetOutcome.MANIFEST_FILE_NAME),
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
        Files.write(traceDir.resolve(TargetOutcome.TRACE_FILE_NAME),
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
