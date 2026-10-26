package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

public class EndOfRunTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final long END_SECONDS = 60L;

    @Test
    public void aDecidedReplayEndsAtOnceWithItsVerdictBehindItsClosedSession()
            throws Exception {
        Path worker = folder.newFolder("worker").toPath();
        Files.write(worker.resolve(ObligationDir.FOCUSED_TASK),
                (focusRow() + "\n").getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, (taskRow() + "\n").getBytes(
                StandardCharsets.UTF_8));
        Process jvm = workload("replay", worker,
                "-D" + FocusedReplay.PLAN_PROPERTY + "=" + plan,
                "-Dcausynth.concolic.task.id=TASK.1",
                "-Dcausynth.concolic.results="
                        + worker.resolve("concolic_region_results.jsonl"));
        assertEquals("the run's own status", 3, ended(jvm, worker));
        Path statement = worker.resolve(ObligationDir.REPLAY_VERDICT);
        assertTrue("the replay stated its verdict: " + log(worker),
                Files.isRegularFile(statement));
        assertFalse("whole, by one rename", Files.exists(worker.resolve(
                ObligationDir.REPLAY_VERDICT + ".part")));
        List<JsonObject> rows = RowCodec.readJsonl(statement);
        assertEquals(1, rows.size());
        assertEquals("OB", rows.get(0).get("obligationId").getAsString());
        String session = rows.get(0).get("sessionId").getAsString();
        Path closed = session.isEmpty()
                ? only(worker.resolve("refused-sessions"))
                : worker.resolve("sessions").resolve(session);
        assertTrue("the session's verdict rows precede the statement: "
                        + closed, RowCodec.readJsonl(closed.resolve(
                SessionDir.OBLIGATIONS)).toString()
                .contains("\"obligationId\":\"OB\""));
    }

    @Test
    public void aReplayEndsAtItsWindowsCloseAndRunsNoTeardown()
            throws Exception {
        Path worker = folder.newFolder("closed").toPath();
        Files.write(worker.resolve(ObligationDir.FOCUSED_TASK),
                (focusRow() + "\n").getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, (taskRow() + "\n").getBytes(
                StandardCharsets.UTF_8));
        Process jvm = workload("window", worker,
                "-D" + FocusedReplay.PLAN_PROPERTY + "=" + plan,
                "-Dcausynth.concolic.task.id=TASK.1",
                "-Dcausynth.concolic.results="
                        + worker.resolve("concolic_region_results.jsonl"));
        assertEquals("the close's own end", 0, ended(jvm, worker));
        assertFalse("no teardown: " + log(worker),
                log(worker).contains("teardown ran"));
        assertTrue("the replay stated its verdict: " + log(worker),
                Files.isRegularFile(worker.resolve(
                        ObligationDir.REPLAY_VERDICT)));
    }

    @Test
    public void aRecordingEndsAtOnceWithItsTraceClosed() throws Exception {
        Path trace = folder.newFolder("trace").toPath();
        Process jvm = workload("recording", trace,
                "-D" + RecordingWindow.WINDOW_MS_FILE + "="
                        + trace.resolve("window_ms"));
        assertEquals(3, ended(jvm, trace));
        assertTrue("its rows written: " + log(trace), new String(
                Files.readAllBytes(trace.resolve("runtime_trace.jsonl")),
                StandardCharsets.UTF_8).contains("its one row"));
        assertTrue("its trace closed", new String(Files.readAllBytes(
                trace.resolve("streaming_trace_manifest.json")),
                StandardCharsets.UTF_8).contains("\"CLOSED\""));
        assertTrue("its window measured", Files.isRegularFile(
                trace.resolve("window_ms")));
    }

    @Test
    public void aKilledNativeRunKeepsItsPlantRows() throws Exception {
        Path trace = folder.newFolder("native").toPath();
        Process jvm = workload("native", trace);
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(
                END_SECONDS);
        while (!log(trace).contains("planted")) {
            if (!jvm.isAlive() || System.nanoTime() > deadline) {
                jvm.destroyForcibly();
                fail("the native run never planted: " + log(trace));
            }
            Thread.sleep(50L);
        }
        jvm.destroy();
        if (!jvm.waitFor(2L, TimeUnit.SECONDS)) jvm.destroyForcibly();
        jvm.waitFor(END_SECONDS, TimeUnit.SECONDS);
        assertTrue("its plant row is in its trace: " + log(trace), new String(
                Files.readAllBytes(trace.resolve("runtime_trace.jsonl")),
                StandardCharsets.UTF_8).contains(RecordingPlant.FATAL));
    }

    @Test
    public void aJvmToldToEndBeforeItsRunStatesNothing() throws Exception {
        Path worker = folder.newFolder("told").toPath();
        Files.write(worker.resolve(ObligationDir.FOCUSED_TASK),
                (focusRow() + "\n").getBytes(StandardCharsets.UTF_8));
        Path plan = worker.resolve("execution_task_plan.jsonl");
        Files.write(plan, (taskRow() + "\n").getBytes(
                StandardCharsets.UTF_8));
        Process jvm = workload("told", worker,
                "-D" + FocusedReplay.PLAN_PROPERTY + "=" + plan,
                "-Dcausynth.concolic.task.id=TASK.1",
                "-Dcausynth.concolic.results="
                        + worker.resolve("concolic_region_results.jsonl"));
        assertEquals(3, ended(jvm, worker));
        assertFalse("no statement: " + log(worker), Files.exists(
                worker.resolve(ObligationDir.REPLAY_VERDICT)));
        assertTrue(log(worker).contains("was told to end"));
    }

    public static final class Workload {
        public static void main(String[] args) throws Exception {
            CountDownLatch shuttingDown = new CountDownLatch(1);
            Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                shuttingDown.countDown();
                parkForever();
            }, "a-cluster-teardown"));
            new Thread(Workload::parkForever, "a-cluster-thread").start();
            if ("native".equals(args[0])) {
                CausynthTraceRecorder.startRecording();
                CausynthTraceRecorder.plantFatal("<a.B: void run()>#u8",
                        "", true, false);
                System.out.println("planted");
                parkForever();
            } else if ("recording".equals(args[0])) {
                CausynthTraceRecorder.startRecording();
                CausynthTraceRecorder.recordingGap(GapKind.ADMISSION_GAP,
                        GapClass.DIAGNOSTIC, "recording", "its one row");
            } else {
                RowRuntime.configure(Paths.get(System.getProperty(
                        "causynth.concolic.results")));
            }
            if ("window".equals(args[0])) {
                CausynthTraceRecorder.startRecording();
                CausynthTraceRecorder.stopRecording();
                System.out.println("teardown ran");
                parkForever();
            }
            if ("told".equals(args[0])) {
                new Thread(() -> System.exit(0), "a-signal").start();
                shuttingDown.await();
            }
            JUnitMethodRunner.exit(3);
        }

        private static void parkForever() {
            while (true) {
                try {
                    Thread.sleep(Long.MAX_VALUE);
                } catch (InterruptedException ignored) {
                }
            }
        }
    }

    private static Process workload(String kind, Path dir,
                                    String... properties) throws Exception {
        List<String> command = new ArrayList<>(Arrays.asList(
                Paths.get(System.getProperty("java.home"), "bin", "java")
                        .toString()));
        command.addAll(Arrays.asList(properties));
        command.addAll(Arrays.asList("-cp",
                System.getProperty("java.class.path"),
                Workload.class.getName(), kind));
        ProcessBuilder builder = new ProcessBuilder(command)
                .redirectErrorStream(true)
                .redirectOutput(dir.resolve("jvm.log").toFile());
        boolean traced = "recording".equals(kind) || "native".equals(kind);
        builder.environment().put("CAUSYNTH_CONCOLIC_WORKER_DIR",
                traced ? "" : dir.toString());
        builder.environment().put("CAUSYNTH_CONCOLIC_SESSIONS",
                traced ? "" : dir.resolve("sessions").toString());
        builder.environment().put("CAUSYNTH_TRACE_MODE",
                traced ? "discovery" : "replay-context");
        builder.environment().put("CAUSYNTH_TRACE_OUTPUT_DIR",
                dir.toString());
        return builder.start();
    }

    private static int ended(Process jvm, Path dir) throws Exception {
        if (!jvm.waitFor(END_SECONDS, TimeUnit.SECONDS)) {
            jvm.destroyForcibly();
            fail("the workload JVM did not end in " + END_SECONDS
                    + " s; its teardown held it: " + log(dir));
        }
        return jvm.exitValue();
    }

    private static String log(Path dir) throws Exception {
        File log = dir.resolve("jvm.log").toFile();
        return log.exists() ? new String(Files.readAllBytes(log.toPath()),
                StandardCharsets.UTF_8) : "(no log)";
    }

    private static Path only(Path dir) throws Exception {
        File[] entries = dir.toFile().listFiles();
        assertTrue("one entry in " + dir, entries != null
                && entries.length == 1);
        return entries[0].toPath();
    }

    private static String focusRow() {
        String focus = "hdfs/dn0#epoch0/region/REGION.1/ctx:Root:TICK#1/idx:"
                + "<a.B: void run()>@0";
        return "{\"taskId\":\"TASK.1\",\"obligationId\":\"OB\","
                + "\"pathId\":\"p\",\"focused\":\"" + focus + "\","
                + "\"focusedOccurrenceId\":\""
                + OccurrenceAddress.parse(focus).id() + "\",\"seedSessionId\":"
                + "\"seed\",\"flip\":{\"siteId\":\"<a.B: void run()>#u8\","
                + "\"ordinal\":1,\"outcome\":true},\"inheritedFlips\":[],"
                + "\"rootAssignments\":{},\"clockDeltas\":{},\"answers\":{},"
                + "\"rootMints\":{}}";
    }

    private static JsonObject taskRow() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "hdfs/nn0#epoch0");
        encoded.addProperty("occurrenceId",
                "hdfs/nn0#epoch0/region/REGION.1#1");
        encoded.addProperty("rootMethod", "<a.B: void run()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", "<a.B: void run()>");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "hdfs/nn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branchMethods", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("defaultBackedgeTraversals", 8);
        encoded.add("loopBound", loopBound);
        return encoded;
    }
}
