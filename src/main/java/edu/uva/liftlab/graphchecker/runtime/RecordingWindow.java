package edu.uva.liftlab.graphchecker.runtime;

/**
 * The recording window: the one moment both passes count from, until the
 * workload's test is over.
 *
 * <p>The workload opens it ({@code CausynthTraceRecorder.startRecording}),
 * not the engine and not a source registration, and may close it when its
 * test is over ({@code stopRecording}): its teardown is neither recorded
 * nor held.  Every count an address is
 * made of restarts here: a root hop's k ({@link Lineage}), site counts and
 * frame iterations ({@link Identity}), branch ordinals.  Counts before the
 * window are set-up history neither run controls.  A count files the index
 * it was taken in; counted in a later one, a site it reached starts again at
 * 1, its earlier entries standing at 0 ({@code Identity.Counters#reopened}),
 * and every other count is dropped.</p>
 *
 * <p>Where the workload opens it is its system's adapter's: once its cluster
 * is up, or -- for a case that declares it ({@link #atStartup}), whose fatal
 * value is set while the cluster starts -- before the cluster starts.</p>
 */
final class RecordingWindow {
    /**
     * The JVM property a case's {@code recording_window} sets on every
     * workload JVM of its run (experiments/lib/execute.sh).
     */
    static final String DECLARED = "causynth.recording.window";
    /**
     * The JVM property naming the file the window's wall duration, in ms,
     * is written to when it closes (experiments/lib/execute.sh: the
     * recording's trace directory, a replay's worker directory): the
     * campaign's measured slowdown of the VM over the recording is the
     * ratio of the two ({@code run_engine.sh campaign_view_hold_max},
     * {@code Confirmation#VIEW_HOLD_MAX_PROPERTY}).
     */
    static final String WINDOW_MS_FILE = "causynth.window.ms.file";
    private static volatile int index;
    private static volatile boolean closed;
    private static volatile long openedNanos;

    private RecordingWindow() {
    }

    /**
     * Whether the case declares its window open before its cluster starts
     * ({@code recording_window=startup}): an opt-in for a bug whose fatal
     * value is set during startup (HBase's master activation time), which a
     * window opened once the cluster is up never records.
     */
    static boolean atStartup() {
        return "startup".equals(System.getProperty(DECLARED));
    }

    /** Which window this JVM is in: 0 until the workload opens one. */
    static int index() {
        return index;
    }

    /**
     * Whether the workload has opened its window in this run.  Trap: source
     * registration is not the window (a restart may sit between them).
     */
    static boolean opened() {
        return index > 0 && !closed;
    }

    /** The workload opens its window: every count starts again here. */
    static void open() {
        index++;
        closed = false;
        openedNanos = System.nanoTime();
    }

    /** The workload's test is over: what runs after is its teardown.  The
     *  window's wall duration is stated ({@link #measured}). */
    static void close() {
        closed = true;
        measured();
    }

    /** Whether the window's duration was stated. */
    private static boolean stated;
    /** What marks a window the run ended inside ({@link #measured}). */
    static final String CUT = "cut";

    /**
     * States the window's wall duration, once, to {@link #WINDOW_MS_FILE}
     * when named: from its open to its close, or -- a run that ends inside
     * it (a replay ended early: at its witness, a refusal or a stall) --
     * to now, marked {@value #CUT}: a cut window measured only part of the
     * workload's, which the campaign names (run_engine.sh
     * campaign_view_hold_max).  The run's one end calls it ({@code
     * JUnitMethodRunner#exit}: {@code ConcolicResultPublisher
     * #publishRunTotals}, {@code CausynthTraceRecorder#closeTrace}); a run
     * that never opened its window states nothing, and the campaign fails
     * by name.
     */
    static synchronized void measured() {
        String file = System.getProperty(WINDOW_MS_FILE, "");
        if (stated || file.isEmpty() || index == 0) return;
        stated = true;
        long millis = (System.nanoTime() - openedNanos) / 1_000_000L;
        try {
            java.nio.file.Files.write(java.nio.file.Paths.get(file),
                    (millis + (closed ? "" : "\t" + CUT) + "\n").getBytes(
                            java.nio.charset.StandardCharsets.UTF_8));
        } catch (java.io.IOException | RuntimeException unwritten) {
            // Unwritten, the campaign fails by name when it reads it.
        }
    }

    /** Test seam: a fixture that models a run before its window. */
    static synchronized void reset() {
        index = 0;
        closed = false;
        stated = false;
    }
}
