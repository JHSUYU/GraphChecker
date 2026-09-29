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
 * it was taken in and is dropped when it counts in a later one.</p>
 */
final class RecordingWindow {
    private static volatile int index;
    private static volatile boolean closed;

    private RecordingWindow() {
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
    }

    /** The workload's test is over: what runs after is its teardown. */
    static void close() {
        closed = true;
    }

    /** Test seam: a fixture that models a run before its window. */
    static void reset() {
        index = 0;
        closed = false;
    }
}
