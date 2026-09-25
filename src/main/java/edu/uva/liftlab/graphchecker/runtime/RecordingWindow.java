package edu.uva.liftlab.graphchecker.runtime;

/**
 * The recording window: the one moment both passes count from.
 *
 * <p>The workload opens it ({@code CausynthTraceRecorder.startRecording}),
 * not the engine and not a source registration.  Every count an address is
 * made of restarts here: a root hop's k ({@link Lineage}), site counts and
 * frame iterations ({@link Identity}), branch ordinals.  Counts before the
 * window are set-up history neither run controls.  A count files the index
 * it was taken in and is dropped when it counts in a later one.</p>
 */
final class RecordingWindow {
    private static volatile int index;

    private RecordingWindow() {
    }

    /** Which window this JVM is in: 0 until the workload opens one. */
    static int index() {
        return index;
    }

    /** Whether the workload has opened its window in this run. */
    static boolean opened() {
        return index > 0;
    }

    /** The workload opens its window: every count starts again here. */
    static void open() {
        index++;
    }

    /** Test seam: a fixture that models a run before its window. */
    static void reset() {
        index = 0;
    }
}
