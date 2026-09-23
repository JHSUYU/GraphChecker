package edu.uva.liftlab.graphchecker.runtime;

/**
 * The recording window: the one moment both passes count from.
 *
 * <p>A workload starts its cluster, names its sources, and then opens the
 * window over the thing being recorded ({@code
 * CausynthTraceRecorder.startRecording}).  The recording states only what
 * happened inside the window, the plan counts activations from there, and a
 * replay is held to the window's schedule only -- so every count an address
 * is made of starts again here: a root hop's k ({@link Lineage}), a level's
 * site counts and a frame's iteration ({@link Identity}), an occurrence's
 * branch ordinals.  A count taken before the window is set-up history
 * neither run controls: hdfs-11741's balancer sends a varying number of
 * set-up RPCs under a request it opened before the window, so the first
 * send inside it was {@code @12} in the recording and something else in the
 * replay.</p>
 *
 * <p>It is the workload that opens it, not the engine, and not "a source has
 * been registered": hdfs-11741 registers the balancer, restarts the cluster,
 * and only then registers the new NameNode and opens the window, so a
 * replay counting from the registration numbered a NameNode generation the
 * recording never wrote a line for.  The index is 0 until the window opens;
 * a count files the index it was taken in and is dropped the first time it
 * counts in a later one.</p>
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
