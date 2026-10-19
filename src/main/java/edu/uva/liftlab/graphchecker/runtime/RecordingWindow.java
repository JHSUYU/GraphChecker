package edu.uva.liftlab.graphchecker.runtime;

final class RecordingWindow {
    static final String DECLARED = "causynth.recording.window";
    static final String WINDOW_MS_FILE = "causynth.window.ms.file";
    private static volatile int index;
    private static volatile boolean closed;
    private static volatile long openedNanos;

    private RecordingWindow() {
    }

    static boolean atStartup() {
        return "startup".equals(System.getProperty(DECLARED));
    }

    static int index() {
        return index;
    }

    static boolean opened() {
        return index > 0 && !closed;
    }

    static void open() {
        index++;
        closed = false;
        openedNanos = System.nanoTime();
    }

    static void close() {
        closed = true;
        measured();
    }

    private static boolean stated;
    static final String CUT = "cut";

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
        }
    }

    static synchronized void reset() {
        index = 0;
        closed = false;
        stated = false;
    }
}
