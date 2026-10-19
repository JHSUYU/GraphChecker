package edu.uva.liftlab.graphchecker.runtime;

final class PoolWorkers {
    private static final String[][] GROWTH = {
            {"java.util.concurrent.ThreadPoolExecutor", "addWorker"},
            {"java.util.concurrent.ForkJoinPool", "createWorker"},
            {"org.eclipse.jetty.util.thread.QueuedThreadPool", "startThread"},
    };

    private PoolWorkers() {
    }

    static boolean constructing() {
        for (StackTraceElement frame : new Throwable().getStackTrace()) {
            for (String[] growth : GROWTH) {
                if (growth[0].equals(frame.getClassName())
                        && growth[1].equals(frame.getMethodName())) {
                    return true;
                }
            }
        }
        return false;
    }
}
