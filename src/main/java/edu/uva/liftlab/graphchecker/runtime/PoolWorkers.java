package edu.uva.liftlab.graphchecker.runtime;

/**
 * Whether the thread under construction is a pool's own worker.
 *
 * <p>A new thread inherits its creator's scope: lineage, execution index,
 * request flow.  A pool's worker is the exception.  The pool creates it
 * while some caller submits a task, and it then runs every later task of the
 * pool, each of which carries its own scope across the handoff.  Inherited,
 * the submitter's scope would sit under all of them, and it would be that of
 * whichever caller happened to grow the pool, at whatever depth: a timing,
 * not a cause.  So a worker starts in no scope but its node's.</p>
 */
final class PoolWorkers {
    /** The methods where a pool creates its workers: class, then method. */
    private static final String[][] GROWTH = {
            {"java.util.concurrent.ThreadPoolExecutor", "addWorker"},
            {"java.util.concurrent.ForkJoinPool", "createWorker"},
            {"org.eclipse.jetty.util.thread.QueuedThreadPool", "startThread"},
    };

    private PoolWorkers() {
    }

    /** From {@link InheritedState#inherit}, which {@code Thread.init} runs. */
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
