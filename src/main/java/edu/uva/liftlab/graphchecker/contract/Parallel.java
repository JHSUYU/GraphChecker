package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

/**
 * INDEPENDENT ITEMS ON A HOST'S CORES, THEIR RESULTS IN THE ITEMS' ORDER: a
 * parallel map over a fixed-order list, so whatever is made of the results
 * is what one thread taking the items in turn made of them, byte for byte.
 * An item is a function of what it is given and of state that is read-only
 * or safe to share; state that remembers the order it was asked in (a
 * session's lowering, the leaf set a seq's first row was asked for, {@code
 * explore.Corpus#leaves}) is held to one thread by an affinity ({@link
 * #grouped}): the items of one key run in their order on one thread, the
 * keys side by side.
 *
 * <p>A JVM computes on {@link #width} cores: one, unless its main is a
 * head step, one JVM alone on its host -- the planner ({@code ExploreMain}),
 * whose independent keys and rows take every core ({@link #HOST_CORES});
 * every other one (a host solver, a composition, a confirmation, a replay)
 * runs beside work the host ledger booked the other cores for.  Reads of
 * many small files take at least {@link #READS} at once (on NFS a read is
 * its latency: HR1 hdfs-adhoc-07's 1897 obligation workers, one after
 * another, two of COMPOSE's minutes), and a corpus's sessions, hundreds of
 * MB of rows each, {@link #READS} at a time (hdfs-11741 i1's 175 sessions
 * took 45-70 s one at a time).</p>
 */
public final class Parallel {
    /** The host's cores. */
    public static final int HOST_CORES =
            Runtime.getRuntime().availableProcessors();
    /** How many sessions are read at once, and directories at least. */
    public static final int READS = 8;
    /** The cores this JVM computes on ({@link #width(int)}). */
    private static volatile int width = 1;

    /** One item's work, failing as reading fails. */
    public interface Fn<F, T> {
        T apply(F from) throws IOException;
    }

    private Parallel() {
    }

    /** How many small files' directories are read at once: {@link
     *  #READS}, or {@link #width} where that is more. */
    public static int directoriesAtOnce() {
        return Math.max(READS, width);
    }

    /** This JVM computes on {@code cores} cores: a head step's main says
     *  its host's ({@link #HOST_CORES}). */
    public static void width(int cores) {
        width = Math.max(1, cores);
    }

    /** {@code fn} of each of {@code from} on {@link #width} cores, in
     *  {@code from}'s order; the first failure as it was thrown. */
    public static <F, T> List<T> map(List<F> from, Fn<F, T> fn)
            throws IOException {
        return map(from, fn, width);
    }

    /** {@link #map}, at most {@code atOnce} at a time. */
    public static <F, T> List<T> map(List<F> from, Fn<F, T> fn, int atOnce)
            throws IOException {
        Object[] done = new Object[from.size()];
        run(from.size(), atOnce, at -> done[at] = fn.apply(from.get(at)));
        return list(done);
    }

    /**
     * {@link #map} with an affinity: the items of one {@code key} run on one
     * thread in {@code from}'s order, so all that remembers its asking order
     * among them sees the order one thread taking all of {@code from} in
     * turn gave it; the keys run side by side, the largest first (the order
     * the keys run in decides nothing).
     */
    public static <F, T> List<T> grouped(List<F> from,
                                         Function<F, String> key,
                                         Fn<F, T> fn) throws IOException {
        Map<String, List<Integer>> byKey =
                new LinkedHashMap<String, List<Integer>>();
        for (int at = 0; at < from.size(); at++) {
            byKey.computeIfAbsent(key.apply(from.get(at)),
                    any -> new ArrayList<Integer>()).add(at);
        }
        List<List<Integer>> groups = new ArrayList<List<Integer>>(
                byKey.values());
        groups.sort((one, other) -> Integer.compare(other.size(),
                one.size()));
        Object[] done = new Object[from.size()];
        run(groups.size(), width, group -> {
            for (int at : groups.get(group)) {
                done[at] = fn.apply(from.get(at));
            }
        });
        return list(done);
    }

    /** What a {@link #stream} takes its items from: the next, or null when
     *  there is none left. */
    public interface Source<F> {
        F next() throws IOException;
    }

    /** What a {@link #stream} hands each result to, in order. */
    public interface Sink<T> {
        void take(T done) throws IOException;
    }

    /**
     * {@code fn} of each item {@code source} gives, on {@link #width} cores,
     * each result handed to {@code sink} in the order the items came.  This
     * thread takes the items and hands the results, so a source reading a
     * file and a sink writing one do nothing else, and at most {@link
     * #width} items are in hand at once: a file's text is never all held.
     * On one core, or for one item alone, it all runs here.  The items run
     * on one pool of the JVM's ({@link Streams}), so {@code fn} never
     * streams itself.
     */
    public static <F, T> void stream(Source<F> source, Fn<F, T> fn,
                                     Sink<T> sink) throws IOException {
        int ahead = width;
        if (ahead <= 1) {
            for (F item = source.next(); item != null; item = source.next()) {
                sink.take(fn.apply(item));
            }
            return;
        }
        F first = source.next();
        if (first == null) return;
        F second = source.next();
        if (second == null) {
            sink.take(fn.apply(first));
            return;
        }
        Deque<Future<T>> pending = new ArrayDeque<Future<T>>();
        try {
            pending.add(Streams.POOL.submit(() -> fn.apply(first)));
            for (F item = second; item != null; item = source.next()) {
                F one = item;
                pending.add(Streams.POOL.submit(() -> fn.apply(one)));
                if (pending.size() >= ahead) sink.take(done(pending.poll()));
            }
            while (!pending.isEmpty()) sink.take(done(pending.poll()));
        } finally {
            for (Future<T> left : pending) left.cancel(true);
        }
    }

    /** The streams' workers, one per core of the host, made as first asked
     *  and kept (a corpus read streams each file of every session it
     *  reads). */
    private static final class Streams {
        static final ExecutorService POOL = Executors.newFixedThreadPool(
                HOST_CORES, work -> {
                    Thread thread = new Thread(work, "stream");
                    thread.setDaemon(true);
                    return thread;
                });
    }

    /** One stream item's result, or its failure as it was thrown. */
    private static <T> T done(Future<T> future) throws IOException {
        try {
            return future.get();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("interrupted", interrupted);
        } catch (ExecutionException failed) {
            rethrow(failed.getCause());
            throw new IllegalStateException(failed);
        }
    }

    /** Work that runs beside this thread's ({@link #beside}). */
    public interface Action {
        void run() throws IOException;
    }

    /** Work started on a thread of its own, joined later: a file written
     *  while the round goes on computing ({@code ExploreMain#round}). */
    public static final class Beside {
        private final Thread thread;
        private volatile Throwable failed;

        private Beside(String name, Action action) {
            thread = new Thread(() -> {
                try {
                    action.run();
                } catch (Throwable thrown) {
                    failed = thrown;
                }
            }, name);
            thread.setDaemon(true);
            thread.start();
        }

        /** Waits for the work to end; its failure as it was thrown. */
        public void join() throws IOException {
            await();
            rethrow(failed);
        }

        /** Waits for the work to end, whatever it ended in. */
        public void await() {
            boolean interrupted = false;
            while (true) {
                try {
                    thread.join();
                    break;
                } catch (InterruptedException again) {
                    interrupted = true;
                }
            }
            if (interrupted) Thread.currentThread().interrupt();
        }
    }

    /** {@code action} on a thread of its own, from now on. */
    public static Beside beside(String name, Action action) {
        return new Beside(name, action);
    }

    /** A step's failure, as it was thrown; none, nothing. */
    private static void rethrow(Throwable thrown) throws IOException {
        if (thrown == null) return;
        if (thrown instanceof IOException) throw (IOException) thrown;
        if (thrown instanceof RuntimeException) {
            throw (RuntimeException) thrown;
        }
        if (thrown instanceof Error) throw (Error) thrown;
        throw new IOException(thrown);
    }

    /** One step of {@link #run}, by its index. */
    private interface Step {
        void run(int at) throws IOException;
    }

    /** Steps {@code 0..count-1} on at most {@code atOnce} threads, this one
     *  among them, each taking the next step as it finishes one; a failure
     *  stops the steps after it, every step before it runs, and the first
     *  failing step's failure is thrown as it was. */
    private static void run(int count, int atOnce, Step step)
            throws IOException {
        int threads = Math.min(atOnce, count);
        if (threads <= 1) {
            for (int at = 0; at < count; at++) step.run(at);
            return;
        }
        AtomicInteger next = new AtomicInteger();
        // The first failing step so far, and its failure.
        AtomicInteger firstAt = new AtomicInteger(Integer.MAX_VALUE);
        Throwable[] first = {null};
        Runnable worker = () -> {
            for (int at = next.getAndIncrement();
                 at < count && at < firstAt.get();
                 at = next.getAndIncrement()) {
                try {
                    step.run(at);
                } catch (Throwable thrown) {
                    synchronized (first) {
                        if (at < firstAt.get()) {
                            firstAt.set(at);
                            first[0] = thrown;
                        }
                    }
                }
            }
        };
        // Each with the JVM's own stack size (-Xss): the naming walks
        // recurse deep.
        Thread[] helpers = new Thread[threads - 1];
        for (int at = 0; at < helpers.length; at++) {
            helpers[at] = new Thread(worker, "parallel-" + at);
            helpers[at].setDaemon(true);
            helpers[at].start();
        }
        worker.run();
        boolean interrupted = false;
        for (Thread helper : helpers) {
            while (true) {
                try {
                    helper.join();
                    break;
                } catch (InterruptedException again) {
                    interrupted = true;
                }
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
        synchronized (first) {
            rethrow(first[0]);
        }
    }

    @SuppressWarnings("unchecked")
    private static <T> List<T> list(Object[] done) {
        return new ArrayList<T>((List<T>) Arrays.asList(done));
    }
}
