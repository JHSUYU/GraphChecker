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

public final class Parallel {
    public static final int HOST_CORES =
            Runtime.getRuntime().availableProcessors();
    public static final int READS = 8;
    private static volatile int width = 1;

    public interface Fn<F, T> {
        T apply(F from) throws IOException;
    }

    private Parallel() {
    }

    public static int directoriesAtOnce() {
        return Math.max(READS, width);
    }

    public static void width(int cores) {
        width = Math.max(1, cores);
    }

    public static <F, T> List<T> map(List<F> from, Fn<F, T> fn)
            throws IOException {
        return map(from, fn, width);
    }

    public static <F, T> List<T> map(List<F> from, Fn<F, T> fn, int atOnce)
            throws IOException {
        Object[] done = new Object[from.size()];
        run(from.size(), atOnce, at -> done[at] = fn.apply(from.get(at)));
        return list(done);
    }

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

    public interface Source<F> {
        F next() throws IOException;
    }

    public interface Sink<T> {
        void take(T done) throws IOException;
    }

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

    private static final class Streams {
        static final ExecutorService POOL = Executors.newFixedThreadPool(
                HOST_CORES, work -> {
                    Thread thread = new Thread(work, "stream");
                    thread.setDaemon(true);
                    return thread;
                });
    }

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

    public interface Action {
        void run() throws IOException;
    }

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

        public void join() throws IOException {
            await();
            rethrow(failed);
        }

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

    public static Beside beside(String name, Action action) {
        return new Beside(name, action);
    }

    private static void rethrow(Throwable thrown) throws IOException {
        if (thrown == null) return;
        if (thrown instanceof IOException) throw (IOException) thrown;
        if (thrown instanceof RuntimeException) {
            throw (RuntimeException) thrown;
        }
        if (thrown instanceof Error) throw (Error) thrown;
        throw new IOException(thrown);
    }

    private interface Step {
        void run(int at) throws IOException;
    }

    private static void run(int count, int atOnce, Step step)
            throws IOException {
        int threads = Math.min(atOnce, count);
        if (threads <= 1) {
            for (int at = 0; at < count; at++) step.run(at);
            return;
        }
        AtomicInteger next = new AtomicInteger();
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
