package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * Many directories of one iteration read at once, in their order: on NFS a
 * read is its latency, and parsing the rows is the rest (hdfs-11741 i1's
 * 175 sessions took 45-70 s one at a time; HR1 hdfs-adhoc-07's 1897
 * obligation workers, one after another, two of COMPOSE's minutes).
 */
final class ParallelReads {
    /** How many are read at once. */
    private static final int AT_ONCE = 8;

    /** One read, failing as reading fails. */
    interface Read<F, T> {
        T read(F from) throws IOException;
    }

    private ParallelReads() {
    }

    /**
     * {@code read} of each of {@code from}, at most {@link #AT_ONCE} at a
     * time, in {@code from}'s order; the first failure as it was thrown.
     */
    static <F, T> List<T> each(List<F> from, Read<F, T> read, Object of)
            throws IOException {
        List<T> done = new ArrayList<T>(from.size());
        if (from.isEmpty()) return done;
        ExecutorService readers = Executors.newFixedThreadPool(
                Math.min(AT_ONCE, from.size()));
        try {
            List<Future<T>> reading = new ArrayList<Future<T>>();
            for (F one : from) {
                reading.add(readers.submit(() -> read.read(one)));
            }
            for (Future<T> one : reading) {
                done.add(one.get());
            }
            return done;
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("interrupted while reading " + of,
                    interrupted);
        } catch (ExecutionException failed) {
            Throwable cause = failed.getCause();
            if (cause instanceof IOException) throw (IOException) cause;
            if (cause instanceof RuntimeException) {
                throw (RuntimeException) cause;
            }
            throw new IOException(cause);
        } finally {
            readers.shutdownNow();
        }
    }
}
