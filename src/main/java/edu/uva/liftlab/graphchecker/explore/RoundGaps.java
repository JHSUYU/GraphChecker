package edu.uva.liftlab.graphchecker.explore;

import com.google.common.hash.HashFunction;
import com.google.common.hash.Hashing;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;

/**
 * A ROUND'S GAPS AS THE ROUND SAYS THEM ({@link ExploreMain#round}): each
 * distinct row once, in the order it was first said, rendered and deflated
 * on a thread of their own as the round goes on, never held as rows --
 * SGF8-adhoc-05 round 5 said 345 K gaps, 1 GB of text its planner held to
 * the round's end -- and written whole at its end ({@link #write}), byte for
 * byte the file {@link RowCodec#writeAll} writes of their distinct list,
 * counted by kind for the round's manifest ({@link #byKind}).  A row is its
 * line ({@link RowCodec#writeGap} renders every part), and distinct by its
 * line's 128-bit digest.  One thread says them.
 */
final class RoundGaps implements Consumer<GapRow>, AutoCloseable {
    /** How many rows are handed to the writer at once. */
    private static final int BATCH = 1024;
    private static final HashFunction DIGEST = Hashing.murmur3_128();

    private final ExecutorService writer = Executors.newSingleThreadExecutor(
            work -> {
                Thread thread = new Thread(work, "round-gaps");
                thread.setDaemon(true);
                return thread;
            });
    private final Path file;
    private final RowCodec.Runs runs;
    /** The digests of the rows written. */
    private final Digests seen = new Digests();
    /** kind -> its distinct rows, in the order each kind was first said. */
    private final Map<String, Integer> byKind =
            new LinkedHashMap<String, Integer>();
    private List<GapRow> batch = new ArrayList<GapRow>(BATCH);
    /** What the writer failed on, thrown at {@link #write}. */
    private volatile Throwable failed;

    /** The gaps of the file {@code file} names (gzip by its name). */
    RoundGaps(Path file) {
        this.file = file;
        this.runs = new RowCodec.Runs(file);
    }

    /** One gap said. */
    @Override
    public void accept(GapRow gap) {
        batch.add(gap);
        if (batch.size() == BATCH) hand();
    }

    /** Gaps said in their order. */
    void addAll(Collection<GapRow> gaps) {
        for (GapRow gap : gaps) accept(gap);
    }

    /** The batch said so far, to the writer. */
    private void hand() {
        if (batch.isEmpty()) return;
        List<GapRow> rows = batch;
        batch = new ArrayList<GapRow>(BATCH);
        writer.execute(() -> take(rows));
    }

    /** On the writer: each new row's line into the file's runs. */
    private void take(List<GapRow> rows) {
        if (failed != null) return;
        try {
            for (GapRow gap : rows) {
                byte[] line = RowCodec.toLine(RowCodec.writeGap(gap))
                        .getBytes(StandardCharsets.UTF_8);
                ByteBuffer digest = ByteBuffer.wrap(
                        DIGEST.hashBytes(line).asBytes());
                if (!seen.add(digest.getLong(0), digest.getLong(8))) continue;
                byKind.merge(gap.kind().name(), 1, Integer::sum);
                runs.add(line);
            }
        } catch (Throwable thrown) {
            failed = thrown;
        }
    }

    /** Writes the file, once every gap said is in it. */
    void write() throws IOException {
        hand();
        writer.shutdown();
        boolean interrupted = false;
        while (true) {
            try {
                if (writer.awaitTermination(1, TimeUnit.MINUTES)) break;
            } catch (InterruptedException again) {
                interrupted = true;
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
        if (failed instanceof IOException) throw (IOException) failed;
        if (failed instanceof RuntimeException) {
            throw (RuntimeException) failed;
        }
        if (failed instanceof Error) throw (Error) failed;
        if (failed != null) throw new IOException(failed);
        runs.write(file);
    }

    /** kind -> how many distinct rows of it the file holds, each kind in
     *  the order it was first said; whole once {@link #write} returned. */
    Map<String, Integer> byKind() {
        return Collections.unmodifiableMap(byKind);
    }

    /** Ends the writer, whatever the round came to. */
    @Override
    public void close() {
        writer.shutdownNow();
    }

    /** 128-bit digests, two longs each, open addressing. */
    private static final class Digests {
        private long[] slots = new long[2 * 1024];
        private int size;
        private boolean zero;

        /** Whether {@code (high, low)} was not held, holding it. */
        boolean add(long high, long low) {
            if (high == 0 && low == 0) {
                boolean added = !zero;
                zero = true;
                return added;
            }
            if (2 * (size + 1) > slots.length / 2) grow();
            if (!put(slots, high, low)) return false;
            size++;
            return true;
        }

        private static boolean put(long[] slots, long high, long low) {
            int mask = slots.length / 2 - 1;
            for (int at = (int) (high ^ (high >>> 32)) & mask; ;
                 at = (at + 1) & mask) {
                long heldHigh = slots[2 * at];
                long heldLow = slots[2 * at + 1];
                if (heldHigh == 0 && heldLow == 0) {
                    slots[2 * at] = high;
                    slots[2 * at + 1] = low;
                    return true;
                }
                if (heldHigh == high && heldLow == low) return false;
            }
        }

        private void grow() {
            long[] larger = new long[2 * slots.length];
            for (int at = 0; at < slots.length; at += 2) {
                if (slots[at] != 0 || slots[at + 1] != 0) {
                    put(larger, slots[at], slots[at + 1]);
                }
            }
            slots = larger;
        }
    }
}
