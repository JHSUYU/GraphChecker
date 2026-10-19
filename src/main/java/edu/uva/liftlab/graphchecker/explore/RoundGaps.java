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

final class RoundGaps implements Consumer<GapRow>, AutoCloseable {
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
    private final Digests seen = new Digests();
    private final Map<String, Integer> byKind =
            new LinkedHashMap<String, Integer>();
    private List<GapRow> batch = new ArrayList<GapRow>(BATCH);
    private volatile Throwable failed;

    RoundGaps(Path file) {
        this.file = file;
        this.runs = new RowCodec.Runs(file);
    }

    @Override
    public void accept(GapRow gap) {
        batch.add(gap);
        if (batch.size() == BATCH) hand();
    }

    void addAll(Collection<GapRow> gaps) {
        for (GapRow gap : gaps) accept(gap);
    }

    private void hand() {
        if (batch.isEmpty()) return;
        List<GapRow> rows = batch;
        batch = new ArrayList<GapRow>(BATCH);
        writer.execute(() -> take(rows));
    }

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

    Map<String, Integer> byKind() {
        return Collections.unmodifiableMap(byKind);
    }

    @Override
    public void close() {
        writer.shutdownNow();
    }

    private static final class Digests {
        private long[] slots = new long[2 * 1024];
        private int size;
        private boolean zero;

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
