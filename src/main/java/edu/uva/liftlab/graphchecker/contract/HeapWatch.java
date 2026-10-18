package edu.uva.liftlab.graphchecker.contract;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.lang.management.MemoryUsage;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.concurrent.atomic.AtomicLong;

/**
 * AN ENGINE JVM THAT ONLY COLLECTS IS OUT OF HEAP.  Past
 * {@link #COLLECTING} of a {@link #WINDOW_MS} window in the collector, its
 * old generation at least {@link #FULL} full after the collection that last
 * swept it, the JVM ends with {@link #OUT_OF_HEAP}, the status the campaign
 * runs a main again from at twice its heap (run_engine.sh
 * {@code campaign_jvm_out_of_heap_status}: {@code engine_java}, a served
 * planner's {@code campaign_planner_ended}).  The JVM's own overhead limit
 * never fires on such a heap: it also asks eden to stay full after a full
 * collection, which empties it (SGF7-adhoc-10's served planner at
 * -Xmx8192m: 5.6 GB of its old generation live, 543 full collections in
 * 10 minutes, a round unplanned for 30, under every GCTimeLimit and
 * GCHeapFreeLimit tried).
 */
public final class HeapWatch {
    /** run_engine.sh's {@code campaign_jvm_out_of_heap_status}. */
    public static final int OUT_OF_HEAP = 3;
    static final long WINDOW_MS = 60_000L;
    static final long LOOK_MS = 5_000L;
    static final double COLLECTING = 0.5;
    public static final double FULL = 0.9;

    /** The most the old generation held after a sweep, as the watch saw
     *  it, since {@link #takePeakSwept} last read it, in bytes. */
    private static final AtomicLong PEAK_SWEPT = new AtomicLong();

    private HeapWatch() {
    }

    /** Watches this JVM from a daemon thread of its own. */
    public static void start() {
        Thread watch = new Thread(HeapWatch::watch, "engine-heap-watch");
        watch.setDaemon(true);
        watch.start();
    }

    /** Whether a JVM that spent {@code collecting} of its window in the
     *  collector, its old generation {@code full} after its last sweep,
     *  is out of heap. */
    static boolean outOfHeap(double collecting, double full) {
        return collecting >= COLLECTING && full >= FULL;
    }

    private static void watch() {
        MemoryPoolMXBean old = oldGeneration();
        if (old == null) return;
        Deque<long[]> looks = new ArrayDeque<long[]>();
        while (true) {
            try {
                Thread.sleep(LOOK_MS);
            } catch (InterruptedException interrupted) {
                return;
            }
            long now = System.nanoTime() / 1_000_000L;
            looks.addLast(new long[] {now, collectedMillis()});
            while (looks.size() > 1
                    && now - looks.peekFirst()[0] > WINDOW_MS) {
                looks.removeFirst();
            }
            long[] first = looks.peekFirst();
            long span = now - first[0];
            MemoryUsage swept = old.getCollectionUsage();
            if (swept != null) {
                PEAK_SWEPT.accumulateAndGet(swept.getUsed(), Math::max);
            }
            if (span < WINDOW_MS - LOOK_MS || swept == null
                    || swept.getMax() <= 0L) {
                continue;
            }
            double collecting = (double) (looks.peekLast()[1] - first[1])
                    / span;
            double full = (double) swept.getUsed() / swept.getMax();
            if (outOfHeap(collecting, full)) {
                System.err.printf("engine-heap-watch: out of heap: %.0f %%"
                        + " of the last %d s in the collector, the old"
                        + " generation %.0f %% full after its last sweep;"
                        + " ends with %d%n", collecting * 100, span / 1000,
                        full * 100, OUT_OF_HEAP);
                System.err.flush();
                Runtime.getRuntime().halt(OUT_OF_HEAP);
            }
        }
    }

    /**
     * How full the old generation was after the collection that last swept
     * it, 0 before any: the room a stage that ends early by a named bound
     * reads ({@code compose.Composer#HEAP_SHARE}), the measure this watch
     * reads too.
     */
    public static double oldGenerationSwept() {
        MemoryPoolMXBean old = oldGeneration();
        MemoryUsage swept = old == null ? null : old.getCollectionUsage();
        return swept == null || swept.getMax() <= 0L ? 0.0
                : (double) swept.getUsed() / swept.getMax();
    }

    /**
     * How much of a session's files its rows hold once read, per byte of
     * their text (a gzip file's as it decodes, {@code
     * smt.ArtifactIO#decodedSize}): a steady third of them (0.32-0.37 over
     * six rounds of SGF8 05, 07, 10, 14 and 40, their files then plain).
     * What a round adds to the rows comes and goes (the walk's, the
     * frontier's per-session state: peaks of 0.57 to over 1.09 times the
     * files, in Frontier.<init> in three of the six), so no rule over the
     * files alone tells a corpus a JVM holds from one it does not (40: 16.2
     * GB of files out of a 21.5 GB heap; 05: 18.6 GB in it).
     */
    public static final double ROWS_PER_FILE_BYTE = 0.35;

    /**
     * WHETHER A JVM HOLDS ITS NEXT READ -- a served planner its next round,
     * a planner shard its next sessions: its live set at its highest since
     * it last asked ({@code peak}, {@link #takePeakSwept}) with {@link
     * #ROWS_PER_FILE_BYTE} of the session files it reads now ({@code
     * files}), against {@link #FULL} of its old generation ({@code old}),
     * where it would only collect.  Null when it holds it, else why not,
     * {@code who} named, the numbers in MB.  A JVM that measured nothing
     * yet ({@code old} 0) holds it.
     */
    public static String outgrown(String who, long peak, long old,
                                  long files) {
        if (old <= 0L) return null;
        long need = peak + (long) (ROWS_PER_FILE_BYTE * files);
        if (need <= FULL * old) return null;
        return who + " needs ~" + (need >> 20) + " MB of its " + (old >> 20)
                + " MB old generation: " + (peak >> 20) + " MB live at its "
                + "highest last round and " + ROWS_PER_FILE_BYTE + " of the "
                + (files >> 20) + " MB of session files it reads now, past "
                + Math.round(FULL * 100) + " % of it";
    }

    /**
     * The old generation's live set at its highest since the last read --
     * the most it held after a sweep, as the watch saw it every {@link
     * #LOOK_MS}, or after the sweep now -- in bytes, and its most: the
     * measure a served planner judges its next round's room by ({@link
     * #outgrown}).  Reading it starts the next span at what the old
     * generation holds now.
     */
    public static long[] takePeakSwept() {
        MemoryPoolMXBean old = oldGeneration();
        MemoryUsage swept = old == null ? null : old.getCollectionUsage();
        long now = swept == null ? 0L : swept.getUsed();
        long peak = Math.max(now, PEAK_SWEPT.getAndSet(now));
        return new long[] {peak, swept == null ? 0L : swept.getMax()};
    }

    /**
     * The old generation's live set at its highest since {@link
     * #takePeakSwept} last read it, in bytes, without starting a new span: a
     * served planner states it after each round, what its host is charged
     * for its next ({@code run_engine.sh campaign_planner_need_mb}).
     */
    public static long peakSwept() {
        MemoryPoolMXBean old = oldGeneration();
        MemoryUsage swept = old == null ? null : old.getCollectionUsage();
        return Math.max(swept == null ? 0L : swept.getUsed(),
                PEAK_SWEPT.get());
    }

    private static long collectedMillis() {
        long total = 0L;
        for (GarbageCollectorMXBean collector
                : ManagementFactory.getGarbageCollectorMXBeans()) {
            long time = collector.getCollectionTime();
            if (time > 0L) total += time;
        }
        return total;
    }

    /** The heap pool a full collection sweeps last: the largest heap pool
     *  that states its usage after a collection. */
    private static MemoryPoolMXBean oldGeneration() {
        MemoryPoolMXBean old = null;
        for (MemoryPoolMXBean pool
                : ManagementFactory.getMemoryPoolMXBeans()) {
            if (pool.getType() != MemoryType.HEAP
                    || pool.getCollectionUsage() == null) {
                continue;
            }
            if (old == null || pool.getUsage().getMax()
                    > old.getUsage().getMax()) {
                old = pool;
            }
        }
        return old;
    }
}
