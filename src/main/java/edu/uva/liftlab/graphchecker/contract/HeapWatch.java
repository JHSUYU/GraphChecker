package edu.uva.liftlab.graphchecker.contract;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.lang.management.MemoryUsage;
import java.util.ArrayDeque;
import java.util.Deque;

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
    static final double FULL = 0.9;

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
