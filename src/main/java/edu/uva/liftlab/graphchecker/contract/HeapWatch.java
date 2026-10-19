package edu.uva.liftlab.graphchecker.contract;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.lang.management.MemoryUsage;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.concurrent.atomic.AtomicLong;

public final class HeapWatch {
    public static final int OUT_OF_HEAP = 3;
    static final long WINDOW_MS = 60_000L;
    static final long LOOK_MS = 5_000L;
    static final double COLLECTING = 0.5;
    public static final double FULL = 0.9;

    private static final AtomicLong PEAK_SWEPT = new AtomicLong();

    private HeapWatch() {
    }

    public static void start() {
        Thread watch = new Thread(HeapWatch::watch, "engine-heap-watch");
        watch.setDaemon(true);
        watch.start();
    }

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

    public static double oldGenerationSwept() {
        MemoryPoolMXBean old = oldGeneration();
        MemoryUsage swept = old == null ? null : old.getCollectionUsage();
        return swept == null || swept.getMax() <= 0L ? 0.0
                : (double) swept.getUsed() / swept.getMax();
    }

    public static final double ROWS_PER_FILE_BYTE = 0.35;

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

    public static long[] takePeakSwept() {
        MemoryPoolMXBean old = oldGeneration();
        MemoryUsage swept = old == null ? null : old.getCollectionUsage();
        long now = swept == null ? 0L : swept.getUsed();
        long peak = Math.max(now, PEAK_SWEPT.getAndSet(now));
        return new long[] {peak, swept == null ? 0L : swept.getMax()};
    }

    public static long peakSwept() {
        MemoryPoolMXBean old = oldGeneration();
        MemoryUsage swept = old == null ? null : old.getCollectionUsage();
        return Math.max(swept == null ? 0L : swept.getUsed(),
                PEAK_SWEPT.get());
    }

    public static long liveAfterCollection() {
        System.gc();
        return ManagementFactory.getMemoryMXBean().getHeapMemoryUsage()
                .getUsed();
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
