import java.util.concurrent.atomic.AtomicInteger;

/**
 * Concurrent stores and loads of a tracked location name no write that did
 * not happen.
 *
 * <p>A store used to publish its version after its concrete store and a load
 * to compare its word after its concrete load.  Two windows: a reader that
 * loaded the new word before its version landed, and one that loaded the
 * old word after it had, both found a word the newest version did not store
 * and minted a spurious UNOBSERVED write, making the location incomplete
 * for good.  The access and its log entry are now one critical section, so
 * a writer racing a reader leaves an exact log.  Two region threads
 * incrementing one atomic likewise linearize at the compare-and-swap that
 * versions them: each RMW's old value is the one before it.</p>
 */
public final class RegionTrackedRaceSmoke {
    private static final int WRITES = 60;
    private static final int INCREMENTS = 25;

    private static final class Cell {
        volatile int value;
    }

    private static volatile boolean done;

    public static void main(String[] args) throws Exception {
        final Cell cell = new Cell();
        final AtomicInteger atomic = new AtomicInteger();
        require(System.startConcolicRegion("REGION.race", "TASK.race") == 0L,
                "region start rejected");
        System.observeField(cell, Cell.class.getName(),
                "value", "I");
        System.observeField(atomic,
                AtomicInteger.class.getName(), "value", "I");

        Thread writer = region("REGION.race.writer", new Runnable() {
            public void run() {
                for (int index = 1; index <= WRITES; index++) {
                    cell.value = index;
                    atomic.getAndIncrement();
                }
                done = true;
            }
        });
        Thread reader = region("REGION.race.reader", new Runnable() {
            public void run() {
                int seen = 0;
                while (!done) {
                    seen += cell.value;
                }
                for (int index = 0; index < INCREMENTS; index++) {
                    atomic.getAndIncrement();
                }
                if (seen < 0) throw new AssertionError(seen);
            }
        });
        writer.start();
        reader.start();
        writer.join();
        reader.join();

        String field = System.getSharedFieldVersions(cell,
                Cell.class.getName(), "value", "I");
        String counter = System.getSharedFieldVersions(atomic,
                AtomicInteger.class.getName(), "value", "I");
        System.endConcolic();
        require(!field.contains("UNOBSERVED")
                        && field.contains("\"writerSetComplete\":true")
                        && count(field, "\"fieldVersionId\"") == WRITES + 1,
                "a racing reader named a write that did not happen: "
                        + field);
        require(atomic.get() == WRITES + INCREMENTS
                        && !counter.contains("UNOBSERVED")
                        && count(counter, "\"versionKind\":\"RMW\"") > 0,
                "a racing increment named a write that did not happen: "
                        + counter);
        System.out.println("RegionTrackedRaceSmoke OK");
    }

    private static Thread region(final String id, final Runnable body) {
        return new Thread(new Runnable() {
            public void run() {
                require(System.startConcolicRegion(id, "TASK.race") == 0L,
                        "region start rejected on " + id);
                try {
                    body.run();
                } finally {
                    System.endConcolic();
                }
            }
        });
    }

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
