import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater;

/**
 * A read of a tracked location states what it loaded, and whether that is
 * the word its observed version stored.
 *
 * <p>Writes outside every region are versioned where they happen, bytecode
 * or not: an AtomicInteger bumped by a thread with no context and a field
 * updater both write through Unsafe, whose compare-and-swap now publishes an
 * unattributed version in the same critical section as the concrete swap.
 * Solr's SolrCore.close() is the incident: the HTTP request's open()
 * increment ran before any region and left no version, so the region's
 * decrementAndGet resolved to a stale one.</p>
 *
 * <p>A write no hook sees -- here a store while the thread's recording is
 * paused -- still changes the heap.  The read that loads its word publishes
 * an UNOBSERVED version holding the loaded constant, and the location's
 * writer set is no longer complete; the read itself is exact, since it
 * returned exactly what that version holds.  When such a write puts back a
 * word a retained version stored, the read observes that version instead
 * (ABA) and publishes nothing new.</p>
 *
 * <p>Every such read states the value it returned when it is one -- a
 * primitive's constant, a String's content, or null -- which is what a
 * reader pins to when it cannot join its write.</p>
 */
public final class RegionLoadedValueSmoke {
    private static final class Core {
        volatile int count = 1;
    }

    private static final AtomicIntegerFieldUpdater<Core> COUNT =
            AtomicIntegerFieldUpdater.newUpdater(Core.class, "count");

    private static final class Input {
        int value = 3;
    }

    private static final class Named {
        String name;
    }

    private static final class Sink {
        int value;
        String name;
    }

    private static final String UNATTRIBUTED =
            "\"versionKind\":\"WRITE\",\"writerContextId\":0,"
            + "\"regionId\":\"\",\"taskId\":\"\",\"regionEnterEventId\":0";
    private static final String UNOBSERVED =
            "\"versionKind\":\"UNOBSERVED\",\"writerContextId\":0,"
            + "\"regionId\":\"\",\"taskId\":\"\",\"regionEnterEventId\":0";

    public static void main(String[] args) throws Exception {
        final Core core = new Core();
        final AtomicInteger refCount = new AtomicInteger(1);
        require(System.startConcolicRegion("REGION.loaded-value",
                "TASK.loaded-value") == 0L, "region start rejected");
        System.observeExactPrimitiveField(core, Core.class.getName(),
                "count", "I");
        System.observeExactPrimitiveField(refCount,
                AtomicInteger.class.getName(), "value", "I");

        Thread outside = new Thread(new Runnable() {
            @Override
            public void run() {
                COUNT.incrementAndGet(core);
                refCount.incrementAndGet();
            }
        });
        outside.start();
        outside.join();

        // The outside increment is a version: the read joins it, exactly.
        Sink sink = new Sink();
        sink.value = core.count;
        String read = expression(sink);

        // A store no hook sees: the read names it as an UNOBSERVED write.
        System.pauseConcolicPathCondition();
        core.count = 5;
        System.resumeConcolicPathCondition();
        sink.value = core.count;
        String unobserved = expression(sink);

        // An unseen store that puts back 2: the version that stored 2.
        System.pauseConcolicPathCondition();
        core.count = 2;
        System.resumeConcolicPathCondition();
        sink.value = core.count;
        String putBack = expression(sink);
        String field = System.getSharedFieldVersions(core,
                Core.class.getName(), "count", "I");

        // The atomic model: decrementAndGet read 2 and left 1.
        int left = refCount.decrementAndGet();
        String atomic = System.getSharedFieldVersions(refCount,
                AtomicInteger.class.getName(), "value", "I");

        // A String field a symbolic store started the log of.
        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "NAME_SOURCE");
        Named named = new Named();
        named.name = Integer.toString(input.value);
        sink.name = named.name;
        String stated = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "name", "Ljava/lang/String;",
                sink.name);
        named.name = null;
        sink.name = named.name;
        String nulled = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "name", "Ljava/lang/String;",
                sink.name);
        System.endConcolic();

        require(sink.value == 2 && left == 1,
                "the outside increments did not run");
        require(read.contains("\"versionKind\":\"WRITE\"")
                        && read.contains("\"writerSetComplete\":true")
                        && read.contains("\"observedExact\":true")
                        && count(read, "\"Y_I_2\"") == 1,
                "the read names no unattributed write, or states the word"
                        + " it returned twice: " + read);
        require(unobserved.contains("\"versionKind\":\"UNOBSERVED\"")
                        && unobserved.contains("\"writerSetComplete\":false")
                        && unobserved.contains("\"observedExact\":true")
                        && unobserved.contains("\"Y_I_5\""),
                "the read names no unobserved write: " + unobserved);
        require(putBack.contains("\"versionKind\":\"WRITE\"")
                        && putBack.contains("\"writerSetComplete\":false")
                        && putBack.contains("\"observedExact\":true"),
                "the put-back read names no retained version: " + putBack);
        require(count(field, UNOBSERVED) == 1
                        && count(field, UNATTRIBUTED) == 1
                        && field.contains("\"writerSetComplete\":false")
                        && field.contains(
                                "\"incompleteReason\":\"UNOBSERVED_WRITE\"")
                        && count(field, "\"readerContextId\"") == 3,
                "the field log is not INITIAL, WRITE, UNOBSERVED: " + field);
        int initial = atomic.indexOf("\"versionKind\":\"INITIAL\"");
        int outsideWrite = atomic.indexOf(UNATTRIBUTED);
        int rmw = atomic.indexOf("\"versionKind\":\"RMW\"");
        require(initial >= 0 && initial < outsideWrite && outsideWrite < rmw
                        && !atomic.contains("UNOBSERVED")
                        && atomic.contains("\"writerSetComplete\":true"),
                "the atomic's old value is not the outside write: " + atomic);
        require(stated.contains("\"_type\":\"ReadFromExpression\"")
                        && stated.contains("\"concreteValue\":\"3\""),
                "the String read states no value: " + stated);
        require(nulled.contains("\"_type\":\"ReadFromExpression\"")
                        && nulled.contains("\"concreteValue\":null"),
                "the null read states no value: " + nulled);
        System.out.println("RegionLoadedValueSmoke OK");
    }

    private static String expression(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "value", "I", Integer.valueOf(sink.value));
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
