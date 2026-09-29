import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater;

/**
 * A read of a tracked location states what it loaded.
 *
 * <p>A write no hook sees still changes what the location holds.  An
 * AtomicInteger bumped by a thread outside every region runs no atomic model
 * (the model needs a context), and a field updater writes through Unsafe;
 * neither leaves a version.  Solr's SolrCore.close() is the incident: the
 * HTTP request's open() increment ran before any region, the region's
 * decrementAndGet resolved to a stale version, and the term said
 * `count <= 0` while the run returned early.  A read that loads a word the
 * newest version did not store publishes an UNOBSERVED version holding the
 * loaded constant, with no writer, and the location's writer set is no
 * longer complete.  A second read of the same word finds that version and
 * publishes nothing.</p>
 *
 * <p>Every such read states the value it returned when it is one -- a
 * primitive's constant, a String's content, or null -- which is what a
 * reader pins to when it cannot join its write: SOLR-18406's read of a
 * String field whose observed write did not lower had nothing to pin to,
 * and the composition refused every path to the anchor.</p>
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

        // getfield: the heap holds 2, the newest version stored 1.
        Sink sink = new Sink();
        sink.value = core.count;
        String read = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        sink.value = core.count;
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
        require(read.contains("\"versionKind\":\"UNOBSERVED\"")
                        && read.contains("\"writerSetComplete\":false")
                        && read.contains("\"concreteValue\":{")
                        && read.contains("\"Y_I_2\""),
                "the read names no unobserved write: " + read);
        require(count(field, UNOBSERVED) == 1
                        && field.contains("\"writerSetComplete\":false")
                        && count(field, "\"readerContextId\"") == 2,
                "the field log states no single unobserved write: " + field);
        int initial = atomic.indexOf("\"versionKind\":\"INITIAL\"");
        int unobserved = atomic.indexOf(UNOBSERVED);
        int rmw = atomic.indexOf("\"versionKind\":\"RMW\"");
        require(initial >= 0 && initial < unobserved && unobserved < rmw
                        && count(atomic, UNOBSERVED) == 1
                        && atomic.contains("\"Y_I_2\"")
                        && atomic.contains("\"writerSetComplete\":false"),
                "the atomic's old value is not the unobserved write: "
                        + atomic);
        require(stated.contains("\"_type\":\"ReadFromExpression\"")
                        && stated.contains("\"concreteValue\":\"3\""),
                "the String read states no value: " + stated);
        require(nulled.contains("\"_type\":\"ReadFromExpression\"")
                        && nulled.contains("\"concreteValue\":null"),
                "the null read states no value: " + nulled);
        System.out.println("RegionLoadedValueSmoke OK");
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
