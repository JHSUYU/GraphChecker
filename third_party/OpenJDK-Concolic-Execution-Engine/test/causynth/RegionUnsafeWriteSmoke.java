import java.lang.reflect.Field;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

/**
 * A write sun.misc.Unsafe performs is versioned, with the value its caller
 * stored.
 *
 * <p>Unsafe is muted and its writes are natives, so neither a bytecode hook
 * nor a model saw lazySet, a CAS through AtomicReference, or reflection's
 * Field.setInt: the location changed and the log did not.  The native now
 * versions the write in one critical section with it, and the value's
 * expression is the one its caller's operand carried, taken at the call
 * boundary before the muted call cleared it.</p>
 */
public final class RegionUnsafeWriteSmoke {
    private static final class Input {
        int n = 7;
        String name = "abc";
    }

    private static final class Holder {
        int value = 1;
    }

    private static final class Sink {
        int i;
    }

    public static void main(String[] args) throws Exception {
        require(System.startConcolicRegion("REGION.unsafe-write",
                "TASK.unsafe-write") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "n", "I",
                "UNSAFE.N");
        Sink sink = new Sink();

        // AtomicInteger.lazySet is Unsafe.putOrderedInt.
        AtomicInteger atomic = new AtomicInteger(0);
        System.observeField(atomic,
                AtomicInteger.class.getName(), "value", "I");
        atomic.lazySet(in.n);
        sink.i = atomic.get();
        String lazy = field(sink);
        String lazyLog = System.getSharedFieldVersions(atomic,
                AtomicInteger.class.getName(), "value", "I");
        require(sink.i == 7 && lazy.contains("UNSAFE.N")
                        && lazy.contains("\"observedExact\":true"),
                "lazySet's value is not the read's: " + lazy);
        require(lazyLog.contains("\"versionKind\":\"WRITE\"")
                        && lazyLog.contains("\"writerSetComplete\":true")
                        && !lazyLog.contains("UNOBSERVED"),
                "lazySet published no version: " + lazyLog);

        // Reflection's Field.setInt is Unsafe.putInt.
        Holder holder = new Holder();
        System.observeField(holder, Holder.class.getName(),
                "value", "I");
        Field value = Holder.class.getDeclaredField("value");
        value.setAccessible(true);
        value.setInt(holder, in.n + 1);
        sink.i = holder.value;
        String reflected = field(sink);
        require(sink.i == 8 && reflected.contains("UNSAFE.N")
                        && reflected.contains("\"observedExact\":true"),
                "Field.setInt's value is not the read's: " + reflected);

        // AtomicReference.compareAndSet is Unsafe.compareAndSwapObject.
        AtomicReference<String> reference = new AtomicReference<String>();
        System.symbolizeExactField(in, Input.class.getName(), "name",
                "Ljava/lang/String;", "UNSAFE.NAME");
        reference.set(in.name);
        require(reference.compareAndSet(in.name, "next"),
                "the compare-and-set failed");
        String log = System.getSharedFieldVersions(reference,
                AtomicReference.class.getName(), "value",
                "Ljava/lang/Object;");
        require(count(log, "\"writerContextId\"") == 2
                        && log.contains("\"versionKind\":\"RMW\"")
                        && log.contains("\"writerSetComplete\":true")
                        && !log.contains("UNOBSERVED"),
                "the compare-and-set published no version: " + log);

        System.endConcolic();
        System.out.println("RegionUnsafeWriteSmoke OK");
    }

    private static String field(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "i", "I", Integer.valueOf(sink.i));
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
