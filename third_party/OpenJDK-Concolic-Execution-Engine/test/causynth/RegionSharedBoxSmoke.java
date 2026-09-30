import java.util.HashMap;
import java.util.Map;

/**
 * A JVM-wide object never carries a region's expression.
 *
 * <p>Character.valueOf('a') is one object for the whole JVM (the 0..127
 * cache), and so are Boolean.TRUE and FALSE.  valueOf of a symbolic value put
 * the expression on that object, and so did a container read that returned
 * one; every later use of it -- in any code, on any thread -- unboxed to the
 * region's value.  The value now rides the slot that holds the box, which is
 * where the unboxing reads it back; the shared object stays clean.  (This
 * JDK's Integer/Long/Short/Byte/Boolean.valueOf box afresh.)</p>
 */
public final class RegionSharedBoxSmoke {
    private static final class Input {
        char c = 'a';
        int n = 1;
    }

    private static final class Sink {
        char c;
        boolean z;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.shared-box",
                "TASK.shared-box") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "c", "C",
                "BOX.C");
        System.symbolizeExactField(in, Input.class.getName(), "n", "I",
                "BOX.N");
        Sink sink = new Sink();

        Character boxed = Character.valueOf(in.c);
        sink.c = boxed.charValue();
        require(field(sink, "c", "C", Character.valueOf(sink.c))
                        .contains("BOX.C"),
                "the box's value did not reach its unboxing");
        Character other = Character.valueOf('a');
        require(other == boxed, "'a' is not the cached box");
        sink.c = other.charValue();
        require(!field(sink, "c", "C", Character.valueOf(sink.c))
                        .contains("BOX.C"),
                "a concrete valueOf('a') unboxed to the region's value");
        require(System.getSymbolicExpression(other)
                        .contains("\"symbolic\":false"),
                "the cached Character carries an expression");

        Map<Integer, Boolean> flags = new HashMap<Integer, Boolean>();
        flags.put(Integer.valueOf(1), Boolean.TRUE);
        Boolean got = flags.get(Integer.valueOf(in.n));
        require(got == Boolean.TRUE, "the map did not return Boolean.TRUE");
        sink.z = got.booleanValue();
        String read = field(sink, "z", "Z", Boolean.valueOf(sink.z));
        require(read.contains("BOX.N"),
                "the container result's value did not reach its unboxing: "
                        + read);
        sink.z = Boolean.TRUE.booleanValue();
        require(!field(sink, "z", "Z", Boolean.valueOf(sink.z))
                        .contains("BOX.N"),
                "Boolean.TRUE unboxed to the region's value");
        require(System.getSymbolicExpression(Boolean.TRUE)
                        .contains("\"symbolic\":false"),
                "Boolean.TRUE carries an expression");

        System.endConcolic();
        System.out.println("RegionSharedBoxSmoke OK");
    }

    private static String field(Sink sink, String name, String descriptor,
                                Object value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, descriptor, value);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
