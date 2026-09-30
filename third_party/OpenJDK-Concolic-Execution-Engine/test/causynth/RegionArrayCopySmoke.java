import java.util.Arrays;

/**
 * System.arraycopy and Arrays.copyOf move element shadows and versions.
 *
 * <p>No bytecode runs for a copy, so no element hook saw it: a destination
 * kept whatever shadow it had and a tracked element kept its old version,
 * and the next reader found a word no version stored.  CharArrayBuffer's
 * growth was 1,136 of the 1,139 UNOBSERVED reads of one Solr session.  The
 * copy now carries each source element's value into the destination's
 * state, versions each tracked destination element in the same critical
 * section as the copy, and keeps overlapping ranges right.  A store no hook
 * sees makes a recorded write stale; the read then states the heap's word,
 * concrete, instead of the stale value.</p>
 *
 * <p>An object copy that checks each element's store may throw part way,
 * running Java, so it holds no stripe: one that will fail throws as the JVM
 * does and names its tracked destination elements ARRAYCOPY_FAILED; one
 * that passes names them ARRAYCOPY_STORE_CHECK, since it versions
 * nothing.</p>
 */
public final class RegionArrayCopySmoke {
    private static final class Input {
        char c = 'x';
        int n = 7;
        boolean flag = true;
        String s = "abc";
    }

    private static final class Sink {
        char c;
        int i;
        boolean z;
        byte b;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.array-copy",
                "TASK.array-copy") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "c", "C",
                "COPY.C");
        System.symbolizeExactField(in, Input.class.getName(), "n", "I",
                "COPY.N");
        System.symbolizeExactField(in, Input.class.getName(), "flag", "Z",
                "COPY.FLAG");
        System.symbolizeExactField(in, Input.class.getName(), "s",
                "Ljava/lang/String;", "COPY.S");
        Sink sink = new Sink();

        // A symbolic element moved by System.arraycopy keeps its value.
        char[] source = new char[4];
        source[1] = in.c;
        char[] destination = new char[8];
        System.arraycopy(source, 0, destination, 2, 4);
        sink.c = destination[3];
        String moved = field(sink, "c", "C", Character.valueOf(sink.c));
        require(moved.contains("COPY.C"), "the copy lost its value: " + moved);
        sink.c = destination[2];
        require(!field(sink, "c", "C", Character.valueOf(sink.c))
                        .contains("COPY.C"),
                "a concrete element read back symbolic");

        // Arrays.copyOf, the growth of every buffer, is the same copy.
        char[] grown = Arrays.copyOf(source, 16);
        sink.c = grown[1];
        require(field(sink, "c", "C", Character.valueOf(sink.c))
                        .contains("COPY.C"), "copyOf lost the value");

        // A tracked destination element: versioned by the copy, joined.
        int[] cells = new int[2];
        cells[0] = in.n;
        int[] replacement = {5, 6};
        System.arraycopy(replacement, 0, cells, 0, 2);
        sink.i = cells[0];
        String joined = field(sink, "i", "I", Integer.valueOf(sink.i));
        String element = System.getSharedElementVersions(cells, 0);
        require(sink.i == 5 && joined.contains("\"observedExact\":true")
                        && joined.contains("\"writerSetComplete\":true")
                        && !joined.contains("UNOBSERVED"),
                "the copied-over element read is not its copy: " + joined);
        require(count(element, "\"writerContextId\"") == 2
                        && !element.contains("UNOBSERVED")
                        && element.contains("\"writerSetComplete\":true"),
                "the copy published no version: " + element);

        // Overlapping ranges read the source before it is overwritten.
        int[] shift = new int[4];
        shift[1] = in.n;
        System.arraycopy(shift, 1, shift, 0, 3);
        sink.i = shift[0];
        require(field(sink, "i", "I", Integer.valueOf(sink.i))
                        .contains("COPY.N"), "the shift lost its value");

        // boolean[] and byte[] written symbolically read back as written.
        boolean[] flags = new boolean[2];
        flags[0] = in.flag;
        sink.z = flags[0];
        String flag = field(sink, "z", "Z", Boolean.valueOf(sink.z));
        require(flag.contains("COPY.FLAG") && flag.contains("\"_java_type\":\"Z\""),
                "the boolean element did not round-trip: " + flag);
        byte[] bytes = new byte[2];
        bytes[0] = (byte) in.n;
        sink.b = bytes[0];
        require(field(sink, "b", "B", Byte.valueOf(sink.b)).contains("COPY.N"),
                "the byte element did not round-trip");

        // A store no hook sees: the recorded write is stale, the read is
        // the heap's word.
        char[] stale = new char[2];
        stale[0] = in.c;
        System.pauseConcolicPathCondition();
        stale[0] = 'q';
        System.resumeConcolicPathCondition();
        sink.c = stale[0];
        require(sink.c == 'q' && !field(sink, "c", "C",
                        Character.valueOf(sink.c)).contains("COPY.C"),
                "a stale recorded write was read back");

        // A store-checked copy that fails: the exception, no stripe held.
        String[] typed = new String[1];
        typed[0] = in.s;
        require(System.getSharedElementVersions(typed, 0)
                        .contains("\"selected\":true"),
                "the symbolic element store started no log");
        Object[] mixed = {Integer.valueOf(1)};
        boolean thrown = false;
        try {
            System.arraycopy(mixed, 0, typed, 0, 1);
        } catch (ArrayStoreException expected) {
            thrown = true;
        }
        String failed = System.getSharedElementVersions(typed, 0);
        require(thrown && failed.contains("\"ARRAYCOPY_FAILED\"")
                        && failed.contains("\"unnamedWriter\":true"),
                "the failing copy is not named: " + failed);
        // One that passes: copied, and named.
        String[] checked = new String[1];
        checked[0] = in.s;
        Object[] plain = {"plain"};
        System.arraycopy(plain, 0, checked, 0, 1);
        String passed = System.getSharedElementVersions(checked, 0);
        require("plain".equals(checked[0])
                        && passed.contains("\"ARRAYCOPY_STORE_CHECK\""),
                "the store-checked copy is not named: " + passed);

        System.endConcolic();
        System.out.println("RegionArrayCopySmoke OK");
    }

    private static String field(Sink sink, String name, String descriptor,
                                Object value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, descriptor, value);
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
