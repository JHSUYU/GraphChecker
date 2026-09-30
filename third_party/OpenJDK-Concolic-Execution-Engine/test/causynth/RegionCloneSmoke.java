/**
 * Object.clone gives the copy its own identity and copies of the shadows.
 *
 * <p>JVM_Clone copies the whole object, and it used to copy the session
 * identity word with it: the clone shared the original's shadow, container
 * state and version log, so a store into the clone rewrote what a read of
 * the original saw.  The copy now gets a fresh identity whose shadow holds
 * the original's field shadows (an array: its state), and the two part
 * ways at their next store.</p>
 */
public final class RegionCloneSmoke {
    private static final class Input {
        int n = 7;
    }

    private static final class Box implements Cloneable {
        int value;
        int other;

        Box copy() throws CloneNotSupportedException {
            return (Box) clone();
        }
    }

    private static final class Sink {
        int i;
    }

    public static void main(String[] args) throws Exception {
        require(System.startConcolicRegion("REGION.clone", "TASK.clone")
                == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "n", "I",
                "CLONE.N");
        Sink sink = new Sink();

        Box original = new Box();
        original.value = in.n;
        Box copy = original.copy();
        sink.i = copy.value;
        require(field(sink).contains("CLONE.N"),
                "the clone lost its field's value: " + field(sink));
        copy.value = 9;
        sink.i = original.value;
        String read = field(sink);
        require(sink.i == 7 && read.contains("CLONE.N"),
                "a store into the clone reached the original: " + read);
        String log = System.getSharedFieldVersions(original,
                Box.class.getName(), "value", "I");
        require(count(log, "\"writerContextId\"") == 1,
                "the clone's store landed in the original's log: " + log);
        // A symbolic store into the clone starts a log of its own.
        copy.value = in.n + 1;
        String copyLog = System.getSharedFieldVersions(copy,
                Box.class.getName(), "value", "I");
        require(!owner(log).isEmpty() && !owner(copyLog).isEmpty()
                        && !owner(log).equals(owner(copyLog)),
                "the clone shares the original's identity: " + log + " / "
                        + copyLog);

        int[] cells = new int[2];
        cells[0] = in.n;
        int[] cloned = cells.clone();
        sink.i = cloned[0];
        require(field(sink).contains("CLONE.N"),
                "the array clone lost its element");
        cloned[0] = 3;
        sink.i = cells[0];
        require(sink.i == 7 && field(sink).contains("CLONE.N"),
                "a store into the array clone reached the original");

        System.endConcolic();
        System.out.println("RegionCloneSmoke OK");
    }

    // The owner identity an envelope's location names.
    private static String owner(String json) {
        String key = "\"selected\":true,\"location\":{\"ownerSymRid\":";
        int at = json.indexOf(key);
        if (at < 0) return "";
        return json.substring(at + key.length(), json.indexOf(',', at + key.length()));
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
