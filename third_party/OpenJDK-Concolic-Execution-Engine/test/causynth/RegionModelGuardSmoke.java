import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * The pin/guard discipline of the container models, on published
 * expressions: no model adds a condition to the path.
 *
 * <p>A CHOICE a muted body made by the value at a key, a membership or an
 * emptiness is a guard on the chain it produced -- PUT_IF and REMOVE_IF
 * under MATCHES (the value at the key, null where absent, is the expected
 * cell) or CONTAINS, POLL under its own emptiness test -- so another state
 * flips the effect; what a callback the run never ran would have stored is
 * an UNKNOWN cell under the arm it would have run in, named
 * CONTAINER_PINNED; and a call that left the container as it was publishes
 * no version.  A FACT the run observed that the chain may not decide
 * -- what a query answered, an element of an array whose elements are the
 * heap's -- is stated on its node (`concreteValue`, with the `answer` id
 * that names its pin), and an array whose elements are an input states
 * none.</p>
 */
public final class RegionModelGuardSmoke {
    private static final class Input {
        long key = 7L;
        int[] values = {40, 41, 42, 43};
    }

    /** Equal by value, as no cell compares an object. */
    private static final class Point {
        final int at;

        Point(int at) {
            this.at = at;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Point && ((Point) other).at == at;
        }

        @Override
        public int hashCode() {
            return at;
        }
    }

    private static final class Sink {
        Long head;
        Long value;
        int element;
        int input;
    }

    private static final String LONG = "Ljava/lang/Long;";

    public static void main(String[] args) {
        Input input = new Input();
        int[] heap = {5, 6, 7, 8};
        Sink sink = new Sink();
        require(System.startConcolicRegion("REGION.model-guard",
                "TASK.model-guard") == 0L, "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "key", "J",
                "KEY");
        System.symbolizeField(input, "values", "VALUES");
        int before = conditions();

        // computeIfAbsent: the callback ran where get(k) was null, so what
        // it stored is a PUT_IF under that test; the second call's callback
        // did not run, so what it would have stored is unknown, and the
        // call changed nothing: no version.
        Map<Long, Long> computing = new HashMap<>();
        computing.computeIfAbsent(input.key, k -> k + 1);
        computing.computeIfAbsent(input.key, k -> k + 2);
        String computed = System.getSymbolicExpression(computing);
        String computedLog = System.getSharedMapVersions(computing);

        // computeIfPresent: a callback that answered null removes under the
        // key being there (REMOVE_IF); one that did not run stores an
        // unknown cell where the key would have been there.
        Map<Long, Long> present = new HashMap<>();
        present.put(input.key, 1L);
        present.computeIfPresent(input.key, (k, v) -> null);
        present.computeIfPresent(input.key, (k, v) -> v + 1);
        String removed = System.getSymbolicExpression(present);

        // replace(k, v) puts where k is a key; replace(k, e, u) and
        // remove(k, e) act where the value at k is e.
        Map<Long, Long> replacing = new HashMap<>();
        replacing.put(input.key, 1L);
        replacing.replace(input.key, 2L);
        replacing.replace(input.key, 2L, 3L);
        boolean unmatched = replacing.remove(input.key, 4L);
        String replaced = System.getSymbolicExpression(replacing);
        // An expected value equals() matched but no cell would: its match
        // states no answer.
        Map<Long, Point> points = new HashMap<>();
        points.put(input.key, new Point(1));
        boolean equalPoint = points.replace(input.key, new Point(1),
                new Point(2));
        String pointChain = System.getSymbolicExpression(points);

        // A set's add puts where the member was absent, and answers that.
        Set<Long> set = new HashSet<>();
        boolean added = set.add(input.key);
        boolean again = set.add(input.key);
        String members = System.getSymbolicExpression(set);

        // poll() over an empty queue: the head or null, and the queue
        // without its head where it has one -- no emptiness condition.
        ArrayDeque<Long> queue = new ArrayDeque<>();
        queue.add(input.key);
        queue.poll();
        sink.head = queue.poll();
        String polled = field(sink, "head", LONG, sink.head);
        String drained = System.getSymbolicExpression(queue);
        // Before the loop below, whose hasNext() tests are branches.
        int after = conditions();

        // An entry's value states what it returned.
        for (Map.Entry<Long, Long> entry : replacing.entrySet()) {
            sink.value = entry.getValue();
        }
        String entryValue = field(sink, "value", LONG, sink.value);

        // An element of an array whose elements are the heap's, at a
        // symbolic position, states what the load returned; an element of
        // an array whose elements are an input does not.
        sink.element = heap[(int) (input.key & 3)];
        sink.input = input.values[1];
        String element = field(sink, "element", "I",
                Integer.valueOf(sink.element));
        String inputElement = field(sink, "input", "I",
                Integer.valueOf(sink.input));

        String summary = System.finishConcolicRegion();

        System.out.println("COMPUTED " + computed);
        System.out.println("POLLED " + polled);
        require(!unmatched && equalPoint && added && !again
                        && sink.head == null
                        && sink.value == 3L && sink.element == 8
                        && sink.input == 41,
                "the models did not run as written");
        require(after == before,
                "a model's choice added a path condition: " + before + " -> "
                        + after);
        require(count(computed, "\"operation\":\"PUT_IF\"") == 2
                        && computed.contains("\"operation\":\"MATCHES\"")
                        && computed.contains("\"operation\":\"UNKNOWN\"")
                        && computed.contains("\"answer\":")
                        && count(computedLog,
                        "\"versionKind\":\"STATE_PUT_IF\"") == 1
                        && summary.contains("CONTAINER_PINNED:computeIfAbsent"),
                "computeIfAbsent is no guarded PUT_IF and a named unknown "
                        + "cell, or a no-op published: " + computed + " / "
                        + computedLog);
        require(removed.contains("\"operation\":\"REMOVE_IF\"")
                        && removed.contains("\"operation\":\"UNKNOWN\"")
                        && summary.contains(
                        "CONTAINER_PINNED:computeIfPresent"),
                "computeIfPresent is no guarded REMOVE_IF and a named "
                        + "unknown cell: " + removed);
        require(count(replaced, "\"operation\":\"PUT_IF\"") == 2
                        && replaced.contains("\"operation\":\"REMOVE_IF\"")
                        && replaced.contains("\"operation\":\"CONTAINS\"")
                        && replaced.contains("\"operation\":\"MATCHES\""),
                "replace/remove are no guarded mutations: " + replaced);
        require(pointChain.contains("\"operation\":\"MATCHES\"")
                        && !pointChain.contains("\"answer\":"),
                "an equals() match states an identity answer: "
                        + pointChain);
        require(count(members, "\"operation\":\"PUT_IF\"") == 2
                        && members.contains("\"operation\":\"CONTAINS\"")
                        && members.contains("\"answer\":"),
                "a set's add is no PUT_IF under its absence: " + members);
        require(polled.contains("\"operation\":\"PEEK\"")
                        && polled.contains("\"concreteValue\":null")
                        && count(drained, "\"operation\":\"POLL\"") == 2,
                "poll of an empty queue is no PEEK and POLL: " + polled);
        require(entryValue.contains("\"operation\":\"VALUE\"")
                        && entryValue.contains("\"concreteValue\":")
                        && !entryValue.contains("OBSERVE_"),
                "an entry's value states no answer: " + entryValue);
        require(element.contains("\"operation\":\"READ\"")
                        && element.contains("\"concreteValue\":")
                        && element.contains("\"_exp\":\"Y_I_8\""),
                "a heap array's element states no answer: " + element);
        require(inputElement.contains("\"operation\":\"READ\"")
                        && !inputElement.contains("\"concreteValue\":"),
                "an input array's element states an answer: " + inputElement);
        System.out.println("CAUSYNTH_REGION_MODEL_GUARD_SMOKE_OK");
    }

    private static String field(Sink sink, String name, String descriptor,
                                Object value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, descriptor, value);
    }

    private static int conditions() {
        String all = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        String key = "\"conditionCount\":";
        int at = all.indexOf(key) + key.length();
        int end = at;
        while (Character.isDigit(all.charAt(end))) end++;
        return Integer.parseInt(all.substring(at, end));
    }

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + 1)) {
            found++;
        }
        return found;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
