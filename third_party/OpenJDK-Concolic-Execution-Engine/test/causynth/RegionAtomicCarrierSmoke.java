import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/**
 * AtomicBoolean and AtomicReference are one-cell carriers, `value`, observed
 * on the atomic as owner.
 *
 * <p>Their get and set are a getfield and a putfield of interpreted JDK
 * code; their compare-and-set goes through Unsafe, whose hook versions the
 * write and answers the compare -- `old == expected`, true where it
 * succeeded -- over the value it compared (an identity, for
 * AtomicReference), as the result of the call: a branch on it decides it,
 * and nothing is added to the path.  An AtomicReference set to a container states the
 * container's state at the store (referentState), whichever path stored it;
 * updateAndGet runs its lambda interpreted and the CAS publishes the
 * result.</p>
 */
public final class RegionAtomicCarrierSmoke {
    private static final class Input {
        int level = 3;
    }

    private static final class Sink {
        boolean flag;
        boolean first;
        boolean second;
        boolean cas;
    }

    public static void main(String[] args) {
        AtomicBoolean closed = new AtomicBoolean(false);
        AtomicReference<Map<Integer, Integer>> current =
                new AtomicReference<>(new ConcurrentHashMap<>());
        Input input = new Input();

        require(System.startConcolicRegion("REGION.atomic-carrier",
                "TASK.atomic-carrier") == 0L, "region start rejected");
        require(System.observeField(closed, AtomicBoolean.class.getName(),
                "value", "I") == 0, "AtomicBoolean.value not observed");
        require(System.observeField(current,
                AtomicReference.class.getName(), "value",
                "Ljava/lang/Object;") == 0,
                "AtomicReference.value not observed");
        System.symbolizeExactField(input, Input.class.getName(), "level",
                "I", "LEVEL");

        // AtomicBoolean: a set (putfield), a successful and a failed CAS.
        closed.set(input.level > 2);
        int before = conditions();
        Sink sink = new Sink();
        sink.first = closed.compareAndSet(true, false);
        sink.second = closed.compareAndSet(true, false);
        boolean first = sink.first;
        boolean second = sink.second;
        String answers = answer(sink, "first", first)
                + answer(sink, "second", second);
        int after = conditions();
        sink.flag = closed.get();
        String flag = System.getSharedFieldVersions(closed,
                AtomicBoolean.class.getName(), "value", "I");

        // AtomicReference: a set of a fresh map (putfield), a CAS to
        // another, and updateAndGet.
        Map<Integer, Integer> fresh = new ConcurrentHashMap<>();
        fresh.put(1, 10);
        current.set(fresh);
        Map<Integer, Integer> swapped = new ConcurrentHashMap<>();
        sink.cas = current.compareAndSet(fresh, swapped);
        boolean cas = sink.cas;
        String identity = answer(sink, "cas", cas);
        Map<Integer, Integer> updated = current.updateAndGet(map -> {
            Map<Integer, Integer> next = new ConcurrentHashMap<>(map);
            next.put(2, 20);
            return next;
        });
        String reference = System.getSharedFieldVersions(current,
                AtomicReference.class.getName(), "value",
                "Ljava/lang/Object;");
        System.endConcolic();

        System.out.println("ANSWERS " + answers);
        System.out.println("FLAG " + flag);
        System.out.println("IDENTITY " + identity);
        System.out.println("REFERENCE " + reference);

        require(first && !second && !sink.flag && cas
                        && updated.get(2) == 20,
                "the atomics did not run as written");
        require(flag.contains("\"versionKind\":\"INITIAL\"")
                        && flag.contains("\"versionKind\":\"WRITE\"")
                        && flag.contains("\"versionKind\":\"RMW\""),
                "AtomicBoolean's set and CAS are not versions: " + flag);
        require(count(answers, "\"_op\":\"==\"") >= 2 && after == before,
                "the CAS answers are not their results: " + answers);
        require(identity.contains("\"_op\":\"==\"")
                        && identity.contains("\"_type\":\"ReadFromExpression\""),
                "AtomicReference's CAS compared no read of its value: "
                        + identity);
        require(count(reference, "\"referentState\":") >= 3,
                "a store of a map into AtomicReference states no referent: "
                        + reference);
        System.out.println("CAUSYNTH_REGION_ATOMIC_CARRIER_SMOKE_OK");
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

    /** What a CAS result stored in `name` of `sink` is. */
    private static String answer(Sink sink, String name, boolean value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, "Z", Boolean.valueOf(value));
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
