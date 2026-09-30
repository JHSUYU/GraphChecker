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
 * write and records the compare -- `old == expected` when it succeeded,
 * `!=` when it failed -- over the value it compared (an identity, for
 * AtomicReference).  An AtomicReference set to a container states the
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
        boolean first = closed.compareAndSet(true, false);
        boolean second = closed.compareAndSet(true, false);
        String decisions = range(before);
        Sink sink = new Sink();
        sink.flag = closed.get();
        String flag = System.getSharedFieldVersions(closed,
                AtomicBoolean.class.getName(), "value", "I");

        // AtomicReference: a set of a fresh map (putfield), a CAS to
        // another, and updateAndGet.
        Map<Integer, Integer> fresh = new ConcurrentHashMap<>();
        fresh.put(1, 10);
        current.set(fresh);
        Map<Integer, Integer> swapped = new ConcurrentHashMap<>();
        before = conditions();
        boolean cas = current.compareAndSet(fresh, swapped);
        String identity = range(before);
        Map<Integer, Integer> updated = current.updateAndGet(map -> {
            Map<Integer, Integer> next = new ConcurrentHashMap<>(map);
            next.put(2, 20);
            return next;
        });
        String reference = System.getSharedFieldVersions(current,
                AtomicReference.class.getName(), "value",
                "Ljava/lang/Object;");
        System.endConcolic();

        System.out.println("DECISIONS " + decisions);
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
        require(decisions.contains("\"_op\":\"==\"")
                        && decisions.contains("\"_op\":\"!=\""),
                "the CAS decisions are not both recorded: " + decisions);
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

    private static String range(int start) {
        return System.getConcolicPathConditionRange(start, Integer.MAX_VALUE);
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
