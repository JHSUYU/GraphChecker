import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * A container's snapshot states its members in the order the class's own
 * iterator returns them, and says which order that is: a LinkedHashMap in
 * the order its keys were first put (its links, not its table), a HashMap
 * by its table from the first bin, a Hashtable by its table from the last
 * bin down.  SOLR-18413 r9: MigrateCmd's message map, a LinkedHashMap, was
 * stated in hash order, and a lookup keyed at the run's iteration position
 * named another key in the formula.
 */
public final class RegionMapIterationOrderSmoke {
    private static final class Input {
        long value = 7L;
    }

    public static void main(String[] args) {
        Input input = new Input();
        Map<Integer, Long> linked = new LinkedHashMap<Integer, Long>();
        Map<Integer, Long> hashed = new HashMap<Integer, Long>();
        Map<Integer, Long> table = new Hashtable<Integer, Long>();
        for (int key : new int[]{5, 1, 3}) {
            linked.put(key, 0L);
            hashed.put(key, 0L);
            table.put(key, 0L);
        }

        require(System.startConcolicRegion("REGION.order", "TASK.order")
                == 0L, "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "J", "VALUE");
        // The first symbolic put states what each map already held.
        linked.put(9, input.value);
        hashed.put(9, input.value);
        table.put(9, input.value);
        String linkedLog = System.getSharedMapVersions(linked);
        String hashedLog = System.getSharedMapVersions(hashed);
        String tableLog = System.getSharedMapVersions(table);
        System.endConcolic();

        require(ordered(linkedLog, 5, 1, 3)
                        && linkedLog.contains("\"order\":\"INSERTION\"")
                        && linkedLog.contains("\"members\":3"),
                "a LinkedHashMap's snapshot is not in insertion order: "
                        + linkedLog);
        require(ordered(hashedLog, 1, 3, 5)
                        && hashedLog.contains("\"order\":\"HASH\"")
                        && hashedLog.contains("\"members\":3"),
                "a HashMap's snapshot is not in its table's order: "
                        + hashedLog);
        require(ordered(tableLog, 5, 3, 1)
                        && tableLog.contains("\"order\":\"HASH\"")
                        && tableLog.contains("\"members\":3"),
                "a Hashtable's snapshot is not its table from the last bin "
                        + "down: " + tableLog);
        System.out.println("CAUSYNTH_REGION_MAP_ITERATION_ORDER_SMOKE_OK");
    }

    /** Whether the log names these keys first in this order. */
    private static boolean ordered(String log, int... keys) {
        int last = -1;
        for (int key : keys) {
            int at = log.indexOf("\"Y_I_" + key + "\"");
            if (at <= last) return false;
            last = at;
        }
        return true;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
