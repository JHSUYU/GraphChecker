import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * Verifies that a mutation performed through a backed Map entry iterator is
 * exported as a map-state effect while the application guard remains in the
 * region path condition.
 */
public final class RegionMapIteratorRemoveApiSmoke {
    private static final class Value {
        private long expiry;

        private Value(long expiry) {
            this.expiry = expiry;
        }
    }

    private static final class Clock {
        private long now;

        private Clock(long now) {
            this.now = now;
        }
    }

    private static final class State {
        private final Map<Integer, Value> entries =
                new HashMap<Integer, Value>();
    }

    public static void main(String[] args) {
        State state = new State();
        Value old = new Value(10L);
        Clock clock = new Clock(20L);
        state.entries.put(7, old);

        System.startConcolicRegion("REGION.iterator", "ACT.iterator");
        System.symbolizeField(state, "entries", "iterator_map");
        System.symbolizeField(old, "expiry", "iterator_expiry");
        System.symbolizeField(clock, "now", "iterator_now");
        for (Iterator<Map.Entry<Integer, Value>> iterator =
                state.entries.entrySet().iterator(); iterator.hasNext();) {
            Map.Entry<Integer, Value> entry = iterator.next();
            if (entry.getValue().expiry < clock.now) {
                iterator.remove();
            }
        }
        String summary = System.finishConcolicRegion();

        require(!state.entries.containsKey(7), summary);
        require(summary.contains("iterator_expiry"), summary);
        require(summary.contains("iterator_now"), summary);
        require(summary.contains("java/util/HashMap remove"), summary);
        require(summary.contains("\"_op\":\"<\""), summary);
        if (args.length > 0 && "--dump".equals(args[0])) {
            System.out.println(summary);
        }
        System.out.println("CAUSYNTH_REGION_MAP_ITERATOR_REMOVE_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
