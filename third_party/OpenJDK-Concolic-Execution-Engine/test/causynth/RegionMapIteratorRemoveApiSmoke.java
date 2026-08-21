import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Verifies that a mutation performed through a backed Map entry iterator is
 * exported as a map-state effect.  Whole-thread path conditions are omitted
 * from the finish envelope; selected branch hooks export their predicates
 * separately in production.
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
                new LinkedHashMap<Integer, Value>();
    }

    public static void main(String[] args) {
        State state = new State();
        Value old = new Value(10L);
        Value fresh = new Value(30L);
        Clock clock = new Clock(20L);
        state.entries.put(7, old);
        state.entries.put(8, fresh);

        System.startConcolicRegion("REGION.iterator", "ACT.iterator");
        System.symbolizeField(state, "entries", "iterator_map");
        System.symbolizeField(clock, "now", "iterator_now");
        int iteration = 0;
        for (Iterator<Map.Entry<Integer, Value>> iterator =
                state.entries.entrySet().iterator(); iterator.hasNext();) {
            Map.Entry<Integer, Value> entry = iterator.next();
            System.symbolizeExactField(entry.getValue(),
                    Value.class.getName(), "expiry", "J",
                    iteration++ == 0 ? "iterator_expiry"
                            : "iterator_fresh_expiry");
            if (entry.getValue().expiry < clock.now) {
                iterator.remove();
            }
        }
        String relation = System.getSymbolicExpression(state.entries);
        String window = System.getConcolicPathConditionRange(0, 64);
        String summary = System.finishConcolicRegion();

        require(!state.entries.containsKey(7), summary);
        require(state.entries.containsKey(8), summary);
        require(relation.contains("\"operation\":\"REMOVE_AT\""), relation);
        require(summary.contains("\"pathConditionOmitted\":true"), summary);
        require(window.contains("\"pathConditionWatermark\":20"), window);
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
