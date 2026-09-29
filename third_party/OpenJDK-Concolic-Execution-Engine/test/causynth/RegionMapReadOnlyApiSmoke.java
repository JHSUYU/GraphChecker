import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * A method that only reads a map whose state the region tracks runs its own
 * body: getOrDefault, a stream over values() and toString() return concrete
 * results and the thread's symbolic execution goes on.  Each of them used to
 * abort it (SOLR-18413's cluster-state parse and Slice.getReplicas).
 */
public final class RegionMapReadOnlyApiSmoke {
    private static final class Input {
        private int keyId = 42;
    }

    private static final class State {
        private final Map<Integer, Integer> replicas =
                new LinkedHashMap<Integer, Integer>();
    }

    public static void main(String[] args) {
        Input input = new Input();
        State state = new State();
        state.replicas.put(42, 7);

        System.startConcolicRegion("REGION.readonly", "ACT.readonly");
        System.symbolizeField(state, "replicas", "readonly_input_replicas");
        System.symbolizeField(input, "keyId", "readonly_input_keyId");
        state.replicas.put(input.keyId + 1, 8);
        Integer fallback = state.replicas.getOrDefault(99, -1);
        List<Integer> values = state.replicas.values().stream()
                .collect(Collectors.toList());
        String shown = state.replicas.toString();
        Object value = state.replicas.get(input.keyId);
        if (value == null) {
            throw new AssertionError("concrete lookup unexpectedly failed");
        }
        String pathCondition = System.getPathCondition();
        String summary = System.finishConcolicRegion();
        require(fallback.intValue() == -1 && values.size() == 2
                && shown.contains("42=7"), fallback + " " + values + " "
                + shown);
        require(summary.contains("\"aborted\":false"), summary);
        require(pathCondition.contains("\"_op\":\"!=\""), pathCondition);
        System.out.println("CAUSYNTH_REGION_MAP_READ_ONLY_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
