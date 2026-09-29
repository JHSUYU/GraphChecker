import java.util.ArrayList;
import java.util.List;

/**
 * A mutation the model does not follow takes only its container out of the
 * model: removeIf over a list the region tracks leaves the list concrete,
 * and a symbolic branch after it still records (SOLR-18413's update aborted
 * at replicas.removeIf, before the expiry clock it existed for).
 */
public final class RegionListAbandonApiSmoke {
    private static final class Input {
        private int keyId = 42;
    }

    private static final class State {
        private final List<Integer> replicas = new ArrayList<Integer>();
    }

    public static void main(String[] args) {
        Input input = new Input();
        State state = new State();
        state.replicas.add(1);

        System.startConcolicRegion("REGION.abandon", "ACT.abandon");
        System.symbolizeField(state, "replicas", "abandon_input_replicas");
        System.symbolizeField(input, "keyId", "abandon_input_keyId");
        state.replicas.add(input.keyId);
        state.replicas.removeIf(value -> value.intValue() == 1);
        int left = state.replicas.size();
        if (input.keyId > 10) {
            left++;
        }
        String pathCondition = System.getPathCondition();
        String summary = System.finishConcolicRegion();
        require(left == 2, "size " + left);
        require(summary.contains("\"aborted\":false"), summary);
        require(pathCondition.contains("\"_op\":\">\"")
                || pathCondition.contains("\"_op\":\"<=\""), pathCondition);
        System.out.println("CAUSYNTH_REGION_LIST_ABANDON_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
