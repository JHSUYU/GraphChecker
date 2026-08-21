import java.util.HashMap;
import java.util.Map;

public final class RegionMapApiSmoke {
    private static final class Input {
        private int keyId = 42;
    }

    private static final class State {
        private final Map<Integer, Object> allKeys =
                new HashMap<Integer, Object>();
    }

    public static void main(String[] args) {
        Input input = new Input();
        State state = new State();
        state.allKeys.put(42, new Object());

        System.startConcolicRegion("REGION.map", "ACT.map");
        System.symbolizeField(state, "allKeys", "map_input_allKeys");
        System.symbolizeField(input, "keyId", "map_input_keyId");
        state.allKeys.put(input.keyId + 1, new Object());
        Object value;
        synchronized (state) {
            value = (Object) state.allKeys.get(input.keyId);
        }
        if (value == null) {
            throw new AssertionError("concrete lookup unexpectedly failed");
        }
        String writeRelation = System.getSymbolicExpression(state.allKeys);
        String readRelation = System.getSymbolicExpression(value);
        String pathCondition = System.getPathCondition();
        String summary = System.finishConcolicRegion();
        require(readRelation.contains("\"operation\":\"READ\""),
                readRelation);
        require(writeRelation.contains("\"operation\":\"PUT\""),
                writeRelation);
        require((writeRelation + readRelation).contains("map_input_allKeys"),
                writeRelation + readRelation);
        require((writeRelation + readRelation).contains("map_input_keyId"),
                writeRelation + readRelation);
        require(pathCondition.contains("\"_op\":\"!=\""), pathCondition);
        require(pathCondition.contains("\"_code_position\""), pathCondition);
        require(summary.contains("\"pathConditionOmitted\":true"), summary);
        System.out.println("CAUSYNTH_REGION_MAP_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
