import java.util.LinkedHashMap;
import java.util.Map;

/** A symbolic associative value view remains related after toArray(). */
public final class RegionMapValuesToObjectArrayApiSmoke {
    private static final class Entry {
        final int keyId;

        private Entry(int keyId) {
            this.keyId = keyId;
        }
    }

    public static void main(String[] args) {
        Map<Integer, Entry> map = new LinkedHashMap<Integer, Entry>();
        map.put(Integer.valueOf(7), new Entry(17));
        map.put(Integer.valueOf(11), new Entry(19));

        System.startConcolicRegion("REGION.map-values-array",
                "TASK.map-values-array");
        require(System.trackContainerExpression(
                        map, "REGION.map-values-array.in.map"),
                "map live-in rejected");
        Entry[] values = map.values().toArray(new Entry[0]);
        String expression = System.getSymbolicExpression(values);
        String summary = System.finishConcolicRegion();

        require(expression.contains("\"shape\":\"INDEXED\""), expression);
        require(expression.contains("\"operation\":\"WRITE\""), expression);
        require(expression.contains("\"operation\":\"NEXT\""), expression);
        require(expression.contains("VALUE_VIEW"), expression);
        require(expression.contains("REGION.map-values-array.in.map"),
                expression);
        require(summary.contains("\"operation\":\"WRITE\""), summary);
        System.out.println(
                "CAUSYNTH_REGION_MAP_VALUES_TO_OBJECT_ARRAY_API_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
