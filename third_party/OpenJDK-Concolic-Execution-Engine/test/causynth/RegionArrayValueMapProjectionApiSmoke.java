import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Regression for runtime map-value projections: the output array is allocated
 * by Collection.toArray and is not itself symbolized, while fields on each
 * element owner are symbolized before producer execution.
 */
public final class RegionArrayValueMapProjectionApiSmoke {
    private static final class Entry {
        long expiry;

        private Entry(long expiry) {
            this.expiry = expiry;
        }
    }

    public static void main(String[] args) {
        Entry first = new Entry(11L);
        Entry second = new Entry(22L);
        Map<Integer, Entry> values = new LinkedHashMap<Integer, Entry>();
        values.put(1, first);
        values.put(2, second);

        System.startConcolicRegion("REGION.array-value-map-projection",
                "ACT.array-value-map-projection");
        System.pauseConcolicPathCondition();
        System.symbolizeField(first, "expiry",
                "REGION.map.in.expiry.site.1");
        System.symbolizeField(second, "expiry",
                "REGION.map.in.expiry.site.2");
        System.resumeConcolicPathCondition();

        Entry[] output = values.values().toArray(new Entry[0]);
        if (output[0].expiry < 0L || output[1].expiry < 0L) {
            throw new AssertionError("unexpected concrete expiry");
        }
        System.pauseConcolicPathCondition();
        String outputJson = System.getSymbolicExpression(output);
        String firstJson = System.getSymbolicExpression(first);
        String secondJson = System.getSymbolicExpression(second);
        String summary = System.finishConcolicRegion();

        System.out.println("CAUSYNTH_ARRAY_VALUE_MAP_PROJECTION_JSON="
                + outputJson);
        require(outputJson.contains("\"kind\":\"ARRAY_VALUE\""),
                outputJson);
        require(outputJson.contains("\"_java_type\":\"[L"
                + "RegionArrayValueMapProjectionApiSmoke$Entry;\""),
                outputJson);
        require(outputJson.contains("\"_elements_complete\":true"),
                outputJson);
        require(count(outputJson,
                "\"provenance\":\"ARRAY_SHADOW\"") == 2,
                outputJson);
        require(!outputJson.contains("\"expression\":null"), outputJson);
        require(firstJson.contains("\"kind\":\"SYMBOLIC_OBJECT\""),
                firstJson);
        require(secondJson.contains("\"kind\":\"SYMBOLIC_OBJECT\""),
                secondJson);
        require(firstJson.contains("\"_type\":\"SymbolExpression\""),
                firstJson);
        require(secondJson.contains("\"_type\":\"SymbolExpression\""),
                secondJson);
        String firstReference = expressionId(firstJson);
        String secondReference = expressionId(secondJson);
        require(firstReference.startsWith("M_L'"), firstJson);
        require(secondReference.startsWith("M_L'"), secondJson);
        require(!firstReference.equals(secondReference), outputJson);
        require(outputJson.contains("\"_exp\":\"" + firstReference
                + "\""), outputJson);
        require(outputJson.contains("\"_exp\":\"" + secondReference
                + "\""), outputJson);
        require(summary.contains("REGION.array-value-map-projection"),
                summary);
        require(summary.contains(
                "M_J_field_REGION.map.in.expiry.site.1"), summary);
        require(summary.contains(
                "M_J_field_REGION.map.in.expiry.site.2"), summary);
        System.out.println(
                "CAUSYNTH_REGION_ARRAY_VALUE_MAP_PROJECTION_API_SMOKE_OK");
    }

    private static int count(String value, String needle) {
        int result = 0;
        int from = 0;
        while ((from = value.indexOf(needle, from)) >= 0) {
            result++;
            from += needle.length();
        }
        return result;
    }

    private static String expressionId(String envelope) {
        String marker = "\"_exp\":\"";
        int start = envelope.indexOf(marker);
        require(start >= 0, envelope);
        start += marker.length();
        int end = envelope.indexOf('"', start);
        require(end > start, envelope);
        return envelope.substring(start, end);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
