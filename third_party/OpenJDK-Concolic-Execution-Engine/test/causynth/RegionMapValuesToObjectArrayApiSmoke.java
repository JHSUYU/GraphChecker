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
        long status = System.startConcolicRegion("REGION.map-values-array",
                "TASK.map-values-array");
        require(status == 0L, "region start rejected: " + status);
        require(System.trackContainerExpression(
                        map, "REGION.map-values-array.in.map"),
                "map live-in rejected");
        long initial = System.selectSharedMapCarrier(map);
        require(initial > 0L, "map carrier selection rejected: " + initial);

        // Select the empty state first, then publish two STATE_PUT versions.
        // values() keeps all three states as one guarded read; toArray()
        // inherits it instead of issuing a second map read.
        map.put(Integer.valueOf(7), new Entry(17));
        map.put(Integer.valueOf(11), new Entry(19));
        Entry[] values = map.values().toArray(new Entry[0]);
        String expression = System.getSymbolicExpression(values);
        String versions = System.getSharedMapVersions(map);
        String summary = System.finishConcolicRegion();

        require(expression.contains("\"shape\":\"INDEXED\""), expression);
        require(expression.contains("\"operation\":\"WRITE\""), expression);
        require(expression.contains("\"operation\":\"NEXT\""), expression);
        require(expression.contains("VALUE_VIEW"), expression);
        require(expression.contains("REGION.map-values-array.in.map"),
                expression);
        require(!expression.contains("TruncatedExpression"), expression);
        require(versions.contains("\"selected\":true"), versions);
        require(versions.contains("\"locationKind\":\"MAP_STATE\""),
                versions);
        require(count(versions, "\"fieldVersionId\"") == 3, versions);
        require(count(versions, "\"versionKind\":\"STATE_PUT\"") == 2,
                versions);
        require(count(versions, "\"readEventId\"") == 1, versions);
        require(versions.contains("\"candidateCount\":3"), versions);
        require(expression.contains("\"_type\":\"ReadFromExpression\""),
                expression);
        require(expression.contains(
                "\"exactlyOne\":[\"rf1\",\"rf2\",\"rf3\"]"), expression);
        require(count(expression,
                "\"versionKind\":\"INITIAL\"") == 1, expression);
        require(count(expression,
                "\"versionKind\":\"STATE_PUT\"") == 2, expression);
        require(!expression.contains("\"versionKind\":\"\""), expression);
        require(versions.contains("\"serializationTruncated\":false"),
                versions);
        require(versions.contains("\"readLogTruncated\":false"), versions);
        require(!versions.contains("TruncatedExpression"), versions);
        require(summary.contains("\"complete\":true"), summary);
        System.out.println(
                "CAUSYNTH_REGION_MAP_VALUES_TO_OBJECT_ARRAY_API_SMOKE_OK");
    }

    private static int count(String text, String fragment) {
        int matches = 0;
        int cursor = 0;
        while ((cursor = text.indexOf(fragment, cursor)) >= 0) {
            matches++;
            cursor += fragment.length();
        }
        return matches;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
