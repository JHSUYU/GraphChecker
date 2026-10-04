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
        // The empty base is stated first, then two STATE_PUT versions.
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
        require(count(versions, "\"writerContextId\"") == 3, versions);
        require(count(versions, "\"versionKind\":\"STATE_PUT\",") == 2,
                versions);
        require(count(versions, "\"readEventId\"") == 1, versions);
        require(count(versions, "\"readerContextId\"") == 1, versions);
        // The logged read states the version its plan chose (schema 2), the
        // one its read-from node names, so the read is a row even where its
        // value reaches no published expression.
        require(versions.contains("\"schemaVersion\":2"), versions);
        require(count(versions, "\"observedVersion\":") == 1, versions);
        require(versions.contains("\"observedExact\":"), versions);
        // The INITIAL version states the content the recorder walked before
        // the first symbolic mutation: this map was empty, and zero is an
        // answer rather than an absent one.
        require(versions.contains(
                "\"initialSnapshot\":{\"stated\":true,\"entries\":0,"
                + "\"truncated\":false}"), versions);
        // One read, one version named: the state the values view observed is
        // the newest STATE_PUT, and the value it carries is the whole chain
        // below it, so the stated base and both puts are in the read.
        require(expression.contains("\"_type\":\"ReadFromExpression\""),
                expression);
        require(count(expression, "\"observedVersion\"") == 1, expression);
        require(count(expression,
                "\"versionKind\":\"STATE_PUT\"") == 1, expression);
        require(count(expression,
                "\"operation\":\"SNAPSHOT_BASE\"") == 1, expression);
        require(count(expression, "\"operation\":\"PUT\"") == 2, expression);
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
