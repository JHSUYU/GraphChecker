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

        // Select the empty state first, then publish two real STATE_PUT
        // versions.  Same-thread program order makes the second put the exact
        // writer observed by values(); toArray() must inherit that one read,
        // not issue a second map read of its own.
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
        require(versions.contains("\"readsObserved\":1"), versions);
        require(count(versions, "\"readEventId\"") == 1, versions);
        require(versions.contains("\"resolution\":\"EXACT\""), versions);
        require(versions.contains("\"candidateCount\":1"), versions);
        require(numberAfter(versions, "\"chosenFieldVersionId\":", false)
                        == numberAfter(versions, "\"fieldVersionId\":", true),
                "values() did not read the latest put: " + versions);
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

    private static long numberAfter(String text, String marker,
                                    boolean last) {
        int markerIndex = last ? text.lastIndexOf(marker)
                : text.indexOf(marker);
        require(markerIndex >= 0, "missing " + marker + ": " + text);
        int start = markerIndex + marker.length();
        int end = start;
        while (end < text.length()
                && text.charAt(end) >= '0' && text.charAt(end) <= '9') {
            end++;
        }
        require(end > start, "missing number after " + marker + ": " + text);
        return Long.parseLong(text.substring(start, end));
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
