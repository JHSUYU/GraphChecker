import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Each record of a location's read log states what its read's plan chose,
 * in the shape its read-from node states it (envelope schema 2): the
 * observed version as {@code {fieldVersionId, versionKind}} -- the id one of
 * the log's versions carries --, whether the read is exact, the location's
 * writer-set completeness, the loaded word's type letter for a scalar, and
 * {@code unnamedWriter} where a write no hook saw reached the location.
 * A read whose value reaches no published expression is still a read of
 * its version.
 */
public final class RegionReadRecordSmoke {
    private static final class Holder {
        int count = 1;
    }

    private static final class Sink {
        int value;
    }

    public static void main(String[] args) {
        Holder holder = new Holder();
        require(System.startConcolicRegion("REGION.read-record",
                "TASK.read-record") == 0L, "region start rejected");
        require(System.observeField(holder, Holder.class.getName(), "count",
                "I") == 0, "the observation failed");
        Sink sink = new Sink();
        sink.value = holder.count;
        // A store no hook sees: the next read names an UNOBSERVED version.
        System.pauseConcolicPathCondition();
        holder.count = 5;
        System.resumeConcolicPathCondition();
        sink.value = holder.count;
        String log = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "count", "I");
        System.endConcolic();
        System.out.println("LOG " + log);

        require(log.contains("\"schemaVersion\":2"),
                "the envelope is no schema 2: " + log);
        String initial = versionId(log, "INITIAL");
        String unobserved = versionId(log, "UNOBSERVED");
        String reads = log.substring(log.indexOf("\"reads\":["),
                log.indexOf("\"serializationTruncated\""));
        require(reads.contains("\"observedVersion\":{\"fieldVersionId\":"
                        + initial + ",\"versionKind\":\"INITIAL\"}"),
                "the first read does not state the INITIAL it read: " + reads);
        require(reads.contains("\"observedVersion\":{\"fieldVersionId\":"
                        + unobserved + ",\"versionKind\":\"UNOBSERVED\"}"),
                "the second read does not state the UNOBSERVED version: "
                        + reads);
        require(count(reads, "\"_java_type\":\"I\"") == 2,
                "a scalar read states no type letter: " + reads);
        require(count(reads, "\"unnamedWriter\":true") == 1
                        && count(reads, "\"observedExact\":") == 2,
                "the read after an unseen write states no unnamed writer: "
                        + reads);
        System.out.println("CAUSYNTH_REGION_READ_RECORD_SMOKE_OK");
    }

    /** The {@code fieldVersionId} of the log's version of one kind. */
    private static String versionId(String log, String kind) {
        Matcher found = Pattern.compile("\"fieldVersionId\":(\\d+),"
                + "\"versionKind\":\"" + kind + "\"").matcher(log);
        require(found.find(), "no " + kind + " version: " + log);
        return found.group(1);
    }

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + needle.length())) {
            found++;
        }
        return found;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
