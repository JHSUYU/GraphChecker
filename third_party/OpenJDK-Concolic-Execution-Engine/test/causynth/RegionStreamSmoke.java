import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * java.util.stream pipelines as the relations they compute (SymStream).
 *
 * <p>The three shapes the HDFS and Solr checks run: a concrete list
 * filtered by a predicate that reads a tracked list and collected
 * (FsVolumeList.chooseVolume), then its size; a list limited by a symbolic
 * bound, mapped and collected (DataNodeDiskMetrics); an unmodifiable map's
 * entry set filtered twice, mapped to its keys and collected, then its size
 * (Solr's DeleteCollectionCmd.referencedByAlias).  Each collected list is a
 * tracked container whose version is an APPEND_IF chain from its stated
 * empty base, and its size a SIZE of it.  Besides: a stream over the
 * tracked list itself reads its members and pins its end; count and
 * anyMatch are a SIZE and an IS_EMPTY of a chain; a set collects guarded
 * PUT_IFs; a pipeline nothing symbolic reached returns a concrete result
 * and names nothing; an unmodeled operation on a pipeline over a symbolic
 * source stops its recording and is named in the region's model gaps, as
 * are the pins that replace a counterfactual.</p>
 */
public final class RegionStreamSmoke {
    private static final class Input {
        String disk = new String("/ssd");
        String alias = new String("alias-x");
        int max = 1;
    }

    private static final class Volume {
        final String path;

        Volume(String path) {
            this.path = path;
        }

        String path() {
            return path;
        }
    }

    private static final class Sink {
        int kept;
        int capped;
        int refs;
        long counted;
        boolean any;
        long skipped;
    }

    public static void main(String[] args) {
        Input input = new Input();
        List<Volume> volumes = new ArrayList<Volume>();
        volumes.add(new Volume(new String("/ssd")));
        volumes.add(new Volume(new String("/hdd")));
        Map<String, List<String>> aliases =
                new HashMap<String, List<String>>();
        Sink sink = new Sink();

        require(System.startConcolicRegion("REGION.stream", "TASK.stream")
                == 0L, "region start rejected");
        System.symbolizeField(input, "disk", "DISK");
        System.symbolizeField(input, "alias", "ALIAS");
        System.symbolizeExactField(input, Input.class.getName(), "max", "I",
                "MAX");

        // 1. A concrete list, filtered by a predicate reading a tracked list.
        List<String> slow = new ArrayList<String>();
        slow.add(input.disk);
        List<Volume> kept = volumes.stream()
                .filter(v -> !slow.contains(v.path))
                .collect(Collectors.toList());
        sink.kept = kept.size();
        String keptVersions = System.getSharedMapVersions(kept);
        String keptSize = field(sink, "kept", "I", Integer.valueOf(sink.kept));

        // 1b. The tracked list itself: READs of its state, its end pinned.
        List<String> fast = slow.stream().filter(s -> s.startsWith("/s"))
                .collect(Collectors.toList());
        String fastVersions = System.getSharedMapVersions(fast);

        // 2. A symbolic limit, a map, a collect.
        List<String> capped = volumes.stream().limit(input.max)
                .map(Volume::path).collect(Collectors.toList());
        sink.capped = capped.size();
        String cappedSize = field(sink, "capped", "I",
                Integer.valueOf(sink.capped));

        // 3. An unmodifiable map's entries, filtered twice, mapped to keys.
        aliases.put(input.alias,
                new ArrayList<String>(Arrays.asList("c1")));
        aliases.put(new String("other"),
                new ArrayList<String>(Arrays.asList("c2")));
        List<String> refs = Collections.unmodifiableMap(aliases).entrySet()
                .stream()
                .filter(e -> !e.getKey().equals("c1"))
                .filter(e -> e.getValue().contains("c1"))
                .map(Map.Entry::getKey)
                .collect(Collectors.toList());
        sink.refs = refs.size();
        String refsSize = field(sink, "refs", "I", Integer.valueOf(sink.refs));

        // 4. count and anyMatch.
        sink.counted = volumes.stream()
                .filter(v -> !slow.contains(v.path)).count();
        sink.any = volumes.stream().anyMatch(v -> slow.contains(v.path));
        String counted = field(sink, "counted", "J",
                Long.valueOf(sink.counted));
        String any = field(sink, "any", "Z", Boolean.valueOf(sink.any));

        // 5. A set.
        Set<String> paths = volumes.stream().map(Volume::path)
                .filter(p -> !slow.contains(p))
                .collect(Collectors.toSet());
        String pathsVersions = System.getSharedMapVersions(paths);

        // 6. Nothing symbolic: the run's result, no state, no gap.
        List<Volume> plain = volumes.stream()
                .filter(v -> v.path.length() > 2)
                .collect(Collectors.toList());
        String plainVersions = System.getSharedMapVersions(plain);

        // 7. An unmodeled operation over a symbolic source.
        sink.skipped = slow.stream().skip(1).count();
        String summary = System.getConcolicRegionSummary();
        System.endConcolic();

        System.out.println("KEPT " + keptVersions);
        System.out.println("CAPPED " + cappedSize);
        System.out.println("REFS " + refsSize);
        System.out.println("SUMMARY " + summary);

        require(kept.size() == 1 && capped.size() == 1 && refs.size() == 1
                        && sink.counted == 1L && sink.any
                        && paths.size() == 1 && plain.size() == 2
                        && sink.skipped == 0L,
                "a modeled pipeline changed what the program computed");
        require(keptVersions.contains("\"versionKind\":\"STATE_COLLECT\"")
                        && keptVersions.contains("\"initialSnapshot\":"
                                + "{\"stated\":true,\"entries\":0,")
                        && keptVersions.contains(
                                "\"operation\":\"APPEND_IF\"")
                        && keptVersions.contains("\"guard\":")
                        && keptVersions.contains("\"operation\":\"CONTAINS\""),
                "the filtered list is no APPEND_IF chain under the "
                        + "predicate: " + keptVersions);
        require(keptSize.contains("\"operation\":\"SIZE\"")
                        && keptSize.contains("APPEND_IF"),
                "the filtered list's size is no SIZE of its chain: "
                        + keptSize);
        require(fastVersions.contains("\"operation\":\"READ\"")
                        && fastVersions.contains("\"operation\":\"PIN\"")
                        && fastVersions.contains("startsWith"),
                "a stream over a tracked list does not read its members or "
                        + "pin its end: " + fastVersions);
        require(cappedSize.contains("APPEND_IF") && cappedSize.contains("MAX")
                        && cappedSize.contains("\"operation\":\"PIN\""),
                "the limited list is no chain under its bound: "
                        + cappedSize);
        require(refsSize.contains("APPEND_IF")
                        && refsSize.contains("ALIAS"),
                "the alias entries' keys are no chain under their filters: "
                        + refsSize);
        require(counted.contains("\"operation\":\"SIZE\"")
                        && counted.contains("APPEND_IF"),
                "count is no SIZE of a chain: " + counted);
        require(any.contains("\"operation\":\"IS_EMPTY\""),
                "anyMatch is no IS_EMPTY of a chain: " + any);
        require(pathsVersions.contains("\"operation\":\"PUT_IF\""),
                "the collected set is no PUT_IF chain: " + pathsVersions);
        require(plainVersions.contains("\"selected\":false"),
                "a concrete pipeline was stated: " + plainVersions);
        require(summary.contains("STREAM_OPERATION_UNMODELED:skip")
                        && summary.contains("STREAM_PINNED:SOURCE_END")
                        && summary.contains("STREAM_PINNED:LIMIT_EXHAUSTED"),
                "the region names no stream gap: " + summary);
        System.out.println("CAUSYNTH_REGION_STREAM_SMOKE_OK");
    }

    private static String field(Sink sink, String name, String descriptor,
                                Object value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, descriptor, value);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
