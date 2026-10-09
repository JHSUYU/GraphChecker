import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.TreeMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;
import java.util.stream.Collector;
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
 *
 * <p>And the review's shapes: a barrier ahead of the first callback over a
 * stateful source pins the result (it once pinned the source empty); a
 * forEach names what it pinned; a values view reads its map's state; a
 * callback mutating the source unstates the result; a natural order an
 * application compareTo decided is pinned and named; a collector kept in a
 * field is known at every use.</p>
 *
 * <p>And toMap: a map's entries collected to keys and joined values in the
 * supplier's map (Solr's Aliases.convertMapOfListToMapOfCommaDelimited) is
 * a PUT chain from its stated empty base; symbolic keys a run found new
 * stand where an earlier one may equal them, with an UNKNOWN cell for what
 * the merge function would have stored; a merge function the run called
 * is stated as what it answered over a READ of the map so far, a null
 * answer a removal; a filter's symbolic drop before the mappers is pinned;
 * a supplier's map that is no empty modeled map (a TreeMap, one already
 * holding members) leaves the result the run's own.</p>
 */
public final class RegionStreamSmoke {
    private static final Collector<Object, ?, List<Object>> TO_LIST =
            Collectors.toList();

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

    private static final class Disk implements Comparable<Disk> {
        final String path;

        Disk(String path) {
            this.path = path;
        }

        @Override
        public int compareTo(Disk other) {
            return path.compareTo(other.path);
        }
    }

    private static final class Sink {
        int kept;
        int capped;
        int refs;
        long counted;
        boolean any;
        long skipped;
        int seen;
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

        // 8. A barrier ahead of the first callback over a stateful source:
        // its members entered sorted unseen, so the result is the run's
        // (never a pin of the source's size to 0); over a concrete source
        // the members past the barrier are stated.
        List<String> sortedFast = slow.stream().sorted()
                .filter(s -> s.startsWith("/s"))
                .collect(Collectors.toList());
        String sortedFastVersions = System.getSharedMapVersions(sortedFast);
        List<Volume> sortedKept = volumes.stream()
                .sorted(Comparator.comparing(Volume::path))
                .filter(v -> !slow.contains(v.path))
                .collect(Collectors.toList());
        String sortedKeptVersions = System.getSharedMapVersions(sortedKept);

        // 9. forEach after a symbolic filter: no chain, so what it pinned
        // is named.
        List<String> two = new ArrayList<String>();
        two.add(input.disk);
        two.add(new String("/x"));
        two.stream().filter(s -> s.startsWith("/s"))
                .forEach(s -> sink.seen++);

        // 10. A values view of a stateful map reads the map's state.
        Map<String, Integer> weights = new HashMap<String, Integer>();
        weights.put(input.disk, Integer.valueOf(3));
        List<Integer> heavy = weights.values().stream()
                .filter(w -> w.intValue() > 1).collect(Collectors.toList());
        String heavyVersions = System.getSharedMapVersions(heavy);

        // 11. A callback mutating the source.
        Map<String, Integer> live = new ConcurrentHashMap<String, Integer>();
        live.put(input.disk, Integer.valueOf(1));
        List<String> touched = live.keySet().stream().filter(k -> {
            live.put(new String("/z"), Integer.valueOf(2));
            return true;
        }).collect(Collectors.toList());

        // 12. A natural order an application compareTo decides.
        List<Disk> disks = new ArrayList<Disk>();
        disks.add(new Disk(new String("/hdd")));
        disks.add(new Disk(new String("/ssd")));
        List<Disk> ordered = disks.stream().sorted()
                .filter(d -> !slow.contains(d.path))
                .collect(Collectors.toList());

        // 13. A collector kept in a field.
        List<Object> reused = volumes.stream()
                .filter(v -> !slow.contains(v.path)).collect(TO_LIST);
        String reusedVersions = System.getSharedMapVersions(reused);

        // 14. toMap: an alias map's entries to keys and joined values.
        Map<String, String> joined = aliases.entrySet().stream()
                .collect(Collectors.toMap(Map.Entry::getKey,
                        e -> String.join(",", e.getValue()),
                        (a, b) -> {
                            throw new IllegalStateException(b);
                        }, LinkedHashMap::new));
        String joinedVersions = System.getSharedMapVersions(joined);
        // 14b. Symbolic keys, toMap's own HashMap and throwing merger.
        Map<String, Integer> lengths = two.stream()
                .collect(Collectors.toMap(s -> s, String::length));
        String lengthsVersions = System.getSharedMapVersions(lengths);
        // 14c. A merge function the run called.
        List<String> twice = new ArrayList<String>();
        twice.add(input.disk);
        twice.add(input.disk);
        Map<String, String> merged = twice.stream()
                .collect(Collectors.toMap(s -> s, s -> s,
                        (a, b) -> a.concat(b)));
        String mergedVersions = System.getSharedMapVersions(merged);
        // 14d. A merge function answering null removes the key.
        Map<String, String> removed = twice.stream()
                .collect(Collectors.toMap(s -> s, s -> s, (a, b) -> null));
        String removedVersions = System.getSharedMapVersions(removed);
        // 14e. A filter before the mappers.
        Map<String, String> filtered = two.stream()
                .filter(s -> s.startsWith("/s"))
                .collect(Collectors.toMap(s -> s, s -> s));
        String filteredVersions = System.getSharedMapVersions(filtered);
        // 14f, 14g. A supplier's map no empty modeled map: a TreeMap, and
        // one already holding a member.
        Map<String, String> sorted = aliases.entrySet().stream()
                .collect(Collectors.toMap(Map.Entry::getKey, e -> "v",
                        (a, b) -> a, TreeMap::new));
        Supplier<Map<String, String>> holding = () -> {
            Map<String, String> held = new HashMap<String, String>();
            held.put("pre", "x");
            return held;
        };
        Map<String, String> prefilled = aliases.entrySet().stream()
                .collect(Collectors.toMap(Map.Entry::getKey, e -> "v",
                        (a, b) -> a, holding));
        String prefilledVersions = System.getSharedMapVersions(prefilled);
        String summary = System.getConcolicRegionSummary();
        System.endConcolic();

        System.out.println("KEPT " + keptVersions);
        System.out.println("CAPPED " + cappedSize);
        System.out.println("REFS " + refsSize);
        System.out.println("SUMMARY " + summary);
        System.out.println("JOINED " + joinedVersions);
        System.out.println("LENGTHS " + lengthsVersions);
        System.out.println("MERGED " + mergedVersions);

        require(kept.size() == 1 && capped.size() == 1 && refs.size() == 1
                        && sink.counted == 1L && sink.any
                        && paths.size() == 1 && plain.size() == 2
                        && sink.skipped == 0L && sortedFast.size() == 1
                        && sortedKept.size() == 1 && sink.seen == 1
                        && heavy.size() == 1 && touched.size() >= 1
                        && ordered.size() == 1 && reused.size() == 1
                        && joined.size() == 2 && lengths.size() == 2
                        && merged.size() == 1
                        && merged.get(input.disk).length() == 8
                        && removed.isEmpty() && filtered.size() == 1
                        && sorted.size() == 2 && prefilled.size() == 3,
                "a modeled pipeline changed what the program computed");
        require(joinedVersions.contains("\"versionKind\":\"STATE_COLLECT\"")
                        && joinedVersions.contains("\"operation\":\"PUT")
                        && joinedVersions.contains("ALIAS")
                        && !joinedVersions.contains("\"operation\":"
                                + "\"UNKNOWN\"")
                        && !summary.contains(
                                "STREAM_OPERATION_UNMODELED:collect"),
                "toMap is no PUT chain of its entries' constant keys: "
                        + joinedVersions);
        require(lengthsVersions.contains("\"operation\":\"MATCHES\"")
                        && lengthsVersions.contains("\"operation\":"
                                + "\"UNKNOWN\"")
                        && lengthsVersions.contains("length")
                        && summary.contains("STREAM_PINNED:MERGE"),
                "a symbolic key a run found new is not tested against the"
                        + " keys before it: " + lengthsVersions);
        require(mergedVersions.contains("concat")
                        && mergedVersions.contains("\"operation\":\"READ\"")
                        && !mergedVersions.contains("\"operation\":"
                                + "\"UNKNOWN\""),
                "a merge function the run called is not stated: "
                        + mergedVersions);
        require(removedVersions.contains("\"operation\":\"REMOVE_IF\""),
                "a merge function's null is no removal: " + removedVersions);
        require(filteredVersions.contains("startsWith")
                        && filteredVersions.contains("\"operation\":\"PIN\"")
                        && summary.contains("STREAM_PINNED:DROPPED"),
                "a filter before toMap is not stated: " + filteredVersions);
        require(summary.contains("STREAM_PINNED:SUPPLIED_MAP")
                        && prefilledVersions.contains("\"selected\":false"),
                "a supplier's map no empty base was stated: "
                        + prefilledVersions);
        require(sortedFastVersions.contains("\"selected\":false")
                        && summary.contains("STREAM_PINNED:SORTED"),
                "a barrier ahead of the first callback was stated: "
                        + sortedFastVersions);
        require(sortedKeptVersions.contains("\"operation\":\"APPEND_IF\"")
                        && !sortedKeptVersions.contains(
                                "\"operation\":\"PIN\""),
                "members past a barrier over a concrete source are not "
                        + "stated as they are: " + sortedKeptVersions);
        require(summary.contains("STREAM_PINNED:FOR_EACH")
                        && count(summary, "STREAM_PINNED:DROPPED") >= 2
                        && count(summary, "STREAM_PINNED:SOURCE_END") >= 2,
                "forEach does not name what it pinned: " + summary);
        require(heavyVersions.contains("\"operation\":\"READ\"")
                        && heavyVersions.contains("APPEND_IF"),
                "a values view does not read its map's state: "
                        + heavyVersions);
        require(summary.contains("STREAM_PINNED:CALLBACK_MUTATES_SOURCE"),
                "a callback mutating the source was not named: " + summary);
        require(summary.contains("STREAM_PINNED:MUTED_APPLICATION:"
                        + "RegionStreamSmoke$Disk.compareTo"),
                "application compareTo run muted was not named: " + summary);
        require(reusedVersions.contains("\"operation\":\"APPEND_IF\""),
                "a collector kept in a field was not known: "
                        + reusedVersions);
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

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + 1)) {
            found++;
        }
        return found;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
