import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * ConcurrentHashMap by its Map contract: SOLR-18406's reservations
 * ({@code reserves.merge(gen, nanoTime() + R, maxBy)},
 * {@code reserves.getOrDefault(gen, 0L)}) and its known commits.
 *
 * <p>Its bodies run muted, so its table nodes leave no rows of their own;
 * an absent key is a READ of the stated state; what a putIfAbsent,
 * computeIfAbsent or merge stores is guarded by the test its body made of
 * the value at the key (MATCHES, stating what it found), so another state
 * flips it -- what a callback the run never ran would have stored is an
 * unknown cell, by name -- a call that changed nothing publishes no
 * version, and none of them adds a condition to the path; a callback runs with
 * propagation, seeded by the contract, and what it returned is what the
 * mutation stores -- its side effects are versioned like any code's;
 * entrySet().removeIf removes each
 * visited key under the predicate's result; a newKeySet is its map; and
 * the INITIAL walk reads a treeified bin.  A callback call on a map
 * nothing symbolic reached runs as bytecode; a removeIf whose predicate
 * throws after removing refuses its map (CALLBACK_THREW_AFTER_MUTATION); a
 * callback five calls deep, past the window stack, refuses its call's map
 * (CALLBACK_DEPTH_EXCEEDED).</p>
 */
public final class RegionConcurrentHashMapSmoke {
    private static final class Input {
        long generation = 7L;
        long deadline = 100L;
    }

    private static final class Counter {
        int computed;
    }

    private static final class Sink {
        Long value;
        Long absent;
        Long fallback;
        Long merged;
        Long computed;
    }

    // Keys whose hashes collide into one bin.
    private static final class Colliding {
        final int id;

        Colliding(int id) {
            this.id = id;
        }

        @Override
        public int hashCode() {
            return 1;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Colliding && ((Colliding) other).id == id;
        }
    }

    private static final String LONG = "Ljava/lang/Long;";

    public static void main(String[] args) {
        Input input = new Input();
        Counter counter = new Counter();
        Map<Long, Long> reserves = new ConcurrentHashMap<>();
        Map<Long, Long> absentOnly = new ConcurrentHashMap<>();
        ConcurrentHashMap<Colliding, Integer> tree = new ConcurrentHashMap<>();
        for (int id = 0; id < 12; id++) tree.put(new Colliding(id), id);
        Set<Long> keys = ConcurrentHashMap.newKeySet();

        require(System.startConcolicRegion("REGION.chm", "TASK.chm") == 0L,
                "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(),
                "generation", "J", "GENERATION");
        System.symbolizeExactField(input, Input.class.getName(), "deadline",
                "J", "DEADLINE");
        System.observeField(counter, Counter.class.getName(), "computed",
                "I");
        Sink sink = new Sink();

        // put, get, an absent get and getOrDefault.
        reserves.put(input.generation, input.deadline);
        sink.value = reserves.get(input.generation);
        sink.absent = absentOnly.get(input.generation);
        sink.fallback = reserves.getOrDefault(input.generation + 1, 0L);
        String value = field(sink, "value", sink.value);
        String absent = field(sink, "absent", sink.absent);
        String fallback = field(sink, "fallback", sink.fallback);

        // putIfAbsent, both ways: a PUT_IF each, a version only for the one
        // that put.
        int before = conditions();
        reserves.putIfAbsent(input.generation, 1L);
        reserves.putIfAbsent(input.generation + 2, 2L);
        String presence = System.getSharedMapVersions(reserves);

        // merge, both ways: the callback's result is the stored value where
        // the key was there, the value where it was not; what the absent
        // arm's callback, which did not run, would have stored is unknown.
        sink.merged = reserves.merge(input.generation, input.deadline + 5,
                (old, update) -> old + update);
        reserves.merge(input.generation + 3, input.deadline, Long::sum);
        String mergeLog = System.getSharedMapVersions(reserves);
        String merged = field(sink, "merged", sink.merged);
        int after = conditions();
        String pinned = System.getConcolicRegionSummary();

        // computeIfAbsent: the callback writes a tracked field.
        sink.computed = reserves.computeIfAbsent(input.generation + 4, key -> {
            counter.computed = 1;
            return key * 2;
        });
        String computed = field(sink, "computed", sink.computed);
        String counted = System.getSharedFieldVersions(counter,
                Counter.class.getName(), "computed", "I");

        // entrySet().removeIf: each visited key under the predicate.
        reserves.entrySet().removeIf(entry -> entry.getValue() > 150L);
        String map = System.getSharedMapVersions(reserves);

        // A newKeySet is its map.
        keys.add(input.generation);
        boolean contained = keys.contains(input.generation);
        String keySet = System.getSharedMapVersions(keys);

        // The INITIAL walk of a treeified bin.
        tree.put(new Colliding(99), (int) input.generation);
        String treeVersions = System.getSharedMapVersions(tree);

        // A callback call nothing symbolic reached: bytecode, no log.
        Map<Long, Long> untracked = new ConcurrentHashMap<>();
        untracked.computeIfAbsent(1L, key -> key + 1);
        String untrackedLog = System.getSharedMapVersions(untracked);

        // A predicate that throws after the first removal.
        Map<Long, Long> removing = new ConcurrentHashMap<>();
        removing.put(input.generation, 1L);
        removing.put(input.generation + 1, 2L);
        try {
            removing.keySet().removeIf(key -> {
                if (key > 7L) throw new IllegalStateException("partial");
                return true;
            });
        } catch (IllegalStateException expected) {
            // the map kept what the predicate saw before it threw
        }
        String removingLog = System.getSharedMapVersions(removing);

        // Five nested callback calls: the fifth is past the window stack.
        Map<Long, Long> m1 = new ConcurrentHashMap<>();
        Map<Long, Long> m2 = new ConcurrentHashMap<>();
        Map<Long, Long> m3 = new ConcurrentHashMap<>();
        Map<Long, Long> m4 = new ConcurrentHashMap<>();
        Map<Long, Long> m5 = new ConcurrentHashMap<>();
        m1.computeIfAbsent(input.generation, a -> m2.computeIfAbsent(a,
                b -> m3.computeIfAbsent(b, c -> m4.computeIfAbsent(c,
                        d -> m5.computeIfAbsent(d, e -> e + 1)))));
        // Four windows stand open inside m4's callback; m5's is the fifth.
        String deepest = System.getSharedMapVersions(m5);
        System.endConcolic();

        System.out.println("VALUE " + value);
        System.out.println("ABSENT " + absent);
        System.out.println("MERGE " + merged);
        System.out.println("MAP " + map);

        require(contained, "the key set lost its key");
        require(value.contains("\"operation\":\"READ\"")
                        && value.contains("DEADLINE"),
                "the get does not read the put: " + value);
        require(absent.contains("\"operation\":\"READ\"")
                        && absent.contains("\"operation\":\"SNAPSHOT_BASE\""),
                "the absent get is no READ of a stated state: " + absent);
        require(fallback.contains("\"operation\":\"READ_OR_DEFAULT\""),
                "getOrDefault is no READ_OR_DEFAULT: " + fallback);
        require(count(presence, "\"versionKind\":\"STATE_PUT_IF\",") == 1
                        && count(presence, "\"operation\":\"MATCHES\"") >= 2
                        && presence.contains("\"answer\":"),
                "putIfAbsent is no PUT_IF guarded by what it found: "
                        + presence);
        require(after == before,
                "a model's choice added a path condition: " + before + " -> "
                        + after);
        require(merged.contains("DEADLINE") && merged.contains("\"+\""),
                "merge's callback result is not what it stored: " + merged);
        require(mergeLog.contains("\"operation\":\"UNKNOWN\"")
                        && pinned.contains("CONTAINER_PINNED:merge"),
                "merge's uncalled arm is no named unknown cell: " + mergeLog);
        require(computed.contains("GENERATION")
                        && counted.contains("\"versionKind\":\"WRITE\""),
                "computeIfAbsent lost its callback or its side effect: "
                        + computed + " / " + counted);
        require(map.contains("\"operation\":\"REMOVE_IF\"")
                        && map.contains("\"guard\":")
                        && !map.contains("ConcurrentHashMap$Node"),
                "removeIf is no guarded REMOVE_IF, or a node leaked: " + map);
        require(map.contains("\"versionKind\":\"STATE_PUT\"")
                        && map.contains("\"initialSnapshot\":{\"stated\":true,"
                                + "\"entries\":0,"),
                "the map's log does not start at its stated empty base: "
                        + map);
        require(keySet.contains("\"versionKind\":\"STATE_ADD\"")
                        && keySet.contains("\"selected\":true"),
                "the key set is not its map's location: " + keySet);
        require(treeVersions.contains("\"initialSnapshot\":{\"stated\":true,"
                        + "\"entries\":12,"),
                "the treeified bin was not walked: " + treeVersions);
        require(untrackedLog.contains("\"selected\":false"),
                "a concrete callback call was modeled: " + untrackedLog);
        require(removingLog.contains("CALLBACK_THREW_AFTER_MUTATION"),
                "a partial removeIf was not refused: " + removingLog);
        require(deepest.contains("CALLBACK_DEPTH_EXCEEDED"),
                "a declined callback window was not refused: " + deepest);
        System.out.println("CAUSYNTH_REGION_CONCURRENT_HASH_MAP_SMOKE_OK");
    }

    private static int conditions() {
        String all = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        String key = "\"conditionCount\":";
        int at = all.indexOf(key) + key.length();
        int end = at;
        while (Character.isDigit(all.charAt(end))) end++;
        return Integer.parseInt(all.substring(at, end));
    }

    private static String field(Sink sink, String name, Long value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, LONG, value);
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
