package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ZkChain;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

public final class ZkCausalGraph {
    private final RecordedStore store;

    private ZkCausalGraph(RecordedStore store) {
        this.store = store;
    }

    public static ZkCausalGraph of(RecordedStore store) {
        return new ZkCausalGraph(store);
    }

    public boolean zkCarried(String occurrence) {
        return !store.consumedBy(occurrence).isEmpty();
    }

    public boolean decoded(Collection<Integer> objects) {
        return !store.versionsOf(objects).isEmpty();
    }

    public Chain chain(Collection<String> targets, Map<String, Long> seeds,
                       Function<String, Collection<String>> senders) {
        Set<String> occurrences = new LinkedHashSet<>(targets);
        Map<String, String> paths = new LinkedHashMap<>();
        Map<String, Long> versions = new LinkedHashMap<>();
        Deque<String> work = new ArrayDeque<>(targets);
        Deque<Map.Entry<String, Long>> located =
                new ArrayDeque<>(seeds.entrySet());
        Set<String> nodes = new LinkedHashSet<>();
        for (String target : targets) nodes.add(node(target));
        for (Map.Entry<String, Long> seed : seeds.entrySet()) {
            for (String decode : store.decodesUpTo(seed.getKey(),
                    seed.getValue())) {
                if (nodes.contains(node(decode))) occurrences.add(decode);
            }
        }
        while (!work.isEmpty() || !located.isEmpty()) {
            while (!work.isEmpty()) {
                String occurrence = work.removeFirst();
                located.addAll(store.consumedBy(occurrence).entrySet());
                for (String sender : senders.apply(occurrence)) {
                    if (occurrences.add(sender)) work.add(sender);
                }
            }
            while (!located.isEmpty()) {
                Map.Entry<String, Long> read = located.removeFirst();
                String location = read.getKey();
                Long held = versions.get(location);
                if (held != null && held >= read.getValue()) continue;
                versions.put(location, read.getValue());
                paths.putIfAbsent(location, store.slotOf(location));
                for (String writer : store.writersUpTo(location,
                        read.getValue())) {
                    if (occurrences.add(writer)) work.add(writer);
                }
            }
        }
        return new Chain(paths, versions, occurrences);
    }

    public Map<String, Map<String, Set<String>>> keys(Chain chain,
                                                      Collection<Integer>
                                                              seeds,
                                                      Collection<String>
                                                              whole) {
        Map<String, Set<String>> pointers = new LinkedHashMap<>();
        Deque<String[]> work = new ArrayDeque<>();
        for (Integer object : seeds) {
            for (RecordedStore.Leaf leaf : store.parsedAs(object)) {
                if (!chain.paths.containsKey(leaf.location)) continue;
                if (pointers.computeIfAbsent(leaf.location,
                        ignored -> new LinkedHashSet<>()).add(leaf.pointer)) {
                    work.add(new String[]{leaf.location, leaf.pointer});
                }
            }
        }
        Map<String, Map<String, Set<String>>> keys = new LinkedHashMap<>();
        while (!work.isEmpty()) {
            String[] at = work.removeFirst();
            for (RecordedStore.Leaf written : store.writtenAt(at[0], at[1],
                    chain.version(at[0]))) {
                carry(keys, written.occurrence, at[0], at[1]);
                for (RecordedStore.Leaf input
                        : store.parsedAs(written.object)) {
                    if (!input.occurrence.equals(written.occurrence)) continue;
                    carry(keys, input.occurrence, input.location,
                            input.pointer);
                    if (pointers.computeIfAbsent(input.location,
                            ignored -> new LinkedHashSet<>())
                            .add(input.pointer)) {
                        work.add(new String[]{input.location,
                                input.pointer});
                    }
                }
            }
        }
        for (String location : chain.paths.keySet()) {
            Set<String> held = pointers.get(location);
            boolean exact = held != null && store.leafStated(location)
                    && !whole.contains(location);
            Set<String> carried = exact ? held
                    : Collections.singleton(WHOLE);
            for (String consumer : store.consumersOf(location)) {
                if (!chain.holds(consumer)) continue;
                for (String pointer : carried) {
                    carry(keys, consumer, location, pointer);
                }
            }
            for (String writer : store.writersUpTo(location,
                    chain.version(location))) {
                for (String pointer : carried) {
                    carry(keys, writer, location, pointer);
                }
            }
        }
        return keys;
    }

    public static final String WHOLE = "";

    private static void carry(Map<String, Map<String, Set<String>>> keys,
                              String occurrence, String location,
                              String pointer) {
        keys.computeIfAbsent(occurrence, ignored -> new LinkedHashMap<>())
                .computeIfAbsent(location, ignored -> new LinkedHashSet<>())
                .add(pointer);
    }

    private static String node(String occurrence) {
        try {
            return OccurrenceAddress.parse(occurrence).node().render();
        } catch (RuntimeException unparsed) {
            return occurrence;
        }
    }

    public static final class Chain {
        public final Map<String, String> paths;
        private final Map<String, Long> versions;
        public final Set<String> occurrences;

        Chain(Map<String, String> paths, Map<String, Long> versions,
              Set<String> occurrences) {
            this.paths = Collections.unmodifiableMap(paths);
            this.versions = versions;
            this.occurrences = Collections.unmodifiableSet(occurrences);
        }

        public boolean holds(String occurrence) {
            return occurrences.contains(occurrence);
        }

        long version(String location) {
            Long held = versions.get(location);
            return held == null ? -1L : held;
        }

        public List<JsonObject> rows() {
            List<JsonObject> rows = new java.util.ArrayList<>();
            for (Map.Entry<String, String> path : paths.entrySet()) {
                int cut = path.getKey().indexOf('\n');
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 1);
                row.addProperty("kind", ZkChain.PATH);
                row.addProperty("transport", path.getKey().substring(0, cut));
                row.addProperty("location", path.getKey().substring(cut + 1));
                row.addProperty("slot", path.getValue());
                rows.add(row);
            }
            for (String occurrence : occurrences) {
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 1);
                row.addProperty("kind", ZkChain.OCCURRENCE);
                row.addProperty("occurrenceId", occurrence);
                rows.add(row);
            }
            return rows;
        }
    }
}
