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

/**
 * THE ZOOKEEPER CAUSAL TRACE (owner 2026-10-15): which regions a shared
 * store carries a value between, read off the recording's store rows
 * ({@link RecordedStore}) -- each write of a location, and each read,
 * decode or watch callback on it -- as design §3.1 traces a message: a
 * writer of a location is an edge into every occurrence that consumed it.
 * Walked backward from the targets, it is the chain: every location a
 * chain occurrence consumed, every writer of such a location (EVERY
 * version: another schedule of the same writes is another history, so no
 * writer is pruned by the recorded order), the queue item senders a writer
 * applied, and the consumers of a chain location on a chain occurrence's
 * node (a view a pairing may re-point to an older decode of).  Only a
 * chain occurrence carries a store's value symbolically: PLAN admits no
 * other ZooKeeper-carried occurrence on a value rule
 * ({@code RuntimeSelectedRegionFinalizer#failureDirectedClosure}), and GROW
 * extends the chain where a replay exposes an edge it lacks.
 */
public final class ZkCausalGraph {
    private final RecordedStore store;

    private ZkCausalGraph(RecordedStore store) {
        this.store = store;
    }

    /** The recording's store rows, as a causal graph. */
    public static ZkCausalGraph of(RecordedStore store) {
        return new ZkCausalGraph(store);
    }

    /** Whether {@code occurrence} (a rendered address) read, decoded or was
     *  called back on a store location: a ZooKeeper-carried occurrence. */
    public boolean zkCarried(String occurrence) {
        return !store.consumedBy(occurrence).isEmpty();
    }

    /**
     * The chain backward from {@code targets} (rendered addresses) and the
     * locations their values were decoded from ({@code seeds}, transport +
     * location: the objects a target read fields on, {@link
     * RecordedStore#versionsOf}); {@code senders} names the occurrences
     * whose queue items a writer applied.
     */
    public Chain chain(Collection<String> targets, Collection<String> seeds,
                       Function<String, Collection<String>> senders) {
        Set<String> occurrences = new LinkedHashSet<>(targets);
        Map<String, String> paths = new LinkedHashMap<>();
        Set<String> nodes = new LinkedHashSet<>();
        Deque<String> work = new ArrayDeque<>(targets);
        Deque<String> located = new ArrayDeque<>(seeds);
        for (String target : targets) nodes.add(node(target));
        while (!work.isEmpty() || !located.isEmpty()) {
            while (!work.isEmpty()) {
                String occurrence = work.removeFirst();
                located.addAll(store.consumedBy(occurrence));
                for (String sender : senders.apply(occurrence)) {
                    if (occurrences.add(sender)) {
                        nodes.add(node(sender));
                        work.add(sender);
                    }
                }
            }
            while (!located.isEmpty()) {
                String location = located.removeFirst();
                if (paths.containsKey(location)) continue;
                paths.put(location, store.slotOf(location));
                for (String writer : store.writersOf(location)) {
                    if (occurrences.add(writer)) {
                        nodes.add(node(writer));
                        work.add(writer);
                    }
                }
            }
        }
        // The consumers of a chain location on a chain node: the decodes a
        // view there may be re-paired with.  Not walked on: what else they
        // consumed reaches the chain only through their own node's reads.
        for (String location : paths.keySet()) {
            for (String consumer : store.consumersOf(location)) {
                if (nodes.contains(node(consumer))) occurrences.add(consumer);
            }
        }
        return new Chain(paths, occurrences);
    }

    /**
     * THE CHAIN'S FIELDS (owner 2026-10-15: "因果追踪，也去看那个字段"):
     * per chain occurrence and location, the JSON pointers whose leaves the
     * chain carries -- "" for the whole document.  Seeded by the leaves the
     * targets read ({@code seeds}: the objects they read fields on and
     * read, by leaf identity, {@link RecordedStore#parsedAs}); a writer of
     * a chain pointer (every version) carries it, and the leaf it wrote is
     * the leaf object it parsed somewhere -- the leaf's own input -- whose
     * pointer is on the chain in turn; a leaf a writer computed fresh ends
     * the store hop there.  A chain location no seed leaf reaches, or one
     * whose leaves were never stated leaf by leaf (a raw read, a document
     * past the bound), is carried whole, and so is each of {@code whole}:
     * a location a target read a field of a decoded object of, which may
     * derive from any of its leaves (an enum's {@code valueOf} of one is no
     * leaf by identity).  Every chain consumer of a location carries its
     * pointers.
     */
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
            for (RecordedStore.Leaf written : store.writtenAt(at[0], at[1])) {
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
            for (String writer : store.writersOf(location)) {
                for (String pointer : carried) {
                    carry(keys, writer, location, pointer);
                }
            }
        }
        return keys;
    }

    /** The pointer prefix of the whole document. */
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

    /** The occurrences and locations of one chain. */
    public static final class Chain {
        /** transport + location -> its session-row slot. */
        public final Map<String, String> paths;
        public final Set<String> occurrences;

        Chain(Map<String, String> paths, Set<String> occurrences) {
            this.paths = Collections.unmodifiableMap(paths);
            this.occurrences = Collections.unmodifiableSet(occurrences);
        }

        public boolean holds(String occurrence) {
            return occurrences.contains(occurrence);
        }

        /** The chain's ZK_CHAIN_PATH and ZK_CHAIN_OCCURRENCE rows ({@link
         *  ZkChain}). */
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
