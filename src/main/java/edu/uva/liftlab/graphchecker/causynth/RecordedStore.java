package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * The shared store of the recording (IDENTITY §7.2), read off its STORE
 * trace rows: which occurrence made each version of each location, and which
 * version each decoded object was parsed from.  What PLAN asks of it: the
 * versions a set of objects holds ({@link #versionsOf}), and the writers a
 * version rests on ({@link #writersUpTo}) -- the one that made it and those
 * of every earlier version of its location, since a store keeps one document
 * per location and each write modifies the one before it (Solr's state
 * writer, aliases and every compare-and-set write), the rule COMPOSE's
 * closure applies to every location ({@code compose.RestsOn#closure}).
 * And which fetch made each decode: the occurrence that read the version and
 * when, whose store-read doors PLAN asks where the fetch lies on the data
 * flow ({@link #fetchesOf}, {@link #fetchesAt}).  A decode of a version its
 * own occurrence wrote (Solr's aliases parsed from the bytes a compare-and-
 * set just stored) fetched nothing: its objects hold the version, and no
 * read door is on their flow.
 */
public final class RecordedStore {
    /** One STORE trace row. */
    public static final class Event {
        final boolean write;
        final String transport;
        final String location;
        final long version;
        /** A write's occurrence address, rendered; a decode's fetch's, or
         *  "" (a provenance site's derived object). */
        final String occurrence;
        /** The row's trace seq: a decode's comes right after its fetch. */
        final long seq;
        /** A decode's objects, renamed as every row names them. */
        public final int[] objects;

        private Event(boolean write, String transport, String location,
                      long version, String occurrence, long seq,
                      int[] objects) {
            this.write = write;
            this.transport = transport;
            this.location = location;
            this.version = version;
            this.occurrence = occurrence == null ? "" : occurrence;
            this.seq = seq;
            this.objects = objects;
        }

        public static Event written(String transport, String location,
                                    long version, String occurrence,
                                    long seq) {
            return new Event(true, transport, location, version, occurrence,
                    seq, new int[0]);
        }

        public static Event decoded(String transport, String location,
                                    long version, int[] objects,
                                    String fetch, long seq) {
            return new Event(false, transport, location, version, fetch, seq,
                    objects);
        }

        String key() {
            return transport + "\n" + location;
        }
    }

    /** One fetch of a version, as its decode states it. */
    static final class Fetch {
        /** transport + location. */
        final String location;
        final long version;
        /** The fetching occurrence's address, rendered. */
        final String occurrence;
        /** Its decode's trace seq: the fetch is the store read just before. */
        final long seq;
        /** The seq of the store event its occurrence made last before this
         *  decode (another decode, a write), or 0: the fetch's read came
         *  after it. */
        final long since;

        private Fetch(Event decode, long since) {
            this.location = decode.key();
            this.version = decode.version;
            this.occurrence = decode.occurrence;
            this.seq = decode.seq;
            this.since = since;
        }
    }

    /** transport + location -> version -> the occurrences that made it. */
    private final Map<String, TreeMap<Long, Set<String>>> writers =
            new HashMap<>();
    /** object -> the versions (transport + location -> version) it holds. */
    private final Map<Integer, Map<String, Long>> decoded = new HashMap<>();
    /** object -> the fetch whose decode registered it first. */
    private final Map<Integer, Fetch> fetchedBy = new HashMap<>();
    /** transport + location -> its fetches, in trace order. */
    private final Map<String, List<Fetch>> fetches = new HashMap<>();

    public RecordedStore(Collection<Event> events) {
        List<Event> ordered = new ArrayList<>(events == null
                ? Collections.<Event>emptyList() : events);
        ordered.sort(Comparator.comparingLong(event -> event.seq));
        for (Event event : ordered) {
            if (!event.write || event.occurrence.isEmpty()) continue;
            writers.computeIfAbsent(event.key(), ignored -> new TreeMap<>())
                    .computeIfAbsent(event.version,
                            ignored -> new LinkedHashSet<>())
                    .add(event.occurrence);
        }
        // occurrence -> the seq of its last store event so far.
        Map<String, Long> last = new HashMap<>();
        for (Event event : ordered) {
            Long since = event.occurrence.isEmpty() ? null
                    : last.put(event.occurrence, event.seq);
            if (event.write) continue;
            Fetch fetch = event.occurrence.isEmpty() || wrote(event) ? null
                    : new Fetch(event, since == null ? 0L : since);
            if (fetch != null) {
                fetches.computeIfAbsent(event.key(),
                        ignored -> new ArrayList<>()).add(fetch);
            }
            for (int object : event.objects) {
                if (object == 0) continue;
                // The first decode that registered it keeps it (runtime.
                // Provenance): a later row naming it again names no object.
                decoded.computeIfAbsent(object, ignored -> new HashMap<>())
                        .putIfAbsent(event.key(), event.version);
                if (fetch != null) fetchedBy.putIfAbsent(object, fetch);
            }
        }
    }

    /** Whether a decode's occurrence made the version it decoded. */
    private boolean wrote(Event decode) {
        TreeMap<Long, Set<String>> made = writers.get(decode.key());
        Set<String> at = made == null ? null : made.get(decode.version);
        return at != null && at.contains(decode.occurrence);
    }

    /** No STORE row: nothing to cross. */
    boolean isEmpty() {
        return writers.isEmpty() && decoded.isEmpty();
    }

    /** The versions {@code objects} were decoded from, by location. */
    Map<String, Long> versionsOf(Collection<Integer> objects) {
        Map<String, Long> versions = new HashMap<>();
        for (Integer object : objects) {
            Map<String, Long> held = decoded.get(object);
            if (held == null) continue;
            for (Map.Entry<String, Long> entry : held.entrySet()) {
                versions.merge(entry.getKey(), entry.getValue(), Math::max);
            }
        }
        return versions;
    }

    /** The fetches whose decodes registered {@code objects}. */
    List<Fetch> fetchesOf(Collection<Integer> objects) {
        Set<Fetch> found = new LinkedHashSet<>();
        for (Integer object : objects) {
            Fetch fetch = fetchedBy.get(object);
            if (fetch != null) found.add(fetch);
        }
        return new ArrayList<>(found);
    }

    /** Every fetch of {@code location} (transport + location). */
    List<Fetch> fetchesAt(String location) {
        return fetches.getOrDefault(location,
                Collections.<Fetch>emptyList());
    }

    /** The occurrences (rendered addresses) that made {@code location}'s
     *  versions up to {@code version}, the latest first. */
    List<String> writersUpTo(String location, long version) {
        TreeMap<Long, Set<String>> made = writers.get(location);
        List<String> found = new ArrayList<>();
        if (made == null) return found;
        for (Set<String> at : made.headMap(version, true)
                .descendingMap().values()) {
            for (String occurrence : at) {
                if (!found.contains(occurrence)) found.add(occurrence);
            }
        }
        return found;
    }
}
