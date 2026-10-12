package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
 */
public final class RecordedStore {
    /** One STORE trace row. */
    public static final class Event {
        final boolean write;
        final String transport;
        final String location;
        final long version;
        /** A write's occurrence address, rendered. */
        final String occurrence;
        /** A decode's objects, renamed as every row names them. */
        public final int[] objects;

        private Event(boolean write, String transport, String location,
                      long version, String occurrence, int[] objects) {
            this.write = write;
            this.transport = transport;
            this.location = location;
            this.version = version;
            this.occurrence = occurrence;
            this.objects = objects;
        }

        public static Event written(String transport, String location,
                                    long version, String occurrence) {
            return new Event(true, transport, location, version, occurrence,
                    new int[0]);
        }

        public static Event decoded(String transport, String location,
                                    long version, int[] objects) {
            return new Event(false, transport, location, version, "",
                    objects);
        }

        String key() {
            return transport + "\n" + location;
        }
    }

    /** transport + location -> version -> the occurrences that made it. */
    private final Map<String, TreeMap<Long, Set<String>>> writers =
            new HashMap<>();
    /** object -> the versions (transport + location -> version) it holds. */
    private final Map<Integer, Map<String, Long>> decoded = new HashMap<>();

    public RecordedStore(Collection<Event> events) {
        for (Event event : events == null
                ? Collections.<Event>emptyList() : events) {
            if (event.write) {
                if (event.occurrence.isEmpty()) continue;
                writers.computeIfAbsent(event.key(), ignored -> new TreeMap<>())
                        .computeIfAbsent(event.version,
                                ignored -> new LinkedHashSet<>())
                        .add(event.occurrence);
                continue;
            }
            for (int object : event.objects) {
                if (object == 0) continue;
                // The first decode that registered it keeps it (runtime.
                // Provenance): a later row naming it again names no object.
                decoded.computeIfAbsent(object, ignored -> new HashMap<>())
                        .putIfAbsent(event.key(), event.version);
            }
        }
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
