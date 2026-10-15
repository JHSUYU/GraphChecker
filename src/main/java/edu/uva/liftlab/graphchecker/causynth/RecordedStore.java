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
 * trace rows: which occurrence made each version of each location, which
 * version each decoded object was parsed from, and which occurrence read,
 * decoded or was called back on each location.  What PLAN asks of it: the
 * versions a set of objects holds ({@link #versionsOf}), and the writers a
 * location rests on ({@link #writersOf}) -- every writer of every version,
 * never pruned by the recorded order (owner 2026-09-29): another schedule
 * of the same writes is another version history -- and the ZooKeeper causal
 * graph's two sides ({@link #consumedBy}, {@link #consumersOf}, {@code
 * ZkCausalGraph}).  And which fetch made each decode: the occurrence that
 * read the version and when, whose store-read doors PLAN asks where the
 * fetch lies on the data flow ({@link #fetchesOf}).  A decode of a version its
 * own occurrence wrote (Solr's aliases parsed from the bytes a compare-and-
 * set just stored) fetched nothing: its objects hold the version, and no
 * read door is on their flow.
 */
public final class RecordedStore {
    /** One STORE trace row: a write, a decode, a read that decoded
     *  nothing, or a watch callback. */
    public static final class Event {
        enum Kind { WRITE, DECODE, READ, FIRED, LEAVES }

        final Kind kind;
        final boolean write;
        final String transport;
        final String location;
        /** The version written, decoded or read; -1 for a callback, whose
         *  version is the next read's. */
        final long version;
        /** A write's occurrence address, rendered; a decode's fetch's, or
         *  "" (a provenance site's derived object); a read's or a
         *  callback's own. */
        final String occurrence;
        /** The row's trace seq: a decode's comes right after its fetch. */
        final long seq;
        /** A decode's objects, or a LEAVES row's leaf objects, renamed as
         *  every row names them. */
        public final int[] objects;
        /** A LEAVES row's pointers, parallel to {@link #objects} (CONTENT
         *  port spelling, '|' for '/'); null: past the bound, the whole
         *  document. */
        final String[] pointers;
        /** A LEAVES row's side: what a write serialized (else a parse). */
        final boolean serialized;
        /** The location as session rows spell it ({@code
         *  MessageDoors#storeLocation}'s slot, stated at record time while
         *  the run's names are known); the raw location where the row
         *  states none. */
        private String slot;

        private Event(Kind kind, String transport, String location,
                      long version, String occurrence, long seq,
                      int[] objects) {
            this(kind, transport, location, version, occurrence, seq,
                    objects, new String[0], false);
        }

        private Event(Kind kind, String transport, String location,
                      long version, String occurrence, long seq,
                      int[] objects, String[] pointers, boolean serialized) {
            this.pointers = pointers;
            this.serialized = serialized;
            this.kind = kind;
            this.write = kind == Kind.WRITE;
            this.transport = transport;
            this.location = location;
            this.version = version;
            this.occurrence = occurrence == null ? "" : occurrence;
            this.seq = seq;
            this.objects = objects;
            this.slot = location;
        }

        /** This event, its location spelled {@code slot} in session rows
         *  ("" keeps the raw location). */
        public Event slot(String slot) {
            if (slot != null && !slot.isEmpty()) this.slot = slot;
            return this;
        }

        public static Event written(String transport, String location,
                                    long version, String occurrence,
                                    long seq) {
            return new Event(Kind.WRITE, transport, location, version,
                    occurrence, seq, new int[0]);
        }

        public static Event decoded(String transport, String location,
                                    long version, int[] objects,
                                    String fetch, long seq) {
            return new Event(Kind.DECODE, transport, location, version, fetch,
                    seq, objects);
        }

        /** A read that decoded nothing (getData, exists, getChildren). */
        public static Event read(String transport, String location,
                                 long version, String occurrence, long seq) {
            return new Event(Kind.READ, transport, location, version,
                    occurrence, seq, new int[0]);
        }

        /** The leaves one write serialized ({@code write}) or one parse
         *  read, each pointer with its leaf object; {@code pointers} null
         *  past the bound (the whole document). */
        public static Event leaves(boolean write, String transport,
                                   String location, long version,
                                   String occurrence, long seq,
                                   String[] pointers, int[] objects) {
            return new Event(Kind.LEAVES, transport, location, version,
                    occurrence, seq, pointers == null ? new int[0] : objects,
                    pointers, write);
        }

        /** A watch callback on {@code location}, in {@code occurrence}. */
        public static Event fired(String transport, String location,
                                  String occurrence, long seq) {
            return new Event(Kind.FIRED, transport, location, -1L,
                    occurrence, seq, new int[0]);
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
    /** occurrence -> the locations it read, decoded or was called back on. */
    private final Map<String, Set<String>> consumed = new HashMap<>();
    /** transport + location -> the occurrences that consumed it. */
    private final Map<String, Set<String>> consumers = new HashMap<>();
    /** transport + location -> its session-row slot. */
    private final Map<String, String> slots = new HashMap<>();
    /** Leaf object -> each (location, pointer, occurrence) a parse read it
     *  at. */
    private final Map<Integer, List<Leaf>> parsedLeaves = new HashMap<>();
    /** transport + location -> pointer -> each (occurrence, leaf object) a
     *  write serialized there. */
    private final Map<String, Map<String, List<Leaf>>> writtenLeaves =
            new HashMap<>();
    /** Locations some LEAVES row states whole (past the bound). */
    private final Set<String> whole = new java.util.HashSet<>();
    /** Locations some LEAVES row states leaf by leaf. */
    private final Set<String> leafed = new java.util.HashSet<>();

    /** One leaf of one LEAVES row. */
    static final class Leaf {
        final String location;
        final String pointer;
        final String occurrence;
        final int object;

        Leaf(String location, String pointer, String occurrence, int object) {
            this.location = location;
            this.pointer = pointer;
            this.occurrence = occurrence;
            this.object = object;
        }
    }

    public RecordedStore(Collection<Event> events) {
        List<Event> ordered = new ArrayList<>(events == null
                ? Collections.<Event>emptyList() : events);
        ordered.sort(Comparator.comparingLong(event -> event.seq));
        for (Event event : ordered) {
            slots.putIfAbsent(event.key(), event.slot);
            if (event.kind == Event.Kind.LEAVES) {
                leaves(event);
                continue;
            }
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
            if (event.write || event.kind == Event.Kind.LEAVES) continue;
            if (!event.occurrence.isEmpty()) {
                consumed.computeIfAbsent(event.occurrence,
                        ignored -> new LinkedHashSet<>()).add(event.key());
                consumers.computeIfAbsent(event.key(),
                        ignored -> new LinkedHashSet<>())
                        .add(event.occurrence);
            }
            if (event.kind != Event.Kind.DECODE) continue;
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

    /** Indexes one LEAVES row. */
    private void leaves(Event event) {
        if (event.pointers == null) {
            whole.add(event.key());
            return;
        }
        leafed.add(event.key());
        for (int at = 0; at < event.pointers.length
                && at < event.objects.length; at++) {
            Leaf leaf = new Leaf(event.key(), event.pointers[at],
                    event.occurrence, event.objects[at]);
            if (event.serialized) {
                writtenLeaves.computeIfAbsent(event.key(),
                        ignored -> new HashMap<>())
                        .computeIfAbsent(leaf.pointer,
                                ignored -> new ArrayList<>()).add(leaf);
            } else if (leaf.object != 0) {
                parsedLeaves.computeIfAbsent(leaf.object,
                        ignored -> new ArrayList<>()).add(leaf);
            }
        }
    }

    /** Each (location, pointer, occurrence) a parse read {@code object}
     *  at. */
    List<Leaf> parsedAs(int object) {
        return parsedLeaves.getOrDefault(object,
                Collections.<Leaf>emptyList());
    }

    /** Each write's leaf at {@code pointer} of {@code location}, every
     *  version. */
    List<Leaf> writtenAt(String location, String pointer) {
        Map<String, List<Leaf>> at = writtenLeaves.get(location);
        return at == null ? Collections.<Leaf>emptyList()
                : at.getOrDefault(pointer, Collections.<Leaf>emptyList());
    }

    /** Whether a location's leaves were ever stated, and never past the
     *  bound: a field-level chain over it is exact. */
    boolean leafStated(String location) {
        return !whole.contains(location) && leafed.contains(location);
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

    /** The occurrences (rendered addresses) that made any version of {@code
     *  location} (transport + location), the latest version's first. */
    List<String> writersOf(String location) {
        TreeMap<Long, Set<String>> made = writers.get(location);
        List<String> found = new ArrayList<>();
        if (made == null) return found;
        for (Set<String> at : made.descendingMap().values()) {
            for (String occurrence : at) {
                if (!found.contains(occurrence)) found.add(occurrence);
            }
        }
        return found;
    }

    /** The locations (transport + location) {@code occurrence} read,
     *  decoded or was called back on: a ZooKeeper-carried occurrence where
     *  any. */
    Set<String> consumedBy(String occurrence) {
        return consumed.getOrDefault(occurrence,
                Collections.<String>emptySet());
    }

    /** {@code location}'s (transport + location) spelling in session
     *  rows. */
    String slotOf(String location) {
        String slot = slots.get(location);
        return slot != null ? slot
                : location.substring(location.indexOf('\n') + 1);
    }

    /** The occurrences that read, decoded or were called back on {@code
     *  location} (transport + location). */
    Set<String> consumersOf(String location) {
        return consumers.getOrDefault(location,
                Collections.<String>emptySet());
    }
}
