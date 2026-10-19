package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

public final class RecordedStore {
    public static final class Event {
        enum Kind { WRITE, DECODE, READ, FIRED, LEAVES }

        final Kind kind;
        final boolean write;
        final String transport;
        final String location;
        final long version;
        final String occurrence;
        final long seq;
        public final int[] objects;
        final String[] pointers;
        final boolean serialized;
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

        public static Event read(String transport, String location,
                                 long version, String occurrence, long seq) {
            return new Event(Kind.READ, transport, location, version,
                    occurrence, seq, new int[0]);
        }

        public static Event leaves(boolean write, String transport,
                                   String location, long version,
                                   String occurrence, long seq,
                                   String[] pointers, int[] objects) {
            return new Event(Kind.LEAVES, transport, location, version,
                    occurrence, seq, pointers == null ? new int[0] : objects,
                    pointers, write);
        }

        public static Event fired(String transport, String location,
                                  String occurrence, long seq) {
            return new Event(Kind.FIRED, transport, location, -1L,
                    occurrence, seq, new int[0]);
        }

        String key() {
            return transport + "\n" + location;
        }
    }

    static final class Fetch {
        final String location;
        final long version;
        final String occurrence;
        final long seq;
        final long since;

        private Fetch(Event decode, long since) {
            this.location = decode.key();
            this.version = decode.version;
            this.occurrence = decode.occurrence;
            this.seq = decode.seq;
            this.since = since;
        }
    }

    private final Map<String, TreeMap<Long, Set<String>>> writers =
            new HashMap<>();
    private final Map<Integer, Map<String, Long>> decoded = new HashMap<>();
    private final Map<Integer, Fetch> fetchedBy = new HashMap<>();
    private final Map<String, Map<String, Long>> consumed = new HashMap<>();
    private final Map<String, TreeMap<Long, Set<String>>> decodes =
            new HashMap<>();
    private final Map<String, Set<String>> consumers = new HashMap<>();
    private final Map<String, String> slots = new HashMap<>();
    private final Map<Integer, List<Leaf>> parsedLeaves = new HashMap<>();
    private final Map<String, Map<String, List<Leaf>>> writtenLeaves =
            new HashMap<>();
    private final Set<String> whole = new java.util.HashSet<>();
    private final Set<String> leafed = new java.util.HashSet<>();

    static final class Leaf {
        final String location;
        final String pointer;
        final String occurrence;
        final int object;
        final long version;

        Leaf(String location, String pointer, String occurrence, int object,
             long version) {
            this.location = location;
            this.pointer = pointer;
            this.occurrence = occurrence;
            this.object = object;
            this.version = version;
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
        Map<String, Long> last = new HashMap<>();
        for (Event event : ordered) {
            Long since = event.occurrence.isEmpty() ? null
                    : last.put(event.occurrence, event.seq);
            if (event.write || event.kind == Event.Kind.LEAVES) continue;
            if (!event.occurrence.isEmpty()) {
                consumed.computeIfAbsent(event.occurrence,
                        ignored -> new LinkedHashMap<>())
                        .merge(event.key(), event.version, Math::max);
                consumers.computeIfAbsent(event.key(),
                        ignored -> new LinkedHashSet<>())
                        .add(event.occurrence);
                if (event.kind == Event.Kind.DECODE) {
                    decodes.computeIfAbsent(event.key(),
                            ignored -> new TreeMap<>())
                            .computeIfAbsent(event.version,
                                    ignored -> new LinkedHashSet<>())
                            .add(event.occurrence);
                }
            }
            if (event.kind != Event.Kind.DECODE) continue;
            Fetch fetch = event.occurrence.isEmpty() || wrote(event) ? null
                    : new Fetch(event, since == null ? 0L : since);
            for (int object : event.objects) {
                if (object == 0) continue;
                decoded.computeIfAbsent(object, ignored -> new HashMap<>())
                        .putIfAbsent(event.key(), event.version);
                if (fetch != null) fetchedBy.putIfAbsent(object, fetch);
            }
        }
    }

    private void leaves(Event event) {
        if (event.pointers == null) {
            whole.add(event.key());
            return;
        }
        leafed.add(event.key());
        for (int at = 0; at < event.pointers.length
                && at < event.objects.length; at++) {
            Leaf leaf = new Leaf(event.key(), event.pointers[at],
                    event.occurrence, event.objects[at], event.version);
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

    List<Leaf> parsedAs(int object) {
        return parsedLeaves.getOrDefault(object,
                Collections.<Leaf>emptyList());
    }

    List<Leaf> writtenAt(String location, String pointer, long version) {
        Map<String, List<Leaf>> at = writtenLeaves.get(location);
        List<Leaf> found = new ArrayList<>();
        if (at == null) return found;
        for (Leaf leaf : at.getOrDefault(pointer,
                Collections.<Leaf>emptyList())) {
            if (leaf.version <= version) found.add(leaf);
        }
        return found;
    }

    boolean leafStated(String location) {
        return !whole.contains(location) && leafed.contains(location);
    }

    private boolean wrote(Event decode) {
        TreeMap<Long, Set<String>> made = writers.get(decode.key());
        Set<String> at = made == null ? null : made.get(decode.version);
        return at != null && at.contains(decode.occurrence);
    }

    boolean isEmpty() {
        return writers.isEmpty() && decoded.isEmpty();
    }

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

    List<Fetch> fetchesOf(Collection<Integer> objects) {
        Set<Fetch> found = new LinkedHashSet<>();
        for (Integer object : objects) {
            Fetch fetch = fetchedBy.get(object);
            if (fetch != null) found.add(fetch);
        }
        return new ArrayList<>(found);
    }

    List<String> writersUpTo(String location, long version) {
        return upTo(writers.get(location), version);
    }

    List<String> decodesUpTo(String location, long version) {
        return upTo(decodes.get(location), version);
    }

    private static List<String> upTo(TreeMap<Long, Set<String>> byVersion,
                                     long version) {
        List<String> found = new ArrayList<>();
        if (byVersion == null) return found;
        for (Set<String> at : byVersion.headMap(version, true)
                .descendingMap().values()) {
            for (String occurrence : at) {
                if (!found.contains(occurrence)) found.add(occurrence);
            }
        }
        return found;
    }

    Map<String, Long> consumedBy(String occurrence) {
        return consumed.getOrDefault(occurrence,
                Collections.<String, Long>emptyMap());
    }

    String slotOf(String location) {
        String slot = slots.get(location);
        return slot != null ? slot
                : location.substring(location.indexOf('\n') + 1);
    }

    Set<String> consumersOf(String location) {
        return consumers.getOrDefault(location,
                Collections.<String>emptySet());
    }
}
