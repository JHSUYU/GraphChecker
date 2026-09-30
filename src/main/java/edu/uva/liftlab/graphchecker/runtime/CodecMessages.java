package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Hole;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * What binds an encode's entries to the message that carries them
 * (WIRE-CODEC §4.4), never the thread: (a) a door walks its own payload
 * ({@link CodecRuntime#outbound}); (b) an encode whose result is an object
 * files its entries under that object's identity, and the store door that
 * writes the object sends them ({@link #written}); (c) an encode bound to an
 * exchange stages into the innermost open bracket on its thread, which the
 * next outbound door of the bracket's transport drains ({@link #drain}).
 *
 * <p>A stored version keeps its message, the last {@link #VERSIONS} per path;
 * every read of a version binds the array it read to that message
 * ({@link #fetched}), inside a notification or not, and a decode applies the
 * message bound to its encoded argument ({@link #delivered}).  Entries are
 * never consumed: N readers of one version, or one array decoded twice, each
 * mint their own holes.  An encode no message carries is counted
 * ({@link #unsent}), one aggregate per codec at the run's close.</p>
 */
final class CodecMessages {
    /** Live encodes bound to their encoded object. */
    static final int MAX_ENCODED = 4096;
    /** Stored versions kept per path. */
    static final int VERSIONS = 8;

    private CodecMessages() {
    }

    /** One hole of one leaf of one encode. */
    static final class Entry {
        final String codec;
        /** Which encode of a bracket this is (0 but for several encodes in
         *  one bracket): a decode applies one encode's entries. */
        final int ordinal;
        final List<Object> path;
        final int hole;
        final CodecExport.Template template;
        final Endpoint producer;
        /** The VM event of the export. */
        final long exportSeq;
        /** The whole leaf's text at the producer. */
        final String recorded;
        /** This hole's text at the producer. */
        final String text;
        /** The hole's operand; only the producer's JVM has it. */
        final JsonObject operand;
        /** The hole's sort; only the producer's JVM states it. */
        final String javaType;

        Entry(String codec, int ordinal, List<Object> path, int hole,
              CodecExport.Template template, Endpoint producer,
              long exportSeq, String recorded, String text,
              JsonObject operand, String javaType) {
            this.codec = codec;
            this.ordinal = ordinal;
            this.path = Collections.unmodifiableList(
                    new ArrayList<Object>(path));
            this.hole = hole;
            this.template = template;
            this.producer = producer;
            this.exportSeq = exportSeq;
            this.recorded = recorded;
            this.text = text;
            this.operand = operand;
            this.javaType = javaType;
        }

        /** The port: the producer endpoint's site. */
        String port() {
            return producer.site();
        }

        Hole contractHole() {
            return Hole.of(codec, path, hole);
        }
    }

    /** One message's entries, under its key. */
    static final class Message {
        /** A store's {@code <transport> <path>@<version>}, else the
         *  exchange's correlation id: rows spell it as one. */
        final String key;
        /** {@code <path>@<version>} for a stored version, else "". */
        final String storeKey;
        final List<Entry> entries;

        Message(String key, String storeKey, List<Entry> entries) {
            this.key = key;
            this.storeKey = storeKey;
            this.entries = Collections.unmodifiableList(
                    new ArrayList<>(entries));
        }

        /** The message with {@code more} entries after its own. */
        Message with(List<Entry> more) {
            List<Entry> all = new ArrayList<>(entries);
            all.addAll(more);
            return new Message(key, storeKey, all);
        }
    }

    // ---- (b) encoded identity -------------------------------------------

    /** An encode waiting for the door that writes its object. */
    private static final class Pending {
        final String codec;
        final List<Entry> entries;
        boolean sent;

        Pending(String codec, List<Entry> entries) {
            this.codec = codec;
            this.entries = entries;
        }
    }

    private static final WeakIdentity<Pending> ENCODED =
            new WeakIdentity<>();
    private static final WeakIdentity<Message> FETCHED =
            new WeakIdentity<>();
    /** Per {@code transport\npath}: version to message, and the newest
     *  version dropped. */
    private static final Map<String, Versions> STORED = new HashMap<>();
    private static final Map<String, Long> UNSENT = new TreeMap<>();

    private static final class Versions {
        final TreeMap<Long, Message> kept = new TreeMap<>();
        long droppedThrough = -1L;
    }

    /**
     * Binds one encode's entries to the object it produced.  Returns how
     * many live encodes were dropped to stay within {@link #MAX_ENCODED}.
     */
    static synchronized int encoded(Object encoded, String codec,
                                    List<Entry> entries) {
        return ENCODED.put(encoded, new Pending(codec, entries),
                MAX_ENCODED);
    }

    /** The entries an encode bound to {@code data}, now sent; none when
     *  no encode produced it. */
    static synchronized List<Entry> written(Object data) {
        Pending pending = data == null ? null : ENCODED.get(data);
        if (pending == null) return Collections.emptyList();
        pending.sent = true;
        return pending.entries;
    }

    // ---- stores ---------------------------------------------------------

    /** Files the message a write of {@code key} ({@code path@version})
     *  sent. */
    static synchronized Message stored(String transport, String key,
                                       List<Entry> entries) {
        Message message = new Message(transport + " " + key, key, entries);
        int at = key.lastIndexOf('@');
        long version = version(key);
        if (at < 0 || version < 0L) return message;
        Versions versions = STORED.computeIfAbsent(transport + "\n"
                + key.substring(0, at), path -> new Versions());
        versions.kept.put(version, message);
        while (versions.kept.size() > VERSIONS) {
            versions.droppedThrough = Math.max(versions.droppedThrough,
                    versions.kept.pollFirstEntry().getKey());
        }
        return message;
    }

    /** What a read of a stored version found. */
    static final class Fetch {
        /** The version's message, or null. */
        final Message message;
        /** Whether the version was stored and dropped since. */
        final boolean dropped;

        Fetch(Message message, boolean dropped) {
            this.message = message;
            this.dropped = dropped;
        }
    }

    /**
     * One read of a stored version: {@code data}, the array it read, is
     * bound to the version's message for whatever decodes it.
     */
    static synchronized Fetch fetched(String transport, String key,
                                      Object data) {
        int at = key.lastIndexOf('@');
        long version = version(key);
        Versions versions = at < 0 ? null
                : STORED.get(transport + "\n" + key.substring(0, at));
        Message message = versions == null ? null
                : versions.kept.get(version);
        if (message != null && data != null) {
            FETCHED.put(data, message, Integer.MAX_VALUE);
        }
        return new Fetch(message, message == null && versions != null
                && version >= 0L && version <= versions.droppedThrough);
    }

    /** The message bound to a decode's encoded argument, or null. */
    static synchronized Message delivered(Object encoded) {
        return encoded == null ? null : FETCHED.get(encoded);
    }

    private static long version(String key) {
        try {
            return Long.parseLong(key.substring(key.lastIndexOf('@') + 1));
        } catch (NumberFormatException | IndexOutOfBoundsException none) {
            return -1L;
        }
    }

    // ---- (c) exchange brackets ------------------------------------------

    /** One open exchange bracket and the encodes staged in it. */
    static final class Bracket {
        final String transport;
        final long token;
        final List<Entry> staged = new ArrayList<>();
        final Map<String, Integer> encodes = new HashMap<>();

        Bracket(String transport, long token) {
            this.transport = transport;
            this.token = token;
        }

        /** The ordinal the next encode of {@code codec} here takes. */
        int nextOrdinal(String codec) {
            return encodes.merge(codec, 1, Integer::sum) - 1;
        }
    }

    private static final ThreadLocal<Deque<Bracket>> BRACKETS =
            ThreadLocal.withInitial(ArrayDeque::new);
    private static long tokens;

    /** Opens a bracket of {@code transport} on this thread. */
    static long beginExchange(String transport) {
        long token;
        synchronized (CodecMessages.class) {
            token = ++tokens;
        }
        BRACKETS.get().push(new Bracket(transport, token));
        return token;
    }

    /**
     * Closes the bracket {@code token} opened, and every bracket opened in
     * it that is still open; what they staged and no door drained is
     * counted unsent.
     */
    static void endExchange(long token) {
        Deque<Bracket> open = BRACKETS.get();
        boolean held = false;
        for (Bracket bracket : open) held |= bracket.token == token;
        if (!held) return;
        while (!open.isEmpty()) {
            Bracket closed = open.pop();
            countUnsent(closed.staged);
            if (closed.token == token) break;
        }
    }

    /** The innermost open bracket on this thread, or null. */
    static Bracket innermost() {
        return BRACKETS.get().peek();
    }

    /**
     * Takes what the innermost open bracket of {@code transport} on this
     * thread staged: the next outbound door of that transport carries it.
     */
    static List<Entry> drain(String transport) {
        for (Bracket bracket : BRACKETS.get()) {
            if (!bracket.transport.equals(transport)) continue;
            List<Entry> drained = new ArrayList<>(bracket.staged);
            bracket.staged.clear();
            return drained;
        }
        return Collections.emptyList();
    }

    // ---- unsent ---------------------------------------------------------

    /** One encode of {@code codec} no message carries. */
    static synchronized void unsent(String codec) {
        UNSENT.merge(codec, 1L, Long::sum);
    }

    private static void countUnsent(List<Entry> staged) {
        Map<String, Boolean> encodes = new LinkedHashMap<>();
        for (Entry entry : staged) {
            encodes.put(entry.codec + "\n" + entry.ordinal, Boolean.TRUE);
        }
        for (String encode : encodes.keySet()) {
            unsent(encode.substring(0, encode.indexOf('\n')));
        }
    }

    /**
     * The encodes no message carried, per codec: the counted ones and the
     * bound encodes no door wrote.
     */
    static synchronized Map<String, Long> unsentCounts() {
        for (Pending pending : ENCODED.values()) {
            if (!pending.sent) unsent(pending.codec);
            pending.sent = true;
        }
        return new TreeMap<>(UNSENT);
    }

    /** Forgets every binding: a session boundary. */
    static synchronized void clear() {
        ENCODED.clear();
        FETCHED.clear();
        STORED.clear();
        UNSENT.clear();
        BRACKETS.remove();
    }

    // ---- a weak identity map --------------------------------------------

    /**
     * Values by the identity of an object that holds them no longer than
     * the object lives; bounded, eldest dropped first.  An encode's object
     * that died unsent is counted unsent when its value is a
     * {@link Pending}.
     */
    private static final class WeakIdentity<V> {
        private final ReferenceQueue<Object> queue = new ReferenceQueue<>();
        private final LinkedHashMap<Ref, V> map = new LinkedHashMap<>();

        V get(Object key) {
            expunge();
            return map.get(new Ref(key, null));
        }

        /** @return how many values were dropped to stay within
         *  {@code bound} */
        int put(Object key, V value, int bound) {
            expunge();
            map.put(new Ref(key, queue), value);
            int dropped = 0;
            Iterator<Map.Entry<Ref, V>> eldest = map.entrySet().iterator();
            while (map.size() > bound && eldest.hasNext()) {
                V gone = eldest.next().getValue();
                eldest.remove();
                died(gone);
                dropped++;
            }
            return dropped;
        }

        List<V> values() {
            expunge();
            return new ArrayList<>(map.values());
        }

        void clear() {
            map.clear();
            while (queue.poll() != null) {
                // Drained: their entries are gone with the map.
            }
        }

        private void expunge() {
            for (Object cleared = queue.poll(); cleared != null;
                 cleared = queue.poll()) {
                died(map.remove(cleared));
            }
        }

        private void died(V value) {
            if (value instanceof Pending && !((Pending) value).sent) {
                unsent(((Pending) value).codec);
            }
        }
    }

    /** A weak reference equal to another of the same live referent. */
    private static final class Ref extends WeakReference<Object> {
        private final int hash;

        Ref(Object referent, ReferenceQueue<Object> queue) {
            super(referent, queue);
            this.hash = System.identityHashCode(referent);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof Ref)) return false;
            Object mine = get();
            return mine != null && mine == ((Ref) other).get();
        }
    }
}
