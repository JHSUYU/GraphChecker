package edu.uva.liftlab.graphchecker.runtime;

import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Message-carried symbolic values shared by every request/response transport.
 *
 * <p>A transport drains the producer thread before sending a message and
 * installs that exact string on the receiver thread.  Consumers only take
 * entries from the installed message; correlation ids are deliberately not
 * an expression lookup mechanism.</p>
 *
 * <p>An expression belongs to a <em>value inside the message</em>, not to a
 * queue.  A port is declared on one pair of bytecode sites and a protocol
 * routes every value of that shape through them, so one message serializes
 * many unrelated values through one port: a receiver that took the head of a
 * shared queue paired whichever leaf happened to be first with whichever
 * decode happened to run first, and any asymmetry between the two sides
 * silently shifted every pairing after it.  Each leaf is therefore addressed
 * by {@code (message, port, element ordinal within that message)} -- the
 * ordinal travels on the wire -- and a decode looks its element up rather
 * than consuming a head.</p>
 *
 * <p>The ordinal is the honest approximation of the value's field path.  The
 * exact key would be the path inside the message -- the repeated field and
 * index the value was set on -- but a declared port names a bytecode site,
 * not a proto field, and the site alone does not say which element of which
 * repeated field it is building.  Ordinals agree with field paths whenever
 * both sides walk one message's elements in the same order, which is what a
 * generated serializer and its generated parser do; they disagree exactly
 * when one side visits a value the other does not, and that disagreement is
 * reported rather than absorbed: a leaf nothing looked up, and a lookup with
 * no leaf, are both named.</p>
 */
public final class SymbolicMessageEnvelope {
    private static final String SCHEMA = "CSE4";
    /** Separator between the consumer occurrences of one entry. */
    private static final String CONSUMERS = "\n";
    private static final int MAX_ENTRIES = 64;
    private static final int MAX_WIRE_LENGTH = 65_536;
    private static final Base64.Encoder ENCODER =
            Base64.getUrlEncoder().withoutPadding();
    private static final Base64.Decoder DECODER = Base64.getUrlDecoder();
    /** The leaves of the message this thread is building. */
    private static final ThreadLocal<Deque<Entry>> OUTBOUND =
            new ThreadLocal<>();
    /** The message this thread is decoding. */
    private static final ThreadLocal<Inbound> INBOUND = new ThreadLocal<>();

    private SymbolicMessageEnvelope() {
    }

    /**
     * Adds one declared port to the next message sent by this thread.
     *
     * <p>{@code consumerOccurrenceIds} are the planned consumer occurrences
     * the plan authorises for this port: a producer rooted at a loop body
     * stages one entry per iteration onto one message, and the receiver's
     * per-element occurrences take them in order, so the entry names the set
     * the plan bound rather than one addressee the sender cannot pick.</p>
     */
    public static boolean stage(String portId, long handle,
                                String producerTaskId,
                                String producerOccurrenceId,
                                List<String> consumerOccurrenceIds) {
        Deque<Entry> entries = OUTBOUND.get();
        if (empty(portId) || handle < 0L || empty(producerTaskId)
                || empty(producerOccurrenceId)
                || consumerOccurrenceIds == null
                || consumerOccurrenceIds.isEmpty()) {
            return false;
        }
        for (String consumer : consumerOccurrenceIds) {
            if (empty(consumer) || consumer.contains(CONSUMERS)) return false;
        }
        if (entries == null) {
            entries = new ArrayDeque<>();
            OUTBOUND.set(entries);
        }
        if (entries.size() >= MAX_ENTRIES) {
            return false;
        }
        int ordinal = 0;
        for (Entry staged : entries) {
            if (portId.equals(staged.portId)) ordinal++;
        }
        entries.addLast(new Entry(true, portId, handle,
                producerTaskId, producerOccurrenceId,
                unmodifiableCopy(consumerOccurrenceIds), ordinal));
        return true;
    }

    /**
     * Removes and serializes the entries staged for the next outbound message.
     * An empty string means the message carries no symbolic envelope.
     */
    public static String takeOutbound() {
        Deque<Entry> entries = OUTBOUND.get();
        OUTBOUND.remove();
        if (entries == null || entries.isEmpty()) return "";
        StringBuilder wire = new StringBuilder(SCHEMA);
        for (Entry entry : entries) {
            wire.append(';').append(token(entry.portId)).append(',')
                    .append(entry.handle).append(',')
                    .append(token(entry.producerTaskId)).append(',')
                    .append(token(entry.producerOccurrenceId)).append(',')
                    .append(token(join(entry.consumerOccurrenceIds)))
                    .append(',').append(entry.ordinal);
        }
        return wire.toString();
    }

    /**
     * Replaces the receiver thread's current message with this exact wire.
     *
     * <p>A different message displacing this one ends it as surely as a
     * close does, and on the client half of an exchange it is the only
     * ending there is: the caller installs the response it is about to
     * decode and nothing closes it until the next call.  So a displaced
     * message reports what nothing looked up, exactly as a closed one does
     * -- unless the same wire is being reinstalled, which is a transport
     * carrying one message across several legs rather than a new message,
     * and which has not finished with its values.</p>
     */
    public static void installInbound(String wire) {
        Inbound displaced = INBOUND.get();
        INBOUND.remove();
        Inbound message = new Inbound(decode(wire), wire);
        if (displaced != null && !displaced.wire.equals(message.wire)) {
            displaced.reportUnattached();
        }
        INBOUND.set(message);
    }

    /**
     * Clears a receiver when the concrete message has no envelope header.
     *
     * <p>Closing a message is the moment its unclaimed leaves become
     * findings: the sender put a value in the message and no decode on this
     * side asked for it, so whatever that value fed is not connected to its
     * producer any more.  They are reported here, once, with the message.</p>
     */
    public static void clearInbound() {
        Inbound message = INBOUND.get();
        INBOUND.remove();
        if (message != null) message.reportUnattached();
    }

    /**
     * Observes the element this port would take next, without taking it.
     * Admission uses the concrete message's producer occurrence before the
     * selected region starts; the attach hook remains the sole consumer.
     */
    public static Entry peek(String portId) {
        Inbound message = INBOUND.get();
        if (message == null || empty(portId)) return Entry.MISSING;
        return message.at(portId, message.nextOrdinal(portId));
    }

    /**
     * Takes the element of this message this port is decoding next.
     *
     * <p>The lookup is by ordinal, not by position: an element already
     * looked up is not handed out again, and an element the sender never
     * staged answers absent instead of borrowing the next value along.</p>
     */
    public static Entry take(String portId) {
        Inbound message = INBOUND.get();
        if (message == null || empty(portId)) return Entry.MISSING;
        return message.take(portId);
    }

    /** Elements of the current message no decode has looked up. */
    public static int inboundUnattached() {
        Inbound message = INBOUND.get();
        return message == null ? 0 : message.unattached();
    }

    /**
     * Clears test/workload thread state without retaining a sent message.
     *
     * <p>A session boundary, not a message boundary: nothing is reported,
     * because what a session drops was never a message this side agreed to
     * decode.</p>
     */
    public static void clear() {
        OUTBOUND.remove();
        INBOUND.remove();
    }

    /** One decoded message and how much of it has been looked up. */
    private static final class Inbound {
        private final List<Entry> entries;
        private final boolean[] lookedUp;
        private final String wire;
        private final Map<String, Integer> next = new LinkedHashMap<>();

        Inbound(List<Entry> entries, String wire) {
            this.entries = entries;
            this.lookedUp = new boolean[entries.size()];
            this.wire = wire;
        }

        int nextOrdinal(String portId) {
            Integer ordinal = next.get(portId);
            return ordinal == null ? 0 : ordinal;
        }

        Entry at(String portId, int ordinal) {
            for (int index = 0; index < entries.size(); index++) {
                Entry entry = entries.get(index);
                if (entry.ordinal == ordinal
                        && portId.equals(entry.portId)) {
                    return entry;
                }
            }
            return Entry.MISSING;
        }

        Entry take(String portId) {
            int ordinal = nextOrdinal(portId);
            next.put(portId, ordinal + 1);
            for (int index = 0; index < entries.size(); index++) {
                Entry entry = entries.get(index);
                if (entry.ordinal != ordinal
                        || !portId.equals(entry.portId)) continue;
                if (lookedUp[index]) break;
                lookedUp[index] = true;
                return entry;
            }
            return Entry.MISSING;
        }

        int unattached() {
            int left = 0;
            for (boolean taken : lookedUp) {
                if (!taken) left++;
            }
            return left;
        }

        /** Names every element nothing looked up; reports each once. */
        void reportUnattached() {
            for (int index = 0; index < entries.size(); index++) {
                if (lookedUp[index]) continue;
                lookedUp[index] = true;
                Entry entry = entries.get(index);
                ConcolicRegionRuntime.reportUnattachedMessageLeaf(
                        entry.portId, entry.ordinal,
                        entry.producerOccurrenceId);
            }
        }
    }

    private static List<Entry> decode(String wire) {
        if (wire == null || wire.length() > MAX_WIRE_LENGTH) {
            throw malformed();
        }
        String[] rows = wire.split(";", -1);
        if (rows.length < 2 || !SCHEMA.equals(rows[0])
                || rows.length - 1 > MAX_ENTRIES) throw malformed();
        List<Entry> entries = new ArrayList<>();
        for (int index = 1; index < rows.length; index++) {
            String[] fields = rows[index].split(",", -1);
            if (fields.length != 6) throw malformed();
            String portId = text(fields[0]);
            String producerTaskId = text(fields[2]);
            String producerOccurrenceId = text(fields[3]);
            List<String> consumerOccurrenceIds = split(text(fields[4]));
            long handle;
            int ordinal;
            try {
                handle = Long.parseLong(fields[1]);
                ordinal = Integer.parseInt(fields[5]);
            } catch (NumberFormatException invalid) {
                throw malformed();
            }
            if (handle < 0L || !Long.toString(handle).equals(fields[1])
                    || ordinal < 0 || ordinal >= MAX_ENTRIES
                    || !Integer.toString(ordinal).equals(fields[5])
                    || empty(portId) || empty(producerTaskId)
                    || empty(producerOccurrenceId)
                    || consumerOccurrenceIds.isEmpty()) throw malformed();
            entries.add(new Entry(true, portId, handle,
                    producerTaskId, producerOccurrenceId,
                    consumerOccurrenceIds, ordinal));
        }
        return entries;
    }

    /** The entry's consumer occurrences as one encodable field value. */
    private static String join(List<String> consumers) {
        StringBuilder joined = new StringBuilder();
        for (String consumer : consumers) {
            if (joined.length() > 0) joined.append(CONSUMERS);
            joined.append(consumer);
        }
        return joined.toString();
    }

    /** The inverse of {@link #join}; an empty field decodes to no consumer. */
    private static List<String> split(String value) {
        List<String> consumers = new ArrayList<>();
        for (String consumer : value.split(CONSUMERS, -1)) {
            if (!empty(consumer)) consumers.add(consumer);
        }
        return Collections.unmodifiableList(consumers);
    }

    private static List<String> unmodifiableCopy(List<String> values) {
        return Collections.unmodifiableList(new ArrayList<>(values));
    }

    private static String token(String value) {
        return ENCODER.encodeToString(value.getBytes(StandardCharsets.UTF_8));
    }

    private static String text(String token) {
        try {
            String value = new String(DECODER.decode(token),
                    StandardCharsets.UTF_8);
            if (token.isEmpty() || !token(value).equals(token)) {
                throw malformed();
            }
            return value;
        } catch (IllegalArgumentException invalid) {
            throw malformed();
        }
    }

    private static boolean empty(String value) {
        return value == null || value.isEmpty();
    }

    private static IllegalArgumentException malformed() {
        return new IllegalArgumentException(
                "malformed symbolic message envelope");
    }

    /** One immutable entry physically decoded from the current message. */
    public static final class Entry {
        private static final Entry MISSING =
                new Entry(false, "", 0L, "", "",
                        Collections.<String>emptyList(), -1);
        private final boolean present;
        private final String portId;
        private final long handle;
        private final String producerTaskId;
        private final String producerOccurrenceId;
        private final List<String> consumerOccurrenceIds;
        private final int ordinal;

        private Entry(boolean present, String portId, long handle,
                      String producerTaskId, String producerOccurrenceId,
                      List<String> consumerOccurrenceIds, int ordinal) {
            this.present = present;
            this.portId = portId;
            this.handle = handle;
            this.producerTaskId = producerTaskId;
            this.producerOccurrenceId = producerOccurrenceId;
            this.consumerOccurrenceIds = consumerOccurrenceIds;
            this.ordinal = ordinal;
        }

        public boolean present() { return present; }

        public long handle() { return handle; }

        public String producerTaskId() { return producerTaskId; }

        public String producerOccurrenceId() {
            return producerOccurrenceId;
        }

        /** Which element of this message and port the value was set on. */
        public int ordinal() { return ordinal; }

        /** The planned consumer occurrences the plan bound to this port. */
        public List<String> consumerOccurrenceIds() {
            return consumerOccurrenceIds;
        }
    }
}
