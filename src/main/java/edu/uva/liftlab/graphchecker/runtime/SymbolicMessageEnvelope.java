package edu.uva.liftlab.graphchecker.runtime;

import java.nio.charset.StandardCharsets;
import java.util.Base64;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;

/**
 * Message-carried symbolic values shared by every request/response transport.
 *
 * <p>A transport drains the producer thread before sending a message and
 * installs that exact string on the receiver thread.  Consumers only take
 * entries from the installed message; correlation ids are deliberately not
 * an expression lookup mechanism.</p>
 */
public final class SymbolicMessageEnvelope {
    private static final String SCHEMA = "CSE2";
    private static final int MAX_ENTRIES = 64;
    private static final int MAX_WIRE_LENGTH = 65_536;
    private static final Base64.Encoder ENCODER =
            Base64.getUrlEncoder().withoutPadding();
    private static final Base64.Decoder DECODER = Base64.getUrlDecoder();
    private static final ThreadLocal<Deque<Entry>> OUTBOUND =
            new ThreadLocal<>();
    private static final ThreadLocal<Deque<Entry>> INBOUND =
            new ThreadLocal<>();

    private SymbolicMessageEnvelope() {
    }

    /** Adds one declared port to the next message sent by this thread. */
    public static boolean stage(String portId, long handle,
                                String producerTaskId,
                                String producerOccurrenceId,
                                String consumerOccurrenceId) {
        Deque<Entry> entries = OUTBOUND.get();
        if (empty(portId) || handle < 0L || empty(producerTaskId)
                || empty(producerOccurrenceId)
                || empty(consumerOccurrenceId)) {
            return false;
        }
        if (entries == null) {
            entries = new ArrayDeque<>();
            OUTBOUND.set(entries);
        }
        if (entries.size() >= MAX_ENTRIES) {
            return false;
        }
        entries.addLast(new Entry(true, portId, handle,
                producerTaskId, producerOccurrenceId,
                consumerOccurrenceId));
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
                    .append(token(entry.consumerOccurrenceId));
        }
        return wire.toString();
    }

    /** Replaces the receiver thread's current message with this exact wire. */
    public static void installInbound(String wire) {
        INBOUND.remove();
        INBOUND.set(decode(wire));
    }

    /** Clears a receiver when the concrete message has no envelope header. */
    public static void clearInbound() {
        INBOUND.remove();
    }

    /**
     * Observes the next entry for {@code portId} without consuming it.
     * Admission uses the concrete message's producer occurrence before the
     * selected region starts; the attach hook remains the sole consumer.
     */
    public static Entry peek(String portId) {
        Deque<Entry> entries = INBOUND.get();
        if (entries == null || empty(portId)) return Entry.MISSING;
        for (Entry entry : entries) {
            if (portId.equals(entry.portId)) return entry;
        }
        return Entry.MISSING;
    }

    /** Consumes one port from the current inbound message, or returns absent. */
    public static Entry take(String portId) {
        Deque<Entry> entries = INBOUND.get();
        if (entries == null || empty(portId)) return Entry.MISSING;
        for (Iterator<Entry> iterator = entries.iterator();
             iterator.hasNext();) {
            Entry entry = iterator.next();
            if (!portId.equals(entry.portId)) continue;
            iterator.remove();
            if (entries.isEmpty()) INBOUND.remove();
            return entry;
        }
        return Entry.MISSING;
    }

    /** Clears test/workload thread state without retaining a sent message. */
    public static void clear() {
        OUTBOUND.remove();
        INBOUND.remove();
    }

    private static Deque<Entry> decode(String wire) {
        if (wire == null || wire.length() > MAX_WIRE_LENGTH) {
            throw malformed();
        }
        String[] rows = wire.split(";", -1);
        if (rows.length < 2 || !SCHEMA.equals(rows[0])
                || rows.length - 1 > MAX_ENTRIES) throw malformed();
        Deque<Entry> entries = new ArrayDeque<>();
        for (int index = 1; index < rows.length; index++) {
            String[] fields = rows[index].split(",", -1);
            if (fields.length != 5) throw malformed();
            String portId = text(fields[0]);
            String producerTaskId = text(fields[2]);
            String producerOccurrenceId = text(fields[3]);
            String consumerOccurrenceId = text(fields[4]);
            long handle;
            try {
                handle = Long.parseLong(fields[1]);
            } catch (NumberFormatException invalid) {
                throw malformed();
            }
            if (handle < 0L || !Long.toString(handle).equals(fields[1])
                    || empty(portId) || empty(producerTaskId)
                    || empty(producerOccurrenceId)
                    || empty(consumerOccurrenceId)) throw malformed();
            entries.addLast(new Entry(true, portId, handle,
                    producerTaskId, producerOccurrenceId,
                    consumerOccurrenceId));
        }
        return entries;
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
                new Entry(false, "", 0L, "", "", "");
        private final boolean present;
        private final String portId;
        private final long handle;
        private final String producerTaskId;
        private final String producerOccurrenceId;
        private final String consumerOccurrenceId;

        private Entry(boolean present, String portId, long handle,
                      String producerTaskId, String producerOccurrenceId,
                      String consumerOccurrenceId) {
            this.present = present;
            this.portId = portId;
            this.handle = handle;
            this.producerTaskId = producerTaskId;
            this.producerOccurrenceId = producerOccurrenceId;
            this.consumerOccurrenceId = consumerOccurrenceId;
        }

        public boolean present() { return present; }

        public String portId() { return portId; }

        public long handle() { return handle; }

        public String producerTaskId() { return producerTaskId; }

        public String producerOccurrenceId() {
            return producerOccurrenceId;
        }

        public String consumerOccurrenceId() {
            return consumerOccurrenceId;
        }
    }
}
