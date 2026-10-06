package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Base64;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Message-carried symbolic values shared by every request/response transport.
 *
 * <p>A transport drains the producer thread before sending and installs that
 * exact string on the receiver thread; correlation ids are never an
 * expression lookup.</p>
 *
 * <p>Each leaf is addressed by {@code (port, ordinal)}, and a decode looks its
 * element up rather than consuming a queue head: one port carries many
 * unrelated values, so head-of-queue pairing shifts every pairing after the
 * first asymmetry.  The k-th element of a port is the port's k-th field in
 * the door's walk of the message ({@link MessageCodec}), which both sides
 * walk alike, staged or not ({@link #skip}), or a declared row's k-th
 * capture; a disagreement is reported (a leaf nothing looked up, a lookup
 * with no leaf), never absorbed.</p>
 *
 * <p>The wire carries only what the receiver cannot derive: handle and
 * position.  Plan data does not travel; both sides load the same plan.
 * Refusing a wire is a named row, never an exception into the workload.</p>
 */
public final class SymbolicMessageEnvelope {
    private static final String SCHEMA = "CSE6";
    /**
     * How many values one message may carry: the only bound on a wire.  Do
     * not add a length bound; it would be a second authority over the same
     * thing.
     */
    private static final int MAX_ENTRIES = 64;
    private static final Base64.Encoder ENCODER =
            Base64.getUrlEncoder().withoutPadding();
    private static final Base64.Decoder DECODER = Base64.getUrlDecoder();

    /** The message this thread is building. */
    private static final ThreadLocal<Outbound> OUTBOUND = new ThreadLocal<>();
    /** The message this thread is decoding. */
    private static final ThreadLocal<Inbound> INBOUND = new ThreadLocal<>();

    private SymbolicMessageEnvelope() {
    }

    /**
     * A {@link #take} that found no element: the sender staged nothing for
     * this element of the port on this message.
     */
    static final long ABSENT = -1L;

    /**
     * Adds one declared port to the next message sent by this thread, with
     * the export that staged it ({@code producer}, which stays here).
     *
     * <p>Only the staged handle and its position travel; the plan's
     * occurrences for the port do not, since both sides hold the plan and
     * the attach names its own activation
     * ({@code HandoffMint.attachConsumerRegion}).</p>
     */
    static boolean stage(String portId, long handle, Endpoint producer) {
        if (empty(portId) || handle < 0L) return false;
        return outbound().stage(portId, handle, producer);
    }

    /**
     * Counts one element of {@code portId} the next message carries none
     * for, so the elements after it keep the ordinals the receiver's walk
     * gives them.
     */
    static void skip(String portId) {
        if (!empty(portId)) outbound().count(portId);
    }

    /**
     * Files the exports staged on the message this thread is about to send,
     * as that message's ({@link Interactions#carried}): the door calls it
     * with the message's correlation and half just before it drains the
     * envelope ({@link #takeOutbound}).
     */
    static void carriedBy(String correlationId, String half) {
        Outbound message = OUTBOUND.get();
        if (message == null) return;
        for (Entry entry : message.entries) {
            Interactions.carried(entry.portId, correlationId, half,
                    entry.producer);
        }
    }

    private static Outbound outbound() {
        Outbound message = OUTBOUND.get();
        if (message == null) {
            message = new Outbound();
            OUTBOUND.set(message);
        }
        return message;
    }

    /**
     * Removes and serializes the entries staged for the next outbound message.
     * An empty string means the message carries no symbolic envelope.
     */
    public static String takeOutbound() {
        Outbound message = OUTBOUND.get();
        OUTBOUND.remove();
        if (message == null || message.entries.isEmpty()) return "";
        StringBuilder wire = new StringBuilder(SCHEMA);
        for (Entry entry : message.entries) {
            wire.append(';').append(token(entry.portId)).append(',')
                    .append(entry.handle).append(',').append(entry.ordinal);
        }
        return wire.toString();
    }

    /**
     * Replaces the receiver thread's current message with this exact wire.
     *
     * <p>A displaced message ends like a closed one and reports what nothing
     * looked up (on a client half nothing else closes it), unless the same
     * wire is reinstalled: that is one message crossing several legs.</p>
     */
    public static void installInbound(String wire) {
        Inbound displaced = INBOUND.get();
        INBOUND.remove();
        List<Entry> entries;
        try {
            entries = decode(wire);
        } catch (IllegalArgumentException refused) {
            // A refused wire is a named row, never an exception: thrown, it
            // breaks the workload's IPC.  Nothing is installed, so every
            // decode answers no element and the claim fails on the values.
            if (displaced != null) displaced.reportUnattached();
            RowRuntime.messageContextRefused(
                    "inbound symbolic message envelope",
                    refused.getMessage() + "; "
                            + (wire == null ? 0 : wire.length())
                            + " characters");
            return;
        }
        Inbound message = new Inbound(entries, wire);
        if (displaced != null && !displaced.wire.equals(message.wire)) {
            displaced.reportUnattached();
        }
        INBOUND.set(message);
    }

    /**
     * Clears a receiver when the concrete message has no envelope header;
     * its unclaimed leaves are reported here, once.
     */
    public static void clearInbound() {
        Inbound message = INBOUND.get();
        INBOUND.remove();
        if (message != null) message.reportUnattached();
    }

    /**
     * Takes the element this port is decoding next, by ordinal: its handle
     * (0 for a concrete one), or {@link #ABSENT} when the message carries
     * none, rather than borrowing the next value.
     */
    static long take(String portId) {
        Inbound message = INBOUND.get();
        if (message == null || empty(portId)) return ABSENT;
        return message.take(portId);
    }

    /** Clears thread state at a session boundary; nothing is reported. */
    static void clear() {
        OUTBOUND.remove();
        INBOUND.remove();
    }

    /** Per port, the next ordinal one side counts: both sides count
     *  alike. */
    private static class Ordinals {
        private final Map<String, Integer> next = new LinkedHashMap<>();

        /** Counts one element of {@code portId}. */
        int count(String portId) {
            Integer held = next.get(portId);
            int ordinal = held == null ? 0 : held;
            next.put(portId, ordinal + 1);
            return ordinal;
        }
    }

    /** One decoded message and how much of it has been looked up. */
    private static final class Inbound extends Ordinals {
        private final List<Entry> entries;
        private final boolean[] lookedUp;
        private final String wire;

        Inbound(List<Entry> entries, String wire) {
            this.entries = entries;
            this.lookedUp = new boolean[entries.size()];
            this.wire = wire;
        }

        long take(String portId) {
            int ordinal = count(portId);
            for (int index = 0; index < entries.size(); index++) {
                Entry entry = entries.get(index);
                if (entry.ordinal != ordinal
                        || !portId.equals(entry.portId)) continue;
                if (lookedUp[index]) break;
                lookedUp[index] = true;
                return entry.handle;
            }
            return ABSENT;
        }

        /**
         * Names every element nothing looked up, once each: what it fed
         * names no producer, and the fix is the port's decode.
         */
        void reportUnattached() {
            for (int index = 0; index < entries.size(); index++) {
                if (lookedUp[index]) continue;
                lookedUp[index] = true;
                RowRuntime.messageContextRefused(
                        entries.get(index).portId,
                        "the sender staged this port's value in a message"
                                + " and no decode on this side asked for it,"
                                + " so the value it fed names no producer");
            }
        }
    }

    /** One message being built. */
    private static final class Outbound extends Ordinals {
        private final List<Entry> entries = new ArrayList<>();

        boolean stage(String portId, long handle, Endpoint producer) {
            int ordinal = count(portId);
            if (entries.size() >= MAX_ENTRIES) return false;
            entries.add(new Entry(portId, handle, ordinal, producer));
            return true;
        }
    }

    private static List<Entry> decode(String wire) {
        if (wire == null) throw malformed();
        String[] rows = wire.split(";", -1);
        if (rows.length < 2 || !SCHEMA.equals(rows[0])
                || rows.length - 1 > MAX_ENTRIES) throw malformed();
        List<Entry> entries = new ArrayList<>();
        for (int index = 1; index < rows.length; index++) {
            String[] fields = rows[index].split(",", -1);
            if (fields.length != 3) throw malformed();
            String portId = text(fields[0]);
            long handle;
            int ordinal;
            try {
                handle = Long.parseLong(fields[1]);
                ordinal = Integer.parseInt(fields[2]);
            } catch (NumberFormatException invalid) {
                throw malformed();
            }
            if (handle < 0L || !Long.toString(handle).equals(fields[1])
                    || ordinal < 0
                    || !Integer.toString(ordinal).equals(fields[2])
                    || empty(portId)) throw malformed();
            entries.add(new Entry(portId, handle, ordinal, null));
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

    /** One staged or decoded leaf: its port, handle and position, and the
     *  export that staged it (the sender's side only; it never travels). */
    private static final class Entry {
        private final String portId;
        private final long handle;
        private final int ordinal;
        private final Endpoint producer;

        private Entry(String portId, long handle, int ordinal,
                      Endpoint producer) {
            this.portId = portId;
            this.handle = handle;
            this.ordinal = ordinal;
            this.producer = producer;
        }
    }
}
