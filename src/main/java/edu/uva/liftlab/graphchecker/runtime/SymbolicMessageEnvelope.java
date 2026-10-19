package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Base64;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class SymbolicMessageEnvelope {
    private static final String SCHEMA = "CSE6";
    private static final int MAX_ENTRIES = 64;
    private static final Base64.Encoder ENCODER =
            Base64.getUrlEncoder().withoutPadding();
    private static final Base64.Decoder DECODER = Base64.getUrlDecoder();

    private static final ThreadLocal<Outbound> OUTBOUND = new ThreadLocal<>();
    private static final ThreadLocal<Inbound> INBOUND = new ThreadLocal<>();

    private SymbolicMessageEnvelope() {
    }

    static final long ABSENT = -1L;

    static boolean stage(String portId, long handle, Endpoint producer) {
        if (empty(portId) || handle < 0L) return false;
        return outbound().stage(portId, handle, producer);
    }

    static void skip(String portId) {
        if (!empty(portId)) outbound().count(portId);
    }

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

    public static void installInbound(String wire) {
        Inbound displaced = INBOUND.get();
        INBOUND.remove();
        List<Entry> entries;
        try {
            entries = decode(wire);
        } catch (IllegalArgumentException refused) {
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

    public static void clearInbound() {
        Inbound message = INBOUND.get();
        INBOUND.remove();
        if (message != null) message.reportUnattached();
    }

    static long take(String portId) {
        Inbound message = INBOUND.get();
        if (message == null || empty(portId)) return ABSENT;
        return message.take(portId);
    }

    static void clear() {
        OUTBOUND.remove();
        INBOUND.remove();
    }

    private static class Ordinals {
        private final Map<String, Integer> next = new LinkedHashMap<>();

        int count(String portId) {
            Integer held = next.get(portId);
            int ordinal = held == null ? 0 : held;
            next.put(portId, ordinal + 1);
            return ordinal;
        }
    }

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
