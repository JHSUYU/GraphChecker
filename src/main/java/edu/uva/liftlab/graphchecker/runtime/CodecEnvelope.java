package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.RowCodec;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.List;

/**
 * The wire form of a message's codec entries (WIRE-CODEC §4.5): {@code CSE6}
 * then one base64url JSON object per hole -- its codec, encode ordinal, key
 * path, hole index, the leaf's template, the producer endpoint, the export's
 * event, the leaf's recorded text and the hole's.  The producer travels on
 * the message, so a consumer pairs by what it received, in any JVM.
 *
 * <p>Bounds: {@link #MAX_ENTRIES} per message, and a transport's
 * {@code envelopeBytes} (an HTTP header); what does not fit is named, the
 * first entry left out first.  A malformed envelope installs nothing and is
 * named, never thrown into the workload.</p>
 */
final class CodecEnvelope {
    static final String SCHEMA = "CSE6";
    static final int MAX_ENTRIES = 256;
    private static final Base64.Encoder ENCODER =
            Base64.getUrlEncoder().withoutPadding();
    private static final Base64.Decoder DECODER = Base64.getUrlDecoder();

    private CodecEnvelope() {
    }

    /** An envelope and the entries it holds. */
    static final class Written {
        /** "" when it holds none. */
        final String wire;
        final List<CodecMessages.Entry> carried;

        Written(String wire, List<CodecMessages.Entry> carried) {
            this.wire = wire;
            this.carried = carried;
        }
    }

    /** The envelope of {@code entries}, within the entry count and
     *  {@code maxBytes}. */
    static Written write(String messageKey, List<CodecMessages.Entry> entries,
                         int maxBytes) {
        StringBuilder wire = new StringBuilder(SCHEMA);
        List<CodecMessages.Entry> carried = new ArrayList<>();
        for (CodecMessages.Entry entry : entries) {
            String token = ENCODER.encodeToString(json(entry).toString()
                    .getBytes(StandardCharsets.UTF_8));
            if (carried.size() == MAX_ENTRIES
                    || (long) wire.length() + 1 + token.length() > maxBytes) {
                RowRuntime.gap(GapKind.BOUND_INSUFFICIENT,
                        GapClass.DIAGNOSTIC, messageKey, "the message's "
                                + "envelope holds " + carried.size() + " of "
                                + entries.size() + " hole(s), at its bound of "
                                + (carried.size() == MAX_ENTRIES
                                ? MAX_ENTRIES + " entries"
                                : maxBytes + " bytes")
                                + "; first left out: " + entry.contractHole());
                break;
            }
            wire.append(';').append(token);
            carried.add(entry);
        }
        return new Written(carried.isEmpty() ? "" : wire.toString(),
                carried);
    }

    /** The entries of an envelope; none, and a named refusal, when it is
     *  malformed. */
    static List<CodecMessages.Entry> read(String wire) {
        String[] tokens = wire.split(";", -1);
        try {
            if (tokens.length < 2 || !SCHEMA.equals(tokens[0])
                    || tokens.length - 1 > MAX_ENTRIES) {
                throw new IllegalArgumentException("not a " + SCHEMA
                        + " envelope of at most " + MAX_ENTRIES + " entries");
            }
            List<CodecMessages.Entry> entries = new ArrayList<>();
            for (int index = 1; index < tokens.length; index++) {
                JsonElement parsed = JsonParser.parseString(new String(
                        DECODER.decode(tokens[index]),
                        StandardCharsets.UTF_8));
                entries.add(entry(parsed.getAsJsonObject()));
            }
            return entries;
        } catch (RuntimeException malformed) {
            RowRuntime.messageContextRefused("inbound codec envelope",
                    malformed + "; " + wire.length() + " characters");
            return Collections.emptyList();
        }
    }

    private static JsonObject json(CodecMessages.Entry entry) {
        JsonObject json = new JsonObject();
        json.addProperty("c", entry.codec);
        json.addProperty("o", entry.ordinal);
        JsonArray path = new JsonArray();
        for (Object component : entry.path) {
            if (component instanceof Integer) path.add((Integer) component);
            else path.add((String) component);
        }
        json.add("p", path);
        json.addProperty("h", entry.hole);
        json.add("t", entry.template.wire());
        json.add("e", RowCodec.writeEndpoint(entry.producer));
        json.addProperty("s", entry.exportSeq);
        json.addProperty("r", entry.recorded);
        json.addProperty("x", entry.text);
        return json;
    }

    private static CodecMessages.Entry entry(JsonObject json) {
        List<Object> path = new ArrayList<>();
        for (JsonElement component : json.getAsJsonArray("p")) {
            path.add(component.getAsJsonPrimitive().isNumber()
                    ? (Object) component.getAsInt()
                    : component.getAsString());
        }
        CodecExport.Template template = CodecExport.Template.fromWire(
                json.getAsJsonArray("t"));
        int hole = json.get("h").getAsInt();
        if (hole < 0 || hole >= template.holes().size()) {
            throw new IllegalArgumentException("hole " + hole
                    + " is none of its template's");
        }
        return new CodecMessages.Entry(json.get("c").getAsString(),
                json.get("o").getAsInt(), path, hole, template,
                RowCodec.readEndpoint(json.getAsJsonObject("e")),
                json.get("s").getAsLong(), json.get("r").getAsString(),
                json.get("x").getAsString(), null, "");
    }
}
