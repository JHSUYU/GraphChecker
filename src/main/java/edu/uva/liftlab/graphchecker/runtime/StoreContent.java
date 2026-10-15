package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.pauseObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resumeObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.compose.StringIdentities;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

/**
 * THE CONTENT A STORE VERSION CARRIES (PIPELINE §8, a store's content): a
 * JSON document a node writes to a shared store and another node parses,
 * leaf by leaf -- MessageCodec's analogue for a store's JSON codec.
 *
 * <p>The system's codec hands over what it serialized and what it parsed
 * (Solr's {@code Utils.toJSON}, {@code Utils.fromJSON}): the bytes, with the
 * document as the writer saw it -- a tree of maps, lists and leaves built as
 * the serializer walked it, each leaf the object the writer holds, so its
 * expression comes with it ({@link #written}) -- and the tree the parser
 * built ({@link #parsed}).  The store's doors pass the same arrays: a write
 * of bytes the codec wrote exports each leaf of that document on the
 * version it made ({@link #stored}); a fetch names the version its bytes
 * are ({@link #fetched}), and a parse of those bytes mints each leaf of the
 * tree on its entry, paired with the export of that version and the leaf's
 * JSON pointer: CORRELATION_PORT, the port the location and the pointer.
 * Either table is keyed weakly by the array, so a document no store write or
 * fetch takes (an HTTP response, a log line) is dropped with its bytes.</p>
 *
 * <p>A leaf is a String, a number or a boolean.  A String whose text is
 * Java's decimal rendering of a long, or a boolean's, crosses as that value
 * (DEC_LONG, BOOL: the parse mints the rendering of a fresh number), and its
 * export is the value rendered (a {@code toString} the writer's expression
 * is) or the text read; any other String crosses as a String (STR), a number
 * or a boolean leaf as its box's value (NUM), a number widened as the parser
 * reads it back ({@link #wide}).  The writer's kind decides the
 * reader's, so the two ends of one leaf are declared alike; a leaf the
 * reader cannot mint so mints by its own text, unpaired.  At most
 * {@link #MAX_LEAVES} leaves and {@link #MAX_DEPTH} levels of one document
 * are walked; past them a DIAGNOSTIC gap names the location, and the rest
 * crosses as constants.  Both sides capture wherever a replay runs them
 * ({@link #capturing}), at the activation running there or, outside every
 * one, at the thread's occurrence stated unselected (HandoffMint's entry
 * rule): the Overseer's state writer and queue offers write, and a node's
 * watcher parses, outside every opened occurrence (solr-18413 Z2B: 142,295
 * attaches and 332 exports, no expiry exported, when a writer captured only
 * inside one).</p>
 */
final class StoreContent {
    /** The most leaves one document is walked for. */
    static final int MAX_LEAVES = 1024;
    /** The deepest one document is walked. */
    static final int MAX_DEPTH = 16;

    /** The document the codec serialized, by the bytes it returned. */
    private static final Map<byte[], Object> WRITTEN =
            Collections.synchronizedMap(new WeakHashMap<byte[], Object>());
    /** The version a fetch read, by the bytes it returned. */
    private static final Map<byte[], String> FETCHED =
            Collections.synchronizedMap(new WeakHashMap<byte[], String>());
    /** Per version (transport and key) written, each leaf's export. */
    private static final Interactions.Bounded<Map<String, Exported>>
            EXPORTS = Interactions.bounded();

    private StoreContent() {
    }

    /** How a leaf crosses: the template the reader mints it by. */
    enum Kind { STR, DEC_LONG, BOOL, NUM }

    /** One leaf's export: its endpoint, how it crosses and its type. */
    private static final class Exported {
        private final Endpoint producer;
        private final Kind kind;
        private final String javaType;

        private Exported(Endpoint producer, Kind kind, String javaType) {
            this.producer = producer;
            this.kind = kind;
            this.javaType = javaType;
        }
    }

    /** Whether this thread captures a document now: in a replay. */
    static boolean capturing() {
        return RowRuntime.open();
    }

    /** The codec serialized {@code document} into {@code bytes}. */
    static void written(byte[] bytes, Object document) {
        if (bytes != null && document != null) WRITTEN.put(bytes, document);
    }

    /** A fetch of {@code key} returned {@code bytes}: in a replay, or in
     *  the recording's window, which states the parse's leaves. */
    static void fetched(String transport, String key, byte[] bytes) {
        if (bytes != null && (RowRuntime.open() || RecordingWindow.opened())) {
            FETCHED.put(bytes, trimmed(transport) + "\n" + trimmed(key));
        }
    }

    // ---- the writer's side -----------------------------------------------

    /**
     * A write of {@code bytes} made version {@code key}: each leaf of the
     * document the codec serialized them from is exported on it, in a
     * replay.
     *
     * @return that document, or null
     */
    static Object stored(String transport, String key, byte[] bytes) {
        Object document = bytes == null ? null : WRITTEN.remove(bytes);
        if (document == null || !capturing()) return document;
        try {
            export(transport, key, document, contentKeys(transport, key));
        } catch (Throwable failed) {
            // A door never throws into the workload: what failed is named.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    trimmed(transport) + " " + key, "the version's content"
                            + " was not exported: "
                            + ConcolicRegionRuntime.rootCause(failed));
        }
        return document;
    }

    /** Exports each leaf of {@code document} on version {@code key}:
     *  symbolically at or under {@code keys}' prefixes, as its value
     *  elsewhere; every leaf symbolically where {@code keys} is null. */
    static void export(String transport, String key, Object document,
                       List<String> keys) {
        String location = MessageDoors.location(key);
        Map<String, Exported> leaves = new LinkedHashMap<String, Exported>();
        pauseObservation();
        try {
            OccurrenceAddress producer = occurrenceHere(transport);
            for (Leaf leaf : leaves(transport, location, document)) {
                Exported exported = under(keys, leaf.pointer)
                        ? export(producer, transport, location, leaf)
                        : exportConstant(producer, transport, location, leaf);
                if (exported != null) leaves.put(leaf.pointer, exported);
            }
        } finally {
            resumeObservation();
        }
        synchronized (EXPORTS) {
            EXPORTS.put(trimmed(transport) + "\n" + trimmed(key), leaves);
        }
    }

    private static Exported export(OccurrenceAddress producer,
                                   String transport, String location,
                                   Leaf leaf) {
        String port = port(transport, location, leaf.pointer);
        JsonObject answer;
        JsonElement expression;
        try {
            String serialized = engine().exportLeaf(leaf.parent,
                    leaf.slotKind(), leaf.slot);
            answer = JsonParser.parseString(serialized).getAsJsonObject();
            // Through the VM's expression store, as every engine read of an
            // expression is (ConcolicRegionRuntime#engineExpression): a node
            // the VM states by reference is its definition.  Taken raw, a
            // leaf's expression was a bare VmExpressionReference no session
            // table resolves, so no export of a store's content lowered
            // (solr-18413 Z2R: 4,152 refusals, every state.json leaf of the
            // witness's chain FREE or HELD).
            expression = ConcolicRegionRuntime.engineExpression(serialized);
        } catch (Throwable refused) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, port,
                    "the leaf's expression could not be read: "
                            + ConcolicRegionRuntime.rootCause(refused));
            return null;
        }
        String status = optionalString(answer, "status");
        if (!"OK".equals(status) && !"CONSTANT".equals(status)
                || expression == null || !expression.isJsonObject()) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, port,
                    "the VM states no value for the leaf (" + status + " "
                            + optionalString(answer, "reason") + "), so its"
                            + " readers pair with no export");
            return null;
        }
        Kind kind = kindOf(leaf.value);
        JsonObject crossing = expression.getAsJsonObject();
        String javaType = optionalString(answer, "javaType");
        if (kind == Kind.DEC_LONG || kind == Kind.BOOL) {
            JsonObject value = rendered(crossing, kind, (String) leaf.value);
            if (value == null) {
                kind = Kind.STR;
            } else {
                crossing = value;
                javaType = kind == Kind.DEC_LONG ? "J" : "Z";
            }
        } else if (kind == Kind.NUM && !wide(javaType).equals(javaType)) {
            crossing = widened(crossing, javaType, leaf.value, port);
            if (crossing == null) return null;
            javaType = wide(javaType);
        }
        long event = answer.has("exportEvent")
                ? answer.get("exportEvent").getAsLong() : 0L;
        Endpoint endpoint = RowRuntime.exported(producer, event, port, 0L, 0,
                crossing, javaType, String.valueOf(leaf.value));
        return endpoint == null ? null
                : new Exported(endpoint, kind, javaType);
    }

    /**
     * A leaf outside the writing occurrence's content keys
     * ({@link #contentKeys}) goes out as its recorded value, a constant:
     * the readers that pair with it read that value, whatever the writer's
     * expression of it was.
     */
    private static Exported exportConstant(OccurrenceAddress producer,
                                           String transport, String location,
                                           Leaf leaf) {
        Kind kind = kindOf(leaf.value);
        if (kind == null) return null;
        String text = String.valueOf(leaf.value);
        String javaType;
        JsonObject crossing;
        if (kind == Kind.STR) {
            javaType = "java/lang/String";
            crossing = new JsonObject();
            crossing.addProperty("_type", "ConStringSymbolExp");
            crossing.addProperty("_java_type", javaType);
            crossing.addProperty("_exp", "Y_L'String'_" + text);
        } else if (kind == Kind.DEC_LONG) {
            javaType = "J";
            crossing = constant(javaType, text);
        } else if (kind == Kind.BOOL) {
            javaType = "Z";
            crossing = constant(javaType, "true".equals(text) ? "1" : "0");
        } else {
            javaType = wide(boxType(leaf.value));
            crossing = constant(javaType, "D".equals(javaType)
                    ? Double.toString(Double.parseDouble(text))
                    : "Z".equals(javaType) ? ("true".equals(text) ? "1" : "0")
                    : text);
        }
        long event;
        try {
            event = engine().currentEventId();
        } catch (Throwable unread) {
            event = 0L;
        }
        Endpoint endpoint = RowRuntime.exported(producer, event,
                port(transport, location, leaf.pointer), 0L, 0, crossing,
                javaType, text);
        return endpoint == null ? null
                : new Exported(endpoint, kind, javaType);
    }

    /**
     * The content keys of the occurrence running here for the version
     * {@code key} (a plan row's {@code contentKeys}: the leaves of a chain
     * location the question's slice reads, by pointer prefix): null for no
     * restriction -- no planned occurrence, or one whose row states none --,
     * else the prefixes stated for this location, none where it states the
     * occurrence's keys elsewhere.
     */
    private static List<String> contentKeys(String transport, String key) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || active.activation.contentKeys == null) {
            return null;
        }
        String slot = MessageDoors.storeLocation(transport,
                MessageDoors.livePath(transport, key)).slot();
        List<String> prefixes = active.activation.contentKeys.get(slot);
        return prefixes == null ? Collections.<String>emptyList() : prefixes;
    }

    /** Whether a leaf at {@code pointer} lies at or under one of
     *  {@code keys}' prefixes; every leaf where {@code keys} is null. */
    static boolean under(List<String> keys, String pointer) {
        return keys == null
                || ContentPort.covers(keys, ContentPort.pointer(pointer));
    }

    /**
     * What a rendered leaf crosses as: the value a lone rendering
     * ({@code toString} of an integral or a boolean) the writer's expression
     * is renders, else the text read -- as a constant where the expression
     * is one, else as the parse of the expression.  Null for a BOOL leaf
     * the writer computed otherwise: it crosses as its String.
     */
    static JsonObject rendered(JsonObject expression, Kind kind,
                               String text) {
        boolean bool = kind == Kind.BOOL;
        JsonElement value = StringIdentities.renderedValue(expression, bool);
        if (value != null && value.isJsonObject()) {
            return value.getAsJsonObject();
        }
        String type = bool ? "Z" : "J";
        if (VmExpressionIr.exactStringLiteral(expression,
                any -> true) != null) {
            // The VM spells a boolean constant 1 or 0 (Y_Z_1), never its
            // text: Y_Z_false lowered to nothing (solr-18413 Z2U).
            return constant(type, !bool ? text : "true".equals(text) ? "1"
                    : "0");
        }
        if (bool) return null;
        JsonArray params = new JsonArray();
        params.add(expression);
        JsonObject parse = new JsonObject();
        parse.addProperty("_type", "MethodExpression");
        parse.addProperty("_name", "java/lang/Long parseLong");
        parse.add("_param_list", params);
        parse.add("_res_exp", constant(type, text));
        return parse;
    }

    /**
     * The type a number leaf crosses at: a JSON number has no width, and the
     * parser makes a {@code long} of every integral one and a {@code double}
     * of every other, so a writer's {@code int}, {@code short} or {@code
     * byte} crosses as a long and its {@code float} as a double.
     */
    static String wide(String javaType) {
        switch (javaType) {
            case "I": case "S": case "B": return "J";
            case "F": return "D";
            default: return javaType;
        }
    }

    /**
     * {@code expression} of {@code javaType} as the parser reads it back
     * ({@link #wide}): an integral one widened; a constant {@code float},
     * which the serializer writes as its decimal text and the parser reads
     * as the {@code double} that text is, as that double.  A symbolic float
     * crosses as nothing (null), named DIAGNOSTIC: no theory here renders a
     * float's decimal text, so its readers pair with no export and mint
     * their own.
     */
    static JsonObject widened(JsonObject expression, String javaType,
                              Object value, String port) {
        if ("F".equals(javaType)) {
            if (!"ConstExpr".equals(optionalString(expression, "_type"))) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        port, "a symbolic float leaf is not exported: its"
                                + " decimal text, which its readers parse"
                                + " back as a double, is no term here, so"
                                + " they pair with no export");
                return null;
            }
            return constant("D", Double.toString(Double.parseDouble(
                    String.valueOf(value))));
        }
        JsonObject cast = new JsonObject();
        cast.addProperty("_type", "TypeCastExpression");
        cast.add("_exp", expression);
        cast.addProperty("sourceJavaType", javaType);
        cast.addProperty("targetJavaType", wide(javaType));
        cast.addProperty("_java_type", wide(javaType));
        return cast;
    }

    /** A primitive constant as the VM spells one. */
    private static JsonObject constant(String type, String text) {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_exp", "Y_" + type + "_" + text);
        constant.addProperty("_java_type", type);
        return constant;
    }

    // ---- the reader's side -----------------------------------------------

    /**
     * The parser built {@code tree} from {@code bytes}: when the bytes are
     * a version a fetch read, in a replay, each leaf is minted on its
     * entry, paired with that version's export of it.
     *
     * @return the version read, as {@code transport\nkey}, or null for
     *         bytes no fetch named
     */
    static String parsed(byte[] bytes, Object tree) {
        String version = bytes == null ? null : FETCHED.remove(bytes);
        if (version == null || tree == null) return null;
        if (!capturing()) return version;
        int cut = version.indexOf('\n');
        String transport = version.substring(0, cut);
        String key = version.substring(cut + 1);
        // A watcher can parse a version before its writer files it: the
        // write in flight files its leaves first (MessageDoors#stored).
        MessageDoors.filed(transport, key);
        Map<String, Exported> exports;
        synchronized (EXPORTS) {
            exports = EXPORTS.get(version);
        }
        try {
            attach(transport, key, exports, tree,
                    contentKeys(transport, key));
        } catch (Throwable failed) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    transport + " " + key, "the version's content was not"
                            + " minted where it was parsed: "
                            + ConcolicRegionRuntime.rootCause(failed));
        }
        return version;
    }

    /**
     * Mints the parsed leaves of version {@code key} at or under
     * {@code keys}' prefixes, each paired with {@code exports}' leaf at its
     * pointer; every other leaf crosses as the value parsed, no attach.
     * Every leaf where {@code keys} is null.
     */
    static void attach(String transport, String key,
                       Map<String, Exported> exports, Object tree,
                       List<String> keys) {
        String location = MessageDoors.location(key);
        pauseObservation();
        try {
            ActiveRegion active = ConcolicRegionRuntime.activeRegion();
            OccurrenceAddress consumer = active != null
                    && active.d3Address != null ? active.d3Address
                    : occurrenceHere(transport);
            if (consumer == null) return;
            for (Leaf leaf : leaves(transport, location, tree)) {
                if (!under(keys, leaf.pointer)) continue;
                attach(active, consumer, transport, key, location, leaf,
                        exports == null ? null : exports.get(leaf.pointer));
            }
        } finally {
            resumeObservation();
        }
    }

    private static void attach(ActiveRegion active, OccurrenceAddress consumer,
                               String transport, String key, String location,
                               Leaf leaf, Exported export) {
        String port = port(transport, location, leaf.pointer);
        boolean paired = export != null && fits(export, leaf.value);
        Kind kind = paired ? export.kind : kindOf(leaf.value);
        Endpoint endpoint = RowRuntime.nextEndpoint(consumer, port, 0);
        if (endpoint == null || kind == null) return;
        String answer = FocusedReplay.answer(endpoint.id());
        String arrival = String.valueOf(leaf.value);
        if (!answer.isEmpty()) {
            Object planted = planted(kind, leaf.value, answer);
            if (planted == null || !leaf.replace(planted)) {
                RowRuntime.gap(GapKind.ASSIGNMENT_UNPLANTED, GapClass.BLOCKING,
                        port, "the wave's answer " + answer + " could not be"
                                + " written into the parsed leaf");
                return;
            }
            FocusedReplay.answered(!planted.equals(leaf.value));
            leaf.value = planted;
        }
        String label = HandoffMint.mintLabel(active != null
                ? HandoffMint.handoffMintKey(port, active.activation
                        .occurrenceId, HandoffMint.nextAttach(active
                        .activation.occurrenceId, port, "."), ".")
                : HandoffMint.ambientMintKey(port, consumer.render(), "."),
                port);
        JsonObject hole = mint(leaf, kind, label);
        if (hole == null) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, port,
                    "the parsed leaf was not minted, so what reads it reads"
                            + " a constant");
            return;
        }
        if (active != null) active.pathRecordingStarted = true;
        if (paired) {
            Interactions.carried(port, key, MessageDoors.REQUEST,
                    export.producer);
        }
        long seq;
        try {
            seq = engine().currentEventId();
        } catch (Throwable unread) {
            seq = 0L;
        }
        RowRuntime.attachedAt(endpoint, seq, port, 0L, key,
                MessageDoors.REQUEST, optionalString(hole, "exp"),
                optionalString(hole, "javaType"), arrival, !answer.isEmpty(),
                answer);
    }

    /**
     * Whether a leaf the reader holds can cross as {@code export} says: a
     * String as a String, a rendering as the value rendered, a box as a
     * value of its own type (the writer's number widened, {@link #wide}).
     */
    private static boolean fits(Exported export, Object value) {
        Kind own = kindOf(value);
        if (own == null) return false;
        if (export.kind == Kind.STR) return value instanceof String;
        return export.kind == own && (own != Kind.NUM
                || export.javaType.equals(boxType(value)));
    }

    /**
     * Mints {@code leaf} as {@code kind}'s template, its one hole labelled
     * {@code label}: the hole, or null.  A refusal landing on the leaf
     * object (a JVM-wide box, a String another mint claimed) is answered
     * by a fresh equal object, stored in its place.
     */
    private static JsonObject mint(Leaf leaf, Kind kind, String label) {
        String template = template(kind, leaf.value, label);
        for (int attempt = 0; attempt < 2; attempt++) {
            JsonObject answer;
            try {
                answer = JsonParser.parseString(engine().mintLeaf(leaf.parent,
                        leaf.slotKind(), leaf.slot, template))
                        .getAsJsonObject();
            } catch (Throwable refused) {
                return null;
            }
            if ("OK".equals(optionalString(answer, "status"))) {
                JsonArray holes = answer.getAsJsonArray("holes");
                return holes == null || holes.size() != 1 ? null
                        : holes.get(0).getAsJsonObject();
            }
            Object fresh = attempt == 0
                    && "OBJECT".equals(optionalString(answer, "landsOn"))
                    ? freshCopy(leaf.value) : null;
            if (fresh == null || !leaf.replace(fresh)) return null;
            leaf.value = fresh;
        }
        return null;
    }

    /** {@code System#mintLeaf}'s template of one hole. */
    private static String template(Kind kind, Object value, String label) {
        JsonObject part = new JsonObject();
        part.addProperty("hole", kind == Kind.STR ? "STR"
                : kind == Kind.DEC_LONG ? "DEC_LONG"
                : kind == Kind.BOOL ? "BOOL" : "NUM");
        part.addProperty("label", label);
        part.addProperty("text", String.valueOf(value));
        JsonArray parts = new JsonArray();
        parts.add(part);
        JsonObject template = new JsonObject();
        template.add("parts", parts);
        return template.toString();
    }

    /** How {@code value} crosses, or null for no leaf. */
    static Kind kindOf(Object value) {
        if (value instanceof String) {
            String text = (String) value;
            if (decimalLong(text)) return Kind.DEC_LONG;
            if ("true".equals(text) || "false".equals(text)) return Kind.BOOL;
            return Kind.STR;
        }
        if (value instanceof Number || value instanceof Boolean) {
            return boxType(value).isEmpty() ? null : Kind.NUM;
        }
        return null;
    }

    /** Whether {@code text} is Java's rendering of a long. */
    static boolean decimalLong(String text) {
        try {
            return Long.toString(Long.parseLong(text)).equals(text);
        } catch (NumberFormatException none) {
            return false;
        }
    }

    /** The descriptor a box's value is, or "" for no modeled box. */
    private static String boxType(Object value) {
        return value instanceof Long ? "J" : value instanceof Integer ? "I"
                : value instanceof Double ? "D" : value instanceof Float ? "F"
                : value instanceof Boolean ? "Z" : value instanceof Short
                ? "S" : value instanceof Byte ? "B" : "";
    }

    /** The leaf a wave's answer plants, as the parser would hold it. */
    private static Object planted(Kind kind, Object value, String answer) {
        try {
            switch (kind) {
                case STR:
                    JsonElement text = JsonParser.parseString(answer);
                    return text.isJsonPrimitive()
                            ? new String(text.getAsString()) : null;
                case DEC_LONG:
                    return Long.toString(Long.parseLong(answer.trim()));
                case BOOL:
                    return Boolean.toString(Boolean.parseBoolean(
                            answer.trim()));
                default:
                    return box(boxType(value), answer.trim());
            }
        } catch (RuntimeException unreadable) {
            return null;
        }
    }

    private static Object box(String type, String text) {
        switch (type) {
            case "J": return new Long(Long.parseLong(text));
            case "I": return new Integer(Integer.parseInt(text));
            case "D": return new Double(Double.parseDouble(text));
            case "F": return new Float(Float.parseFloat(text));
            case "Z": return new Boolean(Boolean.parseBoolean(text));
            case "S": return new Short(Short.parseShort(text));
            case "B": return new Byte(Byte.parseByte(text));
            default: return null;
        }
    }

    /** A fresh object equal to {@code value}, or null. */
    private static Object freshCopy(Object value) {
        if (value instanceof String) return new String((String) value);
        String type = boxType(value);
        return type.isEmpty() ? null : box(type, String.valueOf(value));
    }

    // ---- the documents ---------------------------------------------------

    /** The port one leaf of a location crosses ({@link ContentPort}). */
    static String port(String transport, String location, String pointer) {
        return ContentPort.of(trimmed(transport), MessageDoors.storeLocation(
                transport, location).slot(), pointer);
    }

    /** One leaf of a document: its holder, its slot and its pointer. */
    static final class Leaf {
        final Object parent;
        final Object slot;
        final String pointer;
        Object value;

        Leaf(Object parent, Object slot, String pointer, Object value) {
            this.parent = parent;
            this.slot = slot;
            this.pointer = pointer;
            this.value = value;
        }

        ConcolicVmBroker.SlotKind slotKind() {
            return parent instanceof Map ? ConcolicVmBroker.SlotKind.ENTRY
                    : ConcolicVmBroker.SlotKind.POSITION;
        }

        /** Stores {@code value} in this leaf's slot; whether it could. */
        @SuppressWarnings("unchecked")
        boolean replace(Object value) {
            try {
                if (parent instanceof Map) {
                    ((Map<Object, Object>) parent).put(slot, value);
                } else {
                    ((List<Object>) parent).set((Integer) slot, value);
                }
                return true;
            } catch (RuntimeException unmodifiable) {
                return false;
            }
        }
    }

    /**
     * The leaves of {@code document} depth first, each map's entries in its
     * own order and each list's elements in theirs, at most
     * {@link #MAX_LEAVES} of them at most {@link #MAX_DEPTH} deep; past
     * either bound a DIAGNOSTIC gap names the location.
     */
    static List<Leaf> leaves(String transport, String location,
                             Object document) {
        List<Leaf> leaves = new ArrayList<Leaf>();
        int[] dropped = new int[1];
        walk(document, "", 0, leaves, dropped);
        if (dropped[0] > 0) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "CONTENT_BOUND:" + port(transport, location, ""),
                    dropped[0] + " leaves of this document lie past "
                            + MAX_LEAVES + " leaves or " + MAX_DEPTH
                            + " levels and cross as constants");
        }
        return leaves;
    }

    private static void walk(Object node, String pointer, int depth,
                             List<Leaf> leaves, int[] dropped) {
        if (node instanceof Map) {
            for (Map.Entry<?, ?> entry
                    : new ArrayList<Map.Entry<?, ?>>(((Map<?, ?>) node)
                    .entrySet())) {
                visit(node, entry.getKey(), pointer + "/"
                        + escaped(String.valueOf(entry.getKey())),
                        entry.getValue(), depth, leaves, dropped);
            }
        } else if (node instanceof List) {
            List<?> list = (List<?>) node;
            for (int index = 0; index < list.size(); index++) {
                visit(node, index, pointer + "/" + index, list.get(index),
                        depth, leaves, dropped);
            }
        }
    }

    private static void visit(Object parent, Object slot, String pointer,
                              Object value, int depth, List<Leaf> leaves,
                              int[] dropped) {
        if (value instanceof Map || value instanceof List) {
            if (depth + 1 >= MAX_DEPTH) {
                dropped[0]++;
                return;
            }
            walk(value, pointer, depth + 1, leaves, dropped);
        } else if (kindOf(value) != null) {
            if (leaves.size() < MAX_LEAVES) {
                leaves.add(new Leaf(parent, slot, pointer, value));
            } else {
                dropped[0]++;
            }
        }
    }

    /** A JSON pointer's reference token (RFC 6901). */
    private static String escaped(String token) {
        return token.replace("~", "~0").replace("/", "~1");
    }

    /**
     * The leaves of {@code document} as a recording states them
     * ({@code CausynthTraceRecorder#storeLeaves}): each {@code [pointer,
     * leaf object]}, the pointer as a content port spells it; null past the
     * walk's bound, named, which reads as the whole document.
     */
    static List<Object[]> leafRows(String transport, String location,
                                   Object document) {
        List<Object[]> rows = new ArrayList<Object[]>();
        int[] dropped = new int[1];
        List<Leaf> leaves = new ArrayList<Leaf>();
        walk(document, "", 0, leaves, dropped);
        if (dropped[0] > 0) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "CONTENT_BOUND:" + port(transport, location, ""),
                    dropped[0] + " leaves of this document lie past "
                            + MAX_LEAVES + " leaves or " + MAX_DEPTH
                            + " levels: its leaves are stated as the whole"
                            + " document");
            return null;
        }
        for (Leaf leaf : leaves) {
            rows.add(new Object[] {ContentPort.pointer(leaf.pointer),
                    leaf.value});
        }
        return rows;
    }

    /** The occurrence a door event runs in, as WireExport names one. */
    private static OccurrenceAddress occurrenceHere(String transport) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null && active.d3Address != null) {
            return active.d3Address;
        }
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        OccurrenceAddress here = RowRuntime.occurrenceHere(
                view.source == null ? "" : view.source.key(), transport);
        RowRuntime.ambientActivation(here);
        return here;
    }

    /** Test seam: forgets every document, fetch and export. */
    static void resetForTests() {
        WRITTEN.clear();
        FETCHED.clear();
        synchronized (EXPORTS) {
            EXPORTS.clear();
        }
    }
}
