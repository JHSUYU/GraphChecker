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

final class StoreContent {
    static final int MAX_LEAVES = 1024;
    static final int MAX_DEPTH = 16;

    private static final Map<byte[], Object> WRITTEN =
            Collections.synchronizedMap(new WeakHashMap<byte[], Object>());
    private static final Map<byte[], String> FETCHED =
            Collections.synchronizedMap(new WeakHashMap<byte[], String>());
    private static final Interactions.Bounded<Map<String, Exported>>
            EXPORTS = Interactions.bounded();

    private StoreContent() {
    }

    enum Kind { STR, DEC_LONG, BOOL, NUM }

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

    static boolean capturing() {
        return RowRuntime.open();
    }

    static void written(byte[] bytes, Object document) {
        if (bytes != null && document != null) WRITTEN.put(bytes, document);
    }

    static void fetched(String transport, String key, byte[] bytes) {
        if (bytes != null && (RowRuntime.open()
                || CausynthTraceRecorder.tracing())) {
            FETCHED.put(bytes, trimmed(transport) + "\n" + trimmed(key));
        }
    }


    static Object stored(String transport, String key, byte[] bytes) {
        Object document = bytes == null ? null : WRITTEN.remove(bytes);
        if (document == null || !capturing()) return document;
        try {
            export(transport, key, document, contentKeys(transport, key));
        } catch (Throwable failed) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    trimmed(transport) + " " + key, "the version's content"
                            + " was not exported: "
                            + ConcolicRegionRuntime.rootCause(failed));
        }
        return document;
    }

    static void export(String transport, String key, Object document,
                       List<String> keys) {
        if (keys.isEmpty()) return;
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

    private static List<String> contentKeys(String transport, String key) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null && active.activation.contentKeys == null) {
            return Collections.<String>emptyList();
        }
        String slot = MessageDoors.storeLocation(transport,
                MessageDoors.livePath(transport, key)).slot();
        List<String> prefixes = active != null
                ? active.activation.contentKeys.get(slot)
                : ConcolicTaskPlan.configuration().chainKeys.get(slot);
        return prefixes == null ? Collections.<String>emptyList() : prefixes;
    }

    static boolean under(List<String> keys, String pointer) {
        return ContentPort.covers(keys, ContentPort.pointer(pointer));
    }

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

    static String wide(String javaType) {
        switch (javaType) {
            case "I": case "S": case "B": return "J";
            case "F": return "D";
            default: return javaType;
        }
    }

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

    private static JsonObject constant(String type, String text) {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_exp", "Y_" + type + "_" + text);
        constant.addProperty("_java_type", type);
        return constant;
    }


    static String parsed(byte[] bytes, Object tree) {
        String version = bytes == null ? null : FETCHED.remove(bytes);
        if (version == null || tree == null) return null;
        if (!capturing()) return version;
        int cut = version.indexOf('\n');
        String transport = version.substring(0, cut);
        String key = version.substring(cut + 1);
        MessageDoors.filed(transport, key);
        Map<String, Exported> exports;
        synchronized (EXPORTS) {
            exports = EXPORTS.get(version);
        }
        List<String> keys = contentKeys(transport, key);
        if (keys.isEmpty()) return version;
        try {
            attach(transport, key, exports, tree, keys);
        } catch (Throwable failed) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    transport + " " + key, "the version's content was not"
                            + " minted where it was parsed: "
                            + ConcolicRegionRuntime.rootCause(failed));
        }
        return version;
    }

    static void attach(String transport, String key,
                       Map<String, Exported> exports, Object tree,
                       List<String> keys) {
        if (keys.isEmpty()) return;
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

    private static boolean fits(Exported export, Object value) {
        Kind own = kindOf(value);
        if (own == null) return false;
        if (export.kind == Kind.STR) return value instanceof String;
        return export.kind == own && (own != Kind.NUM
                || export.javaType.equals(boxType(value)));
    }

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

    static boolean decimalLong(String text) {
        try {
            return Long.toString(Long.parseLong(text)).equals(text);
        } catch (NumberFormatException none) {
            return false;
        }
    }

    private static String boxType(Object value) {
        return value instanceof Long ? "J" : value instanceof Integer ? "I"
                : value instanceof Double ? "D" : value instanceof Float ? "F"
                : value instanceof Boolean ? "Z" : value instanceof Short
                ? "S" : value instanceof Byte ? "B" : "";
    }

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

    private static Object freshCopy(Object value) {
        if (value instanceof String) return new String((String) value);
        String type = boxType(value);
        return type.isEmpty() ? null : box(type, String.valueOf(value));
    }


    static String port(String transport, String location, String pointer) {
        return ContentPort.of(trimmed(transport), MessageDoors.storeLocation(
                transport, location).slot(), pointer);
    }

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

    private static String escaped(String token) {
        return token.replace("~", "~0").replace("/", "~1");
    }

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
}
