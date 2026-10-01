package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The near half of a codec crossing (WIRE-CODEC §4.3): one leaf's expression,
 * read from the VM at an encode, cut into a template of literal text and
 * typed holes, each hole's operand its own export.  A concrete leaf exports
 * too, as a constant template: its consumer's hole pairs with a constant arm.
 *
 * <p>The cut: a {@code concat} is flattened; {@code toString}/{@code valueOf}
 * of an integral operand is a {@code DEC_INT}/{@code DEC_LONG} hole of that
 * operand, of a boolean one a {@code BOOL} hole; a constant String is
 * literal text; any other String piece an {@code STR} hole; a primitive or
 * box leaf is one {@code NUM} hole.  Adjacent literals merge, and adjacent
 * holes become one {@code STR} hole (their texts could split more than one
 * way).  A String leaf with no hole is shaped by its text: a canonical
 * decimal is a DEC hole, {@code true}/{@code false} a BOOL hole, anything
 * else one STR hole, each over the constant.</p>
 */
final class CodecExport {
    /** Holes one template states before its leaf is one STR hole. */
    static final int MAX_HOLES = 8;
    /** The longest String leaf a template is matched against (f14's cap). */
    static final int MAX_LEAF_CHARS = 4096;

    private CodecExport() {
    }

    /** A hole's kind: the VM's template grammar (System#mintLeaf). */
    enum Kind {
        NUM("", "", ""),
        DEC_INT("I", "-?(?:0|[1-9][0-9]*)", "-??(?:0|[1-9][0-9]*?)"),
        DEC_LONG("J", "-?(?:0|[1-9][0-9]*)", "-??(?:0|[1-9][0-9]*?)"),
        BOOL("Z", "true|false", "true|false"),
        STR("Ljava/lang/String;", ".*", ".*?");

        /** The hole symbol's sort, as a JVM descriptor ("" for NUM: the
         *  leaf's). */
        final String javaType;
        /** Its text, as long as it may be. */
        final String longest;
        /** Its text, as short as it may be. */
        final String shortest;

        Kind(String javaType, String longest, String shortest) {
            this.javaType = javaType;
            this.longest = longest;
            this.shortest = shortest;
        }
    }

    /** One piece of a template: literal text, or a hole of a kind. */
    static final class Part {
        final String literal;
        final Kind kind;
        /** The hole's operand at the producer; null on the wire. */
        final JsonObject operand;

        private Part(String literal, Kind kind, JsonObject operand) {
            this.literal = literal;
            this.kind = kind;
            this.operand = operand;
        }

        static Part literal(String text) {
            return new Part(text, null, null);
        }

        static Part hole(Kind kind, JsonObject operand) {
            return new Part(null, kind, operand);
        }

        boolean hole() {
            return kind != null;
        }
    }

    /** One leaf's template: its parts in order. */
    static final class Template {
        final List<Part> parts;

        Template(List<Part> parts) {
            this.parts = Collections.unmodifiableList(parts);
        }

        /** The holes, in order. */
        List<Part> holes() {
            List<Part> holes = new ArrayList<>();
            for (Part part : parts) {
                if (part.hole()) holes.add(part);
            }
            return holes;
        }

        /** Whether it is a numeric leaf's one NUM hole. */
        boolean numeric() {
            return parts.size() == 1 && parts.get(0).kind == Kind.NUM;
        }

        /**
         * Each hole's text in {@code text}, or null when the literals are
         * not its text, a decimal is not Java's rendering of an int or a
         * long, or the literals do not tell the holes apart (the reading
         * with every hole as short as it may be and the one with every hole
         * as long differ).  One reading for both sides: the producer states
         * the texts the consumer reads back.
         */
        List<String> match(String text) {
            if (numeric()) return Collections.singletonList(text);
            List<String> shortest = match(text, false);
            return shortest != null && shortest.equals(match(text, true))
                    ? shortest : null;
        }

        private List<String> match(String text, boolean longest) {
            StringBuilder regex = new StringBuilder();
            for (Part part : parts) {
                regex.append(!part.hole() ? Pattern.quote(part.literal)
                        : "(" + (longest ? part.kind.longest
                        : part.kind.shortest) + ")");
            }
            Matcher matched = Pattern.compile(regex.toString(),
                    Pattern.DOTALL).matcher(text);
            if (!matched.matches()) return null;
            List<String> texts = new ArrayList<>();
            int group = 1;
            for (Part part : parts) {
                if (!part.hole()) continue;
                String hole = matched.group(group++);
                if (!inRange(part.kind, hole)) return null;
                texts.add(hole);
            }
            return texts;
        }

        /** The leaf text these hole texts make. */
        String render(List<String> texts) {
            StringBuilder text = new StringBuilder();
            int hole = 0;
            for (Part part : parts) {
                text.append(part.hole() ? texts.get(hole++) : part.literal);
            }
            return text.toString();
        }

        /** The VM's template of these holes: {@code {"parts":[...]}}. */
        String mintJson(List<String> labels, List<String> texts) {
            JsonArray parts = new JsonArray();
            int hole = 0;
            for (Part part : this.parts) {
                JsonObject piece = new JsonObject();
                if (!part.hole()) {
                    piece.addProperty("literal", part.literal);
                } else {
                    piece.addProperty("hole", part.kind.name());
                    piece.addProperty("label", labels.get(hole));
                    if (part.kind != Kind.NUM) {
                        piece.addProperty("text", texts.get(hole));
                    }
                    hole++;
                }
                parts.add(piece);
            }
            JsonObject template = new JsonObject();
            template.add("parts", parts);
            return template.toString();
        }

        /** The same parts without their operands: what the wire carries. */
        JsonArray wire() {
            JsonArray parts = new JsonArray();
            for (Part part : this.parts) {
                JsonObject piece = new JsonObject();
                if (part.hole()) piece.addProperty("h", part.kind.name());
                else piece.addProperty("l", part.literal);
                parts.add(piece);
            }
            return parts;
        }

        /** The parts {@link #wire} wrote. */
        static Template fromWire(JsonArray wire) {
            List<Part> parts = new ArrayList<>();
            for (JsonElement element : wire) {
                JsonObject piece = element.getAsJsonObject();
                parts.add(piece.has("h")
                        ? Part.hole(Kind.valueOf(piece.get("h").getAsString()),
                        null)
                        : Part.literal(piece.get("l").getAsString()));
            }
            return new Template(parts);
        }

        /** One hole standing for a whole leaf of that sort. */
        static Template whole(boolean numeric, JsonObject operand) {
            return new Template(Collections.singletonList(Part.hole(
                    numeric ? Kind.NUM : Kind.STR, operand)));
        }
    }

    /**
     * How a decoded leaf reads against its producer's template: the
     * template and each hole's text when the leaf is the value the producer
     * recorded and reads as the template; one hole of the whole leaf when it
     * is that value and the producer's template was itself one whole-leaf
     * hole (a box the codec decodes as text, or text as a box); otherwise
     * the mismatch, and the leaf stays concrete -- local data of the same
     * message type meets an exchange's entries this way.
     */
    static final class Reading {
        final Template template;
        final List<String> texts;
        /** {@code VALUE_MISMATCH}, {@code TEMPLATE_MISMATCH}, or "". */
        final String mismatch;

        private Reading(Template template, List<String> texts,
                        String mismatch) {
            this.template = template;
            this.texts = texts;
            this.mismatch = mismatch;
        }

        static Reading of(Template produced, Object leaf, String recorded) {
            boolean numeric = !(leaf instanceof String);
            String text = numeric ? String.valueOf(leaf) : (String) leaf;
            if (!text.equals(recorded)) {
                return new Reading(null, null, "VALUE_MISMATCH");
            }
            List<String> texts = produced.numeric() == numeric
                    ? produced.match(text) : null;
            if (texts != null) return new Reading(produced, texts, "");
            if (produced.parts.size() == 1 && produced.parts.get(0).hole()) {
                return new Reading(Template.whole(numeric, null),
                        Collections.singletonList(text), "");
            }
            return new Reading(null, null, "TEMPLATE_MISMATCH");
        }
    }

    /** Whether a hole's text is one its kind renders. */
    static boolean inRange(Kind kind, String text) {
        try {
            if (kind == Kind.DEC_INT) Integer.parseInt(text);
            if (kind == Kind.DEC_LONG) Long.parseLong(text);
            return true;
        } catch (NumberFormatException outOfRange) {
            return false;
        }
    }

    /**
     * Cuts one leaf's expression into its template.  {@code numeric}: the
     * leaf is a primitive or a box, one NUM hole of {@code expression}.
     * {@code concrete} is the leaf's text; {@code javaType} its JVM
     * descriptor.
     */
    static Template cut(JsonObject expression, boolean numeric,
                        String javaType, String concrete) {
        if (numeric) {
            return Template.whole(true, expression != null ? expression
                    : constant(javaType, concrete));
        }
        List<Part> parts = new ArrayList<>();
        List<JsonObject> run = new ArrayList<>();
        if (expression != null) {
            for (JsonObject term : flatten(expression)) {
                Part part = part(term);
                if (part.hole()) {
                    run.add(term);
                    if (run.size() == 1) parts.add(part);
                    else parts.set(parts.size() - 1, Part.hole(Kind.STR,
                            concat(run)));
                    continue;
                }
                if (part.literal.isEmpty()) continue;
                run.clear();
                if (!parts.isEmpty() && !parts.get(parts.size() - 1).hole()) {
                    Part before = parts.remove(parts.size() - 1);
                    parts.add(Part.literal(before.literal + part.literal));
                } else {
                    parts.add(part);
                }
            }
        }
        Template template = new Template(parts);
        if (template.holes().isEmpty()) return shaped(concrete);
        if (template.holes().size() > MAX_HOLES) {
            return Template.whole(false, expression);
        }
        return template;
    }

    /** A constant String leaf, shaped by its text. */
    private static Template shaped(String text) {
        if (inRange(Kind.DEC_INT, text) && decimal(text)) {
            return new Template(Collections.singletonList(Part.hole(
                    Kind.DEC_INT, constant("I", text))));
        }
        if (inRange(Kind.DEC_LONG, text) && decimal(text)) {
            return new Template(Collections.singletonList(Part.hole(
                    Kind.DEC_LONG, constant("J", text))));
        }
        if ("true".equals(text) || "false".equals(text)) {
            return new Template(Collections.singletonList(Part.hole(
                    Kind.BOOL, constant("Z", "true".equals(text) ? "1"
                            : "0"))));
        }
        return Template.whole(false, constantString(text));
    }

    private static boolean decimal(String text) {
        return text.matches(Kind.DEC_LONG.longest);
    }

    /** One term's part: literal, a typed hole, or an STR hole. */
    private static Part part(JsonObject term) {
        String type = optionalString(term, "_type");
        if ("ConStringSymbolExp".equals(type)) {
            return Part.literal(VmExpressionIr.constantPayload(
                    optionalString(term, "_exp")));
        }
        JsonObject rendered = term;
        if (VmExpressionIr.STRING_OPERATION_TYPE.equals(type)) {
            String name = optionalString(term, "_name");
            JsonArray operands = term.getAsJsonArray("_param_list");
            if (!("toString".equals(name) || "valueOf".equals(name))
                    || operands == null || operands.size() != 1
                    || !operands.get(0).isJsonObject()) {
                return Part.hole(Kind.STR, term);
            }
            rendered = operands.get(0).getAsJsonObject();
        }
        String sort = sort(rendered);
        if ("I".equals(sort) || "S".equals(sort) || "B".equals(sort)) {
            return Part.hole(Kind.DEC_INT, rendered);
        }
        if ("J".equals(sort)) return Part.hole(Kind.DEC_LONG, rendered);
        if ("Z".equals(sort)) return Part.hole(Kind.BOOL, rendered);
        return Part.hole(Kind.STR, term);
    }

    /** The sort a term states: its own, else its first operand's. */
    private static String sort(JsonObject term) {
        for (ExpressionWalk walk = ExpressionWalk.of(term); walk.hasNext(); ) {
            String stated = optionalString(walk.next(), "_java_type");
            if (!stated.isEmpty()) return stated;
        }
        return "";
    }

    /** The pieces of a String expression, concats flattened. */
    private static List<JsonObject> flatten(JsonObject expression) {
        List<JsonObject> terms = new ArrayList<>();
        if (VmExpressionIr.STRING_OPERATION_TYPE.equals(
                optionalString(expression, "_type"))
                && "concat".equals(optionalString(expression, "_name"))) {
            JsonArray operands = expression.getAsJsonArray("_param_list");
            for (JsonElement operand : operands == null ? new JsonArray()
                    : operands) {
                if (operand.isJsonObject()) {
                    terms.addAll(flatten(operand.getAsJsonObject()));
                }
            }
            return terms;
        }
        terms.add(expression);
        return terms;
    }

    private static JsonObject concat(List<JsonObject> terms) {
        JsonObject concat = new JsonObject();
        concat.addProperty("_type", VmExpressionIr.STRING_OPERATION_TYPE);
        concat.addProperty("_name", "concat");
        concat.addProperty("_is_not", false);
        JsonArray operands = new JsonArray();
        for (JsonObject term : terms) operands.add(term);
        concat.add("_param_list", operands);
        return concat;
    }

    /** A typed constant, spelled as the VM spells one. */
    static JsonObject constant(String javaType, String value) {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", javaType);
        constant.addProperty("_exp", "Y_" + javaType + "_" + value);
        return constant;
    }

    private static JsonObject constantString(String text) {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConStringSymbolExp");
        constant.addProperty("_java_type", "java/lang/String");
        constant.addProperty("_exp", "Y_L'String'_" + text);
        return constant;
    }

    // ---- one encode, through the VM ------------------------------------

    /**
     * Exports every leaf of one walk: one entry per hole, its producer the
     * occurrence encoding it now.  A leaf the VM will not state is named
     * and left out; so is one whose text passes the matching bound.
     */
    static List<CodecMessages.Entry> export(CodecWalker walker,
                                            List<CodecWalker.Leaf> leaves,
                                            int ordinal) {
        List<CodecMessages.Entry> entries = new ArrayList<>();
        for (CodecWalker.Leaf leaf : leaves) {
            String port = walker.port(leaf.key);
            JsonObject answer = exportLeaf(leaf);
            String status = answer == null ? "UNANSWERED"
                    : optionalString(answer, "status");
            if (!"OK".equals(status) && !"CONSTANT".equals(status)) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        port, "the VM stated no expression for the leaf "
                                + CodecWalker.text(leaf.path) + " of "
                                + walker.codec() + " (" + status + " "
                                + (answer == null ? ""
                                : optionalString(answer, "reason"))
                                + "), so the message carries no value for"
                                + " it");
                continue;
            }
            boolean numeric = !(leaf.value instanceof String);
            String concrete = numeric ? String.valueOf(leaf.value)
                    : (String) leaf.value;
            if (concrete.length() > MAX_LEAF_CHARS) {
                RowRuntime.gap(GapKind.BOUND_INSUFFICIENT,
                        GapClass.DIAGNOSTIC, port, "the leaf "
                                + CodecWalker.text(leaf.path) + " of "
                                + walker.codec() + " is " + concrete.length()
                                + " characters, past the " + MAX_LEAF_CHARS
                                + " a template is matched against");
                continue;
            }
            JsonElement expression = answer.get("expression");
            String javaType = optionalString(answer, "javaType");
            Template template = cut(expression != null
                    && expression.isJsonObject()
                    ? expression.getAsJsonObject() : null, numeric, javaType,
                    concrete);
            List<String> texts = template.match(concrete);
            if (texts == null) {
                // The leaf's text is not its expression's rendering (a cut
                // literal): one hole of the whole leaf.
                template = Template.whole(numeric, expression != null
                        && expression.isJsonObject()
                        ? expression.getAsJsonObject() : constant(javaType,
                        concrete));
                texts = Collections.singletonList(concrete);
            }
            OccurrenceAddress producer = CodecRuntime.occurrenceHere(port);
            if (producer == null) continue;
            long seq = answer.has("exportEvent")
                    ? answer.get("exportEvent").getAsLong() : 0L;
            List<Part> holes = template.holes();
            for (int hole = 0; hole < holes.size(); hole++) {
                Kind kind = holes.get(hole).kind;
                Endpoint endpoint = Identity.endpointAt(producer, port,
                        CodecRuntime.frameSite(port, "", leaf.path, hole),
                        CodecRuntime.attempt());
                entries.add(new CodecMessages.Entry(walker.codec(), ordinal,
                        leaf.path, hole, template, endpoint, seq, concrete,
                        texts.get(hole), holes.get(hole).operand,
                        kind == Kind.NUM ? javaType : kind.javaType));
            }
        }
        return entries;
    }

    /**
     * One leaf's VM export, addressed by its slot; a container the VM does
     * not model is asked for the leaf object's own expression instead.
     */
    private static JsonObject exportLeaf(CodecWalker.Leaf leaf) {
        try {
            ConcolicVmBroker vm = ConcolicVmBroker.engine();
            JsonObject answer = parse(vm.exportLeaf(CodecRuntime.vmParent(
                    leaf), CodecRuntime.vmSlotKind(leaf),
                    CodecRuntime.vmSlot(leaf)));
            if (CodecRuntime.unmodeled(answer)) {
                answer = parse(vm.exportLeaf(leaf.value,
                        ConcolicVmBroker.SlotKind.VALUE, null));
            }
            return answer == null ? null
                    : ConcolicRegionRuntime.decodeVmEnvelope(answer,
                    ConcolicRegionRuntime.activeRegion());
        } catch (Throwable refused) {
            return null;
        }
    }

    static JsonObject parse(String json) {
        JsonElement parsed = JsonParser.parseString(json);
        return parsed.isJsonObject() ? parsed.getAsJsonObject() : null;
    }
}
