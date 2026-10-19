package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.ArrayList;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

public final class SmtNames {

    private SmtNames() {
    }

    public static boolean reference(String token) {
        if (token == null || !token.startsWith(SmtLowering.REFERENCE)) return false;
        String digest = token.substring(SmtLowering.REFERENCE.length());
        if (digest.length() != 16) return false;
        for (int index = 0; index < digest.length(); index++) {
            char value = digest.charAt(index);
            boolean hex = value >= '0' && value <= '9'
                    || value >= 'a' && value <= 'f';
            if (!hex) return false;
        }
        return true;
    }

    public static boolean symbolCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/#'".indexOf(value) >= 0;
    }

    public static Set<String> preambleNames() {
        return Preamble.NAMES;
    }

    private static final class Preamble {
        static final Set<String> NAMES = names();

        private static Set<String> names() {
            List<String> lines = new ArrayList<String>(
                    VmTermLowering.preamble());
            lines.add(VmTermLowering.JAVA_INT_TO_STRING);
            lines.add(VmTermLowering.JAVA_ASCII_LOWER);
            lines.add(VmTermLowering.JAVA_ASCII_UPPER);
            lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
            Set<String> names = new LinkedHashSet<String>();
            for (String line : lines) names.addAll(declaredIn(line));
            return Collections.unmodifiableSet(names);
        }
    }

    private static List<String> declaredIn(String line) {
        List<String> names = new ArrayList<String>();
        if (line == null) return names;
        boolean datatype = line.startsWith("(declare-datatypes");
        for (int index = 0; index < line.length(); index++) {
            if (line.charAt(index) != '(') continue;
            int end = index + 1;
            while (end < line.length()
                    && symbolCharacter(line.charAt(end))) end++;
            String head = line.substring(index + 1, end);
            if (head.isEmpty()) continue;
            if (datatype) {
                names.add(head);
                continue;
            }
            if (!head.startsWith("declare-") && !head.startsWith("define-")) {
                continue;
            }
            int from = end;
            while (from < line.length()
                    && Character.isWhitespace(line.charAt(from))) {
                from++;
            }
            int to = from;
            while (to < line.length()
                    && symbolCharacter(line.charAt(to))) to++;
            if (to > from) names.add(line.substring(from, to));
        }
        return names;
    }

    public static final Set<String> BUILTIN =
            Collections.unmodifiableSet(new LinkedHashSet<String>(
                    Arrays.asList("=", "=>", "+", "-", "*", "/", "<", "<=",
                    ">", ">=", "!", "_",
                    "and", "or", "not", "xor", "ite", "let", "forall",
                    "exists", "distinct", "true", "false", "div", "mod",
                    "abs", "rem", "select", "store", "as", "const", "lambda",
                    "is", "bvadd", "bvsub", "bvmul", "bvand", "bvor",
                    "bvxor", "bvnot", "bvshl", "bvlshr", "bvashr", "bvsdiv",
                    "bvudiv", "bvsrem", "bvurem", "bvule", "bvult", "bvsle",
                    "bvslt", "bvuge", "bvugt", "bvsge", "bvsgt", "concat",
                    "extract", "zero_extend", "sign_extend", "Int", "Bool",
                    "Real", "String", "Array", "Ref", "Value", "AssocState",
                    "IndexedState", "FloatingPoint", "RoundingMode",
                    "roundNearestTiesToEven", "RNE", "RTZ", "RTP", "RTN",
                    "RNA", "nullRef", "java_int_wrap", "java_long_wrap",
                    "java_int_to_string", "java_ascii_lower",
                    "java_ascii_upper", "indexed_state_of",
                    "assoc_state_of", "indexed_read", "indexed_write",
                    "indexed_append", "indexed_insert", "indexed_remove",
                    "indexed_contains", "indexed_size", "indexed_elements",
                    "assoc_has", "assoc_read", "assoc_key_at",
                    "assoc_position_of",
                    "assoc_put", "assoc_remove",
                    "assoc_remove_if", "assoc_put_if",
                    "assoc_size", "assoc_present", "assoc_values",
                    "assoc_order", "assoc_position", "assoc_view_key",
                    "assoc_view_position", "VByte", "VChar",
                    "VShort", "VInt", "VLong", "VFloat", "VDouble", "VBool",
                    "VRef", "VString", "valueByte", "valueChar", "valueShort",
                    "valueInt", "valueLong", "valueFloat", "valueDouble",
                    "valueBool", "valueRef", "valueString", "str", "fp",
                    "to_real", "to_int", "is_int", "divisible",
                    "str.++", "str.len", "str.contains", "str.prefixof",
                    "str.suffixof", "str.from_int", "str.to_int", "str.substr",
                    "str.indexof", "str.at", "str.from_code", "str.to_code",
                    "re.union", "re.++",
                    "str.in_re", "str.to_re", "re.*", "re.range",
                    "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.neg",
                    "fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq",
                    "fp.isNaN", "fp.to_sbv", "to_fp", "int2bv", "bv2int")));

    public static List<String> names(String text) {
        List<String> names = new ArrayList<String>();
        for (String token : tokens(text)) {
            if (name(token)) names.add(token);
        }
        return names;
    }

    public static final class Named implements Iterable<String> {
        private final List<String> names;
        private final Map<String, Integer> position =
                new java.util.HashMap<String, Integer>();

        private Named(List<String> names) {
            this.names = Collections.unmodifiableList(names);
            for (String name : names) position.put(name, position.size());
        }

        @Override
        public java.util.Iterator<String> iterator() {
            return names.iterator();
        }

        public int size() {
            return names.size();
        }

        public int position(String name) {
            Integer at = position.get(name);
            return at == null ? -1 : at;
        }
    }

    public static Named named(Iterable<String> texts) {
        Set<String> names = new LinkedHashSet<String>();
        if (texts != null) {
            for (String text : texts) names.addAll(names(text));
        }
        return new Named(new ArrayList<String>(names));
    }

    public static Set<String> letBound(String text) {
        Set<String> bound = new LinkedHashSet<String>();
        if (text == null || !text.contains("(let ")) return bound;
        List<String> tokens = tokens(text);
        for (int at = 0; at < tokens.size(); at++) {
            if (!"let".equals(tokens.get(at))) continue;
            int index = at + 1;
            if (index >= tokens.size() || !OPEN.equals(tokens.get(index))) {
                continue;
            }
            int depth = 0;
            for (; index < tokens.size(); index++) {
                String token = tokens.get(index);
                if (OPEN.equals(token)) {
                    depth++;
                    if (depth == 2 && index + 1 < tokens.size()
                            && name(tokens.get(index + 1))) {
                        bound.add(tokens.get(index + 1));
                    }
                    continue;
                }
                if (CLOSE.equals(token)) {
                    depth--;
                    if (depth <= 0) break;
                }
            }
        }
        return bound;
    }

    private static List<String> tokens(String text) {
        List<String> tokens = new ArrayList<String>();
        pass(text, KEEP, tokens, Spelling.AS_WRITTEN, null);
        return tokens;
    }

    private static final String OPEN = "|(";
    private static final String CLOSE = "|)";

    public static Set<String> symbols(String text, Set<String> into) {
        for (String name : names(text)) {
            if (!BUILTIN.contains(name)) into.add(name);
        }
        return into;
    }

    public static String rename(String text, Map<String, String> renames,
                                Predicate<String> stated,
                                Set<String> unknown) {
        List<String> kept = new ArrayList<String>();
        StringBuilder out = new StringBuilder();
        pass(text, renames::get, kept, Spelling.AS_WRITTEN, out);
        if (text != null && !text.contains("(let ")) {
            for (String name : kept) {
                if (!name(name) || BUILTIN.contains(name)) continue;
                if (stated != null && stated.test(name)) continue;
                unknown.add(name);
            }
        }
        return out.toString().trim();
    }

    public static String substitute(String text,
                                    Function<String, String> renames) {
        StringBuilder out = new StringBuilder();
        pass(text, renames, null, Spelling.AS_WRITTEN, out);
        return out.toString();
    }

    private static final Function<String, String> KEEP = token -> null;

    private enum Spelling {
        AS_WRITTEN,
        LEGAL
    }

    private static void pass(String text, Function<String, String> renames,
                             List<String> kept, Spelling spelling,
                             StringBuilder out) {
        if (text == null) return;
        int index = 0;
        while (index < text.length()) {
            char value = text.charAt(index);
            if (value == '"') {
                int end = pastLiteral(text, index, '"');
                if (out != null) out.append(text, index, end);
                index = end;
                continue;
            }
            if (value == ';') {
                int end = text.indexOf('\n', index);
                end = end < 0 ? text.length() : end;
                if (out != null) out.append(text, index, end);
                index = end;
                continue;
            }
            if (value == '|') {
                int end = pastLiteral(text, index, '|');
                String token = text.substring(index + 1,
                        Math.max(index + 1, end - 1));
                index = emit(out, text, index, end, token, renames, kept,
                        Spelling.AS_WRITTEN);
                continue;
            }
            if (!symbolCharacter(value)) {
                if (kept != null && value == '(') kept.add(OPEN);
                if (kept != null && value == ')') kept.add(CLOSE);
                if (out != null) out.append(value);
                index++;
                continue;
            }
            int end = index;
            while (end < text.length()
                    && symbolCharacter(text.charAt(end))) {
                end++;
            }
            index = emit(out, text, index, end, text.substring(index, end),
                    renames, kept, spelling);
        }
    }

    private static int emit(StringBuilder out, String text, int start,
                            int end, String token,
                            Function<String, String> renames,
                            List<String> kept, Spelling spelling) {
        String renamed = name(token) ? renames.apply(token) : null;
        if (renamed != null) {
            if (out != null) out.append(renamed);
            return end;
        }
        append(out, text, start, end, token, spelling);
        if (kept != null) kept.add(token);
        return end;
    }

    private static void append(StringBuilder out, String text, int start,
                               int end, String token, Spelling spelling) {
        if (out == null) return;
        if (spelling == Spelling.LEGAL && !simpleSymbol(token)) {
            out.append('|').append(token).append('|');
            return;
        }
        out.append(text, start, end);
    }

    private static int pastLiteral(String text, int at, char delimiter) {
        int index = at + 1;
        while (index < text.length() && text.charAt(index) != delimiter) {
            index++;
        }
        return index < text.length() ? index + 1 : index;
    }

    private static boolean name(String token) {
        if (token.isEmpty()) return false;
        char first = token.charAt(0);
        return !Character.isDigit(first) && first != '-' && first != '.'
                && first != '#' && first != '|';
    }

    public static List<String> reachedPreamble(List<String> preamble,
                                               Iterable<String> texts) {
        return reachedPreamble(preamble, named(texts));
    }

    public static List<String> reachedPreamble(List<String> preamble,
                                               Named names) {
        Map<String, String> definition = new LinkedHashMap<String, String>();
        for (String line : preamble) {
            if (line == null || !line.startsWith("(define-fun")) continue;
            for (String name : declaredIn(line)) definition.put(name, line);
        }
        Set<String> reached = new LinkedHashSet<String>();
        boolean ordered = false;
        Deque<String> pending = new ArrayDeque<String>();
        for (String token : names) {
            ordered |= ContainerStateModel.ORDER_READERS.contains(token);
            if (definition.containsKey(token) && reached.add(token)) {
                pending.push(token);
            }
        }
        while (!pending.isEmpty()) {
            for (String token : names(definition.get(pending.pop()))) {
                ordered |= ContainerStateModel.ORDER_READERS.contains(token);
                if (definition.containsKey(token) && reached.add(token)) {
                    pending.push(token);
                }
            }
        }
        List<String> lines = new ArrayList<String>();
        for (String line : preamble) {
            if (line == null) continue;
            if (!line.startsWith("(define-fun")) {
                lines.add(line);
                continue;
            }
            for (String name : declaredIn(line)) {
                if (reached.contains(name)) {
                    lines.add(ordered ? line
                            : ContainerStateModel.unordered(line));
                    break;
                }
            }
        }
        return lines;
    }

    public static String legalSymbols(String query) {
        if (query == null || query.isEmpty()) return query;
        StringBuilder out = new StringBuilder();
        pass(query, KEEP, null, Spelling.LEGAL, out);
        return out.toString();
    }

    private static boolean simpleSymbol(String token) {
        if (token.isEmpty()) return true;
        char first = token.charAt(0);
        if (first == ':' || first == '#' || Character.isDigit(first)) {
            return true;
        }
        for (int index = 0; index < token.length(); index++) {
            if (!simpleCharacter(token.charAt(index))) return false;
        }
        return true;
    }

    private static boolean simpleCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/".indexOf(value) >= 0;
    }
}
