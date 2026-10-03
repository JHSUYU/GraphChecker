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

/**
 * THE ONE TOKENIZER over SMT-LIB text, and the ONE vocabulary
 * ({@link #BUILTIN}) every stage reads with; stateless.  Two vocabularies
 * over one query would let one stage call a name a theory operator and
 * another call it undeclared.
 */
public final class SmtNames {

    private SmtNames() {
    }

    /** Whether one token is an expression reference: EXPR. and 16 hex. */
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

    /**
     * A character a NAME may be spelled with: SMT-LIB's simple-symbol
     * alphabet plus the runtime's {@code #} and the VM's {@code '}.  Trap: a
     * narrower set splits names at {@code /} and looks up half a name.
     */
    public static boolean symbolCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/#'".indexOf(value) >= 0;
    }

    /**
     * Every name the fixed preamble declares (sorts, constructors,
     * selectors, container functions), read off the preamble text so the
     * two cannot drift.
     */
    public static Set<String> preambleNames() {
        if (PREAMBLE_NAMES.isEmpty()) {
            List<String> lines = new ArrayList<String>(
                    VmTermLowering.preamble());
            lines.add(VmTermLowering.JAVA_INT_TO_STRING);
            lines.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            lines.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
            for (String line : lines) {
                for (String name : declaredIn(line)) PREAMBLE_NAMES.add(name);
            }
        }
        return PREAMBLE_NAMES;
    }

    private static final Set<String> PREAMBLE_NAMES =
            new LinkedHashSet<String>();

    /** The names one preamble line states: the head of every list in it. */
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
            // In a datatype every list head is a name; elsewhere only the
            // token after a declare-/define- keyword.
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

    /**
     * Every name the query's logic gives a meaning to, operators included:
     * in SMT-LIB {@code =} is a SYMBOL, and {@link #names} reads it as one.
     */
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
                    "java_int_to_string", "indexed_state_of",
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
                    // Every theory operator the lowering writes (SmtLowering,
                    // JavaPrimitiveSmtSemantics, ContainerSmtCodec): one
                    // missing here is read as a free symbol and refuses its
                    // path (solr-adhoc q13-22 dropped 36 conjuncts on
                    // str.substr and str.indexof).
                    "str.++", "str.len", "str.contains", "str.prefixof",
                    "str.suffixof", "str.from_int", "str.to_int", "str.substr",
                    "str.indexof", "str.at", "str.from_code", "str.to_code",
                    "str.in_re", "re.*", "re.range",
                    "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.neg",
                    "fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq",
                    "fp.isNaN", "fp.to_sbv", "to_fp", "int2bv", "bv2int")));

    /**
     * Every NAME one SMT term names: the one tokenizer, over
     * {@link #symbolCharacter}'s alphabet.  {@code "..."} names nothing,
     * {@code |...|} is ONE name, numerals and {@code #x}/{@code #b} literals
     * are values.
     */
    public static List<String> names(String text) {
        List<String> names = new ArrayList<String>();
        for (String token : tokens(text)) {
            if (name(token)) names.add(token);
        }
        return names;
    }

    /**
     * The names a {@code let} in this text BINDS, so a caller can exclude
     * them from "names nothing declares" (the associative size model emits
     * {@code let}).  Scope is ignored: over-reporting only withholds a
     * complaint.
     */
    public static Set<String> letBound(String text) {
        Set<String> bound = new LinkedHashSet<String>();
        if (text == null || !text.contains("(let ")) return bound;
        List<String> tokens = tokens(text);
        for (int at = 0; at < tokens.size(); at++) {
            if (!"let".equals(tokens.get(at))) continue;
            // (let  ((name term) (name term))  body
            //       ^ the binding list opens here
            int index = at + 1;
            if (index >= tokens.size() || !OPEN.equals(tokens.get(index))) {
                continue;
            }
            int depth = 0;
            for (; index < tokens.size(); index++) {
                String token = tokens.get(index);
                if (OPEN.equals(token)) {
                    depth++;
                    // Depth 2 is a binding pair, and its next token names it.
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

    /** The text's tokens and parentheses, in order. */
    private static List<String> tokens(String text) {
        List<String> tokens = new ArrayList<String>();
        pass(text, KEEP, tokens, Spelling.AS_WRITTEN);
        return tokens;
    }

    /**
     * How {@link #tokens} spells a parenthesis: no token contains a bar, so
     * neither equals a token, and {@link #name} reads neither as a name.
     */
    private static final String OPEN = "|(";
    private static final String CLOSE = "|)";

    /** The free names of a term: {@link #names} minus {@link #BUILTIN}. */
    public static Set<String> symbols(String text, Set<String> into) {
        for (String name : names(text)) {
            if (!BUILTIN.contains(name)) into.add(name);
        }
        return into;
    }

    /**
     * The text with the caller's renames applied (unrenamed tokens copied as
     * written), collecting into {@code unknown} every free name neither
     * builtin nor {@code stated}, so a query refuses itself rather than use
     * an undeclared constant.  A text with a {@code let} reports none.
     */
    public static String rename(String text, Map<String, String> renames,
                                Predicate<String> stated,
                                Set<String> unknown) {
        List<String> kept = new ArrayList<String>();
        String out = pass(text, renames::get, kept, Spelling.AS_WRITTEN);
        if (text != null && !text.contains("(let ")) {
            for (String name : kept) {
                if (!name(name) || BUILTIN.contains(name)) continue;
                if (stated != null && stated.test(name)) continue;
                unknown.add(name);
            }
        }
        return out.trim();
    }

    /**
     * The text with each name {@code renames} answers for replaced (null
     * keeps it), asked once per occurrence in text order.
     */
    public static String substitute(String text,
                                    Function<String, String> renames) {
        return pass(text, renames, null, Spelling.AS_WRITTEN);
    }

    /** Renames nothing. */
    private static final Function<String, String> KEEP = token -> null;

    /** How the one tokenizer spells the names it copies through. */
    private enum Spelling {
        /** Exactly as written, which is what a rename pass needs. */
        AS_WRITTEN,
        /** Bar-quoted where SMT-LIB cannot spell the name bare. */
        LEGAL
    }

    /**
     * THE tokenizer: the text copied with each name {@code renames} answers
     * for replaced.  {@code kept}, if not null, gets every token not
     * replaced and every parenthesis, in order.  String literals and
     * comments are copied whole.
     */
    private static String pass(String text, Function<String, String> renames,
                               List<String> kept, Spelling spelling) {
        StringBuilder out = new StringBuilder();
        if (text == null) return "";
        int index = 0;
        while (index < text.length()) {
            char value = text.charAt(index);
            if (value == '"') {
                int end = pastLiteral(text, index, '"');
                out.append(text, index, end);
                index = end;
                continue;
            }
            if (value == ';') {
                int end = text.indexOf('\n', index);
                end = end < 0 ? text.length() : end;
                out.append(text, index, end);
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
                out.append(value);
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
        return out.toString();
    }

    /**
     * One token: renamed, or copied exactly as it was spelled.
     *
     * @return the index past the token
     */
    private static int emit(StringBuilder out, String text, int start,
                            int end, String token,
                            Function<String, String> renames,
                            List<String> kept, Spelling spelling) {
        String renamed = name(token) ? renames.apply(token) : null;
        if (renamed != null) {
            out.append(renamed);
            return end;
        }
        append(out, text, start, end, token, spelling);
        if (kept != null) kept.add(token);
        return end;
    }

    private static void append(StringBuilder out, String text, int start,
                               int end, String token, Spelling spelling) {
        if (spelling == Spelling.LEGAL && !simpleSymbol(token)) {
            out.append('|').append(token).append('|');
            return;
        }
        out.append(text, start, end);
    }

    /** One index past the literal that opens at {@code at}. */
    private static int pastLiteral(String text, int at, char delimiter) {
        int index = at + 1;
        while (index < text.length() && text.charAt(index) != delimiter) {
            index++;
        }
        return index < text.length() ? index + 1 : index;
    }

    /**
     * Whether one token is a NAME, not a value: numerals and
     * {@code #x}/{@code #b} literals are values, though
     * {@link #symbolCharacter} admits {@code #}.  No token starts with a
     * bar, so {@link #OPEN} and {@link #CLOSE} are not names.
     */
    private static boolean name(String token) {
        if (token.isEmpty()) return false;
        char first = token.charAt(0);
        return !Character.isDigit(first) && first != '-' && first != '.'
                && first != '#' && first != '|';
    }

    /**
     * The preamble lines one query NEEDS: all but the {@code define-fun}s its
     * texts do not reach, transitively through definition bodies (as
     * {@link SmtLowering#reachedBy} does for declarations), and where it
     * reaches no reader of a map's order, the maps' definitions that keep no
     * order ({@link ContainerStateModel#unordered}).  Unused lambdas are not
     * neutral: they change the fragment z3 decides.  Sorts, datatypes and
     * {@code declare-fun}s always stay.
     */
    public static List<String> reachedPreamble(List<String> preamble,
                                               Iterable<String> texts) {
        Map<String, String> definition = new LinkedHashMap<String, String>();
        for (String line : preamble) {
            if (line == null || !line.startsWith("(define-fun")) continue;
            for (String name : declaredIn(line)) definition.put(name, line);
        }
        Set<String> reached = new LinkedHashSet<String>();
        boolean ordered = false;
        Deque<String> pending = new ArrayDeque<String>();
        if (texts != null) {
            for (String text : texts) {
                for (String token : names(text)) {
                    ordered |= ContainerStateModel.ORDER_READERS
                            .contains(token);
                    if (definition.containsKey(token)
                            && reached.add(token)) {
                        pending.push(token);
                    }
                }
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

    /**
     * The text with every name SMT-LIB cannot spell bare bar-quoted (a
     * runtime symbol like {@code MAP_STATE/4#-3@v112} would otherwise read
     * as a bit-vector literal).  A spelling, not a rename, so published
     * terms stay valid; idempotent.
     */
    public static String legalSymbols(String query) {
        if (query == null || query.isEmpty()) return query;
        return pass(query, KEEP, null, Spelling.LEGAL);
    }

    /** Whether SMT-LIB already spells this token the way it is written. */
    private static boolean simpleSymbol(String token) {
        if (token.isEmpty()) return true;
        char first = token.charAt(0);
        // A keyword, a numeral or a radix literal is not a symbol at all.
        if (first == ':' || first == '#' || Character.isDigit(first)) {
            return true;
        }
        for (int index = 0; index < token.length(); index++) {
            if (!simpleCharacter(token.charAt(index))) return false;
        }
        return true;
    }

    /** SMT-LIB's simple-symbol alphabet. */
    private static boolean simpleCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/".indexOf(value) >= 0;
    }
}
