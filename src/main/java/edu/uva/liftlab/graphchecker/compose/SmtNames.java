package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.ArrayList;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

/**
 * THE ONE TOKENIZER over SMT-LIB text, and the vocabulary it reads with.
 *
 * <p>Relocated out of {@link SmtLowering} unchanged: the same bodies, the
 * same order, no rule altered.  Nothing here holds any state of a lowering
 * -- every member is static and every answer is a function of the text and
 * the theory's own names -- which is why it can stand apart from the class
 * that owns the sessions, the declarations and the assertions.</p>
 *
 * <p>ONE vocabulary and ONE pass, for every stage: {@link #BUILTIN} is what
 * the theory states, {@link #names} is how a term is broken into tokens,
 * {@link #symbols} is the free names of it, {@link #rename} is the same
 * pass with a caller's variables substituted, and {@link #reachedPreamble}
 * is which lines of a fixed preamble a query's own texts reach.  Two
 * vocabularies over one query text is a name one stage calls a theory
 * operator and the other calls undeclared, which is the defect this file
 * exists to make impossible.</p>
 *
 * <p>{@link SmtLowering} keeps a delegator for each member its callers name,
 * so nothing outside this package had to change.</p>
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

    /** Whether one symbol occurs in a term as a symbol, not a substring. */
    public static boolean mentions(String term, String symbol) {
        if (term == null || symbol == null || symbol.isEmpty()) return false;
        int at = term.indexOf(symbol);
        while (at >= 0) {
            boolean before = at == 0
                    || !symbolCharacter(term.charAt(at - 1));
            int end = at + symbol.length();
            boolean after = end >= term.length()
                    || !symbolCharacter(term.charAt(end));
            if (before && after) return true;
            at = term.indexOf(symbol, at + 1);
        }
        return false;
    }

    /**
     * A character a NAME may be spelled with.
     *
     * <p>SMT-LIB's simple-symbol alphabet, plus the two the runtime's own
     * names use: {@code #} in a row's location symbol, {@code '} in the
     * VM's.  The set was letters, digits, {@code _ . $} -- which splits
     * {@code M_I_field_HOFF.…_edu/uva/liftlab/…} at the slash, so half a
     * name was looked up, no declaration was found for it, and a query
     * emitted a subterm over a constant it never declared.</p>
     */
    public static boolean symbolCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/#'".indexOf(value) >= 0;
    }

    /**
     * Every name the fixed preamble gives a meaning to.
     *
     * <p>Sorts, datatype constructors and selectors, and the functions the
     * container model is written in.  A caller that renders the preamble
     * states these; one that reads a lowered term must not call them free.
     * Read off the preamble text so the two cannot drift apart.</p>
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
            // Outside a datatype only a declaration states a name, and it is
            // the token after the keyword; inside one, every list opens with
            // a sort, a constructor or a selector.
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
     * Every name the query's own logic gives a meaning to.
     *
     * <p>The operators belong here for the same reason the datatype
     * selectors do: in SMT-LIB {@code =} and {@code <=} are SYMBOLS, and
     * {@link #names} reads them as such, so a caller asking "which names
     * does nothing declare" must be told that the theory declares these.
     * Left out, the check reported {@code =} as a free symbol of every term
     * it read.</p>
     *
     * <p>One set, for both stages: it was the composer's private BUILTIN and
     * the flip query's own KEYWORDS, and the two differed -- the flip
     * query's was missing every datatype selector and every bit-vector
     * operator the composer lists, and the composer's was missing
     * {@code is_int} beside the {@code to_int} and {@code to_real} it
     * already had.  Two vocabularies over one query text is a name one
     * stage calls a theory operator and the other calls undeclared.</p>
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
                    "Real", "String", "Ref", "Value", "AssocState",
                    "IndexedState", "FloatingPoint", "RoundingMode",
                    "roundNearestTiesToEven", "RNE", "RTZ", "RTP", "RTN",
                    "RNA", "nullRef", "java_int_wrap", "java_long_wrap",
                    "java_int_to_string", "indexed_state_of",
                    "assoc_state_of", "indexed_read", "indexed_write",
                    "indexed_append", "indexed_insert", "indexed_remove",
                    "indexed_contains", "indexed_size", "indexed_elements",
                    "assoc_has", "assoc_read", "assoc_key_at",
                    "assoc_value_at", "assoc_put", "assoc_remove",
                    "assoc_size", "assoc_present", "assoc_values",
                    "assoc_order", "assoc_position", "VByte", "VChar",
                    "VShort", "VInt", "VLong", "VFloat", "VDouble", "VBool",
                    "VRef", "VString", "valueByte", "valueChar", "valueShort",
                    "valueInt", "valueLong", "valueFloat", "valueDouble",
                    "valueBool", "valueRef", "valueString", "str", "fp",
                    "to_real", "to_int", "is_int", "divisible",
                    // The string-theory names THIS lowering writes, and no
                    // others: VmLoweringCore writes str.len, str.contains,
                    // str.prefixof, str.suffixof and str.++, and
                    // VmTermLowering's java_int_to_string writes str.++ and
                    // str.from_int.  A name the engine emits and this set
                    // does not hold is read as a free symbol and refuses
                    // the path that carries it -- which is what dropped
                    // hdfs-17960's third path the moment P3 conjoined the
                    // prefix of a writer occurrence whose branch compares
                    // two snapshot names ("join-pi renameSnapshot#u19#1
                    // names symbols nothing declares: [str.++]").
                    "str.++", "str.len", "str.contains", "str.prefixof",
                    "str.suffixof", "str.from_int")));

    /**
     * Every NAME one SMT term names: the one tokenizer.
     *
     * <p>The alphabet is {@link #symbolCharacter}'s, which is SMT-LIB's, so
     * {@code /} and {@code #} are parts of a name and not breaks in it.  A
     * second tokenizer that stopped at {@code /} cut
     * {@code M_I_field_REGION...._java/util/concurrent/atomic/AtomicInteger}
     * into five pieces and reported all five as symbols nothing declares --
     * the same one-rule-two-implementations defect as the two declaration
     * maps, in the same path.  Text inside {@code "..."} is a literal and
     * names nothing; text inside {@code |...|} is ONE name, however it is
     * spelled; a numeral is a value and not a name, and neither is a
     * {@code #x}/{@code #b} literal.</p>
     */
    public static List<String> names(String text) {
        List<String> names = new ArrayList<String>();
        pass(text, Collections.<String, String>emptyMap(), names);
        return names;
    }

    /**
     * The names a {@code let} in this text BINDS.
     *
     * <p>A bound name is not free, so a pass that reports "nothing declares
     * this" must not report one.  {@link #rename} already knows that and
     * declines to report anything at all once it sees a {@code let}; this
     * is the same fact, stated precisely enough that a caller can keep
     * reporting the names a {@code let} did NOT bind.
     *
     * <p>hdfs-11741 campaign #6: the associative size model emits {@code
     * (let ((previous_size ...)) (ite ... previous_size (- previous_size
     * 1)))} for the map a key was removed from, and {@code Composer#unknown}
     * -- which tokenizes without this -- refused every path that reached the
     * anchor with "this term names symbols nothing declares:
     * [previous_size, previous_size, previous_size]".
     *
     * <p>The shape is SMT-LIB's: {@code (let ((name term)+) body)}. Only the
     * first token of each binding pair is a name; everything in the pair's
     * term, and the body, is ordinary text this walks past. Nesting is
     * handled by depth, and a name bound in one {@code let} is reported for
     * the whole text rather than for its scope alone -- deliberately, since
     * the caller's question is "is this token a binder's name somewhere in
     * this term", and answering it too generously only ever withholds a
     * complaint.</p>
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
            if (index >= tokens.size() || !"(".equals(tokens.get(index))) {
                continue;
            }
            int depth = 0;
            for (; index < tokens.size(); index++) {
                String token = tokens.get(index);
                if ("(".equals(token)) {
                    depth++;
                    // Depth 2 is a binding pair, and its next token names it.
                    if (depth == 2 && index + 1 < tokens.size()) {
                        String name = tokens.get(index + 1);
                        if (name(name) && !"(".equals(name)
                                && !")".equals(name)) {
                            bound.add(name);
                        }
                    }
                    continue;
                }
                if (")".equals(token)) {
                    depth--;
                    if (depth <= 0) break;
                }
            }
        }
        return bound;
    }

    /** The text as parentheses and names, in order. */
    private static List<String> tokens(String text) {
        List<String> tokens = new ArrayList<String>();
        int index = 0;
        while (index < text.length()) {
            char value = text.charAt(index);
            if (value == '"' || value == '|') {
                int end = pastLiteral(text, index, value);
                tokens.add(text.substring(index, end));
                index = end;
                continue;
            }
            if (value == ';') {
                int end = text.indexOf('\n', index);
                index = end < 0 ? text.length() : end;
                continue;
            }
            if (value == '(' || value == ')') {
                tokens.add(String.valueOf(value));
                index++;
                continue;
            }
            if (Character.isWhitespace(value)) {
                index++;
                continue;
            }
            int start = index;
            while (index < text.length()
                    && !Character.isWhitespace(text.charAt(index))
                    && text.charAt(index) != '(' && text.charAt(index) != ')'
                    && text.charAt(index) != '"' && text.charAt(index) != ';') {
                index++;
            }
            tokens.add(text.substring(start, index));
        }
        return tokens;
    }

    /**
     * The same names, minus the ones the theory declares.
     *
     * <p>What a caller means by "the symbols of this term": the free names,
     * which it then asks the corpus about.  One tokenizer, one vocabulary --
     * the flip query and the closure planner each had their own pair.</p>
     */
    public static Set<String> symbols(String text, Set<String> into) {
        for (String name : names(text)) {
            if (!BUILTIN.contains(name)) into.add(name);
        }
        return into;
    }

    /**
     * The same text with the caller's renames applied, and every name it
     * left free that nothing states.
     *
     * <p>A recorded predicate arrives already spelled in SMT-LIB over the
     * symbols the recording declared, so a stage that needs it over its own
     * variables RENAMES -- it never re-derives the predicate.  Renaming is
     * therefore one pass of the one tokenizer, and a token the renames do
     * not name is copied through exactly as it was written, bars and all.</p>
     *
     * <p>{@code unknown} collects the free names that are neither theory
     * vocabulary nor stated by {@code stated}; that is what makes a query
     * refuse itself rather than emit a formula over a constant nothing
     * declares.  A term that BINDS names of its own ({@code let}) reports
     * none of them, because a bound name is not free and the pass does not
     * track scopes.</p>
     */
    public static String rename(String text, Map<String, String> renames,
                                Predicate<String> stated,
                                Set<String> unknown) {
        Set<String> named = new LinkedHashSet<String>();
        String out = pass(text, renames, named);
        if (text != null && !text.contains("(let ")) {
            for (String name : named) {
                if (BUILTIN.contains(name)) continue;
                if (stated != null && stated.test(name)) continue;
                unknown.add(name);
            }
        }
        return out.trim();
    }

    /** How the one tokenizer spells the names it copies through. */
    private enum Spelling {
        /** Exactly as written, which is what a rename pass needs. */
        AS_WRITTEN,
        /**
         * Bar-quoted where SMT-LIB cannot spell the name bare.
         *
         * <p>A row's symbol is a NAME the runtime chose --
         * {@code MAP_STATE/4#-3@v112} -- and {@code #} is not in SMT-LIB's
         * simple-symbol alphabet: it opens a bit-vector literal, so z3
         * answers the whole query with "invalid bit-vector literal" and the
         * composition has no verdict at all.  {@code |...|} is the SAME
         * symbol spelled legally, which is why the fix is a spelling and
         * not a rename: renaming would need every published term rewritten
         * in step, and a term the runtime wrote about {@code x} must stay
         * about {@code x}.  Idempotent, because an already-quoted name is
         * one token here and is copied through.</p>
         */
        LEGAL
    }

    private static String pass(String text, Map<String, String> renames,
                               Collection<String> named) {
        return pass(text, renames, named, Spelling.AS_WRITTEN);
    }

    private static String pass(String text, Map<String, String> renames,
                               Collection<String> named, Spelling spelling) {
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
                // A comment runs to the end of the line and names nothing.
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
                index = emit(out, text, index, end, token, renames, named,
                        Spelling.AS_WRITTEN);
                continue;
            }
            if (!symbolCharacter(value)) {
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
                    renames, named, spelling);
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
                            Map<String, String> renames,
                            Collection<String> named, Spelling spelling) {
        if (!name(token)) {
            append(out, text, start, end, token, spelling);
            return end;
        }
        String renamed = renames.get(token);
        if (renamed != null) {
            out.append(renamed);
            return end;
        }
        append(out, text, start, end, token, spelling);
        named.add(token);
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
     * Whether one token is a NAME and not a value.
     *
     * <p>A numeral is a value; so is {@code #x1f} and {@code #b01}, which
     * SMT-LIB spells with a {@code #} that {@link #symbolCharacter} admits
     * because the runtime's own location symbols use one.  Reporting a
     * hexadecimal literal as a free name is how a float in a lowered term
     * became "this term names symbols nothing declares".</p>
     */
    private static boolean name(String token) {
        if (token.isEmpty()) return false;
        char first = token.charAt(0);
        return !Character.isDigit(first) && first != '-' && first != '.'
                && first != '#';
    }

    /**
     * The preamble lines one query NEEDS: every line but a {@code
     * define-fun} nothing in it reaches.
     *
     * <p>A preamble is fixed and a query is not.  Stating the whole
     * container model in every query put the associative model -- five
     * array fields, {@code assoc_put}'s five stores and {@code
     * assoc_remove}'s two lambdas -- into 17960's queries, which name no
     * associative term at all, and the indexed model into 11741's, which
     * name no indexed term at all.  Those are not neutral: a lambda and a
     * datatype the query never applies still put the goal in a fragment
     * z3 decides differently, and a reader of a published query cannot
     * tell a definition the formula rests on from one it does not.</p>
     *
     * <p>Only a {@code define-fun} is dropped.  A sort, a datatype and a
     * {@code declare-fun} are what the query's own SORTS are written in,
     * so dropping one would change what its declarations mean; a
     * definition is reached or it is inert.  Reachability is transitive
     * through definition bodies -- {@code assoc_put} names {@code
     * assoc_has} -- and it is the same notion {@link SmtLowering#reachedBy} applies
     * to declarations, over the same tokenizer ({@link #names}).</p>
     */
    public static List<String> reachedPreamble(List<String> preamble,
                                               Iterable<String> texts) {
        Map<String, String> definition = new LinkedHashMap<String, String>();
        for (String line : preamble) {
            if (line == null || !line.startsWith("(define-fun")) continue;
            for (String name : declaredIn(line)) definition.put(name, line);
        }
        Set<String> reached = new LinkedHashSet<String>();
        Deque<String> pending = new ArrayDeque<String>();
        if (texts != null) {
            for (String text : texts) {
                for (String token : names(text)) {
                    if (definition.containsKey(token)
                            && reached.add(token)) {
                        pending.push(token);
                    }
                }
            }
        }
        while (!pending.isEmpty()) {
            for (String token : names(definition.get(pending.pop()))) {
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
                    lines.add(line);
                    break;
                }
            }
        }
        return lines;
    }

    /**
     * The same text, with every name SMT-LIB cannot spell bare quoted.
     *
     * <p>A row's symbol is a NAME the runtime chose --
     * {@code MAP_STATE/4#-3@v112} -- and {@code #} is not in SMT-LIB's
     * simple-symbol alphabet: it opens a bit-vector literal, so z3 answers
     * the whole query with "invalid bit-vector literal" and the
     * composition has no verdict at all.  {@code |...|} is the SAME symbol
     * spelled legally, which is why the fix is a spelling and not a
     * rename: renaming would need every published term rewritten in step,
     * and a term the runtime wrote about {@code x} must stay about
     * {@code x}.</p>
     *
     * <p>Idempotent: an already-quoted name is copied through, so a body
     * that passes here twice is the text it was.</p>
     */
    public static String legalSymbols(String query) {
        if (query == null || query.isEmpty()) return query;
        return pass(query, Collections.<String, String>emptyMap(),
                new ArrayList<String>(), Spelling.LEGAL);
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

    /** Copies one string or one already-quoted symbol, closing mark and
     *  all. */
    private static boolean simpleCharacter(char value) {
        if (Character.isLetterOrDigit(value)) return true;
        return "~!@$%^&*_-+=<>.?/".indexOf(value) >= 0;
    }
}
