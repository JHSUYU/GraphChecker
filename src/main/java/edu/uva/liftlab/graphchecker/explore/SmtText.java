package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * The SMT-LIB text a flip query is assembled from: tokens, names, literals.
 *
 * <p>Decision predicates arrive already spelled in SMT-LIB over the symbols
 * the recording declared ({@code DecisionRow.term}), so exploration never
 * re-derives a predicate -- it renames.  A symbol is a session-local name;
 * the query's variable is not, because a root is one quantity across the
 * corpus and a handoff is one value per interaction.  Renaming is therefore
 * the only rewriting this stage does to a recorded term.</p>
 */
final class SmtText {
    /** The SMT-LIB vocabulary a recorded predicate may use. */
    private static final Set<String> KEYWORDS = new HashSet<String>(
            Arrays.asList("and", "or", "not", "xor", "=>", "=", "distinct",
                    "<", "<=", ">", ">=", "+", "-", "*", "/", "div", "mod",
                    "abs", "ite", "let", "true", "false", "select", "store",
                    "concat", "extract", "_", "as", "const", "Int", "Bool",
                    "Real", "to_int", "to_real", "is_int", "nullRef"));

    private SmtText() {
    }

    /** Whether one token is the query's own vocabulary rather than a symbol. */
    static boolean vocabulary(String token) {
        if (token.isEmpty() || KEYWORDS.contains(token)) return true;
        if (token.startsWith("#x") || token.startsWith("#b")) return true;
        if (token.startsWith("bv") || token.startsWith("|")
                || token.startsWith("\"")) {
            return true;
        }
        char first = token.charAt(0);
        if (first == '-' || first == '+' || Character.isDigit(first)) {
            try {
                new BigInteger(token.replace("+", ""));
                return true;
            } catch (NumberFormatException notANumeral) {
                return token.matches("[-+]?[0-9]+\\.[0-9]+");
            }
        }
        return false;
    }

    /**
     * The same, with the names the query's PREAMBLE already states.
     *
     * <p>A lowered term names two more kinds of thing than a recorded one:
     * the container model's own vocabulary, and the subterms and identities
     * the lowering minted.  The query renders both (it renders the
     * lowering's declarations), so neither is a free name -- but neither is
     * a recorded symbol either, and without this the one rule that catches
     * the propagation cut would fire on every one of them.</p>
     */
    static String rewrite(String term, Map<String, String> rename,
                          java.util.function.Predicate<String> stated,
                          Set<String> unknown) {
        StringBuilder out = new StringBuilder();
        StringBuilder token = new StringBuilder();
        boolean binds = term.contains("(let ");
        for (int index = 0; index <= term.length(); index++) {
            char at = index == term.length() ? ' ' : term.charAt(index);
            if (at == '(' || at == ')' || Character.isWhitespace(at)) {
                if (token.length() > 0) {
                    String text = token.toString();
                    String renamed = rename.get(text);
                    if (renamed != null) {
                        out.append(renamed);
                    } else {
                        if (!binds && !vocabulary(text)
                                && (stated == null || !stated.test(text))) {
                            unknown.add(text);
                        }
                        out.append(text);
                    }
                    token.setLength(0);
                }
                if (index < term.length()) out.append(at);
            } else {
                token.append(at);
            }
        }
        return out.toString().trim();
    }

    /** Every token of one term that is neither vocabulary nor renamed. */
    static Set<String> symbols(String term, Set<String> into) {
        StringBuilder token = new StringBuilder();
        for (int index = 0; index <= term.length(); index++) {
            char at = index == term.length() ? ' ' : term.charAt(index);
            if (at == '(' || at == ')' || Character.isWhitespace(at)) {
                if (token.length() > 0) {
                    String text = token.toString();
                    if (!vocabulary(text)) into.add(text);
                    token.setLength(0);
                }
            } else {
                token.append(at);
            }
        }
        return into;
    }

    /** One recorded value as a literal of one sort, or "" when it is not one. */
    static String literal(String value, String sort) {
        String text = value == null ? "" : value.trim();
        if (text.isEmpty()) return "";
        if ("Bool".equals(sort)) {
            if ("true".equalsIgnoreCase(text) || "1".equals(text)) {
                return "true";
            }
            if ("false".equalsIgnoreCase(text) || "0".equals(text)) {
                return "false";
            }
            return "";
        }
        return JavaPrimitiveSmtSemantics.integralLiteral(text);
    }

    /** Allocates one unique variable name per keyed quantity. */
    static final class Names {
        private final Map<String, String> byKey =
                new LinkedHashMap<String, String>();
        private final Set<String> taken = new HashSet<String>();

        String name(String key, String preferred) {
            String existing = byKey.get(key);
            if (existing != null) return existing;
            String base = sanitize(preferred);
            String candidate = base;
            int suffix = 2;
            while (!taken.add(candidate)) {
                candidate = base + "_" + suffix++;
            }
            byKey.put(key, candidate);
            return candidate;
        }

        private static String sanitize(String text) {
            StringBuilder clean = new StringBuilder();
            for (int index = 0; index < text.length()
                    && clean.length() < 48; index++) {
                char at = text.charAt(index);
                clean.append(Character.isLetterOrDigit(at) || at == '_'
                        ? at : '_');
            }
            if (clean.length() == 0) clean.append('v');
            if (Character.isDigit(clean.charAt(0))) clean.insert(0, 'v');
            return clean.toString();
        }
    }
}
