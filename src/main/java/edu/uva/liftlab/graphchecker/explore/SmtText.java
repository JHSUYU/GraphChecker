package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * The two things a flip query needs beyond the one lowering: a recorded
 * value as a literal, and one unique variable name per quantity.
 *
 * <p>Tokenizing, free names and renaming are NOT here: they are one pass of
 * the one tokenizer ({@code SmtLowering.names}, {@code symbols},
 * {@code rename}), because a name ends where SMT-LIB says it ends and a
 * second answer to that is a symbol one stage binds and the other reports
 * undeclared.</p>
 */
final class SmtText {
    private SmtText() {
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
