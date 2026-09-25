package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/** Recorded value as a literal, and one unique variable name per quantity.
 *  Tokenizing and renaming live in the one tokenizer ({@code SmtLowering}): a
 *  second tokenizer would disagree on where a symbol ends. */
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

    static final class Names {
        private final Map<String, String> byKey =
                new LinkedHashMap<String, String>();
        private final Set<String> taken = new HashSet<String>();

        String name(String key, String preferred) {
            String existing = byKey.get(key);
            if (existing != null) return existing;
            // One sanitizer (smtName); the 48-char cap is for readability, the
            // suffix resolves collisions.
            String legal = edu.uva.liftlab.graphchecker.compose
                    .VmTermLowering.smtName(preferred);
            String base = legal.length() > 48 ? legal.substring(0, 48)
                    : legal;
            String candidate = base;
            int suffix = 2;
            while (!taken.add(candidate)) {
                candidate = base + "_" + suffix++;
            }
            byKey.put(key, candidate);
            return candidate;
        }
    }
}
