package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering;

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

    /**
     * One recorded value as a literal of the query sort it is bound at (a
     * {@link VmTermLowering.Sort#smt} spelling), or "" when it is not one:
     * the composition's one literal rule ({@link VmTermLowering#smtLiteral}),
     * so a String's arrival is its JSON string literal's content quoted here
     * as there.
     */
    static String literal(String value, String sort) {
        for (VmTermLowering.Sort each : VmTermLowering.Sort.values()) {
            if (each.smt.equals(sort)) {
                return VmTermLowering.smtLiteral(value, each);
            }
        }
        return "";
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
