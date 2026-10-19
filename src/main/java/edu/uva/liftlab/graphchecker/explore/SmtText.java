package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

final class SmtText {
    private SmtText() {
    }

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
