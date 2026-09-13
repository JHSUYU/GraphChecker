package edu.uva.liftlab.graphchecker.concolic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;

/** Shared transformations for building solver queries from emitted SMT-LIB. */
final class SmtLibQueries {
    private SmtLibQueries() {
    }

    /**
     * Exactly one of {@code selectors}, wherever {@code activation} holds.
     *
     * <p>A partition that is only in force under a guard: where the guard is
     * false the choice is not made at all, which is how "this occurrence did
     * not run" stays expressible.</p>
     */
    static String conditionalExactlyOne(String activation,
                                        Collection<String> selectors) {
        List<String> ordered = new ArrayList<>(selectors);
        Collections.sort(ordered);
        if (ordered.isEmpty()) {
            throw new IllegalArgumentException(
                    "an active guarded choice needs a candidate");
        }
        StringBuilder count = new StringBuilder("(= (+");
        for (String selector : ordered) {
            count.append(" (ite ").append(selector).append(" 1 0)");
        }
        count.append(") 1)");
        return "(=> " + firstNonBlank(activation, "true") + " "
                + count + ")";
    }

    static String stripSolverCommands(String input) {
        StringBuilder result = new StringBuilder();
        String[] lines = (input == null ? "" : input)
                .split("\\r?\\n", -1);
        for (String line : lines) {
            String trimmed = line.trim();
            if (trimmed.startsWith("(check-sat")
                    || trimmed.startsWith("(get-model")
                    || trimmed.startsWith("(get-value")
                    || trimmed.startsWith("(get-unsat-core")
                    || trimmed.startsWith("(exit")) {
                continue;
            }
            result.append(line).append(System.lineSeparator());
        }
        return result.toString();
    }
}
