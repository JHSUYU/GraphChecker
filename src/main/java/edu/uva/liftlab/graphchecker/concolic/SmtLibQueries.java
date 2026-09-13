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
