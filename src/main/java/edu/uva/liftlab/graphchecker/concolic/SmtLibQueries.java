package edu.uva.liftlab.graphchecker.concolic;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

    /** Folds constants in the one-command-per-line SMT emitted by Composer. */
    static String foldConstants(String input) {
        String source = input == null ? "" : input;
        StringBuilder result = new StringBuilder(source.length());
        String[] lines = source.split("\\r?\\n", -1);
        for (int index = 0; index < lines.length; index++) {
            String line = lines[index];
            String folded = line;
            if (line.contains("true") || line.contains("false")) {
                int[] cursor = {0};
                String candidate = term(line, cursor);
                while (cursor[0] < line.length()
                        && Character.isWhitespace(line.charAt(cursor[0]))) {
                    cursor[0]++;
                }
                if (candidate != null && cursor[0] == line.length()) {
                    folded = candidate;
                }
            }
            result.append(folded);
            if (index + 1 < lines.length) result.append(System.lineSeparator());
        }
        return result.toString();
    }

    private static String term(String source, int[] cursor) {
        while (cursor[0] < source.length()
                && Character.isWhitespace(source.charAt(cursor[0]))) {
            cursor[0]++;
        }
        if (cursor[0] >= source.length()) return "";
        int start = cursor[0];
        char first = source.charAt(cursor[0]++);
        if (first == '"' || first == '|') {
            while (cursor[0] < source.length()) {
                if (source.charAt(cursor[0]++) != first) continue;
                if (first == '"' && cursor[0] < source.length()
                        && source.charAt(cursor[0]) == '"') {
                    cursor[0]++;
                } else return source.substring(start, cursor[0]);
            }
            return null;
        }
        if (first != '(') {
            while (cursor[0] < source.length()
                    && !Character.isWhitespace(source.charAt(cursor[0]))
                    && source.charAt(cursor[0]) != '('
                    && source.charAt(cursor[0]) != ')') cursor[0]++;
            return source.substring(start, cursor[0]);
        }
        List<String> parts = new ArrayList<>();
        while (true) {
            while (cursor[0] < source.length()
                    && Character.isWhitespace(source.charAt(cursor[0]))) {
                cursor[0]++;
            }
            if (cursor[0] >= source.length()) return null;
            if (source.charAt(cursor[0]) == ')') {
                cursor[0]++;
                return fold(parts);
            }
            String part = term(source, cursor);
            if (part == null) return null;
            parts.add(part);
        }
    }

    private static String fold(List<String> parts) {
        if (parts.isEmpty()) return "()";
        String operator = parts.get(0);
        if ("ite".equals(operator) && parts.size() == 4) {
            if ("true".equals(parts.get(1))) return parts.get(2);
            if ("false".equals(parts.get(1))) return parts.get(3);
            if (parts.get(2).equals(parts.get(3))) return parts.get(2);
        }
        if (("and".equals(operator) || "or".equals(operator))
                && parts.size() > 1) {
            String absorbing = "and".equals(operator) ? "false" : "true";
            String identity = "and".equals(operator) ? "true" : "false";
            List<String> live = new ArrayList<>();
            live.add(operator);
            for (int index = 1; index < parts.size(); index++) {
                if (absorbing.equals(parts.get(index))) return absorbing;
                if (!identity.equals(parts.get(index))) live.add(parts.get(index));
            }
            if (live.size() == 1) return identity;
            if (live.size() == 2) return live.get(1);
            parts = live;
        } else if ("not".equals(operator) && parts.size() == 2) {
            if ("true".equals(parts.get(1))) return "false";
            if ("false".equals(parts.get(1))) return "true";
        } else if ("=>".equals(operator) && parts.size() == 3) {
            if ("false".equals(parts.get(1))
                    || "true".equals(parts.get(2))) return "true";
            if ("true".equals(parts.get(1))) return parts.get(2);
        }
        StringBuilder result = new StringBuilder("(");
        for (int index = 0; index < parts.size(); index++) {
            if (index > 0) result.append(' ');
            result.append(parts.get(index));
        }
        return result.append(')').toString();
    }

    /** Propagates unconditional comparisons into generated constants. */
    static String propagateAssertedComparisons(String input) {
        String source = input == null ? "" : input;
        String[] lines = source.split("\\r?\\n", -1);
        Set<String> truths = new LinkedHashSet<>();
        Set<String> falsehoods = new LinkedHashSet<>();
        for (String line : lines) {
            List<String> command = parts(line);
            if (command.size() != 2 || !"assert".equals(command.get(0))) {
                continue;
            }
            String body = command.get(1);
            List<String> annotation = parts(body);
            if (annotation.size() >= 2 && "!".equals(annotation.get(0))) {
                body = annotation.get(1);
            }
            collectComparisons(body, truths, falsehoods);
        }
        StringBuilder result = new StringBuilder(source.length());
        for (int index = 0; index < lines.length; index++) {
            String line = lines[index];
            List<String> definition = parts(line);
            if (definition.size() == 5
                    && "define-fun".equals(definition.get(0))
                    && "()".equals(definition.get(2))) {
                for (String truth : truths) line = line.replace(truth, "true");
                for (String falsehood : falsehoods) {
                    line = line.replace(falsehood, "false");
                }
                line = foldConstants(line);
            }
            result.append(line);
            if (index + 1 < lines.length) result.append(System.lineSeparator());
        }
        return result.toString();
    }

    private static void collectComparisons(String expression,
                                           Set<String> truths,
                                           Set<String> falsehoods) {
        List<String> values = parts(expression);
        if (!values.isEmpty() && "and".equals(values.get(0))) {
            for (int index = 1; index < values.size(); index++) {
                collectComparisons(values.get(index), truths, falsehoods);
            }
            return;
        }
        if (values.size() != 3) return;
        String opposite;
        if ("<".equals(values.get(0))) opposite = ">=";
        else if ("<=".equals(values.get(0))) opposite = ">";
        else if (">".equals(values.get(0))) opposite = "<=";
        else if (">=".equals(values.get(0))) opposite = "<";
        else return;
        truths.add(expression);
        falsehoods.add("(" + opposite + " " + values.get(1)
                + " " + values.get(2) + ")");
    }

    private static List<String> parts(String expression) {
        List<String> result = new ArrayList<>();
        int[] cursor = {0};
        while (cursor[0] < expression.length()
                && Character.isWhitespace(expression.charAt(cursor[0]))) {
            cursor[0]++;
        }
        if (cursor[0] >= expression.length()
                || expression.charAt(cursor[0]++) != '(') return result;
        while (cursor[0] < expression.length()) {
            while (cursor[0] < expression.length()
                    && Character.isWhitespace(expression.charAt(cursor[0]))) {
                cursor[0]++;
            }
            if (cursor[0] < expression.length()
                    && expression.charAt(cursor[0]) == ')') return result;
            String value = term(expression, cursor);
            if (value == null || value.isEmpty()) return new ArrayList<>();
            result.add(value);
        }
        return new ArrayList<>();
    }

    /** Drops generated {@code define-fun}s unreachable from solver commands. */
    static String dropUnusedDefinitions(String input) {
        String source = input == null ? "" : input;
        String[] lines = source.split("\\r?\\n", -1);
        Map<String, Integer> definitions = new LinkedHashMap<>();
        boolean[] defined = new boolean[lines.length];
        for (int index = 0; index < lines.length; index++) {
            String name = definitionName(lines[index]);
            if (!name.isEmpty()) {
                definitions.put(name, index);
                defined[index] = true;
            }
        }
        boolean[] live = new boolean[lines.length];
        for (Map.Entry<String, Integer> definition
                : definitions.entrySet()) {
            for (int index = 0; index < lines.length; index++) {
                if (!defined[index]
                        && references(lines[index], definition.getKey())) {
                    live[definition.getValue()] = true;
                    break;
                }
            }
        }
        boolean changed;
        do {
            changed = false;
            for (Map.Entry<String, Integer> dependency
                    : definitions.entrySet()) {
                if (live[dependency.getValue()]) continue;
                for (int index : definitions.values()) {
                    if (live[index] && references(lines[index],
                            dependency.getKey())) {
                        live[dependency.getValue()] = true;
                        changed = true;
                        break;
                    }
                }
            }
        } while (changed);
        StringBuilder result = new StringBuilder(source.length());
        for (int index = 0; index < lines.length; index++) {
            if (!defined[index] || live[index]) {
                result.append(lines[index]).append(System.lineSeparator());
            }
        }
        return result.toString();
    }

    private static String definitionName(String line) {
        String prefix = "(define-fun ";
        if (!line.startsWith(prefix)) return "";
        int end = line.indexOf(' ', prefix.length());
        return end < 0 ? "" : line.substring(prefix.length(), end);
    }

    private static boolean references(String line, String symbol) {
        for (int at = 0; (at = line.indexOf(symbol, at)) >= 0;
             at += symbol.length()) {
            int end = at + symbol.length();
            boolean left = at == 0 || line.charAt(at - 1) == '('
                    || Character.isWhitespace(line.charAt(at - 1));
            boolean right = end == line.length() || line.charAt(end) == ')'
                    || Character.isWhitespace(line.charAt(end));
            if (left && right) return true;
        }
        return false;
    }
}
