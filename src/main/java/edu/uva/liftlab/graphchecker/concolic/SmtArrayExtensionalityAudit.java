package edu.uva.liftlab.graphchecker.concolic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Proves the narrow SMT fragment in which array extensionality is redundant
 * for satisfiability.
 *
 * <p>The weak and extensional array theories are equisatisfiable when arrays
 * are never required to be different and are not passed to an uninterpreted
 * observer: a weak model can be quotiented by element-wise equality.  The
 * audit is deliberately conservative.  A parse error, an unknown operand
 * sort at a negative equality, an array-valued quantified variable, or an
 * uninterpreted observer makes it fail closed.</p>
 */
final class SmtArrayExtensionalityAudit {
    private SmtArrayExtensionalityAudit() {
    }

    static boolean provesExtensionalityRedundant(String smt) {
        try {
            List<Node> forms = new Parser(smt).parse();
            Analyzer analyzer = new Analyzer(forms);
            return analyzer.hasArraySort && analyzer.safe();
        } catch (RuntimeException malformedOrUnknown) {
            return false;
        }
    }

    private enum Polarity {
        POSITIVE, NEGATIVE, BOTH;

        private Polarity flipped() {
            if (this == POSITIVE) return NEGATIVE;
            if (this == NEGATIVE) return POSITIVE;
            return BOTH;
        }
    }

    private static final class Type {
        private static final Type UNKNOWN = new Type(false, false, null);
        private static final Type SCALAR = new Type(true, false, null);
        private static final Type BOOL = new Type(true, false, null);
        private final boolean known;
        private final boolean arrayBearing;
        private final Type element;

        private Type(boolean known, boolean arrayBearing, Type element) {
            this.known = known;
            this.arrayBearing = arrayBearing;
            this.element = element;
        }

        private static Type array(Type element) {
            return new Type(true, true, element);
        }
    }

    private static final class Function {
        private final Type result;
        private final boolean interpreted;

        private Function(Type result, boolean interpreted) {
            this.result = result;
            this.interpreted = interpreted;
        }
    }

    private static final class Analyzer {
        private final List<Node> forms;
        private final Map<String, Type> sorts = new HashMap<>();
        private final Map<String, Function> functions = new HashMap<>();
        private boolean hasArraySort;

        private Analyzer(List<Node> forms) {
            this.forms = forms;
            sorts.put("Bool", Type.BOOL);
            sorts.put("Int", Type.SCALAR);
            sorts.put("Real", Type.SCALAR);
            sorts.put("String", Type.SCALAR);
            collectDeclarations();
        }

        private boolean safe() {
            Map<String, Node> definitions = new HashMap<>();
            for (Node form : forms) {
                if (form.isList() && form.children.size() >= 5
                        && "define-fun".equals(form.children.get(0).atom)) {
                    definitions.put(form.children.get(1).atom, form);
                }
            }
            Map<String, Node> reachableDefinitions = new HashMap<>();
            for (Node form : forms) {
                if (form.isList() && form.children.size() == 2
                        && "assert".equals(form.children.get(0).atom)) {
                    collectCalledDefinitions(form.children.get(1), definitions,
                            reachableDefinitions);
                }
            }
            int previousSize = -1;
            while (previousSize != reachableDefinitions.size()) {
                previousSize = reachableDefinitions.size();
                for (Node definition : new ArrayList<>(
                        reachableDefinitions.values())) {
                    collectCalledDefinitions(definition.children.get(4),
                            definitions, reachableDefinitions);
                }
            }
            for (Node form : forms) {
                if (!form.isList() || form.children.isEmpty()) continue;
                String command = form.children.get(0).atom;
                if ("assert".equals(command) && form.children.size() == 2) {
                    if (!safeFormula(form.children.get(1),
                            Polarity.POSITIVE, Collections.<String, Type>emptyMap())) {
                        return false;
                    }
                } else if ("define-fun".equals(command)
                        && form.children.size() >= 5
                        && reachableDefinitions.containsKey(
                        form.children.get(1).atom)) {
                    Map<String, Type> locals = parameters(form.children.get(2));
                    // A definition is a macro and may be called at either
                    // polarity.  BOTH is conservative and keeps the audit
                    // independent of call-site expansion.
                    if (!safeFormula(form.children.get(4), Polarity.BOTH,
                            locals)) {
                        return false;
                    }
                }
            }
            return true;
        }

        private void collectCalledDefinitions(Node expression,
                                              Map<String, Node> definitions,
                                              Map<String, Node> result) {
            if (!expression.isList()) {
                Node definition = definitions.get(expression.atom);
                if (definition != null
                        && definition.children.get(2).isList()
                        && definition.children.get(2).children.isEmpty()) {
                    result.put(expression.atom, definition);
                }
                return;
            }
            if (!expression.children.isEmpty()) {
                String head = expression.children.get(0).atom;
                Node definition = definitions.get(head);
                if (definition != null) result.put(head, definition);
            }
            for (Node child : expression.children) {
                collectCalledDefinitions(child, definitions, result);
            }
        }

        private void collectDeclarations() {
            for (Node form : forms) {
                if (!form.isList() || form.children.isEmpty()) continue;
                String command = form.children.get(0).atom;
                if ("declare-sort".equals(command)
                        && form.children.size() >= 2) {
                    sorts.put(form.children.get(1).atom, Type.SCALAR);
                } else if ("declare-datatypes".equals(command)) {
                    collectDatatypes(form);
                }
            }
            for (Node form : forms) {
                if (!form.isList() || form.children.isEmpty()) continue;
                String command = form.children.get(0).atom;
                if ("declare-const".equals(command)
                        && form.children.size() == 3) {
                    functions.put(form.children.get(1).atom,
                            new Function(type(form.children.get(2)), true));
                } else if ("declare-fun".equals(command)
                        && form.children.size() == 4) {
                    functions.put(form.children.get(1).atom,
                            new Function(type(form.children.get(3)), false));
                } else if ("define-fun".equals(command)
                        && form.children.size() >= 4) {
                    functions.put(form.children.get(1).atom,
                            new Function(type(form.children.get(3)), true));
                }
            }
        }

        private void collectDatatypes(Node declaration) {
            if (declaration.children.size() < 3
                    || !declaration.children.get(2).isList()) return;
            List<Node> definitions = declaration.children.get(2).children;
            for (Node definition : definitions) {
                if (!definition.isList() || definition.children.isEmpty()) {
                    continue;
                }
                sorts.put(definition.children.get(0).atom, Type.SCALAR);
            }
            // The generated datatypes are non-recursive.  A small fixpoint
            // also handles a datatype containing another declared datatype.
            for (int pass = 0; pass <= definitions.size(); pass++) {
                for (Node definition : definitions) {
                    if (!definition.isList()
                            || definition.children.isEmpty()) continue;
                    boolean bearing = false;
                    for (int index = 1; index < definition.children.size(); index++) {
                        Node constructor = definition.children.get(index);
                        if (!constructor.isList()) continue;
                        for (int field = 1; field < constructor.children.size(); field++) {
                            Node accessor = constructor.children.get(field);
                            if (accessor.isList() && accessor.children.size() == 2
                                    && type(accessor.children.get(1)).arrayBearing) {
                                bearing = true;
                            }
                        }
                    }
                    if (bearing) {
                        sorts.put(definition.children.get(0).atom,
                                new Type(true, true, null));
                        hasArraySort = true;
                    }
                }
            }
            for (Node definition : definitions) {
                if (!definition.isList() || definition.children.isEmpty()) {
                    continue;
                }
                Type result = type(definition.children.get(0));
                for (int index = 1; index < definition.children.size(); index++) {
                    Node constructor = definition.children.get(index);
                    if (!constructor.isList() || constructor.children.isEmpty()) {
                        continue;
                    }
                    functions.put(constructor.children.get(0).atom,
                            new Function(result, true));
                    for (int field = 1; field < constructor.children.size(); field++) {
                        Node accessor = constructor.children.get(field);
                        if (accessor.isList() && accessor.children.size() == 2) {
                            functions.put(accessor.children.get(0).atom,
                                    new Function(type(accessor.children.get(1)), true));
                        }
                    }
                }
            }
        }

        private Type type(Node sort) {
            if (sort == null) return Type.UNKNOWN;
            if (!sort.isList()) {
                Type known = sorts.get(sort.atom);
                return known == null ? Type.UNKNOWN : known;
            }
            if (sort.children.size() >= 3
                    && "Array".equals(sort.children.get(0).atom)) {
                hasArraySort = true;
                return Type.array(type(sort.children.get(2)));
            }
            // FloatingPoint and parameterized scalar sorts are not arrays.
            return sort.children.isEmpty() ? Type.UNKNOWN : Type.SCALAR;
        }

        private Map<String, Type> parameters(Node list) {
            Map<String, Type> result = new HashMap<>();
            if (!list.isList()) return result;
            for (Node entry : list.children) {
                if (entry.isList() && entry.children.size() == 2) {
                    result.put(entry.children.get(0).atom,
                            type(entry.children.get(1)));
                }
            }
            return result;
        }

        private boolean safeFormula(Node expression, Polarity polarity,
                                    Map<String, Type> locals) {
            if (!expression.isList() || expression.children.isEmpty()) {
                return true;
            }
            String head = expression.children.get(0).atom;
            if ("!".equals(head)) {
                return expression.children.size() >= 2
                        && safeFormula(expression.children.get(1), polarity,
                        locals);
            }
            if ("not".equals(head)) {
                return expression.children.size() == 2
                        && safeFormula(expression.children.get(1),
                        polarity.flipped(), locals);
            }
            if ("=>".equals(head)) {
                if (expression.children.size() < 3) return false;
                for (int index = 1; index + 1 < expression.children.size(); index++) {
                    if (!safeFormula(expression.children.get(index),
                            polarity.flipped(), locals)) return false;
                }
                return safeFormula(expression.children.get(
                        expression.children.size() - 1), polarity, locals);
            }
            if ("and".equals(head) || "or".equals(head)) {
                for (int index = 1; index < expression.children.size(); index++) {
                    if (!safeFormula(expression.children.get(index), polarity,
                            locals)) return false;
                }
                return true;
            }
            if ("=".equals(head)) {
                boolean boolEquality = true;
                for (int index = 1; index < expression.children.size(); index++) {
                    Type operand = termType(expression.children.get(index), locals);
                    if (operand.arrayBearing && polarity != Polarity.POSITIVE) {
                        return false;
                    }
                    if (!operand.known && polarity != Polarity.POSITIVE) {
                        return false;
                    }
                    boolEquality &= operand == Type.BOOL;
                }
                if (boolEquality) {
                    for (int index = 1; index < expression.children.size(); index++) {
                        if (!safeFormula(expression.children.get(index),
                                Polarity.BOTH, locals)) return false;
                    }
                }
                return safeTerms(expression, locals);
            }
            if ("distinct".equals(head)) {
                for (int index = 1; index < expression.children.size(); index++) {
                    Type operand = termType(expression.children.get(index), locals);
                    if (!operand.known || operand.arrayBearing) return false;
                }
                return safeTerms(expression, locals);
            }
            if ("ite".equals(head) && expression.children.size() == 4) {
                return safeFormula(expression.children.get(1), Polarity.BOTH,
                        locals)
                        && safeFormula(expression.children.get(2), polarity,
                        locals)
                        && safeFormula(expression.children.get(3), polarity,
                        locals);
            }
            if ("forall".equals(head) || "exists".equals(head)
                    || "lambda".equals(head)) {
                if (expression.children.size() != 3) return false;
                Map<String, Type> nested = new HashMap<>(locals);
                Map<String, Type> boundVariables = parameters(
                        expression.children.get(1));
                for (Type bound : boundVariables.values()) {
                    if (bound.arrayBearing) return false;
                }
                nested.putAll(boundVariables);
                return safeFormula(expression.children.get(2), polarity,
                        nested);
            }
            return safeTerms(expression, locals);
        }

        private boolean safeTerms(Node expression, Map<String, Type> locals) {
            Function function = expression.children.isEmpty() ? null
                    : functions.get(expression.children.get(0).atom);
            for (int index = 1; index < expression.children.size(); index++) {
                Node argument = expression.children.get(index);
                Type argumentType = termType(argument, locals);
                if (function != null && !function.interpreted
                        && argumentType.arrayBearing) {
                    return false;
                }
                if (argument.isList() && !argument.children.isEmpty()) {
                    String head = argument.children.get(0).atom;
                    if (argumentType == Type.BOOL || "ite".equals(head)
                            || "let".equals(head) || "lambda".equals(head)
                            || "forall".equals(head) || "exists".equals(head)) {
                        if (!safeFormula(argument, Polarity.BOTH, locals)) {
                            return false;
                        }
                    } else if (!safeTerms(argument, locals)) {
                        return false;
                    }
                }
            }
            return true;
        }

        private Type termType(Node term, Map<String, Type> locals) {
            if (!term.isList()) {
                Type local = locals.get(term.atom);
                if (local != null) return local;
                Function symbol = functions.get(term.atom);
                if (symbol != null) return symbol.result;
                if ("true".equals(term.atom) || "false".equals(term.atom)) {
                    return Type.BOOL;
                }
                if (term.atom.matches("[-+]?[0-9]+(\\.[0-9]+)?")) {
                    return Type.SCALAR;
                }
                return Type.UNKNOWN;
            }
            if (term.children.isEmpty()) return Type.UNKNOWN;
            String head = term.children.get(0).atom;
            if ("select".equals(head) && term.children.size() >= 2) {
                Type array = termType(term.children.get(1), locals);
                return array.element == null ? Type.UNKNOWN : array.element;
            }
            if ("store".equals(head) && term.children.size() >= 2) {
                return termType(term.children.get(1), locals);
            }
            if ("ite".equals(head) && term.children.size() == 4) {
                Type left = termType(term.children.get(2), locals);
                Type right = termType(term.children.get(3), locals);
                if (left == right) return left;
                if (left.known && right.known
                        && left.arrayBearing == right.arrayBearing) return left;
                return Type.UNKNOWN;
            }
            if ("let".equals(head) && term.children.size() == 3
                    && term.children.get(1).isList()) {
                Map<String, Type> nested = new HashMap<>(locals);
                for (Node binding : term.children.get(1).children) {
                    if (binding.isList() && binding.children.size() == 2) {
                        nested.put(binding.children.get(0).atom,
                                termType(binding.children.get(1), locals));
                    }
                }
                return termType(term.children.get(2), nested);
            }
            if ("lambda".equals(head)) return Type.array(Type.UNKNOWN);
            if ("=".equals(head) || "distinct".equals(head)
                    || "not".equals(head) || "and".equals(head)
                    || "or".equals(head) || "=>".equals(head)
                    || "<".equals(head) || "<=".equals(head)
                    || ">".equals(head) || ">=".equals(head)) {
                return Type.BOOL;
            }
            Function function = functions.get(head);
            return function == null ? Type.UNKNOWN : function.result;
        }
    }

    private static final class Node {
        private final String atom;
        private final List<Node> children;

        private Node(String atom, List<Node> children) {
            this.atom = atom;
            this.children = children;
        }

        private boolean isList() {
            return children != null;
        }
    }

    private static final class Parser {
        private final String input;
        private int offset;

        private Parser(String input) {
            this.input = input == null ? "" : input;
        }

        private List<Node> parse() {
            List<Node> result = new ArrayList<>();
            skipSpace();
            while (offset < input.length()) {
                result.add(node());
                skipSpace();
            }
            return result;
        }

        private Node node() {
            skipSpace();
            if (offset >= input.length()) throw new IllegalArgumentException();
            if (input.charAt(offset) != '(') {
                return new Node(token(), null);
            }
            offset++;
            List<Node> children = new ArrayList<>();
            skipSpace();
            while (offset < input.length() && input.charAt(offset) != ')') {
                children.add(node());
                skipSpace();
            }
            if (offset >= input.length()) throw new IllegalArgumentException();
            offset++;
            return new Node(null, children);
        }

        private String token() {
            int start = offset;
            char first = input.charAt(offset);
            if (first == '"') {
                offset++;
                while (offset < input.length()) {
                    if (input.charAt(offset) == '"') {
                        if (offset + 1 < input.length()
                                && input.charAt(offset + 1) == '"') {
                            offset += 2;
                        } else {
                            offset++;
                            return input.substring(start, offset);
                        }
                    } else {
                        offset++;
                    }
                }
                throw new IllegalArgumentException();
            }
            if (first == '|') {
                offset++;
                while (offset < input.length() && input.charAt(offset) != '|') {
                    offset += input.charAt(offset) == '\\'
                            && offset + 1 < input.length() ? 2 : 1;
                }
                if (offset >= input.length()) throw new IllegalArgumentException();
                offset++;
                return input.substring(start, offset);
            }
            while (offset < input.length()) {
                char value = input.charAt(offset);
                if (Character.isWhitespace(value) || value == '(' || value == ')'
                        || value == ';') break;
                offset++;
            }
            if (start == offset) throw new IllegalArgumentException();
            return input.substring(start, offset);
        }

        private void skipSpace() {
            while (offset < input.length()) {
                char value = input.charAt(offset);
                if (Character.isWhitespace(value)) {
                    offset++;
                } else if (value == ';') {
                    while (offset < input.length()
                            && input.charAt(offset) != '\n') offset++;
                } else {
                    return;
                }
            }
        }
    }
}
