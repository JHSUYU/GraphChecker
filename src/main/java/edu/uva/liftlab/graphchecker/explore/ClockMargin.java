package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * THE MARGIN a DEMANDED flip over a clock is strengthened by.
 *
 * <p>The solver returns the cheapest world (hdfs-11741: {@code expiryDate <
 * now} by one millisecond), but a clock is replayed as a SKEW ({@code
 * ObligationFactory#solve}) over an instant that drifts between runs, so a thin
 * margin falls back on the recorded arm (NOT_ADMITTED).</p>
 *
 * <p>So each comparison atom naming a CLOCK cell is demanded with room: {@code
 * a >= b} true becomes {@code a >= b + eps}; demanded FALSE applies the same
 * rule to the asserted negation. {@code eps} = {@value #MARGIN_MS} ms.</p>
 *
 * <p>Trap: a JVM {@code lcmp} lowers to {@link
 * JavaPrimitiveSmtSemantics#integralCompareResult} under {@code (>= ... 0)}; it
 * is read back as {@code A >= B} (verified by rebuilding the text), since
 * adding eps to the three-valued compare code makes the query UNSAT.</p>
 *
 * <p>Nothing else is touched: atoms with no clock, unresolved polarity (under
 * {@code ite}, {@code =}, {@code distinct}, {@code xor}) or non-arithmetic
 * operands are returned for one DIAGNOSTIC row each. Polarity passes only
 * through {@code not}, {@code and}, {@code or}.</p>
 */
final class ClockMargin {
    static final long MARGIN_MS = 60_000L;

    private static final Set<String> COMPARISONS =
            new LinkedHashSet<String>(java.util.Arrays.asList(
                    "<", "<=", ">", ">="));

    /** Heads that make an operand non-arithmetic (a margin needs a quantity).
     */
    private static final Set<String> NOT_ARITHMETIC =
            new LinkedHashSet<String>(java.util.Arrays.asList(
                    "ite", "=", "distinct", "xor", "not", "and", "or", "=>",
                    "<", "<=", ">", ">=", "let", "forall", "exists"));

    private ClockMargin() {
    }

    /** One demanded term, strengthened, and the atoms it could not reach. */
    static final class Strengthened {
        final String text;
        /** Atoms left as they were, one DIAGNOSTIC each. */
        final List<String> unstrengthened;

        private Strengthened(String text, List<String> unstrengthened) {
            this.text = text;
            this.unstrengthened = Collections.unmodifiableList(
                    unstrengthened);
        }
    }

    /**
     * One demanded assertion with every clock comparison given {@code epsilon}
     * of room.
     *
     * @param asserted the lowered, renamed text the query asserts
     * @param clocks   the query's CLOCK cell variables
     * @param epsilon  the margin; {@code 0} leaves the text alone
     */
    static Strengthened strengthen(String asserted, Set<String> clocks,
                                   long epsilon) {
        List<String> unreached = new ArrayList<String>();
        if (asserted == null || asserted.isEmpty() || clocks == null
                || clocks.isEmpty() || epsilon <= 0) {
            return new Strengthened(asserted == null ? "" : asserted,
                    unreached);
        }
        Node root = parse(asserted, new int[]{0});
        if (root == null) {
            return new Strengthened(asserted, unreached);
        }
        Walk walk = new Walk(asserted, clocks, epsilon);
        walk.visit(root, Boolean.TRUE);
        return new Strengthened(walk.rewritten(),
                new ArrayList<String>(walk.unstrengthened));
    }


    private static final class Edit implements Comparable<Edit> {
        private final int start;
        private final int end;
        private final String text;

        private Edit(int start, int end, String text) {
            this.start = start;
            this.end = end;
            this.text = text;
        }

        @Override
        public int compareTo(Edit other) {
            return Integer.compare(start, other.start);
        }
    }

    private static final class Walk {
        private final String source;
        private final Set<String> clocks;
        private final long epsilon;
        private final List<Edit> edits = new ArrayList<Edit>();
        private final Set<String> unstrengthened = new LinkedHashSet<String>();

        private Walk(String source, Set<String> clocks, long epsilon) {
            this.source = source;
            this.clocks = clocks;
            this.epsilon = epsilon;
        }

        /** One subterm at the demanded polarity: TRUE (holds if it does), FALSE
         *  (holds if it does not), null (unknown). */
        private void visit(Node node, Boolean polarity) {
            if (node.children == null) return;
            String head = node.head();
            if ("not".equals(head) && node.children.size() == 2) {
                visit(node.children.get(1), polarity == null ? null
                        : Boolean.valueOf(!polarity.booleanValue()));
                return;
            }
            if (("and".equals(head) || "or".equals(head))
                    && node.children.size() > 1) {
                // Monotone connectives: a stronger conjunct strengthens the
                // whole.
                for (int index = 1; index < node.children.size(); index++) {
                    visit(node.children.get(index), polarity);
                }
                return;
            }
            if (COMPARISONS.contains(head) && node.children.size() == 3) {
                atom(node, head, node.children.get(1), node.children.get(2),
                        polarity);
                return;
            }
            // Anything else decides no polarity below it.
            for (int index = 1; index < node.children.size(); index++) {
                visit(node.children.get(index), null);
            }
        }

        /** One comparison atom, read back through the JVM's compare. */
        private void atom(Node node, String head, Node left, Node right,
                          Boolean polarity) {
            String operator = head;
            Node a = left;
            Node b = right;
            boolean whole = false;
            Node[] compared = integralCompare(left, right);
            if (compared == null) {
                compared = integralCompare(right, left);
                if (compared != null) {
                    // (op 0 CMP) is the mirrored comparison of A and B.
                    operator = mirrored(head);
                    whole = true;
                }
            } else {
                whole = true;
            }
            if (compared != null) {
                a = compared[0];
                b = compared[1];
            }
            if (!names(a, clocks) && !names(b, clocks)) return;
            if (polarity == null) {
                unstrengthened.add(node.text());
                return;
            }
            if (!arithmetic(a) || !arithmetic(b)) {
                unstrengthened.add(node.text());
                return;
            }
            // The margin goes on the side that makes the DEMANDED proposition
            // harder; for a demanded false it moves to the other side of the
            // negated atom.
            boolean upper = ">".equals(operator) || ">=".equals(operator);
            boolean left0 = upper != polarity.booleanValue();
            String padded = "(+ " + (left0 ? a.text() : b.text()) + " "
                    + epsilon + ")";
            if (!whole) {
                Node side = left0 ? a : b;
                edits.add(new Edit(side.start, side.end, padded));
                return;
            }
            edits.add(new Edit(node.start, node.end, "(" + operator + " "
                    + (left0 ? padded : a.text()) + " "
                    + (left0 ? b.text() : padded) + ")"));
        }

        private String rewritten() {
            if (edits.isEmpty()) return source;
            Collections.sort(edits);
            StringBuilder out = new StringBuilder(source.length() + 64);
            int at = 0;
            for (Edit edit : edits) {
                if (edit.start < at) continue;
                out.append(source, at, edit.start).append(edit.text);
                at = edit.end;
            }
            return out.append(source, at, source.length()).toString();
        }
    }

    private static String mirrored(String operator) {
        if (">".equals(operator)) return "<";
        if (">=".equals(operator)) return "<=";
        if ("<".equals(operator)) return ">";
        return ">=";
    }

    /** The two longs an {@code lcmp} term beside {@code 0} compares, or null;
     *  recognized only if rebuilding it yields the same text. */
    private static Node[] integralCompare(Node compare, Node zero) {
        if (compare.children == null || compare.children.size() != 4
                || !"ite".equals(compare.head())
                || !"0".equals(zero.text().trim())) {
            return null;
        }
        Node less = compare.children.get(1);
        if (less.children == null || less.children.size() != 3) return null;
        Node a = less.children.get(1);
        Node b = less.children.get(2);
        String stated = JavaPrimitiveSmtSemantics.integralCompareResult(
                a.text(), b.text());
        if (!flat(stated).equals(flat(compare.text()))) return null;
        return new Node[]{a, b};
    }

    private static boolean names(Node node, Set<String> wanted) {
        if (node.children == null) return wanted.contains(node.text());
        for (Node child : node.children) {
            if (names(child, wanted)) return true;
        }
        return false;
    }

    /** Whether a margin can be added to this term (it must be arithmetic). */
    private static boolean arithmetic(Node node) {
        if (node.children == null) return true;
        String head = node.head();
        if (NOT_ARITHMETIC.contains(head) || head.startsWith("fp.")) {
            return false;
        }
        for (Node child : node.children) {
            if (!arithmetic(child)) return false;
        }
        return true;
    }

    private static String flat(String text) {
        StringBuilder out = new StringBuilder(text.length());
        boolean space = false;
        for (int at = 0; at < text.length(); at++) {
            char one = text.charAt(at);
            if (one == ' ' || one == '\t' || one == '\n' || one == '\r') {
                space = out.length() > 0;
                continue;
            }
            if (space) out.append(' ');
            space = false;
            out.append(one);
        }
        return out.toString();
    }

    // ---- the one reading of an s-expression --------------------------

    private static final class Node {
        private final String source;
        private final int start;
        private final int end;
        /** Null for a token. */
        private final List<Node> children;

        private Node(String source, int start, int end, List<Node> children) {
            this.source = source;
            this.start = start;
            this.end = end;
            this.children = children;
        }

        private String text() {
            return source.substring(start, end);
        }

        private String head() {
            if (children == null || children.isEmpty()) return "";
            Node first = children.get(0);
            return first.children == null ? first.text() : "";
        }
    }

    /** One term from {@code at[0]}; {@code at[0]} is left past it. */
    private static Node parse(String text, int[] at) {
        int index = skip(text, at[0]);
        if (index >= text.length()) {
            at[0] = index;
            return null;
        }
        if (text.charAt(index) != '(') {
            int end = token(text, index);
            at[0] = end;
            return new Node(text, index, end, null);
        }
        List<Node> children = new ArrayList<Node>();
        int cursor = index + 1;
        while (true) {
            cursor = skip(text, cursor);
            if (cursor >= text.length()) {
                at[0] = cursor;
                return new Node(text, index, cursor, children);
            }
            if (text.charAt(cursor) == ')') {
                at[0] = cursor + 1;
                return new Node(text, index, cursor + 1, children);
            }
            int[] inner = new int[]{cursor};
            Node child = parse(text, inner);
            if (child == null || inner[0] <= cursor) {
                at[0] = text.length();
                return new Node(text, index, text.length(), children);
            }
            children.add(child);
            cursor = inner[0];
        }
    }

    private static int skip(String text, int at) {
        int index = at;
        while (index < text.length()
                && Character.isWhitespace(text.charAt(index))) {
            index++;
        }
        return index;
    }

    /** Past one token; a quoted symbol or string stays whole. */
    private static int token(String text, int at) {
        char first = text.charAt(at);
        if (first == '|' || first == '"') {
            int index = at + 1;
            while (index < text.length() && text.charAt(index) != first) {
                index++;
            }
            return index >= text.length() ? text.length() : index + 1;
        }
        int index = at;
        while (index < text.length()) {
            char one = text.charAt(index);
            if (Character.isWhitespace(one) || one == '(' || one == ')') break;
            index++;
        }
        return index == at ? at + 1 : index;
    }
}
