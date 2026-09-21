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
 * <p>A flip query asks for the complement of an arm the recording took, and
 * the solver answers with the cheapest world that satisfies it: on
 * hdfs-11741 campaign #4, {@code expiryDate < now} was satisfied by ONE
 * millisecond.  The instant is not what the replay then runs -- a clock is
 * stated as a SKEW ({@code ObligationFactory#solve}) and the replay adds it
 * to the instant it reads for itself, while the quantity the guard compares
 * against moves between runs by tens to thousands of milliseconds -- so the
 * guard fell back on the recorded arm and 35 of wave 1's 59 replays came
 * back NOT_ADMITTED with "wrong decision at removeExpiredKeys#u15".  The 5
 * that were admitted had margins of +57 to +405ms; the refusals, -21ms and
 * below.</p>
 *
 * <p>So every comparison atom of a demanded decision term that names a CLOCK
 * cell is asked for with room to spare: {@code a >= b} demanded true becomes
 * {@code a >= b + eps}, {@code a < b} becomes {@code a + eps < b}, and a
 * demanded FALSE is the same rule on the proposition the query actually
 * asserts -- {@code (not (>= a b))} becomes {@code (not (>= (+ a eps) b))},
 * which is {@code a + eps < b}.  {@code eps} is {@value #DEFAULT_MARGIN_MS}
 * milliseconds unless the system property {@value #MARGIN_PROPERTY} states
 * another (0 turns the strengthening off).</p>
 *
 * <p>WHAT AN ATOM IS.  The JVM does not compare two longs with a relational
 * operator: it runs {@code lcmp} and branches on the result, which lowers to
 * {@link JavaPrimitiveSmtSemantics#integralCompareResult} -- {@code (ite (<
 * A B) (- 1) (ite (> A B) 1 0))} -- under a {@code (>= ... 0)}.  Every one
 * of the 35 refusals is that shape, so {@code (>= CMP 0)} is READ BACK as
 * {@code A >= B} (the same equivalence the lowering states, checked by
 * rebuilding the text) and strengthened there.  Adding the margin to the
 * {@code 0} would have added a millisecond count to a three-valued compare
 * code and made every one of those queries unsatisfiable.</p>
 *
 * <p>NOTHING ELSE IS TOUCHED.  An atom no clock cell reaches is left alone;
 * so is one whose polarity this walk cannot resolve (under an {@code ite},
 * an {@code =}, a {@code distinct} or an {@code xor}), and so is one whose
 * operands are not arithmetic -- a margin has the unit of the quantity it is
 * added to, and a term with a branch in it is not a millisecond count.  Each
 * of those is named to the caller, which files it as one DIAGNOSTIC row.
 * Polarity is pushed through {@code not}, {@code and} and {@code or} only,
 * which are the connectives a demanded conjunct is built from.</p>
 */
final class ClockMargin {
    /** How many milliseconds of room a demanded clock comparison is given. */
    static final long DEFAULT_MARGIN_MS = 60_000L;
    /** The one property that overrides it. */
    static final String MARGIN_PROPERTY = "causynth.clock.flip.margin.ms";

    /** The comparison atoms this rule is about. */
    private static final Set<String> COMPARISONS =
            new LinkedHashSet<String>(java.util.Arrays.asList(
                    "<", "<=", ">", ">="));

    /**
     * What may stand inside an operand the margin is added to or compared
     * against: an arithmetic term, and never a branch or a predicate.
     */
    private static final Set<String> NOT_ARITHMETIC =
            new LinkedHashSet<String>(java.util.Arrays.asList(
                    "ite", "=", "distinct", "xor", "not", "and", "or", "=>",
                    "<", "<=", ">", ">=", "let", "forall", "exists"));

    private ClockMargin() {
    }

    /** The margin this JVM states, in milliseconds. */
    static long margin() {
        String stated = System.getProperty(MARGIN_PROPERTY);
        if (stated == null || stated.trim().isEmpty()) {
            return DEFAULT_MARGIN_MS;
        }
        try {
            long value = Long.parseLong(stated.trim());
            return value < 0 ? DEFAULT_MARGIN_MS : value;
        } catch (NumberFormatException notAMargin) {
            return DEFAULT_MARGIN_MS;
        }
    }

    /** One demanded term, strengthened, and the atoms it could not reach. */
    static final class Strengthened {
        final String text;
        /** The atoms left as they were, each one a DIAGNOSTIC of its own. */
        final List<String> unstrengthened;

        private Strengthened(String text, List<String> unstrengthened) {
            this.text = text;
            this.unstrengthened = Collections.unmodifiableList(
                    unstrengthened);
        }
    }

    /**
     * One demanded assertion with every clock comparison it states given
     * {@code epsilon} milliseconds of room.
     *
     * @param asserted the text the query asserts, lowered and renamed: the
     *                 flipped conjunct's negation, or an inherited flip's
     *                 own conjunct
     * @param clocks   the query's CLOCK cell variables, by name
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

    // ---- the walk ----------------------------------------------------

    /** One edit: the span of the source it replaces, and what it says. */
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

        /**
         * One subterm, at the polarity the assertion demands of it.
         *
         * @param polarity {@code TRUE} where the demanded proposition holds
         *                 if this subterm does, {@code FALSE} where it holds
         *                 if this subterm does not, {@code null} where this
         *                 walk cannot say
         */
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
                // Both are monotone in every argument, so a conjunct made
                // stronger makes the whole demanded proposition stronger.
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
            // Anything else -- an ite, an =, a distinct, an xor, an
            // arithmetic term -- decides no polarity for what is under it.
            for (int index = 1; index < node.children.size(); index++) {
                visit(node.children.get(index), null);
            }
        }

        /** One comparison atom, read back through the JVM's own compare. */
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
                    // (op 0 CMP) states the mirrored comparison of A and B.
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
            // WHICH SIDE THE MARGIN GOES ON: the one that makes the
            // DEMANDED proposition harder to satisfy.  Demanded true, the
            // greater side has to clear the smaller by eps; demanded false,
            // the query asserts the atom's negation, so the margin moves to
            // the other side and the negation says the same thing.
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

    /** {@code >=} and {@code <=} read from the other side, and so on. */
    private static String mirrored(String operator) {
        if (">".equals(operator)) return "<";
        if (">=".equals(operator)) return "<=";
        if ("<".equals(operator)) return ">";
        return ">=";
    }

    /**
     * The two longs a {@code (ite (< A B) (- 1) (ite (> A B) 1 0))} beside a
     * {@code 0} compares, or null when this is not that atom.
     *
     * <p>Recognized by REBUILDING it: the lowering has one spelling for a
     * JVM {@code lcmp} ({@link
     * JavaPrimitiveSmtSemantics#integralCompareResult}), and a candidate
     * that does not come back as that text is some other {@code ite}.</p>
     */
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

    /** Whether any name of this subterm is one of these. */
    private static boolean names(Node node, Set<String> wanted) {
        if (node.children == null) return wanted.contains(node.text());
        for (Node child : node.children) {
            if (names(child, wanted)) return true;
        }
        return false;
    }

    /**
     * Whether a margin can be added to this term at all: it has to be an
     * arithmetic one, because eps has the unit of what it is added to.
     */
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

    /** One subterm of the asserted text, and where it stands in it. */
    private static final class Node {
        private final String source;
        private final int start;
        private final int end;
        /** Null for a token; the head and its arguments for a list. */
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

        /** The operator this list applies, or {@code ""}. */
        private String head() {
            if (children == null || children.isEmpty()) return "";
            Node first = children.get(0);
            return first.children == null ? first.text() : "";
        }
    }

    /** One term, read from {@code at[0]}, which is left past it. */
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

    /** Past one token, keeping a quoted symbol or a string whole. */
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
