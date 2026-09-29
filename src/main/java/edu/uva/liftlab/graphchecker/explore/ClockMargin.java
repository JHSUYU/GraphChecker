package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.SExpression;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

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
 * rule to the asserted negation. {@code eps} = one minute
 * ({@link #MARGIN_NANOS}), in the ticks of the clock the atom names; an
 * atom naming clocks of two ticks is left alone.</p>
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
public final class ClockMargin {
    public static final long MARGIN_NANOS = TimeUnit.MINUTES.toNanos(1);

    /** The margin in the ticks of a clock whose tick is {@code clockNanos}
     *  nanoseconds ({@code RootMintRow#clockNanos}). */
    public static long margin(long clockNanos) {
        return JavaPrimitiveSmtSemantics.clockTicks(MARGIN_NANOS, clockNanos);
    }

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
     * One demanded assertion with every clock comparison given its clock's
     * margin of room.
     *
     * @param asserted the lowered, renamed text the query asserts
     * @param margins  the query's CLOCK cell variables, each with its
     *                 margin in its own ticks ({@link #margin})
     */
    static Strengthened strengthen(String asserted,
                                   Map<String, Long> margins) {
        List<String> unreached = new ArrayList<String>();
        if (asserted == null || asserted.isEmpty() || margins == null
                || margins.isEmpty()) {
            return new Strengthened(asserted == null ? "" : asserted,
                    unreached);
        }
        SExpression root = SExpression.parse(asserted, 0);
        if (root == null) {
            return new Strengthened(asserted, unreached);
        }
        Walk walk = new Walk(asserted, margins);
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
        private final Map<String, Long> margins;
        private final List<Edit> edits = new ArrayList<Edit>();
        private final Set<String> unstrengthened = new LinkedHashSet<String>();

        private Walk(String source, Map<String, Long> margins) {
            this.source = source;
            this.margins = margins;
        }

        /** One subterm at the demanded polarity: TRUE (holds if it does), FALSE
         *  (holds if it does not), null (unknown). */
        private void visit(SExpression node, Boolean polarity) {
            if (node.atom()) return;
            String head = node.head();
            if ("not".equals(head) && node.children().size() == 2) {
                visit(node.children().get(1), polarity == null ? null
                        : Boolean.valueOf(!polarity.booleanValue()));
                return;
            }
            if (("and".equals(head) || "or".equals(head))
                    && node.children().size() > 1) {
                // Monotone connectives: a stronger conjunct strengthens the
                // whole.
                for (int index = 1; index < node.children().size(); index++) {
                    visit(node.children().get(index), polarity);
                }
                return;
            }
            if (COMPARISONS.contains(head) && node.children().size() == 3) {
                atom(node, head, node.children().get(1), node.children().get(2),
                        polarity);
                return;
            }
            // Anything else decides no polarity below it.
            for (int index = 1; index < node.children().size(); index++) {
                visit(node.children().get(index), null);
            }
        }

        /** One comparison atom, read back through the JVM's compare. */
        private void atom(SExpression node, String head, SExpression left,
                          SExpression right, Boolean polarity) {
            String operator = head;
            SExpression a = left;
            SExpression b = right;
            boolean whole = false;
            SExpression[] compared = integralCompare(left, right);
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
            Set<Long> named = new LinkedHashSet<Long>();
            marginsNamed(a, margins, named);
            marginsNamed(b, margins, named);
            if (named.isEmpty()) return;
            if (polarity == null || named.size() > 1) {
                unstrengthened.add(node.text());
                return;
            }
            long epsilon = named.iterator().next();
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
                SExpression side = left0 ? a : b;
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
    private static SExpression[] integralCompare(SExpression compare,
                                                 SExpression zero) {
        if (compare.atom() || compare.children().size() != 4
                || !"ite".equals(compare.head())
                || !"0".equals(zero.text().trim())) {
            return null;
        }
        SExpression less = compare.children().get(1);
        if (less.atom() || less.children().size() != 3) return null;
        SExpression a = less.children().get(1);
        SExpression b = less.children().get(2);
        String stated = JavaPrimitiveSmtSemantics.integralCompareResult(
                a.text(), b.text());
        if (!flat(stated).equals(flat(compare.text()))) return null;
        return new SExpression[]{a, b};
    }

    /** Into {@code into}, the margin of every clock cell this term names. */
    private static void marginsNamed(SExpression node,
                                     Map<String, Long> margins,
                                     Set<Long> into) {
        if (node.atom()) {
            Long margin = margins.get(node.text());
            if (margin != null) into.add(margin);
            return;
        }
        for (SExpression child : node.children()) {
            marginsNamed(child, margins, into);
        }
    }

    /** Whether a margin can be added to this term (it must be arithmetic). */
    private static boolean arithmetic(SExpression node) {
        if (node.atom()) return true;
        String head = node.head();
        if (NOT_ARITHMETIC.contains(head) || head.startsWith("fp.")) {
            return false;
        }
        for (SExpression child : node.children()) {
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
}
