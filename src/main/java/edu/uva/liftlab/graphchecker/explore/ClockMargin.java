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

public final class ClockMargin {
    public static final long MARGIN_NANOS = TimeUnit.MINUTES.toNanos(1);

    public static long margin(long clockNanos) {
        return JavaPrimitiveSmtSemantics.clockTicks(MARGIN_NANOS, clockNanos);
    }

    private static final Set<String> COMPARISONS =
            new LinkedHashSet<String>(java.util.Arrays.asList(
                    "<", "<=", ">", ">="));

    private static final Set<String> NOT_ARITHMETIC =
            new LinkedHashSet<String>(java.util.Arrays.asList(
                    "ite", "=", "distinct", "xor", "not", "and", "or", "=>",
                    "<", "<=", ">", ">=", "let", "forall", "exists"));

    private ClockMargin() {
    }

    static final class Strengthened {
        final String text;
        final List<String> unstrengthened;

        private Strengthened(String text, List<String> unstrengthened) {
            this.text = text;
            this.unstrengthened = Collections.unmodifiableList(
                    unstrengthened);
        }
    }

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
            for (int index = 1; index < node.children().size(); index++) {
                visit(node.children().get(index), null);
            }
        }

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
