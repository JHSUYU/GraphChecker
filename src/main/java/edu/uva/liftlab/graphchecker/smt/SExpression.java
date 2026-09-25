package edu.uva.liftlab.graphchecker.smt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * THE s-expression reader: one term of SMT-LIB text (a z3 answer, a lowered
 * term) as offsets into that text, so a caller can quote or rewrite a
 * subterm exactly as written.  A {@code |quoted|} symbol or {@code "string"}
 * is one atom; an unclosed list ends at the end of the text.
 */
public final class SExpression {
    private final String source;
    /** Where this term starts and ends in {@link #source}. */
    public final int start;
    public final int end;
    /** Null for an atom. */
    private final List<SExpression> children;

    private SExpression(String source, int start, int end,
                        List<SExpression> children) {
        this.source = source;
        this.start = start;
        this.end = end;
        this.children = children;
    }

    /** The first term at or after {@code at}, or null when there is none. */
    public static SExpression parse(String text, int at) {
        int index = skip(text, Math.max(0, at));
        if (index >= text.length()) return null;
        if (text.charAt(index) != '(') {
            return new SExpression(text, index, atomEnd(text, index), null);
        }
        List<SExpression> children = new ArrayList<SExpression>();
        int cursor = index + 1;
        while (true) {
            cursor = skip(text, cursor);
            if (cursor >= text.length()) {
                return new SExpression(text, index, cursor, children);
            }
            if (text.charAt(cursor) == ')') {
                return new SExpression(text, index, cursor + 1, children);
            }
            SExpression child = parse(text, cursor);
            children.add(child);
            cursor = child.end;
        }
    }

    public boolean atom() {
        return children == null;
    }

    /** The list's members; empty for an atom. */
    public List<SExpression> children() {
        return children == null ? Collections.<SExpression>emptyList()
                : Collections.unmodifiableList(children);
    }

    /** This term exactly as written. */
    public String text() {
        return source.substring(start, end);
    }

    /** The atom a list opens with, or "". */
    public String head() {
        if (children == null || children.isEmpty()) return "";
        SExpression first = children.get(0);
        return first.atom() ? first.text() : "";
    }

    private static int skip(String text, int at) {
        int index = at;
        while (index < text.length()
                && Character.isWhitespace(text.charAt(index))) {
            index++;
        }
        return index;
    }

    /** Past one atom; a quoted symbol or string stays whole. */
    private static int atomEnd(String text, int at) {
        char first = text.charAt(at);
        if (first == '|' || first == '"') {
            int index = text.indexOf(first, at + 1);
            return index < 0 ? text.length() : index + 1;
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
