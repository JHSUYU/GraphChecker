package edu.uva.liftlab.graphchecker.compose;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * THE OPEN LINKS of a claimed path's causal chain, read off the composed
 * formula exactly as {@code experiments/accept/cone.py} reads them, so
 * COMPOSE and the checker name one set (PIPELINE §8): a boundary constant --
 * a handoff's {@code v_H}, {@code _field_HOFF.} -- the path's fatal condition
 * names (through define-funs; let-bound and quantified names, and a
 * define-fun's parameters, are no constants) that no message family
 * asserted under the path's selector names, and a boundary value an arm the
 * witness chose holds FREE or HELD ({@code concrete[]}, its arm).  Each is a
 * value the witness rests on that no producer the corpus attests made.
 *
 * <p>Read iteratively: a composed formula nests thousands deep.</p>
 */
final class Cone {

    /** What makes a constant a handoff's value ({@code HandoffMint}). */
    static final String BOUNDARY = "_field_HOFF.";

    private final String text;
    private final Set<String> consts = new HashSet<String>();
    /** Each define-fun's form, parsed when first named. */
    private final Map<String, int[]> defs = new HashMap<String, int[]>();
    private final Map<String, Set<String>> defined =
            new HashMap<String, Set<String>>();
    /** The selector's fatal and family assertions' bodies. */
    private final List<Node> fatalBodies = new ArrayList<Node>();
    private final List<Node> familyBodies = new ArrayList<Node>();

    private Cone(String text, String selector) {
        this.text = text;
        for (int[] form : topLevel(text)) read(form, selector);
    }

    /**
     * The open links of the path {@code selector} selects ({@code pathId}),
     * whose witness chose {@code arms}: cone.py's {@code unbound} for that
     * path, sorted.
     */
    static Set<String> unbound(String formula, String selector,
                               String pathId, Collection<String> arms,
                               Collection<Composer.Concrete> concrete) {
        Set<String> open = new TreeSet<String>();
        Cone cone = new Cone(formula, selector);
        Set<String> bound = new HashSet<String>();
        for (Node family : cone.familyBodies) {
            bound.addAll(cone.names(family, Collections.<String>emptySet()));
        }
        // The last fatal assertion of the selector, as cone.py's dict keeps.
        if (!cone.fatalBodies.isEmpty()) {
            for (String name : cone.names(
                    cone.fatalBodies.get(cone.fatalBodies.size() - 1),
                    Collections.<String>emptySet())) {
                if (name.contains(BOUNDARY) && !bound.contains(name)) {
                    open.add(name);
                }
            }
        }
        for (Composer.Concrete row : concrete) {
            if (("HELD".equals(row.kind) || "FREE".equals(row.kind))
                    && row.arm != null && arms.contains(row.arm)
                    && pathId.equals(row.pathId)
                    && row.subject.contains(BOUNDARY)) {
                open.add(row.subject);
            }
        }
        return open;
    }

    /** One top-level command: the declarations, definitions and the
     *  selector's fatal and family assertions are kept. */
    private void read(int[] form, String selector) {
        List<String> head = atoms(form[0] + 1, form[1], 3);
        if (head.isEmpty()) return;
        switch (head.get(0)) {
            case "declare-const":
                if (head.size() > 1) consts.add(head.get(1));
                return;
            case "declare-fun": {
                Node node = parse(form[0], form[1]);
                if (node.kids.size() > 2 && node.kids.get(2).kids != null
                        && node.kids.get(2).kids.isEmpty()) {
                    consts.add(node.kids.get(1).atom);
                }
                return;
            }
            case "define-fun":
                if (head.size() > 1) defs.put(head.get(1), form);
                return;
            case "assert":
                // Only an assertion under this selector is parsed whole.
                if (text.indexOf("(=> " + selector + " ", form[0]) < 0
                        || text.indexOf("(=> " + selector + " ", form[0])
                        >= form[1]) {
                    return;
                }
                assertion(parse(form[0], form[1]), selector);
                return;
            default:
        }
    }

    /** {@code (assert (! (=> selector body) :named name))}: a fatal or a
     *  family of this selector keeps its body. */
    private void assertion(Node node, String selector) {
        if (node.kids.size() < 2) return;
        Node body = node.kids.get(1);
        String name = "";
        if (body.kids != null && !body.kids.isEmpty()
                && "!".equals(body.kids.get(0).atom)) {
            for (int at = 0; at + 1 < body.kids.size(); at++) {
                if (":named".equals(body.kids.get(at).atom)) {
                    name = body.kids.get(at + 1).atom;
                }
            }
            body = body.kids.get(1);
        }
        if (body.kids == null || body.kids.size() != 3
                || !"=>".equals(body.kids.get(0).atom)
                || !selector.equals(body.kids.get(1).atom)) {
            return;
        }
        if (name.startsWith("path_fatal")) {
            fatalBodies.add(body.kids.get(2));
        } else if (name.startsWith("message_family")) {
            familyBodies.add(body.kids.get(2));
        }
    }

    /** The declared constants {@code root} depends on, {@code bound} names
     *  aside (cone.py's {@code Formula.names}). */
    private Set<String> names(Node root, Set<String> bound) {
        Set<String> found = new LinkedHashSet<String>();
        Deque<Object[]> pending = new ArrayDeque<Object[]>();
        pending.push(new Object[]{root, bound});
        while (!pending.isEmpty()) {
            Object[] next = pending.pop();
            Node node = (Node) next[0];
            @SuppressWarnings("unchecked")
            Set<String> scope = (Set<String>) next[1];
            if (node.kids == null) {
                String atom = node.atom;
                if (scope.contains(atom)) continue;
                if (consts.contains(atom)) {
                    found.add(atom);
                } else if (defs.containsKey(atom)) {
                    found.addAll(defined(atom));
                }
                continue;
            }
            if (node.kids.isEmpty()) continue;
            String head = node.kids.get(0).atom;
            if ("let".equals(head) && node.kids.size() > 2) {
                Set<String> inner = new HashSet<String>(scope);
                for (Node binding : node.kids.get(1).kidsOrNone()) {
                    if (binding.kidsOrNone().size() < 2) continue;
                    pending.push(new Object[]{binding.kids.get(1), scope});
                    inner.add(binding.kids.get(0).atom);
                }
                pending.push(new Object[]{node.kids.get(2), inner});
            } else if (("forall".equals(head) || "exists".equals(head))
                    && node.kids.size() > 2) {
                Set<String> inner = new HashSet<String>(scope);
                for (Node binder : node.kids.get(1).kidsOrNone()) {
                    if (!binder.kidsOrNone().isEmpty()) {
                        inner.add(binder.kids.get(0).atom);
                    }
                }
                pending.push(new Object[]{node.kids.get(2), inner});
            } else {
                for (Node kid : node.kids) pending.push(new Object[]{kid, scope});
            }
        }
        return found;
    }

    /** A define-fun's constants, its parameters aside; memoized, a cycle
     *  reading as nothing. */
    private Set<String> defined(String name) {
        Set<String> done = defined.get(name);
        if (done != null) return done;
        defined.put(name, Collections.<String>emptySet());
        int[] form = defs.get(name);
        Node node = parse(form[0], form[1]);
        Set<String> params = new HashSet<String>();
        if (node.kids.size() > 2) {
            for (Node param : node.kids.get(2).kidsOrNone()) {
                if (!param.kidsOrNone().isEmpty()) {
                    params.add(param.kids.get(0).atom);
                }
            }
        }
        Set<String> found = node.kids.size() > 4
                ? names(node.kids.get(4), params)
                : Collections.<String>emptySet();
        defined.put(name, found);
        return found;
    }

    // ------------------------------------------------------------------
    // Reading SMT-LIB text (cone.py's forms()).
    // ------------------------------------------------------------------

    /** One term: an atom, or a list ({@code kids}). */
    private static final class Node {
        final String atom;
        final List<Node> kids;

        Node(String atom, List<Node> kids) {
            this.atom = atom;
            this.kids = kids;
        }

        List<Node> kidsOrNone() {
            return kids == null ? Collections.<Node>emptyList() : kids;
        }
    }

    /** Each top-level form's [start, end) in {@code text}. */
    static List<int[]> topLevel(String text) {
        List<int[]> forms = new ArrayList<int[]>();
        int depth = 0;
        int start = -1;
        for (int at = 0; at < text.length(); at++) {
            char one = text.charAt(at);
            if (one == ';') {
                int end = text.indexOf('\n', at);
                at = end < 0 ? text.length() : end;
            } else if (one == '|' || one == '"') {
                at = closing(text, at);
            } else if (one == '(') {
                if (depth == 0) start = at;
                depth++;
            } else if (one == ')' && depth > 0) {
                depth--;
                if (depth == 0) forms.add(new int[]{start, at + 1});
            }
        }
        return forms;
    }

    /** The first {@code limit} atoms of the list body [from, to), nested
     *  lists skipped. */
    private List<String> atoms(int from, int to, int limit) {
        List<String> found = new ArrayList<String>();
        int at = from;
        while (at < to && found.size() < limit) {
            char one = text.charAt(at);
            if (Character.isWhitespace(one)) {
                at++;
            } else if (one == '(' || one == ')') {
                return found;
            } else {
                int end = atomEnd(at, to);
                found.add(text.substring(at, end));
                at = end;
            }
        }
        return found;
    }

    /** The term [from, to), parsed with an explicit stack. */
    private Node parse(int from, int to) {
        Deque<List<Node>> open = new ArrayDeque<List<Node>>();
        List<Node> top = new ArrayList<Node>();
        open.push(top);
        int at = from;
        while (at < to) {
            char one = text.charAt(at);
            if (one == ';') {
                int end = text.indexOf('\n', at);
                at = end < 0 || end > to ? to : end;
            } else if (Character.isWhitespace(one)) {
                at++;
            } else if (one == '(') {
                List<Node> list = new ArrayList<Node>();
                open.peek().add(new Node(null, list));
                open.push(list);
                at++;
            } else if (one == ')') {
                if (open.size() > 1) open.pop();
                at++;
            } else {
                int end = atomEnd(at, to);
                open.peek().add(new Node(text.substring(at, end), null));
                at = end;
            }
        }
        return top.isEmpty() ? new Node("", null) : top.get(0);
    }

    private int atomEnd(int at, int to) {
        char first = text.charAt(at);
        if (first == '|' || first == '"') {
            return Math.min(to, closing(text, at) + 1);
        }
        int end = at;
        while (end < to) {
            char one = text.charAt(end);
            if (Character.isWhitespace(one) || one == '(' || one == ')'
                    || one == ';') {
                break;
            }
            end++;
        }
        return end == at ? at + 1 : end;
    }

    /** The index of the {@code |} or {@code "} closing the one at
     *  {@code at} (a string's {@code ""} is an escaped quote). */
    private static int closing(String text, int at) {
        char quote = text.charAt(at);
        int index = at + 1;
        while (index < text.length()) {
            if (text.charAt(index) == quote) {
                if (quote == '"' && index + 1 < text.length()
                        && text.charAt(index + 1) == '"') {
                    index += 2;
                    continue;
                }
                return index;
            }
            index++;
        }
        return text.length() - 1;
    }
}
