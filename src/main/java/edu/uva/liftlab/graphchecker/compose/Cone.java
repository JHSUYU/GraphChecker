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

final class Cone {

    static final String BOUNDARY = "_field_HOFF.";

    private final String text;
    private final Set<String> consts = new HashSet<String>();
    private final Map<String, int[]> defs = new HashMap<String, int[]>();
    private final Map<String, Set<String>> defined =
            new HashMap<String, Set<String>>();
    private final Map<String, List<int[]>> asserted =
            new HashMap<String, List<int[]>>();

    Cone(String text) {
        this.text = text;
        for (int[] form : topLevel(text)) read(form);
    }

    synchronized Set<String> unbound(String selector, String pathId,
                                     Collection<String> arms,
                                     Collection<Composer.Concrete> concrete) {
        List<Node> fatal = new ArrayList<Node>();
        List<Node> families = new ArrayList<Node>();
        for (int[] form : asserted.getOrDefault(selector,
                Collections.<int[]>emptyList())) {
            assertion(parse(form[0], form[1]), selector, fatal, families);
        }
        Set<String> open = new TreeSet<String>();
        Set<String> bound = new HashSet<String>();
        for (Node family : families) {
            bound.addAll(names(family, Collections.<String>emptySet()));
        }
        for (Composer.Concrete row : concrete) {
            if (SmtLowering.settled(row.kind) && pathId.equals(row.pathId)) {
                bound.add(row.subject);
                bound.add(SmtNames.legalSymbols(row.subject));
            }
        }
        if (!fatal.isEmpty()) {
            for (String name : names(fatal.get(fatal.size() - 1),
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

    private void read(int[] form) {
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
            case "assert": {
                List<String> lead = leading(form[0], form[1], 7);
                int arrow = lead.indexOf("=>");
                if (arrow > 0 && arrow + 1 < lead.size()
                        && "(".equals(lead.get(arrow - 1))) {
                    asserted.computeIfAbsent(lead.get(arrow + 1),
                            selector -> new ArrayList<int[]>()).add(form);
                }
                return;
            }
            default:
        }
    }

    private static void assertion(Node node, String selector,
                                  List<Node> fatal, List<Node> families) {
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
            fatal.add(body.kids.get(2));
        } else if (name.startsWith("message_family")) {
            families.add(body.kids.get(2));
        }
    }

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

    private List<String> leading(int from, int to, int limit) {
        List<String> tokens = new ArrayList<String>();
        int at = from;
        while (at < to && tokens.size() < limit) {
            char one = text.charAt(at);
            if (Character.isWhitespace(one)) {
                at++;
            } else if (one == '(' || one == ')') {
                tokens.add(String.valueOf(one));
                at++;
            } else {
                int end = atomEnd(at, to);
                tokens.add(text.substring(at, end));
                at = end;
            }
        }
        return tokens;
    }

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
