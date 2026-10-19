package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

final class ReturnOnlyFormals {
    interface Slice {
        Set<String> relevant(String method);

        String thisCell(String method);

        void requeue(String method);
    }

    private static final Set<String> RETURNS = names("call_return",
            "dispatch_return");
    private static final Set<String> CALLS = names("call_argument",
            "caller_argument", "method_caller_literal_argument",
            "dispatch_argument", "dispatch_caller_argument",
            "method_receiver", "dispatch_receiver",
            "dispatch_caller_receiver");
    private static final Set<String> THROWN = names("exception_throw",
            "exception_guard");
    private static final Set<String> STORES = names(
            "container_mutation_argument", "container_array_store_base");
    private static final Set<String> CONTENTS = names(
            "container_mutation_argument", "container_array_store_base",
            "container_array_store_value", "constructor_argument_object");
    private static final Set<String> READS = names("call_return",
            "dispatch_return", "functional_return",
            "container_call_mutation_effect", "guard_dependency");

    private final Slice slice;
    private final Map<String, List<Map<String, Object>>> rowsByOwner =
            new LinkedHashMap<>();
    private final Map<String, Integer> versions = new LinkedHashMap<>();
    private final Map<String, Summary> summaries = new LinkedHashMap<>();
    private final Set<String> computing = new LinkedHashSet<>();
    private final Set<String> effects = new LinkedHashSet<>();
    private final Set<String> returnOnly = new LinkedHashSet<>();
    private final Set<String> withReturnOnly = new LinkedHashSet<>();
    private final Map<String, Set<String>> callers = new LinkedHashMap<>();
    private int turns;

    ReturnOnlyFormals(Slice slice) {
        this.slice = slice;
    }

    boolean returnOnly(String method, String formal) {
        return summary(method).contains(formal);
    }

    boolean demanded(String callee, String formal, boolean resultDemanded,
                     String caller) {
        if (!returnOnly(callee, formal)) return true;
        callers.computeIfAbsent(formal,
                ignored -> new LinkedHashSet<String>()).add(caller);
        return resultDemanded;
    }

    void row(Map<String, Object> row) {
        String from = owner(text(row.get("fromCell")));
        String to = owner(text(row.get("toCell")));
        index(from, row);
        if (to != null && !to.equals(from)) index(to, row);
    }

    void grew(String method) {
        versions.merge(method, 1, Integer::sum);
        if (withReturnOnly.contains(method)) slice.requeue(method);
    }

    private void index(String method, Map<String, Object> row) {
        if (method == null) return;
        rowsByOwner.computeIfAbsent(method,
                ignored -> new ArrayList<Map<String, Object>>()).add(row);
        grew(method);
    }

    static String owner(String cell) {
        int end = cell == null || !cell.startsWith("<") ? -1
                : cell.indexOf(")>");
        return end < 0 ? null : cell.substring(0, end + 2);
    }

    private Set<String> summary(String method) {
        int version = versions.getOrDefault(method, 0);
        Summary kept = summaries.get(method);
        if (kept != null && kept.version == version && kept.turns == turns) {
            return kept.returnOnly;
        }
        if (!computing.add(method)) return Collections.emptySet();
        try {
            Set<String> found = compute(method);
            summaries.put(method, new Summary(version, turns, found));
            return found;
        } finally {
            computing.remove(method);
        }
    }

    private Set<String> compute(String method) {
        Body body = new Body(method);
        List<String> origins = new ArrayList<>();
        for (Map<String, Object> row : rowsByOwner.getOrDefault(method,
                Collections.<Map<String, Object>>emptyList())) {
            body.read(row, origins);
        }
        Set<String> relevant = new LinkedHashSet<>(slice.relevant(method));
        String self = slice.thisCell(method);
        for (String stored : body.stored) {
            if (body.heldOutside(stored, self)) origins.add(stored);
        }
        Set<String> ret = body.closure(Collections.singleton(
                method + ".return"));
        for (String cell : relevant) {
            if (!ret.contains(cell)) origins.add(cell);
        }
        for (List<Map<String, Object>> calls : body.calls.values()) {
            for (Map<String, Object> call : calls) {
                if (!body.linked(call)) origins.add(text(call.get("fromCell")));
            }
        }
        Set<String> eff = body.closure(origins);
        Set<String> found = new LinkedHashSet<>();
        for (String formal : formals(method, relevant, self)) {
            if (ret.contains(formal) && !eff.contains(formal)
                    && !effects.contains(formal)) {
                found.add(formal);
                returnOnly.add(formal);
                withReturnOnly.add(method);
            } else if (effects.add(formal) && returnOnly.contains(formal)) {
                turns++;
                slice.requeue(method);
                for (String caller : callers.getOrDefault(formal,
                        Collections.<String>emptySet())) {
                    slice.requeue(caller);
                }
            }
        }
        return found;
    }

    private static List<String> formals(String method, Set<String> relevant,
                                        String self) {
        List<String> formals = new ArrayList<>();
        for (String cell : relevant) {
            if (cell.startsWith(method + ".param")) formals.add(cell);
        }
        if (self != null && relevant.contains(self)) formals.add(self);
        return formals;
    }

    private final class Body {
        private final String method;
        private final String returned;
        private final Map<String, List<String>> upstream =
                new LinkedHashMap<>();
        private final Map<String, List<Map<String, Object>>> results =
                new LinkedHashMap<>();
        private final Map<Object, List<Map<String, Object>>> calls =
                new LinkedHashMap<>();
        private final Map<String, List<String>> provenance =
                new LinkedHashMap<>();
        private final Set<String> stored = new LinkedHashSet<>();

        private Body(String method) {
            this.method = method;
            this.returned = method + ".return";
        }

        private void read(Map<String, Object> row, List<String> origins) {
            String from = text(row.get("fromCell"));
            String to = text(row.get("toCell"));
            String kind = text(row.get("kind"));
            String source = owner(from);
            String target = owner(to);
            boolean out = method.equals(source);
            boolean in = method.equals(target);
            if (in) {
                add(upstream, to, from);
                if (!CONTENTS.contains(kind)) add(provenance, to, from);
                if (STORES.contains(kind)) stored.add(to);
            }
            if (THROWN.contains(kind)) origins.add(to);
            if (out && !in) {
                if (RETURNS.contains(kind) && from.equals(returned)) return;
                if (CALLS.contains(kind) && target != null
                        && !CausynthStaticFacts.constructor(target)) {
                    add(calls, row.get("unitIndex"), row);
                    return;
                }
                origins.add(from);
            } else if (in && !out) {
                if (RETURNS.contains(kind)) add(results, to, row);
                if (source == null || READS.contains(kind)
                        || CALLS.contains(kind)) {
                    return;
                }
                origins.add(to);
            }
        }

        private boolean heldOutside(String cell, String self) {
            Set<String> seen = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>();
            work.add(cell);
            while (!work.isEmpty()) {
                String next = work.pop();
                if (!seen.add(next)) continue;
                String held = owner(next);
                if (next.startsWith(method + ".param") || next.equals(self)
                        || held == null && next.startsWith("<")) {
                    return true;
                }
                if (!method.equals(held)) continue;
                work.addAll(provenance.getOrDefault(next,
                        Collections.<String>emptyList()));
                for (Map<String, Object> result : results.getOrDefault(next,
                        Collections.<Map<String, Object>>emptyList())) {
                    for (Map<String, Object> call : calls.getOrDefault(
                            result.get("unitIndex"),
                            Collections.<Map<String, Object>>emptyList())) {
                        work.add(text(call.get("fromCell")));
                    }
                }
            }
            return false;
        }

        private boolean linked(Map<String, Object> call) {
            String formal = text(call.get("toCell"));
            return returnOnly(owner(formal), formal);
        }

        private Set<String> closure(Collection<String> start) {
            Set<String> seen = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>(start);
            while (!work.isEmpty()) {
                String cell = work.pop();
                if (!seen.add(cell) || !method.equals(owner(cell))) continue;
                work.addAll(upstream.getOrDefault(cell,
                        Collections.<String>emptyList()));
                for (Map<String, Object> result : results.getOrDefault(cell,
                        Collections.<Map<String, Object>>emptyList())) {
                    String callee = owner(text(result.get("fromCell")));
                    for (Map<String, Object> call : calls.getOrDefault(
                            result.get("unitIndex"),
                            Collections.<Map<String, Object>>emptyList())) {
                        if (callee.equals(owner(text(call.get("toCell"))))
                                && linked(call)) {
                            work.add(text(call.get("fromCell")));
                        }
                    }
                }
            }
            return seen;
        }
    }

    private static <K, V> void add(Map<K, List<V>> map, K key, V value) {
        map.computeIfAbsent(key, ignored -> new ArrayList<V>()).add(value);
    }

    private static Set<String> names(String... names) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(
                Arrays.asList(names)));
    }

    private static final class Summary {
        private final int version;
        private final int turns;
        private final Set<String> returnOnly;

        private Summary(int version, int turns, Set<String> returnOnly) {
            this.version = version;
            this.turns = turns;
            this.returnOnly = returnOnly;
        }
    }
}
