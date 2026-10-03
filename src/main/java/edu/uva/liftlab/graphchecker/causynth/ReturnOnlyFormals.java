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

/**
 * Matched calls (SYMBOL-SCOPE §2.2): which demanded formals of a method --
 * its parameters and its {@code this} -- only its return needs.  The slice
 * demands such a formal's actual at a call site only where that call's
 * result is demanded ({@code SeedBackwardStaticAnalyzer#propagateCallArguments},
 * {@code #expandCallerArguments}, {@code #expandCallerReceiver}): a value that
 * enters a helper at one call leaves it only through that call's return.
 * Without it the slice entered a shared helper through its return at one
 * call and left it through every other caller's argument (hdfs-11741 on the
 * W6 tree: {@code PBHelperClient.getByteString(byte[])}, demanded at {@code
 * convert(BlockKey)}, demanded the bytes of its other 17 callers, SASL's
 * {@code convert(CipherOption)} among them, and through it {@code
 * DNConf.encryptionAlgorithm}).
 *
 * <p>The summary of a method {@code m} is read off the slice's own rows, the
 * edges with a cell of {@code m} at an end (a cell's method is the signature
 * it starts with, {@link #owner}):
 * <ul>
 *   <li>{@code Ret}: backward from {@code <m>.return} over the rows into
 *   {@code m}'s cells;</li>
 *   <li>{@code Eff}: backward, the same way, from every <em>effect
 *   origin</em> -- a relevant cell {@code Ret} does not hold; a cell of
 *   {@code m} a row takes out of {@code m} other than its return to a call
 *   ({@code call_return}, {@code dispatch_return}) and an argument or a
 *   receiver of a call (a field or array store, a container publication, a
 *   wire capture, a fault's {@code .throws}, a guard of another method's
 *   activation or store, a container argument the callee mutates); a cell of
 *   {@code m} a row from another method brings in other than a callee's
 *   return, a caller's argument, a functional return, a guard by a callee's
 *   fault and a mutated container argument (a wire consumer, a fault
 *   marker's result); the declared throw's exception (its thrown value
 *   and the guards deciding it); a container or array a row stores into
 *   ({@code container_mutation_argument}, {@code container_array_store_base})
 *   when the object is reached from a formal, {@code this} or a field --
 *   through copies, reads, views and call results, not through what was
 *   stored into it -- since the store changes an object a caller holds; and
 *   an actual a call inside {@code m} passes to a formal of its callee that
 *   is no return-only formal, or to a constructor (a constructor stores
 *   what it is passed);</li>
 *   <li>through a call inside {@code m} whose callee's summary marks the
 *   formal return-only, the actual is upstream of the call's result: it is
 *   in {@code Ret} or {@code Eff} as that result is.</li>
 * </ul>
 * A formal is return-only when {@code Ret} holds it and {@code Eff} does
 * not: one flowing into both the return and an effect reaches every caller.
 * A virtual call is decided per CHA target -- each implementation's own
 * summary, the union of their demands at the site.  A call of {@code m}
 * itself is a flow inside {@code m} (the body's fixpoint, through its return
 * and its formals); a cycle through other methods is conservative: a method
 * whose summary is being computed marks no formal return-only.  A library
 * call is followed by its contract, as before; it has no summary.
 *
 * <p>Monotone: a formal once found an effect stays one, and a formal that
 * turns from return-only into an effect re-queues its method, whose next
 * pass demands it at every caller the call index finds, and re-queues every
 * caller that met it while it was return-only ({@link #demanded}), whose
 * own next pass demands it at that call and decides its own formals again
 * -- a call through a type whose declaration of the method no dispatch
 * source names included.  A summary is kept until a row touching
 * the method or its relevance grows, or a formal anywhere turns; a method
 * with a return-only formal is re-queued whenever a row touches it, so its
 * callers' demand follows the rows.
 */
final class ReturnOnlyFormals {
    /** The slice a summary reads. */
    interface Slice {
        /** The method's demanded cells. */
        Set<String> relevant(String method);

        /** The method's {@code this} cell, or null. */
        String thisCell(String method);

        /** Processes the method again. */
        void requeue(String method);
    }

    /** A call's result: the callee's return, at the call site. */
    private static final Set<String> RETURNS = names("call_return",
            "dispatch_return");
    /** An actual into a callee's formal, or a receiver into its {@code
     *  this}: the callee's summary decides it. */
    private static final Set<String> CALLS = names("call_argument",
            "caller_argument", "method_caller_literal_argument",
            "dispatch_argument", "dispatch_caller_argument",
            "method_receiver", "dispatch_receiver",
            "dispatch_caller_receiver");
    /** The declared throw's rows: their exception node is an effect. */
    private static final Set<String> THROWN = names("exception_throw",
            "exception_guard");
    /** Rows storing into a container or an array, into the object. */
    private static final Set<String> STORES = names(
            "container_mutation_argument", "container_array_store_base");
    /** Rows bringing what an object holds, not the object itself. */
    private static final Set<String> CONTENTS = names(
            "container_mutation_argument", "container_array_store_base",
            "container_array_store_value", "constructor_argument_object");
    /** Rows from another method's cell into one of the method's that carry
     *  no demand of their own: what the method reads from it. */
    private static final Set<String> READS = names("call_return",
            "dispatch_return", "functional_return",
            "container_call_mutation_effect", "guard_dependency");

    private final Slice slice;
    private final Map<String, List<Map<String, Object>>> rowsByOwner =
            new LinkedHashMap<>();
    private final Map<String, Integer> versions = new LinkedHashMap<>();
    private final Map<String, Summary> summaries = new LinkedHashMap<>();
    private final Set<String> computing = new LinkedHashSet<>();
    /** Formals once found an effect. */
    private final Set<String> effects = new LinkedHashSet<>();
    /** Formals once found return-only, and their methods. */
    private final Set<String> returnOnly = new LinkedHashSet<>();
    private final Set<String> withReturnOnly = new LinkedHashSet<>();
    /** A return-only formal: the callers that met it. */
    private final Map<String, Set<String>> callers = new LinkedHashMap<>();
    /** How many formals turned from return-only into an effect. */
    private int turns;

    ReturnOnlyFormals(Slice slice) {
        this.slice = slice;
    }

    /** Whether only {@code method}'s return needs its demanded {@code
     *  formal} (a parameter cell or its {@code this} cell). */
    boolean returnOnly(String method, String formal) {
        return summary(method).contains(formal);
    }

    /**
     * The one rule: whether a call in {@code caller} demands the {@code
     * callee}'s demanded {@code formal} -- always, unless only the callee's
     * return needs it and the call's result is not demanded.  A return-only
     * formal remembers the caller either way, to re-queue it if it turns.
     */
    boolean demanded(String callee, String formal, boolean resultDemanded,
                     String caller) {
        if (!returnOnly(callee, formal)) return true;
        callers.computeIfAbsent(formal,
                ignored -> new LinkedHashSet<String>()).add(caller);
        return resultDemanded;
    }

    /** Indexes a new row under the methods of its two cells. */
    void row(Map<String, Object> row) {
        String from = owner(text(row.get("fromCell")));
        String to = owner(text(row.get("toCell")));
        index(from, row);
        if (to != null && !to.equals(from)) index(to, row);
    }

    /** The method's relevance grew. */
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

    /**
     * The method a cell belongs to: the method signature it starts with
     * ({@code <m>::local}, {@code <m>.paramN:T}, {@code <m>.return}, {@code
     * <m>.throws}, {@code <m>#uN}); null for a field or a literal.
     */
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

    /** One method's rows, by what they bring into its cells. */
    private final class Body {
        private final String method;
        private final String returned;
        /** A cell of the method: the cells rows bring into it. */
        private final Map<String, List<String>> upstream =
                new LinkedHashMap<>();
        /** A call's result cell: the return rows into it. */
        private final Map<String, List<Map<String, Object>>> results =
                new LinkedHashMap<>();
        /** A call site: the rows passing its actuals and receiver. */
        private final Map<Object, List<Map<String, Object>>> calls =
                new LinkedHashMap<>();
        /** A cell of the method: the cells the object it holds comes
         *  from (upstream without {@link #CONTENTS}). */
        private final Map<String, List<String>> provenance =
                new LinkedHashMap<>();
        /** The containers and arrays rows store into ({@link #STORES}). */
        private final Set<String> stored = new LinkedHashSet<>();

        private Body(String method) {
            this.method = method;
            this.returned = method + ".return";
        }

        /** Files one row; adds the origin it is, if any. */
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

        /** Whether the object {@code cell} holds is reached from a formal,
         *  {@code self} or a field: backward over {@link #provenance}, and
         *  from a call's result to the call's actuals. */
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

        /** Whether a call's actual is upstream of the call's result: its
         *  callee's summary marks the formal return-only. */
        private boolean linked(Map<String, Object> call) {
            String formal = text(call.get("toCell"));
            return returnOnly(owner(formal), formal);
        }

        /** The method's cells, and the cells they read, backward from
         *  {@code start}. */
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
