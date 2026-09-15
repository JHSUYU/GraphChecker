package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.Interaction;
import edu.uva.liftlab.graphchecker.d3.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One obligation's query: the path as its replay ran it, with one decision
 * negated, over a world the corpus states.
 *
 * <p>Four rules, and nothing else, decide what a symbol of that query may be:
 *
 * <ul>
 *   <li>a ROOT is one quantity across the corpus -- free inside the domain the
 *       case declares for it, free over both values when it is a declared
 *       marker, and PINNED to what the recording read when it has no domain,
 *       because the composition pins it there too and a flip that needs it to
 *       move could never become a finding;</li>
 *   <li>a CLOCK is per path, unbounded, with a {@code >= 0} floor only: every
 *       execution reads it fresh, so it is never an equality between paths;</li>
 *   <li>a HANDOFF {@code v_H(I)} is bound by its family: {@code OR_q (pi_q AND
 *       guard_q AND v_H = e_q)} over the producer paths whose export endpoint
 *       is I's producer.  The walk closes over the handoffs those arms name in
 *       turn -- a producer forwards what it was handed -- to a fixed point.  A
 *       control with no arm stays free and is named {@code unproducible}; a
 *       NESTED handoff with no arm is pinned to the arrival the recording
 *       states, which is what the composition does with an unproduced
 *       delivery;</li>
 *   <li>a STATE read is joined to the write version it observed, else pinned
 *       to the value the recording states, else the obligation is refused
 *       naming it ({@code UNSTATED_VALUE}).</li>
 * </ul>
 *
 * <p>Nothing else is free.  A token of a recorded predicate that is none of
 * the above is an undeclared name: on the flipped decision it refuses the
 * obligation, on a prefix decision it drops that conjunct with a named gap,
 * because the flipped arm is the claim and the prefix is context.</p>
 */
final class FlipQuery {
    private FlipQuery() {
    }

    /** One handoff of the focused occurrence the replay can be answered at. */
    static final class Control {
        final String attachEndpointId;
        final String variable;
        final boolean unproducible;

        private Control(String attachEndpointId, String variable,
                        boolean unproducible) {
            this.attachEndpointId = attachEndpointId;
            this.variable = variable;
            this.unproducible = unproducible;
        }
    }

    /** One assembled query, or the reason there is none. */
    static final class Built {
        final String smt2;
        final String refusal;
        final DecisionRow flipped;
        final List<Control> controls;
        /** query variable -> the root it stands for, for the model read-back. */
        final Map<String, String> rootVariables;
        final List<GapRow> gaps;

        private Built(String smt2, String refusal, DecisionRow flipped,
                      List<Control> controls, Map<String, String> rootVariables,
                      List<GapRow> gaps) {
            this.smt2 = smt2;
            this.refusal = refusal;
            this.flipped = flipped;
            this.controls = Collections.unmodifiableList(controls);
            this.rootVariables =
                    Collections.unmodifiableMap(rootVariables);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        boolean ok() {
            return refusal.isEmpty();
        }
    }

    /**
     * Whether one decision is worth an obligation: its predicate has to
     * mention something exploration can move.
     *
     * <p>A decision over constants is closed by the recording -- negating it
     * asks for a world the execution does not have -- and one over a value
     * nothing declares cannot be asked for either.</p>
     */
    static boolean flippable(Corpus corpus, String sessionId,
                             DecisionRow decision) {
        if (!decision.clockReadings().isEmpty()) return true;
        for (String token : SmtText.symbols(decision.term(),
                new LinkedHashSet<String>())) {
            Corpus.SymbolKind kind = corpus.symbolKind(sessionId, token);
            if (kind == Corpus.SymbolKind.ROOT
                    || kind == Corpus.SymbolKind.HANDOFF) {
                return true;
            }
        }
        return false;
    }

    static Built build(Corpus corpus, Task task, Corpus.RecordedPath path,
                       int flipIndex) {
        return new Builder(corpus, task, path).build(flipIndex);
    }

    /** One symbol as one session named it. */
    private static final class Ref {
        private final String sessionId;
        private final String symbol;

        private Ref(String sessionId, String symbol) {
            this.sessionId = sessionId;
            this.symbol = symbol;
        }

        private String key() {
            return sessionId + "|" + symbol;
        }
    }

    private static final class Builder {
        private final Corpus corpus;
        private final Task task;
        private final Corpus.RecordedPath path;
        private final SmtText.Names names = new SmtText.Names();
        private final Map<String, String> sorts =
                new LinkedHashMap<String, String>();
        private final Map<String, String> meaning =
                new LinkedHashMap<String, String>();
        private final List<String> assertions = new ArrayList<String>();
        private final Set<String> explained = new LinkedHashSet<String>();
        private final Deque<Ref> pending = new ArrayDeque<Ref>();
        private final Set<String> queued = new LinkedHashSet<String>();
        private final Map<String, Control> controls =
                new LinkedHashMap<String, Control>();
        private final Map<String, String> rootVariables =
                new LinkedHashMap<String, String>();
        private final List<GapRow> gaps = new ArrayList<GapRow>();
        private String refusal = "";

        private Builder(Corpus corpus, Task task, Corpus.RecordedPath path) {
            this.corpus = corpus;
            this.task = task;
            this.path = path;
        }

        private Built build(int flipIndex) {
            DecisionRow flipped = path.decisions.get(flipIndex);
            for (int index = 0; index <= flipIndex; index++) {
                DecisionRow decision = path.decisions.get(index);
                Set<String> unknown = new LinkedHashSet<String>();
                String term = rename(decision.term(), path.sessionId,
                        new LinkedHashSet<String>(), unknown);
                boolean last = index == flipIndex;
                if (!unknown.isEmpty()) {
                    String named = unknown.iterator().next();
                    if (last) {
                        return refuse(GapKind.DECLARATION_MISSING,
                                decision.siteId() + "#" + decision.ordinal(),
                                "the flipped predicate names " + named
                                        + ", which no mint, attach or read of "
                                        + path.sessionId + " declares",
                                flipped);
                    }
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            decision.siteId() + "#" + decision.ordinal(),
                            "prefix conjunct dropped: " + named
                                    + " is undeclared"));
                    continue;
                }
                boolean holds = last ? !decision.outcome() : decision.outcome();
                assertions.add(holds ? term : "(not " + term + ")");
            }
            drain();
            if (!refusal.isEmpty()) {
                return new Built("", refusal, flipped,
                        new ArrayList<Control>(controls.values()),
                        rootVariables, gaps);
            }
            return new Built(render(flipped, flipIndex), "", flipped,
                    new ArrayList<Control>(controls.values()), rootVariables,
                    gaps);
        }

        /** The fixed point: every symbol the query names gets its own rule. */
        private void drain() {
            int guard = 0;
            while (!pending.isEmpty() && refusal.isEmpty()) {
                if (++guard > 100_000) {
                    refusal = "SYMBOL_CLOSURE_DID_NOT_TERMINATE";
                    return;
                }
                Ref ref = pending.remove();
                switch (corpus.symbolKind(ref.sessionId, ref.symbol)) {
                    case ROOT:
                        root(corpus.root(ref.sessionId, ref.symbol));
                        break;
                    case HANDOFF:
                        handoff(corpus.attach(ref.sessionId, ref.symbol));
                        break;
                    case READ:
                        read(corpus.read(ref.sessionId, ref.symbol));
                        break;
                    default:
                        break;
                }
            }
        }

        // ---- the four rules ------------------------------------------

        private void root(RootMintRow row) {
            String variable = variable(row.sessionId(), row.symbol());
            if (!explained.add(variable)) return;
            if (row.kind() == RootKind.CLOCK) {
                assertions.add("(>= " + variable + " 0)");
                return;
            }
            rootVariables.put(variable, row.rootId());
            if (row.kind() == RootKind.MARKER && row.declared()) return;
            String[] domain = corpus.domainOf(row);
            if (domain == null) {
                pin(variable, row.recordedValue(),
                        "root " + row.rootId() + " has no declared domain");
                return;
            }
            String min = SmtText.literal(domain[0], sorts.get(variable));
            String max = SmtText.literal(domain[1], sorts.get(variable));
            if (min.isEmpty() || max.isEmpty()) {
                pin(variable, row.recordedValue(),
                        "root " + row.rootId() + " has an unreadable domain");
                return;
            }
            assertions.add("(and (>= " + variable + " " + min + ") (<= "
                    + variable + " " + max + "))");
        }

        private void handoff(AttachRow attach) {
            String variable = variable(attach.sessionId(), attach.symbol());
            boolean control = attach.endpoint().occurrence()
                    .equals(task.focused());
            if (!explained.add(variable)) {
                if (control) registerControl(attach, variable, false);
                return;
            }
            List<String> arms = new ArrayList<String>();
            List<String> refusals = new ArrayList<String>();
            Set<String> seen = new LinkedHashSet<String>();
            if (attach.producer() != null) {
                for (ExportRow export : corpus.exportsAt(attach.producer())) {
                    String arm = arm(export, variable, refusals);
                    if (!arm.isEmpty() && seen.add(arm)) arms.add(arm);
                }
            } else {
                refusals.add("the attach is unpaired: no producer endpoint");
            }
            if (!arms.isEmpty()) {
                assertions.add(SmtText.disjoin(arms));
                if (control) registerControl(attach, variable, false);
                return;
            }
            if (control) {
                registerControl(attach, variable, true);
                gaps.add(GapRow.of(attach.sessionId(),
                        GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        attach.endpoint().toString(),
                        "no producer arm in this corpus: " + reasons(refusals)));
                return;
            }
            String arrival = SmtText.literal(attach.arrival(),
                    sorts.get(variable));
            if (arrival.isEmpty()) {
                gaps.add(GapRow.of(attach.sessionId(),
                        GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        attach.endpoint().toString(),
                        "nested handoff with neither an arm nor an arrival: "
                                + reasons(refusals)));
                return;
            }
            assertions.add("(= " + variable + " " + arrival + ")");
        }

        private void read(ReadRow row) {
            String variable = variable(row.sessionId(), row.symbol());
            if (!explained.add(variable)) return;
            WriteRow writer = corpus.writeOf(row.sessionId(), row.location(),
                    row.observedVersion());
            if (writer != null) {
                SessionReader.Session session = corpus.session(row.sessionId());
                SmtLowering.Lowered lowered = session.lowering()
                        .lower(writer.expressionRef());
                Set<String> unknown = new LinkedHashSet<String>();
                if (lowered.ok()) {
                    String value = rename(lowered.text(), row.sessionId(),
                            new LinkedHashSet<String>(), unknown);
                    if (unknown.isEmpty()) {
                        assertions.add("(= " + variable + " " + value + ")");
                        return;
                    }
                }
            }
            String stated = SmtText.literal(row.concreteValue(),
                    sorts.get(variable));
            if (!stated.isEmpty()) {
                assertions.add("(= " + variable + " " + stated + ")");
                return;
            }
            refusal = "UNSTATED_VALUE:" + row.endpoint();
            gaps.add(GapRow.of(row.sessionId(), GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, row.endpoint().toString(),
                    "the read joins no write version and the recording "
                            + "states no value for it"));
        }

        /**
         * One family arm: what one producer path delivered, under the
         * decisions it took and the valuation it ran under.
         *
         * <p>The guard states only roots the corpus VARIED: a root every
         * replay read the same way separates no arm from another, and stating
         * it would pin the very quantity the flip exists to move.  A clock is
         * never an equality.  An arm from a run in which the producer ran
         * concretely is UNATTESTED -- it states what was delivered, not why --
         * and is named as such.</p>
         */
        private String arm(ExportRow export, String variable,
                           List<String> refusals) {
            SessionReader.Session session = corpus.session(export.sessionId());
            if (session == null) {
                refusals.add("no session to resolve " + export.sessionId());
                return "";
            }
            Set<String> roots = new LinkedHashSet<String>();
            Set<String> unknown = new LinkedHashSet<String>();
            SmtLowering.Lowered lowered =
                    session.lowering().lower(export.expressionRef());
            String delivered;
            boolean attested;
            if (lowered.ok()) {
                delivered = rename(lowered.text(), export.sessionId(), roots,
                        unknown);
                if (!unknown.isEmpty()) {
                    refusals.add("delivered a value this replay did not "
                            + "state: " + unknown.iterator().next());
                    return "";
                }
                attested = corpus.ranFocused(export.sessionId(),
                        export.endpoint().occurrence());
            } else {
                delivered = SmtText.literal(export.recordedValue(),
                        sorts.get(variable));
                if (delivered.isEmpty()) {
                    refusals.add(lowered.refusal());
                    return "";
                }
                attested = false;
            }
            List<String> conjuncts = new ArrayList<String>();
            for (DecisionRow decision : corpus.decisionsOf(export.sessionId(),
                    export.endpoint().occurrence())) {
                // The prefix of the DELIVERY: a decision the producer took
                // after putting the value on the wire cannot be a condition
                // of what it delivered.  The session's own event order says
                // which those are (CONTRACT-SPEC v1.1 seq).
                if (decision.seq() >= export.seq()) continue;
                if (!flippable(corpus, export.sessionId(), decision)) continue;
                String term = rename(decision.term(), export.sessionId(),
                        roots, unknown);
                if (!unknown.isEmpty()) {
                    refusals.add("its prefix names " + unknown.iterator().next()
                            + ", which that replay did not declare");
                    return "";
                }
                conjuncts.add(decision.outcome() ? term
                        : "(not " + term + ")");
            }
            for (String rootId : roots) {
                if (!corpus.varied(rootId)) continue;
                String rootVariable = rootVariable(rootId);
                String reading = SmtText.literal(
                        corpus.rootReading(export.sessionId(), rootId),
                        sorts.get(rootVariable));
                if (rootVariable.isEmpty() || reading.isEmpty()) continue;
                conjuncts.add("(= " + rootVariable + " " + reading + ")");
            }
            conjuncts.add("(= " + variable + " " + delivered + ")");
            if (!attested) {
                gaps.add(GapRow.of(export.sessionId(), GapKind.UNATTESTED_ARM,
                        GapClass.DIAGNOSTIC, export.endpoint().toString(),
                        "the producer ran concretely in this session: the arm "
                                + "states the delivery, not the reason for it"));
            }
            return SmtText.conjoin(conjuncts);
        }

        // ---- naming --------------------------------------------------

        /**
         * Renames one recorded term into the query's variables, declaring and
         * enqueueing every symbol it names.
         */
        private String rename(String term, String sessionId,
                              Set<String> rootsTouched, Set<String> unknown) {
            Map<String, String> rename = new LinkedHashMap<String, String>();
            for (String token : SmtText.symbols(term,
                    new LinkedHashSet<String>())) {
                Corpus.SymbolKind kind = corpus.symbolKind(sessionId, token);
                if (kind == Corpus.SymbolKind.UNKNOWN) continue;
                rename.put(token, variable(sessionId, token));
                if (kind == Corpus.SymbolKind.ROOT) {
                    RootMintRow root = corpus.root(sessionId, token);
                    if (root.kind() != RootKind.CLOCK) {
                        rootsTouched.add(root.rootId());
                    }
                }
            }
            return SmtText.rewrite(term, rename, unknown);
        }

        /**
         * The query variable one session's symbol stands for.
         *
         * <p>A root is ONE variable across the corpus, because a root is one
         * quantity and a family arm's guard is what states each replay's own
         * reading of it.  A clock is one variable per session, because every
         * execution reads it fresh.  A handoff is one variable per
         * INTERACTION -- both endpoints -- so two producers of the same port
         * are two variables and never one.  A state read is one variable per
         * read event, because a version id is a session-local name.</p>
         */
        private String variable(String sessionId, String symbol) {
            switch (corpus.symbolKind(sessionId, symbol)) {
                case ROOT: {
                    RootMintRow row = corpus.root(sessionId, symbol);
                    boolean clock = row.kind() == RootKind.CLOCK;
                    String key = clock
                            ? "clock|" + row.rootId() + "|" + sessionId
                            : "root|" + row.rootId();
                    String name = names.name(key, (clock ? "clk_" : "r_")
                            + row.rootId() + (clock ? "_" + sessionId : ""));
                    declare(name, row.kind() == RootKind.MARKER
                            ? "Bool" : "Int",
                            (clock ? "clock " : "root ") + row.rootId()
                                    + " recorded " + row.recordedValue());
                    enqueue(sessionId, symbol);
                    return name;
                }
                case HANDOFF: {
                    AttachRow row = corpus.attach(sessionId, symbol);
                    Interaction interaction = row.producer() == null ? null
                            : Interaction.of(InteractionKind.WIRE,
                                    row.producer(), row.endpoint());
                    String key = interaction == null
                            ? "unpaired|" + row.endpoint().id()
                            : "handoff|" + interaction.id();
                    String name = names.name(key, "vH_" + row.endpoint().site()
                            + "_" + row.endpoint().siteIndex().hash());
                    declare(name, sortOf(row.javaType(), name,
                            "handoff " + row.endpoint()),
                            "handoff " + row.endpoint() + " arrival "
                                    + row.arrival() + " : " + row.javaType());
                    enqueue(sessionId, symbol);
                    return name;
                }
                case READ: {
                    ReadRow row = corpus.read(sessionId, symbol);
                    String name = names.name("read|" + sessionId + "|"
                            + row.endpoint().id(), "st_"
                            + row.location().slot() + "_"
                            + row.endpoint().siteIndex().hash());
                    declare(name, sortOf(row.javaType(), name,
                            "read " + row.endpoint()),
                            "read " + row.endpoint() + " of " + row.location()
                                    + " version " + row.observedVersion()
                                    + " : " + row.javaType());
                    enqueue(sessionId, symbol);
                    return name;
                }
                default:
                    return symbol;
            }
        }

        /** The variable one root already has, or "" when it has none yet. */
        private String rootVariable(String rootId) {
            for (Map.Entry<String, String> entry : rootVariables.entrySet()) {
                if (entry.getValue().equals(rootId)) return entry.getKey();
            }
            RootMintRow any = corpus.anyRoot(rootId);
            return any == null ? ""
                    : variable(any.sessionId(), any.symbol());
        }

        /**
         * The sort the runtime declared one value at.
         *
         * <p>A descriptor this query cannot state -- a reference, a string, a
         * floating value -- refuses the obligation under its own name instead
         * of being lowered as an integer.  The shared lowering states those
         * sorts; the flip query's own assembly does not, and guessing is how
         * two formulas come to be about two different variables.</p>
         */
        private String sortOf(String javaType, String name, String subject) {
            String sort = SmtText.sortOfJavaType(javaType);
            if (!sort.isEmpty()) return sort;
            refusal = "UNSTATED_VALUE:" + subject;
            gaps.add(GapRow.of(path.sessionId, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, subject,
                    "the runtime declared " + name + " at javaType '"
                            + javaType + "', which is not a sort this query "
                            + "states"));
            return "Int";
        }

        private void declare(String name, String sort, String what) {
            sorts.put(name, sort);
            meaning.put(name, what);
        }

        private void enqueue(String sessionId, String symbol) {
            Ref ref = new Ref(sessionId, symbol);
            if (queued.add(ref.key())) pending.add(ref);
        }

        private void registerControl(AttachRow attach, String variable,
                                     boolean unproducible) {
            controls.put(attach.endpoint().id(), new Control(
                    attach.endpoint().id(), variable, unproducible));
        }

        private void pin(String variable, String recorded, String why) {
            String literal = SmtText.literal(recorded, sorts.get(variable));
            if (literal.isEmpty()) {
                gaps.add(GapRow.of(path.sessionId, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, variable,
                        why + ", and no recorded value to pin it to"));
                return;
            }
            assertions.add("(= " + variable + " " + literal + ")");
        }

        private Built refuse(GapKind kind, String subject, String detail,
                             DecisionRow flipped) {
            gaps.add(GapRow.of(path.sessionId, kind, GapClass.BLOCKING,
                    subject, detail));
            return new Built("", kind.name() + ":" + subject, flipped,
                    new ArrayList<Control>(controls.values()), rootVariables,
                    gaps);
        }

        private static String reasons(List<String> refusals) {
            return refusals.isEmpty() ? "no export row names this interaction"
                    : refusals.get(0);
        }

        private String render(DecisionRow flipped, int flipIndex) {
            StringBuilder text = new StringBuilder();
            text.append("; task ").append(task.taskId())
                    .append(" focused ").append(task.focused().render())
                    .append('\n');
            text.append("; path ").append(path.pathId).append(" session ")
                    .append(path.sessionId).append('\n');
            text.append("; flip ").append(flipped.siteId()).append('#')
                    .append(flipped.ordinal()).append(" recorded ")
                    .append(flipped.outcome()).append(" -> ")
                    .append(!flipped.outcome()).append(" after ")
                    .append(flipIndex).append(" prefix decisions\n");
            for (Map.Entry<String, String> entry : meaning.entrySet()) {
                text.append("; ").append(entry.getKey()).append(" = ")
                        .append(entry.getValue()).append('\n');
            }
            text.append("(set-logic ALL)\n");
            for (Map.Entry<String, String> entry : sorts.entrySet()) {
                text.append("(declare-fun ").append(entry.getKey())
                        .append(" () ").append(entry.getValue()).append(")\n");
            }
            for (String assertion : assertions) {
                text.append("(assert ").append(assertion).append(")\n");
            }
            text.append("(check-sat)\n(get-model)\n");
            return text.toString();
        }
    }
}
