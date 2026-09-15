package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.d3.smt.Arms;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
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
 * The anchor's closure, as a list of tasks.
 *
 * <p>The closure is what the anchor's failure can depend on, and nothing
 * else: the anchor occurrence itself, the PRODUCER of every interaction its
 * paths read (transitively -- a producer often forwards a value it was
 * itself handed, so its export names another {@code v_H} whose own producer
 * belongs to the closure too), the WRITER of every version its paths read,
 * and the occurrences its node's state connects it to (the writers and
 * readers of one location).</p>
 *
 * <p>Each closure element becomes one task with ONE focused occurrence, and
 * carries the co-occurrences it is state-connected to as its {@code factor}:
 * those replay symbolically with it, because a value in a container is
 * written by one activation and read by another on the same node, and
 * separating them would leave the read with nothing to join to.  The
 * producer of a wire interaction is never a factor -- it is another node's
 * activation and therefore its own task, explored on its own frontier and
 * admitted on its own prefix.</p>
 */
public final class ClosurePlanner {
    /** How many tasks one anchor may open, before the closure is truncated. */
    public static final int DEFAULT_MAX_TASKS = 64;

    private ClosurePlanner() {
    }

    /** The closure of one anchor, and what could not be named in it. */
    public static final class Plan {
        public final List<Task> tasks;
        public final List<GapRow> gaps;

        private Plan(List<Task> tasks, List<GapRow> gaps) {
            this.tasks = Collections.unmodifiableList(tasks);
            this.gaps = Collections.unmodifiableList(gaps);
        }
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor) {
        return plan(corpus, anchor, DEFAULT_MAX_TASKS);
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks) {
        List<Task> tasks = new ArrayList<Task>();
        List<GapRow> gaps = new ArrayList<GapRow>();
        Set<String> visited = new LinkedHashSet<String>();
        Deque<OccurrenceAddress> pending = new ArrayDeque<OccurrenceAddress>();
        pending.add(anchor);
        visited.add(anchor.id());
        while (!pending.isEmpty() && tasks.size() < maxTasks) {
            OccurrenceAddress occurrence = pending.remove();
            String seed = seedSession(corpus, occurrence);
            if (seed.isEmpty()) {
                // A closure member is explored by ONE focused replay of the
                // recording it was planned from, so an address no session
                // activated and no session decided anything at is not a task
                // -- there is no run to focus, and no rows to walk further
                // from.  It is BLOCKING for the same reason a truncated
                // closure is: the composition would offer the solver an arm
                // whose path condition nothing attests.
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                        occurrence.render(),
                        "no session of this corpus activated this occurrence "
                                + "or recorded a decision of it, so no replay "
                                + "can be focused on it and it is not a task"));
                continue;
            }
            List<OccurrenceAddress> factor = stateConnected(corpus,
                    occurrence);
            tasks.add(Task.of(taskId(occurrence), occurrence, factor, seed));
            for (OccurrenceAddress next
                    : successors(corpus, occurrence, factor, gaps)) {
                if (visited.add(next.id())) pending.add(next);
            }
        }
        if (!pending.isEmpty()) {
            // A truncated closure composes a formula that is missing
            // producers the anchor's paths read, and a composition missing an
            // arm is not a weaker claim -- it is an unsound one.
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                    anchor.render(), "closure truncated at " + maxTasks
                            + " tasks; " + pending.size() + " occurrences "
                            + "were not planned, so this anchor's closure is "
                            + "incomplete"));
        }
        return new Plan(tasks, gaps);
    }

    /** One task's id: the occurrence it focuses and nothing else. */
    public static String taskId(OccurrenceAddress focused) {
        return ExploreIds.sha16("task|" + focused.id());
    }

    /**
     * The task one published obligation names.
     *
     * <p>A task id is its focused occurrence's id and nothing else, so the
     * worker that executes an obligation recovers the task from the corpus
     * rather than from a second file that could disagree with the wave's.</p>
     */
    public static Task taskOf(Corpus corpus, String taskId) {
        if (taskId == null || taskId.isEmpty()) return null;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!taskId.equals(taskId(occurrence))) continue;
            String seed = seedSession(corpus, occurrence);
            // The wave never published a task for such an occurrence (it said
            // so as a BLOCKING gap), so "no task" is the honest answer here
            // too, rather than a Task with an empty recording behind it.
            if (seed.isEmpty()) return null;
            return Task.of(taskId, occurrence, stateConnected(corpus,
                    occurrence), seed);
        }
        return null;
    }

    /**
     * Everything one occurrence's failure can depend on outside its own node
     * state: the producers of the interactions it reads and the writers of
     * the versions it reads, plus the co-occurrences its factor names, whose
     * own producers belong to the closure just as much.
     */
    private static List<OccurrenceAddress> successors(
            Corpus corpus, OccurrenceAddress occurrence,
            List<OccurrenceAddress> factor, List<GapRow> gaps) {
        List<OccurrenceAddress> next = new ArrayList<OccurrenceAddress>();
        List<OccurrenceAddress> group = new ArrayList<OccurrenceAddress>();
        group.add(occurrence);
        group.addAll(factor);
        // The group is ONE symbolic unit -- a factor member exists because
        // its writes feed the focused occurrence's reads -- so what "the
        // admitted paths read" is asked of the group, not of each member
        // alone: the addKeys activation decides nothing itself, and the
        // handoff it writes into the map is read by the occurrence beside it.
        Set<String> read = readSymbols(corpus, group);
        for (OccurrenceAddress member : group) {
            if (!member.equals(occurrence)) next.add(member);
            for (AttachRow attach : corpus.attachesOn(member)) {
                if (!read.contains(attach.symbol())) {
                    unread(gaps, attach.sessionId(), attach.endpoint()
                            .toString(), "handoff");
                    continue;
                }
                producers(corpus, attach, next, gaps,
                        new LinkedHashSet<String>());
            }
            for (ReadRow row : corpus.readsOn(member)) {
                if (!read.contains(row.symbol())) {
                    unread(gaps, row.sessionId(), row.endpoint().toString(),
                            "state read");
                    continue;
                }
                for (WriteRow write : eligibleWrites(corpus, row)) {
                    next.add(write.endpoint().occurrence());
                }
            }
        }
        return next;
    }

    /**
     * Every symbol the admitted paths of one occurrence actually read.
     *
     * <p>The closure is what the anchor's failure CAN depend on, and an
     * activation's rows are not all of that: a port the region attached but
     * no path ever branched on, and no value it read ever rested on, is a
     * delivery this anchor does not use.  Planning its producer as a task
     * spends replays on a region the composition will not name.</p>
     *
     * <p>The set is the same closure the query takes: the symbols the
     * decisions and the target predicate name, then the symbols the writes
     * behind the reads among them name, to a fixed point -- a read joins a
     * write whose expression may itself be a handoff the producer
     * forwarded.  An attach or a read outside it is recorded as a diagnostic
     * rather than dropped in silence, because "the closure did not grow" and
     * "the closure grew and I did not say why" read the same in a report.</p>
     */
    private static Set<String> readSymbols(Corpus corpus,
                                           List<OccurrenceAddress> group) {
        Set<String> named = new LinkedHashSet<String>();
        List<ReadRow> reads = new ArrayList<ReadRow>();
        for (OccurrenceAddress member : group) {
            // The runtime publishes a predicate over a propagated value as a
            // REFERENCE into the session's expression table -- "(not
            // EXPR.7e13ce0f9e7944ea)" -- so reading the token as a name asks
            // about nothing: every read the path really rests on looks
            // unread, and the closure says so in rows that are not true.
            // The ONE lowering resolves it, the same routine the composer
            // and the flip query run (CONTRACT-SPEC: one lowering, shared).
            for (Corpus.RecordedPath path : corpus.pathsOf(member)) {
                for (DecisionRow decision : path.decisions) {
                    SmtText.symbols(FlipQuery.statedTerm(corpus,
                            path.sessionId, decision.term()), named);
                }
            }
            for (TargetRow target : corpus.targetsOn(member)) {
                SmtText.symbols(FlipQuery.statedTerm(corpus,
                        target.sessionId(), target.phiTerm()), named);
            }
            reads.addAll(corpus.readsOn(member));
        }
        Set<String> settled = new LinkedHashSet<String>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (String symbol : new ArrayList<String>(named)) {
                if (!settled.add(symbol)) continue;
                for (ReadRow row : reads) {
                    if (!symbol.equals(row.symbol())) continue;
                    for (WriteRow write : eligibleWrites(corpus, row)) {
                        SmtLowering.Lowered lowered =
                                corpus.lowering(write.sessionId())
                                        .lower(write.expressionRef());
                        grew |= named.addAll(lowered.declarations().keySet());
                    }
                }
            }
        }
        return named;
    }

    /**
     * The writes one read could have taken its value from.
     *
     * <p>The observed one, and every write by an occurrence HB-CONCURRENT
     * with the reader (R-I7.1).  The concurrency rule is
     * {@code d3.smt.Arms}', so the closure grows by exactly the writers the
     * composition will offer the solver as alternatives.</p>
     */
    private static List<WriteRow> eligibleWrites(Corpus corpus, ReadRow row) {
        List<WriteRow> eligible = new ArrayList<WriteRow>();
        for (WriteRow write : corpus.writesOf(row.sessionId(),
                SmtLowering.locationKey(row.location()))) {
            if (write.version() == row.observedVersion()
                    || corpus.arms().concurrent(row.endpoint().occurrence(),
                            write.endpoint().occurrence(), row.sessionId())) {
                eligible.add(write);
            }
        }
        return eligible;
    }

    /** A delivery this anchor's paths never read: recorded, not planned. */
    private static void unread(List<GapRow> gaps, String sessionId,
                               String subject, String what) {
        gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, subject,
                "no admitted path of this occurrence reads this " + what
                        + ", so its producer is not a task"));
    }

    /**
     * The producer of one attach, and the producers of every handoff its
     * delivery is forwarded from.
     *
     * <p>A key id an NN hands a balancer, which hands it to a data node, is
     * one value with two interactions; the first is in the closure of the
     * second's consumer.  Following the exported expression's own nested
     * handoff symbols is what makes the chain end at the mint rather than at
     * the first hop.</p>
     */
    private static void producers(Corpus corpus, AttachRow attach,
                                  List<OccurrenceAddress> into,
                                  List<GapRow> gaps, Set<String> seen) {
        if (attach == null || !seen.add(attach.endpoint().id())) return;
        if (attach.producer() == null) {
            gaps.add(GapRow.of(attach.sessionId(), GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                    "attach is unpaired: no producer endpoint to close over"));
            return;
        }
        crossCheck(attach, gaps);
        into.add(attach.producer().occurrence());
        SessionReader session = corpus.session(attach.sessionId());
        if (session == null) return;
        for (ExportRow export : corpus.exportsAt(attach.producer())) {
            SessionReader exporting = corpus.session(export.sessionId());
            if (exporting == null) continue;
            SmtLowering.Lowered lowered = corpus.lowering(export.sessionId())
                    .lower(export.expressionRef());
            for (Map.Entry<String, String> symbol
                    : lowered.declarations().entrySet()) {
                AttachRow nested = corpus.attach(export.sessionId(),
                        symbol.getKey());
                if (nested != null) {
                    into.add(nested.endpoint().occurrence());
                    producers(corpus, nested, into, gaps, seen);
                }
            }
        }
    }

    /**
     * The recorded pairing against the consumer's own causal context.
     *
     * <p>Under identity v3 a consumer started by a message carries its
     * producer's endpoint id INSIDE its own id, so the run states the pairing
     * twice: once as the attach row's producer endpoint, once as the
     * occurrence's {@code Anchor} context.  The ROW is the authority -- it is
     * the pairing the run recorded -- and the context is a cross-check: when
     * the two disagree, the closure still follows the row and a reader is
     * told, because two statements about one interaction that do not agree is
     * the runtime's defect to fix and not this stage's to arbitrate.  A
     * {@code Root} or {@code Lost} context raises nothing: there is no anchor
     * to disagree with, and an unpaired attach already says
     * {@code LINEAGE_LOST}.</p>
     */
    private static void crossCheck(AttachRow attach, List<GapRow> gaps) {
        CausalContext context = attach.endpoint().occurrence().context();
        if (!(context instanceof CausalContext.Anchor)) return;
        String anchored = ((CausalContext.Anchor) context)
                .producerEndpointId();
        String recorded = attach.producer().id();
        if (anchored.equals(recorded)) return;
        gaps.add(GapRow.of(attach.sessionId(), GapKind.TOPOLOGY_DIVERGENCE,
                GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                "the recorded pairing names producer endpoint " + recorded
                        + " and the consumer's causal anchor names "
                        + anchored + "; the closure follows the recorded "
                        + "pairing"));
    }

    /**
     * The co-occurrences one occurrence is state-connected to: the writers
     * and readers of a location it touches, on its own node.
     */
    private static List<OccurrenceAddress> stateConnected(
            Corpus corpus, OccurrenceAddress occurrence) {
        Set<LocationId> locations = new LinkedHashSet<LocationId>();
        for (ReadRow read : corpus.readsOn(occurrence)) {
            locations.add(read.location());
        }
        for (WriteRow write : corpus.writesOn(occurrence)) {
            locations.add(write.location());
        }
        Set<String> connected = new LinkedHashSet<String>();
        for (LocationId location : locations) {
            connected.addAll(corpus.touching(occurrence, location));
        }
        connected.remove(occurrence.id());
        List<OccurrenceAddress> factor = new ArrayList<OccurrenceAddress>();
        for (String id : connected) {
            OccurrenceAddress member = corpus.occurrence(id);
            if (member != null) factor.add(member);
        }
        return factor;
    }

    /**
     * Every seed occurrence that decided something over a SYMBOL.
     *
     * <p>Owner's ruling, 2026-09-15: a branch that carries a symbol IS a flip
     * target.  The static graph is used only to decide what to TRACK -- the
     * root-dependence slice picks the carriers, the occurrences to replay and
     * the BRANCHES TO FLIP -- so a decision the recording published a
     * predicate for is a candidate wherever inside G_S^W it sits, and
     * whether that flip is producible is the solver's verdict
     * (UNPRODUCIBLE_ANSWER when a model lands on a symbol nothing binds,
     * HANDOVER SS1.5) rather than a pre-filter here.  It does not have to be
     * reachable from the anchor through rows, and on 17960 it cannot be: the
     * seed runs the marker's TRUE arm, where {@code deleteSnapshot} defers
     * and the counter decrement never executes, so the anchor's dependence on
     * the deletion region exists only on the arm the flip would create.  A
     * closure that waits for a row stating that dependence waits for the
     * replay it is supposed to ask for.</p>
     *
     * <p>Such an occurrence is a TASK -- one focused replay, its own
     * obligations {@code prefix and not d} -- and NOT a closure member: it
     * opens no slot and joins no family until its rows connect it, which the
     * per-wave recomputation does on its own (INTERACTION-ID SS8 case 1). The
     * test is rows only: an {@code ActivationRow} of the seed session with
     * {@code instrumented == true} and a {@code DecisionRow} of that
     * occurrence that states a predicate -- {@link FlipQuery#flippable}, the
     * same rule the obligation factory cuts candidates with, so a decision
     * cannot be a task's reason and not its candidate.</p>
     *
     * @param planned task ids the closure already holds, which are not
     *                planned twice and stay closure members
     */
    public static List<Task> symbolicDecision(Corpus corpus,
                                              Set<String> planned) {
        String seed = corpus.seedSessionId();
        SessionReader session = seed.isEmpty() ? null : corpus.session(seed);
        if (session == null) return new ArrayList<Task>();
        Set<String> instrumented = new LinkedHashSet<String>();
        for (ActivationRow activation : session.activations()) {
            if (activation.instrumented()) {
                instrumented.add(activation.occurrence().id());
            }
        }
        Map<String, OccurrenceAddress> deciding =
                new LinkedHashMap<String, OccurrenceAddress>();
        for (DecisionRow decision : session.decisions()) {
            OccurrenceAddress occurrence = decision.occurrence();
            if (!instrumented.contains(occurrence.id())) continue;
            if (deciding.containsKey(occurrence.id())) continue;
            if (!FlipQuery.flippable(corpus, seed, decision)) continue;
            deciding.put(occurrence.id(), occurrence);
        }
        List<Task> tasks = new ArrayList<Task>();
        for (OccurrenceAddress occurrence : deciding.values()) {
            String taskId = taskId(occurrence);
            if (planned.contains(taskId)) continue;
            // No factor: a factor is the state-connected unit the closure
            // computed, and this occurrence is not in the closure yet.
            tasks.add(Task.of(taskId, occurrence,
                    new ArrayList<OccurrenceAddress>(), seed));
        }
        return tasks;
    }

    /** The session an occurrence was first recorded in. */
    private static String seedSession(Corpus corpus,
                                      OccurrenceAddress occurrence) {
        for (SessionReader session : corpus.sessions()) {
            if (corpus.activation(session.sessionId(), occurrence) != null
                    || !corpus.decisionsOf(session.sessionId(), occurrence)
                    .isEmpty()) {
                return session.sessionId();
            }
        }
        return "";
    }
}
