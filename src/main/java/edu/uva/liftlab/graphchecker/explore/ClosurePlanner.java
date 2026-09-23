package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

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
 * The target's closure: what its failure can depend on, and the branches
 * exploration may flip in it (CLOSURE-V2 SS1-SS2).
 *
 * <p>Demand starts at the ANNOTATED TARGET and not at a region: the operands
 * of the fatal predicate, as the VM's own expression states them, and the
 * branch sites the target site is control-dependent on
 * ({@link StaticScopeMap}'s guard set).  A port the region attached and a
 * field it read that no demanded value rests on are deliveries this failure
 * does not use.</p>
 *
 * <p>Each boundary variable of a demanded value grows the closure two ways,
 * and both are needed:</p>
 * <ul>
 *   <li>by ROWS -- the producer that paired with this attach, the writers
 *       whose versions this read could have observed -- which is what the
 *       recording states;</li>
 *   <li>by the STATIC MAP -- every occurrence of a region holding a write
 *       site of that location, or an export site of that port -- which is
 *       what the recording CANNOT state.  On 17960 the seed runs the
 *       marker's true arm, where {@code deleteSnapshot} defers and the
 *       counter decrement never executes: no row of any session puts the
 *       deletion region in the anchor's closure, and a closure that waits
 *       for one waits for the replay it is supposed to ask for.</li>
 * </ul>
 *
 * <p>And a third way, because the first two ask only about what a ROW says:
 * a value this occurrence contributed -- its export, its write -- states the
 * shared state it RESTS ON inside its own expression, and no read row of
 * this occurrence names it ({@link #statedReads}, E2).  The NameNode's
 * export of its key set is the removal scan of the previous tick; without
 * that edge no closure holds the scan and no query declares the clock it
 * read.</p>
 *
 * <p>A static candidate is ON ONE NODE, because a CONCRETE location lives in
 * one process and a message was sent by one process: a write site's
 * candidates are the occurrences on the READER's node (N1, {@link #writers}),
 * an export site's are those on the PAIRED PRODUCER's node (N2,
 * {@link #producers}).  The class field a carrier names exists in every JVM
 * that loaded it, and none of the others hold the heap this read observed --
 * on the hdfs-11741 campaign #4 corpus (2026-09-20) admitting them gave wave
 * 1 246 obligations, 124 of them the Balancer's own
 * {@code removeExpiredKeys#u15} flips in worlds where nothing on the
 * Balancer's path to the target changed.</p>
 *
 * <p>A static candidate is a member like any other -- it opens slots and
 * joins families -- and what it is demanded FOR is its own write or export:
 * the branches that decide whether that write happens are its guard set, and
 * those are the only branches a wave flips in it.  A candidate region no
 * session activated at all is named (INTERACTION-ID SS8 case 2) and is not a
 * task: there is no run to focus.</p>
 */
public final class ClosurePlanner {
    /** How many tasks one anchor may open, before the closure is truncated. */
    public static final int DEFAULT_MAX_TASKS = 64;

    /** In the closure because the rows put it there. */
    public static final String CLOSURE_MEMBER = "CLOSURE_MEMBER";
    /** In the closure because it sent a message a member served. */
    public static final String CONTROL_PRODUCER = "CONTROL_PRODUCER";
    /** In the closure because it holds a static write site of a location. */
    public static final String STATIC_CANDIDATE_WRITER =
            "STATIC_CANDIDATE_WRITER";
    /** In the closure because it holds a static export site of a port. */
    public static final String STATIC_CANDIDATE_PRODUCER =
            "STATIC_CANDIDATE_PRODUCER";

    private ClosurePlanner() {
    }

    /** The closure of one anchor, and what could not be named in it. */
    public static final class Plan {
        public final List<Task> tasks;
        public final List<GapRow> gaps;
        /** task id -> why that occurrence is in the closure. */
        public final Map<String, String> why;
        /** task id -> the site ids this wave may flip in it. */
        public final Map<String, Set<String>> flipSites;

        private Plan(List<Task> tasks, List<GapRow> gaps,
                     Map<String, String> why,
                     Map<String, Set<String>> flipSites) {
            this.tasks = Collections.unmodifiableList(tasks);
            this.gaps = Collections.unmodifiableList(gaps);
            this.why = Collections.unmodifiableMap(why);
            this.flipSites = Collections.unmodifiableMap(flipSites);
        }
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks, StaticScopeMap scope) {
        List<GapRow> gaps = new ArrayList<GapRow>();
        Map<String, Demand> demands = new LinkedHashMap<String, Demand>();
        Deque<String> pending = new ArrayDeque<String>();
        Demand start = new Demand(anchor, CLOSURE_MEMBER, true);
        // The anchor's flips are the GUARD SET of the annotated target and
        // nothing else (CLOSURE-V2 SS1).  The target site itself is a throw,
        // which is not a branch and which no DecisionRow stands at; the
        // branch that decides whether the throw is reached is one of its
        // guards, and on 17960 that is the fatal predicate's own site.
        for (StaticScopeMap.Site target : scope.targetSites()) {
            start.flipSites.addAll(target.guards);
        }
        demands.put(anchor.id(), start);
        pending.add(anchor.id());
        Set<String> truncated = new LinkedHashSet<String>();
        while (!pending.isEmpty()) {
            Demand demand = demands.get(pending.remove());
            demand.dirty = false;
            for (Demand next : successors(corpus, scope, demand, gaps)) {
                Demand held = demands.get(next.occurrence.id());
                if (held != null) {
                    if (held.absorb(next) && !held.dirty) {
                        held.dirty = true;
                        pending.add(held.occurrence.id());
                    }
                    continue;
                }
                if (demands.size() >= maxTasks) {
                    truncated.add(next.occurrence.render());
                    continue;
                }
                demands.put(next.occurrence.id(), next);
                pending.add(next.occurrence.id());
            }
        }
        if (!truncated.isEmpty()) {
            // A truncated closure composes a formula that is missing
            // producers the anchor's paths read, and a composition missing an
            // arm is not a weaker claim -- it is an unsound one.  The
            // fixed point still runs to the end for the demands it did
            // admit, so what this refusal names is exactly what was left
            // out.
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                    GapClass.BLOCKING, anchor.render(),
                    "closure truncated at " + maxTasks + " tasks; "
                            + truncated.size() + " occurrences were not "
                            + "planned, so this anchor's closure is "
                            + "incomplete: " + truncated));
        }
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flips =
                new LinkedHashMap<String, Set<String>>();
        for (Demand demand : demands.values()) {
            String seed = seedSession(corpus, demand.occurrence);
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
                        demand.occurrence.render(),
                        "no session of this corpus activated this occurrence "
                                + "or recorded a decision of it, so no replay "
                                + "can be focused on it and it is not a task"));
                continue;
            }
            String taskId = taskId(demand.occurrence);
            tasks.add(Task.of(taskId, demand.occurrence,
                    stateConnected(corpus, demand.occurrence), seed));
            why.put(taskId, demand.why);
            // The flip sites of a task: the guards of its demanded sites,
            // and every FAULT decision of the occurrence (DESIGN4 SS1.4) --
            // a fault guards everything the send would have produced.
            Set<String> sites = new LinkedHashSet<String>(demand.flipSites);
            sites.addAll(corpus.faultSites(demand.occurrence));
            flips.put(taskId, sites);
        }
        return new Plan(tasks, gaps, why, flips);
    }

    /** One task's id: the occurrence it focuses and nothing else. */
    public static String taskId(OccurrenceAddress focused) {
        return ArtifactIO.digest("task|" + focused.id(), 16);
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

    /** What one occurrence is demanded for, and where its flips may be. */
    private static final class Demand {
        private final OccurrenceAddress occurrence;
        /** session|expressionRef of the values this occurrence contributed. */
        private final Set<String> contributed = new LinkedHashSet<String>();
        private final Set<String> flipSites = new LinkedHashSet<String>();
        private final boolean anchor;
        private String why;
        private boolean dirty;

        private Demand(OccurrenceAddress occurrence, String why,
                       boolean anchor) {
            this.occurrence = occurrence;
            this.why = why;
            this.anchor = anchor;
        }

        /**
         * Folds another reason to demand this occurrence into this one.
         *
         * <p>{@code CLOSURE_MEMBER} wins: an occurrence the rows connect is
         * in the closure whatever the static map also says about it, and the
         * static reason is what is left when no row does.</p>
         *
         * @return whether this demand grew
         */
        private boolean absorb(Demand other) {
            boolean grew = contributed.addAll(other.contributed);
            grew |= flipSites.addAll(other.flipSites);
            if (CLOSURE_MEMBER.equals(other.why)
                    && !CLOSURE_MEMBER.equals(why)) {
                why = CLOSURE_MEMBER;
                grew = true;
            }
            return grew;
        }
    }

    /**
     * Everything one demand reaches: the producers of the interactions its
     * demanded values rest on and the writers of the versions they read, by
     * rows and by the static map.
     */
    private static List<Demand> successors(Corpus corpus, StaticScopeMap map,
                                           Demand demand, List<GapRow> gaps) {
        List<OccurrenceAddress> group = new ArrayList<OccurrenceAddress>();
        group.add(demand.occurrence);
        group.addAll(stateConnected(corpus, demand.occurrence));
        // The group is ONE symbolic unit -- a factor member exists because
        // its writes feed the focused occurrence's reads -- so what "the
        // demanded values read" is asked of the group, not of each member
        // alone: the addKeys activation decides nothing itself, and the
        // handoff it writes into the map is read by the occurrence beside it.
        Set<String> demanded = demanded(corpus, demand, group);
        List<Demand> next = new ArrayList<Demand>();
        for (OccurrenceAddress member : group) {
            if (!member.equals(demand.occurrence)) {
                // A factor member is in the closure because the occurrence it
                // is state-connected to is, so it INHERITS that reason: being
                // somebody's factor is not a reason of its own, and calling
                // it one would report a static candidate's sibling as a
                // member the rows connected.
                next.add(new Demand(member, demand.why, false));
            }
            for (AttachRow attach : corpus.attachesOn(member)) {
                if (!demanded.contains(attach.symbol())) {
                    unread(gaps, attach.sessionId(), attach.endpoint()
                            .toString(), "handoff");
                    continue;
                }
                producers(corpus, map, attach, next, gaps);
            }
            for (ReadRow row : corpus.readsOn(member)) {
                if (!demanded.contains(row.symbol())) {
                    unread(gaps, row.sessionId(), row.endpoint().toString(),
                            "state read");
                    continue;
                }
                writers(corpus, map, row, next, gaps);
            }
        }
        statedReads(corpus, map, demand, next, gaps);
        controlProducer(corpus, demand, next);
        return next;
    }

    /**
     * The occurrence that SENT the message a demanded occurrence served is
     * in the closure as its control producer: it contributes no value, but
     * its fault point decides whether the message -- and everything the
     * served occurrence produced -- exists at all (DESIGN4 SS1.4).  The
     * pairing is the served occurrence's ANCHOR, which is the sender's
     * producer endpoint, and the schedule's SEND event states which
     * occurrence minted it.
     */
    private static void controlProducer(Corpus corpus, Demand demand,
                                        List<Demand> next) {
        if (!(demand.occurrence.context() instanceof CausalContext.Anchor)) {
            return;
        }
        OccurrenceAddress sender = corpus.senderOf(
                ((CausalContext.Anchor) demand.occurrence.context())
                        .producerEndpointId());
        if (sender != null) next.add(new Demand(sender, CONTROL_PRODUCER, false));
    }

    /**
     * E2 -- A DEMANDED EXPORT STATES THE SHARED STATE IT RESTS ON.
     *
     * <p>What an occurrence is demanded FOR is its own write or export
     * ({@link Demand#contributed}), and the VM publishes that value's reads
     * of shared state only INSIDE the expression: a
     * {@code ReadFromExpression}, or the {@code ConsumerBoundaryExpression}
     * over one, carrying a {@code location} and a {@code readEventId}.  No
     * {@code ReadRow} of the producing occurrence names them, so
     * {@link #writers} was never asked about them and the state the
     * delivery is MADE OF was in no closure.</p>
     *
     * <p>So each resolved read grows the closure exactly as a read row
     * would: the writer of the version the producer had in hand, and the
     * static write sites of that location's carrier ON THE PRODUCER'S OWN
     * NODE (N1 -- the map it read is an object in its own heap).  The
     * writer is demanded for ITS expression in turn, so a chain of ticks
     * closes by the same rule.  {@link Corpus#expressionStateReads} is the
     * one resolution, shared with the composer's
     * {@code ComposedFamilies.expressionWrites}.</p>
     *
     * <p>Never the anchor: the anchor is demanded for its fatal predicate,
     * whose operands are what {@link #demanded} already walks, and it
     * contributes no delivery of its own.</p>
     *
     * <p>Without this edge, on the hdfs-11741 campaign #4 corpus
     * (2026-09-20), the NameNode's export region records no state read at
     * all -- 1324 instance reads and not one map read -- so once the
     * cross-node static fan-out of N1 was gone, nn0's
     * {@code removeExpiredKeys#u15} and {@code updateKeys#u2} were in no
     * flip set and the rotation flip the witness needs was proposed
     * nowhere.</p>
     */
    private static void statedReads(Corpus corpus, StaticScopeMap map,
                                    Demand demand, List<Demand> into,
                                    List<GapRow> gaps) {
        if (demand.anchor) return;
        for (String contributed : demand.contributed) {
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            for (Corpus.StateRead read : corpus.expressionStateReads(
                    sessionId, contributed.substring(split + 1))) {
                writersOfVersion(corpus, map, sessionId, demand.occurrence,
                        read.locationKey(), read.write().version(),
                        demand.occurrence.render(),
                        read.locationKey() + " (read at event "
                                + read.readEventId() + ")", into, gaps);
            }
        }
    }

    /**
     * The symbols one occurrence's demanded values name.
     *
     * <p>Three sources and no fourth: the fatal predicate of an anchor, the
     * decisions at the sites the demand's GUARD SET names, and the
     * expressions this occurrence contributed to the closure (its write or
     * its export).  Then the fixed point over reads: a demanded read joins
     * the writes it could have observed, and what those wrote is demanded in
     * turn -- a write may itself carry a handoff its producer forwarded.</p>
     *
     * <p>The runtime publishes a predicate over a propagated value as a
     * REFERENCE into the session's expression table -- "(not
     * EXPR.7e13ce0f9e7944ea)" -- so reading the token as a name asks about
     * nothing.  The ONE lowering resolves it, the same routine the composer
     * and the flip query run (CONTRACT-SPEC: one lowering, shared).</p>
     */
    private static Set<String> demanded(Corpus corpus, Demand demand,
                                        List<OccurrenceAddress> group) {
        Set<String> named = new LinkedHashSet<String>();
        List<ReadRow> reads = new ArrayList<ReadRow>();
        for (OccurrenceAddress member : group) {
            for (Corpus.RecordedPath path : corpus.pathsOf(member)) {
                for (DecisionRow decision : path.decisions) {
                    if (!demand.flipSites.contains(decision.siteId())) {
                        continue;
                    }
                    reaches(corpus, path.sessionId, FlipQuery.statedTerm(
                            corpus, path.sessionId, decision.term()), named);
                }
            }
            if (demand.anchor) {
                for (TargetRow target : corpus.targetsOn(member)) {
                    reaches(corpus, target.sessionId(),
                            FlipQuery.statedTerm(corpus, target.sessionId(),
                                    target.phiTerm()), named);
                }
            }
            reads.addAll(corpus.readsOn(member));
        }
        for (String contributed : demand.contributed) {
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            reaches(corpus, sessionId, lowering.lower(
                    contributed.substring(split + 1)).text(), named);
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
                        grew |= reaches(corpus, write.sessionId(),
                                corpus.lowering(write.sessionId())
                                        .lower(write.expressionRef()).text(),
                                named);
                    }
                }
            }
        }
        return named;
    }

    /**
     * The recorded symbols one lowered term reaches, into {@code named}.
     *
     * <p>Reachable from it, not visible in it: a container version is
     * lowered once and named, so a guard over a map read is
     * {@code (not (= container_dag__... nullRef))} and the recording's own
     * symbols -- the handoffs and roots that were PUT into that map -- are
     * inside the body behind the name.  {@link SmtLowering#reachedSymbols}
     * is the one answer, the same one the flip query binds its variables
     * by; asking {@code SmtLowering.symbols} instead left 11741's anchor
     * demanding a single {@code container_dag__} name that matches no row,
     * so every read and every attach of its group was reported
     * {@code ADMISSION_GAP} and the closure never left the target's node.
     * </p>
     *
     * <p>And the STATE behind the name too -- the v_C rule (CLOSURE-V2).
     * A demand is what the failure can DEPEND on, not what its text spells:
     * a container version is the value of the read that observed it, and
     * that read's row is the only thing that names the cell, because the
     * chain in the body ends at the mutations and, for 11741's
     * {@code allKeys}, at an empty base.  The flip query asks the other
     * half alone -- it BINDS names, and a name its text never mentions is a
     * variable nothing constrains.</p>
     *
     * @return whether the set grew
     */
    private static boolean reaches(Corpus corpus, String sessionId,
                                   String text, Set<String> named) {
        SmtLowering lowering = corpus.lowering(sessionId);
        if (lowering == null) return false;
        Set<String> reached = new LinkedHashSet<String>();
        lowering.reachedSymbols(text, reached, reached);
        return named.addAll(reached);
    }

    /**
     * The writes one read could have taken its value from.
     *
     * <p>The observed one, and every write by an occurrence HB-CONCURRENT
     * with the reader (R-I7.1).  The concurrency rule is
     * {@code smt.Arms}', so the closure grows by exactly the writers the
     * composition will offer the solver as alternatives.</p>
     */
    private static List<WriteRow> eligibleWrites(Corpus corpus, ReadRow row) {
        return eligibleWrites(corpus, row.sessionId(),
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), row.endpoint().occurrence());
    }

    /**
     * The same, for a read stated by an expression rather than by a row.
     *
     * <p>One rule and one implementation: a read is a session, a location
     * key, the version it observed and the occurrence that made it,
     * whether the runtime published it as a {@link ReadRow} or only inside
     * the expression of the value it fed (E2).  It is the CORPUS's
     * ({@link Corpus#eligibleWrites}), because the same relation is the
     * causal graph's shared-state in-edge ({@link Corpus#upstreamOf}) and
     * two spellings of it would be two answers to "which writer could this
     * read have observed".</p>
     */
    private static List<WriteRow> eligibleWrites(Corpus corpus,
                                                 String sessionId,
                                                 String locationKey,
                                                 long observedVersion,
                                                 OccurrenceAddress reader) {
        return corpus.eligibleWrites(sessionId, locationKey, observedVersion,
                reader);
    }

    /** A delivery this anchor's paths never read: recorded, not planned. */
    private static void unread(List<GapRow> gaps, String sessionId,
                               String subject, String what) {
        gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, subject,
                "no demanded value of this occurrence rests on this " + what
                        + ", so its producer is not a task"));
    }

    /**
     * Who could have produced one demanded attach: the endpoint that paired
     * with it in this session, and every static export site of its port.
     *
     * <p>The nested case -- a key id an NN hands a balancer, which hands it
     * to a data node -- needs no walk of its own: the producer is demanded
     * FOR its export, so the leaves of that export are its demand and its
     * own attaches are found when it is processed.</p>
     *
     * <p><b>N2 -- a message was sent by ONE process.</b>  The static export
     * sites of a port are candidates only on the node of the attach's PAIRED
     * producer ({@code attach.producer().occurrence().node()}): the arrival
     * this attach records carries the bytes some one JVM put on the wire, and
     * an occurrence on another node did not put them there.  Unfiltered, the
     * export sites of {@code block-key-id} made every {@code PBHelper.convert}
     * occurrence on dn0, dn1 AND the balancer a candidate producer of a
     * message nn0 sent -- which is how, on the hdfs-11741 campaign #4 corpus
     * (2026-09-20), wave 1 proposed 246 obligations, 124 of them the
     * Balancer's own {@code removeExpiredKeys#u15} flips in worlds where
     * nothing on the Balancer's path to the target changed.</p>
     *
     * <p>An UNPAIRED attach states no sender, so nothing is restricted there
     * and every node's export sites stay candidates, beside the
     * {@code LINEAGE_LOST} row that says why.</p>
     */
    private static void producers(Corpus corpus, StaticScopeMap map,
                                  AttachRow attach, List<Demand> into,
                                  List<GapRow> gaps) {
        String portId = attach.endpoint().site();
        List<StaticScopeMap.Site> exports = map.exportsOf(portId);
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : exports) {
            guards.addAll(site.guards);
        }
        if (attach.producer() == null) {
            gaps.add(GapRow.of(attach.sessionId(), GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                    "attach is unpaired: no producer endpoint to close over"));
        } else {
            crossCheck(attach, gaps);
            Demand paired = new Demand(attach.producer().occurrence(),
                    CLOSURE_MEMBER, false);
            paired.flipSites.addAll(guards);
            for (ExportRow export : corpus.exportsAt(attach.producer())) {
                paired.contributed.add(export.sessionId() + "|"
                        + export.expressionRef());
            }
            into.add(paired);
        }
        // N2: the sender, or null when the attach names none -- and null is
        // "every node", which is what an unpaired attach leaves open.
        NodeId sender = attach.producer() == null ? null
                : attach.producer().occurrence().node();
        for (StaticScopeMap.Site site : exports) {
            candidates(corpus, map, site, STATIC_CANDIDATE_PRODUCER, guards,
                    into, gaps, attach.sessionId(), "port " + portId, sender);
        }
    }

    /**
     * Who could have written one demanded read: the writers of the versions
     * it could have observed, and every static write site of its location.
     *
     * <p>The location is named the way the recording names it and the map is
     * named the way the program text does, so the two are joined through the
     * site of a write the recording DID observe: that site's carrier is this
     * location's carrier, and the carrier's other write sites are the
     * candidates.  A demanded location no session ever wrote has no carrier
     * to look up, and that is said rather than guessed.</p>
     *
     * <p><b>N1 -- a concrete location lives in ONE process.</b>  A shared
     * state edge is an incoming edge from Writers_W(l) where {@code l} is the
     * CONCRETE location -- the VM's own object identity (SS4), which
     * distinguishes the instances of one class field -- so the static
     * candidates are restricted to occurrences on the node of the READING
     * occurrence ({@code row.endpoint().occurrence().node()}).  The carrier is
     * the class field the map names -- {@code BlockTokenSecretManager.allKeys}
     * -- and its write sites exist in every JVM that loads the class, but only
     * the reader's JVM holds the heap this read observed: no occurrence
     * elsewhere can have written it.  Unfiltered, dn1's {@code allKeys} read
     * admitted the Balancer's three KeyManager refreshes and dn0's refresh as
     * candidate writers, and on the hdfs-11741 campaign #4 corpus
     * (2026-09-20) wave 1 proposed 246 obligations, 124 of them the Balancer's
     * own {@code removeExpiredKeys#u15} flips in worlds where nothing on the
     * Balancer's path to the target changed.</p>
     *
     * <p>The ROW half is untouched: {@link #eligibleWrites} is already per
     * session and per location KEY, and a location key names one object of one
     * run.</p>
     */
    private static void writers(Corpus corpus, StaticScopeMap map,
                                ReadRow row, List<Demand> into,
                                List<GapRow> gaps) {
        writersOfVersion(corpus, map, row.sessionId(),
                row.endpoint().occurrence(),
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), row.endpoint().toString(),
                String.valueOf(row.location()), into, gaps);
    }

    /**
     * The closure's growth by ONE read of ONE version of ONE location.
     *
     * <p>The body of {@link #writers}, taken as its own routine because E2
     * asks the same question of a read the runtime published only inside an
     * expression: a read is a session, a location key, the version it
     * observed and the occurrence that made it, and the answer must not
     * depend on which file the runtime happened to state it in.</p>
     *
     * @param subject what a diagnostic about this read is addressed at
     * @param located how the location reads in that diagnostic
     */
    private static void writersOfVersion(Corpus corpus, StaticScopeMap map,
                                         String sessionId,
                                         OccurrenceAddress reader,
                                         String locationKey,
                                         long observedVersion,
                                         String subject, String located,
                                         List<Demand> into,
                                         List<GapRow> gaps) {
        Set<String> carriers = carriersOf(corpus, map, locationKey);
        for (WriteRow write : eligibleWrites(corpus, sessionId, locationKey,
                observedVersion, reader)) {
            Demand paired = new Demand(write.endpoint().occurrence(),
                    CLOSURE_MEMBER, false);
            paired.contributed.add(write.sessionId() + "|"
                    + write.expressionRef());
            paired.flipSites.addAll(guardsAt(map, write.endpoint().site()));
            into.add(paired);
        }
        if (carriers.isEmpty() && map.stated()) {
            gaps.add(GapRow.of(sessionId, GapKind.DECLARATION_MISSING,
                    GapClass.DIAGNOSTIC, subject,
                    "no recorded write of " + located + " matches a "
                            + "write site of the static map, so this "
                            + "location's carrier is unnamed and no static "
                            + "candidate writer of it can be"));
            return;
        }
        // N1: the heap this read observed is the reading JVM's own.
        for (String carrier : carriers) {
            for (StaticScopeMap.Site site : map.writersOf(carrier)) {
                candidates(corpus, map, site, STATIC_CANDIDATE_WRITER,
                        new LinkedHashSet<String>(site.guards), into, gaps,
                        sessionId, "carrier " + carrier, reader.node());
            }
        }
    }

    /** Every carrier the static map names for one location key. */
    private static Set<String> carriersOf(Corpus corpus, StaticScopeMap map,
                                          String locationKey) {
        Set<String> carriers = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            for (WriteRow write : corpus.writesOf(session.sessionId(),
                    locationKey)) {
                carriers.addAll(map.carriersAt(write.endpoint().site(),
                        write.javaType()));
            }
        }
        return carriers;
    }

    /**
     * What a writer may flip about the write it contributed.
     *
     * <p>The recording states a bytecode index inside a method and the map
     * states a unit index, so the join is the method: a writer's flip sites
     * are the guards of every static write site IN THE METHOD it wrote from.
     * A method with two write sites offers both guard sets, which is one
     * flip too many rather than one too few.</p>
     */
    private static Set<String> guardsAt(StaticScopeMap map,
                                        String recordedSite) {
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : map.sitesAt(recordedSite)) {
            guards.addAll(site.guards);
        }
        return guards;
    }

    /**
     * Every occurrence of the region one static site belongs to, ON ONE NODE.
     *
     * <p>A region the corpus holds no activation of is INTERACTION-ID SS8
     * case 2: the candidate exists in the program and not in any recording,
     * so it is named and no task is opened -- a replay cannot be focused on
     * an occurrence nothing ran.</p>
     *
     * <p>{@code node} is the process the candidate must have run in: the
     * READER's node for a static write site (N1 -- a concrete location lives
     * in one JVM's heap) and the PAIRED PRODUCER's node for a static export
     * site (N2 -- a message was sent by one process).  A site's region runs on
     * every node that loaded the class, and a candidate elsewhere could not
     * have written this location or sent this message; admitting it cost the
     * hdfs-11741 campaign #4 corpus (2026-09-20) 124 of wave 1's 246
     * obligations, all of them Balancer flips reachable from neither.
     * {@code null} means "no node was stated" -- an unpaired attach -- and
     * every node's occurrences stay candidates.</p>
     *
     * <p>The "never activated" diagnostic follows the same restriction: it is
     * asked of THIS node's activations, and its detail names the node, so a
     * region another node ran and this one did not is reported as the growth
     * it would actually need.</p>
     */
    private static void candidates(Corpus corpus, StaticScopeMap map,
                                   StaticScopeMap.Site site,
                                   String why, Set<String> guards,
                                   List<Demand> into, List<GapRow> gaps,
                                   String sessionId, String what,
                                   NodeId node) {
        boolean ran = false;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!holds(map, occurrence.regionId(), site)
                    || (node != null && !node.equals(occurrence.node()))
                    || !activated(corpus, occurrence)) {
                continue;
            }
            ran = true;
            Demand candidate = new Demand(occurrence, why, false);
            candidate.flipSites.addAll(guards);
            into.add(candidate);
        }
        if (ran) return;
        gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, site.regionId,
                "a static " + (STATIC_CANDIDATE_WRITER.equals(why)
                        ? "write" : "export") + " site of " + what + " is in "
                        + site.siteId + ", and no session of this corpus "
                        + "activated that region"
                        + (node == null ? "" : " on " + node.render())
                        + ": the retained set would have "
                        + "to grow before it can be a task (INTERACTION-ID "
                        + "SS8 case 2)"));
    }

    /**
     * Whether one occurrence's region would RUN one static site.
     *
     * <p>By HOLDING, not by equality of region ids.  A declared region
     * entered synchronously inside another region's occurrence opens none of
     * its own, so a site of region R is recorded under an occurrence of the
     * enclosing R' that holds R's method -- and the static map publishes a
     * site under its INNERMOST holder alone ({@code
     * StaticScopeMap#holders}), so R' never appears beside that site and
     * equality found no occurrence at all.  The candidate then read as
     * "no session activated that region" and no task was opened for a
     * writer the corpus had run.</p>
     *
     * <p>The map's method set is the same {@code Region} rows {@code
     * holders} reads, asked the other way round.  An occurrence whose region
     * the map does not know -- no skeletons beside the map, a {@code ROLE.}
     * occurrence no region declares -- falls back to comparing the ids,
     * which is what this join was before.</p>
     */
    private static boolean holds(StaticScopeMap map, String regionId,
                                 StaticScopeMap.Site site) {
        Set<String> methods = map == null
                ? Collections.<String>emptySet() : map.methodsOf(regionId);
        return methods.isEmpty()
                ? site.regionId.equals(regionId)
                : methods.contains(SiteId.methodOf(site.siteId));
    }

    /** Whether some session of this corpus ran one occurrence. */
    private static boolean activated(Corpus corpus,
                                     OccurrenceAddress occurrence) {
        for (SessionReader session : corpus.sessions()) {
            if (corpus.activation(session.sessionId(), occurrence) != null) {
                return true;
            }
        }
        return false;
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
     * The session a task is planned from: the SEED when it ran the
     * occurrence, else the first ADMITTED session that did, else {@code ""}.
     * A replay that was not admitted did not run the world it was asked
     * for, so nothing is planned from it.
     */
    private static String seedSession(Corpus corpus,
                                      OccurrenceAddress occurrence) {
        String seed = corpus.seedSessionId();
        if (!seed.isEmpty() && ran(corpus, seed, occurrence)) return seed;
        for (SessionReader session : corpus.sessions()) {
            if (session.admitted()
                    && ran(corpus, session.sessionId(), occurrence)) {
                return session.sessionId();
            }
        }
        return "";
    }

    /** Whether one session activated or decided at one occurrence. */
    private static boolean ran(Corpus corpus, String sessionId,
                               OccurrenceAddress occurrence) {
        return corpus.activation(sessionId, occurrence) != null
                || !corpus.decisionsOf(sessionId, occurrence).isEmpty();
    }
}
