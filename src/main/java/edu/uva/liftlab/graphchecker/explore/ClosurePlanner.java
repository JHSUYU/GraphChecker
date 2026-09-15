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
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
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
                            StaticScopeMap map) {
        return plan(corpus, anchor, DEFAULT_MAX_TASKS, map);
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks, StaticScopeMap map) {
        StaticScopeMap scope = map == null ? StaticScopeMap.empty() : map;
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
            flips.put(taskId, new LinkedHashSet<String>(demand.flipSites));
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
        return next;
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
                    SmtText.symbols(FlipQuery.statedTerm(corpus,
                            path.sessionId, decision.term()), named);
                }
            }
            if (demand.anchor) {
                for (TargetRow target : corpus.targetsOn(member)) {
                    SmtText.symbols(FlipQuery.statedTerm(corpus,
                            target.sessionId(), target.phiTerm()), named);
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
            named.addAll(lowering.lower(contributed.substring(split + 1))
                    .declarations().keySet());
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
     * {@code smt.Arms}', so the closure grows by exactly the writers the
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
        for (StaticScopeMap.Site site : exports) {
            candidates(corpus, site, STATIC_CANDIDATE_PRODUCER, guards, into,
                    gaps, attach.sessionId(), "port " + portId);
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
     */
    private static void writers(Corpus corpus, StaticScopeMap map,
                                ReadRow row, List<Demand> into,
                                List<GapRow> gaps) {
        Set<String> carriers = new LinkedHashSet<String>();
        for (SessionReader session : corpus.sessions()) {
            for (WriteRow write : corpus.writesOf(session.sessionId(),
                    SmtLowering.locationKey(row.location()))) {
                carriers.addAll(map.carriersAt(write.endpoint().site(),
                        write.javaType()));
            }
        }
        for (WriteRow write : eligibleWrites(corpus, row)) {
            Demand paired = new Demand(write.endpoint().occurrence(),
                    CLOSURE_MEMBER, false);
            paired.contributed.add(write.sessionId() + "|"
                    + write.expressionRef());
            paired.flipSites.addAll(guardsAt(map, write.endpoint().site()));
            into.add(paired);
        }
        if (carriers.isEmpty() && map.stated()) {
            gaps.add(GapRow.of(row.sessionId(), GapKind.DECLARATION_MISSING,
                    GapClass.DIAGNOSTIC, row.endpoint().toString(),
                    "no recorded write of " + row.location() + " matches a "
                            + "write site of the static map, so this "
                            + "location's carrier is unnamed and no static "
                            + "candidate writer of it can be"));
            return;
        }
        for (String carrier : carriers) {
            for (StaticScopeMap.Site site : map.writersOf(carrier)) {
                candidates(corpus, site, STATIC_CANDIDATE_WRITER,
                        new LinkedHashSet<String>(site.guards), into, gaps,
                        row.sessionId(), "carrier " + carrier);
            }
        }
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
     * Every occurrence of the region one static site belongs to.
     *
     * <p>A region the corpus holds no activation of is INTERACTION-ID SS8
     * case 2: the candidate exists in the program and not in any recording,
     * so it is named and no task is opened -- a replay cannot be focused on
     * an occurrence nothing ran.</p>
     */
    private static void candidates(Corpus corpus, StaticScopeMap.Site site,
                                   String why, Set<String> guards,
                                   List<Demand> into, List<GapRow> gaps,
                                   String sessionId, String what) {
        boolean ran = false;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!site.regionId.equals(occurrence.regionId())
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
                        + "activated that region: the retained set would have "
                        + "to grow before it can be a task (INTERACTION-ID "
                        + "SS8 case 2)"));
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
