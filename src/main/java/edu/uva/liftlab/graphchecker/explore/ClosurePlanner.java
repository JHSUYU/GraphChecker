package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Arms;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The target's closure: what its failure can depend on, and the branches
 * exploration may flip in it (PIPELINE §7.2).
 *
 * <p>Demand starts at the ANNOTATED TARGET: the fatal predicate's operands and
 * the target's guard set ({@link StaticScopeMap}). Deliveries no demanded value
 * rests on are not followed. Each boundary variable grows it:</p>
 * <ul>
 *   <li>by ROWS: the paired producer, the writers a read could have
 * observed;</li>
 *   <li>by the STATIC MAP: occurrences of regions holding a write/export
 *       site of that location/port -- what the recording cannot state (a writer
 *       the seed's arm never ran, e.g. hdfs-17960's deferred decrement);</li>
 *   <li>by STATED READS ({@link #statedReads}, E2): shared state a
 *       contributed value rests on appears only inside its expression.</li>
 * </ul>
 *
 * <p>Static candidates are ON ONE NODE: the READER's for a write site (N1,
 * {@link #writers}), the PAIRED PRODUCER's for an export site (N2, {@link
 * #producers}); a class field exists in every JVM, but only one heap or sender
 * is the real one. A candidate is flipped only at its own guards; a region no
 * session activated is named (PIPELINE §7.2), not a task.</p>
 */
public final class ClosurePlanner {
    /** How many tasks one anchor may open, before the closure is truncated. */
    public static final int DEFAULT_MAX_TASKS = 64;

    /** Connected by rows. */
    public static final String CLOSURE_MEMBER = "CLOSURE_MEMBER";
    /** Sent the message a member served. */
    public static final String CONTROL_PRODUCER = "CONTROL_PRODUCER";
    /** Holds a static write site of a demanded location. */
    public static final String STATIC_CANDIDATE_WRITER =
            "STATIC_CANDIDATE_WRITER";
    /** Holds a static export site of a demanded port. */
    public static final String STATIC_CANDIDATE_PRODUCER =
            "STATIC_CANDIDATE_PRODUCER";

    private ClosurePlanner() {
    }

    /** The closure of one anchor, and what could not be named in it. */
    public static final class Plan {
        public final List<Task> tasks;
        public final List<GapRow> gaps;
        /** task id -> why it is in the closure. */
        public final Map<String, String> why;
        /** task id -> site ids this wave may flip. */
        public final Map<String, Set<String>> flipSites;
        /** A demanded occurrence no session captured -> the admitted
         *  focused session whose rows name it: GROWTH (PIPELINE §7.8). */
        public final Map<OccurrenceAddress, String> exposed;
        /** Demanded, uncaptured, and run by the seed replay alone: a focused
         *  replay that runs it will expose it, so it is a gap only at the
         *  fixpoint ({@link ExploreMain}). */
        public final Set<OccurrenceAddress> waiting;
        /** Demanded past the task bound, so not planned: the closure is
         *  incomplete, which only {@link ExploreMain} can weigh. */
        public final Set<String> truncated;

        private Plan(List<Task> tasks, List<GapRow> gaps,
                     Map<String, String> why,
                     Map<String, Set<String>> flipSites,
                     Map<OccurrenceAddress, String> exposed,
                     Set<OccurrenceAddress> waiting, Set<String> truncated) {
            this.tasks = Collections.unmodifiableList(tasks);
            this.gaps = Collections.unmodifiableList(gaps);
            this.why = Collections.unmodifiableMap(why);
            this.flipSites = Collections.unmodifiableMap(flipSites);
            this.exposed = Collections.unmodifiableMap(exposed);
            this.waiting = Collections.unmodifiableSet(waiting);
            this.truncated = Collections.unmodifiableSet(truncated);
        }
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks, StaticScopeMap scope) {
        Walk walk = new Walk(corpus, scope);
        Map<String, Demand> demands = new LinkedHashMap<String, Demand>();
        Deque<String> pending = new ArrayDeque<String>();
        Demand start = new Demand(anchor, CLOSURE_MEMBER, true);
        // The anchor flips only the decisions on its way to the throw: the
        // target's guard set (PIPELINE §7.2) and, when no run of it reached
        // the throw, the chain its path left by; flipping a chain guard of a
        // path that went on to the throw only leaves it.  The throw itself is
        // no branch.
        boolean reached = false;
        for (TargetRow row : corpus.targetsOn(anchor)) {
            reached |= row.reachedAnchor();
        }
        for (StaticScopeMap.Site target : scope.targetSites()) {
            start.flipSites.addAll(reached ? target.guards
                    : target.pathSites());
        }
        demands.put(anchor.id(), start);
        pending.add(anchor.id());
        Set<String> truncated = new LinkedHashSet<String>();
        while (!pending.isEmpty()) {
            Demand demand = demands.get(pending.remove());
            demand.dirty = false;
            for (Demand next : successors(walk, demand)) {
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
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flips =
                new LinkedHashMap<String, Set<String>>();
        Map<OccurrenceAddress, String> exposed =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> waiting =
                new LinkedHashSet<OccurrenceAddress>();
        for (Demand demand : demands.values()) {
            String seed = seedSession(corpus, demand.occurrence);
            if (seed.isEmpty()) {
                uncaptured(corpus, demand.occurrence, exposed, waiting,
                        walk.gaps);
                continue;
            }
            String taskId = taskId(demand.occurrence);
            tasks.add(Task.of(taskId, demand.occurrence,
                    stateConnected(corpus, demand.occurrence), seed));
            why.put(taskId, demand.why);
            // Flip sites: the demanded guards plus every FAULT decision
            // (PIPELINE §7.2).
            Set<String> sites = new LinkedHashSet<String>(demand.flipSites);
            sites.addAll(corpus.faultSites(demand.occurrence));
            flips.put(taskId, sites);
        }
        return new Plan(tasks, new ArrayList<GapRow>(walk.gaps), why, flips,
                exposed, waiting, truncated);
    }

    /**
     * A demanded occurrence no session CAPTURED: the hooks ran it -- its
     * runtime identity is in some session's rows (a SEND, the sender an anchor
     * names, a producer of a delivery) -- but no planned task admitted it, so
     * it has no decisions to flip.  It is the retained set that must grow
     * (PIPELINE §7.2, §7.8): an admitted focused
     * session naming it is re-run with a plan row at its address, and the
     * next wave has it as a task.  hdfs-17899: a DataNode's periodic
     * heartbeat sends its request through the woven IPC door under no task,
     * and the closure demands that door as the sender of a message the
     * NameNode served.
     *
     * <p>Named by the seed replay alone it is WAITING: a focused replay that
     * runs it exposes it, and the seed is not re-run.  Named by no session it
     * is BLOCKING.  A role
     * is no region of the static graph: nothing captures it, and the closure
     * goes on through the sender its anchor names.  Several occurrences are
     * grown from one session where one names them all: one re-run each.</p>
     *
     * <p>THE TICK BOUND: an occurrence a daemon tick past the recording's
     * last began ({@link Corpus#tickPastRecording}) is neither grown nor
     * waited for -- only a replay slower than the recording ran it, so
     * nothing the recording decided rests on it.</p>
     */
    private static void uncaptured(Corpus corpus,
                                   OccurrenceAddress occurrence,
                                   Map<OccurrenceAddress, String> exposed,
                                   Set<OccurrenceAddress> waiting,
                                   Set<GapRow> gaps) {
        if (occurrence.role()) {
            if (occurrence.lineageLost()) {
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                        occurrence.render(), "the closure reached a scope "
                                + "the recording lost: " + occurrence
                                .regionId() + " is a role, not a region of "
                                + "the static graph, so nothing can weave "
                                + "it"));
            }
            return;
        }
        String tick = corpus.tickPastRecording(occurrence);
        if (tick != null) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    occurrence.render(), "begun by the daemon tick " + tick
                            + ": a replay slower than the recording ran it, "
                            + "so it is not grown, and what it delivered "
                            + "stays in the wire arms"));
            return;
        }
        String seed = corpus.seedSessionId();
        String exposing = "";
        for (String sessionId : corpus.namedBy(occurrence)) {
            if (sessionId.equals(seed)
                    || !corpus.session(sessionId).admitted()
                    || corpus.session(sessionId).obligations().isEmpty()) {
                continue;
            }
            if (exposing.isEmpty()) exposing = sessionId;
            if (exposed.containsValue(sessionId)) {
                exposing = sessionId;
                break;
            }
        }
        if (!exposing.isEmpty()) {
            exposed.put(occurrence, exposing);
            return;
        }
        if (corpus.namedBy(occurrence).contains(seed)) {
            waiting.add(occurrence);
            return;
        }
        gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                GapClass.BLOCKING, occurrence.render(),
                "no session of this corpus ran this occurrence, so no replay "
                        + "can be focused on it and it is not a task"));
    }

    /** One task's id: the occurrence it focuses and nothing else. */
    public static String taskId(OccurrenceAddress focused) {
        return ArtifactIO.digest("task|" + focused.id(), 16);
    }

    /** The task one published obligation names, recovered from the corpus. */
    public static Task taskOf(Corpus corpus, String taskId) {
        if (taskId == null || taskId.isEmpty()) return null;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!taskId.equals(taskId(occurrence))) continue;
            String seed = seedSession(corpus, occurrence);
            // The wave published no task for it (growth or a gap), so none
            // here either.
            if (seed.isEmpty()) return null;
            return Task.of(taskId, occurrence, stateConnected(corpus,
                    occurrence), seed);
        }
        return null;
    }

    /** What one occurrence is demanded for, and where its flips may be. */
    private static final class Demand {
        private final OccurrenceAddress occurrence;
        /** session|expressionRef of values this occurrence contributed. */
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
         * Folds another reason to demand this occurrence; {@code
         * CLOSURE_MEMBER} wins over static reasons.
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
     * One anchor's walk over the corpus: the gaps it says (the same gap said
     * twice is one gap, as {@link ExploreMain} publishes them), the unread
     * deliveries it said ({@link #unread}), the static candidates it
     * offered ({@link #candidates}), and what the static map answered it:
     * each answer scans every site of the map, and the walk asks again for
     * every demanded read of a site.
     */
    private static final class Walk {
        private final Corpus corpus;
        private final StaticScopeMap map;
        private final Set<GapRow> gaps = new LinkedHashSet<GapRow>();
        /** what|endpoint id of each delivery said unread. */
        private final Set<String> unread = new LinkedHashSet<String>();
        /** (site, node) -> the activated occurrences that hold the site. */
        private final Map<List<Object>, List<OccurrenceAddress>> holders =
                new HashMap<List<Object>, List<OccurrenceAddress>>();
        /** (reason, site, guards, node) -> the occurrences offered under it. */
        private final Map<List<Object>, Set<String>> offered =
                new HashMap<List<Object>, Set<String>>();
        /** session|occurrence id -> the owners of every location it read or
         *  wrote in that session. */
        private final Map<String, Set<String>> held =
                new HashMap<String, Set<String>>();
        private final Map<String, Set<String>> carriers =
                new HashMap<String, Set<String>>();
        private final Map<String, Set<String>> guards =
                new HashMap<String, Set<String>>();
        private final Map<String, List<StaticScopeMap.Site>> writers =
                new HashMap<String, List<StaticScopeMap.Site>>();

        private Walk(Corpus corpus, StaticScopeMap map) {
            this.corpus = corpus;
            this.map = map;
        }

        /** {@link StaticScopeMap#carriersAt}. */
        private Set<String> carriersAt(String recordedSite, String javaType,
                                       LocationId location) {
            return carriers.computeIfAbsent(recordedSite + "|" + javaType
                            + "|" + location.kind(),
                    key -> map.carriersAt(recordedSite, javaType,
                            location.kind()));
        }

        /** A writer's flip sites: guards of every static write site in the
         *  METHOD it wrote from (bci vs unit index do not compare); may be
         *  one too many. */
        private Set<String> guardsAt(String recordedSite) {
            return guards.computeIfAbsent(recordedSite, key -> {
                Set<String> held = new LinkedHashSet<String>();
                for (StaticScopeMap.Site site : map.sitesAt(recordedSite)) {
                    held.addAll(site.guards);
                }
                return held;
            });
        }

        /** {@link StaticScopeMap#writersOf}. */
        private List<StaticScopeMap.Site> writersOf(String carrier) {
            return writers.computeIfAbsent(carrier, map::writersOf);
        }

        /** Every activated occurrence holding one static site, on {@code
         *  node} (null = any): one scan of the corpus per site and node. */
        private List<OccurrenceAddress> holders(StaticScopeMap.Site site,
                                                NodeId node) {
            return holders.computeIfAbsent(Arrays.<Object>asList(site, node),
                    key -> {
                        List<OccurrenceAddress> found =
                                new ArrayList<OccurrenceAddress>();
                        for (OccurrenceAddress occurrence
                                : corpus.occurrences()) {
                            if (holds(map, occurrence.regionId(), site)
                                    && (node == null
                                    || node.equals(occurrence.node()))
                                    && activated(corpus, occurrence)) {
                                found.add(occurrence);
                            }
                        }
                        return found;
                    });
        }

        /**
         * Whether one session saw this occurrence hold objects, and not the
         * one that owns this location: a heap location is one object's
         * (SYMBOL-SCOPE §5.5), and a store reaches only an object its
         * occurrence holds.  A static field, an owner that names no one
         * object ({@link Arms#namedOwner}) or an occurrence the session
         * states no access of says nothing either way.
         */
        private boolean holdsOthersOnly(OccurrenceAddress occurrence,
                                        String sessionId,
                                        LocationId location) {
            if (location.kind() == LocationKind.STATIC
                    || !Arms.namedOwner(location)) {
                return false;
            }
            Set<String> owners = held.computeIfAbsent(
                    sessionId + "|" + occurrence.id(), key -> {
                        Set<String> found = new HashSet<String>();
                        for (ReadRow read
                                : corpus.readsOn(sessionId, occurrence)) {
                            found.add(read.location().owner());
                        }
                        for (WriteRow write
                                : corpus.writesOn(sessionId, occurrence)) {
                            found.add(write.location().owner());
                        }
                        return found;
                    });
            return !owners.isEmpty() && !owners.contains(location.owner());
        }
    }

    /**
     * Everything one demand reaches, by rows and by the static map.
     *
     * <p>The group (occurrence + state-connected factor) is ONE symbolic
     * unit: the demanded values are asked of the reads and attaches of every
     * member.  A member joins the closure only through them -- as a writer
     * of a demanded read or the producer of a demanded attach -- never for
     * touching what the occurrence touches: two readers of one location
     * pass nothing to each other (SOLR-18413 r5: the leader's state watcher
     * shares the node's cluster-state maps with every other watcher's parse
     * and every Overseer mutation, and each of those, a member, made its own
     * group's members members in turn).</p>
     */
    private static List<Demand> successors(Walk walk, Demand demand) {
        Corpus corpus = walk.corpus;
        List<OccurrenceAddress> group = new ArrayList<OccurrenceAddress>();
        group.add(demand.occurrence);
        group.addAll(stateConnected(corpus, demand.occurrence));
        Set<String> demanded = demanded(corpus, demand, group);
        List<Demand> next = new ArrayList<Demand>();
        for (OccurrenceAddress member : group) {
            for (AttachRow attach : corpus.attachesOn(member)) {
                if (!demanded.contains(attach.symbol())) {
                    unread(walk, attach.sessionId(), attach.endpoint(),
                            "handoff");
                    continue;
                }
                producers(walk, attach, next);
            }
            for (ReadRow row : corpus.readsOn(member)) {
                if (!demanded.contains(row.symbol())) {
                    unread(walk, row.sessionId(), row.endpoint(),
                            "state read");
                    continue;
                }
                writers(walk, row, next);
            }
        }
        statedReads(walk, demand, next);
        controlProducer(corpus, demand, next);
        return next;
    }

    /** Both doors of the message a demanded occurrence served join as control
     *  producers: they contribute no value, but their fault points decide
     *  whether the message exists (IDENTITY §7.3). Paired via the served
     *  occurrence's ANCHOR (the producer endpoint). */
    private static void controlProducer(Corpus corpus, Demand demand,
                                        List<Demand> next) {
        if (!(demand.occurrence.context() instanceof CausalContext.Anchor)) {
            return;
        }
        String endpoint = ((CausalContext.Anchor) demand.occurrence.context())
                .producerEndpointId();
        for (OccurrenceAddress door : new OccurrenceAddress[] {
                corpus.senderOf(endpoint), corpus.receiverOf(endpoint)}) {
            if (door == null || door.equals(demand.occurrence)) continue;
            next.add(new Demand(door, CONTROL_PRODUCER, false));
        }
    }

    /**
     * E2 -- A DEMANDED EXPORT STATES THE SHARED STATE IT RESTS ON.
     *
     * <p>The VM publishes a contributed value's shared-state reads only inside
     * its expression; no ReadRow names them. Each resolved read grows the
     * closure like a read row (writer of that version, static write sites on
     * the producer's node, N1); writers recurse the same way. {@link
     * Corpus#expressionStateReads} is the one resolution, shared with {@code
     * ComposedFamilies.expressionWrites}. Never the anchor (it contributes no
     * delivery).</p>
     */
    private static void statedReads(Walk walk, Demand demand,
                                    List<Demand> into) {
        if (demand.anchor) return;
        for (String contributed : demand.contributed) {
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            for (Corpus.StateRead read : walk.corpus.expressionStateReads(
                    sessionId, contributed.substring(split + 1))) {
                writersOfVersion(walk, sessionId, demand.occurrence,
                        read.write().location(), read.write().version(),
                        Collections.<String>emptySet(), null,
                        demand.occurrence.render(),
                        read.locationKey() + " (read at event "
                                + read.readEventId() + ")", into);
            }
        }
    }

    /** The symbols one occurrence's demanded values name: what the anchor's
     *  fatal rests on ({@link Arms#fatalRests}: its predicate, or the path
     *  condition that reached a concrete one), its decisions at its
     *  guard-set sites, and its contributed
     *  expressions -- then the fixed point over its group's reads and the
     *  writes they could observe. A factor member deciding the same site
     *  decides it on its own objects, and demands nothing here. Terms are
     *  EXPR references, resolved by the ONE lowering (CONTRACT-SPEC §5). */
    private static Set<String> demanded(Corpus corpus, Demand demand,
                                        List<OccurrenceAddress> group) {
        Set<String> named = new LinkedHashSet<String>();
        GroupReads reads = new GroupReads(corpus, group);
        for (Corpus.RecordedPath path : corpus.pathsOf(demand.occurrence)) {
            for (DecisionRow decision : path.decisions) {
                if (!demand.flipSites.contains(decision.siteId())) continue;
                reaches(corpus, path.sessionId, FlipQuery.reach(corpus,
                        path.sessionId, decision.term()), named);
                reads.under(corpus, path.sessionId, decision.term(), named);
            }
        }
        if (demand.anchor) {
            for (TargetRow target : corpus.targetsOn(demand.occurrence)) {
                Corpus.RecordedPath path = corpus.path(target.sessionId(),
                        demand.occurrence);
                for (String rest : Arms.fatalRests(target, path == null
                        ? Collections.<DecisionRow>emptyList()
                        : path.decisions)) {
                    reaches(corpus, target.sessionId(), FlipQuery.reach(
                            corpus, target.sessionId(), rest), named);
                    reads.under(corpus, target.sessionId(), rest, named);
                }
            }
        }
        for (String contributed : demand.contributed) {
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            SmtLowering lowering = corpus.lowering(sessionId);
            if (lowering == null) continue;
            reaches(corpus, sessionId, lowering.lower(
                    contributed.substring(split + 1)).reach(), named);
        }
        Set<String> settled = new LinkedHashSet<String>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (String symbol : new ArrayList<String>(named)) {
                if (!settled.add(symbol)) continue;
                for (ReadRow row : reads.of(symbol)) {
                    for (WriteRow write : corpus.eligibleWrites(
                            row.sessionId(),
                            SmtLowering.locationKey(row.location()),
                            row.observedVersion(),
                            row.endpoint().occurrence())) {
                        grew |= reaches(corpus, write.sessionId(),
                                corpus.lowering(write.sessionId())
                                        .lower(write.expressionRef()).reach(),
                                named);
                    }
                }
            }
        }
        return named;
    }

    /**
     * One group's read rows, indexed once per {@link #demanded}, which asks
     * them once per decision at a flip site and once per demanded symbol:
     * a group holds every read its state-connected factor made (SOLR-18413
     * r2: 109,016 rows, mostly Lucene streams, and a rescan of them per
     * decision was two thirds of the wave planner's time).
     */
    private static final class GroupReads {
        private final Map<String, List<ReadRow>> bySymbol =
                new HashMap<String, List<ReadRow>>();
        /** session|location key -> the symbols its reads stated. */
        private final Map<String, Set<String>> symbolsAt =
                new HashMap<String, Set<String>>();

        private GroupReads(Corpus corpus, List<OccurrenceAddress> group) {
            for (OccurrenceAddress member : group) {
                for (ReadRow row : corpus.readsOn(member)) {
                    bySymbol.computeIfAbsent(row.symbol(),
                            symbol -> new ArrayList<ReadRow>()).add(row);
                    if (row.symbol().isEmpty()) continue;
                    symbolsAt.computeIfAbsent(row.sessionId() + "|"
                                    + SmtLowering.locationKey(row.location()),
                            key -> new LinkedHashSet<String>())
                            .add(row.symbol());
                }
            }
        }

        /** The rows that stated one symbol, in recorded order. */
        private List<ReadRow> of(String symbol) {
            List<ReadRow> rows = bySymbol.get(symbol);
            return rows == null ? Collections.<ReadRow>emptyList() : rows;
        }

        /**
         * The read rows a term's expressions read by structure, into {@code
         * named}: a scalar read the lowering joined to its version's value
         * is inlined there, and still what the term rests on (SOLR-18406:
         * the phi reads a commit point's `deleted` flag at its INITIAL,
         * which the join made the constant false).
         */
        private void under(Corpus corpus, String sessionId, String term,
                           Set<String> named) {
            for (String location : corpus.readLocations(sessionId, term)) {
                Set<String> symbols = symbolsAt.get(sessionId + "|"
                        + location);
                if (symbols != null) named.addAll(symbols);
            }
        }
    }

    /**
     * The recorded symbols one lowered term REACHES (not merely spells), into
     * {@code named}: {@link SmtLowering#reachedSymbols}, as the flip query
     * uses, over its text and every join a mint or a pin stood in for
     * ({@link SmtLowering.Lowered#reach}). Trap: {@code SmtLowering.symbols}
     * sees only a {@code container_dag__} name that matches no row. Includes
     * the state behind a container name (the v_C rule, PIPELINE §7.5).
     *
     * @return whether the set grew
     */
    private static boolean reaches(Corpus corpus, String sessionId,
                                   List<String> texts, Set<String> named) {
        SmtLowering lowering = corpus.lowering(sessionId);
        if (lowering == null) return false;
        Set<String> reached = new LinkedHashSet<String>();
        for (String text : texts) {
            lowering.reachedSymbols(text, reached, reached);
        }
        return named.addAll(reached);
    }

    /**
     * A delivery this anchor's paths never read: recorded, not planned.
     * Once per endpoint, not per session or per pass: a demand is walked
     * again every time it grows, and every replay repeats the seed's rows --
     * hdfs-11741 v69's planner ran out of heap rendering these.
     */
    private static void unread(Walk walk, String sessionId,
                               Endpoint endpoint, String what) {
        if (!walk.unread.add(what + "|" + endpoint.id())) return;
        walk.gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, endpoint.toString(),
                "no demanded value of this occurrence rests on this " + what
                        + ", so its producer is not a task"));
    }

    /**
     * Who could have produced one demanded attach: the paired endpoint, and the
     * port's static export sites. Nested handoffs need no walk: the producer is
     * demanded for its export, and its own attaches follow.
     *
     * <p><b>N2 -- a message was sent by ONE process:</b> static candidates only
     * on the paired producer's node. An unpaired attach restricts nothing (and
     * is reported LINEAGE_LOST).</p>
     */
    private static void producers(Walk walk, AttachRow attach,
                                  List<Demand> into) {
        String portId = attach.endpoint().site();
        List<StaticScopeMap.Site> exports = walk.map.exportsOf(portId);
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : exports) {
            guards.addAll(site.guards);
        }
        if (attach.producer() == null) {
            walk.gaps.add(GapRow.of(attach.sessionId(), GapKind.LINEAGE_LOST,
                    GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                    "attach is unpaired: no producer endpoint to close over"));
        } else {
            crossCheck(attach, walk.gaps);
            Demand paired = new Demand(attach.producer().occurrence(),
                    CLOSURE_MEMBER, false);
            paired.flipSites.addAll(guards);
            for (ExportRow export : walk.corpus.exportsOf(
                    attach.producer())) {
                paired.contributed.add(export.sessionId() + "|"
                        + export.expressionRef());
            }
            into.add(paired);
        }
        // N2: null (unpaired) means every node.
        NodeId sender = attach.producer() == null ? null
                : attach.producer().occurrence().node();
        for (StaticScopeMap.Site site : exports) {
            candidates(walk, site, STATIC_CANDIDATE_PRODUCER, guards, into,
                    attach.sessionId(), "port " + portId, sender, null);
        }
    }

    /**
     * Who could have written one demanded read: the eligible row writers, and
     * the static write sites of its carrier (joined through a write the
     * recording did observe; no such write = no carrier, said).  A read of
     * a reference rests on the container each eligible store delivered, too:
     * the writers of every state of it the read could have seen through
     * that store ({@link Corpus#referentStates}), which a query through the
     * read is answered from (COMPOSE, {@code SmtLowering#query}).
     *
     * <p><b>N1 -- a concrete location lives in ONE process:</b> static
     * candidates only on the reader's node (Writers_W(l) is per concrete
     * object, SYMBOL-SCOPE §5.5).</p>
     */
    private static void writers(Walk walk, ReadRow row, List<Demand> into) {
        writersOfVersion(walk, row.sessionId(), row.endpoint().occurrence(),
                row.location(), row.observedVersion(),
                walk.carriersAt(row.endpoint().site(), row.javaType(),
                        row.location()),
                row, row.endpoint().toString(),
                String.valueOf(row.location()), into);
    }

    /**
     * The closure's growth by one read of one version of one location, whether
     * the runtime stated it as a row or only in an expression (E2).
     *
     * @param readCarriers the carriers the read's own site names (a read
     *                     of a version no store of the window wrote: its
     *                     INITIAL)
     * @param read the read's row, or null for a read only an expression
     *             states: that read is never re-pointed (COMPOSE re-pairs
     *             the anchor's rows alone), so a query through it is the
     *             run's, whose container read the expression states too
     * @param subject what a diagnostic about this read is addressed at
     * @param located how the location reads in that diagnostic
     */
    private static void writersOfVersion(Walk walk, String sessionId,
                                         OccurrenceAddress reader,
                                         LocationId location,
                                         long observedVersion,
                                         Set<String> readCarriers,
                                         ReadRow read,
                                         String subject, String located,
                                         List<Demand> into) {
        Corpus corpus = walk.corpus;
        String locationKey = SmtLowering.locationKey(location);
        // Every carrier the static map names for the location, and the
        // read's own.
        Set<String> carriers = new LinkedHashSet<String>();
        for (WriteRow write : corpus.writeSitesOf(locationKey)) {
            carriers.addAll(walk.carriersAt(write.endpoint().site(),
                    write.javaType(), write.location()));
        }
        carriers.addAll(readCarriers);
        for (WriteRow write : corpus.eligibleWrites(sessionId, locationKey,
                observedVersion, reader)) {
            wrote(walk, write, into);
            if (read == null) continue;
            for (WriteRow state : corpus.referentStates(write, read)) {
                wrote(walk, state, into);
            }
        }
        if (carriers.isEmpty() && walk.map.stated()) {
            walk.gaps.add(GapRow.of(sessionId, GapKind.DECLARATION_MISSING,
                    GapClass.DIAGNOSTIC, subject,
                    "no recorded write of " + located + " matches a "
                            + "write site of the static map, so this "
                            + "location's carrier is unnamed and no static "
                            + "candidate writer of it can be"));
            return;
        }
        // N1: the heap this read observed is the reader JVM's.
        for (String carrier : carriers) {
            for (StaticScopeMap.Site site : walk.writersOf(carrier)) {
                candidates(walk, site, STATIC_CANDIDATE_WRITER, site.guards,
                        into, sessionId, "carrier " + carrier, reader.node(),
                        location);
            }
        }
    }

    /** One recorded write a demanded value may rest on: its writer, flipped
     *  at the guards of its method's write sites, contributing what it
     *  wrote. */
    private static void wrote(Walk walk, WriteRow write, List<Demand> into) {
        Demand paired = new Demand(write.endpoint().occurrence(),
                CLOSURE_MEMBER, false);
        paired.contributed.add(write.sessionId() + "|"
                + write.expressionRef());
        paired.flipSites.addAll(walk.guardsAt(write.endpoint().site()));
        into.add(paired);
    }

    /**
     * Every activated occurrence of the region holding one static site, on
     * {@code node} (N1/N2; null = any). None: named (PIPELINE §7.2), scoped
     * to that node, and no task.
     *
     * <p>A WRITER OF THIS LOCATION, NOT OF ITS CARRIER: a static write site
     * stands in for a store the recording did not see run (hdfs-17960's
     * deferred decrement), and a heap location is one object's
     * (Writers_W(l), SYMBOL-SCOPE §5.5).  An occurrence whose accesses the
     * read's session states, none of them to that object, holds other
     * objects only ({@link Walk#holdsOthersOnly}) and is no candidate.
     * SOLR-18413 r5: the leader's reads of a RoutingRule, a Slice, a
     * DocCollection and a ClusterState made every occurrence on the node
     * that builds one (each state watcher's parse, each Overseer mutation) a
     * candidate writer of those objects' fields.</p>
     *
     * <p>ONCE PER WALK: one site's holders on one node are scanned once, and
     * an occurrence is offered once per reason, site, guard set and node,
     * whichever read or attach asks for it: a demand offered again changes
     * nothing it is folded into ({@link Demand#absorb}); the gap names the
     * asking session, so every ask says it.  SOLR-18413 r2: the anchor's 282
     * demanded reads (fields of Slice, SolrInputDocument, IndexSchema, ...)
     * asked for 329,393 writer candidates of 107 occurrences, every walk of
     * the anchor, and the wave-1 planner ran out of an 8 GB heap.</p>
     *
     * @param location the location a write site's store is asked about,
     *                 or null for an export site
     */
    private static void candidates(Walk walk, StaticScopeMap.Site site,
                                   String why, Collection<String> guards,
                                   List<Demand> into, String sessionId,
                                   String what, NodeId node,
                                   LocationId location) {
        List<OccurrenceAddress> holders = walk.holders(site, node);
        Set<String> offered = walk.offered.computeIfAbsent(
                Arrays.<Object>asList(why, site, guards, node),
                key -> new HashSet<String>());
        for (OccurrenceAddress occurrence : holders) {
            if (offered.contains(occurrence.id())) continue;
            if (location != null && walk.holdsOthersOnly(occurrence,
                    sessionId, location)) {
                continue;
            }
            offered.add(occurrence.id());
            Demand candidate = new Demand(occurrence, why, false);
            candidate.flipSites.addAll(guards);
            into.add(candidate);
        }
        if (!holders.isEmpty()) return;
        walk.gaps.add(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, site.regionId,
                "a static " + (STATIC_CANDIDATE_WRITER.equals(why)
                        ? "write" : "export") + " site of " + what + " is in "
                        + site.siteId + ", and no session of this corpus "
                        + "activated that region"
                        + (node == null ? "" : " on " + node.render())
                        + ": the retained set would have "
                        + "to grow before it can be a task (PIPELINE "
                        + "§7.2)"));
    }

    /** Whether an occurrence's region would RUN a static site: by HOLDING its
     *  method, or a method whose calls run it ({@link
     *  StaticScopeMap.Site#callers}), not region-id equality. Under the fold
     *  rule a site of R is recorded under an enclosing R', while the map
     *  names only the innermost holder; and a store no recorded run entered
     *  is run by the region that calls into it (SOLR-18406: nothing deleted
     *  the reserved commit point, and the checkpoint that would have calls
     *  its delete()). Falls back to id equality when the map knows no method
     *  set. */
    private static boolean holds(StaticScopeMap map, String regionId,
                                 StaticScopeMap.Site site) {
        Set<String> methods = map.methodsOf(regionId);
        if (methods.isEmpty()) return site.regionId.equals(regionId);
        if (methods.contains(SiteId.methodOf(site.siteId))) return true;
        for (String caller : site.callers) {
            if (methods.contains(caller)) return true;
        }
        return false;
    }

    /**
     * Whether some session of this corpus ran one occurrence as an
     * activation of its region.  An ambient row (a port event outside every
     * admitted activation, {@code RowRuntime#ambientActivation}) names where
     * the event ran, not a region that ran the site: counted, every refused
     * attach made the handler it ran in a static candidate, and each
     * candidate's doors control producers (hdfs-17967-pathA r1: a closure
     * truncated at 64, with 40 NameNode registration handlers and 37
     * DataNode senders left out).  An ambient occurrence still grows the
     * closure through the rows that name it ({@link #uncaptured}).
     */
    private static boolean activated(Corpus corpus,
                                     OccurrenceAddress occurrence) {
        for (ActivationRow row : corpus.activationsOf(occurrence)) {
            if (row.instrumented()) return true;
        }
        return false;
    }

    /** Cross-checks the recorded pairing against the consumer's Anchor context
     *  (identity v3 states it twice). The row is authoritative; a mismatch is
     *  the runtime's defect, reported. Root/Lost contexts raise nothing. */
    private static void crossCheck(AttachRow attach, Set<GapRow> gaps) {
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

    /** Co-occurrences state-connected to one occurrence (writers/readers of its
     *  locations). */
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

    /** The session a task is planned from: the SEED if it captured the
     *  occurrence ({@link #ran}), else the first ADMITTED one that did, else
     *  "". */
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

    /** Whether one session CAPTURED one occurrence: a planned task admitted
     *  it, or it decided.  A role's ambient activation is its capture (no
     *  region to plan). */
    private static boolean ran(Corpus corpus, String sessionId,
                               OccurrenceAddress occurrence) {
        ActivationRow activation = corpus.activation(sessionId, occurrence);
        return activation != null
                && (activation.instrumented() || occurrence.role())
                || !corpus.decisionsOf(sessionId, occurrence).isEmpty();
    }
}
