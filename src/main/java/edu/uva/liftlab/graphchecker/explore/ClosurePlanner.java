package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.compose.RestsOn;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.FrozenSet;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Held;
import edu.uva.liftlab.graphchecker.contract.HeapWatch;
import edu.uva.liftlab.graphchecker.contract.IdentitySet;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.OpenSet;
import edu.uva.liftlab.graphchecker.contract.PairSet;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.UnplannedInput;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.plan.SystemView;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
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
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public final class ClosurePlanner {
    public static final int DEFAULT_MAX_TASKS = 64;

    public static final int CLOSURE_CEILING = 1024;

    public static final String CLOSURE_MEMBER = "CLOSURE_MEMBER";
    public static final String CONTROL_PRODUCER = "CONTROL_PRODUCER";
    public static final String STORE_ITEM_PRODUCER = "STORE_ITEM_PRODUCER";
    public static final String STORE_FETCH = "STORE_FETCH";
    public static final String STATIC_CANDIDATE_WRITER =
            "STATIC_CANDIDATE_WRITER";
    public static final String STATIC_CANDIDATE_PRODUCER =
            "STATIC_CANDIDATE_PRODUCER";
    public static final String UNRECORDED_WRITER = "UNRECORDED_WRITER";

    static final ForkJoinPool CORES = new ForkJoinPool(
            Runtime.getRuntime().availableProcessors());

    private ClosurePlanner() {
    }

    public static final class Plan {
        public final List<Task> tasks;
        public final Map<String, String> why;
        public final Map<String, Set<String>> flipSites;
        public final Map<OccurrenceAddress, String> exposed;
        public final Set<OccurrenceAddress> waiting;
        public final Set<String> truncated;
        public final Set<String> ceilingCut;
        public final Map<OccurrenceAddress, String> unpaused;
        public final Set<OccurrenceAddress> runWhole;
        public final Concrete concrete;
        public final Map<String, Set<OccurrenceAddress>> unrecordedWriters;

        private Plan(List<Task> tasks, Map<String, String> why,
                     Map<String, Set<String>> flipSites,
                     Map<OccurrenceAddress, String> exposed,
                     Set<OccurrenceAddress> waiting, Set<String> truncated,
                     Set<String> ceilingCut,
                     Map<OccurrenceAddress, String> unpaused,
                     Set<OccurrenceAddress> runWhole, Concrete concrete,
                     Map<String, Set<OccurrenceAddress>> unrecordedWriters) {
            this.unpaused = Collections.unmodifiableMap(unpaused);
            this.runWhole = Collections.unmodifiableSet(runWhole);
            this.tasks = Collections.unmodifiableList(tasks);
            this.why = Collections.unmodifiableMap(why);
            this.flipSites = Collections.unmodifiableMap(flipSites);
            this.exposed = Collections.unmodifiableMap(exposed);
            this.waiting = Collections.unmodifiableSet(waiting);
            this.truncated = Collections.unmodifiableSet(truncated);
            this.ceilingCut = Collections.unmodifiableSet(ceilingCut);
            this.concrete = concrete;
            this.unrecordedWriters =
                    Collections.unmodifiableMap(unrecordedWriters);
        }
    }

    public static final class Concrete {
        public final int paths;
        public final int decided;
        public final List<ReadRow> reads;
        public final int offCone;

        private Concrete(int paths, int decided, List<ReadRow> reads,
                         int offCone) {
            this.paths = paths;
            this.decided = decided;
            this.reads = Collections.unmodifiableList(reads);
            this.offCone = offCone;
        }
    }

    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks, StaticScopeMap scope,
                            Branches branches, Set<String> doorsOnly,
                            Set<String> heldDoorsOnly, ClientFaults faults,
                            SystemView view, Consumer<GapRow> gaps) {
        return plan(corpus, anchor, maxTasks, CLOSURE_CEILING, scope,
                branches, doorsOnly, heldDoorsOnly, faults, view, gaps);
    }

    static Plan plan(Corpus corpus, OccurrenceAddress anchor, int maxTasks,
                     int ceiling, StaticScopeMap scope, Branches branches,
                     Set<String> doorsOnly, Set<String> heldDoorsOnly,
                     ClientFaults faults, SystemView view,
                     Consumer<GapRow> gaps) {
        return plan(corpus, anchor, maxTasks, ceiling, scope, branches,
                doorsOnly, heldDoorsOnly, faults, view, CORES, gaps);
    }

    static Plan plan(Corpus corpus, OccurrenceAddress anchor, int maxTasks,
                     int ceiling, StaticScopeMap scope, Branches branches,
                     Set<String> doorsOnly, Set<String> heldDoorsOnly,
                     ClientFaults faults, SystemView view, ForkJoinPool cores,
                     Consumer<GapRow> gaps) {
        Walk walk = new Walk(corpus, scope, anchor, view, cores, gaps);
        Map<String, Demand> demands = walk.demands;
        Deque<String> pending = walk.pending;
        Demand start = new Demand(anchor, CLOSURE_MEMBER, true);
        boolean reached = walk.restsOn.reached();
        start.flipSites.addAll(corpus.openArmAsks(anchor));
        for (StaticScopeMap.Site target : scope.targetSites()) {
            start.flipSites.addAll(reached ? target.guards
                    : target.pathSites());
        }
        Concrete concrete = concrete(corpus, anchor, start.flipSites, scope);
        if (concrete != null) {
            for (ReadRow read : concrete.reads) {
                if (!read.symbol().isEmpty()) {
                    start.predicate.add(read.symbol());
                }
            }
        }
        start.predicate.addAll(storeReads(corpus, anchor, start.flipSites,
                scope));
        walk.admit(start);
        Set<String> truncated = new LinkedHashSet<String>();
        Set<String> ceilingCut = new LinkedHashSet<String>();
        Candidates candidates = new Candidates(corpus);
        int connectedPlanned = 1;
        int candidatesPlanned = 0;
        Set<String> plannedCandidates = new LinkedHashSet<String>();
        boolean ceilingReached = false;
        try {
            while (true) {
                while (!pending.isEmpty()) {
                    walk.ahead();
                    Demand demand = demands.get(pending.remove());
                    demand.dirty = false;
                    for (Demand next : walk.take(demand)) {
                        Demand held = demands.get(next.occurrence.id());
                        if (held != null) {
                            if (held.absorb(next) && !held.dirty) {
                                held.dirty = true;
                                pending.add(held.occurrence.id());
                            }
                            continue;
                        }
                        Demand queued = candidates.take(next);
                        if (queued == null) continue;
                        if (connectedPlanned >= ceiling) {
                            truncated.add(queued.occurrence.render());
                            ceilingCut.add(queued.occurrence.render());
                            for (String id : plannedCandidates) {
                                Demand planned = demands.get(id);
                                if (planned == null
                                        || !Candidates.staticCandidate(
                                                planned)) {
                                    continue;
                                }
                                walk.drop(planned);
                                truncated.add(planned.occurrence.render());
                            }
                            plannedCandidates.clear();
                            ceilingReached = true;
                            continue;
                        }
                        connectedPlanned++;
                        walk.admit(queued);
                    }
                }
                if (!ceilingReached && candidatesPlanned < maxTasks) {
                    walk.prepare(candidates.upcoming(maxTasks
                            - candidatesPlanned));
                }
                Demand candidate = candidates.next();
                if (candidate == null) break;
                if (ceilingReached || candidatesPlanned >= maxTasks) {
                    truncated.add(candidate.occurrence.render());
                    continue;
                }
                candidatesPlanned++;
                plannedCandidates.add(candidate.occurrence.id());
                walk.admit(candidate);
            }
        } finally {
            walk.drain();
        }
        List<Task> tasks = new ArrayList<Task>();
        Map<String, String> why = new LinkedHashMap<String, String>();
        Map<String, Set<String>> flips =
                new LinkedHashMap<String, Set<String>>();
        Map<OccurrenceAddress, String> exposed =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> waiting =
                new LinkedHashSet<OccurrenceAddress>();
        Map<OccurrenceAddress, String> unpaused =
                new LinkedHashMap<OccurrenceAddress, String>();
        Set<OccurrenceAddress> runWhole =
                new LinkedHashSet<OccurrenceAddress>();
        int unfailed = 0;
        int viewed = 0;
        for (Demand demand : demands.values()) {
            String seed = seedSession(corpus, demand.occurrence);
            if (seed.isEmpty()) {
                uncaptured(corpus, branches, demand, scope, exposed, waiting,
                        walk.gaps);
                continue;
            }
            if (demand.value
                    && heldDoorsOnly.contains(demand.occurrence.render())) {
                walk.gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        demand.occurrence.render(), "demanded as a value ("
                                + demand.why + "), it runs for its doors"
                                + " alone by the system's declaration"
                                + " (causynth.doors.only.roots): the values it"
                                + " writes are the recording's"));
            } else if (demand.value
                    && !ranWhole(corpus, demand.occurrence)) {
                String rerun = exposing(corpus, branches, demand.occurrence,
                        exposed.values())[0];
                if (!rerun.isEmpty()
                        || doorsOnly.contains(demand.occurrence.render())) {
                    unpaused.put(demand.occurrence, rerun);
                }
                if (rerun.isEmpty()) runWhole.add(demand.occurrence);
                walk.gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        demand.occurrence.render(), "run for its doors"
                                + " alone (a control producer or a store"
                                + " fetch) by every session that captured it,"
                                + " it is demanded as a value (" + demand.why
                                + "): its replays run it whole once GROW has"
                                + " dropped the mark; until one has, its guards"
                                + " and roots ran paused and have no term to"
                                + " flip"));
            }
            String taskId = taskId(demand.occurrence);
            tasks.add(Task.of(taskId, demand.occurrence,
                    stateConnected(corpus, demand.occurrence), seed));
            why.put(taskId, demand.why);
            Set<String> sites = new LinkedHashSet<String>();
            for (String site : demand.flipSites) {
                if (view.holds(methodOf(site))) {
                    viewed++;
                } else {
                    sites.add(site);
                }
            }
            for (String site : corpus.faultSites(demand.occurrence)) {
                if (faults.fails(demand.occurrence, site)) {
                    sites.add(site);
                } else if (!sites.contains(site)) {
                    unfailed++;
                }
            }
            flips.put(taskId, sites);
        }
        if (viewed > 0) {
            walk.gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "VIEW_GUARDS_UNFLIPPED", viewed + " demanded guard(s) of"
                            + " the system's view classes are no flip sites:"
                            + " a node's decode of a store version follows"
                            + " the version, whose writer states what else"
                            + " it could hold"));
        }
        if (unfailed > 0) {
            walk.gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "CLIENT_FAULTS_UNFLIPPED", unfailed + " fault door(s)"
                            + " of the closure are no flip sites: "
                            + faults.why()));
        }
        return new Plan(tasks, why, flips,
                exposed, waiting, truncated, ceilingCut, unpaused, runWhole,
                concrete, walk.unrecorded);
    }

    static String methodOf(String site) {
        int unit = site.lastIndexOf("#u");
        return unit < 0 ? site : site.substring(0, unit);
    }



    private static final class Candidates {
        private final Corpus corpus;
        private final Map<String, Demand> waiting =
                new HashMap<String, Demand>();
        private final Map<String, Deque<Demand>> byClass =
                new HashMap<String, Deque<Demand>>();
        private final Deque<String> turn = new ArrayDeque<String>();

        private Candidates(Corpus corpus) {
            this.corpus = corpus;
        }

        private Demand take(Demand next) {
            String id = next.occurrence.id();
            Demand held = waiting.get(id);
            boolean candidate = staticCandidate(next);
            if (held == null) {
                if (!candidate) return next;
                waiting.put(id, next);
                String key = classOf(next.occurrence);
                Deque<Demand> queue = byClass.get(key);
                if (queue == null) {
                    queue = new ArrayDeque<Demand>();
                    byClass.put(key, queue);
                    if (!turn.contains(key)) turn.add(key);
                }
                queue.add(next);
                return null;
            }
            held.absorb(next);
            if (candidate) return null;
            waiting.remove(id);
            byClass.get(classOf(held.occurrence)).remove(held);
            return held;
        }

        private Demand next() {
            while (!turn.isEmpty()) {
                String key = turn.remove();
                Deque<Demand> queue = byClass.get(key);
                Demand next = queue.poll();
                if (next == null) {
                    byClass.remove(key);
                    continue;
                }
                if (queue.isEmpty()) {
                    byClass.remove(key);
                } else {
                    turn.add(key);
                }
                waiting.remove(next.occurrence.id());
                return next;
            }
            return null;
        }

        private List<Demand> upcoming(int most) {
            List<Demand> upcoming = new ArrayList<Demand>();
            Deque<String> keys = new ArrayDeque<String>(turn);
            Map<String, java.util.Iterator<Demand>> rest =
                    new HashMap<String, java.util.Iterator<Demand>>();
            while (upcoming.size() < most && !keys.isEmpty()) {
                String key = keys.remove();
                java.util.Iterator<Demand> queue = rest.computeIfAbsent(key,
                        unused -> new ArrayList<Demand>(byClass.getOrDefault(
                                key, new ArrayDeque<Demand>())).iterator());
                if (!queue.hasNext()) continue;
                upcoming.add(queue.next());
                if (queue.hasNext()) keys.add(key);
            }
            return upcoming;
        }

        private String classOf(OccurrenceAddress occurrence) {
            return corpus.classOf(occurrence);
        }

        private static boolean staticCandidate(Demand demand) {
            return STATIC_CANDIDATE_WRITER.equals(demand.why)
                    || STATIC_CANDIDATE_PRODUCER.equals(demand.why);
        }
    }

    private static Concrete concrete(Corpus corpus, OccurrenceAddress anchor,
                                     Set<String> flipSites,
                                     StaticScopeMap scope) {
        List<ReadRow> reads = new ArrayList<ReadRow>();
        int paths = 0;
        int decided = 0;
        int offCone = 0;
        for (TargetRow row : corpus.targetsOn(anchor)) {
            String sessionId = row.sessionId();
            SessionReader session = corpus.session(sessionId);
            if (session == null || !session.admitted()) continue;
            if (row.observedFatal()) return null;
            long at = 0L;
            Set<Long> named = new LinkedHashSet<Long>();
            if (row.reachedAnchor()) {
                if (!corpus.termSymbols(sessionId, row.phiTerm()).isEmpty()) {
                    return null;
                }
                at = row.seq();
                named.addAll(corpus.readEvents(sessionId, row.phiTerm()));
            } else {
                for (DecisionRow decision
                        : corpus.decisionsOf(sessionId, anchor)) {
                    if (!FlipQuery.asks(flipSites, decision)) continue;
                    if (!corpus.termSymbols(sessionId, decision.term())
                            .isEmpty()) {
                        return null;
                    }
                    at = Math.max(at, decision.seq());
                    named.addAll(corpus.readEvents(sessionId,
                            decision.term()));
                }
            }
            paths++;
            if (at > 0L) decided++;
            for (ReadRow read : corpus.readsOn(sessionId, anchor)) {
                if (named.contains(Long.valueOf(read.seq()))) {
                    reads.add(read);
                } else if (!RowOrder.beforeEvent(read.seq(), read.tie(),
                        at)) {
                    continue;
                } else if (scope.demandedAt(read.endpoint().site(),
                        read.javaType(), read.location().kind())) {
                    reads.add(read);
                } else {
                    offCone++;
                }
            }
        }
        return paths == 0 ? null
                : new Concrete(paths, decided, reads, offCone);
    }

    private static Set<String> storeReads(Corpus corpus,
                                          OccurrenceAddress anchor,
                                          Set<String> flipSites,
                                          StaticScopeMap scope) {
        Set<String> symbols = new LinkedHashSet<String>();
        for (TargetRow row : corpus.targetsOn(anchor)) {
            SessionReader session = corpus.session(row.sessionId());
            if (session == null || !session.admitted()) continue;
            long at = row.reachedAnchor() ? row.seq() : 0L;
            if (!row.reachedAnchor()) {
                for (DecisionRow decision
                        : corpus.decisionsOf(row.sessionId(), anchor)) {
                    if (FlipQuery.asks(flipSites, decision)) {
                        at = Math.max(at, decision.seq());
                    }
                }
            }
            for (ReadRow read : corpus.readsOn(row.sessionId(), anchor)) {
                if (read.location().kind() == LocationKind.STORE
                        && RowOrder.beforeEvent(read.seq(), read.tie(), at)
                        && scope.demandedAt(
                        read.endpoint().site(), read.javaType(),
                        LocationKind.STORE)) {
                    symbols.add(read.symbol());
                }
            }
        }
        return symbols;
    }

    static Map<UnplannedInput, String> unplanned(Corpus corpus,
                                                Branches branches) {
        Map<UnplannedInput, String> exposed =
                new LinkedHashMap<UnplannedInput, String>();
        for (SessionReader session : corpus.sessions()) {
            if (session.seed() || session.obligations().isEmpty()
                    || !branches.parents(session.sessionId())) {
                continue;
            }
            for (GapRow gap : session.gaps(GapKind.UNPLANNED_INPUT)) {
                exposed.putIfAbsent(UnplannedInput.parse(gap.subject()),
                        session.sessionId());
            }
        }
        return exposed;
    }

    private static void uncaptured(Corpus corpus, Branches branches,
                                   Demand demand, StaticScopeMap scope,
                                   Map<OccurrenceAddress, String> exposed,
                                   Set<OccurrenceAddress> waiting,
                                   Consumer<GapRow> gaps) {
        OccurrenceAddress occurrence = demand.occurrence;
        if (occurrence.role()) {
            if (occurrence.lineageLost()) {
                gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                        occurrence.render(), "the closure reached a scope "
                                + "the recording lost (" + demand.why
                                + "): " + occurrence.regionId() + " is a "
                                + "role, not a region of the static graph, "
                                + "so nothing can weave it" + unrecorded(
                                demand, scope)));
            }
            return;
        }
        Corpus.TickPast tick = corpus.tickPastRecording(occurrence);
        if (tick != null) {
            gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    occurrence.render(), "begun by the daemon tick " + tick
                            + ": a replay slower than the recording ran it, "
                            + "so it is not grown, and what it delivered "
                            + "stays in the wire arms"));
            return;
        }
        String seed = corpus.seedSessionId();
        String[] chosen = exposing(corpus, branches, occurrence,
                exposed.values());
        String exposing = chosen[0];
        String stopped = chosen[1];
        if (!exposing.isEmpty()) {
            exposed.put(occurrence, exposing);
            return;
        }
        if (corpus.namedBy(occurrence).contains(seed)) {
            if (UNRECORDED_WRITER.equals(demand.why)) {
                exposed.put(occurrence, seed);
            } else {
                waiting.add(occurrence);
            }
            return;
        }
        if (!stopped.isEmpty()) {
            gaps.accept(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    occurrence.render(), "only sessions whose branch "
                            + "stopped ran this occurrence (" + stopped
                            + " among them), so it is not grown"));
            return;
        }
        gaps.accept(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                GapClass.BLOCKING, occurrence.render(),
                "no session of this corpus ran this occurrence, so no replay "
                        + "can be focused on it and it is not a task"));
    }

    private static boolean ranWhole(Corpus corpus,
                                    OccurrenceAddress occurrence) {
        String rendered = occurrence.render();
        for (SessionReader session : corpus.sessions()) {
            if ((session.manifest().seed() || session.admitted())
                    && ran(corpus, session.sessionId(), occurrence)
                    && !session.manifest().doorsOnly().contains(rendered)) {
                return true;
            }
        }
        return false;
    }

    static boolean valueDemand(String why) {
        return CLOSURE_MEMBER.equals(why)
                || UNRECORDED_WRITER.equals(why)
                || STORE_ITEM_PRODUCER.equals(why)
                || STATIC_CANDIDATE_WRITER.equals(why)
                || STATIC_CANDIDATE_PRODUCER.equals(why);
    }

    private static String[] exposing(Corpus corpus, Branches branches,
                                     OccurrenceAddress occurrence,
                                     Collection<String> rerun) {
        String seed = corpus.seedSessionId();
        String exposing = "";
        String stopped = "";
        for (String sessionId : corpus.namedBy(occurrence)) {
            SessionReader session = corpus.session(sessionId);
            if (sessionId.equals(seed) || !session.admitted()
                    || session.obligations().isEmpty()) {
                continue;
            }
            if (!branches.parents(sessionId)) {
                stopped = sessionId;
                continue;
            }
            if (exposing.isEmpty()) exposing = sessionId;
            if (rerun.contains(sessionId)) {
                exposing = sessionId;
                break;
            }
        }
        return new String[] {exposing, stopped};
    }

    private static String unrecorded(Demand demand, StaticScopeMap scope) {
        Set<String> methods = new LinkedHashSet<String>();
        for (Frame frame : demand.occurrence.index().frames()) {
            String method = SiteId.methodOf(frame.callSite());
            methods.add(method.isEmpty() ? frame.callSite() : method);
        }
        Set<String> roots = new TreeSet<String>();
        for (StaticScopeMap.Site site : scope.declaredSites()) {
            if (methods.contains(SiteId.methodOf(site.siteId))) {
                roots.add(site.siteId + (site.declared == null ? ""
                        : " " + site.declared.inputKind));
            }
        }
        return "; unrecorded there: roots " + roots + ", decisions "
                + new TreeSet<String>(demand.flipSites);
    }

    public static String taskId(OccurrenceAddress focused) {
        return ArtifactIO.digest("task|" + focused.id(), 16);
    }

    public static Task taskOf(Corpus corpus, String taskId) {
        if (taskId == null || taskId.isEmpty()) return null;
        for (OccurrenceAddress occurrence : corpus.occurrences()) {
            if (!taskId.equals(taskId(occurrence))) continue;
            String seed = seedSession(corpus, occurrence);
            if (seed.isEmpty()) return null;
            return Task.of(taskId, occurrence, stateConnected(corpus,
                    occurrence), seed);
        }
        return null;
    }

    private static final class Demand {
        private final OccurrenceAddress occurrence;
        private Set<String> contributed = new LinkedHashSet<String>();
        private Map<String, Long> cutoffs = new LinkedHashMap<String, Long>();
        private boolean shared;
        private final Set<Contribution> holds =
                Collections.newSetFromMap(
                        new java.util.IdentityHashMap<Contribution, Boolean>(
                                1));
        private Contribution exactly;
        private Set<String> flipSites = new LinkedHashSet<String>();
        private boolean flipsShared;
        private final Set<String> predicate = new LinkedHashSet<String>();
        private final boolean anchor;
        private String why;
        private boolean value;
        private boolean storeWriter;
        private boolean dirty;
        private int version;
        private final PairSet paired = new PairSet();
        private final BitSet expandedReads = new BitSet();
        private int expandedContributed;
        private Named named;
        private WriteRow madeOf;
        private volatile Set<WriteRow> absorbed;

        private Demand(OccurrenceAddress occurrence, String why,
                       boolean anchor) {
            this.occurrence = occurrence;
            this.why = why;
            this.value = valueDemand(why);
            this.anchor = anchor;
        }

        private Demand(OccurrenceAddress occurrence, String why,
                       Contribution values) {
            this(occurrence, why, false);
            contributed = values.contributed;
            cutoffs = values.cutoffs;
            shared = true;
            holds.add(values);
            exactly = values;
        }

        private boolean absorbs(WriteRow write) {
            return write == madeOf
                    || absorbed != null && absorbed.contains(write);
        }

        private void launched() {
            shared = true;
            flipsShared = true;
        }

        private void own() {
            if (!shared) return;
            contributed = new LinkedHashSet<String>(contributed);
            cutoffs = new LinkedHashMap<String, Long>(cutoffs);
            shared = false;
        }

        private boolean absorb(Demand other) {
            WriteRow write = other.madeOf;
            if (write != null) {
                if (write == madeOf || absorbed != null
                        && absorbed.contains(write)) {
                    return false;
                }
                if (absorbed == null) {
                    absorbed = ConcurrentHashMap.newKeySet(1);
                }
                absorbed.add(write);
            }
            boolean grew = false;
            if (other.exactly == null || !holds.contains(other.exactly)) {
                own();
                grew = contributed.addAll(other.contributed);
                for (Map.Entry<String, Long> cutoff
                        : other.cutoffs.entrySet()) {
                    grew |= contributes(cutoff.getKey(), cutoff.getValue());
                }
                if (grew) exactly = null;
                holds.addAll(other.holds);
            }
            if (flipsShared && !flipSites.containsAll(other.flipSites)) {
                flipSites = new LinkedHashSet<String>(flipSites);
                flipsShared = false;
            }
            grew |= flipSites.addAll(other.flipSites);
            if (CLOSURE_MEMBER.equals(other.why)
                    ? !CLOSURE_MEMBER.equals(why)
                    : Candidates.staticCandidate(this)
                    && !Candidates.staticCandidate(other)
                    || other.value && !value
                    && !Candidates.staticCandidate(other)) {
                why = other.why;
                grew = true;
            }
            if (other.value && !value) {
                value = true;
                grew = true;
            }
            if (other.storeWriter && !storeWriter) {
                storeWriter = true;
                grew = true;
            }
            if (grew) version++;
            return grew;
        }

        private void contributes(String sessionId, String expressionRef,
                                 long seq) {
            own();
            if (contributed.add(sessionId + "|" + expressionRef)) {
                exactly = null;
            }
            contributes(sessionId, seq);
        }

        private boolean contributes(String sessionId, long seq) {
            Long held = cutoffs.get(sessionId);
            if (held != null && held.longValue() >= seq) return false;
            own();
            cutoffs.put(sessionId, seq);
            exactly = null;
            return true;
        }

        private static Map<String, List<String>> delivered(
                Set<String> contributed) {
            Map<String, List<String>> bySession =
                    new HashMap<String, List<String>>();
            for (String each : contributed) {
                int split = each.indexOf('|');
                if (split < 0) continue;
                bySession.computeIfAbsent(each.substring(0, split),
                        session -> new ArrayList<String>())
                        .add(each.substring(split + 1));
            }
            return bySession;
        }

        private static List<String> delivered(
                Map<String, List<String>> bySession, String sessionId) {
            List<String> refs = bySession.get(sessionId);
            return refs == null ? new ArrayList<String>() : refs;
        }
    }

    private static final class Named {
        private final Named before;
        private final Set<String> symbols = new OpenSet<String>();
        List<String> fresh = new ArrayList<String>();
        boolean whole = true;
        private final Set<DecisionRow> decisions =
                new IdentitySet<DecisionRow>(8);
        int contributed;
        Set<String> kept = Collections.<String>emptySet();

        Named() {
            before = null;
        }

        private Named(Named before) {
            this.before = before;
            whole = false;
            contributed = before.contributed;
            kept = before.kept;
        }

        boolean holds(String symbol) {
            return symbols.contains(symbol)
                    || before != null && before.symbols.contains(symbol);
        }

        boolean decide(DecisionRow decision) {
            return !(before != null && before.decisions.contains(decision))
                    && decisions.add(decision);
        }

        Named taken() {
            if (before == null) return this;
            before.symbols.addAll(symbols);
            before.decisions.addAll(decisions);
            before.fresh = fresh;
            before.whole = whole;
            before.contributed = contributed;
            before.kept = kept;
            return before;
        }

        void add(String symbol) {
            if (!holds(symbol) && symbols.add(symbol)) fresh.add(symbol);
        }

        void addAll(Collection<String> named) {
            for (String symbol : named) add(symbol);
        }
    }

    private static final class Contribution {
        private final Set<String> contributed;
        private final Map<String, Long> cutoffs;

        private Contribution(Demand built) {
            this.contributed = Collections.unmodifiableSet(built.contributed);
            this.cutoffs = Collections.unmodifiableMap(built.cutoffs);
        }
    }

    private static class Says {
        final Walk walk;
        final Demand demand;
        final List<Said> said = new ArrayList<Said>();
        private Set<Object> gaps;
        Set<String> successors;

        Says(Walk walk, Demand demand) {
            this.walk = walk;
            this.demand = demand;
        }

        private void succeeds(String occurrenceId) {
            if (successors == null) successors = new HashSet<String>();
            successors.add(occurrenceId);
        }

        void say(Says part) {
            said.addAll(part.said);
            if (part.successors != null) {
                for (String occurrenceId : part.successors) {
                    succeeds(occurrenceId);
                }
            }
        }

        void next(Demand successor) {
            succeeds(successor.occurrence.id());
            said.add((at, next) -> next.add(successor));
        }

        void gap(List<Object> key, Supplier<GapRow> row) {
            if (walk.gapKeys.contains(key)) return;
            if (gaps == null) gaps = new HashSet<Object>();
            if (!gaps.add(key)) return;
            said.add((at, next) -> {
                if (at.gapKeys.add(key)) at.gaps.accept(row.get());
            });
        }

        void once(String key, Supplier<GapRow> row) {
            if (walk.cut.contains(key)) return;
            said.add((at, next) -> {
                if (at.cut.add(key)) at.gaps.accept(row.get());
            });
        }

        void faultless(String doorId, Supplier<GapRow> row) {
            if (walk.faultless.contains(doorId)) return;
            said.add((at, next) -> {
                if (at.faultless.add(doorId)) at.gaps.accept(row.get());
            });
        }

        void offer(List<Object> key, List<OccurrenceAddress> holders,
                   String why, Collection<String> guards, String sessionId,
                   LocationId location) {
            Set<String> offered = walk.offered.get(key);
            List<OccurrenceAddress> asked = new ArrayList<OccurrenceAddress>();
            for (OccurrenceAddress occurrence : holders) {
                if (offered == null || !offered.contains(occurrence.id())) {
                    asked.add(occurrence);
                }
            }
            List<Boolean> others = location == null ? null
                    : walk.each(asked, occurrence -> walk.holdsOthersOnly(
                    occurrence, sessionId, location));
            List<OccurrenceAddress> offering =
                    new ArrayList<OccurrenceAddress>();
            for (int at = 0; at < asked.size(); at++) {
                if (others == null || !others.get(at)) {
                    offering.add(asked.get(at));
                }
            }
            if (offering.isEmpty()) return;
            for (OccurrenceAddress occurrence : offering) {
                succeeds(occurrence.id());
            }
            said.add((at, next) -> {
                Set<String> now = at.offered.computeIfAbsent(key,
                        unused -> ConcurrentHashMap.newKeySet());
                for (OccurrenceAddress occurrence : offering) {
                    if (!now.add(occurrence.id())) continue;
                    Demand candidate = new Demand(occurrence, why, false);
                    candidate.flipSites.addAll(guards);
                    next.add(candidate);
                }
            });
        }

        void earlier(WriteRow write) {
            Long first = walk.storeExpanded.get(write.sessionId() + "|"
                    + SmtLowering.locationKey(write.location()));
            if (first != null && first >= write.version()) return;
            said.add((at, next) -> earlierVersions(at, write, next));
        }

        void writer(WriteRow write) {
            Demand held = walk.admitted.get(
                    write.endpoint().occurrence().id());
            if (held != null && held.absorbs(write)) return;
            succeeds(write.endpoint().occurrence().id());
            said.add((at, next) -> next.add(ClosurePlanner.writer(at,
                    write)));
        }
    }

    private static final class Step extends Says {
        private final int version;
        private final GroupReads group;
        private final PairSet paired = new PairSet();
        private final BitSet expanded = new BitSet();
        private int contributed;
        private Named named;
        private final Corpus.Claims claims = new Corpus.Claims();
        private final Map<String, Set<String>> unread =
                new HashMap<String, Set<String>>(4);

        private final Set<String> values;
        private final Map<String, Long> cutoffs;
        private final Set<String> flipSites;
        private final String why;
        private final boolean value;
        private final boolean storeWriter;

        Step(Walk walk, Demand demand, GroupReads group) {
            super(walk, demand);
            this.version = demand.version;
            this.group = group;
            this.contributed = demand.expandedContributed;
            this.named = demand.named;
            this.values = demand.contributed;
            this.cutoffs = demand.cutoffs;
            this.flipSites = demand.flipSites;
            this.why = demand.why;
            this.value = demand.value;
            this.storeWriter = demand.storeWriter;
        }

        long weight() {
            return said.size() + claims.size();
        }

        boolean pair(String sessionId, String symbol) {
            return !demand.paired.contains(sessionId, symbol)
                    && paired.add(sessionId, symbol);
        }

        boolean expand(int member, int row) {
            int read = group.readAt(member, row);
            if (demand.expandedReads.get(read) || expanded.get(read)) {
                return false;
            }
            expanded.set(read);
            return true;
        }

        void unread(List<Object> into, String sessionId, Endpoint endpoint,
                    String what) {
            Set<String> said = walk.unread.get(what);
            if (said != null && said.contains(endpoint.id())
                    || !unread.computeIfAbsent(what,
                    unused -> new HashSet<String>()).add(endpoint.id())) {
                return;
            }
            into.add((Said) (walk, next) -> ClosurePlanner.unread(walk,
                    sessionId, endpoint, what));
        }

        List<Demand> apply(Walk walk) {
            demand.paired.addAll(paired);
            demand.expandedReads.or(expanded);
            demand.expandedContributed = contributed;
            demand.named = named.taken();
            demand.version++;
            List<Demand> next = new ArrayList<Demand>();
            for (Said each : said) each.apply(walk, next);
            return next;
        }
    }

    private interface Said {
        void apply(Walk walk, List<Demand> next);
    }

    static final class Walk {
        private final Corpus corpus;
        private final StaticScopeMap map;
        private final SystemView view;
        private final RestsOn restsOn;
        private final Consumer<GapRow> gaps;
        private final Set<Object> gapKeys = ConcurrentHashMap.newKeySet();
        private final Map<String, Demand> demands =
                new LinkedHashMap<String, Demand>();
        private final Map<String, Demand> admitted =
                new ConcurrentHashMap<String, Demand>();
        private final Map<String, Set<String>> unread =
                new ConcurrentHashMap<String, Set<String>>();
        private final Map<List<Object>, List<OccurrenceAddress>> holders =
                new ConcurrentHashMap<List<Object>, List<OccurrenceAddress>>();
        private final Map<List<Object>, Set<String>> offered =
                new ConcurrentHashMap<List<Object>, Set<String>>();
        private final Map<String, Set<String>> held =
                new ConcurrentHashMap<String, Set<String>>();
        private final Map<String, Set<String>> guards =
                new ConcurrentHashMap<String, Set<String>>();
        private final Map<String, List<StaticScopeMap.Site>> writers =
                new ConcurrentHashMap<String, List<StaticScopeMap.Site>>();
        private final Map<String, Boolean> faults =
                new ConcurrentHashMap<String, Boolean>();
        private final Set<String> faultless = ConcurrentHashMap.newKeySet();
        private final Set<String> anchorTerms = ConcurrentHashMap.newKeySet();
        private final Map<String, Set<OccurrenceAddress>> unrecorded =
                new ConcurrentHashMap<String, Set<OccurrenceAddress>>();
        private final Set<String> cut = ConcurrentHashMap.newKeySet();
        private final Map<String, Long> storeExpanded =
                new ConcurrentHashMap<String, Long>();
        private final Map<String, List<OccurrenceAddress>> groups =
                new HashMap<String, List<OccurrenceAddress>>();
        private final Map<String, GroupReads> groupReads =
                new HashMap<String, GroupReads>();
        private final Map<String, MemberReads> memberReads =
                new HashMap<String, MemberReads>();
        private final Map<String, MemberReads[]> naming =
                new ConcurrentHashMap<String, MemberReads[]>();
        private final Map<List<String>, MemberReads[]> locating =
                new ConcurrentHashMap<List<String>, MemberReads[]>();
        private final Map<List<String>, MemberReads[]> returning =
                new ConcurrentHashMap<List<String>, MemberReads[]>();
        private final Map<String, Contribution> contributions =
                new ConcurrentHashMap<String, Contribution>();
        private final ForkJoinPool cores;
        private final Thread planner;
        final Deque<String> pending = new ArrayDeque<String>();
        private final Map<Demand, Object> steps =
                new java.util.IdentityHashMap<Demand, Object>();
        private static final Object RUNNING = new Object();
        private final java.util.concurrent.BlockingQueue<Object[]> done =
                new java.util.concurrent.LinkedBlockingQueue<Object[]>();
        private int running;

        Walk(Corpus corpus, StaticScopeMap map, OccurrenceAddress anchor,
             SystemView view, ForkJoinPool cores, Consumer<GapRow> gaps) {
            this.planner = Thread.currentThread();
            this.gaps = gaps;
            this.corpus = corpus;
            this.map = map;
            this.view = view;
            this.restsOn = new RestsOn(corpus, map, anchor);
            this.cores = cores;
        }


        private boolean faulted(OccurrenceAddress occurrence) {
            Boolean held = faults.get(occurrence.id());
            if (held == null) {
                held = !corpus.faultSites(occurrence).isEmpty();
                faults.putIfAbsent(occurrence.id(), held);
            }
            return held;
        }

        private Contribution contribution(Endpoint producer) {
            Contribution held = contributions.get(producer.id());
            if (held != null) return held;
            Demand built = new Demand(producer.occurrence(), CLOSURE_MEMBER,
                    false);
            for (ExportRow export : corpus.exportsOf(producer)) {
                built.contributes(export.sessionId(), export.expressionRef(),
                        export.seq());
            }
            held = contributions.putIfAbsent(producer.id(),
                    new Contribution(built));
            return held != null ? held : contributions.get(producer.id());
        }

        void admit(Demand demand) {
            demands.put(demand.occurrence.id(), demand);
            admitted.put(demand.occurrence.id(), demand);
            pending.add(demand.occurrence.id());
        }

        void drop(Demand demand) {
            demands.remove(demand.occurrence.id());
            admitted.remove(demand.occurrence.id());
            pending.remove(demand.occurrence.id());
            steps.remove(demand);
        }

        void ahead() {
            received(false);
            launch(true);
        }

        void prepare(List<Demand> upcoming) {
            received(false);
            launch(upcoming, false);
        }

        private void launch(boolean headTaken) {
            if (cores.getParallelism() < 2) return;
            int window = WINDOW * cores.getParallelism();
            Set<Demand> seen = Collections.newSetFromMap(
                    new java.util.IdentityHashMap<Demand, Boolean>());
            List<Demand> head = new ArrayList<Demand>();
            for (String id : pending) {
                Demand demand = demands.get(id);
                if (demand == null || !seen.add(demand)) continue;
                head.add(demand);
                if (head.size() == window) break;
            }
            launch(head, headTaken);
        }

        static final int WINDOW = 2;
        static final long WEIGHT_BYTES = 2048L;
        static final double HELD_SHARE = 0.25;

        private static long budget() {
            long heap = Runtime.getRuntime().maxMemory();
            double free = 1.0 - HeapWatch.oldGenerationSwept();
            return (long) (heap * free * HELD_SHARE / WEIGHT_BYTES);
        }

        private void launch(List<Demand> order, boolean headTaken) {
            if (cores.getParallelism() < 2) return;
            long weight = 0L;
            for (Object step : steps.values()) {
                if (step instanceof Step) weight += ((Step) step).weight();
            }
            long budget = budget();
            Set<String> named = new HashSet<String>();
            for (int at = 0; at < order.size(); at++) {
                Demand demand = order.get(at);
                Object held = steps.get(demand);
                if (held == RUNNING) continue;
                if (held != null) {
                    Object current = current(demand);
                    if (current instanceof Step) {
                        Step step = (Step) current;
                        if (step.successors != null) {
                            named.addAll(step.successors);
                        }
                        continue;
                    }
                    if (current != null) continue;
                    if (held instanceof Step) {
                        weight -= ((Step) held).weight();
                    }
                }
                if (at == 0 && headTaken
                        || named.contains(demand.occurrence.id())) {
                    continue;
                }
                if (running >= cores.getParallelism() || weight >= budget) {
                    return;
                }
                Step step = new Step(this, demand, reads(demand.occurrence));
                demand.launched();
                cores.execute(() -> done.add(new Object[] {demand,
                        stepAhead(step)}));
                steps.put(demand, RUNNING);
                running++;
            }
        }

        private Object current(Demand demand) {
            Object held = steps.get(demand);
            int version = held instanceof Step ? ((Step) held).version
                    : held instanceof Thrown ? ((Thrown) held).version : -1;
            if (version < 0) return null;
            if (version == demand.version) return held;
            steps.remove(demand);
            return null;
        }

        private static final class Thrown {
            final int version;
            final Throwable thrown;

            Thrown(int version, Throwable thrown) {
                this.version = version;
                this.thrown = thrown;
            }
        }

        private Object stepAhead(Step step) {
            try {
                return step(this, step);
            } catch (RuntimeException | Error thrown) {
                return new Thrown(step.version, thrown);
            }
        }

        private void received(boolean wait) {
            Object[] ended;
            try {
                ended = wait ? done.take() : done.poll();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                throw new IllegalStateException("the walk was interrupted"
                        + " waiting for a step");
            }
            for (; ended != null; ended = done.poll()) {
                running--;
                Demand demand = (Demand) ended[0];
                if (steps.get(demand) == RUNNING) {
                    steps.put(demand, ended[1]);
                }
            }
        }

        void drain() {
            while (running > 0) received(true);
            steps.clear();
        }

        private static final int PART = 16;
        private static final int PARTS = 192;

        <T, R> List<R> each(List<T> items, Function<T, R> each) {
            int size = items.size();
            List<R> done = new ArrayList<R>(size);
            if (size < 2 * PART) {
                for (T item : items) done.add(each.apply(item));
                return done;
            }
            int parts = Math.min(PARTS, size / PART);
            List<ForkJoinTask<List<R>>> asked =
                    new ArrayList<ForkJoinTask<List<R>>>(parts);
            for (int part = 0; part < parts; part++) {
                int from = (int) ((long) size * part / parts);
                int to = (int) ((long) size * (part + 1) / parts);
                asked.add(ForkJoinTask.adapt(() -> {
                    List<R> one = new ArrayList<R>(to - from);
                    for (int at = from; at < to; at++) {
                        one.add(each.apply(items.get(at)));
                    }
                    return one;
                }));
            }
            run(asked);
            for (ForkJoinTask<List<R>> part : asked) {
                done.addAll(part.join());
            }
            return done;
        }

        List<Demand> take(Demand demand) {
            while (steps.get(demand) == RUNNING) {
                received(true);
                launch(false);
            }
            Object held = current(demand);
            steps.remove(demand);
            if (held instanceof Thrown
                    && ((Thrown) held).thrown instanceof Error) {
                throw (Error) ((Thrown) held).thrown;
            }
            Step step = held instanceof Step
                    && restsOn.take(((Step) held).claims) ? (Step) held
                    : null;
            if (step == null) {
                step = step(this, new Step(this, demand,
                        reads(demand.occurrence)));
                if (!restsOn.take(step.claims)) {
                    throw new IllegalStateException("a walk in the order "
                            + "claimed a read's leaves another row holds: "
                            + demand.occurrence.render());
                }
            }
            return step.apply(this);
        }

        List<Set<String>> asked(
                List<Function<Corpus.Claims, Set<String>>> asks,
                Corpus.Claims claims) {
            int size = asks.size();
            List<Set<String>> done = new ArrayList<Set<String>>(size);
            if (size < 2 * PART) {
                for (Function<Corpus.Claims, Set<String>> ask : asks) {
                    done.add(ask.apply(claims));
                }
                return done;
            }
            int parts = Math.min(PARTS, size / PART);
            List<Corpus.Claims> partClaims = new ArrayList<Corpus.Claims>();
            List<ForkJoinTask<List<Set<String>>>> computed =
                    new ArrayList<ForkJoinTask<List<Set<String>>>>(parts);
            for (int part = 0; part < parts; part++) {
                int from = (int) ((long) size * part / parts);
                int to = (int) ((long) size * (part + 1) / parts);
                Corpus.Claims own = new Corpus.Claims();
                partClaims.add(own);
                computed.add(ForkJoinTask.adapt(() -> {
                    List<Set<String>> one =
                            new ArrayList<Set<String>>(to - from);
                    for (int at = from; at < to; at++) {
                        one.add(asks.get(at).apply(own));
                    }
                    return one;
                }));
            }
            run(computed);
            for (int part = 0; part < parts; part++) {
                List<Set<String>> one = computed.get(part).join();
                if (!claims.follow(partClaims.get(part))) {
                    int from = (int) ((long) size * part / parts);
                    int to = (int) ((long) size * (part + 1) / parts);
                    one = new ArrayList<Set<String>>(to - from);
                    for (int at = from; at < to; at++) {
                        one.add(asks.get(at).apply(claims));
                    }
                }
                done.addAll(one);
            }
            return done;
        }

        private <T> void run(List<ForkJoinTask<T>> tasks) {
            if (ForkJoinTask.getPool() == cores) {
                all(tasks);
            } else {
                cores.invoke(ForkJoinTask.adapt(() -> all(tasks)));
            }
        }

        private static <T> void all(List<ForkJoinTask<T>> tasks) {
            for (int at = tasks.size() - 1; at > 0; at--) tasks.get(at).fork();
            tasks.get(0).quietlyInvoke();
            for (int at = 1; at < tasks.size(); at++) {
                tasks.get(at).quietlyJoin();
            }
        }

        private List<OccurrenceAddress> group(OccurrenceAddress occurrence) {
            return groups.computeIfAbsent(occurrence.id(), id -> {
                List<OccurrenceAddress> group =
                        new ArrayList<OccurrenceAddress>();
                group.add(occurrence);
                group.addAll(stateConnected(corpus, occurrence));
                return Collections.unmodifiableList(group);
            });
        }

        GroupReads reads(OccurrenceAddress occurrence) {
            if (Thread.currentThread() != planner) {
                throw new AssertionError("a group indexed off the planner"
                        + " thread: " + occurrence.render());
            }
            return groupReads.computeIfAbsent(occurrence.id(), id -> {
                List<MemberReads> members = new ArrayList<MemberReads>();
                for (OccurrenceAddress member : group(occurrence)) {
                    members.add(memberReads.computeIfAbsent(member.id(),
                            key -> indexed(new MemberReads(corpus, member))));
                }
                return new GroupReads(members, naming, locating, returning);
            });
        }

        private MemberReads indexed(MemberReads member) {
            index(naming, member.at.keySet(), member);
            index(locating, member.symbolsAt.keySet(), member);
            index(returning, member.returning.keySet(), member);
            return member;
        }

        private static <K> void index(Map<K, MemberReads[]> into,
                                      Set<K> keys, MemberReads member) {
            MemberReads[] one = {member};
            for (K key : keys) {
                into.merge(key, one, (held, added) -> {
                    MemberReads[] grown = Arrays.copyOf(held, held.length + 1);
                    grown[held.length] = member;
                    return grown;
                });
            }
        }

        private Set<String> guardsAt(String recordedSite) {
            Set<String> held = guards.get(recordedSite);
            if (held != null) return held;
            held = new LinkedHashSet<String>();
            for (StaticScopeMap.Site site : map.sitesAt(recordedSite)) {
                held.addAll(site.guards);
            }
            Set<String> first = guards.putIfAbsent(recordedSite, held);
            return first != null ? first : held;
        }

        private List<StaticScopeMap.Site> writersOf(String carrier) {
            List<StaticScopeMap.Site> held = writers.get(carrier);
            if (held != null) return held;
            held = map.writersOf(carrier);
            List<StaticScopeMap.Site> first = writers.putIfAbsent(carrier,
                    held);
            return first != null ? first : held;
        }

        private List<OccurrenceAddress> holders(StaticScopeMap.Site site,
                                                NodeId node,
                                                boolean unrecorded) {
            List<Object> key = Arrays.<Object>asList(site, node, unrecorded);
            List<OccurrenceAddress> found = holders.get(key);
            if (found != null) return found;
            found = new ArrayList<OccurrenceAddress>();
            for (OccurrenceAddress occurrence : corpus.occurrences()) {
                if (!holds(map, occurrence.regionId(), site)
                        || node != null && !RuntimeSelectedRegionFinalizer.pairs(
                                node.render(), occurrence.node().render(),
                                corpus.client(node),
                                corpus.client(occurrence.node()))) {
                    continue;
                }
                if (unrecorded ? !activated(corpus, occurrence)
                        && !corpus.activationsOf(occurrence).isEmpty()
                        && !view.holds(entered(occurrence))
                        : activated(corpus, occurrence)) {
                    found.add(occurrence);
                }
            }
            List<OccurrenceAddress> first = holders.putIfAbsent(key, found);
            return first != null ? first : found;
        }

        private boolean holdsOthersOnly(OccurrenceAddress occurrence,
                                        String sessionId,
                                        LocationId location) {
            if (location.kind() == LocationKind.STATIC
                    || !Arms.namedOwner(location)) {
                return false;
            }
            SessionReader session = corpus.session(sessionId);
            ActivationRow ran = corpus.activation(sessionId, occurrence);
            if (session != null && session.manifest().doorsOnly()
                    .contains(occurrence.render())
                    || ran == null || !ran.instrumented()) {
                return false;
            }
            String key = sessionId + "|" + occurrence.id();
            Set<String> owners = held.get(key);
            if (owners == null) {
                owners = new HashSet<String>();
                for (ReadRow read : corpus.readsOn(sessionId, occurrence)) {
                    owners.add(read.location().owner());
                }
                for (WriteRow write : corpus.writesOn(sessionId, occurrence)) {
                    owners.add(write.location().owner());
                }
                Set<String> first = held.putIfAbsent(key, owners);
                if (first != null) owners = first;
            }
            return !owners.isEmpty() && !owners.contains(location.owner());
        }
    }

    private static Step step(Walk walk, Step step) {
        Demand demand = step.demand;
        GroupReads group = step.group;
        Corpus corpus = walk.corpus;
        Map<String, Set<String>> kept = new LinkedHashMap<String,
                Set<String>>();
        Named named = demanded(walk, step, kept);
        Named demanded = named;
        List<Object> expanding = new ArrayList<Object>();
        if (named.whole) {
            for (int place = 0; place < group.members.size(); place++) {
                MemberReads member = group.members.get(place);
                for (AttachRow attach : member.attaches) {
                    if (!demanded.holds(attach.symbol())) {
                        step.unread(expanding, attach.sessionId(),
                                attach.endpoint(), "handoff");
                    } else if (step.pair(attach.sessionId(),
                            attach.symbol())) {
                        expanding.add(attach);
                    }
                }
                for (int at = 0; at < member.rows.size(); at++) {
                    ReadRow row = member.rows.get(at);
                    if (!demanded.holds(row.symbol())) {
                        step.unread(expanding, row.sessionId(),
                                row.endpoint(), "state read");
                    } else if (step.expand(place, at)) {
                        expanding.add(row);
                    }
                }
            }
        } else {
            for (long at : group.placesOf(named.fresh)) {
                int place = (int) (at >>> 32);
                MemberReads member = group.members.get(place);
                int item = (int) at;
                if (item < member.attaches.size()) {
                    AttachRow attach = member.attaches.get(item);
                    if (step.pair(attach.sessionId(), attach.symbol())) {
                        expanding.add(attach);
                    }
                } else {
                    int read = item - member.attaches.size();
                    if (step.expand(place, read)) {
                        expanding.add(member.rows.get(read));
                    }
                }
            }
        }
        for (Object said : walk.each(expanding, item -> {
            if (item instanceof Said) return item;
            Says part = new Says(walk, demand);
            if (item instanceof AttachRow) {
                producers(walk, (AttachRow) item, part);
            } else {
                writers(walk, (ReadRow) item, part);
            }
            return part;
        })) {
            if (said instanceof Said) {
                step.said.add((Said) said);
            } else {
                step.say((Says) said);
            }
        }
        for (Map.Entry<String, Set<String>> session : kept.entrySet()) {
            for (String symbol : session.getValue()) {
                AttachRow attach = corpus.attach(session.getKey(), symbol);
                if (attach != null && attach.seq()
                        < corpus.forcedFrom(session.getKey())
                        && step.pair(session.getKey(), symbol)) {
                    producers(walk, attach, step);
                }
            }
        }
        statedReads(walk, step);
        if (step.value) {
            controlProducer(walk, step);
        } else if (CONTROL_PRODUCER.equals(step.why)
                && !walk.corpus.startedBy(demand.occurrence).isEmpty()) {
            step.once(demand.occurrence.id() + "|producer",
                    () -> GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    demand.occurrence.render(), "a control producer "
                            + "contributes no value: the doors of the message"
                            + " that started it are not asked"));
        }
        return step;
    }

    private static void keep(Map<String, Set<String>> kept, String session,
                             Set<String> symbols) {
        kept.computeIfAbsent(session, key -> new LinkedHashSet<String>())
                .addAll(symbols);
    }

    private static void controlProducer(Walk walk, Step step) {
        Corpus corpus = walk.corpus;
        for (String endpoint : corpus.startedBy(step.demand.occurrence)) {
            doorsOf(walk, step, endpoint);
        }
        for (OccurrenceAddress reader
                : corpus.replyLegsOf(step.demand.occurrence)) {
            if (walk.faulted(reader)) {
                step.next(new Demand(reader, CONTROL_PRODUCER, false));
            } else {
                step.faultless(reader.id(), () -> GapRow.of(
                        ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                        GapClass.DIAGNOSTIC, reader.render(), "a reader of"
                                + " the reply to a request "
                                + step.demand.occurrence.render()
                                + " sent decided no fault in any session, so"
                                + " nothing of it decides whether the sender"
                                + " sees the reply: no control producer"));
            }
        }
    }

    private static void doorsOf(Walk walk, Step step, String endpoint) {
        Corpus corpus = walk.corpus;
        Demand demand = step.demand;
        Map<String, Integer> cut = new LinkedHashMap<String, Integer>();
        List<OccurrenceAddress> doors = corpus.doorsOf(endpoint,
                demand.occurrence, cut);
        for (Map.Entry<String, Integer> each : cut.entrySet()) {
            step.once(demand.occurrence.id() + "|" + endpoint + "|"
                    + each.getKey(), () -> GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    demand.occurrence.render(), each.getValue()
                            + " occurrence(s) of " + (Corpus.OWN_TURN.equals(
                            each.getKey()) ? "this occurrence's own turn"
                            : "turns standing on the message (its handlers)")
                            + " hold no door of message " + endpoint
                            + " that started it: they are what it started"));
        }
        OccurrenceAddress sender = corpus.senderOf(endpoint);
        for (OccurrenceAddress door : doors) {
            if (door.equals(demand.occurrence)) continue;
            if (step.storeWriter && door.equals(sender)) {
                step.next(new Demand(door, STORE_ITEM_PRODUCER, false));
            } else if (walk.faulted(door)) {
                step.next(new Demand(door, CONTROL_PRODUCER, false));
            } else {
                step.faultless(door.id(), () -> GapRow.of(
                        ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        door.render(), "a door of the message that started "
                                + demand.occurrence.render() + " decided no "
                                + "fault in any session, so nothing of it "
                                + "decides whether the message exists: no "
                                + "control producer"));
            }
        }
    }

    private static void statedReads(Walk walk, Step step) {
        Demand demand = step.demand;
        if (demand.anchor) {
            anchorReads(walk, step);
            return;
        }
        int index = 0;
        int done = step.contributed;
        step.contributed = step.values.size();
        for (String contributed : step.values) {
            if (index++ < done) continue;
            int split = contributed.indexOf('|');
            if (split < 0) continue;
            String sessionId = contributed.substring(0, split);
            for (Corpus.StateRead read : walk.corpus.expressionStateReads(
                    sessionId, contributed.substring(split + 1))) {
                writersOfVersion(walk, step, sessionId, demand.occurrence,
                        read.write().location(), read.write().version(),
                        walk.map.carriersAt(read.site(), read.javaType(),
                                read.write().location().kind()), null,
                        demand.occurrence.id(), demand.occurrence::render,
                        () -> read.locationKey() + " (read at event "
                                + read.readEventId() + ")");
            }
        }
    }

    private static void anchorReads(Walk walk, Step step) {
        Demand demand = step.demand;
        Corpus corpus = walk.corpus;
        List<String[]> terms = new ArrayList<String[]>();
        for (Corpus.RecordedPath path : corpus.pathsOf(demand.occurrence)) {
            for (DecisionRow decision : path.decisions) {
                if (FlipQuery.asks(step.flipSites, decision)) {
                    terms.add(new String[] {path.sessionId,
                            decision.term()});
                }
            }
        }
        for (TargetRow target : corpus.targetsOn(demand.occurrence)) {
            terms.add(new String[] {target.sessionId(), target.phiTerm()});
        }
        for (String[] term : terms) {
            java.util.regex.Matcher refs = Corpus.EXPRESSION_REF.matcher(
                    term[1] == null ? "" : term[1]);
            while (refs.find()) {
                if (!walk.anchorTerms.add(term[0] + "|" + refs.group())) {
                    continue;
                }
                for (Corpus.StateRead read : corpus.expressionStateReads(
                        term[0], refs.group())) {
                    writersOfVersion(walk, step, term[0], demand.occurrence,
                            read.write().location(), read.write().version(),
                            walk.map.carriersAt(read.site(), read.javaType(),
                                    read.write().location().kind()), null,
                            demand.occurrence.id(), demand.occurrence::render,
                            () -> read.locationKey() + " (read at event "
                                    + read.readEventId() + ")");
                }
            }
        }
    }

    private static Named demanded(Walk walk, Step step,
                                  Map<String, Set<String>> kept) {
        Demand demand = step.demand;
        Corpus corpus = walk.corpus;
        GroupReads reads = step.group;
        List<String> sessions = new ArrayList<String>();
        List<Function<Corpus.Claims, Set<String>>> asks =
                new ArrayList<Function<Corpus.Claims, Set<String>>>();
        if (demand.anchor) {
            for (Corpus.RecordedPath path : walk.restsOn.admitted(
                    new ArrayList<GapRow>())) {
                TargetRow target = corpus.target(path.sessionId,
                        demand.occurrence);
                if (target == null) continue;
                sessions.add(path.sessionId);
                asks.add(claims -> walk.restsOn.ofPath(path.sessionId,
                        target, path.decisions, claims));
            }
        }
        Map<String, List<String>> delivered =
                Demand.delivered(step.values);
        for (Map.Entry<String, Long> cutoff : step.cutoffs.entrySet()) {
            String session = cutoff.getKey();
            long at = cutoff.getValue();
            List<String> refs = Demand.delivered(delivered, session);
            sessions.add(session);
            asks.add(claims -> walk.restsOn.ofDelivery(session,
                    demand.occurrence, at, refs, claims));
        }
        List<Set<String>> answers = walk.asked(asks, step.claims);
        for (int at = 0; at < answers.size(); at++) {
            keep(kept, sessions.get(at), answers.get(at));
        }
        Set<String> keeps = new OpenSet<String>();
        for (Set<String> symbols : kept.values()) keeps.addAll(symbols);
        Named named = demand.named;
        named = named == null || !keeps.containsAll(named.kept)
                ? new Named() : new Named(named);
        step.named = named;
        named.kept = keeps;
        List<Supplier<List<Collection<String>>>> decided =
                new ArrayList<Supplier<List<Collection<String>>>>();
        for (Corpus.RecordedPath path : corpus.pathsOf(demand.occurrence)) {
            for (DecisionRow decision : path.decisions) {
                if (!FlipQuery.asks(step.flipSites, decision)
                        || !named.decide(decision)) {
                    continue;
                }
                decided.add(() -> termNames(corpus, reads, path.sessionId,
                        decision.term()));
            }
        }
        for (List<Collection<String>> names : walk.each(decided,
                Supplier::get)) {
            for (Collection<String> symbols : names) named.addAll(symbols);
        }
        if (demand.anchor && named.whole) {
            for (TargetRow target : corpus.targetsOn(demand.occurrence)) {
                for (Collection<String> symbols : termNames(corpus, reads,
                        target.sessionId(), target.phiTerm())) {
                    named.addAll(symbols);
                }
            }
            named.addAll(demand.predicate);
        }
        int index = 0;
        int done = named.contributed;
        named.contributed = step.values.size();
        List<String> values = new ArrayList<String>();
        for (String contributed : step.values) {
            if (index++ < done) continue;
            if (contributed.indexOf('|') >= 0) values.add(contributed);
        }
        for (Set<String> symbols : walk.each(values, contributed -> {
            int split = contributed.indexOf('|');
            return corpus.expressionSymbols(contributed.substring(0, split),
                    contributed.substring(split + 1));
        })) {
            named.addAll(symbols);
        }
        named.addAll(keeps);
        for (int next = 0; next < named.fresh.size(); ) {
            int end = named.fresh.size();
            for (List<Collection<String>> brought : walk.each(
                    new ArrayList<String>(named.fresh.subList(next, end)),
                    symbol -> brought(corpus, reads, symbol))) {
                for (Collection<String> symbols : brought) {
                    named.addAll(symbols);
                }
            }
            next = end;
        }
        return named;
    }

    private static List<Collection<String>> termNames(Corpus corpus,
                                                      GroupReads reads,
                                                      String sessionId,
                                                      String term) {
        List<Collection<String>> names = new ArrayList<Collection<String>>();
        names.add(corpus.termSymbols(sessionId, term));
        reads.under(corpus, sessionId, term, names);
        return names;
    }

    private static List<Collection<String>> brought(Corpus corpus,
                                                    GroupReads reads,
                                                    String symbol) {
        List<Collection<String>> brought = new ArrayList<Collection<String>>();
        for (ReadRow row : reads.of(symbol)) {
            reads.holding(row, brought);
            for (WriteRow write : corpus.eligibleWrites(row.sessionId(),
                    SmtLowering.locationKey(row.location()),
                    row.observedVersion(), row.endpoint().occurrence())) {
                brought.add(corpus.expressionSymbols(write.sessionId(),
                        write.expressionRef()));
            }
        }
        return brought;
    }

    static final class MemberReads {
        private final List<AttachRow> attaches;
        private final List<ReadRow> rows;
        private final Map<String, List<ReadRow>> bySymbol =
                new HashMap<String, List<ReadRow>>();
        private final Map<String, int[]> at = new HashMap<String, int[]>();
        private final Map<List<String>, Set<String>> symbolsAt =
                new HashMap<List<String>, Set<String>>();
        private final Map<List<String>, Set<String>> returning =
                new HashMap<List<String>, Set<String>>();

        private MemberReads(Corpus corpus, OccurrenceAddress member) {
            attaches = corpus.attachesOn(member);
            rows = corpus.readsOn(member);
            Map<String, List<Integer>> places =
                    new HashMap<String, List<Integer>>();
            for (int index = 0; index < attaches.size(); index++) {
                places.computeIfAbsent(attaches.get(index).symbol(),
                        symbol -> new ArrayList<Integer>()).add(index);
            }
            for (int index = 0; index < rows.size(); index++) {
                ReadRow row = rows.get(index);
                places.computeIfAbsent(row.symbol(),
                        symbol -> new ArrayList<Integer>())
                        .add(attaches.size() + index);
                bySymbol.computeIfAbsent(row.symbol(),
                        symbol -> new ArrayList<ReadRow>()).add(row);
                if (row.symbol().isEmpty()) continue;
                symbolsAt.computeIfAbsent(Arrays.asList(row.sessionId(),
                                SmtLowering.locationKey(row.location())),
                        key -> new LinkedHashSet<String>())
                        .add(row.symbol());
                long object = VmRows.referencedObjectRid(
                        row.concreteValue());
                if (object > 0L) {
                    returning.computeIfAbsent(Arrays.asList(row.sessionId(),
                                    Long.toString(object)),
                            key -> new LinkedHashSet<String>())
                            .add(row.symbol());
                }
            }
            for (Map.Entry<String, List<Integer>> each : places.entrySet()) {
                int[] held = new int[each.getValue().size()];
                for (int index = 0; index < held.length; index++) {
                    held[index] = each.getValue().get(index);
                }
                at.put(each.getKey(), held);
            }
            symbolsAt.replaceAll((key, symbols) -> FrozenSet.of(symbols));
            returning.replaceAll((key, symbols) -> FrozenSet.of(symbols));
            Held.trimmed(bySymbol);
        }
    }

    static final class GroupReads {
        final List<MemberReads> members;
        private final Map<MemberReads, Integer> place =
                new java.util.IdentityHashMap<MemberReads, Integer>();
        private final Map<String, MemberReads[]> naming;
        private final Map<List<String>, MemberReads[]> locating;
        private final Map<List<String>, MemberReads[]> returning;

        private final int[] readBase;

        private GroupReads(List<MemberReads> members,
                           Map<String, MemberReads[]> naming,
                           Map<List<String>, MemberReads[]> locating,
                           Map<List<String>, MemberReads[]> returning) {
            this.members = members;
            this.readBase = new int[members.size()];
            int reads = 0;
            for (int index = 0; index < members.size(); index++) {
                place.put(members.get(index), index);
                readBase[index] = reads;
                reads += members.get(index).rows.size();
            }
            this.naming = naming;
            this.locating = locating;
            this.returning = returning;
        }

        int readAt(int member, int row) {
            return readBase[member] + row;
        }

        private List<MemberReads> in(MemberReads[] indexed) {
            if (indexed == null) return Collections.<MemberReads>emptyList();
            List<MemberReads> held = new ArrayList<MemberReads>(
                    indexed.length);
            for (MemberReads member : indexed) {
                if (place.containsKey(member)) held.add(member);
            }
            if (held.size() > 1) {
                held.sort((one, other) -> Integer.compare(place.get(one),
                        place.get(other)));
            }
            return held;
        }

        private void holding(ReadRow row, List<Collection<String>> into) {
            if (row.location().kind() != LocationKind.MAP) return;
            List<String> key = Arrays.asList(row.sessionId(),
                    row.location().owner());
            for (MemberReads member : in(returning.get(key))) {
                into.add(member.returning.get(key));
            }
        }

        List<ReadRow> of(String symbol) {
            List<ReadRow> rows = Collections.<ReadRow>emptyList();
            boolean own = false;
            for (MemberReads member : in(naming.get(symbol))) {
                List<ReadRow> stated = member.bySymbol.get(symbol);
                if (stated == null) continue;
                if (rows.isEmpty()) {
                    rows = stated;
                    continue;
                }
                if (!own) {
                    rows = new ArrayList<ReadRow>(rows);
                    own = true;
                }
                rows.addAll(stated);
            }
            return rows;
        }

        long[] placesOf(Collection<String> symbols) {
            List<long[]> found = new ArrayList<long[]>();
            int count = 0;
            for (String symbol : symbols) {
                for (MemberReads member : in(naming.get(symbol))) {
                    int[] places = member.at.get(symbol);
                    long high = (long) place.get(member) << 32;
                    long[] held = new long[places.length];
                    for (int index = 0; index < places.length; index++) {
                        held[index] = high | places[index];
                    }
                    found.add(held);
                    count += held.length;
                }
            }
            long[] all = new long[count];
            int next = 0;
            for (long[] held : found) {
                System.arraycopy(held, 0, all, next, held.length);
                next += held.length;
            }
            Arrays.sort(all);
            return all;
        }

        private void under(Corpus corpus, String sessionId, String term,
                           List<Collection<String>> into) {
            for (String location : corpus.readLocations(sessionId, term)) {
                List<String> key = Arrays.asList(sessionId, location);
                for (MemberReads member : in(locating.get(key))) {
                    into.add(member.symbolsAt.get(key));
                }
            }
        }
    }

    private static void unread(Walk walk, String sessionId,
                               Endpoint endpoint, String what) {
        if (!walk.unread.computeIfAbsent(what,
                unused -> ConcurrentHashMap.newKeySet()).add(endpoint.id())) {
            return;
        }
        walk.gaps.accept(GapRow.of(sessionId, GapKind.ADMISSION_GAP,
                GapClass.DIAGNOSTIC, endpoint.toString(),
                "no demanded value of this occurrence rests on this " + what
                        + ", so its producer is not a task"));
    }

    private static void producers(Walk walk, AttachRow attach, Says step) {
        String portId = attach.endpoint().site();
        List<StaticScopeMap.Site> exports = walk.map.exportsOf(portId);
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : exports) {
            guards.addAll(site.guards);
        }
        if (attach.producer() == null) {
            step.once(attach.endpoint().id() + "|unpaired",
                    () -> GapRow.of(attach.sessionId(),
                        GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                        attach.endpoint().toString(), "attach is unpaired:"
                                + " no producer endpoint to close over"));
        } else {
            crossCheck(attach, step);
            Demand paired = new Demand(attach.producer().occurrence(),
                    CLOSURE_MEMBER, walk.contribution(attach.producer()));
            paired.flipSites.addAll(guards);
            step.next(paired);
        }
        NodeId sender = attach.producer() == null ? null
                : attach.producer().occurrence().node();
        for (StaticScopeMap.Site site : exports) {
            candidates(walk, site, STATIC_CANDIDATE_PRODUCER, guards, step,
                    attach.sessionId(), "port " + portId, sender, null, false);
        }
    }

    private static void writers(Walk walk, ReadRow row, Says step) {
        if (row.location().kind() == LocationKind.STORE) {
            storeWriters(walk, row, step);
            storeFetches(walk, row, step);
            return;
        }
        writersOfVersion(walk, step, row.sessionId(),
                row.endpoint().occurrence(),
                row.location(), row.observedVersion(),
                walk.map.carriersAt(row.endpoint().site(), row.javaType(),
                        row.location().kind()),
                row, row.endpoint().id(), row.endpoint()::toString,
                () -> String.valueOf(row.location()));
    }

    private static void writersOfVersion(Walk walk, Says step,
                                         String sessionId,
                                         OccurrenceAddress reader,
                                         LocationId location,
                                         long observedVersion,
                                         Set<String> readCarriers,
                                         ReadRow read, String readAt,
                                         Supplier<String> subject,
                                         Supplier<String> located) {
        Corpus corpus = walk.corpus;
        String locationKey = SmtLowering.locationKey(location);
        Set<String> carriers = new LinkedHashSet<String>();
        for (WriteRow write : corpus.writeSitesOf(locationKey)) {
            carriers.addAll(walk.map.carriersAt(write.endpoint().site(),
                    write.javaType(), write.location().kind()));
        }
        carriers.addAll(readCarriers);
        for (WriteRow write : corpus.eligibleWrites(sessionId, locationKey,
                observedVersion, reader)) {
            wrote(walk, write, step);
            if (read == null) continue;
            for (WriteRow state : corpus.referentStates(write, read)) {
                wrote(walk, state, step);
            }
        }
        if (carriers.isEmpty() && walk.map.stated()) {
            step.once(readAt + "|" + field(location) + "|carrier",
                    () -> GapRow.of(sessionId,
                        GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        subject.get(), "no recorded write of "
                                + located.get() + " matches a write site of"
                                + " the static map, so this location's "
                                + "carrier is unnamed and no static "
                                + "candidate writer of it can be"));
            return;
        }
        boolean unrecorded = unrecorded(corpus, sessionId, locationKey,
                observedVersion);
        for (String carrier : carriers) {
            for (StaticScopeMap.Site site : walk.writersOf(carrier)) {
                candidates(walk, site, STATIC_CANDIDATE_WRITER, site.guards,
                        step, sessionId, "carrier " + carrier, reader.node(),
                        location, unrecorded && !walk.view.holds(carrier));
            }
        }
    }

    private static boolean unrecorded(Corpus corpus, String sessionId,
                                      String locationKey, long version) {
        if (version < 0L) return false;
        for (WriteRow write : corpus.writesOf(sessionId, locationKey)) {
            if (write.version() == version && !write.initial()) return false;
        }
        return true;
    }

    private static void storeWriters(Walk walk, ReadRow row, Says step) {
        for (WriteRow write : walk.corpus.eligibleWrites(row.sessionId(),
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), row.endpoint().occurrence())) {
            wrote(walk, write, step);
        }
    }

    private static void storeFetches(Walk walk, ReadRow row, Says step) {
        NodeId reader = row.endpoint().occurrence().node();
        boolean asked = false;
        for (String fetch : walk.map.storeFetches(row.location().owner(),
                row.location().slot())) {
            OccurrenceAddress occurrence = OccurrenceAddress.parse(fetch);
            if (reader.equals(occurrence.node())) {
                step.next(new Demand(occurrence, STORE_FETCH, false));
                asked = true;
            }
        }
        String location = SmtLowering.locationKey(row.location());
        if (!asked) {
            step.once(location + "|" + reader.render() + "|fetch",
                    () -> GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    location + " @ " + reader.render(), "a demanded store"
                            + " read of this location on this node rests on"
                            + " no fetch PLAN asked (it asks the fetches of"
                            + " what its targets read), so no read door on"
                            + " its flow is flippable"));
        }
    }

    private static void earlierVersions(Walk walk, WriteRow write,
                                        List<Demand> into) {
        String key = SmtLowering.locationKey(write.location());
        Long first = walk.storeExpanded.putIfAbsent(write.sessionId() + "|"
                + key, write.version());
        if (first != null && first >= write.version()) return;
        for (WriteRow earlier : walk.corpus.writesOf(write.sessionId(), key)) {
            if (earlier.initial() || earlier.version() >= write.version()
                    || first != null && earlier.version() < first) {
                continue;
            }
            into.add(writer(walk, earlier));
        }
        if (first != null) {
            walk.storeExpanded.put(write.sessionId() + "|" + key,
                    write.version());
        }
    }

    private static void wrote(Walk walk, WriteRow write, Says step) {
        if (write.initial()) return;
        step.writer(write);
        if (write.location().kind() == LocationKind.STORE) {
            step.earlier(write);
        }
    }

    private static Demand writer(Walk walk, WriteRow write) {
        Demand paired = new Demand(write.endpoint().occurrence(),
                CLOSURE_MEMBER, false);
        paired.contributes(write.sessionId(), write.expressionRef(),
                write.seq());
        paired.flipSites.addAll(walk.guardsAt(write.endpoint().site()));
        paired.storeWriter = write.location().kind() == LocationKind.STORE;
        paired.madeOf = write;
        return paired;
    }

    private static void candidates(Walk walk, StaticScopeMap.Site site,
                                   String why, Collection<String> guards,
                                   Says step, String sessionId,
                                   String what, NodeId node,
                                   LocationId location, boolean unrecorded) {
        List<OccurrenceAddress> holders = walk.holders(site, node, false);
        step.offer(Arrays.<Object>asList(why, site, guards, node),
                holders, why, guards, sessionId, location);
        if (unrecorded) {
            List<OccurrenceAddress> ran = walk.holders(site, node, true);
            step.offer(Arrays.<Object>asList(UNRECORDED_WRITER, site, guards,
                    node), ran, UNRECORDED_WRITER, guards, sessionId,
                    location);
            Set<OccurrenceAddress> lacked = walk.unrecorded.computeIfAbsent(
                    sessionId, key -> ConcurrentHashMap.newKeySet());
            lacked.addAll(holders);
            lacked.addAll(ran);
            if (!ran.isEmpty()) return;
        }
        if (!holders.isEmpty()) return;
        step.gap(Arrays.<Object>asList(why, sessionId, site.regionId,
                site.siteId, what, String.valueOf(node)),
                () -> GapRow.of(sessionId, GapKind.ADMISSION_GAP,
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

    private static String entered(OccurrenceAddress occurrence) {
        List<Frame> frames = occurrence.index().frames();
        if (frames.isEmpty()) return "";
        String site = frames.get(0).callSite();
        String method = SiteId.methodOf(site);
        return method.isEmpty() ? site : method;
    }

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

    private static boolean activated(Corpus corpus,
                                     OccurrenceAddress occurrence) {
        for (ActivationRow row : corpus.activationsOf(occurrence)) {
            if (row.instrumented()) return true;
        }
        return false;
    }

    private static void crossCheck(AttachRow attach, Says step) {
        CausalContext context = attach.endpoint().occurrence().context();
        if (!(context instanceof CausalContext.Anchor)) return;
        String anchored = ((CausalContext.Anchor) context)
                .producerEndpointId();
        String recorded = attach.producer().id();
        if (anchored.equals(recorded)) return;
        step.once(attach.endpoint().id() + "|" + recorded + "|pairing",
                () -> GapRow.of(attach.sessionId(),
                GapKind.TOPOLOGY_DIVERGENCE,
                GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                "the recorded pairing names producer endpoint " + recorded
                        + " and the consumer's causal anchor names "
                        + anchored + "; the closure follows the recorded "
                        + "pairing"));
    }

    private static String field(LocationId location) {
        boolean rid = location.kind() != LocationKind.STATIC
                && location.kind() != LocationKind.VIEW
                && Arms.namedOwner(location);
        return location.kind() + " " + (rid ? "" : location.owner()) + "."
                + location.slot();
    }

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

    private static boolean ran(Corpus corpus, String sessionId,
                               OccurrenceAddress occurrence) {
        ActivationRow activation = corpus.activation(sessionId, occurrence);
        return activation != null
                && (activation.instrumented() || occurrence.role())
                || !corpus.decisionsOf(sessionId, occurrence).isEmpty();
    }
}
