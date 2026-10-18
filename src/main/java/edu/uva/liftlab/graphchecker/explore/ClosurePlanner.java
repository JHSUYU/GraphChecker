package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.VmRows;

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
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.HeapWatch;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
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
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * The target's closure: what its failure can depend on, and the branches
 * exploration may flip in it (PIPELINE §7.2).
 *
 * <p>Demand starts at the ANNOTATED TARGET: the fatal predicate's operands and
 * the target's guard set ({@link StaticScopeMap}), or, where every admitted
 * path decided it on no symbol, the shared state on its guards' cone it read
 * before it decided ({@link #concrete}). Deliveries no demanded value rests
 * on are not followed. Each boundary variable grows it:</p>
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
    /** How many static candidate writers and producers one anchor's closure
     *  plans before the rest are cut ({@code region_path_max_tasks}); the
     *  occurrences the rows connect are never counted ({@link Candidates}). */
    public static final int DEFAULT_MAX_TASKS = 64;

    /** The runaway guard: past this many occurrences the rows connect
     *  (static candidates not counted), the rest of them are cut too, and so
     *  is every static candidate (a recorded writer is never cut while one
     *  is kept); the cut is a declared bound (result.json {@code bounded},
     *  {@code region_path_closure_ceiling}), never a silently unlimited plan
     *  (solr-adhoc-07's whole row-connected closure is 252). */
    public static final int CLOSURE_CEILING = 1024;

    /** Connected by rows. */
    public static final String CLOSURE_MEMBER = "CLOSURE_MEMBER";
    /** Sent the message a member served. */
    public static final String CONTROL_PRODUCER = "CONTROL_PRODUCER";
    /** Sent an item a member that wrote a demanded store version applied
     *  ({@link #doorsOf}): the version rests on its content. */
    public static final String STORE_ITEM_PRODUCER = "STORE_ITEM_PRODUCER";
    /** Fetched, on a target's data flow, a store location a member read
     *  ({@link #storeFetches}). */
    public static final String STORE_FETCH = "STORE_FETCH";
    /** Holds a static write site of a demanded location. */
    public static final String STATIC_CANDIDATE_WRITER =
            "STATIC_CANDIDATE_WRITER";
    /** Holds a static export site of a demanded port. */
    public static final String STATIC_CANDIDATE_PRODUCER =
            "STATIC_CANDIDATE_PRODUCER";

    /**
     * THE PLANNER HOST'S CORES, which a walk runs its demands' steps on
     * ahead of taking them ({@link Walk#ahead}).
     */
    static final ForkJoinPool CORES = new ForkJoinPool(
            Runtime.getRuntime().availableProcessors());

    private ClosurePlanner() {
    }

    /** The closure of one anchor, and what could not be named in it. */
    public static final class Plan {
        public final List<Task> tasks;
        public final List<GapRow> gaps;
        /** task id -> why it is in the closure. */
        public final Map<String, String> why;
        /** task id -> site ids this round may flip. */
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
        /** Of them, those the rows connect, cut past {@link
         *  #CLOSURE_CEILING}; the rest are static candidates cut past the
         *  task bound. */
        public final Set<String> ceilingCut;
        /** A demanded occurrence every session ran for its doors alone
         *  ({@code SessionManifest#doorsOnly}) that a value demand reached ->
         *  the admitted focused session whose replay is re-run once GROW has
         *  dropped the mark, or "" for none (the mark only dropped): it is
         *  no value's capture until a replay ran it whole. */
        public final Map<OccurrenceAddress, String> unpaused;
        /** Demanded as a value, run for its doors alone by every session
         *  that captured it, and ran by no focused replay GROW could re-run:
         *  a gap the fixed point makes BLOCKING ({@link ExploreMain}). */
        public final Set<OccurrenceAddress> runWhole;
        /** What every admitted path decided the anchor on, when that is no
         *  symbol ({@link ClosurePlanner#concrete}): no root reaches it yet,
         *  which only {@link ExploreMain} can weigh.  Null for any other
         *  anchor. */
        public final Concrete concrete;

        private Plan(List<Task> tasks, List<GapRow> gaps,
                     Map<String, String> why,
                     Map<String, Set<String>> flipSites,
                     Map<OccurrenceAddress, String> exposed,
                     Set<OccurrenceAddress> waiting, Set<String> truncated,
                     Set<String> ceilingCut,
                     Map<OccurrenceAddress, String> unpaused,
                     Set<OccurrenceAddress> runWhole, Concrete concrete) {
            this.unpaused = Collections.unmodifiableMap(unpaused);
            this.runWhole = Collections.unmodifiableSet(runWhole);
            this.tasks = Collections.unmodifiableList(tasks);
            this.gaps = Collections.unmodifiableList(gaps);
            this.why = Collections.unmodifiableMap(why);
            this.flipSites = Collections.unmodifiableMap(flipSites);
            this.exposed = Collections.unmodifiableMap(exposed);
            this.waiting = Collections.unmodifiableSet(waiting);
            this.truncated = Collections.unmodifiableSet(truncated);
            this.ceilingCut = Collections.unmodifiableSet(ceilingCut);
            this.concrete = concrete;
        }
    }

    /** A concrete anchor ({@link ClosurePlanner#concrete}): its admitted
     *  paths, how many of them decided it, and what it read on its path
     *  guards' cone before they did. */
    public static final class Concrete {
        /** The admitted paths at the anchor. */
        public final int paths;
        /** Of them, those that decided it: reached it, or left the way to
         *  the throw at a flip site. */
        public final int decided;
        /** Its predicate reads, in corpus order: the closure demands them. */
        public final List<ReadRow> reads;
        /** The reads it made before it decided off its path guards' cone:
         *  not demanded, counted ({@code ExploreMain#concreteRow}). */
        public final int offCone;

        private Concrete(int paths, int decided, List<ReadRow> reads,
                         int offCone) {
            this.paths = paths;
            this.decided = decided;
            this.reads = Collections.unmodifiableList(reads);
            this.offCone = offCone;
        }
    }

    /** The closure of one anchor; {@code branches} says which sessions may
     *  expose a region for growth, {@code doorsOnly} which occurrences the
     *  current plan runs for their doors alone (rendered addresses), {@code
     *  heldDoorsOnly} which of them the system declares so for good ({@code
     *  plan.DoorsOnlyRoots}), {@code faults} where a fault door fails,
     *  {@code view} the system's view classes, whose guards are no flip
     *  sites. */
    public static Plan plan(Corpus corpus, OccurrenceAddress anchor,
                            int maxTasks, StaticScopeMap scope,
                            Branches branches, Set<String> doorsOnly,
                            Set<String> heldDoorsOnly, ClientFaults faults,
                            SystemView view) {
        return plan(corpus, anchor, maxTasks, CLOSURE_CEILING, scope,
                branches, doorsOnly, heldDoorsOnly, faults, view);
    }

    /** {@link #plan} under another closure ceiling (a test's). */
    static Plan plan(Corpus corpus, OccurrenceAddress anchor, int maxTasks,
                     int ceiling, StaticScopeMap scope, Branches branches,
                     Set<String> doorsOnly, Set<String> heldDoorsOnly,
                     ClientFaults faults, SystemView view) {
        return plan(corpus, anchor, maxTasks, ceiling, scope, branches,
                doorsOnly, heldDoorsOnly, faults, view, CORES);
    }

    /** {@link #plan}, its steps on {@code cores} (a test's). */
    static Plan plan(Corpus corpus, OccurrenceAddress anchor, int maxTasks,
                     int ceiling, StaticScopeMap scope, Branches branches,
                     Set<String> doorsOnly, Set<String> heldDoorsOnly,
                     ClientFaults faults, SystemView view, ForkJoinPool cores) {
        Walk walk = new Walk(corpus, scope, anchor, cores);
        Map<String, Demand> demands = walk.demands;
        Deque<String> pending = walk.pending;
        Demand start = new Demand(anchor, CLOSURE_MEMBER, true);
        // The anchor flips only the decisions on its way to the throw: the
        // target's guard set (PIPELINE §7.2) and, when no admitted run of it
        // reached the throw (RestsOn#reached: a refused replay's reach states
        // nothing), the chain its path left by; flipping a chain guard of a
        // path that went on to the throw only leaves it.  A reached one also
        // asks, of each open decider arm a run left phi without
        // (TargetRow.OpenArm), the one decision whose flip runs it.  The
        // throw itself is no branch.
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
        // The anchor is the first occurrence the rows connect.
        int connectedPlanned = 1;
        int candidatesPlanned = 0;
        // The static candidates planned so far, and whether the rows'
        // demand reached the ceiling: then no candidate stays planned.
        Set<String> plannedCandidates = new LinkedHashSet<String>();
        boolean ceilingReached = false;
        try {
            while (true) {
                while (!pending.isEmpty()) {
                    // The demands behind the head are walked ahead on the cores,
                    // each against its state as its step starts ({@link
                    // Walk#ahead}), while the walk takes them in queue order,
                    // each step taken while it is the walk of its demand's state
                    // as it is taken, else walked again here ({@link
                    // Walk#take}).  So the walk is the one-at-a-time walk's,
                    // step for step (PIPELINE §7.2).
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
                            // A recorded writer is never cut while a static
                            // candidate is kept: the candidates planned so far
                            // leave the plan.
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
                // Row-connected demand is exhausted: the next static candidate,
                // while the bound has room -- the walks of the next ones
                // computed at once, each taken when its candidate is planned
                // while it is the walk of its state then ({@link Walk#prepare}).
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
            // No step runs on after the walk: each reads it.
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
            // Run for its doors alone by every session that captured it
            // (SessionManifest#doorsOnly), it is no value's capture: GROW
            // drops the mark (doorsOnly: the current plan's) and re-runs the
            // focused replay that ran it, else none is -- the seed is not
            // re-run -- and the fixed point names it (ExploreMain).  One
            // the system declares heavy (plan.DoorsOnlyRoots) stays so: the
            // values it writes are the recording's, named.
            if (demand.value
                    && heldDoorsOnly.contains(demand.occurrence.render())) {
                walk.gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
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
                walk.gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
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
            // Flip sites: the demanded guards plus every FAULT decision
            // (PIPELINE §7.2) where it fails (ClientFaults); never a guard
            // of the system's view classes (plan.SystemView): a node's
            // decode of a store version follows the version, and what else
            // it could read is its writer's to state -- no read alone sees
            // another value (SGF8 round 0 of 14, 39, 40: 615 such flips, 446
            // unsat, 123 replays not admitted, none admitted).
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
            walk.gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "VIEW_GUARDS_UNFLIPPED", viewed + " demanded guard(s) of"
                            + " the system's view classes are no flip sites:"
                            + " a node's decode of a store version follows"
                            + " the version, whose writer states what else"
                            + " it could hold"));
        }
        if (unfailed > 0) {
            walk.gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "CLIENT_FAULTS_UNFLIPPED", unfailed + " fault door(s)"
                            + " of the closure are no flip sites: "
                            + faults.why()));
        }
        return new Plan(tasks, new ArrayList<GapRow>(walk.gaps), why, flips,
                exposed, waiting, truncated, ceilingCut, unpaused, runWhole,
                concrete);
    }

    /** The method a site ({@code <method>#u<n>}) is in. */
    static String methodOf(String site) {
        int unit = site.lastIndexOf("#u");
        return unit < 0 ? site : site.substring(0, unit);
    }



    /**
     * THE TASK BOUND COUNTS STATIC CANDIDATES ONLY (owner: a genuinely large
     * closure converges; over budget, recorded writers first, the rest cut and
     * named: REGION_PATH_CLOSURE_TRUNCATED).  A demand the rows connect -- a recorded
     * writer or producer, a control producer, the anchor's own -- is planned
     * as it is found, never counted against the bound (only {@link
     * #CLOSURE_CEILING} stops it, a declared bound); a static candidate
     * writer or producer waits until no row-connected demand is left, and
     * then the candidates are planned round-robin over their (node, region,
     * context shape) class ({@link Corpus#classOf}), at most {@code
     * maxTasks} of them, so one class's
     * many occurrences never crowd out the rest (solr-adhoc-07 IB1: 59 of 64
     * tasks were {@code CoreContainer.getCore} candidates of {@code
     * SolrCores.cores} while two recorded {@code create} writers were cut;
     * its row-connected closure is 252 occurrences).  A candidate the rows
     * later connect is planned at once.
     */
    private static final class Candidates {
        private final Corpus corpus;
        /** occurrence id -> its waiting demand. */
        private final Map<String, Demand> waiting =
                new HashMap<String, Demand>();
        /** class -> its waiting candidates, in the order found. */
        private final Map<String, Deque<Demand>> byClass =
                new HashMap<String, Deque<Demand>>();
        /** The classes with a waiting candidate, the next one first. */
        private final Deque<String> turn = new ArrayDeque<String>();

        private Candidates(Corpus corpus) {
            this.corpus = corpus;
        }

        /** The demand to plan now, or null: a static candidate waits (and
         *  absorbs another reason to demand it); a row-connected demand of
         *  a waiting one takes it out of the wait. */
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

        /** The next waiting candidate, round-robin over the classes, or
         *  null when none waits. */
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

        /** The next {@code most} waiting candidates {@link #next} would
         *  give, as they wait now. */
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

    /**
     * D0 -- A CONCRETE ANCHOR DEMANDS WHAT IT READ BEFORE IT DECIDED
     * (R1-ROOTS §2.3, PIPELINE §7.2).
     *
     * <p>An admitted path (the seed, or a focused session admitted whole)
     * DECIDED the anchor where it took its arm: a reached anchor at its
     * target row, on its phi; an unreached one on its decisions at the flip
     * sites, the way to the throw, the last of them where it left it (none:
     * it decided nothing on that way).  The anchor is CONCRETE when some
     * admitted path is at it, none observed the fatal, and none decided it
     * on a recorded symbol: every path COMPOSE takes is refused ("decided
     * concretely on its healthy arm", or never reached), and nothing the
     * anchor's demand starts from names a value a flip could move -- the
     * closure was the anchor and its doors alone, and 195 of 260 finished
     * ad-hoc verdicts (h4, q12, q13) ended there with no gap saying why.  An
     * unreached path with a symbolic decision on the way is not concrete:
     * flipping it is how a replay reaches the throw (SOLR-18413's leader
     * leaves at a concrete test of the boolean a clock-decided {@code
     * isExpired} returned).</p>
     *
     * <p>Its PREDICATE READS are then the reads its deciding predicate
     * names (phi, or the decisions at the flip sites; by read event, so a
     * compound guard's later tests count though they read after the target
     * row's seq), and the shared-state reads the anchor made
     * before it decided, in each admitted path, that the root demand found
     * on the throw's path guards ({@link StaticScopeMap#demandedAt},
     * SYMBOL-SCOPE §4.6: the nearest read of each path back from the guards'
     * operands, tracked however many flows away, a value the VM keeps no
     * expression under -- a String, a reference, a container -- as well).
     * A read the occurrence made later cannot reach the decision it had
     * already taken; an earlier one off the guards' cone reaches it only
     * through a read on it, whose writers the closure then asks.  The
     * closure demands them as it demands the reads a symbolic predicate
     * names: their writers become tasks, flipped at their own guards and
     * fault sites, so a clock or a fault that chose what the anchor read is
     * asked; a replay that moves it runs the anchor again, and its own rows
     * say whether the predicate turned symbolic or the fatal was observed.
     * </p>
     *
     * @return null when the anchor is not concrete
     */
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
            // What the deciding predicate itself read, by read event: a
            // compound guard's phi stands at its first test, and its later
            // tests read after that (hdfs-adhoc-26: the cTime reads of
            // `LV >= cur && cTime <= ns.cTime`, events past the target row).
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

    /**
     * The store versions the anchor read at its provenance sites before it
     * decided, in each admitted path (SYMBOL-SCOPE §5.7), whether or not
     * the anchor is concrete: a version's content is no value any term
     * names, so a symbolic predicate's demand never reaches it, and what
     * the guard read of a decoded object rests on that version all the
     * same (solr-bugs-reindex-cleanup: the alias check reads the aliases a
     * fetch parsed, beside the values it decides symbolically on).
     */
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

    /**
     * THE INVOCATIONS A FLIPPED WORLD ADDED (PIPELINE §7.8): each {@link
     * GapKind#UNPLANNED_INPUT} a session states -- a planned marker of a
     * demanded door called at an invocation its task plans no input for --
     * with the session that exposes it, the first in corpus order that may
     * parent an obligation ({@link Branches#parents}: admitted, focused, its
     * branch not stopped), as an exposed region is grown.  The seed replay
     * exposes none: the recording planned its own invocations.  GROW plans
     * each as the input {@link UnplannedInput#grown} of its task and re-runs
     * the exposing replay, whose world the new root then flips in.
     */
    static Map<UnplannedInput, String> unplanned(Corpus corpus,
                                                Branches branches) {
        Map<UnplannedInput, String> exposed =
                new LinkedHashMap<UnplannedInput, String>();
        for (SessionReader session : corpus.sessions()) {
            if (session.seed() || session.obligations().isEmpty()
                    || !branches.parents(session.sessionId())) {
                continue;
            }
            for (GapRow gap : session.gaps()) {
                if (gap.kind() != GapKind.UNPLANNED_INPUT) continue;
                exposed.putIfAbsent(UnplannedInput.parse(gap.subject()),
                        session.sessionId());
            }
        }
        return exposed;
    }

    /**
     * A demanded occurrence no session CAPTURED: the hooks ran it -- its
     * runtime identity is in some session's rows (a SEND, the sender an anchor
     * names, a producer of a delivery) -- but no planned task admitted it, so
     * it has no decisions to flip.  It is the retained set that must grow
     * (PIPELINE §7.2, §7.8): an admitted focused
     * session naming it is re-run with a plan row at its address, and the
     * next round has it as a task.  hdfs-17899: a DataNode's periodic
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
     *
     * <p>Only a session that may parent an obligation exposes ({@link
     * Branches#parents}): one named only by admitted sessions whose branch
     * stopped is a DIAGNOSTIC gap, since nothing grown from them could be
     * cut from.</p>
     */
    private static void uncaptured(Corpus corpus, Branches branches,
                                   Demand demand, StaticScopeMap scope,
                                   Map<OccurrenceAddress, String> exposed,
                                   Set<OccurrenceAddress> waiting,
                                   Set<GapRow> gaps) {
        OccurrenceAddress occurrence = demand.occurrence;
        if (occurrence.role()) {
            if (occurrence.lineageLost()) {
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
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
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
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
            waiting.add(occurrence);
            return;
        }
        if (!stopped.isEmpty()) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    occurrence.render(), "only sessions whose branch "
                            + "stopped ran this occurrence (" + stopped
                            + " among them), so it is not grown"));
            return;
        }
        gaps.add(GapRow.of(ExploreCodec.EXPLORATION, GapKind.ADMISSION_GAP,
                GapClass.BLOCKING, occurrence.render(),
                "no session of this corpus ran this occurrence, so no replay "
                        + "can be focused on it and it is not a task"));
    }

    /** Whether a session that captured {@code occurrence} ran it whole, not
     *  for its doors alone ({@code SessionManifest#doorsOnly}). */
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

    /** Whether a demand wants a value of its occurrence -- a member's, a
     *  store item's sender's, a static candidate's -- not only the doors of
     *  a message or a fetch. */
    static boolean valueDemand(String why) {
        return CLOSURE_MEMBER.equals(why)
                || STORE_ITEM_PRODUCER.equals(why)
                || STATIC_CANDIDATE_WRITER.equals(why)
                || STATIC_CANDIDATE_PRODUCER.equals(why);
    }

    /**
     * The admitted focused session whose replay re-runs {@code occurrence}
     * grown (one that may parent an obligation, {@link Branches#parents};
     * one already re-run for another first), and the last one that ran it
     * but whose branch stopped; "" for none.  Never the seed: it is not
     * re-run.
     */
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

    /**
     * What a lost scope ran that no row states: the roots the scope map
     * declares in the methods its index stands on, and the decisions the
     * closure would have flipped there.  Unnamed work's regions open no
     * occurrence (IDENTITY §1), so these are what the closure loses.
     */
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
        private Set<String> contributed = new LinkedHashSet<String>();
        /** Session -> the seq of the last value this occurrence contributed
         *  there: where the prefix its deliveries rest on ends ({@link
         *  #demanded}). */
        private Map<String, Long> cutoffs = new LinkedHashMap<String, Long>();
        /** Whether {@link #contributed} and {@link #cutoffs} are still a
         *  {@link Contribution}'s, copied before this demand changes them. */
        private boolean shared;
        /*
         * Its identity sets start at the smallest table, not the default 64
         * slots: a demand is made for every write a demanded read could
         * observe and folded at once into the one it repeats (Demand.<init>
         * and the garbage it leaves were 2 % of SGF8PLAN-adhoc-05 round 2's
         * walk, its two default identity tables 0.7 KB of it).
         */
        /** The contributions every value of which this demand holds. */
        private final Set<Contribution> holds =
                Collections.newSetFromMap(
                        new java.util.IdentityHashMap<Contribution, Boolean>(
                                1));
        /** The contribution this demand's values are exactly, or null. */
        private Contribution exactly;
        private Set<String> flipSites = new LinkedHashSet<String>();
        /** Whether {@link #flipSites} is a step's still ({@link
         *  #launched}), copied before this demand changes it. */
        private boolean flipsShared;
        /** The symbols of a concrete anchor's predicate reads ({@link
         *  #concrete}); none on any other demand. */
        private final Set<String> predicate = new LinkedHashSet<String>();
        private final boolean anchor;
        private String why;
        /** Whether a reason it was demanded for wants its value ({@link
         *  #valueDemand}), not only its doors: kept apart from {@link #why},
         *  which says whether the rows connect it. */
        private boolean value;
        /** Whether it wrote a store version a demand read ({@link
         *  #wrote}): the senders of what it applied produce that value. */
        private boolean storeWriter;
        private boolean dirty;
        /** How often its state changed: a step computed ahead of one
         *  version is that version's walk only ({@link Walk#take}). */
        private int version;
        /*
         * WHAT ITS WALKS EXPANDED ALREADY ({@link #step}).  A demand is
         * walked again each time it grows, and what it demands only grows,
         * so each walk expands only what no walk before it did: a demanded
         * read's writers, a paired handoff's producers, a contributed
         * value's stated reads -- the same successors again would be absorbed
         * growing nothing.  Walked whole every time, a hub every session
         * contributes to repeated all of it per session (SGF8PLAN-adhoc-05,
         * round 2: 40 min in this walk, single-threaded, hashing the keys of
         * the static candidates it offered again).
         */
        /** session|symbol of each handoff whose producers it expanded. */
        private final Set<String> paired = new HashSet<String>();
        /** The demanded reads whose writers it expanded. */
        private final Set<ReadRow> expandedReads = Collections.newSetFromMap(
                new java.util.IdentityHashMap<ReadRow, Boolean>(1));
        /** How many of its contributed values' stated reads it expanded, in
         *  {@link #contributed}'s order (which only appends). */
        private int expandedContributed;
        /** What its values name, as its last walk closed it ({@link
         *  #demanded}); null before its first walk. */
        private Named named;
        /** The write a writer's demand was made of ({@link #writer}), or
         *  null: all it holds, and all it ever will, it holds of it. */
        private WriteRow madeOf;
        /** The writes whose writer's demand it absorbed ({@link #absorb});
         *  null until one.  Steps on the cores ask it ({@link
         *  Says#writer}) while the walk adds to it. */
        private volatile Set<WriteRow> absorbed;

        private Demand(OccurrenceAddress occurrence, String why,
                       boolean anchor) {
            this.occurrence = occurrence;
            this.why = why;
            this.value = valueDemand(why);
            this.anchor = anchor;
        }

        /** A demand whose values are exactly {@code values}'s. */
        private Demand(OccurrenceAddress occurrence, String why,
                       Contribution values) {
            this(occurrence, why, false);
            contributed = values.contributed;
            cutoffs = values.cutoffs;
            shared = true;
            holds.add(values);
            exactly = values;
        }

        /** Whether it holds what {@code write}'s writer's demand holds: it
         *  was made of it, or absorbed it ({@link #absorb}). */
        private boolean absorbs(WriteRow write) {
            return write == madeOf
                    || absorbed != null && absorbed.contains(write);
        }

        /** A step of it runs on the cores, over its values and flip sites
         *  as they stand ({@link Step}): what changes them next copies them
         *  first. */
        private void launched() {
            shared = true;
            flipsShared = true;
        }

        /** Its own values, before it changes them. */
        private void own() {
            if (!shared) return;
            contributed = new LinkedHashSet<String>(contributed);
            cutoffs = new LinkedHashMap<String, Long>(cutoffs);
            shared = false;
        }

        /**
         * Folds another reason to demand this occurrence: {@code
         * CLOSURE_MEMBER} wins over every other reason, any reason the rows
         * connect over a static one -- a static candidate later reached as
         * a control producer is one, never cut with the static candidates
         * at the ceiling -- and a connected value reason over a door's (a
         * control producer later reached as a store item's sender is that
         * sender, as PLAN states it); and a reason that wants its value
         * makes it a value demand whatever its reason (a control producer
         * also demanded as a static writer wants its own producer, and is
         * run whole once GROW drops a doors-only mark).
         *
         * @return whether this demand grew
         */
        private boolean absorb(Demand other) {
            // A writer's demand it absorbed already -- the same write
            // offered again by another read that could observe it, or by
            // another demand's group -- changes nothing: its values, guards
            // and reason were folded then and only grow (SGF8PLAN-adhoc-05
            // round 2: absorb was 15 % of the walk, mostly writers' demands
            // folded again).
            WriteRow write = other.madeOf;
            if (write != null) {
                if (write == madeOf || absorbed != null
                        && absorbed.contains(write)) {
                    return false;
                }
                if (absorbed == null) {
                    // A row's equality is its identity.
                    absorbed = ConcurrentHashMap.newKeySet(1);
                }
                absorbed.add(write);
            }
            boolean grew = false;
            // Values it holds already add nothing: one producer's every
            // delivery, paired again by each session's attach of it (Z3D
            // snapshot-no-active round 2: 239 sessions).
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

        /** One value this occurrence contributed: its expression, in its
         *  session, at its seq. */
        private void contributes(String sessionId, String expressionRef,
                                 long seq) {
            own();
            if (contributed.add(sessionId + "|" + expressionRef)) {
                exactly = null;
            }
            contributes(sessionId, seq);
        }

        /** @return whether the prefix in this session now runs further */
        private boolean contributes(String sessionId, long seq) {
            Long held = cutoffs.get(sessionId);
            if (held != null && held.longValue() >= seq) return false;
            own();
            cutoffs.put(sessionId, seq);
            exactly = null;
            return true;
        }

        /** The expressions of {@code contributed} (session|ref), by
         *  session, each session's in contributed order: in one pass, not
         *  one per session (a hub every session contributes to). */
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

        /** The expressions one session's {@link #delivered} lists. */
        private static List<String> delivered(
                Map<String, List<String>> bySession, String sessionId) {
            List<String> refs = bySession.get(sessionId);
            return refs == null ? new ArrayList<String>() : refs;
        }
    }

    /**
     * WHAT ONE DEMAND'S VALUES NAME ({@link #demanded}), kept from walk to
     * walk.  The fixed point over the group's reads adds, for each symbol,
     * what that symbol alone brings (the reference reads its container rests
     * on, the symbols of the writes its reads could observe), so the closure
     * of more seeds is the closure of the old ones joined with the new
     * ones': a walk closes only the seeds no walk named before, and the
     * rows it then expands are only those naming a symbol it added ({@link
     * #step}).  The seeds grow with the demand -- its flip sites'
     * decisions, its contributed values -- except what COMPOSE keeps of its
     * deliveries, asked again per walk ({@link RestsOn#ofDelivery}): where
     * that no longer holds all it held, the demand is named anew, whole, as
     * every walk was before (SGF8PLAN-adhoc-05 round 2: the fixed point
     * redone whole per walk was a third of the 30-40 min walk, the scan of
     * every row of the group another tenth).
     */
    private static final class Named {
        /** What the demand's last walk named, which this walk adds to
         *  ({@link #taken}), or null: this walk names them all. */
        private final Named before;
        /** The symbols (this walk's, beside {@link #before}'s). */
        private final Set<String> symbols = new HashSet<String>();
        /** Those this walk added, in the order added. */
        List<String> fresh = new ArrayList<String>();
        /** Whether this walk named them all: the demand's first walk, or
         *  one whose kept symbols shrank. */
        boolean whole = true;
        /** The decisions at its flip sites whose symbols it holds (this
         *  walk's, beside {@link #before}'s). */
        private final Set<DecisionRow> decisions = Collections.newSetFromMap(
                new java.util.IdentityHashMap<DecisionRow, Boolean>());
        /** How many of the demand's contributed values' symbols it holds,
         *  in {@link Demand#contributed}'s order (which only appends). */
        int contributed;
        /** What COMPOSE kept of the demand's paths and deliveries. */
        Set<String> kept = Collections.<String>emptySet();

        Named() {
            before = null;
        }

        /** Named again, by a walk of its own ({@link Step}), over what the
         *  last walk named: what this one adds is fresh. */
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

        /** Whether this decision is named here the first time. */
        boolean decide(DecisionRow decision) {
            return !(before != null && before.decisions.contains(decision))
                    && decisions.add(decision);
        }

        /** What the demand holds once this walk is taken: the last walk's
         *  naming with this one's added. */
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

    /** What every delivery of one producer endpoint contributes, in every
     *  session ({@link #producers}): built once per walk, shared by each
     *  demand paired with it until that demand changes its values. */
    private static final class Contribution {
        private final Set<String> contributed;
        private final Map<String, Long> cutoffs;

        private Contribution(Demand built) {
            this.contributed = Collections.unmodifiableSet(built.contributed);
            this.cutoffs = Collections.unmodifiableMap(built.cutoffs);
        }
    }

    /**
     * WHAT A WALK OF ONE DEMAND SAYS ({@link #step}) -- a successor, a gap,
     * a gap or a fault-less door said once per key, the occurrences offered
     * once per key, a store version's earlier versions, a write's writer --
     * in the order the walk says it, applied when the walk is taken ({@link
     * Step#apply}), so every rule the walk decides by its order is decided
     * there.  What the walk has said already is not said again: what it
     * holds only grows, so what a step read as said is said when the step
     * is taken; else the steps held would hold it all again (SGF8-adhoc-05
     * round 5: 12 million offers and 11 million gaps in 192 steps ran a
     * 21 GB heap out).
     */
    private static class Says {
        final Walk walk;
        final Demand demand;
        final List<Said> said = new ArrayList<Said>();
        /** The keys of the gaps said here ({@link #gap}). */
        private Set<String> gaps;
        /** The occurrences of the successors said here, null for none: the
         *  demands taking it may grow ({@link Walk#launch}). */
        Set<String> successors;

        Says(Walk walk, Demand demand) {
            this.walk = walk;
            this.demand = demand;
        }

        private void succeeds(String occurrenceId) {
            if (successors == null) successors = new HashSet<String>();
            successors.add(occurrenceId);
        }

        /** What one part said, said here in its place ({@link #step}). */
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

        /** A gap made as it is taken, one per {@code key}: what it states
         *  ({@link Walk#gapKeys}). */
        void gap(String key, Supplier<GapRow> row) {
            if (walk.gapKeys.contains(key)) return;
            if (gaps == null) gaps = new HashSet<String>();
            if (!gaps.add(key)) return;
            said.add((at, next) -> {
                if (at.gapKeys.add(key)) at.gaps.add(row.get());
            });
        }

        /** A gap said once per {@code key} ({@link Walk#cut}). */
        void once(String key, Supplier<GapRow> row) {
            if (walk.cut.contains(key)) return;
            said.add((at, next) -> {
                if (at.cut.add(key)) at.gaps.add(row.get());
            });
        }

        /** A door that decided no fault, said once ({@link
         *  #controlProducer}). */
        void faultless(String doorId, Supplier<GapRow> row) {
            if (walk.faultless.contains(doorId)) return;
            said.add((at, next) -> {
                if (at.faultless.add(doorId)) at.gaps.add(row.get());
            });
        }

        /** {@link #candidates}: the holders not offered under {@code key}
         *  and not holding others' objects only, offered. */
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
            // Whether each holds others' objects only, asked on the cores:
            // a session's first asks fill its owner sets, which made one
            // part of SGF8-adhoc-05 round 5's walk 9-15 s.
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

        /** {@link #earlierVersions} of a store version written, where
         *  some are not demanded yet ({@link Walk#storeExpanded}). */
        void earlier(WriteRow write) {
            Long first = walk.storeExpanded.get(write.sessionId() + "|"
                    + SmtLowering.locationKey(write.location()));
            if (first != null && first >= write.version()) return;
            said.add((at, next) -> earlierVersions(at, write, next));
        }

        /** The demand of one write's writer ({@link ClosurePlanner#writer}),
         *  made as it is taken -- unless the writer's demand holds the
         *  write already ({@link Demand#absorbs}). */
        void writer(WriteRow write) {
            Demand held = walk.admitted.get(
                    write.endpoint().occurrence().id());
            if (held != null && held.absorbs(write)) return;
            succeeds(write.endpoint().occurrence().id());
            said.add((at, next) -> next.add(ClosurePlanner.writer(at,
                    write)));
        }
    }

    /**
     * ONE WALK OF ONE DEMAND -- what it says ({@link Says}) and what it
     * leaves the demand -- computed against the demand's state as it
     * stands; what it says about one expansion, apart, is a {@link Says} of
     * its own, said in its place ({@link #step}).
     */
    private static final class Step extends Says {
        /** The demand's {@link Demand#version} this walk is of. */
        private final int version;
        /** Its group's reads, indexed before it ran ({@link Walk#reads}). */
        private final GroupReads group;
        private final Set<String> paired = new HashSet<String>();
        private final Set<ReadRow> expanded = Collections.newSetFromMap(
                new java.util.IdentityHashMap<ReadRow, Boolean>());
        private int contributed;
        private Named named;
        /** What its walk claimed of the leaves its order alone makes
         *  ({@code Corpus#readLeaves}): taken when it is ({@link
         *  Walk#take}). */
        private final Corpus.Claims claims = new Corpus.Claims();
        /** what -> the endpoint ids of the unread said here: once a step,
         *  with no key built per row ({@link Walk#unread}). */
        private final Map<String, Set<String>> unread =
                new HashMap<String, Set<String>>(4);

        /*
         * The demand as it stood when the step was made, on the planner's
         * thread: the walk changes a demand while steps of others run, and
         * what it changes of a running step's demand it copies first
         * ({@link Demand#launched}).  What only the demand's own take
         * changes -- its naming, the handoffs it paired, the reads it
         * expanded -- the step reads in place: the walk takes a demand only
         * once its running step ended ({@link Walk#take}).
         */
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

        /** What it holds until taken: each thing it said, each claim and
         *  each answer over one ({@link Walk#launch}). */
        long weight() {
            return said.size() + claims.size();
        }

        /** Whether this handoff (session|symbol) is paired the first time. */
        boolean pair(String key) {
            return !demand.paired.contains(key) && paired.add(key);
        }

        /** Whether this demanded read is expanded the first time. */
        boolean expand(ReadRow read) {
            return !demand.expandedReads.contains(read)
                    && expanded.add(read);
        }

        /** {@link #unread} of an undemanded row, into {@code into}. */
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

        /** Takes this walk: its demand holds what it expanded and named,
         *  and what it said is applied in order; its successors, in
         *  theirs. */
        List<Demand> apply(Walk walk) {
            demand.paired.addAll(paired);
            demand.expandedReads.addAll(expanded);
            demand.expandedContributed = contributed;
            demand.named = named.taken();
            demand.version++;
            List<Demand> next = new ArrayList<Demand>();
            for (Said each : said) each.apply(walk, next);
            return next;
        }
    }

    /** One change a step says ({@link Step}), applied when it is taken. */
    private interface Said {
        void apply(Walk walk, List<Demand> next);
    }

    /**
     * One anchor's walk over the corpus: the gaps it says (the same gap said
     * twice is one gap, as {@link ExploreMain} publishes them), the unread
     * deliveries it said ({@link #unread}), the static candidates it
     * offered ({@link #candidates}), and what the static map answered it:
     * each answer scans every site of the map, and the walk asks again for
     * every demanded read of a site.
     */
    static final class Walk {
        private final Corpus corpus;
        private final StaticScopeMap map;
        /** What a delivery rests on, as COMPOSE keeps it ({@link
         *  #demanded}). */
        private final RestsOn restsOn;
        private final Set<GapRow> gaps = new LinkedHashSet<GapRow>();
        /** The keys of the gaps that state no holder of a static site
         *  ({@link Says#gap}): the walk says each once. */
        private final Set<String> gapKeys = ConcurrentHashMap.newKeySet();
        /** occurrence id -> its demand: the walk's ({@link #plan}), in the
         *  order admitted. */
        private final Map<String, Demand> demands =
                new LinkedHashMap<String, Demand>();
        /** The same, for the steps on the cores ({@link Says#writer}). */
        private final Map<String, Demand> admitted =
                new ConcurrentHashMap<String, Demand>();
        /** what -> the endpoint ids of the deliveries said unread: asked of
         *  every undemanded row a whole walk meets, no key is built for it
         *  (SGF8PLAN-adhoc-05 round 2: the concatenated what|id was 6 % of
         *  the walk). */
        private final Map<String, Set<String>> unread =
                new ConcurrentHashMap<String, Set<String>>();
        /** (site, node) -> the activated occurrences that hold the site. */
        private final Map<List<Object>, List<OccurrenceAddress>> holders =
                new ConcurrentHashMap<List<Object>, List<OccurrenceAddress>>();
        /** (reason, site, guards, node) -> the occurrences offered under it. */
        private final Map<List<Object>, Set<String>> offered =
                new ConcurrentHashMap<List<Object>, Set<String>>();
        /** session|occurrence id -> the owners of every location it read or
         *  wrote in that session. */
        private final Map<String, Set<String>> held =
                new ConcurrentHashMap<String, Set<String>>();
        private final Map<String, Set<String>> guards =
                new ConcurrentHashMap<String, Set<String>>();
        private final Map<String, List<StaticScopeMap.Site>> writers =
                new ConcurrentHashMap<String, List<StaticScopeMap.Site>>();
        /** occurrence id -> whether a session recorded a fault decision of
         *  it ({@link #faulted}). */
        private final Map<String, Boolean> faults =
                new ConcurrentHashMap<String, Boolean>();
        /** Doors said to decide no fault, once each ({@link
         *  #controlProducer}). */
        private final Set<String> faultless = ConcurrentHashMap.newKeySet();
        /** The narrowings' cuts already named (occurrence, message, kind). */
        private final Set<String> cut = ConcurrentHashMap.newKeySet();
        /** session|store location -> the highest version whose earlier
         *  versions' writers are demanded ({@link #earlierVersions}). */
        private final Map<String, Long> storeExpanded =
                new ConcurrentHashMap<String, Long>();
        /** occurrence id -> its group (it and its state-connected factor)
         *  and the group's reads: a demand is walked again each time it
         *  grows (hdfs-adhoc-07 EX1: 93 walks of 31 demands). */
        private final Map<String, List<OccurrenceAddress>> groups =
                new HashMap<String, List<OccurrenceAddress>>();
        private final Map<String, GroupReads> groupReads =
                new HashMap<String, GroupReads>();
        /** occurrence id -> its own reads, indexed once per walk: every
         *  group it is a member of reads them there ({@link GroupReads}). */
        private final Map<String, MemberReads> memberReads =
                new HashMap<String, MemberReads>();
        /** symbol, session|location key, session|object -> the members
         *  whose rows hold it ({@link MemberReads#at}, {@link
         *  MemberReads#symbolsAt}, {@link MemberReads#returning}), in the
         *  order indexed: a group asks only them, not each of its members
         *  ({@link GroupReads}). */
        private final Map<String, MemberReads[]> naming =
                new ConcurrentHashMap<String, MemberReads[]>();
        private final Map<String, MemberReads[]> locating =
                new ConcurrentHashMap<String, MemberReads[]>();
        private final Map<String, MemberReads[]> returning =
                new ConcurrentHashMap<String, MemberReads[]>();
        /** producer endpoint id -> {@link #contribution}. */
        private final Map<String, Contribution> contributions =
                new ConcurrentHashMap<String, Contribution>();
        /** The cores the steps run on ({@link #ahead}). */
        private final ForkJoinPool cores;
        /** The thread the walk is taken on: the only one that writes it. */
        private final Thread planner;
        /** The ids of the demands to walk, in the order they are taken. */
        final Deque<String> pending = new ArrayDeque<String>();
        /** demand -> its step computed ahead, {@link #RUNNING} while it
         *  runs, or what it threw, until taken ({@link #take}). */
        private final Map<Demand, Object> steps =
                new java.util.IdentityHashMap<Demand, Object>();
        /** A step on the cores, not yet {@link #received}. */
        private static final Object RUNNING = new Object();
        /** The steps that ran, each with its demand, as they end. */
        private final java.util.concurrent.BlockingQueue<Object[]> done =
                new java.util.concurrent.LinkedBlockingQueue<Object[]>();
        /** How many steps run. */
        private int running;

        Walk(Corpus corpus, StaticScopeMap map, OccurrenceAddress anchor,
             ForkJoinPool cores) {
            this.planner = Thread.currentThread();
            this.corpus = corpus;
            this.map = map;
            this.restsOn = new RestsOn(corpus, map, anchor);
            this.cores = cores;
        }

        /*
         * WHAT A STEP READS.  A step ({@link Step}) runs on any core while
         * the walk takes others, and reads the corpus, the map and the
         * walk's memos -- each below holds a function of its key, filled by
         * whichever core asks first ({@code putIfAbsent}: a JDK 8
         * ConcurrentHashMap holds a bin while computeIfAbsent computes), so
         * every core reads the value the walk alone would have; what only
         * the order gives, a read's leaves by seq, it claims ({@code
         * Corpus#readLeaves}) -- its demand as it stood when the step was
         * made ({@link Step}: what the walk changes of it, it copies first,
         * {@link Demand#launched}; what only the demand's take changes, in
         * place, as the walk waits for its step), and its group's reads,
         * indexed on the planner's thread ({@link #reads}: each key's
         * members an array the walk replaces whole).  What the walk decides
         * in its order (the gaps, the keys said once, the occurrences
         * offered, the store versions expanded, the demands and the writes
         * they absorbed) a step writes none of: it reads them, concurrent,
         * only to leave out what was said already ({@link Says}).
         */

        /** Whether a session recorded a fault decision of {@code
         *  occurrence} ({@link Corpus#faultSites}), asked once. */
        private boolean faulted(OccurrenceAddress occurrence) {
            Boolean held = faults.get(occurrence.id());
            if (held == null) {
                held = !corpus.faultSites(occurrence).isEmpty();
                faults.putIfAbsent(occurrence.id(), held);
            }
            return held;
        }

        /** What every session's exports at one producer endpoint
         *  contribute, in their order: once per walk, one instance (a
         *  demand holds it by identity, {@link Demand#holds}). */
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

        /** Plans one demand: it is walked as its turn comes. */
        void admit(Demand demand) {
            demands.put(demand.occurrence.id(), demand);
            admitted.put(demand.occurrence.id(), demand);
            pending.add(demand.occurrence.id());
        }

        /** Takes a planned demand out of the plan, and its step. */
        void drop(Demand demand) {
            demands.remove(demand.occurrence.id());
            admitted.remove(demand.occurrence.id());
            pending.remove(demand.occurrence.id());
            steps.remove(demand);
        }

        /**
         * STEPS AHEAD: while the walk takes its demands in queue order, the
         * steps of the ones behind the head run on the cores ({@link
         * #launch}) -- each against its demand's state as it starts, the
         * walk going on as they run -- and the walk waits only for the step
         * it takes, starting others as steps end; one that runs none, it
         * walks itself, beside them ({@link #take}: SGF8-adhoc-05 round 5's
         * walk 303 s so, 337 s with such a head started on the cores and
         * waited for).  On one core none runs ahead: a step there runs
         * alone, as the walk takes it.
         */
        void ahead() {
            received(false);
            launch(true);
        }

        /** The steps of {@code upcoming}'s demands, run ahead as the
         *  queue's are ({@link #launch}): the static candidates planned one
         *  at a time, each walked as its turn comes. */
        void prepare(List<Demand> upcoming) {
            received(false);
            launch(upcoming, false);
        }

        /** {@link #launch} over the queue's first demands, {@link #WINDOW}
         *  a core, each its first time there. */
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

        /** The demands a window holds a core ({@link #launch}): as many
         *  again as run at once, to keep the cores busy as steps end. */
        static final int WINDOW = 2;
        /** The heap one unit of a held step's weight may hold ({@link
         *  Step#weight}): at most a successor said with its sets, about
         *  2 KB; most are a lambda over rows the corpus holds anyway. */
        static final long WEIGHT_BYTES = 2048L;
        /** The share of the heap the old generation left free after its
         *  last collection that the steps held may take. */
        static final double HELD_SHARE = 0.25;

        /** How much the steps held at once may weigh ({@link #launch}):
         *  {@link #HELD_SHARE} of the heap the old generation left free
         *  after its last collection ({@code HeapWatch}), so a walk whose
         *  heap fills holds fewer -- down to none, the walk one step at a
         *  time. */
        private static long budget() {
            long heap = Runtime.getRuntime().maxMemory();
            double free = 1.0 - HeapWatch.oldGenerationSwept();
            return (long) (heap * free * HELD_SHARE / WEIGHT_BYTES);
        }

        /**
         * Starts the steps of {@code order}'s demands -- queue order, the
         * first the one the walk takes next where {@code headTaken} -- that
         * hold no step of their state and run none, in order, while fewer
         * than the cores run and the steps held weigh less than the {@link
         * #budget} -- held until taken, a step holds everything
         * it said ({@link Step#weight}): SGF8-adhoc-05 round 5's 96 at once
         * took its 21 GB heap to 22 GB resident -- and none that a step
         * before it, ended, names a successor of ({@link Says#successors}):
         * taking that one grows it, so its step now would be another
         * state's (SGF8-adhoc-19 round 10: 699 of 1,611 were).  Their
         * groups are indexed here, on the planner's thread ({@link
         * #reads}).
         */
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
                    // What a step of its state threw: walked in the order.
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
                // Counted once it runs: a pool that cannot run it throws.
                cores.execute(() -> done.add(new Object[] {demand,
                        stepAhead(step)}));
                steps.put(demand, RUNNING);
                running++;
            }
        }

        /** {@code demand}'s step held -- or what it threw -- where it is of
         *  its state now ({@link Demand#version}); else none, and none is
         *  held. */
        private Object current(Demand demand) {
            Object held = steps.get(demand);
            int version = held instanceof Step ? ((Step) held).version
                    : held instanceof Thrown ? ((Thrown) held).version : -1;
            if (version < 0) return null;
            if (version == demand.version) return held;
            steps.remove(demand);
            return null;
        }

        /** What a step computed ahead threw, and the demand's version it
         *  was of. */
        private static final class Thrown {
            final int version;
            final Throwable thrown;

            Thrown(int version, Throwable thrown) {
                this.version = version;
                this.thrown = thrown;
            }
        }

        /** {@code step}, computed on a core, or what it threw ({@link
         *  #take}). */
        private Object stepAhead(Step step) {
            try {
                return step(this, step);
            } catch (RuntimeException | Error thrown) {
                return new Thrown(step.version, thrown);
            }
        }

        /** Holds the steps that ended -- waiting for one where {@code
         *  wait} -- each where its demand is still planned. */
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

        /** Waits for every step that runs: none reads the walk after it. */
        void drain() {
            while (running > 0) received(true);
            steps.clear();
        }

        /** The fewest items a part of a fold holds: a fold of fewer than
         *  two parts' items is computed here. */
        private static final int PART = 16;
        /** At most this many parts of one fold. */
        private static final int PARTS = 192;

        /**
         * {@code each} of {@code items}, in their order: a long list in
         * parts on the walk's cores, a short one here.  {@code each} is a
         * function of its item and the walk's memos, which hold functions
         * of their keys, so the list is the one computed here alone.
         */
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

        /**
         * Takes one demand's walk ({@link #step}): its step that runs is
         * waited for -- the steps behind it started as others end ({@link
         * #launch}) -- and taken where it is the walk of the demand's state
         * now ({@link Demand#version}) and what it claimed is still no other
         * row's ({@code RestsOn#take}), else one computed here; here too
         * where one computed ahead threw: what the walk throws is what the
         * walk in its order throws, never what a step threw at another
         * moment.  An Error a step of the demand's state now threw ends the
         * walk (a group indexed off the planner's thread, {@link #reads});
         * one of an earlier state's is walked again.  Waiting for the
         * demand's own step is what lets a step read in place what only its
         * demand's take changes ({@link Step}).  Its memos and its events
         * are applied in the order the step said them, and its successors
         * returned in theirs.
         */
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
                // Its walk now, here, in the order: what it claims no one
                // has taken.
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

        /**
         * What COMPOSE keeps of each of a step's paths and deliveries, in
         * their order ({@link RestsOn#ofDelivery}): a long list in parts on
         * the walk's cores, each under claims of its own ({@code
         * Corpus#readLeaves}) taken after the parts before it ({@code
         * Claims#follow}) -- a part that claimed a seq one before it
         * claimed by another row computed again here, under theirs.
         */
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

        /** Runs these on the walk's cores until each is done, whatever
         *  one threw: its caller joins them in their order. */
        private <T> void run(List<ForkJoinTask<T>> tasks) {
            if (ForkJoinTask.getPool() == cores) {
                all(tasks);
            } else {
                cores.invoke(ForkJoinTask.adapt(() -> all(tasks)));
            }
        }

        /** Every one of these done: JDK 8's invokeAll returns at the first
         *  that throws, the others still reading the walk while its taker
         *  writes it. */
        private static <T> void all(List<ForkJoinTask<T>> tasks) {
            for (int at = tasks.size() - 1; at > 0; at--) tasks.get(at).fork();
            tasks.get(0).quietlyInvoke();
            for (int at = 1; at < tasks.size(); at++) {
                tasks.get(at).quietlyJoin();
            }
        }

        /** The occurrence and its state-connected factor: one symbolic
         *  unit ({@link #step}). */
        private List<OccurrenceAddress> group(OccurrenceAddress occurrence) {
            return groups.computeIfAbsent(occurrence.id(), id -> {
                List<OccurrenceAddress> group =
                        new ArrayList<OccurrenceAddress>();
                group.add(occurrence);
                group.addAll(stateConnected(corpus, occurrence));
                return Collections.unmodifiableList(group);
            });
        }

        /** {@link GroupReads} of an occurrence's {@link #group}: its
         *  members' {@link MemberReads}, each indexed once per walk -- on
         *  the planner's thread, before a step reads it ({@link #ahead},
         *  {@link #take}): a JDK 8 HashMap resizes at the computeIfAbsent
         *  after the insert that filled it, whatever the key, so cores
         *  asking at once lose the keys held and index groups again into
         *  lists others iterate. */
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

        /** Each key's members, a new array each time one is added: a
         *  step on the cores reads the one it got whole. */
        private static void index(Map<String, MemberReads[]> into,
                                  Set<String> keys, MemberReads member) {
            MemberReads[] one = {member};
            for (String key : keys) {
                into.merge(key, one, (held, added) -> {
                    MemberReads[] grown = Arrays.copyOf(held, held.length + 1);
                    grown[held.length] = member;
                    return grown;
                });
            }
        }

        /** A writer's flip sites: guards of every static write site in the
         *  METHOD it wrote from (bci vs unit index do not compare); may be
         *  one too many. */
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

        /** {@link StaticScopeMap#writersOf}. */
        private List<StaticScopeMap.Site> writersOf(String carrier) {
            List<StaticScopeMap.Site> held = writers.get(carrier);
            if (held != null) return held;
            held = map.writersOf(carrier);
            List<StaticScopeMap.Site> first = writers.putIfAbsent(carrier,
                    held);
            return first != null ? first : held;
        }

        /** Every activated occurrence holding one static site, on {@code
         *  node} (null = any): one scan of the corpus per site and node. */
        private List<OccurrenceAddress> holders(StaticScopeMap.Site site,
                                                NodeId node) {
            List<Object> key = Arrays.<Object>asList(site, node);
            List<OccurrenceAddress> found = holders.get(key);
            if (found != null) return found;
            found = new ArrayList<OccurrenceAddress>();
            for (OccurrenceAddress occurrence : corpus.occurrences()) {
                if (holds(map, occurrence.regionId(), site)
                        && (node == null || node.equals(occurrence.node()))
                        && activated(corpus, occurrence)) {
                    found.add(occurrence);
                }
            }
            List<OccurrenceAddress> first = holders.putIfAbsent(key, found);
            return first != null ? first : found;
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
    private static Step step(Walk walk, Step step) {
        Demand demand = step.demand;
        GroupReads group = step.group;
        Corpus corpus = walk.corpus;
        Map<String, Set<String>> kept = new LinkedHashMap<String,
                Set<String>>();
        Named named = demanded(walk, step, kept);
        Named demanded = named;
        // Named whole, every row of the group is asked; named again, only
        // the rows naming a symbol this walk added, in the same order: every
        // other demanded row was expanded by the walk that named its symbol,
        // and every undemanded one was said unread by the last whole walk.
        // What it expands, in order -- the unread said between -- each
        // expansion's events computed on the walk's cores ({@link
        // Walk#each}) and said in place.
        List<Object> expanding = new ArrayList<Object>();
        if (named.whole) {
            for (MemberReads member : group.members) {
                for (AttachRow attach : member.attaches) {
                    if (!demanded.holds(attach.symbol())) {
                        step.unread(expanding, attach.sessionId(),
                                attach.endpoint(), "handoff");
                    } else if (step.pair(attach.sessionId() + "|"
                            + attach.symbol())) {
                        expanding.add(attach);
                    }
                }
                for (ReadRow row : member.rows) {
                    if (!demanded.holds(row.symbol())) {
                        step.unread(expanding, row.sessionId(),
                                row.endpoint(), "state read");
                    } else if (step.expand(row)) {
                        expanding.add(row);
                    }
                }
            }
        } else {
            for (long at : group.placesOf(named.fresh)) {
                MemberReads member = group.members.get((int) (at >>> 32));
                int item = (int) at;
                if (item < member.attaches.size()) {
                    AttachRow attach = member.attaches.get(item);
                    if (step.pair(attach.sessionId() + "|"
                            + attach.symbol())) {
                        expanding.add(attach);
                    }
                } else {
                    ReadRow row = member.rows.get(item
                            - member.attaches.size());
                    if (step.expand(row)) expanding.add(row);
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
        // A handoff what COMPOSE keeps names, whoever received it: the
        // producer of the value a reached occurrence decided on, however many
        // joins from the group (two hops: the anchor reads a location W1
        // wrote, W1 read one W2 wrote, and W2 decided on v_H).
        for (Map.Entry<String, Set<String>> session : kept.entrySet()) {
            for (String symbol : session.getValue()) {
                AttachRow attach = corpus.attach(session.getKey(), symbol);
                // A forced world's arrival came from no run's world.
                if (attach != null && attach.seq()
                        < corpus.forcedFrom(session.getKey())
                        && step.pair(session.getKey() + "|" + symbol)) {
                    producers(walk, attach, step);
                }
            }
        }
        statedReads(walk, step);
        // A control producer contributes no value: whether its own message
        // exists is no question of the anchor's (solr-18413 round Z7: the
        // doors of every request and queue item behind the store writers'
        // items, six hops deep, doubled the plan).  Nor does a store fetch.
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

    /** What COMPOSE keeps of one session's path or delivery, joined. */
    private static void keep(Map<String, Set<String>> kept, String session,
                             Set<String> symbols) {
        kept.computeIfAbsent(session, key -> new LinkedHashSet<String>())
                .addAll(symbols);
    }

    /** A door of the message a demanded occurrence served -- its sender or
     *  its receiver ({@link Corpus#doorsOf}), paired via the message that
     *  started the served occurrence ({@link Corpus#startedBy}: its ANCHOR,
     *  or each item its turn took in) -- joins as a control producer where a
     *  session recorded a fault decision of it: it contributes no value,
     *  but that fault point decides whether the message exists (IDENTITY
     *  §7.3), the door PLAN's CONTROL_PRODUCER rule admits (it read a
     *  fault marker).  Any other door -- run under no planned task
     *  (hdfs-adhoc-28's heartbeat tick, in a scope with no IPC client door:
     *  it reads no marker), a role, or a captured one that decided no
     *  fault -- has nothing that decides the message: one DIAGNOSTIC row,
     *  never a member, never waited for.  Only a value's occurrence asks:
     *  a control producer's own message is not followed.  The sender of the
     *  message that started a store writer ({@link Demand#storeWriter})
     *  joins as a value ({@link #STORE_ITEM_PRODUCER}): the writer applied
     *  its item, so the version rests on the item's content, a key it
     *  removed as much as a value it set, and the doors of the sender's own
     *  message are asked in turn -- once: the sender's cells are not
     *  demanded. */
    private static void controlProducer(Walk walk, Step step) {
        Corpus corpus = walk.corpus;
        for (String endpoint : corpus.startedBy(step.demand.occurrence)) {
            doorsOf(walk, step, endpoint);
        }
    }

    /** {@link #controlProducer} over the doors of one message that started
     *  the demanded occurrence. */
    private static void doorsOf(Walk walk, Step step, String endpoint) {
        Corpus corpus = walk.corpus;
        Demand demand = step.demand;
        Map<String, Integer> cut = new LinkedHashMap<String, Integer>();
        List<OccurrenceAddress> doors = corpus.doorsOf(endpoint,
                demand.occurrence, cut);
        // Each narrowing names what it cut (counted, DIAGNOSTIC).
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
            // What a store writer applied came from the message's sender: a
            // value, whose own message's doors are asked in turn
            // (solr-bugs-overseer-lock-leak: the Runner's item removes
            // readOnly from state.json v8; the queue tick's markTaskAsRunning
            // door decides whether the Runner runs).
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

    /**
     * E2 -- A DEMANDED EXPORT STATES THE SHARED STATE IT RESTS ON.
     *
     * <p>The VM publishes a contributed value's shared-state reads only inside
     * its expression; no ReadRow names them. Each resolved read grows the
     * closure like a read row (writer of that version, static write sites on
     * the producer's node, N1); writers recurse the same way. {@link
     * Corpus#expressionStateReads} is the one resolution, shared with {@code
     * compose.RestsOn#seedWrites}. Never the anchor (it contributes no
     * delivery).</p>
     */
    private static void statedReads(Walk walk, Step step) {
        Demand demand = step.demand;
        if (demand.anchor) return;
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
                        Collections.<String>emptySet(), null,
                        demand.occurrence.id(), demand.occurrence::render,
                        () -> read.locationKey() + " (read at event "
                                + read.readEventId() + ")");
            }
        }
    }

    /** The symbols one occurrence's demanded values name: the anchor's fatal
     *  predicate (a concrete one's predicate reads, {@link #concrete}),
     *  its decisions at its guard-set sites, and its contributed
     *  expressions; what COMPOSE keeps of each of its admitted paths and
     *  deliveries ({@link RestsOn}: the decisions and reads of every
     *  occurrence the joins from its prefix reach that rest on what moves,
     *  so a handoff they name is demanded of the group member that
     *  received it -- hdfs-11741's balancer KeyManager, deciding on the
     *  expiry dates of nn0's updateBlockKeys@1 response); then the fixed
     *  point over its group's reads and the writes they could observe. A
     *  factor member deciding the same site decides it on its own objects,
     *  and demands nothing here. Terms are EXPR references, asked of their
     *  expressions' DAG ({@link Corpus#termSymbols}), never rendered.
     *  Each walk adds only what its demand grew by ({@link Named}). */
    private static Named demanded(Walk walk, Step step,
                                  Map<String, Set<String>> kept) {
        Demand demand = step.demand;
        Corpus corpus = walk.corpus;
        GroupReads reads = step.group;
        // Each fold below takes, per item, what the item names -- a function
        // of the item alone, computed on the walk's cores ({@link
        // Walk#each}) -- and adds it in the items' order.
        List<String> sessions = new ArrayList<String>();
        List<Function<Corpus.Claims, Set<String>>> asks =
                new ArrayList<Function<Corpus.Claims, Set<String>>>();
        if (demand.anchor) {
            // COMPOSE's disjuncts, by its one admission rule.
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
        Set<String> keeps = new HashSet<String>();
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
        // The fixed point, over the symbols this walk added: those an
        // earlier walk added brought theirs then.  A level of fresh symbols
        // at once, each one's part added in its order: the next level is
        // what they added, in the order a fold one symbol at a time adds it.
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

    /** What one term names, in the order {@link #demanded} adds it: its
     *  symbols, then the symbols of the group's reads its expressions read
     *  by structure ({@link GroupReads#under}). */
    private static List<Collection<String>> termNames(Corpus corpus,
                                                      GroupReads reads,
                                                      String sessionId,
                                                      String term) {
        List<Collection<String>> names = new ArrayList<Collection<String>>();
        names.add(corpus.termSymbols(sessionId, term));
        reads.under(corpus, sessionId, term, names);
        return names;
    }

    /** What one fresh symbol brings in {@link #demanded}'s fixed point, in
     *  the order it is added: for each group row stating it, the reference
     *  reads its container rests on ({@link GroupReads#holding}), then the
     *  symbols of each write the row could observe. */
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

    /**
     * One occurrence's read rows, every session's, indexed once per walk
     * ({@link Walk#memberReads}): by symbol, by session and location, and
     * by the object a reference read returned; and its attaches and reads in
     * the order a walk asks them, each at its place ({@link #at}).
     */
    static final class MemberReads {
        /** Its attaches, then its reads, in recorded order. */
        private final List<AttachRow> attaches;
        private final List<ReadRow> rows;
        private final Map<String, List<ReadRow>> bySymbol =
                new HashMap<String, List<ReadRow>>();
        /** symbol -> the places, ascending, of the attaches and reads that
         *  name it: an attach's index, or a read's past every attach. */
        private final Map<String, int[]> at = new HashMap<String, int[]>();
        /** session|location key -> the symbols its reads stated. */
        private final Map<String, Set<String>> symbolsAt =
                new HashMap<String, Set<String>>();
        /** session|object -> the symbols of the reference reads that
         *  returned that object. */
        private final Map<String, Set<String>> returning =
                new HashMap<String, Set<String>>();

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
                symbolsAt.computeIfAbsent(row.sessionId() + "|"
                                + SmtLowering.locationKey(row.location()),
                        key -> new LinkedHashSet<String>())
                        .add(row.symbol());
                long object = VmRows.referencedObjectRid(
                        row.concreteValue());
                if (object > 0L) {
                    returning.computeIfAbsent(row.sessionId() + "|"
                                    + object,
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
        }
    }

    /**
     * One group's read rows ({@link #demanded} asks them once per decision
     * at a flip site and once per demanded symbol): its members' {@link
     * MemberReads}, in group order, each answer the members' own in that
     * order.  A group holds every read its state-connected factor made
     * (SOLR-18413 r2: 109,016 rows, mostly Lucene streams, and a rescan of
     * them per decision was two thirds of the wave planner's time), and the
     * groups of a closure overlap: indexed per group, every member's reads
     * were held once per group it is in (solr-adhoc-39 PV7 round 6: past
     * 14 GB in the closure walk alone).  A question is asked of the members
     * the walk's index names for it ({@link Walk#naming}), not of each
     * member: a factor of hundreds asked for every symbol was a tenth of
     * SGF8PLAN-adhoc-05 round 2's walk.
     */
    static final class GroupReads {
        final List<MemberReads> members;
        /** member -> its place in {@link #members}. */
        private final Map<MemberReads, Integer> place =
                new java.util.IdentityHashMap<MemberReads, Integer>();
        private final Map<String, MemberReads[]> naming;
        private final Map<String, MemberReads[]> locating;
        private final Map<String, MemberReads[]> returning;

        private GroupReads(List<MemberReads> members,
                           Map<String, MemberReads[]> naming,
                           Map<String, MemberReads[]> locating,
                           Map<String, MemberReads[]> returning) {
            this.members = members;
            for (int index = 0; index < members.size(); index++) {
                place.put(members.get(index), index);
            }
            this.naming = naming;
            this.locating = locating;
            this.returning = returning;
        }

        /** Those of {@code indexed} in this group, in group order. */
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

        /**
         * The symbols of the reference reads a container's state read rests
         * on, into {@code named}.  Those of its session
         * that returned the container, the read the VM states as a
         * relation's owner when the reference rides the query's receiver
         * slot (VM.md, the owner of a relation).  Through a capture the
         * owner is not stated (hdfs-bugs slowdisk-zero: chooseVolume's
         * filter asks {@code contains} of the list
         * getSlowDisksToExclude() returned, inside the lambda that captured
         * it), and the store of another list would then be no writer of
         * the state the anchor read.
         */
        private void holding(ReadRow row, List<Collection<String>> into) {
            if (row.location().kind() != LocationKind.MAP) return;
            String key = row.sessionId() + "|" + row.location().owner();
            for (MemberReads member : in(returning.get(key))) {
                into.add(member.returning.get(key));
            }
        }

        /** The rows that stated one symbol, in recorded order. */
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

        /** The places of the attaches and reads naming one of these
         *  symbols, in the order a walk asks them: a member's place in the
         *  group (high), the row's in the member ({@link MemberReads#at},
         *  low). */
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

        /**
         * The read rows a term's expressions read by structure, into {@code
         * named}: a scalar read the lowering joined to its version's value
         * is inlined there, and still what the term rests on (SOLR-18406:
         * the phi reads a commit point's `deleted` flag at its INITIAL,
         * which the join made the constant false).
         */
        private void under(Corpus corpus, String sessionId, String term,
                           List<Collection<String>> into) {
            for (String location : corpus.readLocations(sessionId, term)) {
                String key = sessionId + "|" + location;
                for (MemberReads member : in(locating.get(key))) {
                    into.add(member.symbolsAt.get(key));
                }
            }
        }
    }

    /**
     * A delivery this anchor's paths never read: recorded, not planned.
     * Once per endpoint, not per session or per pass: a demand is walked
     * again every time it grows, and every replay repeats the seed's rows --
     * hdfs-11741 v69's planner ran out of heap rendering these.
     */
    private static void unread(Walk walk, String sessionId,
                               Endpoint endpoint, String what) {
        if (!walk.unread.computeIfAbsent(what,
                unused -> ConcurrentHashMap.newKeySet()).add(endpoint.id())) {
            return;
        }
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
    private static void producers(Walk walk, AttachRow attach, Says step) {
        String portId = attach.endpoint().site();
        List<StaticScopeMap.Site> exports = walk.map.exportsOf(portId);
        Set<String> guards = new LinkedHashSet<String>();
        for (StaticScopeMap.Site site : exports) {
            guards.addAll(site.guards);
        }
        if (attach.producer() == null) {
            // Once per endpoint, as the first session states it.
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
        // N2: null (unpaired) means every node.
        NodeId sender = attach.producer() == null ? null
                : attach.producer().occurrence().node();
        for (StaticScopeMap.Site site : exports) {
            candidates(walk, site, STATIC_CANDIDATE_PRODUCER, guards, step,
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
     * @param readAt the id of what reads (its endpoint, or the occurrence
     *               an expression states it of): a diagnostic about it is
     *               said once per field it reads ({@link #field}), not per
     *               session or object -- every replay repeats the seed's
     *               reads, of objects of its own
     * @param subject what that diagnostic is addressed at
     * @param located how the location reads in it
     */
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
        // Every carrier the static map names for the location, and the
        // read's own.
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
        // N1: the heap this read observed is the reader JVM's.
        for (String carrier : carriers) {
            for (StaticScopeMap.Site site : walk.writersOf(carrier)) {
                candidates(walk, site, STATIC_CANDIDATE_WRITER, site.guards,
                        step, sessionId, "carrier " + carrier, reader.node(),
                        location);
            }
        }
    }

    /**
     * Who made the store version a demanded read observed (IDENTITY §7.2):
     * the eligible row writers, as for any read -- a one-JVM cluster's nodes
     * are one session, whose happens-before spans them, so no node limits
     * them -- each with the earlier versions of the location it rests on
     * ({@link #wrote}).  No static candidate: a store location is a path,
     * which no site of the map stores.
     */
    private static void storeWriters(Walk walk, ReadRow row, Says step) {
        for (WriteRow write : walk.corpus.eligibleWrites(row.sessionId(),
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), row.endpoint().occurrence())) {
            wrote(walk, write, step);
        }
    }

    /**
     * The fetches of a demanded store read's location, on its reader's node,
     * that PLAN stated on the target's data flow (SYMBOL-SCOPE §4.2: the
     * plan's {@code storeFetches}, whose read doors alone mint; {@link
     * StaticScopeMap#storeFetches}): a fault at one's read registers no
     * watch, so the node never fetches the next version and its reader reads
     * an older one.  Each joins contributing no value, flipped at its fault
     * decisions, as every task is, and is not followed ({@link
     * #step}).
     */
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
        // PLAN asked the fetches of what its targets read; one EXPLORE
        // demands beyond them has none asked, named once per location and
        // node: no read door on its flow is flippable.
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

    /**
     * The earlier versions of a store location a demanded version rests on:
     * a store keeps one document per location, and each write modifies the
     * one before it (Solr's state writer, its aliases, every compare-and-set
     * write), the rule {@code RestsOn#closure} applies to every location.
     * The writers are demanded once per session and location, below the
     * first version asked ({@link Walk#storeExpanded}): every later one asked
     * there is among them or above them.
     */
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

    /** One recorded write a demanded value may rest on: its writer, flipped
     *  at the guards of its method's write sites, contributing what it
     *  wrote; a store version also rests on its location's earlier ones
     *  ({@link #earlierVersions}).  An INITIAL has no writer: no run
     *  decided it. */
    private static void wrote(Walk walk, WriteRow write, Says step) {
        if (write.initial()) return;
        step.writer(write);
        if (write.location().kind() == LocationKind.STORE) {
            step.earlier(write);
        }
    }

    /** The demand of one write's writer; a store version's -- the one a
     *  demand read, or an earlier one it rests on -- applied what the
     *  senders of its own message sent ({@link Demand#storeWriter}), as
     *  PLAN's {@code crossStore} has every writer up to the version read. */
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
                                   Says step, String sessionId,
                                   String what, NodeId node,
                                   LocationId location) {
        List<OccurrenceAddress> holders = walk.holders(site, node);
        step.offer(Arrays.<Object>asList(why, site, guards, node),
                holders, why, guards, sessionId, location);
        if (!holders.isEmpty()) return;
        step.gap(why + "|" + sessionId + "|" + site.regionId + "|"
                + site.siteId + "|" + what + "|" + node,
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
     *  the runtime's defect, reported once per consumer endpoint and
     *  producer, as the first session states it (every replay repeats the
     *  seed's pairings). Root/Lost contexts raise nothing. */
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

    /** A location as a diagnostic about its reads names it once: the field
     *  it is of, an object's rid dropped (a rid is one run's,
     *  {@link LocationId}); a static or view owner kept. */
    private static String field(LocationId location) {
        boolean rid = location.kind() != LocationKind.STATIC
                && location.kind() != LocationKind.VIEW
                && Arms.namedOwner(location);
        return location.kind() + " " + (rid ? "" : location.owner()) + "."
                + location.slot();
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
