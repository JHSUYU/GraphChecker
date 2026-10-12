package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.JavaSmtSorts;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WorldRefutation;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
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
import java.util.function.Supplier;

/** One iteration's sessions, indexed: the ONE corpus view both stages read.
 *  Identity is the contract's: an interaction by both endpoints, a location by
 *  {@link LocationId}, a symbol by its minting session (raw symbols, versions
 *  and expression refs are session-local). One path id spelling: {@link
 *  #pathId}. */
public final class Corpus implements Arms.Rows {
    /** One occurrence's decisions in one session: a path, as it ran. */
    public static final class RecordedPath {
        public final String pathId;
        public final String sessionId;
        public final OccurrenceAddress occurrence;
        public final List<DecisionRow> decisions;

        private RecordedPath(String sessionId, OccurrenceAddress occurrence,
                             List<DecisionRow> decisions) {
            this.pathId = pathId(sessionId, occurrence);
            this.sessionId = sessionId;
            this.occurrence = occurrence;
            this.decisions = Collections.unmodifiableList(decisions);
        }
    }

    /** What one raw symbol of one session names. */
    public enum SymbolKind { ROOT, HANDOFF, READ, UNKNOWN }

    /** One decision a focused replay was held to: whose, where, which arm. */
    public static final class Flip {
        /** The occurrence the flip is addressed at (contract id). */
        public final String focusedOccurrenceId;
        public final String siteId;
        public final int ordinal;
        public final boolean outcome;
        /** The obligation that first asked for this flip. */
        public final String obligationId;

        public Flip(String focusedOccurrenceId, String siteId, int ordinal,
                    boolean outcome, String obligationId) {
            this.focusedOccurrenceId = focusedOccurrenceId == null ? ""
                    : focusedOccurrenceId;
            this.siteId = siteId == null ? "" : siteId;
            this.ordinal = ordinal;
            this.outcome = outcome;
            this.obligationId = obligationId == null ? "" : obligationId;
        }

        /** How a refusal names this flip. */
        public String render() {
            return siteId + "#" + ordinal + " -> " + outcome
                    + " at occurrence " + focusedOccurrenceId
                    + " (obligation " + obligationId + ")";
        }
    }

    /** THE WORLD one session ran in, from its focus row: the recording plus its
     *  planted roots, clock skews, answers, pairings and the flips it was
     *  held to (own and inherited). A path cut from it exists only there, so
     *  a child inherits all of it ({@link ObligationFactory#solve} merges,
     *  {@link FlipQuery} asserts). Empty for the seed and for sessions no
     *  worker states a focus row for. */
    public static final class World {
        public final Map<String, String> rootAssignments;
        public final Map<String, String> clockDeltas;
        public final Map<String, String> answers;
        /** Reader -> the writer it was held to, each as a confirmation names
         *  it ({@code ConfirmMain#holding}). */
        public final Map<String, String> pairings;
        /** The row's own flip first, then the flips it inherited. */
        public final List<Flip> flips;

        World(Map<String, String> rootAssignments,
              Map<String, String> clockDeltas,
              Map<String, String> answers,
              Map<String, String> pairings,
              List<Flip> flips) {
            this.rootAssignments =
                    Collections.unmodifiableMap(rootAssignments);
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.answers = Collections.unmodifiableMap(answers);
            this.pairings = Collections.unmodifiableMap(pairings);
            this.flips = Collections.unmodifiableList(flips);
        }

        /** The seed's world, and that of a session with no worker. */
        static World empty() {
            return new World(new LinkedHashMap<String, String>(),
                    new LinkedHashMap<String, String>(),
                    new LinkedHashMap<String, String>(),
                    new LinkedHashMap<String, String>(),
                    new ArrayList<Flip>());
        }
    }

    /** The iteration these sessions were read from, or null. */
    private final Path iteration;
    private final List<SessionReader> sessions;
    private final Map<String, SessionReader> sessionById =
            new LinkedHashMap<String, SessionReader>();
    /** One lowering per session. */
    private final Map<String, SmtLowering> loweringById =
            new LinkedHashMap<String, SmtLowering>();
    /** session id -> what this corpus derives from that session's rows
     *  alone ({@link Derived}). */
    private final Map<String, Derived> bySession =
            new LinkedHashMap<String, Derived>();
    /** occurrence id -> the activations of it, across sessions. */
    private final Map<String, List<ActivationRow>> activations =
            new LinkedHashMap<String, List<ActivationRow>>();
    /** session|occurrence -> that path's decisions, in recorded order. */
    private final Map<String, List<DecisionRow>> decisions =
            new LinkedHashMap<String, List<DecisionRow>>();
    /** producer endpoint id -> every export recorded at it. */
    private final Map<String, List<ExportRow>> exports =
            new LinkedHashMap<String, List<ExportRow>>();
    /** session|symbol -> the minting row. */
    private final Map<String, AttachRow> attachBySymbol =
            new LinkedHashMap<String, AttachRow>();
    /** Every symbol some session's attach minted. */
    private final Set<String> handoffSymbols = new LinkedHashSet<String>();
    private final Map<String, RootMintRow> rootBySymbol =
            new LinkedHashMap<String, RootMintRow>();
    private final Map<String, ReadRow> readBySymbol =
            new LinkedHashMap<String, ReadRow>();
    /** occurrence id -> session id -> its attaches, reads, writes, targets. */
    private final ByOccurrence<AttachRow> attachesOn =
            new ByOccurrence<AttachRow>();
    private final ByOccurrence<ReadRow> readsOn = new ByOccurrence<ReadRow>();
    private final ByOccurrence<WriteRow> writesOn =
            new ByOccurrence<WriteRow>();
    private final ByOccurrence<TargetRow> targetsOn =
            new ByOccurrence<TargetRow>();
    /** occurrence id -> the locations it reads / writes, in any session. */
    private final Map<String, Set<String>> readLocations =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> writtenLocations =
            new LinkedHashMap<String, Set<String>>();
    /** session|location|version -> the write that produced it. */
    private final Map<String, WriteRow> writeByVersion =
            new LinkedHashMap<String, WriteRow>();
    /** session|locationKey -> every write of it, in that session. */
    private final Map<String, List<WriteRow>> writesByLocation =
            new LinkedHashMap<String, List<WriteRow>>();
    /** locationKey -> site|java type -> its first write, in any session. */
    private final Map<String, Map<String, WriteRow>> writeSitesByLocation =
            new LinkedHashMap<String, Map<String, WriteRow>>();
    /** interaction id -> the attaches whose own pairing names it. */
    private final Map<String, List<AttachRow>> attachesByInteraction =
            new LinkedHashMap<String, List<AttachRow>>();
    /** interaction id -> the interaction itself, for every pairing stated. */
    private final Map<String, Interaction> interactions =
            new LinkedHashMap<String, Interaction>();
    /** {@code session|interaction id} -> a forced session's attaches from
     *  before its forced world: its own path's messages alone. */
    private final Map<String, List<AttachRow>> ownAttaches =
            new LinkedHashMap<String, List<AttachRow>>();
    /** {@code session|producer id} -> a forced session's exports from
     *  before its forced world, as {@link #ownAttaches}. */
    private final Map<String, List<ExportRow>> ownExports =
            new LinkedHashMap<String, List<ExportRow>>();
    /** Every symbol the runtime declared, at the sort it minted it at. */
    private final Map<String, Sort> declaredSymbols =
            new LinkedHashMap<String, Sort>();
    /** root id -> whether the corpus ran it at more than one value. */
    private final Map<String, Boolean> varied = new HashMap<String, Boolean>();
    /** {@link #derived}, once per root. */
    private final Map<String, Boolean> derived = new HashMap<String, Boolean>();
    /** root id -> every session's mint of it, built on first ask. */
    private Map<String, List<RootMintRow>> roots;
    /** Root symbol -> every root id declared under it. */
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();
    /** session|occurrence -> that session's first activation of it. */
    private final Map<String, ActivationRow> activationByOccurrence =
            new LinkedHashMap<String, ActivationRow>();
    /** endpoint id -> the endpoint, so an anchor's producer can be found. */
    private final Map<String, Endpoint> endpointById =
            new LinkedHashMap<String, Endpoint>();
    /** node|location -> every occurrence of that node touching it. */
    private final Map<String, Set<String>> locationTouches =
            new LinkedHashMap<String, Set<String>>();
    /** root id -> session -> its mint row. */
    private final Map<String, Map<String, RootMintRow>> rootsById =
            new LinkedHashMap<String, Map<String, RootMintRow>>();
    private final Map<String, OccurrenceAddress> occurrenceById =
            new LinkedHashMap<String, OccurrenceAddress>();
    /** occurrence id -> the sessions whose rows name it, whether or not
     *  they captured it: where a run states it RAN. */
    private final Map<String, Set<String>> namedBy =
            new LinkedHashMap<String, Set<String>>();
    /** What the case declares each root may be, by root id. */
    private final Map<String, RootDomain> declaredDomains =
            new LinkedHashMap<String, RootDomain>();

    /** session id -> the world its focus row states it ran in. */
    private final Map<String, World> worlds =
            new LinkedHashMap<String, World>();

    /**
     * ONE WORLD A REPLAY REFUTED for an open decider arm's flip
     * (WORLD_REFUTED, {@code runtime.FocusedReplay#refuted}): the session
     * that ran it faithfully and never entered the flip's occurrence, the
     * world its focus row states, and why.  The flip is asked again without
     * it ({@link ObligationFactory#solve}); an UNSAT then rests on it.
     */
    public static final class Refuted {
        public final String obligationId;
        public final String sessionId;
        public final World world;
        /** {@link ObligationFactory#wholeWorldDigest}. */
        public final String digest;
        public final WorldRefutation refutation;

        Refuted(String obligationId, String sessionId, World world,
                WorldRefutation refutation) {
            this.obligationId = obligationId;
            this.sessionId = sessionId;
            this.world = world;
            this.digest = ObligationFactory.wholeWorldDigest(world);
            this.refutation = refutation;
        }
    }

    /** flip ({@link ObligationFactory#flip}) -> the worlds replays refuted
     *  for it, in wave and name order. */
    private final Map<String, List<Refuted>> refuted =
            new LinkedHashMap<String, List<Refuted>>();
    /** Obligation id -> the verdict its worker's own file states. */
    private final Map<String, ObligationResult> waveVerdicts =
            new LinkedHashMap<String, ObligationResult>();
    /** Producer endpoint id of a SEND -> the stance its SEND stood in. */
    private final Map<String, ContextShape.Stance> senderStanceByEndpoint =
            new HashMap<String, ContextShape.Stance>();
    /** Producer endpoint id of a SEND -> the occurrence that sent it. */
    private final Map<String, String> senderByEndpoint =
            new LinkedHashMap<String, String>();
    /** Producer endpoint id of a RECV -> the occurrence that took it in. */
    private final Map<String, String> receiverByEndpoint =
            new LinkedHashMap<String, String>();
    /** Producer endpoint id -> the stances of the turns that took it in
     *  at their root, no occurrence open ({@link #doorsOf}). */
    private final Map<String, Set<String>> receivingStances =
            new LinkedHashMap<String, Set<String>>();
    /** Where a context anchored on nothing stands -> the messages it took
     *  into itself (a DataNode's turn and its DataTransfer op; a batching
     *  Overseer turn, every item it flushed at once). */
    private final Map<String, Set<String>> takenInByStance =
            new HashMap<String, Set<String>>();

    private final Arms arms;

    /**
     * THE FORCED SESSIONS (PIPELINE §7.10), held apart: the recording's world
     * with the declared occurrence forced to the throw.  Every row of one is
     * indexed under its session, so its forced path composes and is asked
     * in its own scope ({@link #forcedPaths}), and none in the corpus-wide
     * views -- {@link #sessions}, the rows of an occurrence across sessions,
     * a location's writers and sites, the schedule's senders -- so no other
     * path, arm, slot, closure, witness or verdict reads a forced world.  Its
     * messages from before its forced world are its own path's alone
     * ({@link #ownAttachesOf}, {@link #ownExportsOf}): its handoffs move with
     * their producers there, and no other path pairs with them.  One with no
     * forced target is no session at all.
     */
    private final List<SessionReader> forcedSessions;
    /** Each forced session's forced world's first event: its forced target
     *  row's seq ({@code TargetRow#forced}). */
    private final Map<String, Long> forcedFrom = new HashMap<String, Long>();

    /**
     * WHAT ONE SESSION'S ROWS ALONE GIVE: its state join, the schedule facts
     * the corpus indexes ({@link #indexSchedule}), and what a walk of its
     * expressions found -- functions of those rows only, so a read of the
     * same iteration takes them with the session it keeps ({@link
     * #read(Path, Path, Corpus)}): a landed session's rows never change.
     * Every index across sessions, and every lowering, is built anew.
     */
    private static final class Derived {
        final SessionReader session;
        final SmtLowering.SessionJoin join;
        /** Its schedule, as the corpus indexes it: {@link Fact}s in
         *  order. */
        final List<Fact> schedule;
        /** expression ref -> {@link #expressionSymbols}. */
        final Map<String, Set<String>> symbolsByExpression =
                new ConcurrentHashMap<String, Set<String>>();
        /** {@link #leaves}: the variables one term or read rests on; a
         *  flip's dependence asks every earlier condition of its path
         *  again. */
        final Map<String, Set<String>> leaves =
                new ConcurrentHashMap<String, Set<String>>();
        /** term -> {@link #readLocations}, {@link #readEvents}; expression
         *  ref -> {@link #expressionStateReads}. */
        final Map<String, Set<String>> readLocations =
                new ConcurrentHashMap<String, Set<String>>();
        final Map<String, Set<Long>> readEvents =
                new ConcurrentHashMap<String, Set<Long>>();
        final Map<String, List<StateRead>> stateReads =
                new ConcurrentHashMap<String, List<StateRead>>();

        Derived(SessionReader session) {
            this.session = session;
            this.join = SmtLowering.joinOf(session);
            this.schedule = facts(session);
        }
    }

    /** One schedule fact of a session: where a message was taken in,
     *  sent from, sent by, or received by. */
    private static final class Fact {
        enum Kind { TAKEN_IN, SENDER_STANCE, SENDER, RECEIVER,
            RECEIVING_STANCE }

        final Kind kind;
        final String key;
        final String occurrence;
        final ContextShape.Stance stance;

        Fact(Kind kind, String key, String occurrence,
             ContextShape.Stance stance) {
            this.kind = kind;
            this.key = key;
            this.occurrence = occurrence;
            this.stance = stance;
        }
    }

    private Corpus(Path iteration, List<SessionReader> read,
                   Corpus previous) {
        this.iteration = iteration;
        List<SessionReader> real = new ArrayList<SessionReader>();
        List<SessionReader> forced = new ArrayList<SessionReader>();
        for (SessionReader session : read) {
            // A forced session lands at its forced target only (its run
            // withdraws it otherwise, RowRuntime#closeSession): one without
            // states a forced world nothing fences, and is read as none.
            if (!session.forced()) {
                real.add(session);
            } else if (forcedTarget(session)) {
                forced.add(session);
            }
        }
        this.sessions = Collections.unmodifiableList(real);
        this.forcedSessions = Collections.unmodifiableList(forced);
        for (SessionReader session : real) {
            index(derived(session, previous), false);
        }
        for (SessionReader session : forced) {
            index(derived(session, previous), true);
        }
        this.arms = new Arms(this);
    }

    /** What {@code previous} derived from one session's rows alone, else
     *  derived anew; this corpus's from now on. */
    private Derived derived(SessionReader session, Corpus previous) {
        Derived kept = previous == null ? null
                : previous.bySession.get(session.sessionId());
        Derived of = kept != null && kept.session == session ? kept
                : new Derived(session);
        bySession.put(session.sessionId(), of);
        return of;
    }

    /** Whether a session states a forced target row. */
    private static boolean forcedTarget(SessionReader session) {
        for (TargetRow row : session.targets()) {
            if (row.isForced()) return true;
        }
        return false;
    }

    /** Reads an iteration and its case-declared root domains. */
    public static Corpus read(Path iteration, Path rootDomains)
            throws IOException {
        return read(iteration, rootDomains, null);
    }

    /**
     * The same read, the sessions {@code previous} (a read of the same
     * iteration, or null) holds and the iteration still lists taken from
     * it unread ({@link SessionReader#readAll(Path, List)}), with what was
     * derived from each alone ({@link Derived}); every index across
     * sessions is built anew.  The rows are most of a read: hdfs-11741 i1,
     * 45 s for 175 sessions, every time one landed while a host's solver
     * served ({@code ObligationSolverMain#answerer}); hdfs-adhoc-07 EX1,
     * 140-172 s of a late round's ~900 s, every round its planner planned.
     */
    static Corpus read(Path iteration, Path rootDomains, Corpus previous)
            throws IOException {
        Corpus corpus = new Corpus(iteration, SessionReader.readAll(
                iteration, previous == null
                        ? Collections.<SessionReader>emptyList()
                        : previous.everySession()), previous);
        if (rootDomains != null && Files.isRegularFile(rootDomains)) {
            corpus.declaredDomains.putAll(
                    RootDomain.declared(rootDomains));
        }
        corpus.indexWorlds(iteration);
        corpus.indexRecordedTicks(iteration);
        return corpus;
    }

    /** The recording's schedule, which run_engine sets beside the sessions. */
    static final String RECORDED_SCHEDULE = "recorded_schedule.jsonl";

    /** node|role -> the last daemon tick the recording ran; null when the
     *  iteration states no recorded schedule. */
    private Map<String, Integer> recordedTicks;

    private void indexRecordedTicks(Path iteration) throws IOException {
        Path recorded = iteration.resolve(RECORDED_SCHEDULE);
        if (!Files.isRegularFile(recorded)) return;
        recordedTicks = new HashMap<String, Integer>();
        for (ScheduleEvent event : SessionReader.readSchedule(recorded)) {
            String[] stance = event.context().split("\\|", 3);
            if (stance.length < 2) continue;
            CausalContext.Root tick = daemonTick(CausalContext.parse(stance[1]));
            if (tick != null) {
                recordedTicks.merge(stance[0] + "|" + tick.role().name(),
                        tick.windowIndex(), Math::max);
            }
        }
    }

    /** A daemon tick: a role's w-th root in the window with no declared api
     *  ({@code CausalContext#of(Role, String, int)}), or null. */
    private static CausalContext.Root daemonTick(CausalContext context) {
        if (!(context instanceof CausalContext.Root)) return null;
        CausalContext.Root root = (CausalContext.Root) context;
        return root.api().isEmpty() ? root : null;
    }

    /**
     * The daemon tick that began this occurrence's chain -- its own root, or
     * through each anchor the stance its sender's SEND stood in (a DataNode
     * sends heartbeats from the tick's root, in no region) -- when the
     * recording ran no tick of that role on that node so late, or null.  A
     * replay outlasting the
     * recording runs a periodic daemon more often, and no loop bound stops
     * it: the daemon's loop runs in no region (hdfs-11741 v86: the NameNode
     * handlers of DataNode heartbeats #44 to #100, against #4 and #5
     * recorded, were grown in every wave).  Null too when the iteration
     * states no recorded schedule.
     */
    public String tickPastRecording(OccurrenceAddress occurrence) {
        if (recordedTicks == null) return null;
        String node = occurrence.node().render();
        CausalContext context = occurrence.context();
        Set<String> walked = new HashSet<String>();
        while (context instanceof CausalContext.Anchor) {
            String producer =
                    ((CausalContext.Anchor) context).producerEndpointId();
            ContextShape.Stance stance = senderStanceByEndpoint.get(producer);
            if (stance == null || !walked.add(producer)) break;
            node = stance.node();
            context = stance.context();
        }
        CausalContext.Root tick = daemonTick(context);
        if (tick == null) return null;
        int last = recordedTicks.getOrDefault(node + "|" + tick.role().name(),
                0);
        return tick.windowIndex() <= last ? null : node + " "
                + tick.render() + ", the recording's last being #" + last;
    }

    /**
     * A causal context as the branch rule compares it ({@link Branches},
     * {@link ContextShape}): each sender is the endpoint a row of the corpus
     * states, else the stance its SEND stood in.
     */
    public List<String> contextShape(CausalContext context) {
        return ContextShape.of(context, producer -> {
            Endpoint sender = endpointById.get(producer);
            return sender == null ? senderStanceByEndpoint.get(producer)
                    : new ContextShape.Stance(
                            sender.occurrence().node().render(),
                            sender.occurrence().context());
        });
    }

    /** The world of each replay, off its FOCUS ROW (not {@code
     *  obligation.jsonl}, a subset without clocks or flips: reading a world
     *  from it drops skews). A planted assignment is stated by the ask alone
     *  ({@code ConcolicRegionRuntime#applyFocusedRootAssignment}). */
    private void indexWorlds(Path iteration) throws IOException {
        List<ObligationDir> workers = ObligationDir.workersIn(iteration);
        for (Map.Entry<String, JsonObject> world
                : ObligationDir.worlds(workers).entrySet()) {
            worlds.put(world.getKey(), ExploreCodec.readWorld(
                    world.getValue()));
        }
        for (ObligationDir worker : workers) {
            for (ObligationResult result : worker.results()) {
                waveVerdicts.put(result.obligationId(), result);
                if (result.refutation() == null || worker.focus().isEmpty()) {
                    continue;
                }
                JsonObject focus = worker.focus().get(0);
                JsonObject flip = JsonFields.object(focus, "flip");
                if (!flip.has("siteId")) continue;
                refuted.computeIfAbsent(ObligationFactory.flip(
                        JsonFields.optionalString(focus, "taskId"),
                        JsonFields.optionalString(focus, "pathId"),
                        JsonFields.optionalString(flip, "siteId"),
                        flip.get("ordinal").getAsInt(),
                        flip.get("outcome").getAsBoolean()),
                        key -> new ArrayList<Refuted>()).add(new Refuted(
                        result.obligationId(), worker.sessionId(),
                        ExploreCodec.readWorld(focus), result.refutation()));
            }
        }
    }

    /** How many distinct worlds (by digest) replays refuted for one flip:
     *  what the valve {@link ObligationFactory#MAX_REFUTED_WORLDS} counts. */
    public static int distinctWorlds(List<Refuted> refuted) {
        Set<String> digests = new LinkedHashSet<String>();
        for (Refuted world : refuted) digests.add(world.digest);
        return digests.size();
    }

    /** The worlds replays refuted for one flip ({@link ObligationFactory
     *  #flip}); empty for any flip but an open decider arm's. */
    public List<Refuted> refutedWorlds(String flip) {
        List<Refuted> worlds = refuted.get(flip == null ? "" : flip);
        return worlds == null ? Collections.<Refuted>emptyList()
                : Collections.unmodifiableList(worlds);
    }

    /**
     * The decisions a reached anchor asks for its open decider arms
     * (TargetRow.OpenArm): of each run that reached it and left phi without
     * an arm, the one decision whose flip runs it, as {@link FlipQuery#asked}
     * spells it: what the closure plans the asks by ({@link #openArmFlip}
     * tells which way of it runs the arm).
     */
    public Set<String> openArmAsks(OccurrenceAddress anchor) {
        Set<String> asks = new LinkedHashSet<String>();
        for (TargetRow row : targetsOn(anchor)) {
            TargetRow.OpenArm open = row.openArm();
            if (row.reachedAnchor() && open != null
                    && !open.askedSiteId().isEmpty()) {
                asks.add(FlipQuery.asked(open.askedSiteId(),
                        open.askedOrdinal()));
            }
        }
        return asks;
    }

    /**
     * Whether a flip runs an open decider arm of a reached anchor: it is the
     * decision a run that left the arm open asks ({@link #openArmAsks}), and
     * it goes TOWARD the arm -- the other outcome than that run took there
     * (at the deciding decision itself, the arm's own outcome).  A flip of
     * the same decision the other way is an ordinary flip.
     */
    public boolean openArmFlip(OccurrenceAddress anchor, String siteId,
                               int ordinal, boolean flippedOutcome) {
        for (TargetRow row : targetsOn(anchor)) {
            TargetRow.OpenArm open = row.openArm();
            if (!row.reachedAnchor() || open == null
                    || !open.askedSiteId().equals(siteId)
                    || open.askedOrdinal() != ordinal) {
                continue;
            }
            Boolean ran = null;
            for (DecisionRow decision : decisionsOf(row.sessionId(),
                    anchor)) {
                if (decision.siteId().equals(siteId)
                        && decision.ordinal() == ordinal) {
                    ran = decision.outcome();
                }
            }
            if (ran == null && open.siteId().equals(siteId)
                    && open.ordinal() == ordinal) {
                ran = !open.outcome();
            }
            if (ran != null && ran != flippedOutcome) return true;
        }
        return false;
    }

    /** The world one session ran in; empty for the seed or a session with no
     *  focus row. */
    public World world(String sessionId) {
        World stated = worlds.get(sessionId == null ? "" : sessionId);
        return stated == null ? World.empty() : stated;
    }

    /**
     * WHAT ONE SESSION'S WORLD DELIVERED TO A TASK, digested: the world part
     * of an arm's key ({@link ObligationFactory#dependence}). The EFFECT at
     * the task, never the cause (keying by upstream flips asks one question
     * per flip combination).
     *
     * <p>Covers the occurrence -- whether it ran, and per site how many
     * handoffs from which producers -- and each factor member that FEEDS it
     * ({@link #feeders}: they write state it reads) by what it delivered
     * it: the same handoffs, per-site counts of its writes to {@code
     * locations}, the state the flipped guard reads, and whether it wrote
     * any state the occurrence's region reads on ANY arm -- a location its
     * code, folded regions' included, reads where a replay versions it
     * ({@link StaticScopeMap#readLocations}), not
     * only what the arm this session took read, since the flipped arm reads
     * what the taken one never did (a renewer's write of the lease map the
     * expiry scan iterates only once a lease has expired) --, not how often,
     * which replays vary; and whether it ran them as an activation.  Their
     * handoffs whole, not only those the guard names: the arm consumes them
     * after the flip (hdfs-11741: dn1's expiry scan names only its own
     * clock, and the witness is that scan flipped in the world whose key
     * conversion delivered four keys instead of five). A co-reader feeds
     * nothing (hdfs-17899-bug2: every RPC of the SPS reads the IPC
     * connection an IPC door reads, and keyed by all of them one door flip
     * was 11 obligations). Trap: never a member's writes elsewhere (replays
     * vary them: hdfs-11741's balancer members write SASL and HashMap
     * internals a different number of times in almost every run), never the
     * region's own reads or decisions (behaviour, not input), never
     * delivered VALUES (carried symbolically; clock values differ every
     * run).</p>
     *
     * <p>A function of the session and the epoch's static map alone,
     * whatever the corpus has learned since: the members as a set (the
     * order the corpus lists the factor in moves as sessions land), and
     * none that delivered nothing, whether the session never ran it or ran
     * it to no handoff and no write of state the occurrence's region reads
     * -- its line re-keyed every arm of the session once the corpus found
     * it a feeder (solr-bugs-reindex-cleanup SG1: 627 arms under 8,868 ids,
     * most of the re-keyed ones by members that ran and delivered nothing).
     * LIMIT: a member's write the recording states at no write site
     * (unwoven) re-keys no arm.</p>
     */
    public String inputShape(String sessionId, OccurrenceAddress occurrence,
                             List<OccurrenceAddress> factor,
                             Set<String> locations, StaticScopeMap scope) {
        Set<String> readable = scope.readLocations(occurrence.regionId());
        List<String> members = new ArrayList<String>();
        for (OccurrenceAddress member : factor) {
            if (member.equals(occurrence)) continue;
            List<String> handoffs = attachSites(sessionId, member);
            List<String> writes = writeSites(sessionId, member, locations);
            boolean fed = feeds(sessionId, member, readable, scope);
            if (handoffs.isEmpty() && writes.isEmpty() && !fed) continue;
            boolean ran = activation(sessionId, member) != null;
            members.add(member.id() + ':' + ran + handoffs
                    + producers(sessionId, member) + writes + fed);
        }
        Collections.sort(members);
        StringBuilder text = new StringBuilder();
        text.append(occurrence.id()).append(':')
                .append(activation(sessionId, occurrence) != null)
                .append(attachSites(sessionId, occurrence))
                .append(producers(sessionId, occurrence));
        for (String member : members) text.append('\n').append(member);
        return ArtifactIO.digest(text.toString(), 16);
    }

    /** Whether one member's writes in one session store a location of
     *  {@code readable} ({@link StaticScopeMap#storedAt}); an INITIAL row
     *  is no write. */
    private boolean feeds(String sessionId, OccurrenceAddress member,
                          Set<String> readable, StaticScopeMap scope) {
        if (readable.isEmpty()) return false;
        for (WriteRow write : writesOn.of(member.id(), sessionId)) {
            if (!write.initial() && !Collections.disjoint(readable,
                    scope.storedAt(write.endpoint().site(),
                            write.javaType(), write.location().kind()))) {
                return true;
            }
        }
        return false;
    }

    /**
     * What this corpus answered about one task (the planner's, or the
     * solver's {@code ClosurePlanner#taskOf}), by the task object: the
     * frontier keys every arm its recorded paths took and the candidates
     * key the same arms again ({@link ObligationFactory#dependence}:
     * hdfs-adhoc-07 EX1, 227,681 asks and ~260 s of a ~900 s round, and
     * the task's feeders asked anew each time).  A corpus does not change
     * once read, so each answer is its rows' and the task's.
     */
    private static final class OfTask {
        /** {@link #feeders(Task)}, once asked. */
        List<OccurrenceAddress> feeders;
        /** path id#decision index -> its dependence. */
        final Map<String, String> dependence = new HashMap<String, String>();
    }

    private final Map<Task, OfTask> ofTask =
            new java.util.IdentityHashMap<Task, OfTask>();

    private synchronized OfTask ofTask(Task task) {
        return ofTask.computeIfAbsent(task, key -> new OfTask());
    }

    /** One arm's dependence ({@code ObligationFactory#dependence}) of one
     *  task, by its path and decision: computed once. */
    String dependence(Task task, String decision, Supplier<String> compute) {
        OfTask of = ofTask(task);
        synchronized (of) {
            String held = of.dependence.get(decision);
            if (held != null) return held;
        }
        String keyed = compute.get();
        synchronized (of) {
            of.dependence.put(decision, keyed);
        }
        return keyed;
    }

    /** {@link #feeders(OccurrenceAddress, List)} of one task's occurrence
     *  and factor, once per task. */
    public List<OccurrenceAddress> feeders(Task task) {
        OfTask of = ofTask(task);
        synchronized (of) {
            if (of.feeders == null) {
                of.feeders = Collections.unmodifiableList(
                        feeders(task.focused(), task.factor()));
            }
            return of.feeders;
        }
    }

    /** The members of a factor that WRITE state the occurrence reads, in
     *  any session: through them the world flows in. */
    public List<OccurrenceAddress> feeders(OccurrenceAddress occurrence,
                                           List<OccurrenceAddress> factor) {
        Set<String> read = readLocations.getOrDefault(occurrence.id(),
                Collections.<String>emptySet());
        List<OccurrenceAddress> feeders = new ArrayList<OccurrenceAddress>();
        for (OccurrenceAddress member : factor) {
            if (!Collections.disjoint(read, writtenLocations.getOrDefault(
                    member.id(), Collections.<String>emptySet()))) {
                feeders.add(member);
            }
        }
        return feeders;
    }

    /** Per-site handoff counts (not values). */
    private List<String> attachSites(String sessionId,
                                     OccurrenceAddress occurrence) {
        List<String> sites = new ArrayList<String>();
        for (AttachRow attach : attachesOn(sessionId, occurrence)) {
            sites.add(attach.endpoint().site());
        }
        Collections.sort(sites);
        return sites;
    }

    /** Which occurrences delivered them: a new producer is new topology.
     *  A set, sorted: the order replies arrive in is a race, never input
     *  (hdfs-adhoc-07 CC5: the client's recovery takes the three journal
     *  nodes' replies in any order, and keyed by that order every arm of
     *  every client call it feeds was asked once per order). */
    private Set<String> producers(String sessionId,
                                  OccurrenceAddress occurrence) {
        Set<String> from = new TreeSet<String>();
        for (AttachRow attach : attachesOn(sessionId, occurrence)) {
            Endpoint producer = attach.producer();
            if (producer == null) continue;
            OccurrenceAddress at = producer.occurrence();
            from.add(at == null ? producer.id() : at.id());
        }
        return from;
    }

    /** Per-site counts of the writes to {@code locations} (not values); an
     *  INITIAL row is no write. */
    private List<String> writeSites(String sessionId,
                                    OccurrenceAddress occurrence,
                                    Set<String> locations) {
        List<String> sites = new ArrayList<String>();
        for (WriteRow write : writesOn.of(occurrence.id(), sessionId)) {
            if (write.initial() || !locations.contains(
                    SmtLowering.locationKey(write.location()))) {
                continue;
            }
            sites.add(write.endpoint().site());
        }
        Collections.sort(sites);
        return sites;
    }

    /** The verdict the WAVE's file states for one obligation, or null. Only a
     *  cross-check: the SESSION's row is the verdict, and a corpus stating two
     *  different verdicts is refused by name. */
    public ObligationResult waveVerdict(String obligationId) {
        return waveVerdicts.get(obligationId == null ? "" : obligationId);
    }

    /** The directory the sessions were read from (the slot table sits beside
     *  them). */
    public Path iteration() {
        return iteration;
    }

    /**
     * The occurrence that sent the message a consumer served under
     * {@code producerEndpointId} (its ANCHOR), or null: the schedule's SEND
     * events state the producer endpoint the message carried.
     */
    public OccurrenceAddress senderOf(String producerEndpointId) {
        String sender = senderByEndpoint.get(producerEndpointId);
        return sender == null ? null : occurrenceById.get(sender);
    }

    /**
     * The messages that started {@code occurrence}: its context's anchor,
     * else every message that context took into itself (a DataNode's turn
     * received its DataTransfer op without standing on it; a batching
     * Overseer turn is started by each item it took in), or none.
     */
    public Set<String> startedBy(OccurrenceAddress occurrence) {
        return occurrence.context() instanceof CausalContext.Anchor
                ? Collections.singleton(((CausalContext.Anchor)
                        occurrence.context()).producerEndpointId())
                : takenInByStance.getOrDefault(
                        ContextShape.Stance.of(occurrence).render(),
                        Collections.<String>emptySet());
    }

    /** The occurrence that TOOK IN the message served under {@code
     *  producerEndpointId} (its RECV of it), or null: the receiving door
     *  whose fault point decides delivery (IDENTITY §7.3). */
    public OccurrenceAddress receiverOf(String producerEndpointId) {
        String receiver = receiverByEndpoint.get(producerEndpointId);
        return receiver == null ? null : occurrenceById.get(receiver);
    }

    /**
     * Every door of the message that started {@code served} (IDENTITY
     * §7.3): the occurrence that sent it ({@link #senderOf}), the occurrence
     * that took it in ({@link #receiverOf}), every occurrence of the turn
     * that sent it -- whatever it ran before the send, on any of its
     * threads, a fault of which can stop the turn short of it (RestoreCmd's
     * RESTORECORE requests before its ACTIVE offer) -- and every occurrence
     * of another turn that took it in at its root, before any of its
     * regions opened (an Overseer queue loop's turn and the task item it
     * consumed, whose ZooKeeper door then runs in a region of the turn).
     * The served occurrence's own turn holds no door of it: its other
     * occurrences are what the message started too (an Overseer state
     * update's turn).
     */
    public List<OccurrenceAddress> doorsOf(String producerEndpointId,
                                           OccurrenceAddress served) {
        List<OccurrenceAddress> doors = new ArrayList<OccurrenceAddress>();
        for (OccurrenceAddress door : new OccurrenceAddress[] {
                senderOf(producerEndpointId),
                receiverOf(producerEndpointId)}) {
            if (door != null && !doors.contains(door)) doors.add(door);
        }
        Set<String> stances = new HashSet<String>(receivingStances
                .getOrDefault(producerEndpointId,
                        Collections.<String>emptySet()));
        ContextShape.Stance sentFrom =
                senderStanceByEndpoint.get(producerEndpointId);
        if (sentFrom != null) stances.add(sentFrom.render());
        if (stances.isEmpty()) return doors;
        String own = ContextShape.Stance.of(served).render();
        for (OccurrenceAddress occurrence : occurrenceById.values()) {
            String stance = ContextShape.Stance.of(occurrence).render();
            if (stances.contains(stance) && !stance.equals(own)
                    && !doors.contains(occurrence)) {
                doors.add(occurrence);
            }
        }
        return doors;
    }

    /** One session's schedule as the corpus indexes it, read once. */
    private static List<Fact> facts(SessionReader session) {
        List<ScheduleEvent> events;
        try {
            events = session.schedule();
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        List<Fact> facts = new ArrayList<Fact>();
        for (ScheduleEvent event : events) {
            // A context that took a message into itself stands under it,
            // in or out of a region.
            if (!event.received().isEmpty()) {
                ContextShape.Stance at =
                        ContextShape.Stance.ofSend(event.context());
                if (at != null
                        && !(at.context() instanceof CausalContext.Anchor)) {
                    facts.add(new Fact(Fact.Kind.TAKEN_IN, at.render(),
                            event.received(), null));
                }
            }
            // Where every message was sent from, in or out of a region: a
            // daemon tick's heartbeat is sent from the tick's root alone.
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                ContextShape.Stance stance =
                        ContextShape.Stance.ofSend(event.context());
                if (stance != null) {
                    facts.add(new Fact(Fact.Kind.SENDER_STANCE,
                            event.endpoint(), "", stance));
                }
            }
            if (event.occurrence().isEmpty()) {
                // Taken in at a turn's root, before any region of it opened
                // (a queue item a turn consumes first): the turn's every
                // occurrence is its receiver.  A turn standing on the
                // message (a request's handler) is what it started, no door
                // of it.
                ContextShape.Stance at =
                        ContextShape.Stance.ofSend(event.context());
                if (!event.received().isEmpty() && at != null
                        && !(at.context() instanceof CausalContext.Anchor)) {
                    facts.add(new Fact(Fact.Kind.RECEIVING_STANCE,
                            event.received(), "", at));
                }
                continue;
            }
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                facts.add(new Fact(Fact.Kind.SENDER, event.endpoint(),
                        event.occurrence(), null));
            } else if (!event.received().isEmpty()) {
                facts.add(new Fact(Fact.Kind.RECEIVER, event.received(),
                        event.occurrence(), null));
            }
        }
        return facts;
    }

    private void indexSchedule(String sessionId, List<Fact> facts) {
        for (Fact fact : facts) {
            switch (fact.kind) {
                case TAKEN_IN:
                    takenInByStance.computeIfAbsent(fact.key,
                            key -> new LinkedHashSet<String>())
                            .add(fact.occurrence);
                    break;
                case SENDER_STANCE:
                    senderStanceByEndpoint.put(fact.key, fact.stance);
                    break;
                case SENDER:
                    senderByEndpoint.put(fact.key, fact.occurrence);
                    named(sessionId, fact.occurrence);
                    break;
                case RECEIVING_STANCE:
                    receivingStances.computeIfAbsent(fact.key,
                            key -> new LinkedHashSet<String>())
                            .add(fact.stance.render());
                    break;
                default:
                    receiverByEndpoint.put(fact.key, fact.occurrence);
                    break;
            }
        }
    }

    /** One session's rows; {@code apart}: a forced one's, under its
     *  session only ({@link #forcedSessions}), its messages from before its
     *  forced world its own path's ({@code FlipQuery}'s own run). */
    private void index(Derived of, boolean apart) {
        SessionReader session = of.session;
        long world = Long.MAX_VALUE;
        if (apart) {
            for (TargetRow row : session.targets()) {
                if (row.isForced()) world = Math.min(world, row.seq());
            }
        } else {
            indexSchedule(session.sessionId(), of.schedule);
        }
        sessionById.put(session.sessionId(), session);
        loweringById.put(session.sessionId(),
                SmtLowering.forSession(session, of.join));
        for (ActivationRow row : session.activations()) {
            activationByOccurrence.putIfAbsent(session.sessionId() + "|"
                    + row.occurrence().id(), row);
            if (apart) continue;
            remember(session.sessionId(), row.occurrence());
            // The sender an anchor names: a causal chain goes on through it.
            if (row.anchorProducer() != null) {
                endpointById.put(row.anchorProducer().id(),
                        row.anchorProducer());
                remember(session.sessionId(),
                        row.anchorProducer().occurrence());
            }
            add(activations, row.occurrence().id(), row);
        }
        for (DecisionRow row : session.decisions()) {
            if (!apart) remember(session.sessionId(), row.occurrence());
            add(decisions, session.sessionId() + "|" + row.occurrence().id(), row);
            // A decision's clock cells are corpus symbols at Int.
            for (String cell : row.clockReadings().keySet()) {
                declaredSymbols.put(cell, Sort.INT);
            }
        }
        for (ExportRow row : session.exports()) {
            // A forced world's export is no message any arm delivers; one
            // before it is its own path's alone (Arms#armsAt's scope).
            if (row.seq() >= world) continue;
            if (apart) {
                add(ownExports, session.sessionId() + "|"
                        + row.endpoint().id(), row);
                continue;
            }
            add(exports, row.endpoint().id(), row);
            remember(session.sessionId(), row.endpoint().occurrence());
            endpointById.put(row.endpoint().id(), row.endpoint());
        }
        for (AttachRow row : session.attaches()) {
            attachBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            handoffSymbols.add(row.symbol());
            attachesOn.add(row.endpoint().occurrence().id(), row.sessionId(),
                    row, apart);
            // One variable, one sort: from the JVM descriptor, never a value's
            // spelling.
            declaredSymbols.put(row.symbol(),
                    JavaSmtSorts.sortOfJava(row.javaType()));
            Interaction interaction = row.interaction();
            if (interaction != null && apart && row.seq() < world) {
                add(ownAttaches, session.sessionId() + "|"
                        + interaction.id(), row);
            } else if (interaction != null && !apart) {
                interactions.put(interaction.id(), interaction);
                add(attachesByInteraction, interaction.id(), row);
            }
            if (apart) continue;
            remember(session.sessionId(), row.endpoint().occurrence());
            endpointById.put(row.endpoint().id(), row.endpoint());
            if (row.producer() != null) {
                endpointById.put(row.producer().id(), row.producer());
                remember(session.sessionId(), row.producer().occurrence());
            }
        }
        for (RootMintRow row : session.roots()) {
            if (!apart) remember(session.sessionId(), row.occurrence());
            rootBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            rootsById.computeIfAbsent(row.rootId(),
                    key -> new LinkedHashMap<String, RootMintRow>())
                    .put(session.sessionId(), row);
            rootIdsBySymbol.computeIfAbsent(row.symbol(),
                    key -> new LinkedHashSet<String>()).add(row.rootId());
            declaredSymbols.put(row.symbol(),
                    row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT);
        }
        for (WriteRow row : session.writes()) {
            String location = SmtLowering.locationKey(row.location());
            writeByVersion.put(versionKey(session.sessionId(), location,
                    row.version()), row);
            writesOn.add(row.endpoint().occurrence().id(), row.sessionId(), row,
                    apart);
            add(writesByLocation, session.sessionId() + "|" + location, row);
            if (apart) continue;
            remember(session.sessionId(), row.endpoint().occurrence());
            // An INITIAL's endpoint observed the location; it wrote nothing.
            if (!row.initial()) {
                located(writtenLocations, row.endpoint().occurrence(),
                        location);
                writeSitesByLocation.computeIfAbsent(location,
                        ignored -> new LinkedHashMap<String, WriteRow>())
                        .putIfAbsent(row.endpoint().site() + "|"
                                + row.javaType(), row);
            }
            endpointById.put(row.endpoint().id(), row.endpoint());
            touch(row.endpoint().occurrence(), row.location());
        }
        for (TargetRow row : session.targets()) {
            targetsOn.add(row.occurrence().id(), row.sessionId(), row, apart);
            if (apart) {
                if (row.isForced()) {
                    forcedFrom.merge(session.sessionId(), row.seq(),
                            Math::min);
                }
                continue;
            }
            remember(session.sessionId(), row.occurrence());
        }
        for (ReadRow row : session.reads()) {
            if (!row.symbol().isEmpty()) {
                readBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            }
            readsOn.add(row.endpoint().occurrence().id(), row.sessionId(), row,
                    apart);
            if (apart) continue;
            remember(session.sessionId(), row.endpoint().occurrence());
            located(readLocations, row.endpoint().occurrence(),
                    SmtLowering.locationKey(row.location()));
            endpointById.put(row.endpoint().id(), row.endpoint());
            touch(row.endpoint().occurrence(), row.location());
        }
    }

    private void touch(OccurrenceAddress occurrence, LocationId location) {
        locationTouches.computeIfAbsent(touchKey(occurrence, location),
                key -> new LinkedHashSet<String>()).add(occurrence.id());
    }

    /** node|location: one location of one JVM. */
    private static String touchKey(OccurrenceAddress occurrence,
                                   LocationId location) {
        return occurrence.node().render() + "|"
                + SmtLowering.locationKey(location);
    }

    /** One occurrence a session's rows name, by address. */
    private void remember(String sessionId, OccurrenceAddress occurrence) {
        if (occurrence == null) return;
        occurrenceById.put(occurrence.id(), occurrence);
        named(sessionId, occurrence.id());
    }

    private void named(String sessionId, String occurrenceId) {
        namedBy.computeIfAbsent(occurrenceId,
                key -> new LinkedHashSet<String>()).add(sessionId);
    }

    private static <T> void add(Map<String, List<T>> into, String key, T row) {
        into.computeIfAbsent(key, ignored -> new ArrayList<T>()).add(row);
    }

    private static void located(Map<String, Set<String>> into,
                                OccurrenceAddress occurrence, String location) {
        into.computeIfAbsent(occurrence.id(),
                ignored -> new LinkedHashSet<String>()).add(location);
    }

    /**
     * Rows by occurrence, then by session, in recorded order: one session's
     * rows at an occurrence without filtering every session's
     * (hdfs-17899-bug2's planner, 480 worlds, spent a wave's 20 minutes
     * scanning them per recorded decision).
     */
    private static final class ByOccurrence<T> {
        private final Map<String, Map<String, List<T>>> rows =
                new LinkedHashMap<String, Map<String, List<T>>>();
        /** A forced session's rows ({@link #forcedSessions}): its own, in
         *  no session's {@link #all}. */
        private final Set<String> apart = new HashSet<String>();

        void add(String occurrenceId, String sessionId, T row,
                 boolean forced) {
            if (forced) apart.add(sessionId);
            rows.computeIfAbsent(occurrenceId,
                            ignored -> new LinkedHashMap<String, List<T>>())
                    .computeIfAbsent(sessionId, ignored -> new ArrayList<T>())
                    .add(row);
        }

        /** One session's. */
        List<T> of(String occurrenceId, String sessionId) {
            Map<String, List<T>> bySession = rows.get(occurrenceId);
            List<T> own = bySession == null ? null : bySession.get(sessionId);
            return own == null ? Collections.<T>emptyList()
                    : Collections.unmodifiableList(own);
        }

        /** Every session's, sessions in the order they were read. */
        List<T> all(String occurrenceId) {
            Map<String, List<T>> bySession = rows.get(occurrenceId);
            if (bySession == null) return Collections.<T>emptyList();
            List<T> all = new ArrayList<T>();
            for (Map.Entry<String, List<T>> own : bySession.entrySet()) {
                if (!apart.contains(own.getKey())) all.addAll(own.getValue());
            }
            return all;
        }
    }

    /** One version of one location in one session; {@link
     *  SmtLowering#locationKey} is the one location spelling. */
    private static String versionKey(String sessionId, String locationKey,
                                     long version) {
        return sessionId + "|" + locationKey + "|" + version;
    }

    /** One path's id: the session it ran in and the occurrence it ran. */
    public static String pathId(String sessionId,
                                OccurrenceAddress occurrence) {
        return ArtifactIO.digest(sessionId + "|" + occurrence.id(), 16);
    }

    /** The recording: the one session whose manifest states {@code role: SEED},
     *  else "" (none or several), which callers refuse by name. */
    public String seedSessionId() {
        String seed = SessionReader.seedSessionId(sessions);
        return seed == null ? "" : seed;
    }

    /** Every session that states SEED: what such a refusal names. */
    public List<String> seedSessionIds() {
        return SessionReader.seedSessionIds(sessions);
    }

    /** One session's lowering: the one the composer lowers with. */
    public SmtLowering lowering(String sessionId) {
        return loweringById.get(sessionId);
    }

    /**
     * Every session's lowering as {@link #read} built it.  A lowering keeps
     * what it lowered -- its memo, the names it minted, the count its refused
     * constructs are named by -- so a query built after another would name
     * them differently.  A question asked of a corpus read once for many
     * ({@code ObligationSolverMain --serve}) starts from here: what a JVM of
     * its own would have had.  Every other memo of a corpus is a function of
     * its rows alone.
     */
    void freshLowerings() {
        for (SessionReader session : everySession()) {
            loweringById.put(session.sessionId(), SmtLowering.forSession(
                    session, bySession.get(session.sessionId()).join));
        }
    }

    /** One session's state join; a session this corpus lacks joins nothing. */
    public SmtLowering.SessionJoin join(String sessionId) {
        Derived of = bySession.get(sessionId);
        return of == null ? SmtLowering.NO_JOIN : of.join;
    }

    public List<SessionReader> sessions() {
        return sessions;
    }

    /** {@link #sessions} and the forced ones, as read. */
    private List<SessionReader> everySession() {
        List<SessionReader> every = new ArrayList<SessionReader>(sessions);
        every.addAll(forcedSessions);
        return every;
    }

    /**
     * The FORCED PATHS of one occurrence (PIPELINE §7.10): each forced
     * session read whole whose own verdict admits it and whose target row
     * reached the occurrence forced, its path there; a corpus-wide view
     * lists none.
     */
    public List<RecordedPath> forcedPaths(OccurrenceAddress occurrence) {
        List<RecordedPath> paths = new ArrayList<RecordedPath>();
        for (SessionReader session : forcedSessions) {
            TargetRow target = target(session.sessionId(), occurrence);
            if (target == null || !target.isForced()
                    || !target.reachedAnchor()
                    || !session.incomplete().isEmpty()
                    || !forcedReached(session)) {
                continue;
            }
            RecordedPath path = path(session.sessionId(), occurrence);
            if (path != null) paths.add(path);
        }
        return paths;
    }

    /** Whether a forced session's own verdict states its target reached
     *  forced ({@code runtime.ForcedArms}). */
    private static boolean forcedReached(SessionReader session) {
        if (session.obligations().isEmpty()) return false;
        for (ObligationResult result : session.obligations()) {
            if (result.verdict() != Verdict.ADMITTED) return false;
        }
        return true;
    }

    /** Whether this session is a forced one (held apart). */
    public boolean forced(String sessionId) {
        return forcedFrom.containsKey(sessionId)
                || sessionById.containsKey(sessionId)
                && sessionById.get(sessionId).forced();
    }

    @Override
    public long forcedFrom(String sessionId) {
        Long from = forcedFrom.get(sessionId);
        return from == null ? Long.MAX_VALUE : from.longValue();
    }

    public SessionReader session(String sessionId) {
        return sessionById.get(sessionId);
    }

    public OccurrenceAddress occurrence(String occurrenceId) {
        return occurrenceById.get(occurrenceId);
    }

    /** Every occurrence any session of this corpus published a row for. */
    public List<OccurrenceAddress> occurrences() {
        return new ArrayList<OccurrenceAddress>(occurrenceById.values());
    }

    /** Every path of one occurrence, one per session that ran it. An
     *  activation, a decision or a TARGET row says it ran; a run with no
     *  decisions has the empty path (its absence is what a divergence is). */
    public List<RecordedPath> pathsOf(OccurrenceAddress occurrence) {
        List<RecordedPath> paths = new ArrayList<RecordedPath>();
        for (SessionReader session : sessions) {
            RecordedPath path = path(session.sessionId(), occurrence);
            if (path != null) paths.add(path);
        }
        return paths;
    }

    /** One session's path at one occurrence, or null when it never ran it. */
    public RecordedPath path(String sessionId, OccurrenceAddress occurrence) {
        ActivationRow activation = activation(sessionId, occurrence);
        List<DecisionRow> taken = decisions.get(
                sessionId + "|" + occurrence.id());
        if (activation == null && taken == null
                && target(sessionId, occurrence) == null) {
            return null;
        }
        return new RecordedPath(sessionId, occurrence,
                taken == null ? new ArrayList<DecisionRow>() : taken);
    }

    /** The sessions whose rows name this occurrence, in corpus order: an
     *  activation, a decision, a row at one of its endpoints, a SEND it made,
     *  or an anchor naming it as the sender. */
    public Set<String> namedBy(OccurrenceAddress occurrence) {
        Set<String> sessions = namedBy.get(occurrence.id());
        return sessions == null ? Collections.<String>emptySet()
                : Collections.unmodifiableSet(sessions);
    }

    public ActivationRow activation(String sessionId,
                                    OccurrenceAddress occurrence) {
        return activationOf(sessionId, occurrence.id());
    }

    /** Every session's activation rows of one occurrence, in read order. */
    public List<ActivationRow> activationsOf(OccurrenceAddress occurrence) {
        return activations.getOrDefault(occurrence.id(),
                Collections.<ActivationRow>emptyList());
    }

    public List<DecisionRow> decisionsOf(String sessionId,
                                         OccurrenceAddress occurrence) {
        return decisions.getOrDefault(sessionId + "|" + occurrence.id(),
                Collections.<DecisionRow>emptyList());
    }

    public List<AttachRow> attachesOn(OccurrenceAddress occurrence) {
        return attachesOn.all(occurrence.id());
    }

    /** Every target row published for one occurrence, in any session. */
    public List<TargetRow> targetsOn(OccurrenceAddress occurrence) {
        return targetsOn.all(occurrence.id());
    }

    /** One session's target row at one occurrence, or null. */
    public TargetRow target(String sessionId, OccurrenceAddress occurrence) {
        List<TargetRow> own = targetsOn.of(occurrence.id(), sessionId);
        return own.isEmpty() ? null : own.get(0);
    }

    public List<ReadRow> readsOn(OccurrenceAddress occurrence) {
        return readsOn.all(occurrence.id());
    }

    /** Every attach of ONE session whose consumer sits at this occurrence. */
    public List<AttachRow> attachesOn(String sessionId,
                                      OccurrenceAddress occurrence) {
        return attachesOn.of(occurrence.id(), sessionId);
    }

    /** Every read ONE session made at this occurrence, in recorded order. */
    public List<ReadRow> readsOn(String sessionId,
                                 OccurrenceAddress occurrence) {
        return readsOn.of(occurrence.id(), sessionId);
    }

    public List<WriteRow> writesOn(OccurrenceAddress occurrence) {
        return writesOn.all(occurrence.id());
    }

    /** Every write ONE session made at this occurrence, in recorded order. */
    public List<WriteRow> writesOn(String sessionId,
                                   OccurrenceAddress occurrence) {
        return writesOn.of(occurrence.id(), sessionId);
    }

    // ---- The causal graph (GreyGraph §3.1) ----

    /**
     * The writes one read could have taken its value from: the observed one
     * and every other the one eligibility rule admits ({@code
     * smt.Arms#eligible}, which {@code Arms#stateArms} asks too: the
     * composition offers the same alternatives).  Used by the closure
     * ({@link ClosurePlanner#writers}) and the flip query.
     *
     * @param reader the reading occurrence, for the concurrency rule
     */
    public List<WriteRow> eligibleWrites(String sessionId, String locationKey,
                                         long observedVersion,
                                         OccurrenceAddress reader) {
        String key = sessionId + "|" + locationKey + "|" + observedVersion
                + "|" + (reader == null ? "" : reader.id());
        List<WriteRow> held = eligible.get(key);
        if (held != null) return held;
        List<WriteRow> found = Collections.unmodifiableList(eligibleOf(
                sessionId, locationKey, observedVersion, reader));
        eligible.put(key, found);
        return found;
    }

    /** session|location|version|reader -> {@link #eligibleWrites}: the
     *  closure asks every demanded read again each time a demand grows,
     *  and once per walk of its group. */
    private final Map<String, List<WriteRow>> eligible =
            new ConcurrentHashMap<String, List<WriteRow>>();

    private List<WriteRow> eligibleOf(String sessionId, String locationKey,
                                      long observedVersion,
                                      OccurrenceAddress reader) {
        List<WriteRow> writes = writesOf(sessionId, locationKey);
        List<WriteRow> eligible = new ArrayList<WriteRow>();
        for (WriteRow write : writes) {
            if (arms.eligible(reader, sessionId, locationKey, writes,
                    observedVersion, write)) {
                eligible.add(write);
            }
        }
        return eligible;
    }

    /**
     * The states of the container one reference store delivered that a
     * read of the reference could have seen through it
     * ({@link SmtLowering#statesOf}: from the store's own referent on, the
     * one live at the read and every later one an HB-concurrent writer
     * made): the states a query through the read may be answered from.
     * ONE implementation, used by the closure ({@link ClosurePlanner}) as
     * COMPOSE answers from it; none for a store that states no referent.
     */
    public List<WriteRow> referentStates(WriteRow store, ReadRow read) {
        if (store.referentState() == null) {
            return Collections.<WriteRow>emptyList();
        }
        String session = store.sessionId();
        return SmtLowering.statesOf(writesOf(session, SmtLowering.locationKey(
                store.referentState().location())), store.referentState(),
                read, (reader, writer) -> arms.concurrent(reader, writer,
                        session));
    }

    /** Whether a decision is a FAULT decision: its term REACHES a fault
     *  marker the same session minted (PIPELINE §7.2, {@link #termSymbols}),
     *  by category: a boolean configuration is a MARKER too, and no fault.
     */
    public boolean fault(String sessionId, DecisionRow decision) {
        if (!Arms.predicate(decision.term())) return false;
        for (String symbol : termSymbols(sessionId, decision.term())) {
            RootMintRow root = rootBySymbol(sessionId, symbol);
            if (root != null && root.category() == RootCategory.FAULT) {
                return true;
            }
        }
        return false;
    }

    /**
     * The recorded symbols one published term REACHES: every symbol it names
     * itself, and those of each expression it references ({@code EXPR.*},
     * {@link #expressionSymbols}).  Asked of the expressions' shared DAG,
     * never of the term's lowered text, which unfolds every shared subterm
     * at each use (hdfs-17960's wave planner ran out of heap rendering
     * decisions only to learn whether they reach a fault marker).
     */
    public Set<String> termSymbols(String sessionId, String term) {
        Set<String> reached = new LinkedHashSet<String>();
        if (term == null || term.isEmpty()) return reached;
        for (String name : SmtNames.names(term)) {
            if (symbolKind(sessionId, name) != SymbolKind.UNKNOWN) {
                reached.add(name);
            }
        }
        java.util.regex.Matcher refs = EXPRESSION_REF.matcher(term);
        while (refs.find()) {
            reached.addAll(expressionSymbols(sessionId, refs.group()));
        }
        return reached;
    }

    /**
     * The recorded symbols one expression rests on, kept per session: its
     * symbol leaves, over its shared nodes (each once, {@link
     * ExpressionWalk}), and through each joinable read to the value its
     * version holds, as the lowering's join reads it ({@link
     * SmtLowering.SessionJoin#writeExpression}).  A read whose version holds
     * a container rests on that state's read rows, which the container's
     * value never names (the v_C rule, PIPELINE §7.2); a read no write
     * answers stands as the symbol it was minted.
     */
    public Set<String> expressionSymbols(String sessionId,
                                         String expressionRef) {
        Derived of = bySession.get(sessionId);
        // A session this corpus lacks, or no ref, states no expression.
        if (of == null || expressionRef == null) {
            return new LinkedHashSet<String>();
        }
        Set<String> held = of.symbolsByExpression.get(expressionRef);
        if (held != null) return held;
        Set<String> symbols = new LinkedHashSet<String>();
        SmtLowering.SessionJoin join = join(sessionId);
        Deque<JsonElement> roots = new ArrayDeque<JsonElement>();
        // A ref the session states no expression for (a value the VM kept
        // concrete) rests on no symbol; the row's gate names a dangling ref.
        JsonElement start = expression(sessionId, expressionRef);
        if (start != null) roots.add(start);
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        while (!roots.isEmpty()) {
            JsonElement root = roots.poll();
            for (ExpressionWalk walk = ExpressionWalk.of(root, walked);
                 walk.hasNext(); ) {
                JsonObject node = walk.next();
                String type = VmExpressionIr.typeOf(node);
                if (VmExpressionIr.SYMBOL_TYPE.equals(type)) {
                    String raw = JsonFields.optionalString(node, "_exp");
                    if (!raw.isEmpty()
                            && !VmExpressionIr.builtinSymbol(raw)) {
                        symbols.add(raw);
                    }
                }
                if (!VmRows.GUARDED_READ_TYPE.equals(type)
                        || !VmRows.joinable(node)) {
                    continue;
                }
                long version = VmRows.recordedVersion(node);
                JsonElement location = node.get("location");
                if (version < 0L || location == null
                        || !location.isJsonObject()) {
                    continue;
                }
                String at = SmtLowering.locationKey(
                        location.getAsJsonObject());
                JsonElement written = join.writeExpression(at, version);
                if (written == null) {
                    symbols.addAll(join.mintedReadSymbols(version));
                    continue;
                }
                if ("ContainerRelation".equals(
                        VmExpressionIr.typeOf(written))) {
                    symbols.addAll(join.readSymbols(at, version));
                }
                roots.add(written);
            }
        }
        of.symbolsByExpression.put(expressionRef, symbols);
        return symbols;
    }

    /** The sites of every fault decision any session took at one occurrence. */
    public Set<String> faultSites(OccurrenceAddress occurrence) {
        Set<String> sites = new LinkedHashSet<String>();
        for (RecordedPath path : pathsOf(occurrence)) {
            for (DecisionRow decision : path.decisions) {
                if (fault(path.sessionId, decision)) {
                    sites.add(decision.siteId());
                }
            }
        }
        return sites;
    }

    // ---- Arms.Rows ----

    @Override
    public JsonObject expression(String sessionId, String expressionRef) {
        SessionReader session = sessionById.get(sessionId);
        return session == null || expressionRef == null ? null
                : session.expressions().expression(expressionRef);
    }

    public ExpressionTable expressions(String sessionId) {
        SessionReader session = sessionById.get(sessionId);
        return session == null ? null : session.expressions();
    }

    /** What {@code key} rests on in one session, computed once. */
    public Set<String> leaves(String sessionId, String key,
                              Supplier<Set<String>> compute) {
        Derived of = bySession.get(sessionId);
        if (of == null) return compute.get();
        Set<String> found = of.leaves.get(key);
        if (found == null) {
            found = compute.get();
            of.leaves.put(key, found);
        }
        return found;
    }

    /** One shared-state read a published expression states, and the version the
     *  producer had in hand. */
    public static final class StateRead {
        private final String locationKey;
        private final long readEventId;
        private final WriteRow write;

        private StateRead(String locationKey, long readEventId,
                          WriteRow write) {
            this.locationKey = locationKey;
            this.readEventId = readEventId;
            this.write = write;
        }

        public String locationKey() {
            return locationKey;
        }

        public long readEventId() {
            return readEventId;
        }

        /** The latest write of the location at or before the read. */
        public WriteRow write() {
            return write;
        }
    }

    /** The shared state one published expression rests on: for each read node
     *  ({@code location} + {@code readEventId}), the latest write at or before
     *  the read. ONE implementation, shared by the composer ({@code
     *  compose.RestsOn#seedWrites}) and the closure (PIPELINE §7.2).
     *  Locations the session never wrote are skipped (no version to guess). */
    public List<StateRead> expressionStateReads(String sessionId,
                                                String expressionRef) {
        Derived of = bySession.get(sessionId);
        if (expressionRef == null) return Collections.emptyList();
        List<StateRead> held = of == null ? null
                : of.stateReads.get(expressionRef);
        if (held != null) return held;
        List<StateRead> found = stateReadsOf(sessionId, expressionRef);
        if (of != null) of.stateReads.put(expressionRef, found);
        return found;
    }

    private List<StateRead> stateReadsOf(String sessionId,
                                         String expressionRef) {
        List<StateRead> found = new ArrayList<StateRead>();
        JsonObject expression = expression(sessionId, expressionRef);
        if (expression == null) return Collections.unmodifiableList(found);
        Map<String, Long> read = new LinkedHashMap<String, Long>();
        readNodes(expression, read, ExpressionWalk.identitySet());
        for (Map.Entry<String, Long> each : read.entrySet()) {
            WriteRow latest = null;
            for (WriteRow write : writesOf(sessionId, each.getKey())) {
                if (write.version() > each.getValue().longValue()) continue;
                if (latest == null || latest.version() < write.version()) {
                    latest = write;
                }
            }
            if (latest == null) continue;
            found.add(new StateRead(each.getKey(),
                    each.getValue().longValue(), latest));
        }
        return Collections.unmodifiableList(found);
    }

    /** The locations a term's expressions read, by their structure: every
     *  {@code EXPR} reference the term text names, expanded.  A lowering that
     *  joins a scalar read to the value its version holds no longer names
     *  the read, and what a value rests on is the closure's question. */
    public Set<String> readLocations(String sessionId, String term) {
        String key = term == null ? "" : term;
        Derived of = bySession.get(sessionId);
        Set<String> held = of == null ? null : of.readLocations.get(key);
        if (held != null) return held;
        Set<String> found = readLocationsOf(sessionId, key);
        if (of != null) of.readLocations.put(key, found);
        return found;
    }

    private Set<String> readLocationsOf(String sessionId, String term) {
        Map<String, Long> read = new LinkedHashMap<String, Long>();
        java.util.regex.Matcher refs = EXPRESSION_REF.matcher(
                term == null ? "" : term);
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        while (refs.find()) {
            readNodes(expression(sessionId, refs.group()), read, walked);
        }
        return Collections.unmodifiableSet(read.keySet());
    }

    /** The read events a term's expressions name, by their structure
     *  (every {@code readEventId} under its {@code EXPR} references): what
     *  a predicate read, wherever it stands in the event order. */
    public Set<Long> readEvents(String sessionId, String term) {
        String key = term == null ? "" : term;
        Derived of = bySession.get(sessionId);
        Set<Long> held = of == null ? null : of.readEvents.get(key);
        if (held != null) return held;
        Set<Long> found = readEventsOf(sessionId, key);
        if (of != null) of.readEvents.put(key, found);
        return found;
    }

    private Set<Long> readEventsOf(String sessionId, String term) {
        Set<Long> events = new LinkedHashSet<Long>();
        java.util.regex.Matcher refs = EXPRESSION_REF.matcher(
                term == null ? "" : term);
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        while (refs.find()) {
            for (ExpressionWalk walk = ExpressionWalk.of(
                    expression(sessionId, refs.group()), walked);
                 walk.hasNext(); ) {
                JsonObject node = walk.next();
                JsonElement at = node.get("readEventId");
                if (node.get("location") != null && at != null
                        && at.isJsonPrimitive()) {
                    events.add(Long.valueOf(at.getAsLong()));
                }
            }
        }
        return Collections.unmodifiableSet(events);
    }

    private static final java.util.regex.Pattern EXPRESSION_REF =
            java.util.regex.Pattern.compile("EXPR\\.[0-9a-f]+");

    /** Location key -> the latest event id one expression read it at (any node
     *  with location + readEventId), each node once ({@link ExpressionWalk};
     *  capped at depth 64, the walk dropped the reads below it). */
    private static void readNodes(JsonElement expression,
                                  Map<String, Long> into,
                                  Set<JsonElement> walked) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression, walked);
             walk.hasNext(); ) {
            JsonObject node = walk.next();
            JsonElement location = node.get("location");
            JsonElement at = node.get("readEventId");
            if (location == null || !location.isJsonObject() || at == null
                    || !at.isJsonPrimitive()) {
                continue;
            }
            String key = SmtLowering.locationKey(location.getAsJsonObject());
            long event = at.getAsLong();
            Long held = into.get(key);
            if (held == null || held.longValue() < event) {
                into.put(key, Long.valueOf(event));
            }
        }
    }

    public Map<String, Interaction> interactions() {
        return Collections.unmodifiableMap(interactions);
    }

    public Map<String, Sort> declaredSymbols() {
        return Collections.unmodifiableMap(declaredSymbols);
    }

    /** Root symbols naming more than one root: a name collision that makes
     *  paths reading both unsatisfiable; the runtime's to fix, the
     *  composition's to refuse. */
    public Map<String, Set<String>> collidingRootSymbols() {
        Map<String, Set<String>> collisions =
                new LinkedHashMap<String, Set<String>>();
        for (Map.Entry<String, Set<String>> entry
                : rootIdsBySymbol.entrySet()) {
            if (entry.getValue().size() > 1) {
                collisions.put(entry.getKey(), entry.getValue());
            }
        }
        return collisions;
    }

    @Override
    public List<AttachRow> attachesOf(Interaction interaction) {
        return attachesByInteraction.getOrDefault(interaction.id(),
                Collections.<AttachRow>emptyList());
    }

    /** Every export any session recorded at one producer endpoint. */
    @Override
    public List<ExportRow> exportsOf(Endpoint producer) {
        if (producer == null) return Collections.emptyList();
        return exports.getOrDefault(producer.id(),
                Collections.<ExportRow>emptyList());
    }

    @Override
    public List<AttachRow> ownAttachesOf(String sessionId,
                                         Interaction interaction) {
        return ownAttaches.getOrDefault(sessionId + "|" + interaction.id(),
                Collections.<AttachRow>emptyList());
    }

    @Override
    public List<ExportRow> ownExportsOf(String sessionId, Endpoint producer) {
        if (producer == null) return Collections.emptyList();
        return ownExports.getOrDefault(sessionId + "|" + producer.id(),
                Collections.<ExportRow>emptyList());
    }

    @Override
    public List<WriteRow> writesOf(String sessionId, String locationKey) {
        return writesByLocation.getOrDefault(sessionId + "|" + locationKey,
                Collections.<WriteRow>emptyList());
    }

    @Override
    public List<ReadRow> readsOf(String sessionId, String locationKey) {
        return join(sessionId).reads(locationKey);
    }

    /** One write per (site, java type) that wrote a location, in any session,
     *  first seen first: what writes it, not how often. */
    public Collection<WriteRow> writeSitesOf(String locationKey) {
        Map<String, WriteRow> sites = writeSitesByLocation.get(locationKey);
        return sites == null ? Collections.<WriteRow>emptyList()
                : Collections.unmodifiableCollection(sites.values());
    }

    @Override
    public String pathIdOf(String sessionId, OccurrenceAddress occurrence) {
        return pathId(sessionId, occurrence);
    }

    @Override
    public RootMintRow root(String rootId, String sessionId) {
        return rootOf(sessionId, rootId);
    }

    /**
     * {@link Arms.Rows#varied}: more than one value among what every
     * session ran the root at ({@link #rootValue}), minted or read
     * concretely.  Once per root: this and {@link #roots} are asked per arm
     * and per root, and a corpus does not change once read -- rebuilding
     * them per ask made COMPOSE quadratic in the sessions (hdfs-17899-bug2,
     * 800 sessions).
     */
    @Override
    public boolean varied(String rootId) {
        return varied.computeIfAbsent(rootId, id -> {
            Set<String> values = new LinkedHashSet<String>();
            for (SessionReader session : sessions) {
                String value = rootValue(session.sessionId(), id);
                if (!value.isEmpty()) values.add(value);
            }
            return values.size() > 1;
        });
    }

    /**
     * {@link Arms.Rows#ranRoot}: the session's own mint, else the mint --
     * the seed's first, as {@code Composer#seedRow} -- whose occurrence this
     * session read the root at and states a reading of, unless the root is
     * {@link #derived}.
     */
    @Override
    public RootMintRow ranRoot(String rootId, String sessionId) {
        RootMintRow own = rootOf(sessionId, rootId);
        return own != null ? own : readAt(sessionId, rootId);
    }

    /**
     * Whether a session found this root's source carrying another input's
     * expression where it read it ({@code SessionManifest#derivedRoots}): a
     * value computed from a clock's reading, say, which every run reads
     * anew, so no session's reading of it is a value its rows hold at.
     */
    public boolean derived(String rootId) {
        return derived.computeIfAbsent(rootId, id -> {
            for (SessionReader session : sessions) {
                if (session.manifest() != null
                        && session.manifest().derivedRoots().contains(id)) {
                    return true;
                }
            }
            return false;
        });
    }

    /** The mint whose occurrence this session states a reading of the root
     *  at, or null. */
    private RootMintRow readAt(String sessionId, String rootId) {
        Map<String, String> readings = concreteReadings(sessionId, rootId);
        Map<String, RootMintRow> minted = rootsById.get(rootId);
        if (readings.isEmpty() || minted == null || derived(rootId)) {
            return null;
        }
        List<RootMintRow> order = new ArrayList<RootMintRow>();
        RootMintRow seed = minted.get(seedSessionId());
        if (seed != null) order.add(seed);
        order.addAll(minted.values());
        for (RootMintRow mint : order) {
            if (mint.occurrence() != null
                    && readings.containsKey(mint.occurrence().render())) {
                return mint;
            }
        }
        return null;
    }

    /** Rendered occurrence -> what this session read the root at there
     *  concretely ({@code SessionManifest#concreteReadings}). */
    private Map<String, String> concreteReadings(String sessionId,
                                                 String rootId) {
        SessionReader session = sessionById.get(sessionId);
        Map<String, String> readings = session == null
                || session.manifest() == null ? null
                : session.manifest().concreteReadings().get(rootId);
        return readings == null ? Collections.<String, String>emptyMap()
                : readings;
    }

    @Override
    public Map<String, List<RootMintRow>> roots() {
        if (roots == null) {
            Map<String, List<RootMintRow>> byRoot =
                    new LinkedHashMap<String, List<RootMintRow>>();
            for (Map.Entry<String, Map<String, RootMintRow>> entry
                    : rootsById.entrySet()) {
                // A forced world's mint is no reading of a world any run
                // takes (Composer places clocks from these).
                List<RootMintRow> rows = new ArrayList<RootMintRow>();
                for (RootMintRow row : entry.getValue().values()) {
                    if (row.seq() < forcedFrom(row.sessionId())) rows.add(row);
                }
                if (!rows.isEmpty()) {
                    byRoot.put(entry.getKey(),
                            Collections.unmodifiableList(rows));
                }
            }
            roots = Collections.unmodifiableMap(byRoot);
        }
        return roots;
    }

    @Override
    public AttachRow attachOfSymbol(String symbol, String sessionId) {
        return attach(sessionId, symbol);
    }

    @Override
    public OccurrenceAddress occurrenceOf(String endpointId) {
        Endpoint endpoint = endpointById.get(endpointId);
        return endpoint == null ? null : endpoint.occurrence();
    }

    @Override
    public ActivationRow activationOf(String sessionId,
                                      String occurrenceId) {
        return activationByOccurrence.get(sessionId + "|" + occurrenceId);
    }

    public Arms arms() {
        return arms;
    }

    public WriteRow writeOf(String sessionId, LocationId location,
                            long version) {
        return writeOf(sessionId, SmtLowering.locationKey(location), version);
    }

    public WriteRow writeOf(String sessionId, String locationKey,
                            long version) {
        return version < 0 ? null : writeByVersion.get(
                versionKey(sessionId, locationKey, version));
    }

    /** Every occurrence of the node that writes or reads one location. */
    public Set<String> touching(OccurrenceAddress occurrence,
                                LocationId location) {
        Set<String> found = locationTouches.get(touchKey(occurrence,
                location));
        return found == null ? Collections.<String>emptySet() : found;
    }

    public AttachRow attach(String sessionId, String symbol) {
        return attachBySymbol.get(sessionId + "|" + symbol);
    }

    /** Whether some session's attach minted this symbol: a handoff
     *  variable, which only that session's family binds. */
    public boolean handoffSymbol(String symbol) {
        return handoffSymbols.contains(symbol);
    }

    /** The root one session minted under one symbol, or null. */
    public RootMintRow rootBySymbol(String sessionId, String symbol) {
        return rootBySymbol.get(sessionId + "|" + symbol);
    }

    public ReadRow read(String sessionId, String symbol) {
        return readBySymbol.get(sessionId + "|" + symbol);
    }

    public SymbolKind symbolKind(String sessionId, String symbol) {
        String key = sessionId + "|" + symbol;
        if (rootBySymbol.containsKey(key)) return SymbolKind.ROOT;
        if (attachBySymbol.containsKey(key)) return SymbolKind.HANDOFF;
        if (readBySymbol.containsKey(key)) return SymbolKind.READ;
        return SymbolKind.UNKNOWN;
    }

    /** The value one session RAN one root at, or "": ONE notion for valuations,
     *  arm guards and model comparison. A replay that PLANTED the root states
     *  no recorded value (a counterfactual is not a recording), so the ask
     *  ({@code rootAssignments}) wins; otherwise the mint's {@code
     *  recordedValue}; where it minted none, its concrete reading at the
     *  occurrence of the mint {@link #ranRoot} names. */
    @Override
    public String rootValue(String sessionId, String rootId) {
        String wave = world(sessionId).rootAssignments.get(rootId);
        if (wave != null && !wave.isEmpty()) return wave;
        if (rootOf(sessionId, rootId) != null) {
            return rootReading(sessionId, rootId);
        }
        RootMintRow read = readAt(sessionId, rootId);
        return read == null ? "" : concreteReadings(sessionId, rootId)
                .get(read.occurrence().render());
    }

    /** The mint's own reading, or "" (unlike {@link #rootValue}, ignores the
     *  ask). */
    public String rootReading(String sessionId, String rootId) {
        RootMintRow row = rootOf(sessionId, rootId);
        return row == null || row.recordedValue() == null
                ? "" : row.recordedValue();
    }

    /** What one session minted for one root, or null when it minted none. */
    public RootMintRow rootOf(String sessionId, String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        return bySession == null ? null : bySession.get(sessionId);
    }

    /** Any mint row for one root, for the facts every session agrees on. */
    public RootMintRow anyRoot(String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        return bySession == null || bySession.isEmpty() ? null
                : bySession.values().iterator().next();
    }

    /** What the CASE declares for one root, or null when it declares none. */
    public RootDomain declaredDomain(String rootId) {
        return declaredDomains.get(rootId);
    }

    /**
     * THE DOMAIN OF ONE ROOT, the one reader the flip queries and the
     * composition share: the case file is the authority ({@code +k}/{@code
     * -k} are relative to the recorded reading); else the mint's, an
     * integral configuration's widened by every literal a recorded decision
     * of this corpus compares its symbol with ({@link #comparedLiterals})
     * and kept within what its own validation admits ({@link
     * RootDomain#resolved}).  No domain means pinned here and in the
     * composition.  A CLOCK's is its instant's ({@link #domainOf(RootMintRow,
     * String)}).
     */
    public RootDomain domainOf(RootMintRow root) {
        return RootDomain.resolved(root, declaredDomains,
                comparedLiterals(root.symbol()));
    }

    /** A CLOCK cell's domain about one reading of it (the composition's
     *  timeline): the case's declaration about that reading, else the
     *  mint's. */
    public RootDomain domainOf(RootMintRow root, String reading) {
        return RootDomain.resolved(root, reading, declaredDomains);
    }

    /** symbol -> the literals recorded decisions compare it with. */
    private final Map<String, Set<java.math.BigInteger>> compared =
            new HashMap<String, Set<java.math.BigInteger>>();

    /**
     * Every integral literal a recorded decision of this corpus compares
     * {@code symbol} with directly ({@code (op c symbol)} or {@code (op
     * symbol c)}, {@code op} an order or an equality), its term lowered by
     * the one lowering; once per symbol.
     */
    Set<java.math.BigInteger> comparedLiterals(String symbol) {
        Set<java.math.BigInteger> known = compared.get(symbol);
        if (known != null) return known;
        Set<java.math.BigInteger> literals =
                new java.util.TreeSet<java.math.BigInteger>();
        String name = java.util.regex.Pattern.quote(symbol);
        String literal = "(-?[0-9]+|\\(-\\s+[0-9]+\\))";
        java.util.regex.Pattern atom = java.util.regex.Pattern.compile(
                "\\((?:<=|>=|<|>|=)\\s+(?:" + literal + "\\s+\\|?" + name
                        + "\\|?|\\|?" + name + "\\|?\\s+" + literal + ")\\)");
        for (Map.Entry<String, List<DecisionRow>> path
                : decisions.entrySet()) {
            String sessionId = path.getKey().substring(0,
                    path.getKey().indexOf('|'));
            for (DecisionRow decision : path.getValue()) {
                if (!Arms.predicate(decision.term()) || !termSymbols(
                        sessionId, decision.term()).contains(symbol)) {
                    continue;
                }
                java.util.regex.Matcher found = atom.matcher(
                        FlipQuery.statedTerm(this, sessionId,
                                decision.term()));
                while (found.find()) {
                    String spelled = found.group(1) != null
                            ? found.group(1) : found.group(2);
                    literals.add(new java.math.BigInteger(spelled
                            .replaceAll("[()\\s]", "")));
                }
            }
        }
        compared.put(symbol, literals);
        return literals;
    }
}
