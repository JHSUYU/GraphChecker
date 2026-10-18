package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ByIdentity;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.FrozenSet;
import edu.uva.liftlab.graphchecker.contract.Held;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.RowHold;
import edu.uva.liftlab.graphchecker.contract.RunSpellings;
import edu.uva.liftlab.graphchecker.contract.Task;
import com.google.common.collect.Interner;
import com.google.common.collect.Interners;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.JavaSmtSorts;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WorldRefutation;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractSet;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** One iteration's sessions, indexed: the ONE corpus view both stages read.
 *  Identity is the contract's: an interaction by both endpoints, a location by
 *  {@link LocationId}, a symbol by its minting session (raw symbols, versions
 *  and expression refs are session-local). One path id spelling: {@link
 *  #pathId}.  COMPOSE's holds only some of its sessions' reads and writes
 *  at a time, every answer the one a corpus holding them all gives ({@link
 *  #holding}). */
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
    /** One lowering per session, made as first asked ({@link #lowering});
     *  concurrent, as a session's keys renew its own ({@link #keysDone}). */
    private final Map<String, SmtLowering> loweringById =
            new ConcurrentHashMap<String, SmtLowering>();
    /** What holds the sessions' reads and writes ({@link #holding}); null:
     *  every one held as read. */
    private final RowHold hold;
    /** session id -> what this corpus derives from that session's rows
     *  alone ({@link Derived}). */
    private final Map<String, Derived> bySession =
            new LinkedHashMap<String, Derived>();
    /** occurrence id -> the activations of it, across sessions. */
    private final Map<String, List<ActivationRow>> activations =
            new LinkedHashMap<String, List<ActivationRow>>();
    /** producer endpoint id -> every export recorded at it. */
    private final Map<String, List<ExportRow>> exports =
            new LinkedHashMap<String, List<ExportRow>>();
    /** Every symbol some session's attach minted. */
    private final Set<String> handoffSymbols = new LinkedHashSet<String>();
    /** occurrence id -> session id -> its attaches, targets. */
    private final ByOccurrence<AttachRow> attachesOn =
            new ByOccurrence<AttachRow>();
    private final ByOccurrence<TargetRow> targetsOn =
            new ByOccurrence<TargetRow>();
    /** occurrence id -> the sessions, forced ones aside, that read / wrote
     *  at it, in the order they were read: their rows there are each
     *  session's ({@link StateRows#readsOn}). */
    private final Map<String, Set<String>> readersOn =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> writersOn =
            new LinkedHashMap<String, Set<String>>();
    /** occurrence id -> the locations it reads / writes, in any session. */
    private final Map<String, Set<String>> readLocations =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, Set<String>> writtenLocations =
            new LinkedHashMap<String, Set<String>>();
    /** locationKey -> (site, java type) -> its first write, in any
     *  session: the pair as its two strings, never spelled into one. */
    private final Map<String, Map<List<String>, WriteRow>>
            writeSitesByLocation =
            new LinkedHashMap<String, Map<List<String>, WriteRow>>();
    /** interaction id -> the attaches whose own pairing names it. */
    private final Map<String, List<AttachRow>> attachesByInteraction =
            new LinkedHashMap<String, List<AttachRow>>();
    /** interaction id -> the interaction itself, for every pairing stated. */
    private final Map<String, Interaction> interactions =
            new LinkedHashMap<String, Interaction>();
    /** Every symbol the runtime declared, at the sort it minted it at. */
    private final Map<String, Sort> declaredSymbols =
            new LinkedHashMap<String, Sort>();
    /** root id -> whether the corpus ran it at more than one value;
     *  concurrent, as every memo of a corpus asked by keys computed side
     *  by side ({@code ObligationFactory#dependences}). */
    private final Map<String, Boolean> varied =
            new ConcurrentHashMap<String, Boolean>();
    /** {@link #derived}, once per root. */
    private final Map<String, Boolean> derived =
            new ConcurrentHashMap<String, Boolean>();
    /** root id -> every session's mint of it, built on first ask. */
    private Map<String, List<RootMintRow>> roots;
    /** Root symbol -> every root id declared under it. */
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();
    /** endpoint id -> its occurrence, so an anchor's producer can be found:
     *  its occurrence alone, the endpoint (its execution index) held by the
     *  rows a hold may let go of. */
    private final Map<String, OccurrenceAddress> occurrenceByEndpoint =
            new HashMap<String, OccurrenceAddress>();
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
    /** Session id -> obligation id -> the verdict the worker that landed
     *  the session states in its own file. */
    private final Map<String, Map<String, ObligationResult>> waveVerdicts =
            new LinkedHashMap<String, Map<String, ObligationResult>>();
    /** Session id -> the round directory of the worker that landed it, as
     *  the read found the workers: a round reads it after its corpus read,
     *  while GROW may swap a worker's files (ExploreMain#wave). */
    private final Map<String, Path> landedIn =
            new LinkedHashMap<String, Path>();
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
    /** Producer endpoint id -> the stances of the turns standing on it, its
     *  handlers: what it started, no doors of it ({@link #doorsOf}). */
    private final Map<String, Set<String>> handlerStances =
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
     * WHAT ONE SESSION'S ROWS ALONE GIVE: what its reads and writes give by
     * key ({@link StateRows}), the schedule facts the corpus indexes ({@link
     * #indexSchedule}), and what a walk of its expressions found --
     * functions of those rows only, so a read of the
     * same iteration takes them with the session it keeps ({@link
     * #read(Path, Path, Corpus)}): a landed session's rows never change.
     * Every index across sessions, and every lowering, is built anew.
     */
    private static final class Derived {
        final SessionReader session;
        /** What its reads and writes give, by key; null while its hold has
         *  let them go ({@link #state}). */
        volatile StateRows state;
        /** Its schedule, as the corpus indexes it: {@link Fact}s in
         *  order. */
        final List<Fact> schedule;
        /** expression ref -> {@link #expressionSymbols}, each a {@link
         *  FrozenSet}: 7-10 M symbols in SGF8-adhoc-05 round 5's planner. */
        final Map<String, Set<String>> symbolsByExpression =
                new ConcurrentHashMap<String, Set<String>>();
        /** {@link #leaves}: the variables one term or read rests on; a
         *  flip's dependence asks every earlier condition of its path
         *  again.  Each a {@link HeldLeaves}. */
        final Map<String, Set<String>> leaves =
                new ConcurrentHashMap<String, Set<String>>();
        /** term -> {@link #readLocations}, {@link #readEvents}; expression
         *  ref -> {@link #expressionStateReads}. */
        final Map<String, Set<String>> readLocations =
                new ConcurrentHashMap<String, Set<String>>();
        final Map<String, Set<Long>> readEvents =
                new ConcurrentHashMap<String, Set<Long>>();
        /** The seqs more than one of its read rows stand at (a store read
         *  and its view's): {@link #readLeaves}' key holds one. */
        final Set<Long> sharedSeqs;
        /** "read seq" of a shared seq -> the row whose leaves it holds. */
        final Map<String, ReadRow> sharedBy =
                new ConcurrentHashMap<String, ReadRow>();
        /*
         * ITS ROWS BY WHAT THEY NAME, in this session alone: keyed by the
         * name, never by a key spelled of the session and the name (a
         * corpus of such keys held a string per row, 1.3 GB of
         * SGF8-adhoc-05 round 5's planner), built once with the session.
         */
        /** occurrence id -> its first activation here. */
        final Map<String, ActivationRow> activationByOccurrence =
                new HashMap<String, ActivationRow>();
        /** occurrence id -> its decisions here, in recorded order; in the
         *  order first decided ({@link #deciding}). */
        final Map<String, List<DecisionRow>> decisions =
                new LinkedHashMap<String, List<DecisionRow>>();
        /** symbol -> the attach that minted it here. */
        final Map<String, AttachRow> attachBySymbol =
                new HashMap<String, AttachRow>();
        /** symbol -> the root minted under it here, in mint order
         *  ({@link #configurationLiterals}). */
        final Map<String, RootMintRow> rootBySymbol =
                new LinkedHashMap<String, RootMintRow>();
        /** A forced session's attaches from before its forced world, by
         *  interaction id: its own path's messages alone; and its exports,
         *  by producer endpoint id.  Empty for any other session. */
        final Map<String, List<AttachRow>> ownAttaches =
                new HashMap<String, List<AttachRow>>();
        final Map<String, List<ExportRow>> ownExports =
                new HashMap<String, List<ExportRow>>();

        /** {@code state}: its {@link StateRows} built now, as a corpus that
         *  holds every session's rows reads them; else as first asked. */
        Derived(SessionReader session, boolean state) {
            this.session = session;
            this.state = state ? new StateRows(session) : null;
            this.schedule = facts(session);
            for (ActivationRow row : session.activations()) {
                activationByOccurrence.putIfAbsent(row.occurrence().id(),
                        row);
            }
            for (DecisionRow row : session.decisions()) {
                add(decisions, row.occurrence().id(), row);
            }
            Held.trimmed(decisions);
            for (AttachRow row : session.attaches()) {
                attachBySymbol.put(row.symbol(), row);
            }
            for (RootMintRow row : session.roots()) {
                rootBySymbol.put(row.symbol(), row);
            }
            if (session.forced()) {
                // Its forced world's first event: what is before it is its
                // own path's.
                long world = Long.MAX_VALUE;
                for (TargetRow row : session.targets()) {
                    if (row.isForced()) world = Math.min(world, row.seq());
                }
                for (ExportRow row : session.exports()) {
                    if (row.seq() < world) {
                        add(ownExports, row.endpoint().id(), row);
                    }
                }
                for (AttachRow row : session.attaches()) {
                    if (row.interaction() != null && row.seq() < world) {
                        add(ownAttaches, row.interaction().id(), row);
                    }
                }
            }
            Set<Long> seen = new HashSet<Long>();
            Set<Long> shared = new HashSet<Long>();
            for (ReadRow read : session.reads()) {
                if (read != null && !seen.add(read.seq())) {
                    shared.add(read.seq());
                }
            }
            this.sharedSeqs = shared;
        }
    }

    /**
     * WHAT ONE SESSION'S READS AND WRITES GIVE, by key -- its state join
     * (its writes by location and version among it), its reads by symbol,
     * its rows by occurrence, and the answers that hold its rows -- built
     * from them
     * alone, so a hold that let them go ({@link RowHold}) has these built
     * again as they are read again.
     */
    private static final class StateRows {
        /** Its state join, which also answers its writes by location and
         *  version ({@link SmtLowering#joinOf}). */
        final SmtLowering.SessionJoin join;
        final Map<String, ReadRow> readBySymbol =
                new HashMap<String, ReadRow>();
        /** occurrence id -> its reads / writes there, in recorded order. */
        final Map<String, List<ReadRow>> readsOn =
                new HashMap<String, List<ReadRow>>();
        final Map<String, List<WriteRow>> writesOn =
                new HashMap<String, List<WriteRow>>();
        /** location|version|reader -> {@link #eligibleWrites}: the closure
         *  asks every demanded read again each time a demand grows, and once
         *  per walk of its group. */
        final Map<String, List<WriteRow>> eligible =
                new ConcurrentHashMap<String, List<WriteRow>>();
        /** expression ref -> {@link #expressionStateReads}. */
        final Map<String, List<StateRead>> stateReads =
                new ConcurrentHashMap<String, List<StateRead>>();

        /** A session this corpus lacks: no rows. */
        private StateRows() {
            this.join = SmtLowering.NO_JOIN;
        }

        StateRows(SessionReader session) {
            this.join = SmtLowering.joinOf(session);
            for (WriteRow row : session.writes()) {
                add(writesOn, row.endpoint().occurrence().id(), row);
            }
            for (ReadRow row : session.reads()) {
                if (!row.symbol().isEmpty()) {
                    readBySymbol.put(row.symbol(), row);
                }
                add(readsOn, row.endpoint().occurrence().id(), row);
            }
            Held.trimmed(readsOn);
            Held.trimmed(writesOn);
        }
    }

    private static final StateRows NO_STATE = new StateRows();

    /** What one session's reads and writes give, built again where its hold
     *  let them go; none for a session this corpus lacks. */
    private StateRows state(String sessionId) {
        Derived of = bySession.get(sessionId);
        if (of == null) return NO_STATE;
        StateRows held = of.state;
        if (held != null) {
            if (hold != null) hold.used(of.session);
            return held;
        }
        synchronized (of) {
            held = of.state;
            if (held == null) {
                held = new StateRows(of.session);
                of.state = held;
            }
        }
        return held;
    }

    /** One schedule fact of a session: where a message was taken in,
     *  sent from, sent by, or received by. */
    private static final class Fact {
        enum Kind { TAKEN_IN, SENDER_STANCE, SENDER, RECEIVER,
            RECEIVING_STANCE, HANDLER_STANCE }

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
        this.hold = null;
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
        List<SessionReader> every = new ArrayList<SessionReader>(real);
        every.addAll(forced);
        List<Derived> derived = derived(every, previous);
        for (int at = 0; at < every.size(); at++) {
            bySession.put(every.get(at).sessionId(), derived.get(at));
            index(derived.get(at), at >= real.size());
        }
        this.arms = new Arms(this);
    }

    /**
     * COMPOSE'S CORPUS (PIPELINE §8): every index built from every session's
     * rows, the sessions read {@link Parallel#READS} at a time -- the next
     * ones read while these are indexed -- and their reads and writes held
     * by {@code hold}, at most its bytes, read again as asked for, so the
     * corpus never holds them all.  The sessions are indexed in the
     * order {@link #Corpus(Path, List, Corpus)} indexes them (each read one
     * in read order, the forced ones after), and each answer is the one
     * that corpus gives.
     */
    private Corpus(Path iteration, List<SessionDir> dirs, long bytes)
            throws IOException {
        this.iteration = iteration;
        this.hold = new RowHold(bytes, this::released);
        List<SessionReader> real = new ArrayList<SessionReader>();
        List<Derived> forced = new ArrayList<Derived>();
        SessionReader.Pooled reader = new SessionReader.Pooled();
        List<Derived> read = derived(reader, dirs, 0);
        for (int from = 0; from < dirs.size(); from += Parallel.READS) {
            int next = from + Parallel.READS;
            List<List<Derived>> ahead = new ArrayList<List<Derived>>();
            Parallel.Beside reading = Parallel.beside("corpus-read",
                    () -> ahead.add(derived(reader, dirs, next)));
            try {
                for (Derived of : read) {
                    // As the corpus that holds every session reads them.
                    if (of.session.forced()) {
                        if (forcedTarget(of.session)) forced.add(of);
                        continue;
                    }
                    real.add(of.session);
                    indexHeld(of, false);
                }
            } finally {
                reading.await();
            }
            reading.join();
            read = ahead.get(0);
        }
        List<SessionReader> apart = new ArrayList<SessionReader>();
        for (Derived of : forced) {
            apart.add(of.session);
            indexHeld(of, true);
        }
        this.sessions = Collections.unmodifiableList(real);
        this.forcedSessions = Collections.unmodifiableList(apart);
        this.arms = new Arms(this);
    }

    /** The {@link Parallel#READS} sessions from {@code from} on, read side by
     *  side, each with what its rows alone give but its {@link StateRows},
     *  built as asked. */
    private static List<Derived> derived(SessionReader.Pooled reader,
                                         List<SessionDir> dirs, int from)
            throws IOException {
        if (from >= dirs.size()) return Collections.<Derived>emptyList();
        return Parallel.map(dirs.subList(from, Math.min(dirs.size(),
                from + Parallel.READS)), dir -> {
            SessionReader session = reader.read(dir);
            digestIds(session);
            return new Derived(session, false);
        }, Parallel.READS);
    }

    /** One session read, indexed, and taken into the hold. */
    private void indexHeld(Derived of, boolean apart) {
        bySession.put(of.session.sessionId(), of);
        index(of, apart);
        hold.take(of.session);
    }

    /**
     * COMPOSE's read of an iteration ({@link #Corpus(Path, List, long)}),
     * its sessions' reads and writes held to {@code bytes} of their text,
     * and its case-declared root domains.
     */
    public static Corpus holding(Path iteration, Path rootDomains, long bytes)
            throws IOException {
        Corpus corpus = new Corpus(iteration,
                SessionDir.sessionsIn(iteration), bytes);
        corpus.domains(rootDomains);
        corpus.indexWorlds(iteration);
        corpus.indexRecordedTicks(iteration);
        return corpus;
    }

    /** What was built of one session's rows its hold let go of goes with
     *  them ({@link RowHold}): built again as they are read again. */
    private void released(SessionReader session) {
        Derived of = bySession.get(session.sessionId());
        if (of != null && of.session == session) of.state = null;
        loweringById.remove(session.sessionId());
    }

    /** The text of the sessions' reads and writes it holds now, in decoded
     *  bytes ({@link #holding}); 0 for a corpus holding them all. */
    public long held() {
        return hold == null ? 0L : hold.holding();
    }

    /** The most of it it holds; 0 for a corpus holding them all. */
    public long holdable() {
        return hold == null ? 0L : hold.bytes();
    }

    /** How many sessions it let go of were read again, and their text in
     *  decoded bytes ({@link RowHold#readAgain}). */
    public long[] readAgain() {
        return hold == null ? new long[2] : hold.readAgain();
    }

    /** What {@code previous} derived from each session's rows alone, else
     *  derived anew -- each a function of its session's rows (its schedule
     *  read from its file), so a few sessions at a time ({@link
     *  Parallel#READS}), in the sessions' order -- and a new session's rows'
     *  ids digested there, each held by its row ({@code Endpoint#id}): the
     *  index keys by them (SGF8-adhoc-05 round 5 read whole: 45 % of its
     *  42 s on one core). */
    private static List<Derived> derived(List<SessionReader> sessions,
                                         Corpus previous) {
        try {
            return Parallel.map(sessions, session -> {
                Derived kept = previous == null ? null
                        : previous.bySession.get(session.sessionId());
                if (kept != null && kept.session == session) return kept;
                digestIds(session);
                return new Derived(session, true);
            }, Parallel.READS);
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
    }

    /** The ids of the endpoints and occurrences one session's rows name,
     *  digested once ({@link #derived}). */
    private static void digestIds(SessionReader session) {
        for (ActivationRow row : session.activations()) {
            row.occurrence().id();
            if (row.anchorProducer() != null) row.anchorProducer().id();
        }
        for (ExportRow row : session.exports()) row.endpoint().id();
        for (AttachRow row : session.attaches()) {
            row.endpoint().id();
            if (row.producer() != null) row.producer().id();
        }
        for (WriteRow row : session.writes()) row.endpoint().id();
        for (ReadRow row : session.reads()) row.endpoint().id();
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
        return read(iteration, rootDomains, null, null);
    }

    /**
     * The same read, of the sessions {@code named} names (null: every
     * session the iteration holds) -- an EXPLORE round's corpus, frozen as
     * its planner starts, while the campaign goes on landing sessions
     * (PIPELINE §7.9) -- the sessions {@code previous} (a read of the same
     * iteration, or null) holds and the read still names taken from it
     * unread ({@link SessionReader#readAll(Path, List, Collection)}), with
     * what was derived from each alone ({@link Derived}); every index across
     * sessions is built anew.  The rows are most of a read: hdfs-11741 i1,
     * 45 s for 175 sessions, every time one landed while a host's solver
     * served ({@code ObligationSolverMain#answerer}); hdfs-adhoc-07 EX1,
     * 140-172 s of a late round's ~900 s, every round its planner planned.
     */
    public static Corpus read(Path iteration, Path rootDomains,
                              Corpus previous, Collection<String> named)
            throws IOException {
        Corpus corpus = new Corpus(iteration, SessionReader.readAll(
                iteration, previous == null
                        ? Collections.<SessionReader>emptyList()
                        : previous.everySession(), named), previous);
        corpus.domains(rootDomains);
        corpus.indexWorlds(iteration);
        corpus.indexRecordedTicks(iteration);
        return corpus;
    }

    /** What the case declares each root may be. */
    private void domains(Path rootDomains) throws IOException {
        if (rootDomains != null && Files.isRegularFile(rootDomains)) {
            declaredDomains.putAll(RootDomain.declared(rootDomains));
        }
    }

    /** The recording's schedule, which run_engine sets beside the sessions. */
    public static final String RECORDED_SCHEDULE = "recorded_schedule.jsonl";

    /** node|role -> the last daemon tick the recording ran; null when the
     *  iteration states no recorded schedule. */
    private Map<String, Integer> recordedTicks;

    private void indexRecordedTicks(Path iteration) throws IOException {
        Path recorded = iteration.resolve(RECORDED_SCHEDULE);
        if (!Files.isRegularFile(recorded)) return;
        recordedTicks = new HashMap<String, Integer>();
        for (ScheduleEvent event : SessionReader.readSchedule(recorded)) {
            // A view's publication stands at its node's |VIEW stance, no
            // causal context and no tick (ScheduleEvent.Kind#PUBLISH).
            if (event.kind() == ScheduleEvent.Kind.PUBLISH) continue;
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
    public TickPast tickPastRecording(OccurrenceAddress occurrence) {
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
        return tick.windowIndex() <= last ? null
                : new TickPast(node + " " + tick.render(), last);
    }

    /** A daemon tick past the recording's last ({@link #tickPastRecording}),
     *  read as its words. */
    public static final class TickPast {
        /** The node and the tick, as a context renders it. */
        public final String tick;
        /** The last tick of that role on that node the recording ran: the
         *  bound the closure stops at. */
        public final int last;

        TickPast(String tick, int last) {
            this.tick = tick;
            this.last = last;
        }

        @Override
        public String toString() {
            return tick + ", the recording's last being #" + last;
        }
    }

    /**
     * A causal context as the branch rule compares it ({@link Branches},
     * {@link ContextShape}): each sender is the endpoint a row of the corpus
     * states, else the stance its SEND stood in.
     */
    public List<String> contextShape(CausalContext context) {
        return ContextShape.of(context, producer -> {
            OccurrenceAddress sender = occurrenceByEndpoint.get(producer);
            return sender == null ? senderStanceByEndpoint.get(producer)
                    : new ContextShape.Stance(sender.node().render(),
                            sender.context());
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
            landedIn.put(worker.sessionId(), worker.dir().getParent());
            for (ObligationResult result : worker.results()) {
                waveVerdicts.computeIfAbsent(worker.sessionId(),
                        key -> new LinkedHashMap<String, ObligationResult>())
                        .put(result.obligationId(), result);
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

    /** Each session of the workers' answers -> the round directory of the
     *  worker that landed it, as this corpus's read found them. */
    public Map<String, Path> landedIn() {
        return Collections.unmodifiableMap(landedIn);
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
     * of an arm's key ({@link ObligationFactory#dependence}).  The rule: the
     * key names what the flip query depends on at the task, the EFFECT, never
     * the cause (keying by upstream flips asks one question per flip
     * combination).
     *
     * <p>Covers the occurrence -- whether it ran, its distinct MESSAGE
     * (handoff site, producer) pairs ({@link #handoffs}; what it read of a
     * store is a read, named where the query states it: solr-adhoc-19 SC9,
     * which fields of which state.json versions the task read re-keyed 660
     * of one round's 3722 ids), and each handoff the query
     * STATES (a symbol of {@code stated}: the guard's term, then its kept
     * conditions') by what binds it there ({@link #handoffName}: its
     * producer's arms, or its pinned arrival), the guard's in the order it
     * names them, its kept conditions' as a set; and, where one of those
     * handoffs has a producer, the value its run ran each root the stated
     * terms reach at ({@link #rootName}; never a clock): {@code
     * FlipQuery#arm} pins a producer arm's guard roots, so a root the
     * question tests is then held at its world's value (with no handoff it
     * is free, and the world that took the other arm settles the flip) --
     * and each factor member
     * that FEEDS it ({@link #feeders}) and was delivered something or wrote
     * where the query reads: its MESSAGE handoffs (whole, not only those
     * the guard names: the arm consumes them after the flip -- hdfs-11741's
     * witness is dn1's expiry scan flipped in the world whose key
     * conversion delivered addKeys four keys instead of five, while the
     * guard rests on none of addKeys' writes), and its writes at {@code
     * locations}, every location a read the guard and its kept conditions
     * rest on reads ({@code Independence#locations}), each by what it wrote
     * as the guard reads it, canonical ({@link #written}).  A member flip
     * that writes another value there, a second writer of another class, or
     * a pinned value another read of the task observed, re-key, as does a
     * producer delivering the task another value the query states.  What a
     * member READ OF A STORE (a content port, {@link ContentPort}) is a
     * read, no delivery: the key names it wherever it reaches the query --
     * a write's term, a handoff the query states -- and a member with
     * neither a message handoff nor a write where the query reads is no
     * line (solr-adhoc-19 SC6: members that read cluster state and wrote
     * nothing the guard reads, present in some worlds only, 32 ids of one
     * arm).  Nor is a member that only wrote state the region reads
     * elsewhere: it is no conjunct of the query, and a world that changed
     * it is reached by nesting from the answer's session (PIPELINE §7.5), as
     * an inherited prefix is (solr-adhoc-21 RX4: state watchers and client
     * STATUS calls that ran in one replay only re-keyed half the re-asks).
     * Trap: never a member's writes elsewhere, never the region's own reads
     * or decisions (behaviour, not input), never delivered VALUES carried
     * symbolically (clock values differ every run).</p>
     *
     * <p>A function of the session alone, whatever the corpus has learned
     * since: the members as a set (the order the corpus lists the factor in
     * moves as sessions land).  Semantic counts only: a member is named by
     * its class -- node, region and context shape ({@link #contextShape}),
     * never its exact address, whose anchor hashes and invocation counts
     * every replay renumbers -- a member's writes are a set of (site, what it
     * wrote), and identical lines count once: a poll or a watch callback
     * that wrote the same value k or k' times, or under renumbered ids,
     * delivered one world (solr-adhoc-07/21 IB1).  A run's handle for an
     * object is numbered by where the key first meets it ({@link
     * #numbered}).  LIMITS: a member's write the recording states at no
     * write site (unwoven) re-keys no arm; nor does a member's store read
     * that reaches the query by no read or handoff it states (one that
     * changed only what the arm consumes after the flip: 11741's shape,
     * were addKeys' keys read from a store); the downstream of a schedule
     * variant -- a member that ran in one replay of a world only -- is not
     * asked again: schedules are not worlds.</p>
     */
    public String inputShape(String sessionId, OccurrenceAddress occurrence,
                             List<OccurrenceAddress> factor,
                             Set<String> locations, List<String> stated) {
        Set<String> members = new TreeSet<String>(BY_SHAPE);
        for (OccurrenceAddress member : factor) {
            if (member.equals(occurrence)) continue;
            Set<String> writes = writeSites(sessionId, member, occurrence,
                    locations);
            Set<String> messages = handoffs(sessionId, member, false);
            if (writes.isEmpty() && messages.isEmpty()) continue;
            members.add(classOf(member) + ':'
                    + (activation(sessionId, member) != null)
                    + messages + writes);
        }
        List<String> guard = new ArrayList<String>();
        Set<String> kept = new TreeSet<String>(BY_SHAPE);
        boolean pinned = false;
        for (int at = 0; at < stated.size(); at++) {
            for (String symbol : termSymbols(sessionId, stated.get(at))) {
                if (symbolKind(sessionId, symbol) != SymbolKind.HANDOFF) {
                    continue;
                }
                pinned |= attach(sessionId, symbol).producer() != null;
                String bound = tokenName(sessionId, "handoff|" + sessionId
                        + "|" + symbol, () -> handoffName(attach(sessionId,
                        symbol), new Naming()));
                if (at == 0) {
                    guard.add(bound);
                } else {
                    kept.add(bound);
                }
            }
        }
        StringBuilder text = new StringBuilder();
        text.append(occurrence.id()).append(':')
                .append(activation(sessionId, occurrence) != null)
                .append(handoffs(sessionId, occurrence, false)).append(guard)
                .append(kept).append(pinned ? rootValues(sessionId, stated)
                        : Collections.<String>emptySet());
        for (String member : members) text.append('\n').append(member);
        return ArtifactIO.digest(numbered(text.toString(),
                new LinkedHashMap<String, String>()), 16);
    }

    /**
     * THE RUN'S VALUATION WHERE A QUESTION HOLDS IT AGAINST OTHER RUNS', as
     * an arm's key names it: {@code FlipQuery#handoff} offers a handoff of
     * the task's OWN occurrence every run's arms of it, each pinned to its
     * run's valuation ({@code FlipQuery#arm}), so which of them the query
     * admits turns on what this run's own conditions hold those roots at
     * (STATUS 51, hdfs-adhoc-11: one key, an ADMITTED world and an UNSAT
     * one, core {@code r_in_19=true}).  Where the stated terms reach such a
     * handoff: the values of the roots the path's earlier decisions ({@code
     * prefix}) reach; and, where the query also states a family of this
     * run alone -- a handoff of another occurrence the stated terms reach,
     * or one the task's own handoff's arms of this run name -- every root the
     * run ran ({@link #ranRoot}), since that family pins them all.  Clocks
     * never; a derived root by its id ({@link #rootName}).  "" where the
     * stated terms reach no handoff of the task's own.
     */
    public String heldValuation(String sessionId, OccurrenceAddress occurrence,
                                List<String> stated, List<String> prefix) {
        boolean own = false;
        boolean alone = false;
        for (String term : stated) {
            for (String symbol : termSymbols(sessionId, term)) {
                if (symbolKind(sessionId, symbol) != SymbolKind.HANDOFF) {
                    continue;
                }
                AttachRow attach = attach(sessionId, symbol);
                if (attach.producer() == null) continue;
                if (!attach.endpoint().occurrence().equals(occurrence)) {
                    alone = true;
                    continue;
                }
                own = true;
                alone |= armsNameHandoffs(attach);
            }
        }
        if (!own) return "";
        return "held" + (alone ? valuation(sessionId)
                : rootValues(sessionId, prefix));
    }

    /** The values of the roots {@code terms} reach ({@link #termSymbols}),
     *  each by {@link #rootName}; never a clock. */
    private Set<String> rootValues(String sessionId, List<String> terms) {
        Set<String> values = new TreeSet<String>();
        for (String term : terms) {
            for (String symbol : termSymbols(sessionId, term)) {
                RootMintRow root = rootBySymbol(sessionId, symbol);
                if (root != null && root.kind() != RootKind.CLOCK) {
                    values.add(rootName(root.rootId(),
                            rootValue(sessionId, root.rootId())));
                }
            }
        }
        return values;
    }

    /** Every root one session ran ({@link #ranRoot}) but a clock, each by
     *  {@link #rootName}; once per session. */
    private Set<String> valuation(String sessionId) {
        return valuations.computeIfAbsent(sessionId, id -> {
            Set<String> values = new TreeSet<String>();
            for (String rootId : roots().keySet()) {
                RootMintRow ran = ranRoot(rootId, id);
                if (ran != null && ran.kind() != RootKind.CLOCK) {
                    values.add(rootName(rootId, rootValue(id, rootId)));
                }
            }
            return Collections.unmodifiableSet(values);
        });
    }

    /** {@link #valuation}'s memo: a corpus does not change once read. */
    private final Map<String, Set<String>> valuations =
            new ConcurrentHashMap<String, Set<String>>();

    /** Whether one of the attach's own run's arms names another handoff
     *  (its term or a predicate of its path condition); once per session
     *  and symbol. */
    private boolean armsNameHandoffs(AttachRow attach) {
        String sessionId = attach.sessionId();
        return nesting.computeIfAbsent(sessionId + "|" + attach.symbol(),
                key -> {
            boolean nests = false;
            for (Arms.Arm arm : arms().ownArmsAt(Interaction.of(
                    InteractionKind.WIRE, attach.producer(),
                    attach.endpoint()), attach.symbol(), sessionId)) {
                Set<String> named = new HashSet<String>(expressionSymbols(
                        sessionId, arm.expressionRef()));
                for (String conjunct : arm.pi()) {
                    named.addAll(termSymbols(sessionId, conjunct));
                }
                for (String symbol : named) {
                    nests |= !symbol.equals(attach.symbol()) && symbolKind(
                            sessionId, symbol) == SymbolKind.HANDOFF;
                }
            }
            arms().drainRefusals();
            return nests;
        });
    }

    /** {@link #armsNameHandoffs}'s memo. */
    private final Map<String, Boolean> nesting =
            new ConcurrentHashMap<String, Boolean>();

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
        volatile List<OccurrenceAddress> feeders;
        /** path id#decision index -> its dependence. */
        final Map<String, String> dependence =
                new ConcurrentHashMap<String, String>();
    }

    /** By the task object; concurrent, as keys are computed on every core
     *  ({@code ObligationFactory#dependences}). */
    private final Map<ByIdentity<Task>, OfTask> ofTask =
            new ConcurrentHashMap<ByIdentity<Task>, OfTask>();

    private OfTask ofTask(Task task) {
        return ofTask.computeIfAbsent(new ByIdentity<Task>(task),
                key -> new OfTask());
    }

    /** One arm's dependence ({@code ObligationFactory#dependence}) of one
     *  task, by its path and decision: computed once. */
    String dependence(Task task, String decision, Supplier<String> compute) {
        OfTask of = ofTask(task);
        String held = of.dependence.get(decision);
        if (held != null) return held;
        String keyed = compute.get();
        of.dependence.put(decision, keyed);
        return keyed;
    }

    /** {@link #feeders(OccurrenceAddress, List)} of one task's occurrence
     *  and factor, once per task (a function of the corpus's indexes). */
    public List<OccurrenceAddress> feeders(Task task) {
        OfTask of = ofTask(task);
        List<OccurrenceAddress> held = of.feeders;
        if (held == null) {
            held = Collections.unmodifiableList(feeders(task.focused(),
                    task.factor()));
            of.feeders = held;
        }
        return held;
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

    /**
     * WHAT FED ONE OCCURRENCE -- a member, or the task's own -- as an arm's
     * key names it: each distinct (handoff site, producer) once.  Which
     * export of which producer class delivered there is semantic; how many
     * times it was read again is a timing count (owner 2026-10-11): a store
     * version re-read three or four times is one, hdfs-11741's five keys
     * against four are five distinct exports against four.  The producer by
     * its class and export site, the export itself a handle numbered by
     * first appearance ({@link #handle}); one no row places, by its endpoint,
     * a handle too.  A set: the replies to one call arrive in any order
     * (hdfs-adhoc-07 CC5).  A site's sequential znode suffix is a timing
     * name ({@link #sequences}).  {@code stores}: whether what it read of a
     * store ({@link ContentPort}) counts -- a member's does not: a store
     * read is named wherever it reaches the query ({@link #inputShape}).
     */
    private Set<String> handoffs(String sessionId,
                                 OccurrenceAddress occurrence,
                                 boolean stores) {
        Map<String, Set<String>> handoffsOf = names(sessionId).handoffs;
        String key = occurrence.id() + "|" + stores;
        Set<String> held = handoffsOf.get(key);
        if (held != null) return held;
        Set<String> fed = new TreeSet<String>(BY_SHAPE);
        for (AttachRow attach : attachesOn(sessionId, occurrence)) {
            if (!stores && ContentPort.is(attach.endpoint().site())) {
                continue;
            }
            Endpoint producer = attach.producer();
            String from = producer == null ? ""
                    : "<-" + (producer.occurrence() == null
                    ? handle("endpoint", producer.id())
                    : classOf(producer.occurrence()) + "@"
                    + sequences(producer.site()) + "#"
                    + handle("export", producer.id()));
            fed.add(sequences(attach.endpoint().site()) + from);
        }
        fed = Collections.unmodifiableSet(fed);
        handoffsOf.put(key, fed);
        return fed;
    }


    /**
     * {@code text} with each sequential znode's counter ({@link
     * RunSpellings#SEQUENCE}) as a handle ({@link #handle}): which item of
     * its parent it is, by where the key first meets it, not its counter,
     * which shifts with every item an earlier world or a retry added
     * (solr-adhoc-19 SC6: the first queue item a member read was
     * qn-0000000000 in one world and qn-0000000001 in another).
     */
    static String sequences(String text) {
        if (text == null || text.isEmpty()) return "";
        Matcher counter = RunSpellings.SEQUENCE.matcher(text);
        StringBuffer out = new StringBuffer();
        while (counter.find()) {
            counter.appendReplacement(out, Matcher.quoteReplacement(
                    handle(counter.group(1), "seq:" + counter.group())));
        }
        return counter.appendTail(out).toString();
    }

    /** An occurrence's class: its node, region and context shape ({@link
     *  #contextShape}), no address's anchor hashes or counts -- an arm's key
     *  names a member by it, and the closure's static candidates take their
     *  turns by it ({@code ClosurePlanner}).  A shape with a hop no row names
     *  ({@link ContextShape#UNKNOWN_HOP}) tells nothing apart: such an
     *  occurrence is its own class, by its address. */
    String classOf(OccurrenceAddress occurrence) {
        return classes.computeIfAbsent(occurrence.id(), id -> {
            List<String> shape = contextShape(occurrence.context());
            return shape.contains(ContextShape.UNKNOWN_HOP) ? id
                    : occurrence.node().render() + "|"
                            + occurrence.regionId() + "|" + shape;
        });
    }

    /** {@link #classOf}, once per occurrence: a corpus does not change once
     *  read. */
    private final Map<String, String> classes =
            new java.util.concurrent.ConcurrentHashMap<String, String>();

    /** A member's writes to {@code locations}, each by its site and what
     *  it wrote as the guard reads it, canonical ({@link #written}): a
     *  member flip that writes another value at the same site is another
     *  world (a request writing 5 or 7, an arm writing {@code M_A+10} or
     *  {@code M_A-1}), the same value written again is not (a set); an
     *  INITIAL row is no write. */
    private Set<String> writeSites(String sessionId, OccurrenceAddress member,
                                   OccurrenceAddress task,
                                   Set<String> locations) {
        Set<String> sites = new TreeSet<String>(BY_SHAPE);
        for (WriteRow write : writesOn(sessionId, member)) {
            if (write.initial() || !locations.contains(
                    SmtLowering.locationKey(write.location()))) {
                continue;
            }
            sites.add(write.endpoint().site() + "="
                    + written(sessionId, write, task));
        }
        return sites;
    }

    /**
     * WHAT A WRITE WROTE, AS A FLIP QUERY READS IT (the rule: an arm's key
     * names everything its flip query depends on at the task, modulo the
     * run's own names): its term canonical ({@link #term}), or, where the
     * query binds nothing in particular through it -- it states nothing, or
     * holds an unsupported subterm's free name -- the values the TASK's own
     * reads of that version observed, the only reads the query pins to a
     * value through it ({@code FlipQuery#stated}); none observed it: {@code
     * ?}, an alternative the query takes no value from.  What other
     * occurrences' reads observed is no input of the query.
     */
    private String written(String sessionId, WriteRow write,
                           OccurrenceAddress task) {
        String term = term(sessionId, write.expressionRef(), new Naming());
        if (term != null && !UNSUPPORTED.equals(term)) return term;
        String location = SmtLowering.locationKey(write.location());
        Set<String> values = new TreeSet<String>(BY_SHAPE);
        for (ReadRow read : readsOn(sessionId, task)) {
            if (read.observedVersion() == write.version() && location.equals(
                    SmtLowering.locationKey(read.location()))) {
                values.add(observed(sessionId, read.concreteValue()));
            }
        }
        return values.isEmpty() ? UNSUPPORTED : UNSUPPORTED + values;
    }

    /**
     * A value one session observed, with the names its run alone had named
     * by what they stand for: an object the VM named as a handle ({@link
     * VmRows#objectHandle}), else the value's program names ({@link
     * #programNames}).
     */
    private String observed(String sessionId, String value) {
        String text = String.valueOf(value);
        String[] object = VmRows.objectHandle(text);
        return object != null ? handle(object[0], "rid:" + object[1])
                : programNames(sessionId, text);
    }

    /**
     * What a program spelled (an observed value, a term's constants), with
     * each name a node had only in the session's run (its host and port,
     * its store session's id) by the node ({@link RunSpellings}, as the
     * session states them, {@code SessionManifest#runSpellings}) -- one port
     * spelling names {@code node1} in every run, and a run that states none
     * keeps its spelling (another world, never a fold) -- and each identity
     * hash ({@link RunSpellings#IDENTITY}) and sequential znode counter
     * ({@link #sequences}) as a handle.  Never an engine-built
     * name (a hop's {@code site@node#epoch}, a writer's {@code class@site}):
     * a node named like hex would fold two nodes.
     */
    private String programNames(String sessionId, String text) {
        SessionReader session = sessionById.get(sessionId);
        String named = sequences((session == null
                || session.manifest() == null ? RunSpellings.NONE
                : session.manifest().runSpellings()).name(text));
        if (named.indexOf('@') < 0) return named;
        Matcher hash = RunSpellings.IDENTITY.matcher(named);
        StringBuffer out = new StringBuffer();
        while (hash.find()) {
            hash.appendReplacement(out, Matcher.quoteReplacement(
                    handle(hash.group(1) + "@", hash.group())));
        }
        return hash.appendTail(out).toString();
    }

    /** A handle's mark ({@link #handle}). */
    private static final char MARK = '\u0001';
    private static final char HANDLE = '\u0002';
    private static final Pattern MARKED = Pattern.compile(
            "\u0001([^\u0001\u0002]*)\u0002([^\u0001]*)\u0001");

    /**
     * A RUN'S HANDLE for one program value -- an object the VM named (its
     * rid), an identity hash, a name the lowering minted from a run's
     * handle -- marked in a name: its prefix (the class, or the minted
     * name's kind) and the handle.  An arm's key names it by the prefix and
     * the order the key first meets it in ({@link #numbered}): two worlds
     * whose values are other objects aliased alike name alike (a replay
     * renumbers every rid), and two whose values alias differently name
     * apart, as their flip queries do ({@code
     * SmtLowering#assertIdentitiesDistinct}: distinct rids are distinct).
     */
    static String handle(String prefix, String handle) {
        return MARK + prefix + HANDLE + handle + MARK;
    }

    /** {@code text} with each handle ({@link #handle}) named by its prefix
     *  and the number of its first appearance (1, 2, ...); {@code order}
     *  takes each handle's mark, in that order. */
    static String numbered(String text, Map<String, String> order) {
        if (text.indexOf(MARK) < 0) return text;
        Map<String, Integer> number = new HashMap<String, Integer>();
        Matcher handle = MARKED.matcher(text);
        StringBuffer out = new StringBuffer();
        while (handle.find()) {
            order.putIfAbsent(handle.group(2), handle.group());
            int at = number.computeIfAbsent(handle.group(2),
                    key -> number.size() + 1);
            handle.appendReplacement(out, Matcher.quoteReplacement(
                    handle.group(1) + at));
        }
        return handle.appendTail(out).toString();
    }

    /** {@code text} with each handle by its prefix alone. */
    private static String unmarked(String text) {
        return text.indexOf(MARK) < 0 ? text
                : MARKED.matcher(text).replaceAll("$1");
    }

    /** {@code text} with each open unit ({@link #step}) unnumbered: a
     *  walk's entry numbers order nothing. */
    private static String unopened(String text) {
        return text.indexOf(OPEN) < 0 ? text
                : OPENED.matcher(text).replaceAll(String.valueOf(OPEN));
    }

    /** How the names of one set are ordered: by what they say without
     *  their handles first, so a run's handles do not reorder them (then
     *  by the text itself); an open unit's entry number never (two names
     *  apart by it alone keep their order). */
    private static final Comparator<String> BY_SHAPE = Comparator
            .comparing((String text) -> unmarked(unopened(text)))
            .thenComparing(Corpus::unopened);

    /** One naming unit's name ({@link #step}): the digest of its text, its
     *  handles numbered ({@link #numbered}), then their marks in that
     *  order, so a text that holds it numbers them again with its own and
     *  keeps which of them are one object. */
    private static String unit(String text) {
        Map<String, String> order = new LinkedHashMap<String, String>();
        String digest = ArtifactIO.digest(numbered(text, order), 16);
        return order.isEmpty() ? digest : digest + order.values();
    }

    /**
     * One canonical naming walk (Tarjan's, over naming units: terms and
     * container subterms): each unit it entered whose cycle has not closed,
     * by its entry number, in entry order, with its text once expanded; the
     * lowest entry number a cycle edge met in the unit being expanded;
     * whether its text met an unsupported subterm, and which open container
     * subterms' taint it takes (known when their cycle closes).
     */
    private static final class Naming {
        final Map<String, Integer> entered = new HashMap<String, Integer>();
        final List<String> open = new ArrayList<String>();
        final Map<String, Unit> units = new HashMap<String, Unit>();
        int next;
        int low = Integer.MAX_VALUE;
        boolean unsupported;
        Set<String> taints = new HashSet<String>();
    }

    /** One expanded unit of an open cycle ({@link Naming}). */
    private static final class Unit {
        final boolean taints;
        String text;
        boolean unsupported;
        Set<String> takes;

        Unit(boolean taints) {
            this.taints = taints;
        }
    }

    /**
     * One decision's condition as its occurrence decided it, within its
     * session: the term the flip query states ({@code FlipQuery#statedTerm})
     * with each read named by its location, each root by its id and each
     * handoff by its port.  A poll deciding the same condition on a fresh
     * read of the same location names it alike; a loop deciding {@code
     * (< 0 n)} then {@code (< 1 n)} does not ({@code
     * ObligationFactory#dependence} counts the different conditions of one
     * decision site).
     */
    String decisionShape(String sessionId, String term) {
        return SmtNames.substitute(FlipQuery.statedTerm(this, sessionId,
                term), token -> {
                    switch (symbolKind(sessionId, token)) {
                        case ROOT:
                            return "root:" + rootBySymbol(sessionId, token)
                                    .rootId();
                        case HANDOFF:
                            return "handoff:" + attach(sessionId, token)
                                    .endpoint().site();
                        case READ:
                            return "read:" + SmtLowering.locationKey(
                                    read(sessionId, token).location());
                        default:
                            return null;
                    }
                });
    }

    /** {@link #term}: a term the flip query states nothing through. */
    private static final String UNLOWERED = "!";
    /** {@link #term}: a term the query states with an unsupported
     *  subterm's free name, which binds nothing in particular. */
    private static final String UNSUPPORTED = "?";

    /**
     * One term, CANONICAL and digested, as a flip query states it: null
     * where it states nothing -- it does not lower ({@link
     * SmtLowering#lower}) or names what the query cannot declare ({@link
     * FlipQuery#undeclared}) -- and {@link #UNSUPPORTED} where it holds an
     * unsupported subterm.  The digest is of operators, constants, each
     * root by its id, each handoff and each read by what binds it in the
     * query ({@link #handoffName}, {@link #readName}), each container
     * subterm by its canonical body, a name the lowering minted from a
     * run's handle (an identity, by the object it stands for) as a handle
     * ({@link #handle}), and what the program spelled, its string constants
     * and a long's digits, by its program names ({@link #programNames}).
     * No depth bound; a cycle by {@link #step}.
     */
    private String term(String sessionId, String expressionRef,
                        Naming naming) {
        if (expressionRef == null || expressionRef.isEmpty()) return null;
        String name = step(sessionId, "term|" + sessionId + "|"
                + expressionRef, naming, false, () -> {
                    SmtLowering lowering = lowering(sessionId);
                    SmtLowering.Lowered lowered = lowering == null ? null
                            : lowering.lower(expressionRef);
                    if (lowered == null || !lowered.ok()
                            || FlipQuery.undeclared(this, sessionId,
                            lowered.text()) != null) {
                        return null;
                    }
                    return canonical(sessionId, lowered.text(), naming);
                });
        return UNLOWERED.equals(name) ? null : name;
    }

    /** {@link #step}: where an open unit stands in a text until its cycle
     *  closes, by its entry number. */
    private static final char OPEN = '\u0004';
    private static final Pattern OPENED = Pattern.compile(
            "\u0004(\\d+)\u0004");
    /** {@link #close}: the most text one cycle's names may digest; past it
     *  each of its units is named by its own reference
     *  (ARM_KEY_NAMING_CUT, {@link #namingCut}). */
    static final long NAMING_BUDGET = 1L << 26;

    /**
     * One memoized naming step, a term or a container subterm ({@code body}
     * its canonical text, null where it states nothing): its name, a
     * function of the session alone, whichever unit a walk entered first.
     * A unit no cycle runs through is named by its text ({@link #unit}).
     * The units of one CYCLE -- a walk through concurrent writers meeting
     * what it is expanding, Tarjan's strongly connected component -- are
     * named when it closes ({@link #close}); until then a text holds an open
     * unit by its entry number.  Each unit is expanded once per session
     * (solr-adhoc-09 SC7: naming a cycle anew from every entry was
     * exponential in its depth).  {@code taints}: whether an unsupported
     * subterm in it marks the enclosing walk (a container subterm's does; a
     * term answers {@link #UNSUPPORTED} for itself).
     */
    private String step(String sessionId, String key, Naming naming,
                        boolean taints, Supplier<String> body) {
        Map<String, String> canonicalNames = names(sessionId).canonical;
        String held = canonicalNames.get(key);
        if (held != null) {
            naming.unsupported |= taints && held.charAt(0) == 'U';
            return held.substring(1);
        }
        Integer entered = naming.entered.get(key);
        if (entered != null) {
            naming.low = Math.min(naming.low, entered);
            if (taints) naming.taints.add(key);
            return OPEN + entered.toString() + OPEN;
        }
        int number = naming.next++;
        naming.entered.put(key, number);
        naming.open.add(key);
        int low = naming.low;
        boolean unsupported = naming.unsupported;
        Set<String> outer = naming.taints;
        naming.low = number;
        naming.unsupported = false;
        naming.taints = new HashSet<String>();
        Unit unit = new Unit(taints);
        try {
            unit.text = body.get();
        } finally {
            unit.unsupported = naming.unsupported;
            unit.takes = naming.taints;
            naming.units.put(key, unit);
            naming.unsupported = unsupported;
            naming.taints = outer;
        }
        // The lowest entry number a cycle edge in it met: its own, or an
        // open unit's above it.
        int reached = naming.low;
        naming.low = Math.min(low, reached);
        if (reached < number) {
            // Inside a cycle that closes above: named when it closes.
            if (taints) naming.taints.add(key);
            return OPEN + Integer.toString(number) + OPEN;
        }
        List<String> cycle = naming.open.subList(naming.open.indexOf(key),
                naming.open.size());
        Map<String, String> names = close(new ArrayList<String>(cycle),
                naming);
        for (String member : cycle) {
            naming.entered.remove(member);
            naming.units.remove(member);
        }
        cycle.clear();
        String name = names.get(key);
        canonicalNames.putAll(names);
        naming.unsupported |= taints && name.charAt(0) == 'U';
        return name.substring(1);
    }

    /**
     * The names of one closed cycle's units ({@link #step}), each with its
     * memo mark ('U' unsupported, else 'S').  A unit is unsupported where
     * its own text met an unsupported subterm or a container subterm it
     * takes the taint of is.  A unit whose text is null states nothing
     * ({@link #UNLOWERED}); a term unsupported is {@link #UNSUPPORTED}, and
     * so wherever the cycle holds it.  Any other unit is named by the cycle
     * as it meets it: the texts of the units it reaches, numbered by first
     * appearance from it (it first), each open unit in them by that number
     * ({@code cycleN}) -- a unit alone is its text, a unit holding itself
     * holds {@code cycle1}.  Two cycles name alike only as alike graphs, so
     * an arm settled through one stands for another only where its query
     * reads alike.  Past {@link #NAMING_BUDGET} each unit is named by its
     * own reference: no world folds through it (never a cut of the
     * exploration: its arms are asked again), counted by name.
     */
    private Map<String, String> close(List<String> cycle, Naming naming) {
        Map<String, Unit> units = new HashMap<String, Unit>();
        Map<Integer, String> byNumber = new HashMap<Integer, String>();
        for (String member : cycle) {
            units.put(member, naming.units.get(member));
            byNumber.put(naming.entered.get(member), member);
        }
        Set<String> unsupported = new HashSet<String>();
        for (boolean grew = true; grew; ) {
            grew = false;
            for (String member : cycle) {
                if (unsupported.contains(member)) continue;
                Unit unit = units.get(member);
                boolean tainted = unit.unsupported;
                for (String taken : unit.takes) {
                    tainted |= unsupported.contains(taken);
                }
                if (tainted) grew = unsupported.add(member);
            }
        }
        Map<String, String> fixed = new HashMap<String, String>();
        for (String member : cycle) {
            Unit unit = units.get(member);
            if (unit.text == null) {
                fixed.put(member, UNLOWERED);
            } else if (!unit.taints && unsupported.contains(member)) {
                fixed.put(member, UNSUPPORTED);
            }
        }
        long cost = 0;
        for (String member : cycle) {
            String text = units.get(member).text;
            cost += text == null ? 0 : text.length();
        }
        boolean cut = cycle.size() > 1 && cost * cycle.size() > NAMING_BUDGET;
        if (cut) {
            namingCuts.merge(cycle.size(), 1, Integer::sum);
        }
        Map<String, String> names = new HashMap<String, String>();
        for (String member : cycle) {
            String name = fixed.get(member);
            if (name == null) {
                name = cut ? unit("cut:" + member)
                        : unit(cycleText(member, units, byNumber, fixed));
            }
            names.put(member, (unsupported.contains(member) ? "U" : "S")
                    + name);
        }
        return names;
    }

    /** {@link #close}: one cycle unit's text as the cycle meets it from
     *  {@code from}. */
    private static String cycleText(String from, Map<String, Unit> units,
                                    Map<Integer, String> byNumber,
                                    Map<String, String> fixed) {
        List<String> order = new ArrayList<String>();
        Map<String, Integer> number = new HashMap<String, Integer>();
        order.add(from);
        number.put(from, 1);
        StringBuilder out = new StringBuilder();
        for (int at = 0; at < order.size(); at++) {
            if (at > 0) out.append(OPEN);
            Matcher open = OPENED.matcher(units.get(order.get(at)).text);
            StringBuffer text = new StringBuffer();
            while (open.find()) {
                String member = byNumber.get(Integer.parseInt(open.group(1)));
                String name = fixed.get(member);
                if (name == null) {
                    Integer seen = number.get(member);
                    if (seen == null) {
                        seen = order.size() + 1;
                        number.put(member, seen);
                        order.add(member);
                    }
                    name = "cycle" + seen;
                }
                open.appendReplacement(text, Matcher.quoteReplacement(name));
            }
            out.append(open.appendTail(text));
        }
        return out.toString();
    }

    /** Cycles named each unit by its own reference ({@link #close}), by
     *  their size. */
    private final Map<Integer, Integer> namingCuts =
            new ConcurrentHashMap<Integer, Integer>();

    /** The cycles past {@link #NAMING_BUDGET} so far, named ("ARM_KEY_NAMING_CUT:
     *  ..."), or null where none was. */
    public String namingCut() {
        if (namingCuts.isEmpty()) return null;
        return "ARM_KEY_NAMING_CUT: " + new TreeMap<Integer, Integer>(
                namingCuts) + " (cycle size -> cycles) were past the naming"
                + " budget of " + NAMING_BUDGET + " characters: each of"
                + " their units is named by its own reference, so no world"
                + " folds through them and their arms are asked again";
    }

    /** {@link #canonical}: where a name stands while the program's own
     *  spelling around it is named. */
    private static final char PLACE = '\u0003';

    /** {@link #term}'s canonical text of one lowered text: each name it
     *  holds by {@link #tokenName}, and what the program spelled around
     *  them by {@link #programNames} -- never the names themselves. */
    private String canonical(String sessionId, String text, Naming naming) {
        SmtLowering lowering = lowering(sessionId);
        List<String> names = new ArrayList<String>();
        String program = programNames(sessionId, SmtNames.substitute(text,
                token -> {
                    String name = tokenName(sessionId, lowering, token,
                            naming);
                    if (name == null) return null;
                    names.add(name);
                    return PLACE + String.valueOf(names.size() - 1) + PLACE;
                }));
        StringBuilder out = new StringBuilder();
        int at = 0;
        for (int open = program.indexOf(PLACE); open >= 0;
             open = program.indexOf(PLACE, at)) {
            int close = program.indexOf(PLACE, open + 1);
            out.append(program, at, open).append(names.get(
                    Integer.parseInt(program.substring(open + 1, close))));
            at = close + 1;
        }
        return out.append(program.substring(at)).toString();
    }

    /** One name of a lowered text, canonical ({@link #term}), or null to
     *  keep it as spelled. */
    private String tokenName(String sessionId, SmtLowering lowering,
                             String token, Naming naming) {
        if (SmtNames.BUILTIN.contains(token)) return null;
        String body = lowering == null ? null : lowering.sharedBody(token);
        if (body != null) {
            return "dag:" + step(sessionId, "dag|" + sessionId + "|" + token,
                    naming, true, () -> canonical(sessionId, body, naming));
        }
        switch (symbolKind(sessionId, token)) {
            case ROOT: {
                RootMintRow root = rootBySymbol(sessionId, token);
                return (root.kind() == RootKind.CLOCK ? "clock:" : "root:")
                        + root.rootId();
            }
            case HANDOFF:
                return tokenName(sessionId, "handoff|" + sessionId + "|"
                        + token, () -> handoffName(attach(sessionId, token),
                        naming));
            case READ:
                return tokenName(sessionId, "read|" + sessionId + "|" + token,
                        () -> readName(sessionId, read(sessionId, token),
                                naming));
            default:
                if (lowering == null || !lowering.minted(token)) return null;
                if (token.startsWith("unsupported__")) {
                    naming.unsupported = true;
                }
                // A name the lowering minted from a run's handle: by its
                // kind and which handle it is, an identity by its object.
                String[] object = VmRows.objectHandle(
                        lowering.identityOf(token));
                return handle(token.replaceAll("__[0-9a-f]+$", "__"),
                        object == null ? token : "rid:" + object[1]);
        }
    }

    /**
     * A read as its flip query binds it ({@code FlipQuery#bind}): by its
     * location's kind and slot and the writers it may take its value from
     * ({@link Arms#stateArms}, as the query offers them), each by its
     * class ({@link #classOf}), write site and what the query takes from it
     * ({@code FlipQuery#delivered}): its canonical term; a free choice
     * ({@code ?}, with the observed value where it is the observed writer)
     * where the term states nothing or nothing in particular; no choice
     * ({@code /}) where it is a value of another sort.  With nothing bound
     * the read is pinned to its observed value.
     */
    private String readName(String sessionId, ReadRow row, Naming naming) {
        String location = "read:" + row.location().kind() + ":"
                + sequences(row.location().slot());
        String sort = JavaSmtSorts.sortOfJava(row.javaType()).smt;
        List<Arms.Arm> eligible = arms().stateArms(row.endpoint(), sessionId,
                SmtLowering.locationKey(row.location()),
                row.observedVersion(), !row.unnamedWriter());
        // Asked again by the flip query that states them (Arms recomputes
        // every arm): this walk files nothing.
        arms().drainRefusals();
        List<String> writers = new ArrayList<String>();
        boolean binds = false;
        for (Arms.Arm arm : eligible) {
            WriteRow write = arm.write();
            boolean seen = write != null
                    && write.version() == row.observedVersion();
            String who = write == null ? classOf(arm.producer())
                    : write.initial() ? "initial"
                    : classOf(arm.producer()) + "@" + write.endpoint().site();
            SmtLowering lowering = lowering(arm.sessionId());
            SmtLowering.Lowered lowered = lowering == null ? null
                    : lowering.lower(arm.expressionRef());
            if (lowered != null && lowered.ok()
                    && !lowered.value().sort.smt.equals(sort)) {
                writers.add(who + "=/");
                continue;
            }
            String term = term(arm.sessionId(), arm.expressionRef(), naming);
            binds |= term != null;
            writers.add(who + "=" + (term == null || UNSUPPORTED.equals(term)
                    ? "?" + (seen ? observed(sessionId, row.concreteValue())
                    : "") : term));
        }
        if (!binds) {
            return location + "=" + observed(sessionId, row.concreteValue());
        }
        writers.sort(BY_SHAPE);
        return location + "<-" + writers;
    }

    /**
     * A handoff as its flip query binds it ({@code FlipQuery#handoff}): by
     * its port and the arms of its own run that deliver it ({@link
     * Arms#ownArmsAt}) and that the query states ({@code FlipQuery#arm}: an
     * arm whose term does not lower, names what the query cannot declare or
     * is malformed is dropped), each by its producer's class, the export's
     * site, its canonical delivered term, its path condition's predicates
     * the query states (an unsupported subterm of one marks no term) and
     * the guard's values of the roots that term and those predicates reach
     * ({@link #rootName}): the delivery rests on them.  The rest of the
     * guard -- every other root its run ran, which {@code FlipQuery#arm}
     * pins too -- is that run's valuation of roots the delivery does not
     * rest on, a world's fault flips (Z3S-18413: 46 paths of one arm, one id
     * each, by which client and Overseer door faults their runs took), and
     * is named only where the question reads them ({@link #inputShape}).
     * With no arm it is pinned to its arrival.
     */
    private String handoffName(AttachRow attach, Naming naming) {
        String port = "handoff:" + sequences(attach.endpoint().site());
        List<String> arms = new ArrayList<String>();
        if (attach.producer() != null) {
            String sessionId = attach.sessionId();
            SmtLowering lowering = lowering(sessionId);
            for (Arms.Arm arm : arms().ownArmsAt(Interaction.of(
                    InteractionKind.WIRE, attach.producer(),
                    attach.endpoint()), attach.symbol(), sessionId)) {
                SmtLowering.Lowered lowered = lowering == null ? null
                        : lowering.lower(arm.expressionRef());
                if (lowered == null || !lowered.ok()
                        || FlipQuery.malformed(lowered.text())) {
                    continue;
                }
                String term = term(sessionId, arm.expressionRef(), naming);
                if (term == null) continue;
                boolean unsupported = naming.unsupported;
                Set<String> taints = new HashSet<String>(naming.taints);
                List<String> conditions = new ArrayList<String>();
                // What the delivery rests on: its term's symbols and its
                // stated predicates'.
                Set<String> rests = new HashSet<String>(expressionSymbols(
                        sessionId, arm.expressionRef()));
                for (String conjunct : arm.pi()) {
                    if (!Arms.predicate(conjunct)) continue;
                    String stated = FlipQuery.statedTerm(this, sessionId,
                            conjunct);
                    if (FlipQuery.malformed(stated) || FlipQuery.undeclared(
                            this, sessionId, stated) != null) {
                        continue;
                    }
                    conditions.add(canonical(sessionId, stated, naming));
                    rests.addAll(termSymbols(sessionId, conjunct));
                }
                naming.unsupported = unsupported;
                naming.taints = taints;
                Set<String> guard = new TreeSet<String>();
                for (Map.Entry<String, RootMintRow> guarded
                        : arm.guardMints().entrySet()) {
                    if (rests.contains(guarded.getKey())) {
                        guard.add(rootName(guarded.getValue().rootId(),
                                arm.guard().get(guarded.getKey())));
                    }
                }
                arms.add(classOf(arm.producer()) + "@"
                        + attach.producer().site() + "=" + term + "|"
                        + conditions + "|" + guard);
            }
            arms().drainRefusals();
        }
        if (arms.isEmpty()) {
            return port + "=" + observed(attach.sessionId(), attach.arrival());
        }
        arms.sort(BY_SHAPE);
        return port + "<-" + arms;
    }

    /** A root's value as an arm's key names it: by its id and the value its
     *  run ran it at, but a root its run computed from another input
     *  ({@link #derived}: a clock's reading, every run's own) by its id
     *  alone. */
    private String rootName(String rootId, String value) {
        return "root:" + rootId + (derived(rootId) ? "" : "=" + value);
    }

    /** A handoff's or a read's name ({@link #handoffName}, {@link
     *  #readName}), once per session and token, as a unit ({@link #unit}:
     *  its digest and its handles' marks) once no open unit stands in it
     *  ({@link #step}): a handoff names its arms' conditions, which name the
     *  handoffs they read, so a name held whole grew with every level of a
     *  chain that fans in (solr-adhoc-40 SL1: 8 GB of one name). */
    private String tokenName(String sessionId, String key,
                             Supplier<String> name) {
        Map<String, String> tokenNames = names(sessionId).tokens;
        String held = tokenNames.get(key);
        if (held != null) return held;
        String named = name.get();
        if (named.indexOf(OPEN) >= 0) return named;
        String unit = unit(named);
        tokenNames.put(key, unit);
        return unit;
    }

    /**
     * WHAT ONE SESSION'S ARM KEYS NAME ({@code ObligationFactory#dependence}),
     * held while they are computed: the canonical names of its terms and
     * container subterms ({@link #step}), of its handoffs and reads ({@link
     * #tokenName}), and what fed each of its occurrences ({@link
     * #handoffs}) -- each a function of the session's rows alone, so let go
     * once its keys are ({@link #keysDone}).
     */
    private static final class Names {
        final Map<String, String> canonical =
                new ConcurrentHashMap<String, String>();
        final Map<String, String> tokens =
                new ConcurrentHashMap<String, String>();
        final Map<String, Set<String>> handoffs =
                new ConcurrentHashMap<String, Set<String>>();
    }

    /** {@link Names}, by session. */
    private final Map<String, Names> names =
            new ConcurrentHashMap<String, Names>();

    private Names names(String sessionId) {
        return names.computeIfAbsent(sessionId, any -> new Names());
    }

    /**
     * One session's arm keys are computed: what they named ({@link Names})
     * goes, and what its lowering lowered for them -- a fresh lowering, as
     * a JVM of its own starts with ({@link #freshLowerings}), lowers what
     * the round asks of the session after them.  Held for every session to
     * the round's end, the lowerings' memos were a planner's peak
     * (SGF8-adhoc-40 planning-7: 8.9 GB live before its keys, 2.2 M memo
     * entries and the 21504 MB heap full in them).
     */
    void keysDone(String sessionId) {
        names.remove(sessionId);
        loweringById.remove(sessionId);
    }

    /** The verdict the WAVE's file states for one obligation in the session
     *  its worker landed, or null.  Only a cross-check: the SESSION's row is
     *  the verdict, and a corpus stating two different verdicts is refused by
     *  name.  By session: an obligation asked again under its id has a worker,
     *  and a session, per ask (SGF3-bugs-snapshot-no-active: its first ask's
     *  session NOT_ADMITTED, the re-ask's ADMITTED, each right). */
    public ObligationResult waveVerdict(String sessionId,
                                        String obligationId) {
        return waveVerdicts.getOrDefault(sessionId,
                Collections.<String, ObligationResult>emptyMap())
                .get(obligationId);
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
                                           OccurrenceAddress served,
                                           Map<String, Integer> cut) {
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
        Set<String> handlers = handlerStances.getOrDefault(
                producerEndpointId, Collections.<String>emptySet());
        if (stances.isEmpty() && handlers.isEmpty()) return doors;
        String own = ContextShape.Stance.of(served).render();
        // The occurrences at those stances, in corpus order: no other
        // occurrence is a door or a cut (a scan of every occurrence per
        // demand was 93 s of SGF8-adhoc-05 round 5's walk).
        StanceIndex index = stanceIndex();
        Set<String> asked = new HashSet<String>(stances);
        asked.addAll(handlers);
        int count = 0;
        List<int[]> standing = new ArrayList<int[]>();
        for (String stance : asked) {
            int[] places = index.places.get(stance);
            if (places == null) continue;
            standing.add(places);
            count += places.length;
        }
        int[] places = new int[count];
        int next = 0;
        for (int[] each : standing) {
            System.arraycopy(each, 0, places, next, each.length);
            next += each.length;
        }
        Arrays.sort(places);
        for (int place : places) {
            OccurrenceAddress occurrence = index.occurrences.get(place);
            if (occurrence.equals(served)) continue;
            String stance = index.stances[place];
            if (stances.contains(stance) && !stance.equals(own)) {
                if (!doors.contains(occurrence)) doors.add(occurrence);
            } else if (stances.contains(stance)) {
                cut.merge(OWN_TURN, 1, Integer::sum);
            } else if (handlers.contains(stance)) {
                cut.merge(HANDLER_TURN, 1, Integer::sum);
            }
        }
        return doors;
    }

    /** Every occurrence in corpus order, its stance, and stance -> the
     *  places of the occurrences standing there ({@link #doorsOf}). */
    private static final class StanceIndex {
        final List<OccurrenceAddress> occurrences;
        final String[] stances;
        final Map<String, int[]> places = new HashMap<String, int[]>();

        StanceIndex(Collection<OccurrenceAddress> all) {
            occurrences = new ArrayList<OccurrenceAddress>(all);
            stances = new String[occurrences.size()];
            Map<String, List<Integer>> at =
                    new HashMap<String, List<Integer>>();
            for (int place = 0; place < stances.length; place++) {
                stances[place] = ContextShape.Stance.of(
                        occurrences.get(place)).render();
                at.computeIfAbsent(stances[place],
                        stance -> new ArrayList<Integer>()).add(place);
            }
            for (Map.Entry<String, List<Integer>> each : at.entrySet()) {
                int[] held = new int[each.getValue().size()];
                for (int index = 0; index < held.length; index++) {
                    held[index] = each.getValue().get(index);
                }
                places.put(each.getKey(), held);
            }
        }
    }

    /** {@link StanceIndex}, built at the first {@link #doorsOf}: a corpus
     *  does not change once read. */
    private volatile StanceIndex stanceIndex;

    private StanceIndex stanceIndex() {
        StanceIndex held = stanceIndex;
        if (held != null) return held;
        synchronized (this) {
            if (stanceIndex == null) {
                stanceIndex = new StanceIndex(occurrenceById.values());
            }
            return stanceIndex;
        }
    }

    /** What {@link #doorsOf} cut, by narrowing: the served occurrence's own
     *  turn, and turns standing on the message (its handlers). */
    public static final String OWN_TURN = "own turn";
    public static final String HANDLER_TURN = "handlers";

    /** One session's schedule as the corpus indexes it, read once. */
    private static List<Fact> facts(SessionReader session) {
        List<ScheduleEvent> events;
        try {
            events = session.schedule();
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        List<Fact> facts = new ArrayList<Fact>();
        // One stance per context and one string per name, held by every
        // fact standing there: each event spells its context and ids anew
        // (SGF8-adhoc-05 round 5: 0.9 M facts, 2.3 M strings, 244 MB).
        Map<String, ContextShape.Stance> stances =
                new HashMap<String, ContextShape.Stance>();
        Map<String, String> renders = new HashMap<String, String>();
        for (ScheduleEvent event : events) {
            ContextShape.Stance stance = stance(stances, event.context());
            String received = NAMES.intern(event.received());
            String endpoint = NAMES.intern(event.endpoint());
            String occurrence = NAMES.intern(event.occurrence());
            // A context that took a message into itself stands under it,
            // in or out of a region.
            if (!received.isEmpty() && stance != null
                    && !(stance.context() instanceof CausalContext.Anchor)) {
                facts.add(new Fact(Fact.Kind.TAKEN_IN, renders
                        .computeIfAbsent(stance.render(), NAMES::intern),
                        received, null));
            }
            // Where every message was sent from, in or out of a region: a
            // daemon tick's heartbeat is sent from the tick's root alone.
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !endpoint.isEmpty() && stance != null) {
                facts.add(new Fact(Fact.Kind.SENDER_STANCE, endpoint, "",
                        stance));
            }
            if (occurrence.isEmpty()) {
                // Taken in at a turn's root, before any region of it opened
                // (a queue item a turn consumes first): the turn's every
                // occurrence is its receiver.  A turn standing on the
                // message (a request's handler) is what it started, no door
                // of it.
                if (!received.isEmpty() && stance != null) {
                    facts.add(new Fact(stance.context() instanceof
                            CausalContext.Anchor ? Fact.Kind.HANDLER_STANCE
                            : Fact.Kind.RECEIVING_STANCE, received, "",
                            stance));
                }
                continue;
            }
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !endpoint.isEmpty()) {
                facts.add(new Fact(Fact.Kind.SENDER, endpoint, occurrence,
                        null));
            } else if (!received.isEmpty()) {
                facts.add(new Fact(Fact.Kind.RECEIVER, received, occurrence,
                        null));
            }
        }
        return facts;
    }

    /** The names a corpus derives -- the ids and stance renders its
     *  schedule facts name, the leaves its leaf sets hold -- one string a
     *  name in this JVM while anything holds it. */
    private static final Interner<String> NAMES =
            Interners.newWeakInterner();

    /** A schedule context's stance ({@link ContextShape.Stance#ofSend}),
     *  one per context of one session's schedule: its node and causal
     *  context, its handoffs aside. */
    private static ContextShape.Stance stance(
            Map<String, ContextShape.Stance> stances, String sendContext) {
        int first = sendContext.indexOf('|');
        int second = first < 0 ? -1 : sendContext.indexOf('|', first + 1);
        String key = second < 0 ? sendContext
                : sendContext.substring(0, second);
        if (stances.containsKey(key)) return stances.get(key);
        ContextShape.Stance stance = ContextShape.Stance.ofSend(key);
        stances.put(key, stance == null ? null : new ContextShape.Stance(
                NAMES.intern(stance.node()), stance.context()));
        return stances.get(key);
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
                case HANDLER_STANCE:
                    handlerStances.computeIfAbsent(fact.key,
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
        for (ActivationRow row : session.activations()) {
            if (apart) continue;
            remember(session.sessionId(), row.occurrence());
            // The sender an anchor names: a causal chain goes on through it.
            if (row.anchorProducer() != null) {
                occurrenceByEndpoint.put(row.anchorProducer().id(),
                        row.anchorProducer().occurrence());
                remember(session.sessionId(),
                        row.anchorProducer().occurrence());
            }
            add(activations, row.occurrence().id(), row);
        }
        for (DecisionRow row : session.decisions()) {
            if (!apart) remember(session.sessionId(), row.occurrence());
            // A decision's clock cells are corpus symbols at Int.
            for (String cell : row.clockReadings().keySet()) {
                declaredSymbols.put(cell, Sort.INT);
            }
        }
        for (ExportRow row : session.exports()) {
            // A forced world's export is no message any arm delivers; one
            // before it is its own path's alone (Arms#armsAt's scope).
            if (row.seq() >= world || apart) continue;
            add(exports, row.endpoint().id(), row);
            remember(session.sessionId(), row.endpoint().occurrence());
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
        }
        for (AttachRow row : session.attaches()) {
            handoffSymbols.add(row.symbol());
            attachesOn.add(row.endpoint().occurrence().id(), row.sessionId(),
                    row, apart);
            // One variable, one sort: from the JVM descriptor, never a value's
            // spelling.
            declaredSymbols.put(row.symbol(),
                    JavaSmtSorts.sortOfJava(row.javaType()));
            Interaction interaction = row.interaction();
            if (interaction != null && !apart) {
                interactions.put(interaction.id(), interaction);
                add(attachesByInteraction, interaction.id(), row);
            }
            if (apart) continue;
            remember(session.sessionId(), row.endpoint().occurrence());
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
            if (row.producer() != null) {
                occurrenceByEndpoint.put(row.producer().id(),
                        row.producer().occurrence());
                remember(session.sessionId(), row.producer().occurrence());
            }
        }
        for (RootMintRow row : session.roots()) {
            if (!apart) remember(session.sessionId(), row.occurrence());
            rootsById.computeIfAbsent(row.rootId(),
                    key -> new LinkedHashMap<String, RootMintRow>())
                    .put(session.sessionId(), row);
            rootIdsBySymbol.computeIfAbsent(row.symbol(),
                    key -> new LinkedHashSet<String>()).add(row.rootId());
            declaredSymbols.put(row.symbol(),
                    row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT);
        }
        for (WriteRow row : session.writes()) {
            if (apart) continue;
            String location = SmtLowering.locationKey(row.location());
            located(writersOn, row.endpoint().occurrence(),
                    session.sessionId());
            remember(session.sessionId(), row.endpoint().occurrence());
            // An INITIAL's endpoint observed the location; it wrote nothing.
            if (!row.initial()) {
                located(writtenLocations, row.endpoint().occurrence(),
                        location);
                writeSitesByLocation.computeIfAbsent(location,
                        ignored -> new LinkedHashMap<List<String>,
                                WriteRow>())
                        .putIfAbsent(Arrays.asList(row.endpoint().site(),
                                row.javaType()), row);
            }
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
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
            if (apart) continue;
            located(readersOn, row.endpoint().occurrence(),
                    session.sessionId());
            remember(session.sessionId(), row.endpoint().occurrence());
            located(readLocations, row.endpoint().occurrence(),
                    SmtLowering.locationKey(row.location()));
            occurrenceByEndpoint.put(row.endpoint().id(),
                    row.endpoint().occurrence());
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

    /** One session's lowering, made as first asked ({@link
     *  SmtLowering#forSession}) and kept until its keys are done ({@link
     *  #keysDone}) or its hold lets its rows go; null for a session this
     *  corpus lacks. */
    public SmtLowering lowering(String sessionId) {
        SmtLowering held = loweringById.get(sessionId);
        if (held != null) return held;
        SessionReader session = sessionById.get(sessionId);
        if (session == null) return null;
        // Its join first: reading its rows again may let others go, whose
        // lowerings leave this map.
        SmtLowering made = SmtLowering.forSession(session, join(sessionId));
        SmtLowering first = loweringById.putIfAbsent(sessionId, made);
        return first != null ? first : made;
    }

    /**
     * Every session's lowering made afresh as next asked ({@link
     * #lowering}).  A lowering keeps what it lowered -- its memo, the names
     * it minted, the count its refused constructs are named by -- so a query
     * built after another would name them differently.  A question asked of
     * a corpus read once for many ({@code ObligationSolverMain --serve})
     * starts from here: what a JVM of its own would have had.  Every other memo of a corpus is a function of
     * its rows alone.
     */
    void freshLowerings() {
        loweringById.clear();
    }

    /** One session's state join; a session this corpus lacks joins nothing. */
    public SmtLowering.SessionJoin join(String sessionId) {
        return state(sessionId).join;
    }

    public List<SessionReader> sessions() {
        return sessions;
    }

    /** {@link #sessions} and the forced ones, as read. */
    List<SessionReader> everySession() {
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
        Derived of = bySession.get(sessionId);
        List<DecisionRow> taken = of == null ? null
                : of.decisions.get(occurrence.id());
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
        Derived of = bySession.get(sessionId);
        List<DecisionRow> taken = of == null ? null
                : of.decisions.get(occurrence.id());
        return taken == null ? Collections.<DecisionRow>emptyList() : taken;
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
        List<ReadRow> all = new ArrayList<ReadRow>();
        for (String session : readersOn.getOrDefault(occurrence.id(),
                Collections.<String>emptySet())) {
            all.addAll(readsOn(session, occurrence));
        }
        return all;
    }

    /** Every attach of ONE session whose consumer sits at this occurrence. */
    public List<AttachRow> attachesOn(String sessionId,
                                      OccurrenceAddress occurrence) {
        return attachesOn.of(occurrence.id(), sessionId);
    }

    /** Every read ONE session made at this occurrence, in recorded order. */
    public List<ReadRow> readsOn(String sessionId,
                                 OccurrenceAddress occurrence) {
        List<ReadRow> own = state(sessionId).readsOn.get(occurrence.id());
        return own == null ? Collections.<ReadRow>emptyList()
                : Collections.unmodifiableList(own);
    }

    public List<WriteRow> writesOn(OccurrenceAddress occurrence) {
        List<WriteRow> all = new ArrayList<WriteRow>();
        for (String session : writersOn.getOrDefault(occurrence.id(),
                Collections.<String>emptySet())) {
            all.addAll(writesOn(session, occurrence));
        }
        return all;
    }

    /** Every write ONE session made at this occurrence, in recorded order. */
    public List<WriteRow> writesOn(String sessionId,
                                   OccurrenceAddress occurrence) {
        List<WriteRow> own = state(sessionId).writesOn.get(occurrence.id());
        return own == null ? Collections.<WriteRow>emptyList()
                : Collections.unmodifiableList(own);
    }

    /**
     * Whether {@code read} is {@code occurrence}'s ROLE PREFIX in {@code
     * sessionId}: role work of its node under its causal context before it
     * opened -- before its first read or write on the session's one order
     * ({@link RowOrder}, seq then tie), any read where it states none.  A
     * routed alias captures its view in the request's role work and writes
     * it in a store door's region, often with no VM event between.  The one
     * rule a pairing flip is offered by ({@code PairingFlip#reads}) and a
     * world pairing's read lies on the fatal path by ({@code
     * compose.Composer.Composition#onFatalPath}).
     */
    public boolean rolePrefix(String sessionId, ReadRow read,
                              OccurrenceAddress occurrence) {
        OccurrenceAddress at = read.endpoint().occurrence();
        if (!at.role() || at.equals(occurrence)
                || !at.node().equals(occurrence.node())
                || !at.context().equals(occurrence.context())) {
            return false;
        }
        long openedSeq = Long.MAX_VALUE;
        int openedTie = 0;
        for (ReadRow row : readsOn(sessionId, occurrence)) {
            if (RowOrder.beforeCut(row.seq(), row.tie(), openedSeq,
                    openedTie)) {
                openedSeq = row.seq();
                openedTie = row.tie();
            }
        }
        for (WriteRow row : writesOn(sessionId, occurrence)) {
            if (RowOrder.beforeCut(row.seq(), row.tie(), openedSeq,
                    openedTie)) {
                openedSeq = row.seq();
                openedTie = row.tie();
            }
        }
        return RowOrder.beforeCut(read.seq(), read.tie(), openedSeq,
                openedTie);
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
        String key = locationKey + "|" + observedVersion + "|"
                + (reader == null ? "" : reader.id());
        StateRows state = state(sessionId);
        List<WriteRow> held = state.eligible.get(key);
        if (held != null) return held;
        List<WriteRow> found = Collections.unmodifiableList(eligibleOf(
                sessionId, locationKey, observedVersion, reader));
        if (state != NO_STATE) state.eligible.put(key, found);
        return found;
    }

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
        Set<String> found = of.symbolsByExpression.get(expressionRef);
        if (found != null) return found;
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
        Set<String> held = FrozenSet.of(symbols);
        of.symbolsByExpression.put(expressionRef, held);
        return held;
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

    /** What {@code key} rests on in one session, computed once and held
     *  as {@link HeldLeaves}. */
    public Set<String> leaves(String sessionId, String key,
                              Supplier<Set<String>> compute) {
        Derived of = bySession.get(sessionId);
        if (of == null) return compute.get();
        Set<String> found = of.leaves.get(key);
        if (found == null) {
            found = new HeldLeaves(compute.get());
            of.leaves.put(key, found);
        }
        return found;
    }

    /**
     * {@link #leaves} of one read row, held by its seq: read rows share a seq
     * (a store read and its view's), and they share one set, the first row's
     * asked -- a function of the ORDER the rows are first asked in (STATUS
     * open defect 70).  A computation that may run ahead of that order asks
     * under {@code claims}: a shared seq no one has asked yet is CLAIMED
     * there, by the row it is first asked of, and held there until the
     * claims are taken in the order ({@link #take}).  Without claims -- a
     * computation in the order -- the set is held at once.
     */
    public Set<String> readLeaves(String sessionId, ReadRow read,
                                  Claims claims,
                                  Supplier<Set<String>> compute) {
        Derived of = bySession.get(sessionId);
        if (of == null) return compute.get();
        String key = "read " + read.seq();
        Set<String> found = of.leaves.get(key);
        if (found != null) return found;
        if (claims != null && of.sharedSeqs.contains(read.seq())) {
            return claims.claim(sessionId, read,
                    () -> new HeldLeaves(compute.get()));
        }
        found = new HeldLeaves(compute.get());
        if (of.sharedSeqs.contains(read.seq())) {
            of.sharedBy.put(key, read);
            of.leaves.put(key, found);
            return found;
        }
        Set<String> first = of.leaves.putIfAbsent(key, found);
        return first != null ? first : found;
    }

    /**
     * Takes, in the order, what one computation claimed ({@link
     * #readLeaves}): every shared seq it claimed that no one took yet is
     * held as it claimed it, if each one taken already was taken by the
     * same row; else nothing is taken, and the computation is not the one
     * the order makes (false).
     */
    public boolean take(Claims claims) {
        for (Claims.Claim claim : claims.claimed.values()) {
            Derived of = bySession.get(claim.sessionId);
            ReadRow by = of.sharedBy.get("read " + claim.read.seq());
            if (by != null && by != claim.read) return false;
        }
        for (Claims.Claim claim : claims.claimed.values()) {
            Derived of = bySession.get(claim.sessionId);
            String key = "read " + claim.read.seq();
            if (of.sharedBy.putIfAbsent(key, claim.read) == null) {
                of.leaves.put(key, claim.leaves);
            }
        }
        return true;
    }

    /**
     * WHAT ONE COMPUTATION CLAIMED ({@link #readLeaves}), in the order it
     * claimed it, and the answers computed over a claim ({@link #held}):
     * one computation's at a time, on one thread.
     */
    public static final class Claims {
        private final Map<String, Claim> claimed =
                new LinkedHashMap<String, Claim>();
        /** Whether a claim was read since {@link #since}. */
        private boolean read;
        /** key -> an answer computed over a claim, held here until the
         *  claims are taken ({@code compose.RestsOn}). */
        public final Map<String, Set<String>> held =
                new LinkedHashMap<String, Set<String>>();

        private Set<String> claim(String sessionId, ReadRow read,
                                  Supplier<Set<String>> leaves) {
            String key = sessionId + "|" + read.seq();
            Claim claim = claimed.get(key);
            if (claim == null) {
                claim = new Claim(sessionId, read, leaves.get());
                claimed.put(key, claim);
            }
            this.read = true;
            return claim.leaves;
        }

        /** How many claims and answers over them it holds. */
        public int size() {
            return claimed.size() + held.size();
        }

        /** An answer {@link #held} over a claim is read. */
        public void readHeld() {
            read = true;
        }

        /** Starts one answer's computation: whether the one around it read
         *  a claim, which {@link #over} gives back. */
        public boolean since() {
            boolean was = read;
            read = false;
            return was;
        }

        /** Whether the answer begun at {@link #since} read a claim; the one
         *  around it ({@code was}) has, if either did. */
        public boolean over(boolean was) {
            boolean over = read;
            read = was || over;
            return over;
        }

        /** Takes {@code later}'s claims after these, if each it shares
         *  with these is the same row's; false, taking none, else. */
        public boolean follow(Claims later) {
            for (Map.Entry<String, Claim> each : later.claimed.entrySet()) {
                Claim mine = claimed.get(each.getKey());
                if (mine != null && mine.read != each.getValue().read) {
                    return false;
                }
            }
            for (Map.Entry<String, Claim> each : later.claimed.entrySet()) {
                claimed.putIfAbsent(each.getKey(), each.getValue());
            }
            held.putAll(later.held);
            read |= later.read;
            return true;
        }

        private static final class Claim {
            final String sessionId;
            final ReadRow read;
            final Set<String> leaves;

            Claim(String sessionId, ReadRow read, Set<String> leaves) {
                this.sessionId = sessionId;
                this.read = read;
                this.leaves = leaves;
            }
        }
    }

    /**
     * ONE LEAF SET AS A SESSION KEEPS IT ({@link #leaves}): its names in
     * the order computed, each the JVM's one instance of it ({@link
     * #NAMES}: the sessions' leaf sets name the same symbols and
     * locations), read-only.
     * Held as the walk's LinkedHashSet, with a location leaf spelled anew
     * in each, the leaf sets were the largest thing a planner held after a
     * round (SGF7, offline: 478 of solr-adhoc-40's 1582 MB over 12 of its
     * sessions, 200 K sets of 28 names on average; 239 of solr-adhoc-10's
     * 1209 MB); held so, 48 and 27 MB.  Their readers only iterate them
     * ({@code Independence}).
     */
    static final class HeldLeaves extends AbstractSet<String> {
        private final String[] names;

        HeldLeaves(Set<String> computed) {
            names = new String[computed.size()];
            int at = 0;
            for (String name : computed) names[at++] = NAMES.intern(name);
        }

        @Override
        public Iterator<String> iterator() {
            return Arrays.asList(names).iterator();
        }

        @Override
        public int size() {
            return names.length;
        }
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
        if (expressionRef == null) return Collections.emptyList();
        StateRows state = state(sessionId);
        List<StateRead> held = state.stateReads.get(expressionRef);
        if (held != null) return held;
        List<StateRead> found = stateReadsOf(sessionId, expressionRef);
        if (state != NO_STATE) state.stateReads.put(expressionRef, found);
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
        return FrozenSet.of(read.keySet());
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
        return FrozenSet.of(events);
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
        Derived of = bySession.get(sessionId);
        List<AttachRow> own = of == null ? null
                : of.ownAttaches.get(interaction.id());
        return own == null ? Collections.<AttachRow>emptyList() : own;
    }

    @Override
    public List<ExportRow> ownExportsOf(String sessionId, Endpoint producer) {
        Derived of = producer == null ? null : bySession.get(sessionId);
        List<ExportRow> own = of == null ? null
                : of.ownExports.get(producer.id());
        return own == null ? Collections.<ExportRow>emptyList() : own;
    }

    @Override
    public List<WriteRow> writesOf(String sessionId, String locationKey) {
        return join(sessionId).writes(locationKey);
    }

    @Override
    public List<ReadRow> readsOf(String sessionId, String locationKey) {
        return join(sessionId).reads(locationKey);
    }

    /** One write per (site, java type) that wrote a location, in any session,
     *  first seen first: what writes it, not how often. */
    public Collection<WriteRow> writeSitesOf(String locationKey) {
        Map<List<String>, WriteRow> sites =
                writeSitesByLocation.get(locationKey);
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
    public synchronized Map<String, List<RootMintRow>> roots() {
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
        return occurrenceByEndpoint.get(endpointId);
    }

    @Override
    public ActivationRow activationOf(String sessionId,
                                      String occurrenceId) {
        Derived of = bySession.get(sessionId);
        return of == null ? null : of.activationByOccurrence.get(occurrenceId);
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
        return version < 0 ? null : join(sessionId).write(locationKey,
                version);
    }

    /** Every occurrence of the node that writes or reads one location. */
    public Set<String> touching(OccurrenceAddress occurrence,
                                LocationId location) {
        Set<String> found = locationTouches.get(touchKey(occurrence,
                location));
        return found == null ? Collections.<String>emptySet() : found;
    }

    public AttachRow attach(String sessionId, String symbol) {
        Derived of = bySession.get(sessionId);
        return of == null ? null : of.attachBySymbol.get(symbol);
    }

    /** Whether some session's attach minted this symbol: a handoff
     *  variable, which only that session's family binds. */
    public boolean handoffSymbol(String symbol) {
        return handoffSymbols.contains(symbol);
    }

    /** The root one session minted under one symbol, or null. */
    public RootMintRow rootBySymbol(String sessionId, String symbol) {
        Derived of = bySession.get(sessionId);
        return of == null ? null : of.rootBySymbol.get(symbol);
    }

    public ReadRow read(String sessionId, String symbol) {
        return state(sessionId).readBySymbol.get(symbol);
    }

    public SymbolKind symbolKind(String sessionId, String symbol) {
        Derived of = bySession.get(sessionId);
        if (of == null) return SymbolKind.UNKNOWN;
        if (of.rootBySymbol.containsKey(symbol)) return SymbolKind.ROOT;
        if (of.attachBySymbol.containsKey(symbol)) return SymbolKind.HANDOFF;
        if (state(sessionId).readBySymbol.containsKey(symbol)) {
            return SymbolKind.READ;
        }
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
            new ConcurrentHashMap<String, Set<java.math.BigInteger>>();

    /**
     * {@link #comparedLiterals} of every integral configuration root, the
     * roots whose domain an arm's key names ({@code
     * ObligationFactory#dependence}): asked of every session's decisions,
     * each lowered by its own session's lowering, so asked before keys are
     * computed one session to a thread ({@code
     * ObligationFactory#dependences}), and asked the same way -- one
     * session's decisions in the roots' order on one thread ({@link
     * Parallel#grouped}) -- each root's literals the union of its
     * decisions'.
     */
    void configurationLiterals() {
        // Every symbol a key may ask the domain of: each session's mints by
        // symbol, as a key finds them (#rootBySymbol), so no key asks one
        // first (a root minted under two symbols keeps one in rootsById).
        Map<String, Pattern> roots = new LinkedHashMap<String, Pattern>();
        for (Derived of : bySession.values()) {
            for (RootMintRow mint : of.rootBySymbol.values()) {
                if (mint.kind() == RootKind.INTEGRAL
                        && mint.category() == RootCategory.CONFIG
                        && !compared.containsKey(mint.symbol())) {
                    roots.computeIfAbsent(mint.symbol(), Corpus::comparing);
                }
            }
        }
        List<Map.Entry<String, Map.Entry<String, DecisionRow>>> asked =
                new ArrayList<Map.Entry<String,
                        Map.Entry<String, DecisionRow>>>();
        for (String symbol : roots.keySet()) {
            for (Map.Entry<String, DecisionRow> decided : deciding(symbol)) {
                asked.add(new java.util.AbstractMap.SimpleImmutableEntry<
                        String, Map.Entry<String, DecisionRow>>(symbol,
                        decided));
            }
        }
        List<Set<java.math.BigInteger>> found;
        try {
            found = Parallel.grouped(asked, one -> one.getValue().getKey(),
                    one -> literals(roots.get(one.getKey()),
                            one.getValue().getKey(),
                            one.getValue().getValue()));
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        Map<String, Set<java.math.BigInteger>> literals =
                new LinkedHashMap<String, Set<java.math.BigInteger>>();
        for (String symbol : roots.keySet()) {
            literals.put(symbol, new java.util.TreeSet<java.math.BigInteger>());
        }
        for (int at = 0; at < asked.size(); at++) {
            literals.get(asked.get(at).getKey()).addAll(found.get(at));
        }
        compared.putAll(literals);
    }

    /**
     * Root symbol -> the recorded predicate decisions whose terms reach it,
     * each (session, decision): every decision's symbols found once, at the
     * first ask ({@link #comparedLiterals}).  Asked of every decision once
     * per root, the composition of SGF7B-adhoc-10's 462 sessions spent 870
     * of its 1032 s in its roots' domains, each root's ask walking every
     * decision's term again.
     */
    private Map<String, List<Map.Entry<String, DecisionRow>>> deciding;

    private synchronized List<Map.Entry<String, DecisionRow>> deciding(
            String symbol) {
        if (deciding == null) {
            Set<String> wanted = new HashSet<String>();
            for (Map<String, RootMintRow> mints : rootsById.values()) {
                for (RootMintRow mint : mints.values()) {
                    wanted.add(mint.symbol());
                }
            }
            deciding = new HashMap<String,
                    List<Map.Entry<String, DecisionRow>>>();
            for (Derived of : bySession.values()) {
                String sessionId = of.session.sessionId();
                for (List<DecisionRow> path : of.decisions.values()) {
                    for (DecisionRow decision : path) {
                        if (!Arms.predicate(decision.term())) continue;
                        for (String reached
                                : termSymbols(sessionId, decision.term())) {
                            if (!wanted.contains(reached)) continue;
                            deciding.computeIfAbsent(reached, k ->
                                    new ArrayList<Map.Entry<String,
                                            DecisionRow>>()).add(
                                    new java.util.AbstractMap
                                            .SimpleImmutableEntry<String,
                                            DecisionRow>(sessionId,
                                            decision));
                        }
                    }
                }
            }
        }
        List<Map.Entry<String, DecisionRow>> reaching = deciding.get(symbol);
        return reaching == null
                ? Collections.<Map.Entry<String, DecisionRow>>emptyList()
                : reaching;
    }

    /**
     * Every integral literal a recorded decision of this corpus compares
     * {@code symbol}, a root's, with directly ({@code (op c symbol)} or
     * {@code (op symbol c)}, {@code op} an order or an equality), its term
     * lowered by the one lowering; once per symbol.
     */
    Set<java.math.BigInteger> comparedLiterals(String symbol) {
        Set<java.math.BigInteger> known = compared.get(symbol);
        if (known != null) return known;
        Set<java.math.BigInteger> literals =
                new java.util.TreeSet<java.math.BigInteger>();
        Pattern atom = comparing(symbol);
        for (Map.Entry<String, DecisionRow> decided : deciding(symbol)) {
            literals.addAll(literals(atom, decided.getKey(),
                    decided.getValue()));
        }
        compared.put(symbol, literals);
        return literals;
    }

    /** A comparison of {@code symbol} with an integral literal, as {@link
     *  #comparedLiterals} finds it. */
    private static Pattern comparing(String symbol) {
        String name = Pattern.quote(symbol);
        String literal = "(-?[0-9]+|\\(-\\s+[0-9]+\\))";
        return Pattern.compile("\\((?:<=|>=|<|>|=)\\s+(?:" + literal
                + "\\s+\\|?" + name + "\\|?|\\|?" + name + "\\|?\\s+"
                + literal + ")\\)");
    }

    /** The literals one decision of one session compares a symbol with
     *  ({@code atom}, {@link #comparing}), its term lowered by its
     *  session's lowering. */
    private Set<java.math.BigInteger> literals(Pattern atom, String sessionId,
                                               DecisionRow decision) {
        Set<java.math.BigInteger> literals =
                new java.util.TreeSet<java.math.BigInteger>();
        Matcher found = atom.matcher(FlipQuery.statedTerm(this, sessionId,
                decision.term()));
        while (found.find()) {
            String spelled = found.group(1) != null
                    ? found.group(1) : found.group(2);
            literals.add(new java.math.BigInteger(spelled
                    .replaceAll("[()\\s]", "")));
        }
        return literals;
    }
}
