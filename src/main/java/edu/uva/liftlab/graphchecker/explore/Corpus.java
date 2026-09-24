package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.DoorRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.JavaSmtSorts;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
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
 * One iteration's sessions, indexed: the ONE corpus view both stages read.
 *
 * <p>Everything either stage asks of a recording is asked here: which paths an
 * occurrence has, which interaction an attach belongs to, what some producer
 * exported at an endpoint, which write a read observed, and what a case
 * declares a root may be.  The indexes are keyed the way the contract says
 * identity works -- an interaction by BOTH its endpoints, a location by the
 * replay-stable {@link LocationId}, a symbol by the session that minted it,
 * because a raw symbol, a version id and an expression ref are all
 * session-local names.</p>
 *
 * <p>There was a second one (the composer's own {@code CorpusIndex}), and the
 * two minted a PATH IDENTITY differently -- one digested
 * {@code occurrence.render()}, this one {@code OccurrenceAddress.id()} -- so
 * the same path had two names depending on which stage was speaking, and a
 * selector, a manifest row and an obligation could not be joined.  One
 * spelling, and it is the contract's id: {@link #pathId}.</p>
 */
public final class Corpus implements Arms.Rows {
    /** One occurrence's decisions in one session: a path, as it ran. */
    public static final class RecordedPath {
        public final String pathId;
        public final String sessionId;
        public final OccurrenceAddress occurrence;
        public final List<DecisionRow> decisions;
        public final boolean focused;

        private RecordedPath(String sessionId, OccurrenceAddress occurrence,
                             List<DecisionRow> decisions, boolean focused) {
            this.pathId = pathId(sessionId, occurrence);
            this.sessionId = sessionId;
            this.occurrence = occurrence;
            this.decisions = Collections.unmodifiableList(decisions);
            this.focused = focused;
        }
    }

    /** What one raw symbol of one session names. */
    public enum SymbolKind { ROOT, HANDOFF, READ, UNKNOWN }

    /** One decision a focused replay was held to: whose, where, which arm. */
    public static final class Flip {
        /** The occurrence the flip is addressed at, by the contract's id. */
        public final String focusedOccurrenceId;
        public final String siteId;
        public final int ordinal;
        public final boolean outcome;
        /** The obligation this flip was originally asked by. */
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

    /**
     * THE WORLD one session ran in, as its own focus row states it.
     *
     * <p>A focused replay is not a variation of the recording: it is the
     * recording plus everything its obligation asked for -- the roots it
     * planted, the clocks it skewed, the handoffs it answered, and the
     * DECISIONS it was held to, its own flip and every flip it inherited.
     * A candidate cut from one of its paths inherits all of that
     * ({@link ObligationFactory#solve} merges it, {@link FlipQuery} asserts
     * it), because the path it is cut from exists only in that world: 11741's
     * witness is dn1's expiry compare flipped a second time ON the refresh
     * path a session recorded under nn0's clock skew, and a child that
     * dropped the skew would ask for a path that run never had.</p>
     *
     * <p>The SEED's world is empty -- it read its roots, answered nothing
     * and was held to no decision -- and so is the world of a session no
     * obligation worker of this iteration states a focus row for.</p>
     */
    public static final class World {
        public final Map<String, String> rootAssignments;
        public final Map<String, String> clockDeltas;
        public final Map<String, String> answers;
        public final Map<String, String> rootMints;
        /** The row's own flip first, then the flips it inherited. */
        public final List<Flip> flips;

        World(Map<String, String> rootAssignments,
              Map<String, String> clockDeltas,
              Map<String, String> answers,
              Map<String, String> rootMints,
              List<Flip> flips) {
            this.rootAssignments =
                    Collections.unmodifiableMap(rootAssignments);
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.answers = Collections.unmodifiableMap(answers);
            this.rootMints = Collections.unmodifiableMap(rootMints);
            this.flips = Collections.unmodifiableList(flips);
        }

        /** The world of the seed, and of a session with no worker. */
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
    /** One lowering per session: the cache belongs to the stage that lowers. */
    private final Map<String, SmtLowering> loweringById =
            new LinkedHashMap<String, SmtLowering>();
    /** occurrence id -> the activations of it, across sessions. */
    private final Map<String, List<ActivationRow>> activations =
            new LinkedHashMap<String, List<ActivationRow>>();
    /** session|occurrence -> that path's decisions, in recorded order. */
    private final Map<String, List<DecisionRow>> decisions =
            new LinkedHashMap<String, List<DecisionRow>>();
    /** producer endpoint id -> every export recorded at it. */
    private final Map<String, List<ExportRow>> exports =
            new LinkedHashMap<String, List<ExportRow>>();
    /** session|symbol -> the row that minted it. */
    private final Map<String, AttachRow> attachBySymbol =
            new LinkedHashMap<String, AttachRow>();
    private final Map<String, RootMintRow> rootBySymbol =
            new LinkedHashMap<String, RootMintRow>();
    private final Map<String, ReadRow> readBySymbol =
            new LinkedHashMap<String, ReadRow>();
    /** occurrence id -> the attaches, reads and writes it published. */
    private final Map<String, List<AttachRow>> attachesOn =
            new LinkedHashMap<String, List<AttachRow>>();
    private final Map<String, List<ReadRow>> readsOn =
            new LinkedHashMap<String, List<ReadRow>>();
    /** occurrence id -> the exports it published, across sessions. */
    private final Map<String, List<ExportRow>> exportsOn =
            new LinkedHashMap<String, List<ExportRow>>();
    private final Map<String, List<TargetRow>> targetsOn =
            new LinkedHashMap<String, List<TargetRow>>();
    private final Map<String, List<WriteRow>> writesOn =
            new LinkedHashMap<String, List<WriteRow>>();
    /** session|location|version -> the write that produced it. */
    private final Map<String, WriteRow> writeByVersion =
            new LinkedHashMap<String, WriteRow>();
    /** session|locationKey -> every write of it, in that session. */
    private final Map<String, List<WriteRow>> writesByLocation =
            new LinkedHashMap<String, List<WriteRow>>();
    /** interaction id -> the attaches whose own pairing names it. */
    private final Map<String, List<AttachRow>> attachesByInteraction =
            new LinkedHashMap<String, List<AttachRow>>();
    /** interaction id -> the interaction itself, for every pairing stated. */
    private final Map<String, Interaction> interactions =
            new LinkedHashMap<String, Interaction>();
    /** Every symbol the runtime declared, at the sort it minted it at. */
    private final Map<String, Sort> declaredSymbols =
            new LinkedHashMap<String, Sort>();
    /** Root symbol -> every root id declared under it. */
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();
    /** endpoint id -> the endpoint, so an anchor's producer can be found. */
    /** session|occurrence -> that session's activation of it. */
    private final Map<String, ActivationRow> activationByOccurrence =
            new LinkedHashMap<String, ActivationRow>();
    private final Map<String, Endpoint> endpointById =
            new LinkedHashMap<String, Endpoint>();
    /** node|location -> every occurrence of that node touching it. */
    private final Map<String, Set<String>> locationTouches =
            new LinkedHashMap<String, Set<String>>();
    /** root id -> its mint row per session, and every distinct reading. */
    private final Map<String, Map<String, RootMintRow>> rootsById =
            new LinkedHashMap<String, Map<String, RootMintRow>>();
    private final Map<String, OccurrenceAddress> occurrenceById =
            new LinkedHashMap<String, OccurrenceAddress>();
    /** What the case declares each root may be, by root id. */
    private final Map<String, RootDomain> declaredDomains =
            new LinkedHashMap<String, RootDomain>();

    /** session id -> the world its focus row states it ran in. */
    private final Map<String, World> worlds =
            new LinkedHashMap<String, World>();

    private final Arms arms;

    private Corpus(Path iteration, List<SessionReader> sessions) {
        this.iteration = iteration;
        this.sessions = Collections.unmodifiableList(sessions);
        for (SessionReader session : sessions) index(session);
        this.arms = new Arms(this);
    }

    /** Reads an iteration and its case-declared root domains. */
    public static Corpus read(Path iteration, Path rootDomains)
            throws IOException {
        Corpus corpus = new Corpus(iteration,
                SessionReader.readAll(iteration));
        if (rootDomains != null && Files.isRegularFile(rootDomains)) {
            corpus.declaredDomains.putAll(
                    RootDomain.declared(rootDomains));
        }
        corpus.indexWorlds(iteration);
        return corpus;
    }

    /**
     * THE WORLD each replay of this iteration ran in, off its FOCUS ROW.
     *
     * <p>A replay handed an assignment PLANTED that value: the runtime
     * writes it into the declared field ({@code
     * ConcolicRegionRuntime#applyFocusedRootAssignment}, off {@code
     * FocusedReplay#rootAssignment}), so what that replay ran the root at is
     * stated by the ASK and nowhere else, and this is where the corpus reads
     * it.  A corpus with no obligation workers -- a seed-only one -- states
     * none, and every root value is then a recording.</p>
     *
     * <p>THE FOCUS ROW and not {@code obligation.jsonl}: the focus row is
     * what the replay was DRIVEN by, and it is the only row that states the
     * whole world -- the clock skews, the mints the assignments were planted
     * at, and the flips the replay was held to, its own and the ones it
     * inherited.  The ask file states a subset of it (no clocks, no flips),
     * and reading a world out of a subset is how a child of a skewed replay
     * came to be asked for under no skew at all.</p>
     */
    private void indexWorlds(Path iteration) throws IOException {
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            for (JsonObject row : RowCodec.readJsonl(worker.focusedTask())) {
                worlds.put(worker.sessionId(),
                        ExploreCodec.readWorld(row));
            }
            for (ObligationResult result : RowCodec.readAll(worker.result(),
                    RowCodec::readObligationResult)) {
                waveVerdicts.put(result.obligationId(), result);
            }
        }
    }

    /**
     * The world one session ran in; empty for the seed and for a session no
     * worker of this iteration states a focus row for.
     */
    public World world(String sessionId) {
        World stated = worlds.get(sessionId == null ? "" : sessionId);
        return stated == null ? World.empty() : stated;
    }

    /**
     * WHAT ONE SESSION'S WORLD DELIVERED TO A TASK, as a digest: the world
     * part of an arm's key ({@link ObligationFactory#worldKey}).
     *
     * <p>A world is asked about an arm again where it changed what the
     * region received, and two worlds that changed it the same way ask it
     * the same question -- so the key is the EFFECT at the task, never the
     * cause.  The occurrence itself is not the whole region: a factor member
     * is state-connected to it -- the writers and readers of one location on
     * one node, the {@code Task.factor()} list the planner computes with
     * {@code ClosurePlanner.stateConnected} -- and the two run as ONE
     * symbolic unit, so what the member received and wrote is what the
     * occurrence reads.  HDFS-11741 is the case: dn1's expiry scan runs over
     * the DataNode's own old map BEFORE the put loop, so its own decisions
     * are letter for letter the seed's whether or not nn0 skewed its clock;
     * what nn0's flip changed is the {@code addKeys} occurrence beside it
     * (four attaches instead of five), and addKeys writes the very map the
     * scan reads.</p>
     *
     * <p><b>WHAT ARRIVES, never what the region does with it.</b> At the
     * occurrence and at every factor member: whether it ran, and per site
     * how many handoffs it received from which producer occurrences.  At
     * every other factor member, also how many writes it made per site --
     * the state the occurrence reads is what its factor writes, and whether
     * a write carries a delivered value or a constant is what the member
     * received.  A region's own reads and decisions are its BEHAVIOUR, not
     * its input: how often a loop reads a field is the path the prefix already
     * names, and counting it split one world into as many keys as a
     * replay's timing produced -- on hdfs-11741 round v38, 57 of 103
     * (task, world) groups with more than one session, 84 of their 99
     * differences in per-site read counts.</p>
     *
     * <p>A delivered VALUE is not in it either.  Values are carried
     * symbolically by the families -- that is what a handoff's arm is for
     * -- and a clock-valued handoff is a different value in every run by
     * nature, for reasons no flip caused.</p>
     *
     * <p>Keyed by the CAUSE -- the flips of the world that reach the task
     * over the corpus's causal graph -- one question was asked once per
     * combination of upstream flips that delivered the task the same
     * structure, and one structure per combination was asked at all.  A
     * world whose flips changed nothing the task received digests as the
     * seed does, so the seed's recorded arms settle it.</p>
     */
    public String inputShape(String sessionId, OccurrenceAddress occurrence,
                             List<OccurrenceAddress> factor) {
        StringBuilder text = new StringBuilder();
        if (occurrence != null) {
            text.append(occurrence.id()).append(':')
                    .append(activation(sessionId, occurrence) != null)
                    .append(attachSites(sessionId, occurrence))
                    .append(producers(sessionId, occurrence));
        }
        if (factor != null) {
            for (OccurrenceAddress member : factor) {
                if (member == null || member.equals(occurrence)) continue;
                text.append('\n').append(member.id()).append(':')
                        .append(activation(sessionId, member) != null)
                        .append(attachSites(sessionId, member))
                        .append(producers(sessionId, member))
                        .append(writeSites(sessionId, member));
            }
        }
        return ArtifactIO.digest(text.toString(), 16);
    }

    /** HOW MANY handoffs arrived here, per site: the count, not the value. */
    private List<String> attachSites(String sessionId,
                                     OccurrenceAddress occurrence) {
        List<String> sites = new ArrayList<String>();
        for (AttachRow attach : attachesOn(sessionId, occurrence)) {
            sites.add(attach.endpoint().site());
        }
        Collections.sort(sites);
        return sites;
    }

    /** WHICH occurrences delivered them: a new producer is new topology. */
    private Set<String> producers(String sessionId,
                                  OccurrenceAddress occurrence) {
        Set<String> from = new LinkedHashSet<String>();
        for (AttachRow attach : attachesOn(sessionId, occurrence)) {
            Endpoint producer = attach.producer();
            if (producer == null) continue;
            OccurrenceAddress at = producer.occurrence();
            from.add(at == null ? producer.id() : at.id());
        }
        return from;
    }

    /** HOW MANY writes it made, per site: the count, not the value. */
    private List<String> writeSites(String sessionId,
                                    OccurrenceAddress occurrence) {
        List<String> sites = new ArrayList<String>();
        for (WriteRow write : writesOn(occurrence)) {
            if (!write.sessionId().equals(sessionId)) continue;
            sites.add(write.endpoint().site());
        }
        Collections.sort(sites);
        return sites;
    }

    /**
     * What the WAVE's own file says one obligation settled, or null.
     *
     * <p>Kept only to be checked against the SESSION's row, which is the
     * verdict: the replay owns whether the focused prefix reproduced.  The
     * campaign shell used to stamp {@code verdict: "ADMITTED"} onto this
     * copy after every replay that merely finished, so on hdfs-11741
     * campaign #3 six of eleven obligations were aggregated ADMITTED while
     * their own sessions said NOT_ADMITTED -- and the composition took all
     * eleven as paths.  A corpus that states one verdict twice and
     * differently is refused by name.</p>
     */
    public ObligationResult waveVerdict(String obligationId) {
        return waveVerdicts.get(obligationId == null ? "" : obligationId);
    }

    /** Obligation id -> the verdict the wave's own file states. */
    private final Map<String, ObligationResult> waveVerdicts =
            new LinkedHashMap<String, ObligationResult>();

    /**
     * The directory the sessions were read from.
     *
     * <p>What else the epoch published sits beside them -- the slot table is
     * the one this stage reads -- so a corpus states where it came from
     * rather than having every caller carry the path a second time.</p>
     */
    public Path iteration() {
        return iteration;
    }

    /** Producer endpoint id -> the occurrence whose door sent it. */
    private final Map<String, String> senderByEndpoint =
            new LinkedHashMap<String, String>();
    /** Producer endpoint id -> the occurrence whose door took it in. */
    private final Map<String, String> receiverByEndpoint =
            new LinkedHashMap<String, String>();

    /**
     * The occurrence that sent the message a consumer served under
     * {@code producerEndpointId} (its ANCHOR), or null: the sending door
     * states the producer endpoint the message carried ({@link DoorRow}).
     */
    public OccurrenceAddress senderOf(String producerEndpointId) {
        String sender = senderByEndpoint.get(producerEndpointId);
        return sender == null ? null : occurrenceById.get(sender);
    }

    /**
     * The occurrence that TOOK IN the message a consumer served under
     * {@code producerEndpointId}, or null: the receiving door stands in
     * that occurrence, and its receive-side fault point decides whether the
     * reply is delivered at all (DESIGN4 SS1.2).
     */
    public OccurrenceAddress receiverOf(String producerEndpointId) {
        String receiver = receiverByEndpoint.get(producerEndpointId);
        return receiver == null ? null : occurrenceById.get(receiver);
    }

    private void indexDoors(SessionReader session) {
        for (DoorRow door : session.doors()) {
            if (door.kind() == DoorRow.Kind.SEND) {
                senderByEndpoint.put(door.endpoint(), door.occurrence());
            } else {
                receiverByEndpoint.put(door.endpoint(), door.occurrence());
            }
        }
    }

    private void index(SessionReader session) {
        indexDoors(session);
        sessionById.put(session.sessionId(), session);
        loweringById.put(session.sessionId(), SmtLowering.forSession(session));
        for (ActivationRow row : session.activations()) {
            activationByOccurrence.put(session.sessionId() + "|"
                    + row.occurrence().id(), row);
            remember(occurrenceById, row.occurrence());
            add(activations, row.occurrence().id(), row);
        }
        for (DecisionRow row : session.decisions()) {
            remember(occurrenceById, row.occurrence());
            add(decisions, session.sessionId() + "|" + row.occurrence().id(), row);
            // A decision carries the clock cells it read: each is a symbol
            // of the corpus, at Int.  What a session read of it is the
            // mint's row; the composer domains clocks from the roots.
            for (String cell : row.clockReadings().keySet()) {
                declaredSymbols.put(cell, Sort.INT);
            }
        }
        for (ExportRow row : session.exports()) {
            remember(occurrenceById, row.endpoint().occurrence());
            endpointById.put(row.endpoint().id(), row.endpoint());
            add(exports, row.endpoint().id(), row);
            add(exportsOn, row.endpoint().occurrence().id(), row);
        }
        for (AttachRow row : session.attaches()) {
            remember(occurrenceById, row.endpoint().occurrence());
            endpointById.put(row.endpoint().id(), row.endpoint());
            if (row.producer() != null) {
                endpointById.put(row.producer().id(), row.producer());
                remember(occurrenceById, row.producer().occurrence());
            }
            attachBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            Interaction interaction = row.interaction();
            if (interaction != null) {
                interactions.put(interaction.id(), interaction);
                add(attachesByInteraction, interaction.id(), row);
            }
            add(attachesOn, row.endpoint().occurrence().id(), row);
            // The JVM descriptor the mint states, never the spelling of one
            // value it carried: one variable has one sort.
            declaredSymbols.put(row.symbol(),
                    JavaSmtSorts.sortOfJava(row.javaType()));
        }
        for (RootMintRow row : session.roots()) {
            remember(occurrenceById, row.occurrence());
            rootBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            Map<String, RootMintRow> bySession = rootsById.get(row.rootId());
            if (bySession == null) {
                bySession = new LinkedHashMap<String, RootMintRow>();
                rootsById.put(row.rootId(), bySession);
            }
            bySession.put(session.sessionId(), row);
            Set<String> ids = rootIdsBySymbol.get(row.symbol());
            if (ids == null) {
                ids = new LinkedHashSet<String>();
                rootIdsBySymbol.put(row.symbol(), ids);
            }
            ids.add(row.rootId());
            declaredSymbols.put(row.symbol(),
                    row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT);
        }
        for (WriteRow row : session.writes()) {
            remember(occurrenceById, row.endpoint().occurrence());
            writeByVersion.put(versionKey(session.sessionId(),
                    SmtLowering.locationKey(row.location()),
                    row.version()), row);
            add(writesOn, row.endpoint().occurrence().id(), row);
            add(writesByLocation, session.sessionId() + "|"
                    + SmtLowering.locationKey(row.location()), row);
            endpointById.put(row.endpoint().id(), row.endpoint());
            touch(row.endpoint().occurrence(), row.location());
        }
        for (TargetRow row : session.targets()) {
            remember(occurrenceById, row.occurrence());
            add(targetsOn, row.occurrence().id(), row);
        }
        for (ReadRow row : session.reads()) {
            remember(occurrenceById, row.endpoint().occurrence());
            if (!row.symbol().isEmpty()) {
                readBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            }
            add(readsOn, row.endpoint().occurrence().id(), row);
            endpointById.put(row.endpoint().id(), row.endpoint());
            touch(row.endpoint().occurrence(), row.location());
        }
    }

    private void touch(OccurrenceAddress occurrence, LocationId location) {
        String key = occurrence.node().render() + "|"
                + SmtLowering.locationKey(location);
        Set<String> occurrences = locationTouches.get(key);
        if (occurrences == null) {
            occurrences = new LinkedHashSet<String>();
            locationTouches.put(key, occurrences);
        }
        occurrences.add(occurrence.id());
    }

    private static void remember(Map<String, OccurrenceAddress> into,
                                 OccurrenceAddress occurrence) {
        if (occurrence != null) into.put(occurrence.id(), occurrence);
    }

    private static <T> void add(Map<String, List<T>> into, String key, T row) {
        List<T> rows = into.get(key);
        if (rows == null) {
            rows = new ArrayList<T>();
            into.put(key, rows);
        }
        rows.add(row);
    }

    /**
     * One version of one location, inside one session.
     *
     * <p>{@link SmtLowering#locationKey} is the one spelling of a location
     * in this tree -- the write log, the VM's own location node and every
     * index here -- because a key that differed between them would silently
     * make a state join miss.</p>
     */
    private static String versionKey(String sessionId, String locationKey,
                                     long version) {
        return sessionId + "|" + locationKey + "|" + version;
    }

    /** One path's id: the session it ran in and the occurrence it ran. */
    public static String pathId(String sessionId,
                                OccurrenceAddress occurrence) {
        return ArtifactIO.digest(sessionId + "|" + occurrence.id(), 16);
    }

    /**
     * Which session is the recording, or "" when that has no answer.
     *
     * <p>One rule, stated once in the contract: the recording is the session
     * whose manifest states {@code role: SEED}.  A corpus with none of those,
     * or with more than one, does not state which recording a declaration was
     * written about, and the caller refuses with a named gap -- naming an
     * exploration replay as the recording is how a claim comes to be about
     * the wrong execution.</p>
     */
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

    public List<SessionReader> sessions() {
        return sessions;
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

    /**
     * Every path of one occurrence: one per session that ran it.
     *
     * <p>A session that activated the occurrence but decided nothing still
     * has a path -- an empty one -- because "this occurrence ran here" is
     * what admission is about, and its absence is what a divergence is.
     * Three kinds of row say it ran: the activation, a decision taken in
     * it, and a TARGET row published at it -- a session that reached an
     * anchor deciding nothing on the way has a path there, the empty
     * conjunction, and the target row is what says so.</p>
     */
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
                taken == null ? new ArrayList<DecisionRow>() : taken,
                activation != null && activation.focused());
    }

    public ActivationRow activation(String sessionId,
                                    OccurrenceAddress occurrence) {
        List<ActivationRow> rows = activations.get(occurrence.id());
        if (rows == null) return null;
        for (ActivationRow row : rows) {
            if (row.sessionId().equals(sessionId)) return row;
        }
        return null;
    }

    public List<DecisionRow> decisionsOf(String sessionId,
                                         OccurrenceAddress occurrence) {
        List<DecisionRow> rows = decisions.get(
                sessionId + "|" + occurrence.id());
        return rows == null ? Collections.<DecisionRow>emptyList() : rows;
    }

    /** Every export any session recorded at one producer endpoint. */
    public List<ExportRow> exportsAt(Endpoint producer) {
        if (producer == null) return Collections.emptyList();
        List<ExportRow> rows = exports.get(producer.id());
        return rows == null ? Collections.<ExportRow>emptyList() : rows;
    }

    public List<AttachRow> attachesOn(OccurrenceAddress occurrence) {
        List<AttachRow> rows = attachesOn.get(occurrence.id());
        return rows == null ? Collections.<AttachRow>emptyList() : rows;
    }

    /** Every target row published for one occurrence, in any session. */
    public List<TargetRow> targetsOn(OccurrenceAddress occurrence) {
        List<TargetRow> rows = targetsOn.get(occurrence.id());
        return rows == null ? Collections.<TargetRow>emptyList() : rows;
    }

    /** One session's target row at one occurrence, or null. */
    public TargetRow target(String sessionId, OccurrenceAddress occurrence) {
        for (TargetRow row : targetsOn(occurrence)) {
            if (row.sessionId().equals(sessionId)) return row;
        }
        return null;
    }

    public List<ReadRow> readsOn(OccurrenceAddress occurrence) {
        List<ReadRow> rows = readsOn.get(occurrence.id());
        return rows == null ? Collections.<ReadRow>emptyList() : rows;
    }

    /** Every attach of ONE session whose consumer sits at this occurrence. */
    public List<AttachRow> attachesOn(String sessionId,
                                      OccurrenceAddress occurrence) {
        List<AttachRow> own = new ArrayList<AttachRow>();
        for (AttachRow row : attachesOn(occurrence)) {
            if (row.sessionId().equals(sessionId)) own.add(row);
        }
        return own;
    }

    /** Every read ONE session made at this occurrence, in recorded order. */
    public List<ReadRow> readsOn(String sessionId,
                                 OccurrenceAddress occurrence) {
        List<ReadRow> own = new ArrayList<ReadRow>();
        for (ReadRow row : readsOn(occurrence)) {
            if (row.sessionId().equals(sessionId)) own.add(row);
        }
        return own;
    }

    public List<WriteRow> writesOn(OccurrenceAddress occurrence) {
        List<WriteRow> rows = writesOn.get(occurrence.id());
        return rows == null ? Collections.<WriteRow>emptyList() : rows;
    }

    /** Every export any session published at one occurrence. */
    public List<ExportRow> exportsOn(OccurrenceAddress occurrence) {
        List<ExportRow> rows = exportsOn.get(occurrence.id());
        return rows == null ? Collections.<ExportRow>emptyList() : rows;
    }

    // ---- The causal graph: which occurrences reach which (SS3.1) -------

    /**
     * The writes one read could have taken its value from.
     *
     * <p>The observed one, and every write by an occurrence HB-CONCURRENT
     * with the reader (R-I7.1) -- the CANDIDATE shared-state dependency,
     * which is the same set the composition offers the solver as
     * alternatives, because the rule is {@code smt.Arms}'.  ONE
     * implementation: the closure grows by it
     * ({@link ClosurePlanner#writers}, through
     * {@code ClosurePlanner.eligibleWrites}) and the causal graph's
     * shared-state in-edge is it ({@link #upstreamOf}), so "which writer
     * could this read have observed" has one answer in this stage.</p>
     *
     * @param reader the occurrence that made the read, for the concurrency
     *               rule; the version is the one it observed
     */
    public List<WriteRow> eligibleWrites(String sessionId, String locationKey,
                                         long observedVersion,
                                         OccurrenceAddress reader) {
        List<WriteRow> eligible = new ArrayList<WriteRow>();
        for (WriteRow write : writesOf(sessionId, locationKey)) {
            if (write.version() == observedVersion
                    || arms.concurrent(reader,
                            write.endpoint().occurrence(), sessionId)) {
                eligible.add(write);
            }
        }
        return eligible;
    }

    /**
     * EVERY OCCURRENCE THAT REACHES ONE AND ITS FACTOR, itself included,
     * INSIDE ONE SESSION's rows (DESIGN4 SS3.2): the per-world graph, from
     * which the regions a world exposed are read.
     *
     * <p>The in-edges are the paper's (SS3.1): a MATCHED COMMUNICATION
     * TRANSFER -- an attach and the producer occurrence its own pairing
     * names -- and a CANDIDATE SHARED-STATE DEPENDENCY -- a read of a
     * concrete location and the occurrences that wrote the versions it
     * could have observed, on the reader's own node ({@link #eligibleWrites},
     * {@link #observed}); a read stated only inside a published expression
     * (E2, {@link #expressionStateReads}) is one of those reads.  Not
     * memoized: asked once per admitted session per wave.</p>
     */
    public Set<String> upstreamOf(OccurrenceAddress occurrence,
                                  List<OccurrenceAddress> factor,
                                  String sessionId) {
        Set<String> reached = closure(occurrence, sessionId);
        if (factor != null) {
            for (OccurrenceAddress member : factor) {
                reached.addAll(closure(member, sessionId));
            }
        }
        return reached;
    }

    /** The walk behind it, over one session's edges. */
    private Set<String> closure(OccurrenceAddress occurrence,
                                String sessionId) {
        Set<String> reached = new LinkedHashSet<String>();
        Deque<OccurrenceAddress> pending = new ArrayDeque<OccurrenceAddress>();
        reached.add(occurrence.id());
        pending.add(occurrence);
        while (!pending.isEmpty()) {
            OccurrenceAddress at = pending.remove();
            for (String next : reaches(at, sessionId)) {
                if (!reached.add(next)) continue;
                OccurrenceAddress address = occurrenceById.get(next);
                if (address != null) pending.add(address);
            }
        }
        return reached;
    }

    /** One occurrence's in-edges in one session: who delivered to it, who
     *  wrote for it. */
    private Set<String> reaches(OccurrenceAddress occurrence,
                                String sessionId) {
        Set<String> in = new LinkedHashSet<String>();
        for (AttachRow attach : attachesOn(occurrence)) {
            if (attach.producer() == null
                    || !sessionId.equals(attach.sessionId())) {
                continue;
            }
            OccurrenceAddress producer = attach.producer().occurrence();
            if (producer != null) in.add(producer.id());
        }
        for (ReadRow read : readsOn(occurrence)) {
            if (!sessionId.equals(read.sessionId())) continue;
            observed(read.sessionId(), SmtLowering.locationKey(read.location()),
                    read.observedVersion(), occurrence, in);
        }
        // E2: the shared state a delivery this occurrence made RESTS ON,
        // which only its expression states.
        Set<String> walked = new LinkedHashSet<String>();
        for (ExportRow export : exportsOn(occurrence)) {
            if (!sessionId.equals(export.sessionId())) continue;
            stated(export.sessionId(), export.expressionRef(), occurrence,
                    walked, in);
        }
        for (WriteRow write : writesOn(occurrence)) {
            if (!sessionId.equals(write.sessionId())) continue;
            stated(write.sessionId(), write.expressionRef(), occurrence,
                    walked, in);
        }
        return in;
    }

    /** The reads one published expression states, and who wrote them. */
    private void stated(String sessionId, String expressionRef,
                        OccurrenceAddress reader, Set<String> walked,
                        Set<String> into) {
        if (expressionRef == null || expressionRef.isEmpty()) return;
        if (!walked.add(sessionId + "|" + expressionRef)) return;
        for (StateRead read : expressionStateReads(sessionId, expressionRef)) {
            observed(sessionId, read.locationKey(), read.write().version(),
                    reader, into);
        }
    }

    /**
     * The occurrences that wrote what one read could have observed, ON THE
     * READER'S OWN NODE (N1: a location key is minted per JVM, so two
     * processes both holding {@code INSTANCE/36#72} hold two objects, and
     * cross-node influence is carried by the transfer edge alone).
     */
    private void observed(String sessionId, String locationKey, long version,
                          OccurrenceAddress reader, Set<String> into) {
        for (WriteRow write : eligibleWrites(sessionId, locationKey, version,
                reader)) {
            OccurrenceAddress writer = write.endpoint().occurrence();
            if (writer == null) continue;
            if (reader != null && !reader.node().equals(writer.node())) {
                continue;
            }
            into.add(writer.id());
        }
    }

    /**
     * Whether one decision is a FAULT decision: its term rests on a MARKER
     * root the same session minted (DESIGN4 SS1.4).  The runtime publishes
     * a predicate over a propagated value as a reference into the
     * expression table, so the term is lowered first and the roots it
     * REACHES are asked, not the tokens it shows.
     */
    public boolean fault(String sessionId, DecisionRow decision) {
        SmtLowering lowering = lowering(sessionId);
        if (lowering == null || !Arms.predicate(decision.term())) return false;
        Set<String> reached = new LinkedHashSet<String>();
        lowering.reachedSymbols(FlipQuery.statedTerm(this, sessionId,
                decision.term()), reached, reached);
        for (String symbol : reached) {
            RootMintRow root = rootBySymbol(sessionId, symbol);
            if (root != null && root.kind() == RootKind.MARKER) return true;
        }
        return false;
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

    /**
     * Whether some session ran one region INSTRUMENTED: the weave has it.
     * An ambient activation ({@code instrumented=false}) says only that the
     * region RAN; a region no session ran instrumented is one the weave
     * does not hold, and an admitted replay reaching it is growth
     * (DESIGN4 SS3.3b).
     */
    public boolean woven(String regionId) {
        for (List<ActivationRow> rows : activations.values()) {
            for (ActivationRow row : rows) {
                if (row.instrumented()
                        && row.occurrence().regionId().equals(regionId)) {
                    return true;
                }
            }
        }
        return false;
    }

    // ---- Arms.Rows: what the shared arm builder asks of a corpus -------

    @Override
    public JsonObject expression(String sessionId, String expressionRef) {
        SessionReader session = sessionById.get(sessionId);
        return session == null || expressionRef == null ? null
                : session.expressions().expression(expressionRef);
    }

    /** One session's expression table, as its own terms name it. */
    public ExpressionTable expressions(String sessionId) {
        SessionReader session = sessionById.get(sessionId);
        return session == null ? null : session.expressions();
    }

    /** How deep one expression is walked for the state reads inside it. */
    private static final int EXPRESSION_DEPTH = 64;

    /**
     * One shared-state read a published expression states, and the version
     * of that location the producer had in hand when it read.
     */
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

        /** The location, spelled the way a row and a join both spell it. */
        public String locationKey() {
            return locationKey;
        }

        /** The event id the expression states the read happened at. */
        public long readEventId() {
            return readEventId;
        }

        /** The latest write of that location at or before the read. */
        public WriteRow write() {
            return write;
        }
    }

    /**
     * The shared state one published expression rests on.
     *
     * <p>An expression that projects a value out of shared state names the
     * READ it made -- a {@code ReadFromExpression}, or the
     * {@code ConsumerBoundaryExpression} over one, carrying a
     * {@code location} and a {@code readEventId} -- and never the write
     * that produced that state.  What a closure and a composed arm both
     * need is the WRITE: the latest version of that location at or before
     * the read is the state the producer had in hand, and its writer's
     * prefix is a reason the delivered value is what it is.  On hdfs-11741
     * the NameNode's export reads its key map at event 599; the write it
     * rests on is version 589, the last of the previous tick.</p>
     *
     * <p>ONE implementation of that resolution, because two would be two
     * answers to "what state is this delivery made of": the composer closes
     * an arm with it ({@code ComposedFamilies.expressionWrites}) and the
     * closure grows by it ({@code ClosurePlanner.successors}, E2).</p>
     *
     * <p>Only reads whose location this session actually wrote are
     * returned: a location no write row of the session names has no version
     * to have been read at, and guessing one would state a reason nothing
     * recorded.</p>
     */
    public List<StateRead> expressionStateReads(String sessionId,
                                                String expressionRef) {
        List<StateRead> found = new ArrayList<StateRead>();
        JsonObject expression = expression(sessionId, expressionRef);
        if (expression == null) return found;
        Map<String, Long> read = new LinkedHashMap<String, Long>();
        readNodes(expression, read, 0);
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
        return found;
    }

    /**
     * Location key -> the latest event id one expression read it at.
     *
     * <p>Every node that carries both a {@code location} and a
     * {@code readEventId} states a read of shared state, whatever else the
     * node is -- which is what a {@code ReadFromExpression} and the
     * {@code ConsumerBoundaryExpression} over one are.</p>
     */
    private static void readNodes(JsonElement expression,
                                  Map<String, Long> into, int depth) {
        if (expression == null || depth > EXPRESSION_DEPTH) return;
        if (expression.isJsonArray()) {
            for (JsonElement each : expression.getAsJsonArray()) {
                readNodes(each, into, depth + 1);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject node = expression.getAsJsonObject();
        JsonElement location = node.get("location");
        JsonElement at = node.get("readEventId");
        if (location != null && location.isJsonObject() && at != null
                && at.isJsonPrimitive()) {
            String key = SmtLowering.locationKey(location.getAsJsonObject());
            long event = at.getAsLong();
            Long held = into.get(key);
            if (held == null || held.longValue() < event) {
                into.put(key, Long.valueOf(event));
            }
        }
        for (Map.Entry<String, JsonElement> member : node.entrySet()) {
            readNodes(member.getValue(), into, depth + 1);
        }
    }

    /** Every interaction any session's own pairing states. */
    public Map<String, Interaction> interactions() {
        return Collections.unmodifiableMap(interactions);
    }

    /** Every symbol the runtime declared, at the sort it minted it at. */
    public Map<String, Sort> declaredSymbols() {
        return Collections.unmodifiableMap(declaredSymbols);
    }

    /**
     * Root symbols naming more than one root: a name collision.
     *
     * <p>One solver name for two roots makes one term carry two quantities,
     * and every path that read them both is then unsatisfiable at its own
     * valuation.  It is the runtime's to fix and the composition's to
     * refuse, so the corpus states it rather than either stage deriving
     * it.</p>
     */
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
        List<AttachRow> rows = attachesByInteraction.get(interaction.id());
        return rows == null ? Collections.<AttachRow>emptyList() : rows;
    }

    @Override
    public List<ExportRow> exportsOf(Endpoint producer) {
        return exportsAt(producer);
    }

    @Override
    public List<WriteRow> writesOf(String sessionId, String locationKey) {
        List<WriteRow> writes = writesByLocation.get(
                sessionId + "|" + locationKey);
        return writes == null ? Collections.<WriteRow>emptyList() : writes;
    }

    @Override
    public String pathIdOf(String sessionId, OccurrenceAddress occurrence) {
        return pathId(sessionId, occurrence);
    }

    @Override
    public RootMintRow root(String rootId, String sessionId) {
        return rootOf(sessionId, rootId);
    }

    @Override
    public Map<String, List<RootMintRow>> roots() {
        Map<String, List<RootMintRow>> byRoot =
                new LinkedHashMap<String, List<RootMintRow>>();
        for (Map.Entry<String, Map<String, RootMintRow>> entry
                : rootsById.entrySet()) {
            byRoot.put(entry.getKey(),
                    new ArrayList<RootMintRow>(entry.getValue().values()));
        }
        return byRoot;
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

    /** The arm builder both stages construct their families with. */
    public Arms arms() {
        return arms;
    }

    /** The write one read observed, inside that read's own session. */
    public WriteRow writeOf(String sessionId, LocationId location,
                            long version) {
        return writeOf(sessionId, SmtLowering.locationKey(location), version);
    }

    /** The same, for a caller that already holds the location's key. */
    public WriteRow writeOf(String sessionId, String locationKey,
                            long version) {
        return version < 0 ? null : writeByVersion.get(
                versionKey(sessionId, locationKey, version));
    }

    /** Every occurrence of one node that writes or reads one location. */
    public Set<String> touching(OccurrenceAddress occurrence,
                                LocationId location) {
        Set<String> found = locationTouches.get(
                occurrence.node().render() + "|"
                        + SmtLowering.locationKey(location));
        return found == null ? Collections.<String>emptySet() : found;
    }

    public AttachRow attach(String sessionId, String symbol) {
        return attachBySymbol.get(sessionId + "|" + symbol);
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

    /**
     * What one session RAN one root at, or {@code ""} when it states none.
     *
     * <p>ONE NOTION, because everything a path says about a root is said
     * over it: what the path's own {@code valuation_p} pins, what an arm
     * the path rests on is guarded by, whether the corpus {@link #varied}
     * this root at all, and what an obligation's model is compared against.
     * They must agree, so they are one method.</p>
     *
     * <p>Two ways a replay comes to run a root at a value, and the
     * recording states exactly one of them per replay.  A replay that READ
     * the root states it on the mint ({@code recordedValue}).  A replay
     * that PLANTED it -- the wave wrote the value into the declared field
     * before the mint -- states NO recordedValue by rule (a counterfactual
     * is not a recording), and what it ran under is the ASK: the {@code
     * rootAssignments} of the obligation whose result names this session.
     * Reading only the mint left a flip replay's own valuation stated
     * nowhere: on the 05f4bf265 17960 corpus the two flip sessions' mints
     * state {@code ""}, no path's formula named the marker, no valuation of
     * it was asked, and the composition published MESSAGE_PAIRING_FLIPPED
     * at the recorded valuation over a corpus with no wire row in it.</p>
     *
     * <p>The ask is preferred where both are stated: the value the replay
     * was handed is what it ran under, and a mint that states one too has
     * read the plant back.</p>
     */
    @Override
    public String rootValue(String sessionId, String rootId) {
        String wave = world(sessionId).rootAssignments.get(rootId);
        if (wave != null && !wave.isEmpty()) return wave;
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        RootMintRow row = bySession == null ? null : bySession.get(sessionId);
        return row == null || row.recordedValue() == null
                ? "" : row.recordedValue();
    }

    /**
     * What one session's MINT states it read, or {@code ""}.
     *
     * <p>Told apart from {@link #rootValue} on purpose: this is the
     * recording's own reading, which a refusal needs in order to say that
     * it disagrees with the ask.</p>
     */
    public String rootReading(String sessionId, String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        RootMintRow row = bySession == null ? null : bySession.get(sessionId);
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

    /**
     * What one root may be, as an absolute {@code [min, max]}, or null when
     * the case declares no domain and the runtime published none.
     *
     * <p>The case file is the authority; a bound written {@code +k} or
     * {@code -k} is that many steps from what the recording read, which is
     * the only way a case can state the domain of a counter whose zero
     * nobody chose.  A root with no domain is pinned everywhere -- here and
     * in the composition -- so exploration never spends a wave on a move the
     * composition cannot accept.</p>
     */
    /** What the CASE declares for one root, or null when it declares none. */
    public RootDomain declaredDomain(String rootId) {
        return declaredDomains.get(rootId);
    }

    /** The window this root may move in, or null when it is pinned. */
    public String[] domainOf(RootMintRow root) {
        // A CLOCK has a floor and no window: every execution reads it fresh,
        // so it is never an equality between paths (FlipQuery's rule).
        if (root == null || root.kind() == RootKind.CLOCK) return null;
        RootDomain domain = RootDomain.resolved(root, declaredDomains);
        return domain.min() == null || domain.max() == null ? null
                : new String[]{domain.min(), domain.max()};
    }
}
