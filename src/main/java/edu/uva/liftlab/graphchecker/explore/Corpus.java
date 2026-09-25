package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
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
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.io.UncheckedIOException;
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
     *  planted roots, clock skews, answers and the flips it was held to (own
     *  and inherited). A path cut from it exists only there, so a child
     *  inherits all of it ({@link ObligationFactory#solve} merges, {@link
     *  FlipQuery} asserts). Empty for the seed and for sessions no worker
     *  states a focus row for. */
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
    /** One state join per session, shared by the composer and the flip
     *  lowering. */
    private final Map<String, SmtLowering.SessionJoin> joinById =
            new LinkedHashMap<String, SmtLowering.SessionJoin>();
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
    private final Map<String, RootMintRow> rootBySymbol =
            new LinkedHashMap<String, RootMintRow>();
    private final Map<String, ReadRow> readBySymbol =
            new LinkedHashMap<String, ReadRow>();
    /** occurrence id -> its attaches, reads and writes. */
    private final Map<String, List<AttachRow>> attachesOn =
            new LinkedHashMap<String, List<AttachRow>>();
    private final Map<String, List<ReadRow>> readsOn =
            new LinkedHashMap<String, List<ReadRow>>();
    /** occurrence id -> its exports, across sessions. */
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
    /** session|occurrence -> that session's activation of it. */
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
    /** What the case declares each root may be, by root id. */
    private final Map<String, RootDomain> declaredDomains =
            new LinkedHashMap<String, RootDomain>();

    /** session id -> the world its focus row states it ran in. */
    private final Map<String, World> worlds =
            new LinkedHashMap<String, World>();
    /** Obligation id -> the verdict the wave's own file states. */
    private final Map<String, ObligationResult> waveVerdicts =
            new LinkedHashMap<String, ObligationResult>();
    /** Producer endpoint id of a SEND -> the occurrence that sent it. */
    private final Map<String, String> senderByEndpoint =
            new LinkedHashMap<String, String>();
    /** Producer endpoint id of a RECV -> the occurrence that took it in. */
    private final Map<String, String> receiverByEndpoint =
            new LinkedHashMap<String, String>();

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

    /** The world of each replay, off its FOCUS ROW (not {@code
     *  obligation.jsonl}, a subset without clocks or flips: reading a world
     *  from it drops skews). A planted assignment is stated by the ask alone
     *  ({@code ConcolicRegionRuntime#applyFocusedRootAssignment}). */
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

    /** The world one session ran in; empty for the seed or a session with no
     *  focus row. */
    public World world(String sessionId) {
        World stated = worlds.get(sessionId == null ? "" : sessionId);
        return stated == null ? World.empty() : stated;
    }

    /**
     * WHAT ONE SESSION'S WORLD DELIVERED TO A TASK, digested: the world part of
     * an arm's key ({@link ObligationFactory#worldKey}). The EFFECT at the
     * task, never the cause (keying by upstream flips asks one question per
     * flip combination).
     *
     * <p>Covers the occurrence and its factor ({@code Task.factor()}, one
     * symbolic unit): whether each ran, and per site how many handoffs from
     * which producers; for factor members also per-site write counts. Trap:
     * never the region's own reads or decisions (behaviour, not input; replay
     * timing would split one world into many keys) and never delivered VALUES
     * (carried symbolically; clock values differ every run).</p>
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

    /** Which occurrences delivered them: a new producer is new topology. */
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

    /** Per-site write counts (not values). */
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

    /** The occurrence that TOOK IN the message served under {@code
     *  producerEndpointId} (its RECV runs under that anchor), or null: the
     *  receiving door whose fault point decides delivery (DESIGN4 SS1.2). */
    public OccurrenceAddress receiverOf(String producerEndpointId) {
        String receiver = receiverByEndpoint.get(producerEndpointId);
        return receiver == null ? null : occurrenceById.get(receiver);
    }

    private void indexSchedule(SessionReader session) {
        List<ScheduleEvent> events;
        try {
            events = session.schedule();
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        for (ScheduleEvent event : events) {
            if (event.occurrence().isEmpty()) continue;
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                senderByEndpoint.put(event.endpoint(), event.occurrence());
            } else if (event.kind() == ScheduleEvent.Kind.RECV) {
                // "node|Anchor:<producer endpoint>@<site>[|handoffs]"
                String[] parts = event.context().split("\\|", -1);
                CausalContext anchor = CausalContext.parse(
                        parts.length < 2 ? parts[0] : parts[1]);
                if (anchor instanceof CausalContext.Anchor) {
                    receiverByEndpoint.put(((CausalContext.Anchor) anchor)
                            .producerEndpointId(), event.occurrence());
                }
            }
        }
    }

    private void index(SessionReader session) {
        indexSchedule(session);
        sessionById.put(session.sessionId(), session);
        SmtLowering.SessionJoin join = SmtLowering.joinOf(session);
        joinById.put(session.sessionId(), join);
        loweringById.put(session.sessionId(),
                SmtLowering.forSession(session, join));
        for (ActivationRow row : session.activations()) {
            activationByOccurrence.put(session.sessionId() + "|"
                    + row.occurrence().id(), row);
            remember(occurrenceById, row.occurrence());
            add(activations, row.occurrence().id(), row);
        }
        for (DecisionRow row : session.decisions()) {
            remember(occurrenceById, row.occurrence());
            add(decisions, session.sessionId() + "|" + row.occurrence().id(), row);
            // A decision's clock cells are corpus symbols at Int.
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
            // One variable, one sort: from the JVM descriptor, never a value's
            // spelling.
            declaredSymbols.put(row.symbol(),
                    JavaSmtSorts.sortOfJava(row.javaType()));
        }
        for (RootMintRow row : session.roots()) {
            remember(occurrenceById, row.occurrence());
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
        locationTouches.computeIfAbsent(touchKey(occurrence, location),
                key -> new LinkedHashSet<String>()).add(occurrence.id());
    }

    /** node|location: one location of one JVM. */
    private static String touchKey(OccurrenceAddress occurrence,
                                   LocationId location) {
        return occurrence.node().render() + "|"
                + SmtLowering.locationKey(location);
    }

    private static void remember(Map<String, OccurrenceAddress> into,
                                 OccurrenceAddress occurrence) {
        if (occurrence != null) into.put(occurrence.id(), occurrence);
    }

    private static <T> void add(Map<String, List<T>> into, String key, T row) {
        into.computeIfAbsent(key, ignored -> new ArrayList<T>()).add(row);
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

    /** One session's state join; a session this corpus lacks joins nothing. */
    public SmtLowering.SessionJoin join(String sessionId) {
        return joinById.getOrDefault(sessionId, SmtLowering.NO_JOIN);
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
        return decisions.getOrDefault(sessionId + "|" + occurrence.id(),
                Collections.<DecisionRow>emptyList());
    }

    public List<AttachRow> attachesOn(OccurrenceAddress occurrence) {
        return attachesOn.getOrDefault(occurrence.id(),
                Collections.<AttachRow>emptyList());
    }

    /** Every target row published for one occurrence, in any session. */
    public List<TargetRow> targetsOn(OccurrenceAddress occurrence) {
        return targetsOn.getOrDefault(occurrence.id(),
                Collections.<TargetRow>emptyList());
    }

    /** One session's target row at one occurrence, or null. */
    public TargetRow target(String sessionId, OccurrenceAddress occurrence) {
        for (TargetRow row : targetsOn(occurrence)) {
            if (row.sessionId().equals(sessionId)) return row;
        }
        return null;
    }

    public List<ReadRow> readsOn(OccurrenceAddress occurrence) {
        return readsOn.getOrDefault(occurrence.id(),
                Collections.<ReadRow>emptyList());
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
        return writesOn.getOrDefault(occurrence.id(),
                Collections.<WriteRow>emptyList());
    }

    /** Every export any session published at one occurrence. */
    public List<ExportRow> exportsOn(OccurrenceAddress occurrence) {
        return exportsOn.getOrDefault(occurrence.id(),
                Collections.<ExportRow>emptyList());
    }

    // ---- The causal graph (SS3.1) ----

    /**
     * The writes one read could have taken its value from: the observed one and
     * every HB-concurrent writer (R-I7.1, {@code smt.Arms}) -- the same
     * alternatives the composition offers. ONE implementation, used by the
     * closure ({@link ClosurePlanner#writers}) and by {@link #upstreamOf}.
     *
     * @param reader the reading occurrence, for the concurrency rule
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

    /** Every occurrence that reaches one occurrence and its factor, itself
     *  included, within ONE session (DESIGN4 SS3.2). In-edges (SS3.1): matched
     *  communication transfers and candidate shared-state dependencies on the
     *  reader's node ({@link #eligibleWrites}, {@link #observed}), including
     *  reads stated only in expressions (E2). Not memoized. */
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

    /** One occurrence's in-edges in one session: who delivered to it, who wrote
     *  for it. */
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
        // E2: shared state a delivery rests on, stated only in its expression.
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

    /** Writers of what one read could have observed, ON THE READER'S NODE (N1:
     *  location keys are per JVM; cross-node influence travels only by
     *  transfer). */
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

    /** Whether a decision is a FAULT decision: its lowered term REACHES a
     *  MARKER root the same session minted (DESIGN4 SS1.4). */
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

    /** Whether some session ran the region INSTRUMENTED (the weave holds it);
     *  an admitted replay reaching an unwoven region is growth (DESIGN4
     *  SS3.3b). */
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

    /** Walk depth for state reads inside one expression. */
    private static final int EXPRESSION_DEPTH = 64;

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
     *  ComposedFamilies.expressionWrites}) and the closure (E2). Locations the
     *  session never wrote are skipped (no version to guess). */
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

    /** Location key -> the latest event id one expression read it at (any node
     *  with location + readEventId). */
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
    public List<WriteRow> writesOf(String sessionId, String locationKey) {
        return writesByLocation.getOrDefault(sessionId + "|" + locationKey,
                Collections.<WriteRow>emptyList());
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
     *  recordedValue}. */
    @Override
    public String rootValue(String sessionId, String rootId) {
        String wave = world(sessionId).rootAssignments.get(rootId);
        if (wave != null && !wave.isEmpty()) return wave;
        return rootReading(sessionId, rootId);
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

    /** An absolute {@code [min, max]} for one root, or null when pinned. The
     *  case file is the authority ({@code +k}/{@code -k} are relative to the
     *  recorded reading); no domain means pinned here and in the composition.
     */
    public String[] domainOf(RootMintRow root) {
        // A CLOCK has a floor and no window (FlipQuery's rule).
        if (root == null || root.kind() == RootKind.CLOCK) return null;
        RootDomain domain = RootDomain.resolved(root, declaredDomains);
        return domain.min() == null || domain.max() == null ? null
                : new String[]{domain.min(), domain.max()};
    }
}
