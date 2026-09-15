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
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.JavaSmtSorts;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
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
    /** Clock cell symbol -> session id -> the instant it read. */
    private final Map<String, Map<String, Long>> clockCells =
            new LinkedHashMap<String, Map<String, Long>>();
    /** Root symbol -> every root id declared under it. */
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();
    /** endpoint id -> the endpoint, so an anchor's producer can be found. */
    /** session|occurrence -> that session's activation of it. */
    private final Map<String, ActivationRow> activationByOccurrence =
            new LinkedHashMap<String, ActivationRow>();
    /** session|endpoint -> the session event its row was sequenced at. */
    private final Map<String, Long> seqByEndpoint =
            new LinkedHashMap<String, Long>();
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
        return corpus;
    }

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

    private void index(SessionReader session) {
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
            // A decision carries the clock cells it read: the cell is a
            // symbol of the corpus, at Int, and what each session read of it
            // is what a clock claim is about.
            for (Map.Entry<String, Long> reading
                    : row.clockReadings().entrySet()) {
                Map<String, Long> cells = clockCells.get(reading.getKey());
                if (cells == null) {
                    cells = new LinkedHashMap<String, Long>();
                    clockCells.put(reading.getKey(), cells);
                }
                cells.put(session.sessionId(), reading.getValue());
                declaredSymbols.put(reading.getKey(), Sort.INT);
            }
        }
        for (ExportRow row : session.exports()) {
            remember(occurrenceById, row.endpoint().occurrence());
            seqByEndpoint.put(session.sessionId() + "|"
                    + row.endpoint().id(), row.seq());
            endpointById.put(row.endpoint().id(), row.endpoint());
            add(exports, row.endpoint().id(), row);
        }
        for (AttachRow row : session.attaches()) {
            remember(occurrenceById, row.endpoint().occurrence());
            seqByEndpoint.put(session.sessionId() + "|"
                    + row.endpoint().id(), row.seq());
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
            seqByEndpoint.put(session.sessionId() + "|"
                    + row.endpoint().id(), row.seq());
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
            seqByEndpoint.put(session.sessionId() + "|"
                    + row.endpoint().id(), row.seq());
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
     * <p>One rule, stated once in the contract: the seed is the session whose
     * activations focused nothing.  A corpus with none of those, or with more
     * than one, does not state which recording a declaration was written
     * about, and the caller refuses with a named gap -- naming an exploration
     * replay as the recording is how a claim comes to be about the wrong
     * execution.</p>
     */
    public String seedSessionId() {
        String seed = SessionReader.seedSessionId(sessions);
        return seed == null ? "" : seed;
    }

    /** Every session that focused nothing: what such a refusal names. */
    public List<String> unfocusedSessionIds() {
        return SessionReader.unfocusedSessionIds(sessions);
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

    /**
     * Whether this session explored that occurrence symbolically.
     *
     * <p>The rule is {@link Arms#attested}: instrumented, and symbolic in
     * this session.  Asked through the same object both stages ask, so an
     * arm the explorer treats as attested is not one the composition reads
     * as concrete.</p>
     */
    public boolean attested(String sessionId,
                            OccurrenceAddress occurrence) {
        return arms.attested(sessionId, occurrence);
    }

    /** Every interaction any session's own pairing states. */
    public Map<String, Interaction> interactions() {
        return Collections.unmodifiableMap(interactions);
    }

    /** Every symbol the runtime declared, at the sort it minted it at. */
    public Map<String, Sort> declaredSymbols() {
        return Collections.unmodifiableMap(declaredSymbols);
    }

    /** Clock cell symbol -> session id -> the instant that session read. */
    public Map<String, Map<String, Long>> clockCells() {
        return Collections.unmodifiableMap(clockCells);
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

    @Override
    public long seqOf(String sessionId, String endpointId) {
        Long seq = seqByEndpoint.get(sessionId + "|" + endpointId);
        return seq == null ? -1L : seq.longValue();
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

    /** What one session read at one root, or "" when it minted none. */
    public String rootReading(String sessionId, String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        RootMintRow row = bySession == null ? null : bySession.get(sessionId);
        return row == null ? "" : row.recordedValue();
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
