package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.d3.smt.Arms;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.Interaction;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every session of one iteration, keyed the way a composition reads them.
 *
 * <p>Every key here is an identity of the contract and nothing else: a path
 * is a session and an occurrence, an interaction is its two endpoints, a
 * state edge is a location and a version <em>inside one session</em>.  No
 * key is a request family, a port alone, or a consumer phase -- the three
 * spellings that let one producer's arm be read as another's.</p>
 */
public final class CorpusIndex implements Arms.Rows {

    /** One session's decisions at one occurrence: that session's path. */
    public static final class PathRecord {
        private final String pathId;
        private final String sessionId;
        private final OccurrenceAddress occurrence;
        private final List<DecisionRow> decisions;

        private PathRecord(String sessionId, OccurrenceAddress occurrence,
                           List<DecisionRow> decisions) {
            this.pathId = JsonText.digest(sessionId + "|"
                    + occurrence.render(), 16);
            this.sessionId = sessionId;
            this.occurrence = occurrence;
            this.decisions = Collections.unmodifiableList(decisions);
        }

        public String pathId() {
            return pathId;
        }

        public String sessionId() {
            return sessionId;
        }

        public OccurrenceAddress occurrence() {
            return occurrence;
        }

        public List<DecisionRow> decisions() {
            return decisions;
        }

        @Override
        public String toString() {
            return pathId + " (" + sessionId + " @ " + occurrence.render()
                    + ", " + decisions.size() + " decisions)";
        }
    }

    private final Path iteration;
    private final List<SessionReader> sessions;
    private final Map<String, SessionReader> bySessionId =
            new LinkedHashMap<String, SessionReader>();
    /** session id -> occurrence id -> that session's path there. */
    private final Map<String, Map<String, PathRecord>> pathsBySession =
            new LinkedHashMap<String, Map<String, PathRecord>>();
    /** occurrence id -> every session's path at it. */
    private final Map<String, List<PathRecord>> pathsByOccurrence =
            new LinkedHashMap<String, List<PathRecord>>();
    /** occurrence id -> the target rows naming it. */
    private final Map<String, List<TargetRow>> targetsByOccurrence =
            new LinkedHashMap<String, List<TargetRow>>();
    /** consumer endpoint id -> the attaches at it, any session. */
    private final Map<String, List<AttachRow>> attachesByConsumer =
            new LinkedHashMap<String, List<AttachRow>>();
    /** interaction id -> the attaches its pairing states, any session. */
    private final Map<String, List<AttachRow>> attachesByInteraction =
            new LinkedHashMap<String, List<AttachRow>>();
    /** interaction id -> the interaction itself. */
    private final Map<String, Interaction> interactions =
            new LinkedHashMap<String, Interaction>();
    /** producer endpoint id -> the exports at it, any session. */
    private final Map<String, List<ExportRow>> exportsByProducer =
            new LinkedHashMap<String, List<ExportRow>>();
    /** session id -> "location#version" -> the write of it. */
    private final Map<String, Map<String, WriteRow>> writesBySession =
            new LinkedHashMap<String, Map<String, WriteRow>>();
    /** session id -> its reads, in file order. */
    /** Session -> the symbols its READ rows minted. */
    private final Map<String, Set<String>> readSymbolsBySession =
            new LinkedHashMap<String, Set<String>>();
    private final Map<String, List<ReadRow>> readsBySession =
            new LinkedHashMap<String, List<ReadRow>>();
    /** root id -> its mint rows, one per session that minted it. */
    private final Map<String, List<RootMintRow>> rootsById =
            new LinkedHashMap<String, List<RootMintRow>>();
    /** v_H symbol -> the attach that minted it, by session. */
    private final Map<String, Map<String, AttachRow>> attachesBySymbol =
            new LinkedHashMap<String, Map<String, AttachRow>>();
    /** Every declared symbol of the corpus, at the sort it was minted at. */
    private final Map<String, Sort> declaredSymbols =
            new LinkedHashMap<String, Sort>();
    /** Clock cell symbol -> session id -> the instant it read. */
    private final Map<String, Map<String, Long>> clockCells =
            new LinkedHashMap<String, Map<String, Long>>();
    /** Root symbol -> every root id declared under it. */
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();
    /** Endpoint id -> the occurrence it belongs to: the causal chain. */
    private final Map<String, OccurrenceAddress> occurrenceByEndpoint =
            new LinkedHashMap<String, OccurrenceAddress>();
    /** session|occurrence -> that session's activation of it. */
    private final Map<String, ActivationRow> activationByOccurrence =
            new LinkedHashMap<String, ActivationRow>();
    /** session|endpoint -> the session event its row was sequenced at. */
    private final Map<String, Long> seqByEndpoint =
            new LinkedHashMap<String, Long>();

    private CorpusIndex(Path iteration, List<SessionReader> sessions) {
        this.iteration = iteration;
        this.sessions = Collections.unmodifiableList(sessions);
        for (SessionReader session : sessions) {
            index(session);
        }
    }

    /** Every session under {@code <iteration>/sessions}. */
    public static CorpusIndex of(Path iteration) throws IOException {
        List<SessionReader> sessions = new ArrayList<SessionReader>();
        for (SessionDir dir : SessionDir.sessionsIn(iteration)) {
            sessions.add(SessionReader.read(dir));
        }
        return new CorpusIndex(iteration, sessions);
    }

    /** The sessions given, for a caller that already read them. */
    public static CorpusIndex of(Path iteration,
                                 List<SessionReader> sessions) {
        return new CorpusIndex(iteration,
                new ArrayList<SessionReader>(sessions));
    }

    private void index(SessionReader session) {
        String sessionId = session.sessionId();
        bySessionId.put(sessionId, session);
        for (ActivationRow activation : session.activations()) {
            activationByOccurrence.put(sessionId + "|"
                    + activation.occurrence().id(), activation);
        }

        Map<String, List<DecisionRow>> byOccurrence =
                new LinkedHashMap<String, List<DecisionRow>>();
        Map<String, OccurrenceAddress> addresses =
                new LinkedHashMap<String, OccurrenceAddress>();
        for (DecisionRow decision : session.decisions()) {
            String key = decision.occurrence().id();
            addresses.put(key, decision.occurrence());
            List<DecisionRow> held = byOccurrence.get(key);
            if (held == null) {
                held = new ArrayList<DecisionRow>();
                byOccurrence.put(key, held);
            }
            held.add(decision);
            for (Map.Entry<String, Long> reading
                    : decision.clockReadings().entrySet()) {
                Map<String, Long> cells = clockCells.get(reading.getKey());
                if (cells == null) {
                    cells = new LinkedHashMap<String, Long>();
                    clockCells.put(reading.getKey(), cells);
                }
                cells.put(sessionId, reading.getValue());
                declaredSymbols.put(reading.getKey(), Sort.INT);
            }
        }
        // A session that reached an anchor without deciding anything on the
        // way still has a path there: the empty conjunction.  Its target row
        // is what says it was reached, so the target rows mint the paths the
        // decisions did not.
        for (TargetRow target : session.targets()) {
            addresses.put(target.occurrence().id(), target.occurrence());
            if (!byOccurrence.containsKey(target.occurrence().id())) {
                byOccurrence.put(target.occurrence().id(),
                        new ArrayList<DecisionRow>());
            }
            List<TargetRow> held =
                    targetsByOccurrence.get(target.occurrence().id());
            if (held == null) {
                held = new ArrayList<TargetRow>();
                targetsByOccurrence.put(target.occurrence().id(), held);
            }
            held.add(target);
        }
        Map<String, PathRecord> paths = new LinkedHashMap<String, PathRecord>();
        for (Map.Entry<String, List<DecisionRow>> entry
                : byOccurrence.entrySet()) {
            PathRecord path = new PathRecord(sessionId,
                    addresses.get(entry.getKey()), entry.getValue());
            paths.put(entry.getKey(), path);
            List<PathRecord> byAnchor = pathsByOccurrence.get(entry.getKey());
            if (byAnchor == null) {
                byAnchor = new ArrayList<PathRecord>();
                pathsByOccurrence.put(entry.getKey(), byAnchor);
            }
            byAnchor.add(path);
        }
        pathsBySession.put(sessionId, paths);

        for (ExportRow export : session.exports()) {
            add(exportsByProducer, export.endpoint().id(), export);
            occurrenceByEndpoint.put(export.endpoint().id(),
                    export.endpoint().occurrence());
            seqByEndpoint.put(sessionId + "|" + export.endpoint().id(),
                    export.seq());
        }
        for (AttachRow attach : session.attaches()) {
            add(attachesByConsumer, attach.endpoint().id(), attach);
            occurrenceByEndpoint.put(attach.endpoint().id(),
                    attach.endpoint().occurrence());
            seqByEndpoint.put(sessionId + "|" + attach.endpoint().id(),
                    attach.seq());
            Interaction interaction = attach.interaction();
            if (interaction != null) {
                interactions.put(interaction.id(), interaction);
                add(attachesByInteraction, interaction.id(), attach);
            }
            Map<String, AttachRow> bySession =
                    attachesBySymbol.get(attach.symbol());
            if (bySession == null) {
                bySession = new LinkedHashMap<String, AttachRow>();
                attachesBySymbol.put(attach.symbol(), bySession);
            }
            bySession.put(sessionId, attach);
            // The JVM descriptor the mint states, never the spelling of
            // one value it carried: one variable has one sort.
            declaredSymbols.put(attach.symbol(),
                    JavaSmtSorts.sortOfJava(attach.javaType()));
        }
        Map<String, WriteRow> writes = new LinkedHashMap<String, WriteRow>();
        for (WriteRow write : session.writes()) {
            occurrenceByEndpoint.put(write.endpoint().id(),
                    write.endpoint().occurrence());
            seqByEndpoint.put(sessionId + "|" + write.endpoint().id(),
                    write.seq());
            writes.put(SmtLowering.locationKey(write.location()) + "#"
                    + write.version(), write);
        }
        writesBySession.put(sessionId, writes);
        readsBySession.put(sessionId, session.reads());
        Set<String> readSymbols = new LinkedHashSet<String>();
        for (ReadRow read : session.reads()) {
            if (read.symbol() != null && !read.symbol().isEmpty()) {
                readSymbols.add(read.symbol());
            }
            occurrenceByEndpoint.put(read.endpoint().id(),
                    read.endpoint().occurrence());
            seqByEndpoint.put(sessionId + "|" + read.endpoint().id(),
                    read.seq());
        }
        readSymbolsBySession.put(sessionId, readSymbols);

        for (RootMintRow root : session.roots()) {
            add(rootsById, root.rootId(), root);
            Set<String> ids = rootIdsBySymbol.get(root.symbol());
            if (ids == null) {
                ids = new LinkedHashSet<String>();
                rootIdsBySymbol.put(root.symbol(), ids);
            }
            ids.add(root.rootId());
            declaredSymbols.put(root.symbol(),
                    root.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT);
        }
    }

    private static <T> void add(Map<String, List<T>> index, String key,
                                T value) {
        List<T> held = index.get(key);
        if (held == null) {
            held = new ArrayList<T>();
            index.put(key, held);
        }
        held.add(value);
    }

    // ------------------------------------------------------------------
    // Reading the index.
    // ------------------------------------------------------------------

    public Path iteration() {
        return iteration;
    }

    public List<SessionReader> sessions() {
        return sessions;
    }

    public SessionReader session(String sessionId) {
        return bySessionId.get(sessionId);
    }

    /** Every session's path at one occurrence. */
    public List<PathRecord> pathsAt(OccurrenceAddress occurrence) {
        List<PathRecord> paths = pathsByOccurrence.get(occurrence.id());
        return paths == null ? Collections.<PathRecord>emptyList() : paths;
    }

    /** One session's path at one occurrence, or null. */
    public PathRecord path(String sessionId, OccurrenceAddress occurrence) {
        Map<String, PathRecord> paths = pathsBySession.get(sessionId);
        return paths == null ? null : paths.get(occurrence.id());
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
        return new Arms(this).attested(sessionId, occurrence);
    }

    /** The target rows one session published at one occurrence. */
    public List<TargetRow> targetsAt(OccurrenceAddress occurrence) {
        List<TargetRow> rows = targetsByOccurrence.get(occurrence.id());
        return rows == null ? Collections.<TargetRow>emptyList() : rows;
    }

    /** One session's target row at one occurrence, or null. */
    public TargetRow target(String sessionId, OccurrenceAddress occurrence) {
        for (TargetRow row : targetsAt(occurrence)) {
            if (row.sessionId().equals(sessionId)) return row;
        }
        return null;
    }

    public List<AttachRow> attachesOf(Endpoint consumer) {
        List<AttachRow> rows = attachesByConsumer.get(consumer.id());
        return rows == null ? Collections.<AttachRow>emptyList() : rows;
    }

    public List<AttachRow> attachesOf(Interaction interaction) {
        List<AttachRow> rows = attachesByInteraction.get(interaction.id());
        return rows == null ? Collections.<AttachRow>emptyList() : rows;
    }

    public Interaction interaction(String interactionId) {
        return interactions.get(interactionId);
    }

    public Map<String, Interaction> interactions() {
        return Collections.unmodifiableMap(interactions);
    }

    /** Every attach of one session whose consumer sits at this occurrence. */
    public List<AttachRow> attachesRead(String sessionId,
                                        OccurrenceAddress occurrence) {
        List<AttachRow> read = new ArrayList<AttachRow>();
        SessionReader session = bySessionId.get(sessionId);
        if (session == null) return read;
        for (AttachRow attach : session.attaches()) {
            if (attach.endpoint().occurrence().id().equals(occurrence.id())) {
                read.add(attach);
            }
        }
        return read;
    }

    public List<ExportRow> exportsOf(Endpoint producer) {
        List<ExportRow> rows = exportsByProducer.get(producer.id());
        return rows == null ? Collections.<ExportRow>emptyList() : rows;
    }

    /** The attach that minted this symbol in this session, or null. */
    public AttachRow attachOfSymbol(String symbol, String sessionId) {
        Map<String, AttachRow> bySession = attachesBySymbol.get(symbol);
        if (bySession == null) return null;
        AttachRow own = bySession.get(sessionId);
        if (own != null) return own;
        return bySession.isEmpty() ? null
                : bySession.values().iterator().next();
    }

    /** Whether this symbol is a handoff variable some attach minted. */
    public boolean handoffSymbol(String symbol) {
        return attachesBySymbol.containsKey(symbol);
    }

    public Set<String> handoffSymbols() {
        return attachesBySymbol.keySet();
    }

    /**
     * The rows of one session, as the state join reads them.
     *
     * <p>One view per session and no scope inside it: the write log is
     * the session's, because versions are session-local counters, and a
     * mint version is unique in it by construction.</p>
     */
    public SmtLowering.SessionJoin joinOf(final String sessionId) {
        final Map<String, WriteRow> writes = writesBySession.get(sessionId);
        final SessionReader session = bySessionId.get(sessionId);
        final Map<Long, Set<String>> minted =
                SmtLowering.mintedReadIndex(readsBySession.get(sessionId));
        return new SmtLowering.SessionJoin() {
            @Override
            public JsonElement writeExpression(String locationKey,
                                               long version) {
                if (writes == null || session == null) return null;
                WriteRow write = writes.get(locationKey + "#" + version);
                if (write == null) return null;
                JsonObject expression = session.expressions()
                        .expression(write.expressionRef());
                return expression;
            }

            @Override
            public Set<String> mintedReadSymbols(long version) {
                Set<String> symbols = minted.get(Long.valueOf(version));
                return symbols == null
                        ? Collections.<String>emptySet() : symbols;
            }
        };
    }

    /** The write one session made of this location at this version. */
    public WriteRow write(String sessionId, String locationKey,
                          long version) {
        Map<String, WriteRow> writes = writesBySession.get(sessionId);
        return writes == null ? null
                : writes.get(locationKey + "#" + version);
    }

    /**
     * The writes of one location this session made, in version order.
     *
     * <p>All of them: which of them a given read may have seen is a
     * happens-before question, and the answer belongs to the composition
     * that knows the read.</p>
     */
    public List<WriteRow> writesOf(String sessionId, String locationKey) {
        List<WriteRow> found = new ArrayList<WriteRow>();
        Map<String, WriteRow> writes = writesBySession.get(sessionId);
        if (writes == null) return found;
        for (Map.Entry<String, WriteRow> entry : writes.entrySet()) {
            if (entry.getKey().startsWith(locationKey + "#")) {
                found.add(entry.getValue());
            }
        }
        return found;
    }

    /** Every read one session made at one occurrence. */
    public List<ReadRow> readsAt(String sessionId,
                                 OccurrenceAddress occurrence) {
        List<ReadRow> reads = new ArrayList<ReadRow>();
        List<ReadRow> all = readsBySession.get(sessionId);
        if (all == null) return reads;
        for (ReadRow read : all) {
            if (read.endpoint().occurrence().id().equals(occurrence.id())) {
                reads.add(read);
            }
        }
        return reads;
    }

    // ------------------------------------------------------------------
    // The shared arm rule reads the corpus through this.
    // ------------------------------------------------------------------

    @Override
    public List<String> sessionIds() {
        List<String> ids = new ArrayList<String>();
        for (SessionReader session : sessions) ids.add(session.sessionId());
        return ids;
    }

    @Override
    public JsonObject expression(String sessionId, String expressionRef) {
        SessionReader session = bySessionId.get(sessionId);
        return session == null ? null
                : session.expressions().expression(expressionRef);
    }

    /** One session's expression table, as its own terms name it. */
    public ExpressionTable expressions(String sessionId) {
        SessionReader session = bySessionId.get(sessionId);
        return session == null ? null : session.expressions();
    }

    /** Whether one session published a READ under this symbol. */
    public boolean readSymbol(String sessionId, String symbol) {
        Set<String> symbols = readSymbolsBySession.get(sessionId);
        return symbols != null && symbols.contains(symbol);
    }

    @Override
    public List<DecisionRow> decisionsOf(String sessionId,
                                         OccurrenceAddress occurrence) {
        PathRecord path = path(sessionId, occurrence);
        return path == null ? Collections.<DecisionRow>emptyList()
                : path.decisions();
    }

    @Override
    public String pathIdOf(String sessionId, OccurrenceAddress occurrence) {
        PathRecord path = path(sessionId, occurrence);
        return path == null ? sessionId : path.pathId();
    }

    @Override
    public OccurrenceAddress occurrenceOf(String endpointId) {
        return occurrenceByEndpoint.get(endpointId);
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

    @Override
    public Map<String, List<RootMintRow>> roots() {
        return Collections.unmodifiableMap(rootsById);
    }

    /** The mint row for one root in one session, or null. */
    public RootMintRow root(String rootId, String sessionId) {
        List<RootMintRow> rows = rootsById.get(rootId);
        if (rows == null) return null;
        for (RootMintRow row : rows) {
            if (row.sessionId().equals(sessionId)) return row;
        }
        return null;
    }

    /** Any mint row for one root, for the facts every session agrees on. */
    public RootMintRow anyRoot(String rootId) {
        List<RootMintRow> rows = rootsById.get(rootId);
        return rows == null || rows.isEmpty() ? null : rows.get(0);
    }

    // Whether two sessions recorded a root differently -- a varied root is
    // one exploration moved, and only a varied root is carried on a path --
    // is Arms.Rows.varied, which this index inherits.  A second copy here
    // was the same rule twice, and the rule decides both what a path
    // carries and what an arm is guarded by.

    /** Every symbol the runtime declared, at the sort it minted it at. */
    public Map<String, Sort> declaredSymbols() {
        return Collections.unmodifiableMap(declaredSymbols);
    }

    /** Clock cell symbol -> session id -> the instant that session read. */
    public Map<String, Map<String, Long>> clockCells() {
        return Collections.unmodifiableMap(clockCells);
    }

    /** Root symbols naming more than one root: a name collision. */
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

    /**
     * The session that recorded the run, or null when that has no answer.
     *
     * <p>The rule is the contract's, stated once there; what a corpus with
     * no seed or two seeds MEANS is this stage's, and the composer answers
     * it with a BLOCKING gap.</p>
     */
    public String seedSessionId() {
        return SessionReader.seedSessionId(sessions);
    }

    /** Every session that focused nothing: what that gap names. */
    public List<String> unfocusedSessionIds() {
        return SessionReader.unfocusedSessionIds(sessions);
    }

    @Override
    public String toString() {
        return "corpus " + iteration + " (" + sessions.size() + " sessions, "
                + interactions.size() + " interactions)";
    }
}
