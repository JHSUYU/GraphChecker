package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.Interaction;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
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
public final class CorpusIndex {

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
    /** Root id -> every recorded value any session gave it. */
    private final Map<String, Set<String>> recordedRootValues =
            new LinkedHashMap<String, Set<String>>();
    /** Root symbol -> every root id declared under it. */
    private final Map<String, Set<String>> rootIdsBySymbol =
            new LinkedHashMap<String, Set<String>>();

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
        }
        for (AttachRow attach : session.attaches()) {
            add(attachesByConsumer, attach.endpoint().id(), attach);
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
            declaredSymbols.put(attach.symbol(), sortOfValue(
                    JsonText.firstNonBlank(attach.answeredValue(),
                            attach.arrival())));
        }
        Map<String, WriteRow> writes = new LinkedHashMap<String, WriteRow>();
        for (WriteRow write : session.writes()) {
            writes.put(SmtLowering.locationKey(write.location()) + "#"
                    + write.version(), write);
        }
        writesBySession.put(sessionId, writes);
        readsBySession.put(sessionId, session.reads());

        for (RootMintRow root : session.roots()) {
            add(rootsById, root.rootId(), root);
            Set<String> values = recordedRootValues.get(root.rootId());
            if (values == null) {
                values = new LinkedHashSet<String>();
                recordedRootValues.put(root.rootId(), values);
            }
            if (root.recordedValue() != null
                    && !root.recordedValue().isEmpty()) {
                values.add(root.recordedValue());
            }
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

    /**
     * The sort a recorded value states: a Boolean is one, else an Int.
     *
     * <p>The spelling of a value is weak evidence about its Java type, and
     * it is all an AttachRow states today.  Contract v1.1 puts
     * {@code javaType} on the row; when it lands this reads it through
     * {@code SmtLowering.sortOf(javaType)} and the guess disappears.</p>
     */
    private static Sort sortOfValue(String value) {
        String text = value == null ? "" : value.trim();
        return "true".equals(text) || "false".equals(text)
                ? Sort.BOOL : Sort.INT;
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

    /** Whether this session decided anything at this occurrence. */
    public boolean attested(String sessionId,
                            OccurrenceAddress occurrence) {
        PathRecord path = path(sessionId, occurrence);
        return path != null && !path.decisions().isEmpty();
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

    /** The write log of one session, as the state join reads it. */
    public SmtLowering.SessionJoin joinOf(final String sessionId) {
        final Map<String, WriteRow> writes = writesBySession.get(sessionId);
        final SessionReader session = bySessionId.get(sessionId);
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
        };
    }

    /** The write one session made of this location at this version. */
    public WriteRow write(String sessionId, String locationKey,
                          long version) {
        Map<String, WriteRow> writes = writesBySession.get(sessionId);
        return writes == null ? null
                : writes.get(locationKey + "#" + version);
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

    /**
     * Whether two sessions of this corpus recorded this root differently.
     *
     * <p>A varied root is one exploration moved, and only a varied root is
     * carried on a path: a root every session read the same way is already
     * pinned by its own domain, and asserting it again on every path would
     * put a root nothing branches on "on a path".</p>
     */
    public boolean varied(String rootId) {
        Set<String> values = recordedRootValues.get(rootId);
        return values != null && values.size() > 1;
    }

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
     * The session that recorded the run, or null when every session
     * explored something.
     *
     * <p>Which recording a claim is about is a fact of the rows: the seed
     * replay focused nothing.</p>
     */
    public String seedSessionId() {
        for (SessionReader session : sessions) {
            if (!session.explored()) return session.sessionId();
        }
        return null;
    }

    @Override
    public String toString() {
        return "corpus " + iteration + " (" + sessions.size() + " sessions, "
                + interactions.size() + " interactions)";
    }
}
