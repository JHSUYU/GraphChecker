package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionReader;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

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
 * One iteration's sessions, indexed for exploration.
 *
 * <p>Everything exploration asks of a recording is asked here: which paths an
 * occurrence has, which interaction an attach belongs to, what some producer
 * exported at an endpoint, which write a read observed, and what a case
 * declares a root may be.  The indexes are keyed the way the contract says
 * identity works -- an interaction by BOTH its endpoints, a location by the
 * replay-stable {@link LocationId}, a symbol by the session that minted it,
 * because a raw symbol, a version id and an expression ref are all
 * session-local names.</p>
 */
public final class Corpus {
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
    private final Map<String, List<WriteRow>> writesOn =
            new LinkedHashMap<String, List<WriteRow>>();
    /** session|location|version -> the write that produced it. */
    private final Map<String, WriteRow> writeByVersion =
            new LinkedHashMap<String, WriteRow>();
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

    private Corpus(List<SessionReader> sessions) {
        this.sessions = Collections.unmodifiableList(sessions);
        for (SessionReader session : sessions) index(session);
    }

    /** Reads an iteration and its case-declared root domains. */
    public static Corpus read(Path iteration, Path rootDomains)
            throws IOException {
        Corpus corpus = new Corpus(SessionReader.readAll(iteration));
        if (rootDomains != null && Files.isRegularFile(rootDomains)) {
            for (RootDomain domain : RowCodec.readAll(rootDomains,
                    ExploreCodec::readDomain)) {
                if (!domain.rootId().isEmpty()) {
                    corpus.declaredDomains.put(domain.rootId(), domain);
                }
            }
        }
        return corpus;
    }

    /** A corpus over sessions already in memory (tests, and one-shot runs). */
    public static Corpus of(List<SessionReader> sessions) {
        return new Corpus(new ArrayList<SessionReader>(sessions));
    }

    private void index(SessionReader session) {
        sessionById.put(session.sessionId(), session);
        loweringById.put(session.sessionId(), SmtLowering.forSession(session));
        for (ActivationRow row : session.activations()) {
            remember(occurrenceById, row.occurrence());
            add(activations, row.occurrence().id(), row);
        }
        for (DecisionRow row : session.decisions()) {
            remember(occurrenceById, row.occurrence());
            add(decisions, session.sessionId() + "|" + row.occurrence().id(), row);
        }
        for (ExportRow row : session.exports()) {
            remember(occurrenceById, row.endpoint().occurrence());
            add(exports, row.endpoint().id(), row);
        }
        for (AttachRow row : session.attaches()) {
            remember(occurrenceById, row.endpoint().occurrence());
            attachBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            add(attachesOn, row.endpoint().occurrence().id(), row);
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
        }
        for (WriteRow row : session.writes()) {
            remember(occurrenceById, row.endpoint().occurrence());
            writeByVersion.put(versionKey(session.sessionId(), row.location(),
                    row.version()), row);
            add(writesOn, row.endpoint().occurrence().id(), row);
            touch(row.endpoint().occurrence(), row.location());
        }
        for (ReadRow row : session.reads()) {
            remember(occurrenceById, row.endpoint().occurrence());
            if (!row.symbol().isEmpty()) {
                readBySymbol.put(session.sessionId() + "|" + row.symbol(), row);
            }
            add(readsOn, row.endpoint().occurrence().id(), row);
            touch(row.endpoint().occurrence(), row.location());
        }
    }

    private void touch(OccurrenceAddress occurrence, LocationId location) {
        String key = occurrence.node().render() + "|" + location.toString();
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

    private static String versionKey(String sessionId, LocationId location,
                                     long version) {
        return sessionId + "|" + location.toString() + "|" + version;
    }

    /** One path's id: the session it ran in and the occurrence it ran. */
    public static String pathId(String sessionId,
                                OccurrenceAddress occurrence) {
        return ExploreIds.sha16(sessionId + "|" + occurrence.id());
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
     * Every path of one occurrence: one per session that activated it.
     *
     * <p>A session that activated the occurrence but decided nothing still
     * has a path -- an empty one -- because "this occurrence ran here" is
     * what admission is about, and its absence is what a divergence is.</p>
     */
    public List<RecordedPath> pathsOf(OccurrenceAddress occurrence) {
        List<RecordedPath> paths = new ArrayList<RecordedPath>();
        for (SessionReader session : sessions) {
            ActivationRow activation = activation(session.sessionId(),
                    occurrence);
            List<DecisionRow> path = decisions.get(
                    session.sessionId() + "|" + occurrence.id());
            if (activation == null && path == null) continue;
            paths.add(new RecordedPath(session.sessionId(), occurrence,
                    path == null ? new ArrayList<DecisionRow>() : path,
                    activation != null && activation.focused()));
        }
        return paths;
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

    /** Whether the occurrence ran symbolically in that session. */
    public boolean ranFocused(String sessionId,
                              OccurrenceAddress occurrence) {
        ActivationRow row = activation(sessionId, occurrence);
        return row != null && row.focused();
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

    public List<ReadRow> readsOn(OccurrenceAddress occurrence) {
        List<ReadRow> rows = readsOn.get(occurrence.id());
        return rows == null ? Collections.<ReadRow>emptyList() : rows;
    }

    public List<WriteRow> writesOn(OccurrenceAddress occurrence) {
        List<WriteRow> rows = writesOn.get(occurrence.id());
        return rows == null ? Collections.<WriteRow>emptyList() : rows;
    }

    /** The write one read observed, inside that read's own session. */
    public WriteRow writeOf(String sessionId, LocationId location,
                            long version) {
        return version < 0 ? null
                : writeByVersion.get(versionKey(sessionId, location, version));
    }

    /** Every occurrence of one node that writes or reads one location. */
    public Set<String> touching(OccurrenceAddress occurrence,
                                LocationId location) {
        Set<String> found = locationTouches.get(
                occurrence.node().render() + "|" + location.toString());
        return found == null ? Collections.<String>emptySet() : found;
    }

    public AttachRow attach(String sessionId, String symbol) {
        return attachBySymbol.get(sessionId + "|" + symbol);
    }

    public RootMintRow root(String sessionId, String symbol) {
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

    /** Any mint row of one root, for its kind and its published domain. */
    public RootMintRow anyRoot(String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        if (bySession == null || bySession.isEmpty()) return null;
        return bySession.values().iterator().next();
    }

    /**
     * Whether the sessions of this corpus read one root differently.
     *
     * <p>A root every replay read the same way separates no family arm from
     * another, so an arm states no equality for it.</p>
     */
    public boolean varied(String rootId) {
        Map<String, RootMintRow> bySession = rootsById.get(rootId);
        if (bySession == null) return false;
        Set<String> readings = new LinkedHashSet<String>();
        for (RootMintRow row : bySession.values()) {
            readings.add(row.recordedValue());
        }
        return readings.size() > 1;
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
    public String[] domainOf(RootMintRow root) {
        if (root == null || root.kind() == RootKind.CLOCK) return null;
        RootDomain declared = declaredDomains.get(root.rootId());
        String min = declared == null ? root.domainMin()
                : resolve(declared.min(), root.recordedValue());
        String max = declared == null ? root.domainMax()
                : resolve(declared.max(), root.recordedValue());
        if (min == null || max == null || min.isEmpty() || max.isEmpty()) {
            return null;
        }
        return new String[]{min, max};
    }

    /** One declared bound as an absolute integer; relative bounds resolved. */
    static String resolve(String bound, String recorded) {
        String stated = bound == null ? "" : bound.trim();
        if (stated.isEmpty()) return "";
        try {
            if (stated.startsWith("+") || stated.startsWith("-")) {
                String offset = stated.startsWith("+")
                        ? stated.substring(1) : stated;
                return new BigInteger(recorded.trim())
                        .add(new BigInteger(offset.trim())).toString();
            }
            return new BigInteger(stated).toString();
        } catch (NumberFormatException malformed) {
            return "";
        }
    }
}
