package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * One replay session's rows, one file per kind, read once and whole (symbols,
 * versions and expression refs are session-local and joined across kinds).
 * The one reader of the corpus layout; interprets and lowers nothing.
 */
public final class SessionReader {
    private final SessionDir directory;
    private final List<ActivationRow> activations;
    private final List<DecisionRow> decisions;
    private final List<ExportRow> exports;
    private final List<AttachRow> attaches;
    private final List<WriteRow> writes;
    private final List<ReadRow> reads;
    private final List<RootMintRow> roots;
    private final List<TargetRow> targets;
    private final List<ObligationResult> obligations;
    private final ExpressionTable expressions;
    private final SessionManifest manifest;
    private final String incomplete;

    private SessionReader(SessionDir directory,
                          List<ActivationRow> activations,
                          List<DecisionRow> decisions,
                          List<ExportRow> exports, List<AttachRow> attaches,
                          List<WriteRow> writes, List<ReadRow> reads,
                          List<RootMintRow> roots, List<TargetRow> targets,
                          List<ObligationResult> obligations,
                          ExpressionTable expressions,
                          SessionManifest manifest, String incomplete) {
        this.manifest = manifest;
        this.incomplete = incomplete;
        this.directory = directory;
        this.activations = Collections.unmodifiableList(activations);
        this.decisions = Collections.unmodifiableList(decisions);
        this.exports = Collections.unmodifiableList(exports);
        this.attaches = Collections.unmodifiableList(attaches);
        this.writes = Collections.unmodifiableList(writes);
        this.reads = Collections.unmodifiableList(reads);
        this.roots = Collections.unmodifiableList(roots);
        this.targets = Collections.unmodifiableList(targets);
        this.obligations = Collections.unmodifiableList(obligations);
        this.expressions = expressions;
    }

    /** Reads one session directory of an iteration. */
    public static SessionReader read(Path iteration, String sessionId)
            throws IOException {
        return read(SessionDir.of(iteration, sessionId));
    }

    /**
     * Reads one session directory.  A file the codec refuses is recorded in
     * {@link #incomplete()}, not thrown; IMPORT refuses it as
     * SESSION_INCOMPLETE.
     */
    public static SessionReader read(SessionDir dir) throws IOException {
        Partial partial = new Partial();
        List<ActivationRow> activations = partial.rows(dir.activations(),
                RowCodec::readActivation);
        List<DecisionRow> decisions = partial.rows(dir.decisions(),
                RowCodec::readDecision);
        List<ExportRow> exports = partial.rows(dir.exports(),
                RowCodec::readExport);
        List<AttachRow> attaches = partial.rows(dir.attaches(),
                RowCodec::readAttach);
        List<WriteRow> writes = partial.rows(dir.writes(),
                RowCodec::readWrite);
        List<ReadRow> reads = partial.rows(dir.reads(), RowCodec::readRead);
        List<RootMintRow> roots = partial.rows(dir.roots(),
                RowCodec::readRootMint);
        List<TargetRow> targets = partial.rows(dir.targets(),
                RowCodec::readTarget);
        // Held by no one; read so an unreadable file still marks the session.
        partial.rows(dir.gaps(), RowCodec::readGap);
        List<ObligationResult> obligations = partial.rows(dir.obligations(),
                RowCodec::readObligationResult);
        ExpressionTable expressions = partial.read(dir.expressions(),
                RowCodec::readExpressions, ExpressionTable.empty());
        SessionManifest manifest = partial.read(dir.manifest(),
                RowCodec::readManifest, null);
        return new SessionReader(dir, activations, decisions, exports,
                attaches, writes, reads, roots, targets, obligations,
                expressions, manifest, partial.reason);
    }

    /**
     * One session's manifest and root rows only: what an epoch-wide check
     * needs of every session before it reads any one of them whole.
     */
    public static SessionReader readHeader(SessionDir dir) throws IOException {
        Partial partial = new Partial();
        List<RootMintRow> roots = partial.rows(dir.roots(),
                RowCodec::readRootMint);
        SessionManifest manifest = partial.read(dir.manifest(),
                RowCodec::readManifest, null);
        return new SessionReader(dir, Collections.<ActivationRow>emptyList(),
                Collections.<DecisionRow>emptyList(),
                Collections.<ExportRow>emptyList(),
                Collections.<AttachRow>emptyList(),
                Collections.<WriteRow>emptyList(),
                Collections.<ReadRow>emptyList(), roots,
                Collections.<TargetRow>emptyList(),
                Collections.<ObligationResult>emptyList(),
                ExpressionTable.empty(), manifest, partial.reason);
    }

    /** One session's read, and the first file of it that would not read. */
    private static final class Partial {
        private String reason = "";

        private <T> List<T> rows(Path file, Function<JsonObject, T> reader)
                throws IOException {
            return read(file, path -> RowCodec.readAll(path, reader),
                    Collections.<T>emptyList());
        }

        /** The file as {@code reader} reads it, else {@code unread}. */
        private <T> T read(Path file, PathReader<T> reader, T unread)
                throws IOException {
            try {
                return reader.read(file);
            } catch (RuntimeException unreadable) {
                if (reason.isEmpty()) {
                    Path name = file.getFileName();
                    reason = (name == null ? file.toString()
                            : name.toString()) + " could not be read: "
                            + unreadable.getMessage();
                }
                return unread;
            }
        }
    }

    private interface PathReader<T> {
        T read(Path file) throws IOException;
    }

    /**
     * The session's schedule in run order, read on demand (never held by the
     * corpus).  An unreadable line ends the read: events after a hole are no
     * prefix.
     */
    public static List<ScheduleEvent> readSchedule(SessionDir dir)
            throws IOException {
        return readSchedule(dir.schedule());
    }

    /** This session's schedule, read on demand. */
    public List<ScheduleEvent> schedule() throws IOException {
        return readSchedule(directory);
    }

    /** The same read, of a schedule file wherever it stands. */
    public static List<ScheduleEvent> readSchedule(Path file)
            throws IOException {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        schedulePrefix(file, row -> {
            if (!row.has("mark")) events.add(RowCodec.readScheduleEvent(row));
        });
        return events;
    }

    /**
     * Occurrence id to the position of the first schedule event after it
     * opened (the prefix cut); same tolerance as the events.
     */
    public static Map<String, Long> readScheduleMarks(Path file)
            throws IOException {
        Map<String, Long> marks = new LinkedHashMap<String, Long>();
        schedulePrefix(file, row -> {
            if (!row.has("mark")) return;
            String id = row.get("mark").getAsString();
            if (!marks.containsKey(id)) {
                marks.put(id, row.get("at").getAsLong());
            }
        });
        return marks;
    }

    /** Each row of a schedule file, up to the first one that will not read. */
    private static void schedulePrefix(Path file, Consumer<JsonObject> each)
            throws IOException {
        RowCodec.eachLine(file, line -> {
            try {
                each.accept(RowCodec.fromLine(line));
                return true;
            } catch (RuntimeException unreadable) {
                return false;
            }
        });
    }

    /** Every session of one iteration, in the layout's own order. */
    public static List<SessionReader> readAll(Path iteration)
            throws IOException {
        List<SessionReader> sessions = new ArrayList<SessionReader>();
        for (SessionDir dir : SessionDir.sessionsIn(iteration)) {
            sessions.add(read(dir));
        }
        return sessions;
    }

    public String sessionId() {
        return directory.sessionId();
    }

    public List<ActivationRow> activations() {
        return activations;
    }

    public List<DecisionRow> decisions() {
        return decisions;
    }

    public List<ExportRow> exports() {
        return exports;
    }

    public List<AttachRow> attaches() {
        return attaches;
    }

    public List<WriteRow> writes() {
        return writes;
    }

    public List<ReadRow> reads() {
        return reads;
    }

    public List<RootMintRow> roots() {
        return roots;
    }

    public List<TargetRow> targets() {
        return targets;
    }

    /** The replay's verdicts, one per obligation run; the only authority. */
    public List<ObligationResult> obligations() {
        return obligations;
    }

    /**
     * Only an admitted replay states a topology.  True for the SEED, or when
     * every own result row is {@link Verdict#ADMITTED} (no rows: false).
     * Never read the wave's aggregate file instead.
     */
    public boolean admitted() {
        if (seed()) return true;
        if (obligations.isEmpty()) return false;
        for (ObligationResult result : obligations) {
            if (result.verdict() != Verdict.ADMITTED) return false;
        }
        return true;
    }

    public ExpressionTable expressions() {
        return expressions;
    }

    /** The role this session states, or null; read, never inferred. */
    public SessionManifest manifest() {
        return manifest;
    }

    /** Whether this session states it is the recording. */
    public boolean seed() {
        return manifest != null && manifest.seed();
    }

    /** Why this session could not be read whole, or {@code ""}. */
    public String incomplete() {
        return incomplete;
    }

    /** The one session stating SEED, or null unless exactly one does. */
    public static String seedSessionId(List<SessionReader> sessions) {
        List<String> stated = seedSessionIds(sessions);
        return stated.size() == 1 ? stated.get(0) : null;
    }

    /** Every session that states SEED: what such a refusal names. */
    public static List<String> seedSessionIds(List<SessionReader> sessions) {
        List<String> stated = new ArrayList<String>();
        if (sessions == null) return stated;
        for (SessionReader session : sessions) {
            if (session.seed()) stated.add(session.sessionId());
        }
        return stated;
    }

    @Override
    public String toString() {
        return "session " + sessionId() + " (" + decisions.size()
                + " decisions, " + attaches.size() + " attaches)";
    }
}
