package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
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
    private final List<GapRow> gaps;
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
                          List<GapRow> gaps,
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
        this.gaps = Collections.unmodifiableList(gaps);
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
        return read(dir, new RowPool());
    }

    /** One session, its values shared with every session read with the
     *  same pool ({@link RowPool}). */
    private static SessionReader read(SessionDir dir, RowPool pool)
            throws IOException {
        Partial partial = new Partial(pool);
        List<ActivationRow> activations = partial.rows(dir.activations(),
                json -> RowCodec.readActivation(json, pool));
        List<DecisionRow> decisions = partial.rows(dir.decisions(),
                json -> RowCodec.readDecision(json, pool));
        List<ExportRow> exports = partial.rows(dir.exports(),
                json -> RowCodec.readExport(json, pool));
        List<AttachRow> attaches = partial.rows(dir.attaches(),
                json -> RowCodec.readAttach(json, pool));
        List<WriteRow> writes = partial.rows(dir.writes(),
                json -> RowCodec.readWrite(json, pool));
        List<ReadRow> reads = partial.rows(dir.reads(),
                json -> RowCodec.readRead(json, pool));
        List<RootMintRow> roots = partial.rows(dir.roots(),
                json -> RowCodec.readRootMint(json, pool));
        List<TargetRow> targets = partial.rows(dir.targets(),
                json -> RowCodec.readTarget(json, pool));
        List<GapRow> gaps = partial.rows(dir.gaps(), RowCodec::readGap);
        List<ObligationResult> obligations = partial.rows(dir.obligations(),
                RowCodec::readObligationResult);
        ExpressionTable expressions = partial.read(dir.expressions(),
                file -> SessionExpressionLog.read(file, pool),
                ExpressionTable.empty());
        SessionManifest manifest = partial.read(dir.manifest(),
                RowCodec::readManifest, null);
        return new SessionReader(dir, activations, decisions, exports,
                attaches, writes, reads, roots, targets, gaps, obligations,
                expressions, manifest, partial.reason);
    }

    /**
     * One session's manifest and root rows only: what an epoch-wide check
     * needs of every session before it reads any one of them whole.
     */
    public static SessionReader readHeader(SessionDir dir) throws IOException {
        RowPool pool = new RowPool();
        Partial partial = new Partial(pool);
        List<RootMintRow> roots = partial.rows(dir.roots(),
                json -> RowCodec.readRootMint(json, pool));
        SessionManifest manifest = partial.read(dir.manifest(),
                RowCodec::readManifest, null);
        return new SessionReader(dir, Collections.<ActivationRow>emptyList(),
                Collections.<DecisionRow>emptyList(),
                Collections.<ExportRow>emptyList(),
                Collections.<AttachRow>emptyList(),
                Collections.<WriteRow>emptyList(),
                Collections.<ReadRow>emptyList(), roots,
                Collections.<TargetRow>emptyList(),
                Collections.<GapRow>emptyList(),
                Collections.<ObligationResult>emptyList(),
                ExpressionTable.empty(), manifest, partial.reason);
    }

    /** One session's read, and the first file of it that would not read. */
    private static final class Partial {
        private final RowPool pool;
        private String reason = "";

        private Partial(RowPool pool) {
            this.pool = pool;
        }

        private <T> List<T> rows(Path file, Function<JsonObject, T> reader)
                throws IOException {
            return read(file, path -> RowCodec.readAll(path, pool, reader),
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

    /**
     * The invocation of a parameterized test a schedule file states it ran
     * ({@link ScheduleEvent#INVOCATION}), its row whole; null when it states
     * none.
     */
    public static JsonObject readScheduleInvocation(Path file)
            throws IOException {
        JsonObject[] stated = new JsonObject[1];
        schedulePrefix(file, row -> {
            if (stated[0] == null && row.has("mark") && ScheduleEvent
                    .INVOCATION.equals(row.get("mark").getAsString())) {
                stated[0] = row;
            }
        });
        return stated[0];
    }

    /** The startup marks a schedule file states ({@link
     *  ScheduleEvent#STARTUP}), whole, in their order. */
    public static List<JsonObject> readScheduleStartup(Path file)
            throws IOException {
        List<JsonObject> marks = new ArrayList<JsonObject>();
        schedulePrefix(file, row -> {
            if (row.has("mark") && ScheduleEvent.STARTUP.equals(
                    row.get("mark").getAsString())) {
                marks.add(row);
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

    /**
     * Every session of one iteration, in the layout's own order, sharing one
     * pool (the sessions of a corpus spell the same call sites), each session
     * {@code held} already read from the same directory taken as it is: a
     * landed session's rows never change (it lands whole, in one rename),
     * and reading them is what a corpus read costs.
     */
    public static List<SessionReader> readAll(Path iteration,
                                              List<SessionReader> held)
            throws IOException {
        Map<SessionDir, SessionReader> kept =
                new HashMap<SessionDir, SessionReader>();
        for (SessionReader session : held) {
            kept.put(session.directory, session);
        }
        RowPool pool = new RowPool();
        return ParallelReads.each(SessionDir.sessionsIn(iteration),
                dir -> kept.containsKey(dir) ? kept.get(dir)
                        : read(dir, pool), iteration);
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

    /** What the run refused or noted, each on the subject it names. */
    public List<GapRow> gaps() {
        return gaps;
    }

    /**
     * The occurrences this run answered by their shape (IDENTITY §9): the
     * planned address each of its {@code ADDRESS_UNSTABLE} rows names
     * ({@code runtime.RowRuntime#answered}).  Each ran under a chain of the
     * planned one's shape whose counts differ, so whom it was paired with is
     * that chain's, not the recorded one's.
     */
    public Set<String> answered() {
        Set<String> occurrences = new LinkedHashSet<String>();
        for (GapRow gap : gaps) {
            if (gap.kind() == GapKind.ADDRESS_UNSTABLE) {
                occurrences.add(gap.subject());
            }
        }
        return occurrences;
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
