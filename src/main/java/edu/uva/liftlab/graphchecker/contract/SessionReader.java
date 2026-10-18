package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
 *
 * <p>Its reads and writes, and its gaps, are held as read, or -- taken into a
 * {@link RowHold} -- let go of by the hold and read again from their files
 * when next asked for, value for value the rows read first.</p>
 */
public final class SessionReader {
    private final SessionDir directory;
    private final List<ActivationRow> activations;
    private final List<DecisionRow> decisions;
    private final List<ExportRow> exports;
    private final List<AttachRow> attaches;
    /** Its reads and writes, null while its hold has let them go. */
    private volatile State state;
    private final List<RootMintRow> roots;
    private final List<TargetRow> targets;
    /** Its gaps, null while its hold has let them go. */
    private volatile List<GapRow> gaps;
    /** {@link #answered}, from its gaps as read. */
    private final Set<String> answered;
    private final List<ObligationResult> obligations;
    private final ExpressionTable expressions;
    private final SessionManifest manifest;
    private final String incomplete;
    /** The hold that may let its rows go ({@link RowHold#take}); null:
     *  held for good. */
    private volatile RowHold hold;
    /** What its reads and writes, and its gaps, decode to; -1 until asked
     *  ({@link #heldBytes}). */
    private volatile long stateBytes = -1L;
    private volatile long gapBytes = -1L;

    /** Its reads and writes: one unit of a hold ({@link
     *  RowHold.Kind#STATE}). */
    private static final class State {
        final List<WriteRow> writes;
        final List<ReadRow> reads;

        State(List<WriteRow> writes, List<ReadRow> reads) {
            this.writes = Collections.unmodifiableList(writes);
            this.reads = Collections.unmodifiableList(reads);
        }
    }

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
        this.state = new State(writes, reads);
        this.roots = Collections.unmodifiableList(roots);
        this.targets = Collections.unmodifiableList(targets);
        this.gaps = Collections.unmodifiableList(gaps);
        this.answered = answered(gaps);
        this.obligations = Collections.unmodifiableList(obligations);
        this.expressions = expressions;
    }

    /**
     * Sessions read one by one with one pool among them ({@link RowPool}),
     * as {@link #readAll} reads them all: a corpus that holds only some of
     * its sessions' rows ({@link RowHold}) reads them a few at a time.
     */
    public static final class Pooled {
        private final RowPool pool = new RowPool();

        public SessionReader read(SessionDir dir) throws IOException {
            return SessionReader.read(dir, pool);
        }
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
     * Every session of one iteration -- or those {@code named} names, a
     * corpus stated by its list ({@link SessionDir#named}); null names every
     * session the iteration holds -- in the layout's own order, sharing one
     * pool (the sessions of a corpus spell the same call sites), each session
     * {@code held} already read from the same directory taken as it is: a
     * landed session's rows never change (it lands whole, in one rename),
     * and reading them is what a corpus read costs.
     */
    public static List<SessionReader> readAll(Path iteration,
                                              List<SessionReader> held,
                                              Collection<String> named)
            throws IOException {
        Map<SessionDir, SessionReader> kept =
                new HashMap<SessionDir, SessionReader>();
        for (SessionReader session : held) {
            kept.put(session.directory, session);
        }
        Pooled reader = new Pooled();
        return Parallel.map(named == null
                        ? SessionDir.sessionsIn(iteration)
                        : SessionDir.named(iteration, named),
                dir -> kept.containsKey(dir) ? kept.get(dir)
                        : reader.read(dir), Parallel.READS);
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
        return state().writes;
    }

    public List<ReadRow> reads() {
        return state().reads;
    }

    /** Its reads and writes, read again where its hold let them go. */
    private State state() {
        State held = state;
        RowHold holding = hold;
        if (holding == null) return held;
        if (held != null) {
            holding.used(this, RowHold.Kind.STATE);
            return held;
        }
        synchronized (this) {
            held = state;
            if (held == null) {
                held = reread();
                state = held;
            }
        }
        holding.loaded(this, RowHold.Kind.STATE);
        return held;
    }

    /** Its reads and writes read again, the two files side by side (about
     *  as large: SGF8-adhoc-07's 7.7 and 7.0 GB). */
    @SuppressWarnings("unchecked")
    private State reread() {
        RowPool pool = new RowPool();
        Object[] read = new Object[2];
        try {
            Parallel.map(Arrays.asList(0, 1), which -> {
                read[which] = which == 0 ? again(directory.writes(),
                        json -> RowCodec.readWrite(json, pool), pool)
                        : again(directory.reads(),
                        json -> RowCodec.readRead(json, pool), pool);
                return which;
            }, 2);
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        return new State((List<WriteRow>) read[0], (List<ReadRow>) read[1]);
    }

    /** One file of rows its hold let go of, read again: what it read first
     *  read whole, so a failure now is a fault of the files, thrown. */
    private static <T> List<T> again(Path file, Function<JsonObject, T> reader,
                                     RowPool pool) {
        try {
            return Files.isRegularFile(file)
                    ? RowCodec.readAll(file, pool, reader)
                    : Collections.<T>emptyList();
        } catch (IOException | RuntimeException unreadable) {
            throw new IllegalStateException("the rows " + file + " held were"
                    + " let go of and do not read again: " + unreadable,
                    unreadable);
        }
    }

    /** Taken into {@code hold}, which may let its rows go from now on. */
    void heldBy(RowHold hold) {
        this.hold = hold;
    }

    /** Lets {@code kind} of its rows go (its hold's call, {@link
     *  RowHold#loaded}): read again when next asked for. */
    void release(RowHold.Kind kind) {
        if (kind == RowHold.Kind.STATE) {
            state = null;
        } else {
            gaps = null;
        }
    }

    /** What {@code kind} of its rows decode to, as its files state. */
    long heldBytes(RowHold.Kind kind) {
        if (kind == RowHold.Kind.STATE) {
            long bytes = stateBytes;
            if (bytes < 0L) {
                bytes = RowHold.decoded(directory.reads(), directory.writes());
                stateBytes = bytes;
            }
            return bytes;
        }
        long bytes = gapBytes;
        if (bytes < 0L) {
            bytes = RowHold.decoded(directory.gaps());
            gapBytes = bytes;
        }
        return bytes;
    }

    /** The directory it was read from. */
    SessionDir directory() {
        return directory;
    }

    public List<RootMintRow> roots() {
        return roots;
    }

    public List<TargetRow> targets() {
        return targets;
    }

    /** What the run refused or noted, each on the subject it names. */
    public List<GapRow> gaps() {
        List<GapRow> held = gaps;
        RowHold holding = hold;
        if (holding == null) return held;
        if (held != null) {
            holding.used(this, RowHold.Kind.GAPS);
            return held;
        }
        synchronized (this) {
            held = gaps;
            if (held == null) {
                held = Collections.unmodifiableList(again(directory.gaps(),
                        RowCodec::readGap, new RowPool()));
                gaps = held;
            }
        }
        holding.loaded(this, RowHold.Kind.GAPS);
        return held;
    }

    /**
     * The occurrences this run answered by their shape (IDENTITY §9): the
     * planned address each of its {@code ADDRESS_UNSTABLE} rows names
     * ({@code runtime.RowRuntime#answered}).  Each ran under a chain of the
     * planned one's shape whose counts differ, so whom it was paired with is
     * that chain's, not the recorded one's.
     */
    public Set<String> answered() {
        return answered;
    }

    private static Set<String> answered(List<GapRow> gaps) {
        Set<String> occurrences = new LinkedHashSet<String>();
        for (GapRow gap : gaps) {
            if (gap.kind() == GapKind.ADDRESS_UNSTABLE) {
                occurrences.add(gap.subject());
            }
        }
        return Collections.unmodifiableSet(occurrences);
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
        // A forced world is no world: its rows are its forced path's alone.
        if (forced() || obligations.isEmpty()) return false;
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

    /** Whether this session states it ran forced (PIPELINE §7.10). */
    public boolean forced() {
        return manifest != null && manifest.forced();
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
