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
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;

public final class SessionReader {
    private final SessionDir directory;
    private final List<ActivationRow> activations;
    private final List<DecisionRow> decisions;
    private final List<ExportRow> exports;
    private final List<AttachRow> attaches;
    private volatile State state;
    private final List<RootMintRow> roots;
    private final List<TargetRow> targets;
    private final Map<GapKind, List<GapRow>> gaps;
    private final List<ObligationResult> obligations;
    private final ExpressionTable expressions;
    private final SessionManifest manifest;
    private final String incomplete;
    private volatile RowHold hold;
    private volatile long stateBytes = -1L;

    private static final class State {
        final List<WriteRow> writes;
        final List<ReadRow> reads;

        State(List<WriteRow> writes, List<ReadRow> reads) {
            this.writes = Collections.unmodifiableList(writes);
            this.reads = Collections.unmodifiableList(reads);
        }
    }

    private static final Set<GapKind> HELD_GAPS = Collections.unmodifiableSet(
            EnumSet.of(GapKind.ADDRESS_UNSTABLE, GapKind.BOUND_INSUFFICIENT,
                    GapKind.UNPLANNED_INPUT, GapKind.UNSTATED_VALUE));

    private static Map<GapKind, List<GapRow>> held(List<GapRow> read) {
        Map<GapKind, List<GapRow>> byKind =
                new EnumMap<GapKind, List<GapRow>>(GapKind.class);
        for (GapRow gap : read) {
            if (gap == null) continue;
            byKind.computeIfAbsent(gap.kind(),
                    kind -> new ArrayList<GapRow>()).add(gap);
        }
        for (Map.Entry<GapKind, List<GapRow>> kind : byKind.entrySet()) {
            kind.setValue(Collections.unmodifiableList(kind.getValue()));
        }
        return byKind;
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
        this.gaps = held(gaps);
        this.obligations = Collections.unmodifiableList(obligations);
        this.expressions = expressions;
    }

    public static final class Pooled {
        private final RowPool pool = new RowPool();

        public SessionReader read(SessionDir dir) throws IOException {
            return SessionReader.read(dir, pool);
        }
    }

    public static SessionReader read(Path iteration, String sessionId)
            throws IOException {
        return read(SessionDir.of(iteration, sessionId));
    }

    public static SessionReader read(SessionDir dir) throws IOException {
        return read(dir, new RowPool());
    }

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
        List<GapRow> gaps = partial.rows(dir.gaps(), json -> {
            GapRow gap = RowCodec.readGap(json);
            return HELD_GAPS.contains(gap.kind()) ? gap : null;
        });
        List<ObligationResult> obligations = partial.rows(dir.obligations(),
                RowCodec::readObligationResult);
        ExpressionTable expressions = partial.read(dir.expressions(),
                file -> SessionExpressionLog.read(file, pool),
                ExpressionTable.empty());
        SessionManifest manifest = partial.read(dir.manifest(),
                file -> RowCodec.readManifest(file, pool), null);
        return new SessionReader(dir, activations, decisions, exports,
                attaches, writes, reads, roots, targets, gaps, obligations,
                expressions, manifest, partial.reason);
    }

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

    public static List<ScheduleEvent> readSchedule(SessionDir dir)
            throws IOException {
        return readSchedule(dir.schedule());
    }

    public List<ScheduleEvent> schedule() throws IOException {
        return readSchedule(directory);
    }

    public static List<ScheduleEvent> readSchedule(Path file)
            throws IOException {
        List<ScheduleEvent> events = new ArrayList<ScheduleEvent>();
        schedulePrefix(file, row -> {
            if (!row.has("mark")) events.add(RowCodec.readScheduleEvent(row));
        });
        return events;
    }

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

    private State state() {
        State held = state;
        RowHold holding = hold;
        if (holding == null) return held;
        if (held != null) {
            holding.used(this);
            return held;
        }
        synchronized (this) {
            held = state;
            if (held == null) {
                held = reread();
                state = held;
            }
        }
        holding.loaded(this);
        return held;
    }

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

    void heldBy(RowHold hold) {
        this.hold = hold;
    }

    void release() {
        state = null;
    }

    long heldBytes() {
        long bytes = stateBytes;
        if (bytes < 0L) {
            bytes = RowHold.decoded(directory.reads(), directory.writes());
            stateBytes = bytes;
        }
        return bytes;
    }

    public List<RootMintRow> roots() {
        return roots;
    }

    public List<TargetRow> targets() {
        return targets;
    }

    public List<GapRow> gaps(GapKind kind) {
        if (!HELD_GAPS.contains(kind)) {
            throw new IllegalArgumentException("a session's " + kind
                    + " gaps are not held: only " + HELD_GAPS);
        }
        List<GapRow> rows = gaps.get(kind);
        return rows == null ? Collections.<GapRow>emptyList() : rows;
    }

    public Set<String> answered() {
        Set<String> occurrences = new LinkedHashSet<String>();
        for (GapRow gap : gaps(GapKind.ADDRESS_UNSTABLE)) {
            occurrences.add(gap.subject());
        }
        return occurrences;
    }

    public List<ObligationResult> obligations() {
        return obligations;
    }

    public boolean admitted() {
        if (seed()) return true;
        if (forced() || obligations.isEmpty()) return false;
        for (ObligationResult result : obligations) {
            if (result.verdict() != Verdict.ADMITTED) return false;
        }
        return true;
    }

    public ExpressionTable expressions() {
        return expressions;
    }

    public SessionManifest manifest() {
        return manifest;
    }

    public boolean seed() {
        return manifest != null && manifest.seed();
    }

    public boolean forced() {
        return manifest != null && manifest.forced();
    }

    public String incomplete() {
        return incomplete;
    }

    public static String seedSessionId(List<SessionReader> sessions) {
        List<String> stated = seedSessionIds(sessions);
        return stated.size() == 1 ? stated.get(0) : null;
    }

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
