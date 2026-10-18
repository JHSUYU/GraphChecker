package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * CONTRACT-SPEC §2.1: the file layout of one replay session,
 * {@code <iteration>/sessions/<sessionId>/}, one gzip-compressed JSONL file
 * per row kind ({@code smt.ArtifactIO#GZIP}: every reader opens it through
 * {@code ArtifactIO#input}) and the manifest, plain JSON.  The rows were the
 * bytes every stage moved over NFS: SGF8-adhoc-05 round 5's corpus, 342
 * sessions, 19.1 GB as text, each host solver and the planner reading it
 * whole.
 */
public final class SessionDir extends Value {
    public static final String SESSIONS = "sessions";
    public static final String ACTIVATIONS = "activations.jsonl.gz";
    public static final String DECISIONS = "decisions.jsonl.gz";
    public static final String EXPORTS = "exports.jsonl.gz";
    public static final String ATTACHES = "attaches.jsonl.gz";
    public static final String WRITES = "writes.jsonl.gz";
    public static final String READS = "reads.jsonl.gz";
    public static final String ROOTS = "roots.jsonl.gz";
    public static final String TARGETS = "targets.jsonl.gz";
    public static final String GAPS = "gaps.jsonl.gz";
    /**
     * The replay's verdict per obligation run; the authority, never the
     * wave's aggregate copy.  A SEED states none.
     */
    public static final String OBLIGATIONS = "obligations.jsonl.gz";
    /** The run's {@link ScheduleEvent}s in order; not a row kind. */
    public static final String SCHEDULE = "schedule.jsonl.gz";
    public static final String EXPRESSIONS = "expressions.jsonl.gz";
    /** The role this session STATES it ran as ({@link SessionManifest}). */
    public static final String MANIFEST = "manifest.json";

    private final Path dir;
    private final String sessionId;

    private SessionDir(Path dir, String sessionId) {
        this.dir = dir;
        this.sessionId = sessionId;
    }

    public static SessionDir of(Path iteration, String sessionId) {
        String session = Fields.text(sessionId, "sessionId");
        return new SessionDir(Fields.required(iteration, "iteration")
                .resolve(SESSIONS).resolve(session), session);
    }

    /** A session directory wherever it stands: in an iteration's corpus,
     *  or staged in the worker that replayed it, before it lands; its name
     *  is its session id. */
    public static SessionDir at(Path dir) {
        Path name = Fields.required(dir, "dir").getFileName();
        return new SessionDir(dir, Fields.text(name == null ? ""
                : name.toString(), "sessionId"));
    }

    /**
     * The sessions GROW's swaps withdrew from an iteration's corpus, one per
     * line, beside it: made empty as the exploration starts, before any
     * solver serves, and each appended by the head before its directory
     * leaves ({@code run_engine.sh campaign_explore},
     * {@code campaign_stream_swap}).
     */
    public static final String WITHDRAWN = "withdrawn.txt";

    /**
     * The sessions {@link #WITHDRAWN} names.  Opened, never looked up first:
     * an open reads the file as the head closed it (NFS close-to-open), where
     * a stat may answer from a lookup cached as absent for up to a minute.
     * Absent, it is a corpus whose exploration has not started: none left.
     */
    public static Set<String> withdrawn(Path iteration) throws IOException {
        return listed(iteration, WITHDRAWN);
    }

    /**
     * The exposing sessions of an iteration's corpus whose GROW re-run did
     * not land -- dropped, never run, or not finished -- one per line, beside
     * it: written as the exploration ends, unless a witness ended it ({@code
     * run_engine.sh campaign_stream_uncaptured}).  The regions GROW grew ran
     * uninstrumented in each, so a version a read of it saw that no write row
     * states may be such a region's write ({@code compose.Composer}: free,
     * never held).
     */
    public static final String UNCAPTURED = "uncaptured_sessions.txt";

    /** The sessions {@link #UNCAPTURED} names; absent, none. */
    public static Set<String> uncaptured(Path iteration) throws IOException {
        return listed(iteration, UNCAPTURED);
    }

    /** The sessions an iteration's list {@code file} names, one per line;
     *  absent, none. */
    private static Set<String> listed(Path iteration, String file)
            throws IOException {
        Set<String> named = new HashSet<String>();
        List<String> lines;
        try {
            lines = Files.readAllLines(iteration.resolve(file),
                    StandardCharsets.UTF_8);
        } catch (NoSuchFileException absent) {
            return named;
        }
        for (String line : lines) {
            if (!line.trim().isEmpty()) named.add(line.trim());
        }
        return named;
    }

    /** The sessions an iteration directory holds, in name order. */
    public static List<SessionDir> sessionsIn(Path iteration)
            throws IOException {
        List<SessionDir> found = new ArrayList<>();
        for (Path session : directories(Fields.required(iteration,
                "iteration").resolve(SESSIONS), "*")) {
            found.add(of(iteration, session.getFileName().toString()));
        }
        return found;
    }

    /**
     * The sessions {@code sessionIds} names in an iteration directory, in
     * name order: a corpus stated by its list (an EXPLORE round's, frozen as
     * its planner starts while the campaign goes on landing).  A named
     * session the iteration does not hold is an error, never skipped.
     */
    public static List<SessionDir> named(Path iteration,
                                         Collection<String> sessionIds)
            throws IOException {
        List<SessionDir> found = new ArrayList<>();
        for (String sessionId : new TreeSet<String>(sessionIds)) {
            SessionDir session = of(iteration, sessionId);
            if (!Files.isDirectory(session.dir)) {
                throw new NoSuchFileException(session.dir.toString(), null,
                        "a corpus names a session its iteration does not "
                                + "hold");
            }
            found.add(session);
        }
        return found;
    }

    /**
     * The directories in {@code parent} whose names match {@code glob}, in
     * name order; none when {@code parent} is not there.
     */
    static List<Path> directories(Path parent, String glob)
            throws IOException {
        List<Path> found = new ArrayList<>();
        if (parent == null || !Files.isDirectory(parent)) return found;
        try (DirectoryStream<Path> entries =
                     Files.newDirectoryStream(parent, glob)) {
            for (Path entry : entries) {
                if (Files.isDirectory(entry)) found.add(entry);
            }
        }
        Collections.sort(found);
        return found;
    }

    /** Creates the directory if it is not there yet. */
    public SessionDir create() throws IOException {
        Files.createDirectories(dir);
        return this;
    }

    public Path dir() {
        return dir;
    }

    public String sessionId() {
        return sessionId;
    }

    public Path activations() {
        return dir.resolve(ACTIVATIONS);
    }

    public Path decisions() {
        return dir.resolve(DECISIONS);
    }

    public Path exports() {
        return dir.resolve(EXPORTS);
    }

    public Path attaches() {
        return dir.resolve(ATTACHES);
    }

    public Path writes() {
        return dir.resolve(WRITES);
    }

    public Path reads() {
        return dir.resolve(READS);
    }

    public Path roots() {
        return dir.resolve(ROOTS);
    }

    public Path targets() {
        return dir.resolve(TARGETS);
    }

    public Path gaps() {
        return dir.resolve(GAPS);
    }

    public Path obligations() {
        return dir.resolve(OBLIGATIONS);
    }

    public Path schedule() {
        return dir.resolve(SCHEDULE);
    }

    public Path expressions() {
        return dir.resolve(EXPRESSIONS);
    }

    public Path manifest() {
        return dir.resolve(MANIFEST);
    }

    @Override
    Object[] parts() {
        return new Object[] {dir};
    }

    @Override
    public String toString() {
        return dir.toString();
    }
}
