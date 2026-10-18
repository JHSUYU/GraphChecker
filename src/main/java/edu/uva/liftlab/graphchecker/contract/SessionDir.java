package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
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
