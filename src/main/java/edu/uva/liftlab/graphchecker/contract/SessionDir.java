package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * CONTRACT-SPEC §2.1: the file layout of one replay session,
 * {@code <iteration>/sessions/<sessionId>/}, one JSONL file per row kind.
 */
public final class SessionDir extends Value {
    public static final String SESSIONS = "sessions";
    public static final String ACTIVATIONS = "activations.jsonl";
    public static final String DECISIONS = "decisions.jsonl";
    public static final String EXPORTS = "exports.jsonl";
    public static final String ATTACHES = "attaches.jsonl";
    public static final String WRITES = "writes.jsonl";
    public static final String READS = "reads.jsonl";
    public static final String ROOTS = "roots.jsonl";
    public static final String TARGETS = "targets.jsonl";
    public static final String GAPS = "gaps.jsonl";
    /**
     * The replay's verdict per obligation run; the authority, never the
     * wave's aggregate copy.  A SEED states none.
     */
    public static final String OBLIGATIONS = "obligations.jsonl";
    /** The run's {@link ScheduleEvent}s in order; not a row kind. */
    public static final String SCHEDULE = "schedule.jsonl";
    public static final String EXPRESSIONS = "expressions.jsonl";
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
