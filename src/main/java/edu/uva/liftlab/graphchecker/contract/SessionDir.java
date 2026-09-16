package edu.uva.liftlab.graphchecker.contract;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * CONTRACT-SPEC 2: the file layout of one replay session.
 *
 * <p>{@code <iteration>/sessions/<sessionId>/} with one JSONL file per row kind
 * and the session's {@code expressions.json}.  One kind per file is the whole
 * point: a reader of reads must never have to parse writes, and a stage that
 * only needs targets must not pay for the decisions.</p>
 */
public final class SessionDir {
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
    public static final String EXPRESSIONS = "expressions.json";
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
        Path sessions = Fields.required(iteration, "iteration")
                .resolve(SESSIONS);
        List<SessionDir> found = new ArrayList<>();
        if (!Files.isDirectory(sessions)) return found;
        List<String> names = new ArrayList<>();
        try (DirectoryStream<Path> entries =
                     Files.newDirectoryStream(sessions)) {
            for (Path entry : entries) {
                if (Files.isDirectory(entry)) {
                    names.add(entry.getFileName().toString());
                }
            }
        }
        Collections.sort(names);
        for (String name : names) {
            found.add(of(iteration, name));
        }
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

    public Path expressions() {
        return dir.resolve(EXPRESSIONS);
    }

    public Path manifest() {
        return dir.resolve(MANIFEST);
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof SessionDir)) return false;
        return dir.equals(((SessionDir) value).dir);
    }

    @Override
    public int hashCode() {
        return Objects.hash(dir);
    }

    @Override
    public String toString() {
        return dir.toString();
    }
}
