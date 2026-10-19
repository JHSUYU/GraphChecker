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
    public static final String OBLIGATIONS = "obligations.jsonl.gz";
    public static final String SCHEDULE = "schedule.jsonl.gz";
    public static final String EXPRESSIONS = "expressions.jsonl.gz";
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

    public static SessionDir at(Path dir) {
        Path name = Fields.required(dir, "dir").getFileName();
        return new SessionDir(dir, Fields.text(name == null ? ""
                : name.toString(), "sessionId"));
    }

    public static final String WITHDRAWN = "withdrawn.txt";

    public static Set<String> withdrawn(Path iteration) throws IOException {
        return listed(iteration, WITHDRAWN);
    }

    public static final String UNCAPTURED = "uncaptured_sessions.txt";

    public static Set<String> uncaptured(Path iteration) throws IOException {
        return listed(iteration, UNCAPTURED);
    }

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

    public static List<SessionDir> sessionsIn(Path iteration)
            throws IOException {
        List<SessionDir> found = new ArrayList<>();
        for (Path session : directories(Fields.required(iteration,
                "iteration").resolve(SESSIONS), "*")) {
            found.add(of(iteration, session.getFileName().toString()));
        }
        return found;
    }

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
