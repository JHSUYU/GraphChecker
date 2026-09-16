package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * CONTRACT-SPEC 2: one obligation worker's directory, and the session it ran.
 *
 * <p>{@code <iteration>/obligations-<wave>/<obligationId>/} holds the ASK
 * ({@code obligation.jsonl}, the flip and the root values the wave solved
 * for), the ANSWER ({@code obligation_result.jsonl}) and the focus row the
 * replay was driven by ({@code focused_task.jsonl}).</p>
 *
 * <p>The join from a worker to the session its replay published is the
 * RESULT ROW, never the directory name: an obligation whose replay never
 * published a session names none, and a reader that guessed from the
 * directory would attribute a wave's assignment to a session that does not
 * exist.  This is the one place that walk and that join are written --
 * IMPORT's invariant 10 and the composer's per-path valuation both read it
 * here, and an obligation ledger with two implementations is two answers to
 * "what did this replay run under".</p>
 */
public final class ObligationDir {
    public static final String OBLIGATION = "obligation.jsonl";
    public static final String RESULT = "obligation_result.jsonl";
    public static final String FOCUSED_TASK = "focused_task.jsonl";

    /** The wave directories an iteration publishes, by name. */
    private static final String WAVES = "obligations-*";

    private final Path dir;
    private final String sessionId;

    private ObligationDir(Path dir, String sessionId) {
        this.dir = dir;
        this.sessionId = sessionId;
    }

    /**
     * Every obligation worker of one iteration, in wave and name order.
     *
     * <p>A directory that states no result row published no session and is
     * not a worker of this corpus: it is skipped here rather than answered
     * with an empty session id, so no caller has to know the difference.</p>
     */
    public static List<ObligationDir> workersIn(Path iteration)
            throws IOException {
        List<ObligationDir> workers = new ArrayList<ObligationDir>();
        if (iteration == null || !Files.isDirectory(iteration)) {
            return workers;
        }
        List<Path> waves = new ArrayList<Path>();
        try (DirectoryStream<Path> entries =
                     Files.newDirectoryStream(iteration, WAVES)) {
            for (Path wave : entries) {
                if (Files.isDirectory(wave)) waves.add(wave);
            }
        }
        Collections.sort(waves);
        for (Path wave : waves) {
            List<Path> dirs = new ArrayList<Path>();
            try (DirectoryStream<Path> entries =
                         Files.newDirectoryStream(wave)) {
                for (Path worker : entries) {
                    if (Files.isDirectory(worker)) dirs.add(worker);
                }
            }
            Collections.sort(dirs);
            for (Path worker : dirs) {
                String session = sessionOf(worker);
                if (session.isEmpty()) continue;
                workers.add(new ObligationDir(worker, session));
            }
        }
        return workers;
    }

    /** The session this worker's replay published, off its result row. */
    private static String sessionOf(Path worker) throws IOException {
        Path result = worker.resolve(RESULT);
        if (!Files.isRegularFile(result)) return "";
        String session = "";
        for (JsonObject row : RowCodec.readJsonl(result)) {
            if (row.has("sessionId")
                    && row.get("sessionId").isJsonPrimitive()) {
                session = row.get("sessionId").getAsString();
            }
        }
        return session == null ? "" : session;
    }

    public Path dir() {
        return dir;
    }

    /** The session this worker's replay published; never empty. */
    public String sessionId() {
        return sessionId;
    }

    /** The ask: the flip and the root values the wave solved for. */
    public Path obligation() {
        return dir.resolve(OBLIGATION);
    }

    /** The answer the worker published. */
    public Path result() {
        return dir.resolve(RESULT);
    }

    /** The focus row the replay was driven by. */
    public Path focusedTask() {
        return dir.resolve(FOCUSED_TASK);
    }
}
