package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * CONTRACT-SPEC 2: one obligation worker's directory
 * ({@code <iteration>/obligations-<wave>/<obligationId>/}: ask, answer, focus
 * row) and the session it ran.  The one place the worker-to-session join is
 * written: by the result row, never the directory name.
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
     * Every obligation worker of one iteration, in wave and name order; a
     * directory with no result row published no session and is skipped.
     */
    public static List<ObligationDir> workersIn(Path iteration)
            throws IOException {
        List<ObligationDir> workers = new ArrayList<ObligationDir>();
        for (Path wave : SessionDir.directories(iteration, WAVES)) {
            for (Path worker : SessionDir.directories(wave, "*")) {
                String session = sessionOf(worker);
                if (session.isEmpty()) continue;
                workers.add(new ObligationDir(worker, session));
            }
        }
        return workers;
    }

    /** The session this worker's replay published, off its result row. */
    private static String sessionOf(Path worker) throws IOException {
        String session = "";
        for (JsonObject row : RowCodec.readJsonl(worker.resolve(RESULT))) {
            if (row.has("sessionId")
                    && row.get("sessionId").isJsonPrimitive()) {
                session = row.get("sessionId").getAsString();
            }
        }
        return session;
    }

    public Path dir() {
        return dir;
    }

    /** The session this worker's replay published; never empty. */
    public String sessionId() {
        return sessionId;
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
