package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * CONTRACT-SPEC §3: one obligation worker's directory
 * ({@code <iteration>/obligations-<wave>/<obligationId>/}: ask, answer, focus
 * row) and the session it ran.  The one place the worker-to-session join is
 * written: by the result row, never the directory name.
 */
public final class ObligationDir {
    public static final String OBLIGATION = "obligation.jsonl";
    /** The obligation's answer, written once by its worker. */
    public static final String RESULT = "obligation_result.jsonl";
    /** What a replay stated, which its worker makes the answer once the
     *  replay's process group is gone. */
    public static final String REPLAY_VERDICT = "replay_verdict.jsonl";
    public static final String FOCUSED_TASK = "focused_task.jsonl";
    /** The question the worker's solver asked, as one key
     *  ({@code explore.ObligationFactory#question}). */
    public static final String QUESTION = "question.txt";

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

    /**
     * Obligation id -> the question its solver asked, for every worker of
     * one iteration that states one (a solver that died states none).
     */
    public static Map<String, String> questions(Path iteration)
            throws IOException {
        Map<String, String> asked = new LinkedHashMap<String, String>();
        for (Path wave : SessionDir.directories(iteration, WAVES)) {
            for (Path worker : SessionDir.directories(wave, "*")) {
                Path file = worker.resolve(QUESTION);
                if (!Files.isRegularFile(file)) continue;
                String question = new String(Files.readAllBytes(file),
                        StandardCharsets.UTF_8).trim();
                if (!question.isEmpty()) {
                    asked.put(worker.getFileName().toString(), question);
                }
            }
        }
        return asked;
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
