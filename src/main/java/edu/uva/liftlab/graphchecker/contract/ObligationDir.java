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
    /**
     * The question this worker's answer settles
     * ({@code explore.ObligationFactory#question}): written by the solver
     * for a verdict of its own, and for a replay's by the worker once the
     * replay decided it.  A solver timeout, a replay killed on its bound, a
     * publication the replay ended without, or a worker that did not finish
     * settles none.
     */
    public static final String QUESTION = "question.txt";
    /** The question a SAT solver asked, until its replay decides it. */
    public static final String QUESTION_ASKED = "question.asked";

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

    /** One settled question's answer: the obligation that asked it, and
     *  the verdict its worker wrote. */
    public static final class Answer {
        public final String obligationId;
        public final ObligationResult result;

        private Answer(String obligationId, ObligationResult result) {
            this.obligationId = obligationId;
            this.result = result;
        }
    }

    /**
     * Every question one iteration's workers settled ({@link #QUESTION}),
     * with its first answer in wave and name order that still stands: its
     * worker still holds the question, and an ADMITTED one's session is
     * still in the corpus (taken back -- an unfinished worker, a session
     * GROW moved aside -- it settles nothing).
     */
    public static Map<String, Answer> answered(Path iteration)
            throws IOException {
        Map<String, Answer> answered = new LinkedHashMap<String, Answer>();
        for (Path wave : SessionDir.directories(iteration, WAVES)) {
            for (Path worker : SessionDir.directories(wave, "*")) {
                Path file = worker.resolve(QUESTION);
                if (!Files.isRegularFile(file)) continue;
                String question = new String(Files.readAllBytes(file),
                        StandardCharsets.UTF_8).trim();
                List<ObligationResult> rows = RowCodec.readAll(
                        worker.resolve(RESULT),
                        RowCodec::readObligationResult);
                if (question.isEmpty() || rows.isEmpty()) continue;
                ObligationResult result = rows.get(rows.size() - 1);
                if (result.verdict() == Verdict.SAT_MODEL_READY) continue;
                if (result.verdict() == Verdict.ADMITTED
                        && (result.sessionId().isEmpty()
                        || !Files.isDirectory(SessionDir.of(iteration,
                        result.sessionId()).dir()))) {
                    continue;
                }
                answered.putIfAbsent(question, new Answer(
                        worker.getFileName().toString(), result));
            }
        }
        return answered;
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
