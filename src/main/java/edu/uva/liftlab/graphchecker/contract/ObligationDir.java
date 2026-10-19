package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class ObligationDir {
    public static final String OBLIGATION = "obligation.jsonl";
    public static final String RESULT = "obligation_result.jsonl";
    public static final String REPLAY_VERDICT = "replay_verdict.jsonl";
    public static final String FOCUSED_TASK = "focused_task.jsonl";
    public static final String GAPS = SessionDir.GAPS;
    public static final String QUESTION = "question.txt";
    public static final String QUESTION_ASKED = "question.asked";

    public static ObligationDir of(Path dir) throws IOException {
        return new ObligationDir(dir);
    }

    private static final String WAVES = "obligations-*";

    private final Path dir;
    private final String sessionId;
    private final List<JsonObject> results;
    private final List<JsonObject> focus;

    private ObligationDir(Path dir) throws IOException {
        this.dir = dir;
        this.results = RowCodec.readJsonl(dir.resolve(RESULT));
        this.sessionId = sessionOf(results);
        this.focus = sessionId.isEmpty() ? Collections.<JsonObject>emptyList()
                : RowCodec.readJsonl(dir.resolve(FOCUSED_TASK));
    }

    public static List<ObligationDir> workersIn(Path iteration)
            throws IOException {
        List<ObligationDir> workers = new ArrayList<ObligationDir>();
        for (ObligationDir worker : Parallel.map(workerDirs(iteration),
                ObligationDir::new, Parallel.directoriesAtOnce())) {
            if (!worker.sessionId.isEmpty()) workers.add(worker);
        }
        return workers;
    }

    public static List<Path> workerDirs(Path iteration) throws IOException {
        List<Path> dirs = new ArrayList<Path>();
        for (Path wave : SessionDir.directories(iteration, WAVES)) {
            dirs.addAll(SessionDir.directories(wave, "*"));
        }
        return dirs;
    }

    public static final class Answer {
        public final String obligationId;
        public final ObligationResult result;

        private Answer(String obligationId, ObligationResult result) {
            this.obligationId = obligationId;
            this.result = result;
        }
    }

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

    private static String sessionOf(List<JsonObject> results) {
        String session = "";
        for (JsonObject row : results) {
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

    public String sessionId() {
        return sessionId;
    }

    public List<ObligationResult> results() {
        List<ObligationResult> read = new ArrayList<ObligationResult>();
        for (JsonObject row : results) {
            read.add(RowCodec.readObligationResult(row));
        }
        return read;
    }

    public List<JsonObject> focus() {
        return focus;
    }

    public static Map<String, JsonObject> worlds(List<ObligationDir> workers) {
        Map<String, JsonObject> worlds = new LinkedHashMap<String, JsonObject>();
        for (ObligationDir worker : workers) {
            for (JsonObject row : worker.focus) {
                worlds.put(worker.sessionId, row);
            }
        }
        return worlds;
    }
}
