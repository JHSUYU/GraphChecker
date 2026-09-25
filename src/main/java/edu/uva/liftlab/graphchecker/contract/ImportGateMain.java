package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.option.LongOptions;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * IMPORT's gate: the row contract, checked before any stage reads a row.
 *
 * <pre>
 *   --sessions &lt;dir&gt;       the epoch's sessions/ (or --iteration, parent)
 *   --out &lt;file&gt;           campaign_gaps.jsonl, appended to
 *   --topology-epoch &lt;id&gt;  the epoch these sessions belong to
 * </pre>
 *
 * <p>Appends every {@link RowInvariants} violation and prints a summary; the
 * stage fails on BLOCKING &gt; 0.  Exits 0 whatever it found (the gate
 * reports, the stage decides), nonzero only if the sessions are unreadable.
 * Append-only: an overwritten gap row was never evidence.</p>
 */
public final class ImportGateMain {
    private ImportGateMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path sessions = options.path("sessions");
        Path iteration = options.path("iteration");
        if (iteration == null && sessions != null) {
            iteration = sessions.getParent();
        }
        if (iteration == null) {
            throw new IllegalArgumentException(
                    "Missing --sessions (or --iteration)");
        }
        Path out = options.path("out");
        if (out == null) out = options.path("gaps");
        if (out == null) {
            throw new IllegalArgumentException("Missing --out");
        }
        JsonObject summary = gate(iteration, out,
                options.value("topology-epoch", ""));
        System.out.println(new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(summary));
    }

    /** Checks one epoch, appends its violations, and reports the counts. */
    public static JsonObject gate(Path iteration, Path out,
                                  String topologyEpoch) throws IOException {
        List<SessionReader> sessions = SessionReader.readAll(iteration);
        Map<String, SessionReader> byId =
                new LinkedHashMap<String, SessionReader>();
        for (SessionReader session : sessions) {
            byId.put(session.sessionId(), session);
        }
        // Each worker's focus rows, read once: the first is the ask its
        // session ran under (invariant 6), each one a flip it owes (10).
        Map<String, JsonObject> asks = new LinkedHashMap<String, JsonObject>();
        List<GapRow> flips = new ArrayList<GapRow>();
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            List<JsonObject> rows = RowCodec.readJsonl(worker.focusedTask());
            if (!rows.isEmpty()) {
                asks.putIfAbsent(worker.sessionId(), rows.get(0));
            }
            // Joined by the worker's own result row, never a directory name.
            SessionReader replay = byId.get(worker.sessionId());
            if (replay == null) continue;
            for (JsonObject row : rows) {
                flips.addAll(RowInvariants.flipped(row, replay));
            }
        }
        List<GapRow> gaps = new ArrayList<GapRow>(
                RowInvariants.check(sessions, asks));
        gaps.addAll(flips);

        StringBuilder text = new StringBuilder();
        int blocking = 0;
        String first = "";
        JsonArray named = new JsonArray();
        Map<String, Integer> byKind = new LinkedHashMap<String, Integer>();
        for (GapRow gap : gaps) {
            if (gap.blocking()) {
                blocking++;
                if (first.isEmpty()) first = gap.subject();
                if (named.size() < 8) named.add(gap.subject());
            }
            byKind.merge(gap.kind().name(), 1, Integer::sum);
            JsonObject row = RowCodec.writeGap(gap);
            row.addProperty("topologyEpoch", topologyEpoch);
            text.append(RowCodec.toLine(row)).append(System.lineSeparator());
        }
        if (text.length() > 0) {
            if (out.getParent() != null) {
                Files.createDirectories(out.getParent());
            }
            Files.write(out, text.toString().getBytes(StandardCharsets.UTF_8),
                    StandardOpenOption.CREATE, StandardOpenOption.APPEND);
        }
        JsonObject summary = new JsonObject();
        summary.addProperty("topologyEpoch", topologyEpoch);
        summary.addProperty("sessions", sessions.size());
        summary.addProperty("violations", gaps.size());
        summary.addProperty("blocking", blocking);
        summary.addProperty("diagnostic", gaps.size() - blocking);
        summary.addProperty("firstBlockingSubject", first);
        JsonObject kinds = new JsonObject();
        for (Map.Entry<String, Integer> entry : byKind.entrySet()) {
            kinds.addProperty(entry.getKey(), entry.getValue());
        }
        summary.add("gaps", kinds);
        summary.add("blockingSubjects", named);
        return summary;
    }
}
