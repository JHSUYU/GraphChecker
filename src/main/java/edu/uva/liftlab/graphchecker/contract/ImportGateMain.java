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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * IMPORT's gate: the row contract, checked once per session before any stage
 * reads its rows.
 *
 * <pre>
 *   --sessions &lt;dir&gt;       the epoch's sessions/ (its parent holds the
 *                          obligation waves, whose focus rows say what each
 *                          focused session ran under)
 *   --gate &lt;name&gt;          a session of it to gate, repeatable; none: every
 *                          session of it not gated yet
 *   --gated &lt;file&gt;         the sessions gated before, one id per line, read
 *                          and appended with the ones gated now; none: no
 *                          session was, and none is recorded
 *   --out &lt;file&gt;           campaign_gaps.jsonl, appended to
 *   --topology-epoch &lt;id&gt;  the epoch these sessions belong to
 * </pre>
 *
 * <p>A session is judged once: one the ledger names is not judged again, and
 * the rules over the set are judged against the gated sessions still in the
 * epoch ({@link RowInvariants#check}).  Appends every violation and prints a
 * summary of this gate's own sessions; the stage fails on BLOCKING &gt; 0.
 * Exits 0 whatever it found (the gate reports, the stage decides), nonzero
 * only if the sessions are unreadable or a named one is not in the epoch.
 * Append-only: an overwritten gap row was never evidence.</p>
 */
public final class ImportGateMain {
    private ImportGateMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path sessions = options.path("sessions");
        Path iteration = sessions == null ? null : sessions.getParent();
        if (iteration == null) {
            throw new IllegalArgumentException("Missing --sessions");
        }
        Path out = options.path("out");
        if (out == null) {
            throw new IllegalArgumentException("Missing --out");
        }
        JsonObject summary = gate(iteration, options.all("gate"),
                options.path("gated"), out,
                options.value("topology-epoch", ""));
        System.out.println(new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(summary));
    }

    /**
     * Gates the sessions {@code names} of one epoch (every one not gated yet
     * when none is named), appends their violations, records them in the
     * ledger, and reports the counts.
     */
    public static JsonObject gate(Path iteration, List<String> names,
                                  Path ledger, Path out,
                                  String topologyEpoch) throws IOException {
        Set<String> before = new LinkedHashSet<String>();
        if (ledger != null && Files.exists(ledger)) {
            for (String line : Files.readAllLines(ledger,
                    StandardCharsets.UTF_8)) {
                if (!line.trim().isEmpty()) before.add(line.trim());
            }
        }
        List<SessionDir> roster = SessionDir.sessionsIn(iteration);
        Set<String> asked = new LinkedHashSet<String>(names);
        List<SessionDir> admitted = new ArrayList<SessionDir>();
        List<SessionDir> gated = new ArrayList<SessionDir>();
        for (SessionDir dir : roster) {
            boolean named = asked.remove(dir.sessionId());
            if (before.contains(dir.sessionId())) {
                admitted.add(dir);
            } else if (named || names.isEmpty()) {
                gated.add(dir);
            }
        }
        if (!asked.isEmpty()) {
            throw new IllegalArgumentException("--gate names no session of "
                    + iteration.resolve(SessionDir.SESSIONS) + ": " + asked);
        }
        Set<String> gatedIds = new LinkedHashSet<String>();
        for (SessionDir dir : gated) gatedIds.add(dir.sessionId());
        // Each gated session's focus rows, by the session its worker's own
        // result row names (never a directory name): the first is the ask
        // its session ran under (invariant 6), each one a flip it owes (10).
        Map<String, List<JsonObject>> focus =
                new LinkedHashMap<String, List<JsonObject>>();
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            if (!gatedIds.contains(worker.sessionId())) continue;
            focus.computeIfAbsent(worker.sessionId(),
                    key -> new ArrayList<JsonObject>())
                    .addAll(RowCodec.readJsonl(worker.focusedTask()));
        }
        List<GapRow> gaps = RowInvariants.check(admitted, gated, focus);

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
        append(out, text);
        if (ledger != null) {
            StringBuilder ids = new StringBuilder();
            for (String id : gatedIds) {
                ids.append(id).append(System.lineSeparator());
            }
            append(ledger, ids);
        }
        JsonObject summary = new JsonObject();
        summary.addProperty("topologyEpoch", topologyEpoch);
        summary.addProperty("sessions", gated.size());
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

    /** Appends {@code text} to {@code file}; nothing, not even the file,
     *  when there is none. */
    private static void append(Path file, CharSequence text)
            throws IOException {
        if (text.length() == 0) return;
        if (file.getParent() != null) {
            Files.createDirectories(file.getParent());
        }
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.APPEND);
    }
}
