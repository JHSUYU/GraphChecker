package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * IMPORT's gate: the row contract, checked before any stage reads a row.
 *
 * <pre>
 *   --sessions &lt;dir&gt;         the epoch's sessions/ (or --iteration, its parent)
 *   --out &lt;file&gt;             campaign_gaps.jsonl, appended to
 *   --topology-epoch &lt;id&gt;    the epoch these sessions belong to
 * </pre>
 *
 * <p>Every violation {@link RowInvariants} states is appended as one GapRow,
 * in the campaign gap file's own spelling, and the summary this process
 * prints is what the stage acts on: a BLOCKING count above zero is a campaign
 * failure at IMPORT, naming the first subject, and the DIAGNOSTIC ones are
 * recorded while the campaign goes on.  The process itself exits 0 whatever
 * it found -- the gate reports, the stage decides -- and nonzero only when it
 * could not read the sessions at all.</p>
 *
 * <p>Why here and not in each reader: a row defect is not one stage's
 * problem.  17960 lost two campaigns to rows that EXPLORE and COMPOSE each
 * read as valid, and a gate at the one place every row passes through is the
 * only version of the fix that holds for the stages nobody has written yet.
 * Append-only, because a gap row that a later stage overwrites was never
 * evidence.</p>
 */
public final class ImportGateMain {
    private ImportGateMain() {
    }

    public static void main(String[] argv) throws Exception {
        Map<String, String> options = options(argv);
        Path sessions = path(options, "sessions");
        Path iteration = path(options, "iteration");
        if (iteration == null && sessions != null) {
            iteration = sessions.getParent();
        }
        if (iteration == null) {
            throw new IllegalArgumentException(
                    "Missing --sessions (or --iteration)");
        }
        Path out = path(options, "out");
        if (out == null) out = path(options, "gaps");
        if (out == null) {
            throw new IllegalArgumentException("Missing --out");
        }
        JsonObject summary = gate(iteration, out,
                value(options, "topology-epoch", ""));
        System.out.println(new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(summary));
    }

    /** Checks one epoch, appends its violations, and reports the counts. */
    public static JsonObject gate(Path iteration, Path out,
                                  String topologyEpoch) throws IOException {
        List<SessionReader> sessions = SessionReader.readAll(iteration);
        List<GapRow> gaps = new ArrayList<GapRow>(
                RowInvariants.check(sessions));
        gaps.addAll(flips(iteration, sessions));
        List<String> lines = new ArrayList<String>();
        int blocking = 0;
        String first = "";
        Map<String, Integer> byKind = new LinkedHashMap<String, Integer>();
        for (GapRow gap : gaps) {
            if (gap.blocking()) {
                blocking++;
                if (first.isEmpty()) first = gap.subject();
            }
            Integer count = byKind.get(gap.kind().name());
            byKind.put(gap.kind().name(), count == null ? 1 : count + 1);
            lines.add(RowCodec.toLine(campaignGap(gap, topologyEpoch)));
        }
        if (!lines.isEmpty()) {
            if (out.getParent() != null) {
                Files.createDirectories(out.getParent());
            }
            StringBuilder text = new StringBuilder();
            for (String line : lines) {
                text.append(line).append(System.lineSeparator());
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
        JsonArray named = new JsonArray();
        for (GapRow gap : gaps) {
            if (!gap.blocking()) continue;
            if (named.size() >= 8) break;
            named.add(gap.subject());
        }
        summary.add("blockingSubjects", named);
        return summary;
    }

    /**
     * Invariant 10, over every obligation worker this epoch has finished.
     *
     * <p>The link from a focus row to the session its replay published is the
     * worker's own result row: the focus row names the SEED session it was
     * cut from, and {@code obligation_result.jsonl} names the session the
     * replay wrote.  Nothing is inferred from a directory name.</p>
     */
    private static List<GapRow> flips(Path iteration,
                                      List<SessionReader> sessions)
            throws IOException {
        List<GapRow> gaps = new ArrayList<GapRow>();
        Map<String, SessionReader> byId =
                new LinkedHashMap<String, SessionReader>();
        for (SessionReader session : sessions) {
            byId.put(session.sessionId(), session);
        }
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            gaps.addAll(flip(worker, byId));
        }
        return gaps;
    }

    private static List<GapRow> flip(ObligationDir worker,
                                     Map<String, SessionReader> byId)
            throws IOException {
        List<GapRow> gaps = new ArrayList<GapRow>();
        SessionReader replay = byId.get(worker.sessionId());
        if (replay == null) return gaps;
        for (JsonObject row : RowCodec.readJsonl(worker.focusedTask())) {
            gaps.addAll(RowInvariants.flipped(row, replay));
        }
        return gaps;
    }

    /**
     * One gap row, in the one spelling a gap row has.
     *
     * <p>This file used to carry {@code gapKind}/{@code gapClass} while the
     * session files carried the contract's {@code kind}/{@code cls}, and the
     * reader of both read only the campaign spelling: every session row's
     * code defaulted to {@code ADMISSION_GAP} and its class to
     * {@code BLOCKING}, which is how the accepted HDFS-17960 run published
     * 262 blocking gaps that were all DIAGNOSTIC in their own rows.  One
     * spelling, {@link RowCodec#writeGap}'s, plus the epoch this file is
     * selected on.</p>
     */
    private static JsonObject campaignGap(GapRow gap, String topologyEpoch) {
        JsonObject row = RowCodec.writeGap(gap);
        row.addProperty("topologyEpoch", topologyEpoch);
        return row;
    }

    // ---- options ------------------------------------------------------

    private static Map<String, String> options(String[] argv) {
        Map<String, String> options = new LinkedHashMap<String, String>();
        for (int index = 0; index < argv.length; index++) {
            if (!argv[index].startsWith("--")) continue;
            String name = argv[index].substring(2);
            int equals = name.indexOf('=');
            if (equals >= 0) {
                options.put(name.substring(0, equals),
                        name.substring(equals + 1));
            } else if (index + 1 < argv.length
                    && !argv[index + 1].startsWith("--")) {
                options.put(name, argv[++index]);
            } else {
                options.put(name, "true");
            }
        }
        return options;
    }

    private static String value(Map<String, String> options, String name,
                                String fallback) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty() ? fallback : value;
    }

    private static Path path(Map<String, String> options, String name) {
        String value = options.get(name);
        return value == null || value.trim().isEmpty()
                ? null : Paths.get(value);
    }
}
