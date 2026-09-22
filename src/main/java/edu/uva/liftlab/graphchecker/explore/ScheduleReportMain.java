package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;

/**
 * The schedule divergence report of one iteration.
 *
 * <pre>
 *   --iteration &lt;dir&gt;     the iteration whose sessions and workers to read
 *   --recording &lt;file&gt;    the recording's schedule, the seed's prefix
 * </pre>
 *
 * <p>For every replay: the prefix it inherited, how much of it its own
 * schedule reproduced in order, and the first pair of events where it did
 * not.  The seed replay's prefix is the recording's schedule; a focused
 * replay's is beside its focus row.  Read-only, and it prints one JSON object
 * per replay plus a summary: a measurement, never a gate.</p>
 */
public final class ScheduleReportMain {
    private ScheduleReportMain() {
    }

    public static void main(String[] argv) throws IOException {
        Map<String, String> options = ExploreMain.options(argv);
        Path iteration = ExploreMain.path(options, "iteration");
        if (iteration == null) {
            throw new IllegalArgumentException("--iteration is required");
        }
        Path recording = ExploreMain.path(options, "recording");
        int replays = 0;
        int held = 0;
        for (SessionDir session : SessionDir.sessionsIn(iteration)) {
            SessionManifest manifest;
            try {
                manifest = RowCodec.readManifest(session.manifest());
            } catch (RuntimeException unstated) {
                continue;
            }
            if (manifest.role() != SessionManifest.Role.SEED
                    || recording == null) {
                continue;
            }
            JsonObject row = compare("SEED", session,
                    SessionReader.readSchedule(recording), recording);
            System.out.println(RowCodec.toLine(row));
            replays++;
            if (row.get("held").getAsBoolean()) held++;
        }
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            Path prefix = worker.dir().resolve(SchedulePrefix.FILE);
            if (!Files.isRegularFile(prefix)) continue;
            JsonObject row = compare(worker.dir().getFileName().toString(),
                    SessionDir.of(iteration, worker.sessionId()),
                    SessionReader.readSchedule(prefix), prefix);
            System.out.println(RowCodec.toLine(row));
            replays++;
            if (row.get("held").getAsBoolean()) held++;
        }
        JsonObject summary = new JsonObject();
        summary.addProperty("kind", "SCHEDULE_SUMMARY");
        summary.addProperty("replays", replays);
        summary.addProperty("heldWholePrefix", held);
        System.out.println(RowCodec.toLine(summary));
    }

    private static JsonObject compare(String replay, SessionDir session,
                                      List<ScheduleEvent> prefix,
                                      Path prefixFile) throws IOException {
        List<ScheduleEvent> ran = SessionReader.readSchedule(session);
        int matched = 0;
        while (matched < prefix.size() && matched < ran.size()
                && prefix.get(matched).key().equals(ran.get(matched).key())) {
            matched++;
        }
        JsonObject row = new JsonObject();
        row.addProperty("kind", "SCHEDULE_DIVERGENCE");
        row.addProperty("replay", replay);
        row.addProperty("sessionId", session.sessionId());
        row.addProperty("prefix", prefixFile.toString());
        row.addProperty("prefixEvents", prefix.size());
        row.addProperty("ranEvents", ran.size());
        row.addProperty("matchedInOrder", matched);
        row.addProperty("held", matched == prefix.size());
        if (matched < prefix.size()) {
            row.addProperty("expected", prefix.get(matched).render());
            row.addProperty("ran", matched < ran.size()
                    ? ran.get(matched).render() : "(end of run)");
        }
        JsonArray diverged = new JsonArray();
        for (GapRow gap : RowCodec.readAll(session.gaps(),
                RowCodec::readGap)) {
            if (gap.kind() == GapKind.SCHEDULE_DIVERGED) {
                diverged.add(gap.detail());
            }
        }
        row.add("turnstile", diverged);
        return row;
    }

    /** For a caller that wants the rows without a process. */
    static Path path(String value) {
        return value == null || value.isEmpty() ? null : Paths.get(value);
    }
}
