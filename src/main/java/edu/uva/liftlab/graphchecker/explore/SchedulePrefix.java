package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 * The schedule half of a task's world: the prefix of the discovering
 * session's schedule a focused replay is held to.
 *
 * <p>A task's world is (planted values, schedule prefix).  The planted values
 * are the model and what the path's session was itself handed; the prefix is
 * that session's schedule, CUT where the replay stops being that session: at
 * the first event of any occurrence the obligation changes -- the focused
 * occurrence and its factor, where the flip is, and the mints where a value
 * is planted.  Everything before the cut is the discovering run, in its
 * order; from the cut the replay runs free.</p>
 *
 * <p>The cut is the earliest of each such occurrence's opening mark (where it
 * began, whether or not it made any event) and its first event.  A session
 * whose schedule names none of them -- an occurrence that never ran there --
 * hands its whole schedule: the replay is then held to the run it was cut
 * from until its own events leave it, which the turnstile states.</p>
 */
final class SchedulePrefix {
    /** The file the replay reads, beside its focus row. */
    static final String FILE = "schedule_prefix.jsonl";

    private SchedulePrefix() {
    }

    /** What was cut, for the focus row to state. */
    static final class Cut {
        final String sessionId;
        final int kept;
        final int of;
        final boolean found;

        private Cut(String sessionId, int kept, int of, boolean found) {
            this.sessionId = sessionId;
            this.kept = kept;
            this.of = of;
            this.found = found;
        }

        JsonObject toJson() {
            JsonObject json = new JsonObject();
            json.addProperty("sessionId", sessionId);
            json.addProperty("events", kept);
            json.addProperty("of", of);
            json.addProperty("cutAtFocus", found);
            return json;
        }
    }

    /**
     * Writes the prefix of {@code sessionId}'s schedule, cut before the first
     * event of any of {@code occurrenceIds}, to {@code out/FILE}.
     *
     * @return what was written, or null when the session states no schedule
     */
    static Cut write(Path iteration, String sessionId,
                     Collection<String> occurrenceIds, Path out)
            throws IOException {
        if (iteration == null || sessionId == null || sessionId.isEmpty()) {
            return null;
        }
        SessionDir session = SessionDir.of(iteration, sessionId);
        List<ScheduleEvent> events = SessionReader.readSchedule(session);
        if (events.isEmpty()) return null;
        Map<String, Long> marks =
                SessionReader.readScheduleMarks(session.schedule());
        int cut = events.size();
        boolean found = false;
        for (String id : occurrenceIds) {
            if (id == null || id.isEmpty()) continue;
            Long opened = marks.get(id);
            if (opened != null && opened < cut) {
                cut = (int) Math.max(0L, opened);
                found = true;
            }
            for (int index = 0; index < cut; index++) {
                if (id.equals(events.get(index).occurrence())) {
                    cut = index;
                    found = true;
                    break;
                }
            }
        }
        List<JsonObject> rows = new ArrayList<JsonObject>(cut);
        for (int index = 0; index < cut; index++) {
            rows.add(RowCodec.writeScheduleEvent(events.get(index)));
        }
        RowCodec.writeJsonl(out.resolve(FILE), rows);
        return new Cut(sessionId, cut, events.size(), found);
    }
}
