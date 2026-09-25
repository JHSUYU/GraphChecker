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
 * The schedule half of a task's world: the discovering session's schedule,
 * which a focused replay is held to -- strictly up to the cut, and in its
 * timeouts past it.
 *
 * <p>A task's world is (planted values, schedule).  The planted values are
 * the model and what the path's session was itself handed; the schedule is
 * that session's, CUT at the TARGET: the first event of the focused
 * occurrence, its factor, or the occurrence where the flip is.  Everything
 * before the cut is the discovering run, in its order, with the planted
 * values in it -- a value planted before the target changes what the run
 * computes, and its order only where the value takes another branch, which
 * the turnstile states and lets go.  From the cut on, the flip's effects
 * run free, but the clock does not: the rest of the schedule is handed too
 * ({@link #REST_FILE}), and a timeout WAKE it names takes its turn only
 * after the events it followed there ({@code runtime.ScheduleLog}).  Past
 * the cut on the wall clock, every daemon of a replay many times slower
 * than its recording was due at once.</p>
 *
 * <p>The cut is the earliest of each such occurrence's opening mark (where it
 * began, whether or not it made any event) and its first event.  A session
 * whose schedule names none of them -- an occurrence that never ran there --
 * hands its whole schedule as the prefix: the replay is then held to the run
 * it was cut from until its own events leave it, which the turnstile
 * states.</p>
 */
final class SchedulePrefix {
    /** The file the replay reads, beside its focus row. */
    static final String FILE = "schedule_prefix.jsonl";
    /** The rest of the schedule past the cut, beside it. */
    static final String REST_FILE = "schedule_suffix.jsonl";

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
            json.addProperty("rest", of - kept);
            json.addProperty("of", of);
            json.addProperty("cutAtFocus", found);
            return json;
        }
    }

    /**
     * Writes {@code sessionId}'s schedule, cut before the first event of any
     * of {@code occurrenceIds}: the prefix to {@code out/FILE}, the rest to
     * {@code out/REST_FILE}.
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
        List<JsonObject> rest = new ArrayList<JsonObject>(events.size() - cut);
        for (int index = 0; index < events.size(); index++) {
            (index < cut ? rows : rest).add(
                    RowCodec.writeScheduleEvent(events.get(index)));
        }
        RowCodec.writeJsonl(out.resolve(FILE), rows);
        RowCodec.writeJsonl(out.resolve(REST_FILE), rest);
        return new Cut(sessionId, cut, events.size(), found);
    }
}
