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
import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * The schedule half of a task's world, cut at the target (first event or
 * opening mark of the focused occurrence, its factor, or the flip's
 * occurrence), or earlier at the first occurrence an ORDER of the world's
 * pairings moves after another's ({@code ConfirmMain#holding}): the order the
 * prefix follows is the one the pairings change. Before the cut the replay follows the discovering run's order;
 * past it the flip runs free, but each timeout WAKE in {@link #REST_FILE} still
 * waits for the events it followed ({@code runtime.ScheduleLog}) -- on a slower
 * replay's wall clock every daemon would be due at once. No cut found: whole
 * schedule. A source run cut at its witness hands its mark on with the rest
 * ({@code ScheduleEvent#WITNESS}): its order ends there; so does a run of one
 * invocation of a parameterized test its invocation's ({@code
 * ScheduleEvent#INVOCATION}), and every run its startup marks ({@code
 * ScheduleEvent#STARTUP}).
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
        /** The source run was cut at its witness. */
        final boolean atWitness;

        private Cut(String sessionId, int kept, int of, boolean found,
                    boolean atWitness) {
            this.sessionId = sessionId;
            this.kept = kept;
            this.of = of;
            this.found = found;
            this.atWitness = atWitness;
        }

        JsonObject toJson() {
            JsonObject json = new JsonObject();
            json.addProperty("sessionId", sessionId);
            json.addProperty("events", kept);
            json.addProperty("rest", of - kept);
            json.addProperty("of", of);
            json.addProperty("cutAtFocus", found);
            json.addProperty("endsAtWitness", atWitness);
            return json;
        }
    }

    /**
     * Writes the prefix before the first event/mark of any {@code
     * occurrenceIds} to {@code out/FILE} and the rest to {@code out/REST_FILE};
     * with {@code held} false nothing is held: every event is rest, so only
     * the WAKEs still wait for what they followed (a CONFIRM run's order is
     * the model's, {@code runtime.Confirmation}).
     *
     * @return what was written, or null when the session states no schedule
     */
    static Cut write(Path iteration, String sessionId,
                     Collection<String> occurrenceIds, boolean held, Path out)
            throws IOException {
        if (iteration == null || sessionId == null || sessionId.isEmpty()) {
            return null;
        }
        SessionDir session = SessionDir.of(iteration, sessionId);
        List<ScheduleEvent> events = SessionReader.readSchedule(session);
        if (events.isEmpty()) return null;
        Map<String, Long> marks =
                SessionReader.readScheduleMarks(session.schedule());
        int cut = held ? events.size() : 0;
        boolean found = false;
        for (String id : held ? occurrenceIds
                : Collections.<String>emptyList()) {
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
        // A run cut at its witness orders nothing after it: the order ends
        // there, and the replay reads that off its rest.
        Long witness = marks.get(ScheduleEvent.WITNESS);
        if (witness != null) {
            rest.add(RowCodec.writeScheduleMark(ScheduleEvent.WITNESS,
                    witness));
        }
        // Which invocation of a parameterized test the run was, for the
        // replay to check it runs the same one.
        JsonObject invocation =
                SessionReader.readScheduleInvocation(session.schedule());
        if (invocation != null) rest.add(invocation);
        // The order its nodes passed their startup steps, for the replay to
        // hold them to it (runtime.StartupOrder).
        rest.addAll(SessionReader.readScheduleStartup(session.schedule()));
        RowCodec.writeJsonl(out.resolve(FILE), rows);
        RowCodec.writeJsonl(out.resolve(REST_FILE), rest);
        return new Cut(sessionId, cut, events.size(), found,
                witness != null);
    }
}
