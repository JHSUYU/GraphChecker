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

final class SchedulePrefix {
    static final String FILE =
            edu.uva.liftlab.graphchecker.runtime.ScheduleLog.PREFIX_FILE;
    static final String REST_FILE =
            edu.uva.liftlab.graphchecker.runtime.ScheduleLog.SUFFIX_FILE;

    private SchedulePrefix() {
    }

    static final class Cut {
        final String sessionId;
        final int kept;
        final int of;
        final boolean found;
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

    static Cut write(Path iteration, String sessionId,
                     Collection<String> occurrenceIds, boolean held, Path out)
            throws IOException {
        return write(iteration, sessionId, occurrenceIds, Long.MAX_VALUE,
                held, out);
    }

    static Cut write(Path iteration, String sessionId,
                     Collection<String> occurrenceIds, long beforeEvent,
                     boolean held, Path out) throws IOException {
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
        for (int index = 0; held && index < cut; index++) {
            long made = events.get(index).vmEvent();
            if (made > 0L && made >= beforeEvent) {
                cut = index;
                found = true;
                break;
            }
        }
        List<JsonObject> rows = new ArrayList<JsonObject>(cut);
        List<JsonObject> rest = new ArrayList<JsonObject>(events.size() - cut);
        for (int index = 0; index < events.size(); index++) {
            (index < cut ? rows : rest).add(
                    RowCodec.writeScheduleEvent(events.get(index)));
        }
        Long witness = marks.get(ScheduleEvent.WITNESS);
        if (witness != null) {
            rest.add(RowCodec.writeScheduleMark(ScheduleEvent.WITNESS,
                    witness));
        }
        JsonObject invocation =
                SessionReader.readScheduleInvocation(session.schedule());
        if (invocation != null) rest.add(invocation);
        rest.addAll(SessionReader.readScheduleStartup(session.schedule()));
        RowCodec.writeJsonl(out.resolve(FILE), rows);
        RowCodec.writeJsonl(out.resolve(REST_FILE), rest);
        return new Cut(sessionId, cut, events.size(), found,
                witness != null);
    }
}
