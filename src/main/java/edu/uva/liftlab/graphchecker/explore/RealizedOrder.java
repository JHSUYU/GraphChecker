package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.StableEventNames;
import edu.uva.liftlab.graphchecker.runtime.RecordingPlant;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class RealizedOrder {
    static final String SCOPE = "EVENT";

    private RealizedOrder() {
    }

    static List<JsonObject> rows(Path schedule,
                                 Set<OccurrenceAddress> mints,
                                 Set<OccurrenceAddress> cone)
            throws IOException {
        List<ScheduleEvent> events = SessionReader.readSchedule(schedule);
        Set<String> ids = new HashSet<String>();
        Set<String> minted = new HashSet<String>();
        for (OccurrenceAddress mint : mints) {
            ids.add(mint.id());
            minted.add(scope(mint));
        }
        Set<String> onCone = new HashSet<String>(minted);
        for (OccurrenceAddress occurrence : cone) {
            onCone.add(scope(occurrence));
        }
        long from = from(events, SessionReader.readScheduleMarks(schedule),
                ids);
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (ScheduleEvent[] edge : edges(events, from, minted, onCone)) {
            JsonObject row = new JsonObject();
            row.addProperty(RecordingPlant.KIND, RecordingPlant.ORDER);
            row.addProperty(RecordingPlant.SCOPE, SCOPE);
            row.add("before", event(edge[0]));
            row.add("after", event(edge[1]));
            rows.add(row);
        }
        return rows;
    }

    private static JsonObject event(ScheduleEvent event) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", event.kind().name());
        row.addProperty("context", event.context());
        row.addProperty("site", event.site());
        row.addProperty("k", event.k());
        return row;
    }

    static long from(List<ScheduleEvent> schedule, Map<String, Long> marks,
                     Set<String> mints) {
        long from = Long.MAX_VALUE;
        for (String mint : mints) {
            Long mark = marks.get(mint);
            if (mark != null) from = Math.min(from, mark);
        }
        for (ScheduleEvent event : schedule) {
            if (event.seq() >= from) break;
            if (mints.contains(event.occurrence())) return event.seq();
        }
        return from;
    }

    static List<ScheduleEvent[]> edges(List<ScheduleEvent> schedule,
                                       long from, Set<String> minted,
                                       Set<String> occurrences) {
        StableEventNames names = new StableEventNames();
        for (ScheduleEvent event : schedule) {
            if (event.kind() == ScheduleEvent.Kind.SEND) {
                names.sent(event.context(), event.site(), event.endpoint());
            }
        }
        Set<String> onCone = withProducers(schedule, occurrences);
        Set<String> running = new HashSet<String>();
        List<ScheduleEvent[]> edges = new ArrayList<ScheduleEvent[]>();
        Map<String, Integer> held = new HashMap<String, Integer>();
        int latest = -1;
        for (int at = 0; at < schedule.size(); at++) {
            ScheduleEvent event = schedule.get(at);
            if (event.seq() < from) {
                running.add(event.context());
                continue;
            }
            if (event.kind() == ScheduleEvent.Kind.WAKE && latest >= 0
                    && running.contains(event.context())) {
                ScheduleEvent before = schedule.get(latest);
                String step = scope(before.context());
                ScheduleEvent stableBefore = stable(before, names);
                ScheduleEvent stableAfter = stable(event, names);
                if (!before.context().equals(event.context())
                        && before.k() == 0
                        && onCone.contains(scope(event.context()))
                        && onCone.contains(step)
                        && (!turnCounted(step) || minted.contains(step))
                        && stableBefore != null && stableAfter != null
                        && latest > held.getOrDefault(event.context(), -1)) {
                    edges.add(new ScheduleEvent[] {stableBefore, stableAfter});
                    held.put(event.context(), latest);
                }
            }
            if (step(event)) latest = at;
        }
        return edges;
    }

    static Set<String> withProducers(List<ScheduleEvent> schedule,
                                     Set<String> scopes) {
        Map<String, String> senders = new HashMap<String, String>();
        for (ScheduleEvent event : schedule) {
            if (event.kind() == ScheduleEvent.Kind.SEND
                    && !event.endpoint().isEmpty()) {
                senders.putIfAbsent(event.endpoint(), scope(event.context()));
            }
        }
        Set<String> cone = new HashSet<String>(scopes);
        for (ScheduleEvent event : schedule) {
            String sender = senders.get(event.endpoint());
            if (event.kind() == ScheduleEvent.Kind.RECV && sender != null
                    && scopes.contains(scope(event.context()))) {
                cone.add(sender);
            }
        }
        return cone;
    }

    private static ScheduleEvent stable(ScheduleEvent event,
                                        StableEventNames names) {
        String context = names.context(event.context());
        return context == null ? null : ScheduleEvent.of(event.seq(),
                event.kind(), context, event.site(), event.k(),
                event.occurrence(), event.endpoint());
    }

    static String scope(String context) {
        int node = context.indexOf('|');
        int frames = node < 0 ? -1 : context.indexOf('|', node + 1);
        return frames < 0 ? context : context.substring(0, frames);
    }

    static String scope(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "|"
                + occurrence.context().render();
    }

    static boolean turnCounted(String context) {
        String scope = scope(context);
        String spelled = scope.substring(scope.indexOf('|') + 1);
        if (ContextShape.Stance.VIEW_STANCE.equals(spelled)) return false;
        CausalContext hop = CausalContext.parse(spelled);
        return hop instanceof CausalContext.Root
                && !((CausalContext.Root) hop).role().equals(Role.CLIENT);
    }

    private static boolean step(ScheduleEvent event) {
        return event.kind() != ScheduleEvent.Kind.WAKE
                && event.kind() != ScheduleEvent.Kind.END
                && event.kind() != ScheduleEvent.Kind.PUBLISH;
    }
}
