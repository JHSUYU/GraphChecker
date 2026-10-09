package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.runtime.RecordingPlant;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * THE ORDER THE CONFIRMED WORLD RAN IN, from its moved roots on (PIPELINE
 * §10b): what a native reproduction holds besides the model's own ORDER
 * rows, so that it runs the world CONFIRM saw and not merely its roots.  A
 * native run on the recording's timing plants the roots and still runs
 * another order (solr-bugs-restore-construction Z5: the old Overseer's first
 * RESTORE task waited, in the confirmed session, until the new Overseer had
 * run the second RESTORE, and the shutdown that followed interrupted it;
 * natively it finished first, 0/10).
 *
 * <p>The order is the confirmed session's schedule (ScheduleLog's total
 * order of the events that cross a thread or a node: SEND, RECV, a store's
 * WRITE, START, CLAIM, WAKE, END, each named by kind, context, site and k,
 * the one identity both passes compute) from the first event of a moved
 * root's mint occurrence on: every later event is after the root in the
 * world CONFIRM saw, and the root's effect reaches what the trace records
 * no edge of as well (restore's fault ends the Overseer, a new one is
 * elected and the old one's shutdown interrupts its task: no row states
 * either).  Before the roots the run is the recording's.  It is reduced:
 * each event, but a turn's END, after the latest earlier step -- an event
 * but a WAKE or an END, which are the clock (a poll's count is timing,
 * never a cause) -- when that step is in another context and the event's
 * own context does not already follow it.  By induction every step follows
 * every earlier one, so this is the transitive reduction of the realized
 * order: one edge per context switch.  Each edge is an {@code ORDER} row
 * of scope {@value #SCOPE}, {@code before} and {@code after} two events,
 * which the native run's ScheduleLog holds at admission.</p>
 */
final class RealizedOrder {
    /** An ORDER row's scope when its ends are schedule events. */
    static final String SCOPE = "EVENT";

    private RealizedOrder() {
    }

    /**
     * The ORDER rows of the confirmed session's realized order from the
     * first event of an occurrence in {@code mints} (by id) on, each pair
     * once; none when no such occurrence made an event.
     */
    static List<JsonObject> rows(SessionReader confirmed, Set<String> mints)
            throws IOException {
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (ScheduleEvent[] edge : edges(confirmed.schedule(), mints)) {
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

    /**
     * The reduced realized order of {@code schedule} from the first event of
     * an occurrence in {@code mints} on (class comment): {before, after}
     * pairs in schedule order.
     */
    static List<ScheduleEvent[]> edges(List<ScheduleEvent> schedule,
                                       Set<String> mints) {
        int from = 0;
        while (from < schedule.size()
                && !mints.contains(schedule.get(from).occurrence())) {
            from++;
        }
        List<ScheduleEvent[]> edges = new ArrayList<ScheduleEvent[]>();
        Map<String, Integer> known = new HashMap<String, Integer>();
        int latest = -1;
        for (int at = from; at < schedule.size(); at++) {
            ScheduleEvent event = schedule.get(at);
            if (event.kind() != ScheduleEvent.Kind.END && latest >= 0
                    && !schedule.get(latest).context().equals(
                    event.context())
                    && latest > known.getOrDefault(event.context(), -1)) {
                edges.add(new ScheduleEvent[] {schedule.get(latest), event});
                known.put(event.context(), latest);
            }
            if (step(event)) {
                latest = at;
                known.merge(event.context(), at, Math::max);
            }
        }
        return edges;
    }

    /** Whether an event is a step: not the clock (a WAKE, a turn's END). */
    private static boolean step(ScheduleEvent event) {
        return event.kind() != ScheduleEvent.Kind.WAKE
                && event.kind() != ScheduleEvent.Kind.END;
    }
}
