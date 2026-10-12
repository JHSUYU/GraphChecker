package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
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

/**
 * THE ORDER THE CONFIRMED WORLD RAN IN, from its moved roots on (PIPELINE
 * §10b): what a native reproduction holds besides the model's own ORDER
 * rows, so that it runs the world CONFIRM saw and not merely its roots.  A
 * native run plants the roots and still runs the world at native speed
 * (solr-bugs-restore-construction Z5: a fault ends the Overseer, a new one
 * runs the second RESTORE, and the client's next update routes on the
 * restored collection while the old Overseer's first RESTORE task still
 * waits for its replicas -- in the confirmed session that task's wait woke
 * only after the second RESTORE had answered; natively it finished first,
 * and the update found the collection active, 0/10).
 *
 * <p>The order is the confirmed session's schedule (ScheduleLog's total
 * order of the events that cross a thread or a node: SEND, RECV, a store's
 * WRITE, START, CLAIM, WAKE, END, each named by kind, context, site and k,
 * the one identity both passes compute) from where a moved root's mint
 * occurrence opened on (its schedule mark, or its first event: a clock
 * read's occurrence makes no event of its own, solr-18406).  Its steps are
 * its events but a WAKE or an END, which are the clock: a poll's count is
 * timing, never a cause.</p>
 *
 * <p>Of it, a native run holds what keeps the world the roots found
 * running from getting ahead of the confirmed one, between events a native
 * run makes alike: each WAKE after the step just before it, once per step
 * and context, where the WAKE and the step are as below.  (The whole order,
 * one edge per context switch, reproduced 0/10 on restore, solr-18406 and
 * solr-18413, each run's first unheld row an event it never made.)
 * <ul>
 *   <li>the WAKE in a context running at the start (an event before it): the
 *   roots' effect races the contexts it found running, and the trace states
 *   no edge of how it reaches them (restore: an Overseer's death, a new
 *   one's election).  A context begun after the start is that effect or the
 *   workload's next step and runs as the run makes it; its turns decide on
 *   reads no event names (restore: a new Overseer's state-updater turn
 *   found its queue empty natively and wrote nothing, so the order waiting
 *   for that write never held);</li>
 *   <li>a WAKE, the step in another context: a running context goes on by
 *   itself only where a wait ends, on the wall clock or a signal, and
 *   natively the wait ends before the world it waited on has got where the
 *   confirmed one had; between waits it moves by its program and what it
 *   receives;</li>
 *   <li>the step the first of its kind and site in its context (k 0): a
 *   later count is a loop's (a poll's, a retry's, one send per item), which
 *   natively runs another number of times, so its k-th event is no fixed
 *   point of the world (solr-18413: a request handler's sixth and
 *   fourteenth SEND, which some native runs never made);</li>
 *   <li>both events in contexts of the claim's cone: the contexts of the
 *   occurrences its moved roots are minted in, of the anchor, and of those
 *   CONFIRM's WIRE, STATE and ORDER rows name, and of the senders of the
 *   messages these received ({@link #withProducers}).  A WAKE elsewhere
 *   is timing the claim rests on nowhere (solr-18413 Y8: the client's
 *   {@code RequestStatus.waitFor} polls and the other nodes' Overseer
 *   turns, held behind steps some native runs never made);</li>
 *   <li>the step in no turn-counted root ({@link #turnCounted}) but a
 *   mint's: a daemon tick's or a timed wait's k counts turns a native run
 *   numbers on its own timing (Y8: a queue write of
 *   {@code Root:OVERSEER_STATE_UPDATE#15} no native run made at that
 *   tick).</li>
 * </ul>
 * Both events of an edge are named by their stable contexts ({@link
 * StableEventNames}: without the frames' counts, each message hop its
 * sender's first send of its site), the names the native run computes
 * alike; an edge whose events have none is not held, for the same reason
 * as a later count (solr-18413 IB1: a SPLIT request sent after a
 * REQUESTSTATUS poll had another endpoint id natively, so a WAKE held behind
 * the node work it started waited for an event no native run named, 0/10).
 * Each edge held is an {@code ORDER} row of scope {@value #SCOPE}, {@code
 * before} and {@code after} two events, which the native run's ScheduleLog
 * holds at admission.</p>
 */
final class RealizedOrder {
    /** An ORDER row's scope when its ends are schedule events. */
    static final String SCOPE = "EVENT";

    private RealizedOrder() {
    }

    /**
     * The ORDER rows of the confirmed session's realized order, read off its
     * {@code schedule} file, from where an occurrence of {@code mints}
     * opened on, each pair once, both its events in contexts of the claim's
     * cone ({@code cone}, the mints among it); none when no mint opened.
     */
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

    /**
     * The schedule position (an event's seq) where the first occurrence of
     * {@code mints} opened: the earliest of their marks ({@code
     * ScheduleLog#mark}: the seq of the event after the opening) and of
     * their own events; past every event when none opened.
     */
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

    /**
     * The edges of {@code schedule}'s realized order from position {@code
     * from} on that a native run holds (class comment): {before, after}
     * pairs in schedule order, one per WAKE held, each event under its stable
     * context; {@code minted} and {@code occurrences} are the {@link
     * #scope}s of the mints' and the cone's occurrences.
     */
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

    /**
     * {@code scopes} and, one hop, the scope of each SEND a context in them
     * received (paired by endpoint): the work whose message a cone
     * occurrence took in is the claim's too (solr-bugs-restore-construction:
     * the first RESTORE task's state-update message is what the mint's
     * state-updater turn applied, and that task's wait is what the confirmed
     * order held, natively 0/10 without it).
     */
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

    /** {@code event} under its stable context; null when it has none. */
    private static ScheduleEvent stable(ScheduleEvent event,
                                        StableEventNames names) {
        String context = names.context(event.context());
        return context == null ? null : ScheduleEvent.of(event.seq(),
                event.kind(), context, event.site(), event.k(),
                event.occurrence(), event.endpoint());
    }

    /** An event context's node and causal context, its handoffs left out
     *  ({@code runtime.ScheduleLog#contextOf}): the root or the message its
     *  work descends from. */
    static String scope(String context) {
        int node = context.indexOf('|');
        int frames = node < 0 ? -1 : context.indexOf('|', node + 1);
        return frames < 0 ? context : context.substring(0, frames);
    }

    /** An occurrence's node and causal context, as its events' contexts
     *  begin. */
    static String scope(OccurrenceAddress occurrence) {
        return occurrence.node().render() + "|"
                + occurrence.context().render();
    }

    /**
     * Whether a context stands in a turn-counted root: a daemon tick or a
     * timed-wait loop's turn ({@code Root:<role>#k}, any role but the
     * workload's CLIENT), whose k counts turns a native run, on its own
     * timing, numbers otherwise (a state updater's batches, a poll's wakes).
     */
    static boolean turnCounted(String context) {
        String scope = scope(context);
        CausalContext hop = CausalContext.parse(
                scope.substring(scope.indexOf('|') + 1));
        return hop instanceof CausalContext.Root
                && !((CausalContext.Root) hop).role().equals(Role.CLIENT);
    }

    /** Whether an event is a step: not the clock (a WAKE, a turn's END). */
    private static boolean step(ScheduleEvent event) {
        return event.kind() != ScheduleEvent.Kind.WAKE
                && event.kind() != ScheduleEvent.Kind.END;
    }
}
