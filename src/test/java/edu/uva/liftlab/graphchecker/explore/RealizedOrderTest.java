package edu.uva.liftlab.graphchecker.explore;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.Test;

/**
 * The realized order a native reproduction holds (PIPELINE §10b): from
 * where a moved root's mint occurrence opened on, each WAKE of a context
 * running before it after the step just before it, when that step is
 * another context's first of its kind and site, both on the claim's cone.
 */
public class RealizedOrderTest {
    private final List<ScheduleEvent> schedule = new ArrayList<ScheduleEvent>();
    private final Map<String, Long> marks = new HashMap<String, Long>();

    private void event(Kind kind, String context, String site, int k,
                       String occurrence) {
        sent(kind, context, site, k, occurrence, "");
    }

    private void sent(Kind kind, String context, String site, int k,
                      String occurrence, String endpoint) {
        schedule.add(ScheduleEvent.of(schedule.size(), kind, context, site,
                k, occurrence, endpoint));
    }

    /** The edges with every context of the schedule on the cone. */
    private List<String> edges(String... mints) {
        Set<String> minted = new HashSet<String>();
        Set<String> onCone = new HashSet<String>();
        for (ScheduleEvent event : schedule) {
            String scope = RealizedOrder.scope(event.context());
            onCone.add(scope);
            if (set(mints).contains(event.occurrence())) minted.add(scope);
        }
        return edges(set(mints), minted, onCone);
    }

    private List<String> edges(Set<String> mints, Set<String> minted,
                               Set<String> onCone) {
        List<String> edges = new ArrayList<String>();
        for (ScheduleEvent[] edge : RealizedOrder.edges(schedule,
                RealizedOrder.from(schedule, marks, mints), minted, onCone)) {
            edges.add(edge[0].site() + "<" + edge[1].site());
        }
        return edges;
    }

    private static Set<String> set(String... ids) {
        return new HashSet<String>(Arrays.asList(ids));
    }
    private static final String A = "n|Root:CLIENT/a#1";

    /**
     * Only on the claim's cone: the WAKE and the step each in the context
     * of an occurrence on it, and the step in no turn-counted root but a
     * mint's (solr-18413 Y8: an Overseer state-updater tick's queue write).
     * A turn-counted WAKE side is held: its waits are what the order holds.
     */
    @Test
    public void onlyTheConesContextsHoldAndATickStepOnlyAMints() {
        String task = "n|Root:OVERSEER_TASK#3";
        String waiter = "c|Root:CLIENT/wait#1";
        String poll = "c|Root:CLIENT/poll#2";
        String tick = "n|Root:OVERSEER_STATE_UPDATE#15";
        String update = "c|Root:CLIENT/.update#4";
        event(Kind.WAKE, task + "|run@0", "w0", 0, "task"); // running before
        event(Kind.WAKE, waiter, "q0", 0, "wait");          // running before
        event(Kind.WRITE, A, "mint", 0, "root");
        event(Kind.WAKE, task + "|run@0", "w1", 0, "task");
        event(Kind.RECV, poll, "p1", 0, "poll");
        event(Kind.WAKE, task + "|run@0", "w2", 0, "task");
        event(Kind.SEND, tick, "s1", 0, "osu");
        event(Kind.WAKE, task + "|run@0", "w3", 0, "task");
        event(Kind.RECV, update + "|f@0", "r1", 0, "update");
        event(Kind.WAKE, waiter, "q1", 0, "wait");
        Object[][] rows = {   // minted, on the cone, the edges
            {set(A), set(A, task), list("mint<w1")},
            {set(A), set(A, task, poll), list("mint<w1", "p1<w2")},
            {set(A), set(A, task, tick), list("mint<w1")},
            {set(A, tick), set(A, task, tick), list("mint<w1", "s1<w3")},
            {set(A), set(A, task, update), list("mint<w1")},
            {set(A), set(A, task, update, waiter), list("mint<w1", "r1<q1")},
            {set(A), set(task), list()},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            Set<String> minted = (Set<String>) row[0];
            @SuppressWarnings("unchecked")
            Set<String> onCone = (Set<String>) row[1];
            assertEquals(minted + " " + onCone, row[2],
                    edges(set("root"), minted, onCone));
        }
    }

    private static List<String> list(String... sites) {
        return Arrays.asList(sites);
    }
}
