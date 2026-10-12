package edu.uva.liftlab.graphchecker.explore;

import static org.junit.Assert.assertEquals;

import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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

    private static final String OLD = "n|Root:CLIENT/old#1";
    private static final String A = "n|Root:CLIENT/a#1";
    private static final String B = "n|Root:CLIENT/b#1";
    private static final String C = "n|Root:CLIENT/c#1";
    private static final String NEW = "n|Root:CLIENT/new#1";

    @Test
    public void aRunningContextsWakeWaitsForTheFirstStepBeforeIt() {
        event(Kind.WAKE, OLD, "old-started", 0, "o0"); // old runs before
        event(Kind.SEND, B, "b-early", 0, "o9");
        event(Kind.WRITE, A, "mint", 0, "root");       // the root's mint
        event(Kind.WAKE, OLD, "w1", 0, "o0");          // mint < w1
        event(Kind.WAKE, OLD, "w2", 0, "o0");          // already after it
        event(Kind.RECV, NEW, "n1", 0, "o2");
        event(Kind.WAKE, NEW, "n-wake", 0, "o2");      // begun later: free
        event(Kind.SEND, B, "b2", 1, "o9");            // a loop's second
        event(Kind.WAKE, OLD, "w3", 0, "o0");          // after b2: free
        event(Kind.RECV, C, "c1", 0, "o3");
        event(Kind.END, B, "b-end", 0, "o9");          // the clock
        event(Kind.WAKE, OLD, "w4", 1, "o0");          // c1 < w4
        event(Kind.SEND, OLD, "s", 0, "o0");
        event(Kind.WAKE, OLD, "w5", 2, "o0");          // after its own step
        assertEquals(Arrays.asList("mint<w1", "c1<w4"), edges("root"));
    }

    /** An occurrence that makes no event of its own (a clock read's) starts
     *  the order where it opened, its schedule mark. */
    @Test
    public void aMintWithoutEventsStartsWhereItOpened() {
        event(Kind.WAKE, OLD, "early", 0, "o0");
        event(Kind.RECV, B, "after-mint", 0, "o1");
        event(Kind.WAKE, OLD, "w", 0, "o0");
        marks.put("root", 1L);                           // opened before b's
        assertEquals(Arrays.asList("after-mint<w"), edges("root"));
        marks.put("root", 2L);                           // no step since
        assertEquals(Collections.<String>emptyList(), edges("root"));
    }

    /** A step in the work a loop's later send started has no name a native
     *  run makes alike: no edge; the first send's work keeps its edge, named
     *  without the endpoint's hash. */
    @Test
    public void aStepNamedByALoopsLaterSendHoldsNothing() {
        String sender = "t|Root:CLIENT/x#1|f@";
        event(Kind.WAKE, C, "poll", 0, "o0");               // c runs before
        event(Kind.WRITE, "t|Root:CLIENT/x#1", "mint", 0, "root");
        sent(Kind.SEND, sender + 1, "status", 0, "root", "e1");
        sent(Kind.SEND, sender + 2, "status", 1, "root", "e2");
        event(Kind.START, "n|Anchor:e2@rpc", "late-work", 0, "o2");
        event(Kind.WAKE, C, "poll", 1, "o0");               // after e2's work
        sent(Kind.SEND, sender + 3, "split", 0, "root", "e3");
        event(Kind.START, "n|Anchor:e3@rpc", "split-work", 0, "o3");
        event(Kind.WAKE, C, "poll", 2, "o0");
        List<ScheduleEvent[]> edges = RealizedOrder.edges(schedule,
                RealizedOrder.from(schedule, marks, set("root")),
                set("t|Root:CLIENT/x#1"), set(C, "t|Root:CLIENT/x#1",
                        "n|Anchor:e2@rpc", "n|Anchor:e3@rpc"));
        assertEquals(1, edges.size());
        assertEquals("split-work", edges.get(0)[0].site());
        assertEquals("n|Anchor:{t|Root:CLIENT/x#1|f >split}@rpc",
                edges.get(0)[0].context());
    }

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

    /**
     * The sender of a message a cone context received joins the cone, one
     * hop (solr-bugs-restore-construction: the RESTORE task whose
     * state-update message the mint's turn applied, and whose wait the
     * confirmed order held); a sender whose message no cone context
     * received does not.
     */
    @Test
    public void theSenderOfAMessageAConeContextReceivedJoinsTheCone() {
        String task = "n|Root:OVERSEER_TASK#3";
        String other = "n|Root:OVERSEER_TASK#9";
        String tick = "n|Root:OVERSEER_STATE_UPDATE#6";
        String client = "c|Root:CLIENT/x#1";
        event(Kind.WAKE, task + "|run@0", "w0", 0, "task"); // running before
        event(Kind.WAKE, other, "o0", 0, "other");           // running before
        sent(Kind.SEND, task + "|run@0", "queue", 0, "task", "e7");
        sent(Kind.SEND, other, "elsewhere", 0, "other", "e8");
        sent(Kind.RECV, tick, "take", 0, "osu", "e7");       // the mint's input
        event(Kind.WRITE, tick, "mint", 0, "root");
        event(Kind.WAKE, task + "|run@0", "w1", 0, "task");
        sent(Kind.RECV, client, "took", 0, "client", "e8");
        event(Kind.WRITE, tick, "mint2", 0, "root");
        event(Kind.WAKE, other, "o1", 0, "other");
        Object[][] rows = {   // the cone's occurrences, the edges
            {set(tick), list("mint<w1")},
            {set(tick, client), list("mint<w1", "mint2<o1")},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            Set<String> cone = (Set<String>) row[0];
            assertEquals(cone.toString(), row[1],
                    edges(set("root"), set(tick), cone));
        }
    }

    @Test
    public void aTurnCountedRootIsEveryRoleButTheClients() {
        Object[][] rows = {
            {"n|Root:OVERSEER_STATE_UPDATE#15", true},
            {"n|Root:WAKE/sleep#2|f@0", true},
            {"n|Root:CLIENT/.update#4|f@0", false},
            {"n|Root:CLIENTS#1", true},
            {"n|Anchor:ab@SOLR_HTTP/OVERSEER_TASK", false},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1],
                    RealizedOrder.turnCounted((String) row[0]));
        }
    }

    private static List<String> list(String... sites) {
        return Arrays.asList(sites);
    }

    @Test
    public void noMintMadeNoOrder() {
        event(Kind.WAKE, A, "w", 0, "o0");
        event(Kind.RECV, B, "r", 0, "o1");
        event(Kind.WAKE, A, "w", 1, "o0");
        assertEquals(Collections.<String>emptyList(), edges("root"));
    }
}
