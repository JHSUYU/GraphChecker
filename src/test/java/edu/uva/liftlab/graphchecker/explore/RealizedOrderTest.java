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
import org.junit.Test;

/**
 * The realized order a native reproduction holds (PIPELINE §10b): from
 * where a moved root's mint occurrence opened on, each WAKE of a context
 * running before it after the step just before it, when that step is
 * another context's first of its kind and site.
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

    private List<String> edges(String... mints) {
        List<String> edges = new ArrayList<String>();
        for (ScheduleEvent[] edge : RealizedOrder.edges(schedule,
                RealizedOrder.from(schedule, marks,
                        new HashSet<String>(Arrays.asList(mints))))) {
            edges.add(edge[0].site() + "<" + edge[1].site());
        }
        return edges;
    }

    @Test
    public void aRunningContextsWakeWaitsForTheFirstStepBeforeIt() {
        event(Kind.WAKE, "old", "old-started", 0, "o0"); // old runs before
        event(Kind.SEND, "b", "b-early", 0, "o9");
        event(Kind.WRITE, "a", "mint", 0, "root");       // the root's mint
        event(Kind.WAKE, "old", "w1", 0, "o0");          // mint < w1
        event(Kind.WAKE, "old", "w2", 0, "o0");          // already after it
        event(Kind.RECV, "new", "n1", 0, "o2");
        event(Kind.WAKE, "new", "n-wake", 0, "o2");      // begun later: free
        event(Kind.SEND, "b", "b2", 1, "o9");            // a loop's second
        event(Kind.WAKE, "old", "w3", 0, "o0");          // after b2: free
        event(Kind.RECV, "c", "c1", 0, "o3");
        event(Kind.END, "b", "b-end", 0, "o9");          // the clock
        event(Kind.WAKE, "old", "w4", 1, "o0");          // c1 < w4
        event(Kind.SEND, "old", "s", 0, "o0");
        event(Kind.WAKE, "old", "w5", 2, "o0");          // after its own step
        assertEquals(Arrays.asList("mint<w1", "c1<w4"), edges("root"));
    }

    /** An occurrence that makes no event of its own (a clock read's) starts
     *  the order where it opened, its schedule mark. */
    @Test
    public void aMintWithoutEventsStartsWhereItOpened() {
        event(Kind.WAKE, "old", "early", 0, "o0");
        event(Kind.RECV, "b", "after-mint", 0, "o1");
        event(Kind.WAKE, "old", "w", 0, "o0");
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
        event(Kind.WAKE, "c", "poll", 0, "o0");             // c runs before
        event(Kind.WRITE, "t", "mint", 0, "root");
        sent(Kind.SEND, "t|x@1", "status", 0, "root", "e1");
        sent(Kind.SEND, "t|x@2", "status", 1, "root", "e2");
        event(Kind.START, "n|Anchor:e2@rpc", "late-work", 0, "o2");
        event(Kind.WAKE, "c", "poll", 1, "o0");             // after e2's work
        sent(Kind.SEND, "t|x@3", "split", 0, "root", "e3");
        event(Kind.START, "n|Anchor:e3@rpc", "split-work", 0, "o3");
        event(Kind.WAKE, "c", "poll", 2, "o0");
        List<ScheduleEvent[]> edges = RealizedOrder.edges(schedule,
                RealizedOrder.from(schedule, marks,
                        new HashSet<String>(Arrays.asList("root"))));
        assertEquals(1, edges.size());
        assertEquals("split-work", edges.get(0)[0].site());
        assertEquals("n|Anchor:{t|x >split}@rpc", edges.get(0)[0].context());
    }

    @Test
    public void noMintMadeNoOrder() {
        event(Kind.WAKE, "a", "w", 0, "o0");
        event(Kind.RECV, "b", "r", 0, "o1");
        event(Kind.WAKE, "a", "w", 1, "o0");
        assertEquals(Collections.<String>emptyList(), edges("root"));
    }
}
