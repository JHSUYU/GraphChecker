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
 * The realized order a native reproduction holds (PIPELINE §10b): the
 * confirmed schedule from where a moved root's mint occurrence opened on,
 * reduced to one edge per context switch; the clock (WAKE, END) is never a
 * before, an END never an after.
 */
public class RealizedOrderTest {
    private final List<ScheduleEvent> schedule = new ArrayList<ScheduleEvent>();

    private void event(Kind kind, String context, String site,
                       String occurrence) {
        schedule.add(ScheduleEvent.of(schedule.size(), kind, context, site,
                0, occurrence, ""));
    }

    private final Map<String, Long> marks = new HashMap<String, Long>();

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
    public void theOrderFromTheMintOnReducedToItsContextSwitches() {
        event(Kind.SEND, "a", "early", "o0");      // before the mint: free
        event(Kind.RECV, "b", "early-recv", "o9");
        event(Kind.WRITE, "a", "mint", "root");    // the root's mint
        event(Kind.WRITE, "a", "a2", "o1");        // same context: no edge
        event(Kind.RECV, "b", "b1", "o2");         // a2 < b1
        event(Kind.WAKE, "c", "c-wake", "o3");     // b1 < c-wake
        event(Kind.END, "b", "b-end", "o2");       // an END: no edge
        event(Kind.SEND, "c", "c1", "o3");         // after its own WAKE only
        event(Kind.RECV, "a", "a3", "o1");         // c1 < a3
        event(Kind.WAKE, "b", "b-wake", "o2");     // a3 < b-wake
        event(Kind.SEND, "b", "b2", "o2");         // b-wake already after a3
        assertEquals(Arrays.asList("a2<b1", "b1<c-wake", "c1<a3",
                "a3<b-wake"), edges("root"));
    }

    /** An occurrence that makes no event of its own (a clock read's) starts
     *  the order where it opened, its schedule mark. */
    @Test
    public void aMintWithoutEventsStartsWhereItOpened() {
        event(Kind.SEND, "a", "early", "o0");
        event(Kind.RECV, "b", "opened", "o1");     // the mint opened before
        event(Kind.SEND, "a", "a1", "o0");
        marks.put("root", 1L);
        assertEquals(Arrays.asList("opened<a1"), edges("root"));
        marks.put("root", 3L);
        assertEquals(Collections.<String>emptyList(), edges("root"));
    }

    @Test
    public void noMintMadeNoOrder() {
        event(Kind.SEND, "a", "s", "o0");
        event(Kind.RECV, "b", "r", "o1");
        assertEquals(Collections.<String>emptyList(), edges("root"));
    }
}
