package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §4.4: where a root an occurrence read goes inside it (its
 * influence, and the way into what is demanded), and the doors of the
 * message that started an occurrence.
 */
public class RootRelevanceTest {
    private static final String M = "<a.C: void m()>";
    private static final String OTHER = "<a.D: void n()>";
    private static final String STORED = "<a.C: long expiry>";
    private static final String ROOT = M + "::$l0";

    @Test
    public void aRootReachesTheStoresItDecidesAndTheWiresItFeeds() {
        List<Map<String, Object>> graph = Arrays.asList(
                edge("local_def_use", ROOT, M + "::$l1", M),
                // the arm the root decides stores the location
                edge("guard_dependency", M + "::$l1", STORED, M),
                edge("local_def_use", M + "::$l1", M + "::$l2", M),
                edge("wire_handoff", M + "::$l2", OTHER + "::$i0", OTHER),
                // an edge of a method this occurrence did not perform
                edge("local_def_use", ROOT, OTHER + "::$x", OTHER),
                // past the store: whoever reads the location next
                edge("field_read", STORED, M + "::$l9", M));
        Map<String, List<String>> methods = new LinkedHashMap<>();
        methods.put("REGION.r", Collections.singletonList(M));
        RootRelevance relevance = new RootRelevance(graph,
                Collections.singleton(STORED), methods,
                Collections.<ScheduleEvent>emptyList());
        RootRelevance.Influence influence = relevance.influence(
                Collections.singletonList("REGION.r"), ROOT);
        Object[][] rows = {
            {"the stored locations it reaches", set(STORED),
                influence.carriers},
            {"the wire consumers its value is handed to",
                set(OTHER + "::$i0"), influence.consumers},
            {"its way into a demanded location",
                set(ROOT, M + "::$l1", STORED),
                influence.through(Collections.singleton(STORED))},
            {"its way into a demanded wire",
                set(ROOT, M + "::$l1", M + "::$l2", OTHER + "::$i0"),
                influence.through(Collections.singleton(OTHER + "::$i0"))},
            {"no way in when nothing is demanded", set(),
                influence.through(Collections.<String>emptySet())},
            {"a region that does not hold the method holds none of it",
                set(), relevance.influence(
                        Collections.singletonList("REGION.q"), ROOT).carriers},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], new HashSet<>((Set<?>) row[2]));
        }
    }

    @Test
    public void aMessagesDoorsAreItsSenderAndItsReceivers() {
        List<ScheduleEvent> schedule = Arrays.asList(
                ScheduleEvent.of(0, ScheduleEvent.Kind.SEND,
                        "s/n0#epoch0|Root:CLIENT/hb#1", "HADOOP_IPC#REQUEST",
                        0, "sender", "e1"),
                ScheduleEvent.of(1, ScheduleEvent.Kind.RECV,
                        "s/n1#epoch0|Anchor:e1@HADOOP_IPC/hb",
                        "HADOOP_IPC#REQUEST", 0, "receiver"),
                // a role's send: no occurrence holds its door
                ScheduleEvent.of(2, ScheduleEvent.Kind.SEND,
                        "s/n1#epoch0|Anchor:e1@HADOOP_IPC/hb",
                        "HADOOP_IPC#RESPONSE", 0, "", "e2"));
        RootRelevance relevance = new RootRelevance(
                Collections.<Map<String, Object>>emptyList(),
                Collections.<String>emptySet(),
                Collections.<String, List<String>>emptyMap(), schedule);
        Object[][] rows = {
            {"started by message e1", "Anchor:e1@HADOOP_IPC/hb",
                set("sender", "receiver")},
            {"started by a role's message", "Anchor:e2@HADOOP_IPC/hb", set()},
            {"started by no message", "Root:CLIENT/hb#1", set()},
        };
        for (Object[] row : rows) {
            OccurrenceAddress occurrence = OccurrenceAddress.parse(
                    "s/n1#epoch0/region/REGION.h/ctx:" + row[1] + "/idx:");
            assertEquals((String) row[0], row[2],
                    relevance.doorsOf(occurrence));
        }
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String method) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", kind);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        edge.put("method", method);
        return edge;
    }

    private static Set<String> set(String... cells) {
        return new HashSet<>(Arrays.asList(cells));
    }
}
