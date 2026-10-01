package edu.uva.liftlab.graphchecker.causynth;

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
 * influence), and its way into what is demanded.
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
                Collections.singleton(STORED), methods);
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
