package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.Z3;

import org.junit.Test;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.Assert.assertEquals;

public class NearestWorldTest {
    private static final Pattern PIN =
            Pattern.compile("\\(assert \\(= (\\S+) (\\S+)\\)\\)");

    @Test
    public void aLeafTheFlipDoesNotNeedIsPlantedAtItsRecordedValue()
            throws Exception {
        Map<String, String> recorded = map("s", "\"active\"", "r",
                "\"0-7f\"", "o", "\"active\"");
        Object[][] rows = {
            {map("s", "\"x\"", "r", "\"\"", "o", "\"\""), set(),
                    map("s", "\"x\"", "r", "\"0-7f\"", "o", "\"active\""),
                    "every leaf but the flip's own at its recording"},
            {map("s", "\"x\"", "r", "\"\"", "o", "\"\""), set("o"),
                    map("s", "\"x\"", "r", "\"0-7f\"", "o", "\"\""),
                    "a leaf the flip needs keeps the solver's value"},
            {map("s", "\"x\"", "r", "\"0-7f\"", "o", "\"active\""), set(),
                    map("s", "\"x\"", "r", "\"0-7f\"", "o", "\"active\""),
                    "a model already at its recording is kept"},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            Map<String, String> first = (Map<String, String>) row[0];
            @SuppressWarnings("unchecked")
            Set<String> needed = (Set<String>) row[1];
            NearestWorld nearest = NearestWorld.of(
                    query -> solve(query, first, needed), "", symbols(),
                    recorded, set("s"), Z3.Answer.decided("sat", first),
                    true);
            assertEquals((String) row[3], row[2], nearest.answer.values());
        }
    }

    private static Z3.Answer solve(String query, Map<String, String> first,
                                   Set<String> needed) {
        Map<String, String> values = new LinkedHashMap<String, String>(first);
        Matcher pins = PIN.matcher(query);
        while (pins.find()) {
            if (needed.contains(pins.group(1))) {
                return Z3.Answer.decided("unsat",
                        new LinkedHashMap<String, String>());
            }
            values.put(pins.group(1), pins.group(2));
        }
        return Z3.Answer.decided("sat", values);
    }

    private static List<String> symbols() {
        return Arrays.asList("s", "r", "o");
    }

    private static Map<String, String> map(String... pairs) {
        Map<String, String> map = new LinkedHashMap<String, String>();
        for (int at = 0; at + 1 < pairs.length; at += 2) {
            map.put(pairs[at], pairs[at + 1]);
        }
        return map;
    }

    private static Set<String> set(String... names) {
        return new HashSet<String>(Arrays.asList(names));
    }
}
