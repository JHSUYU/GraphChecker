package edu.uva.liftlab.graphchecker.explore;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;

public class KeyGateTest {
    @Test
    public void anUnsatAskIsExplainedOnlyByAWorldItExtends() {
        Set<String> seed = Collections.<String>emptySet();
        Set<String> f = world("F");
        Set<String> g = world("G");
        Set<String> fg = world("F", "G");
        Object[][] rows = {
            {Arrays.asList(seed), Arrays.asList(f), true,
                    "the seed's arm SAT, a one-flip world's UNSAT: its"
                            + " inherited prefix added conjuncts"},
            {Arrays.asList(f), Arrays.asList(fg), true,
                    "two flips extend one"},
            {Arrays.asList(f), Arrays.asList(g), false,
                    "siblings: neither extends the other"},
            {Arrays.asList(f), Arrays.asList(seed), false,
                    "the smaller world UNSAT, a larger one SAT: no prefix"
                            + " adds a model"},
            {Arrays.asList(f), Arrays.asList(f), false,
                    "one world, two answers"},
            {Arrays.asList(seed, g), Arrays.asList(fg, f), true,
                    "each UNSAT world extends some satisfiable one"},
        };
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            List<Set<String>> satisfiable = (List<Set<String>>) row[0];
            @SuppressWarnings("unchecked")
            List<Set<String>> unsat = (List<Set<String>>) row[1];
            assertEquals((String) row[3], row[2],
                    KeyGate.nestedOnly(satisfiable, unsat));
        }
    }

    private static Set<String> world(String... flips) {
        return new LinkedHashSet<String>(Arrays.asList(flips));
    }
}
