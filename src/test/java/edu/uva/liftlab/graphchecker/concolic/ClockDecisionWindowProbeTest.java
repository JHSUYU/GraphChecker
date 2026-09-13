package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The text-level halves of the solver stage's model-decided freedom and
 * clock-window probes: which comparisons a clock takes part in, how a
 * window is widened, and which selectors read a merged boundary.
 */
public class ClockDecisionWindowProbeTest {
    private static final String CLOCK = "manual__MANUAL_clock";

    /** Java's lcmp idiom yields one atom per operand pair, not two. */
    @Test
    public void lcmpIdiomCountsOncePerOperandPair() {
        String smt = "(declare-const " + CLOCK + " Int)\n"
                + "(declare-const expiry Int)\n"
                + "(assert (= dag (< (ite (< expiry " + CLOCK + ") (- 1)"
                + " (ite (> expiry " + CLOCK + ") 1 0)) 0)))\n"
                + "(assert (>= " + CLOCK + " 5))\n";
        List<String> atoms = BooleanReachConditionExtractor
                .clockComparisonAtoms(smt, Arrays.asList(CLOCK), 8);
        assertEquals(Arrays.asList("(< expiry " + CLOCK + ")",
                "(>= " + CLOCK + " 5)"), atoms);
    }

    /** A symbol that merely prefixes a longer one is not an occurrence. */
    @Test
    public void prefixOfALongerSymbolIsNotTheClock() {
        String smt = "(assert (< " + CLOCK + "_other 3))\n";
        assertTrue(BooleanReachConditionExtractor.clockComparisonAtoms(
                smt, Arrays.asList(CLOCK), 8).isEmpty());
    }

    /**
     * HDFS-17897: a two-node mechanism needs one decision per node, and the
     * first node's reads alone can fill the budget.  The NameNode clock is
     * read eight times on that slice and the DataNode clock once; taking the
     * clocks in order probed the NameNode eight times and never asked about
     * the DataNode's removal at all.
     */
    @Test
    public void everyClockIsAskedAboutBeforeAnyClockIsAskedTwice() {
        String other = "manual__MANUAL_dn";
        StringBuilder smt = new StringBuilder();
        for (int index = 0; index < 6; index++) {
            smt.append("(assert (< nn").append(index).append(' ')
                    .append(CLOCK).append("))\n");
        }
        smt.append("(assert (< dn0 ").append(other).append("))\n");
        List<String> atoms = BooleanReachConditionExtractor
                .clockComparisonAtoms(smt.toString(),
                        Arrays.asList(CLOCK, other), 4);

        assertEquals(4, atoms.size());
        assertTrue(atoms.contains("(< dn0 " + other + ")"));
        assertEquals("(< nn0 " + CLOCK + ")", atoms.get(0));
        assertEquals("(< dn0 " + other + ")", atoms.get(1));
    }

    /**
     * The clock's own domain, window and order are not program decisions.
     * Probing them asks whether a long can leave its range, and the refusal
     * that comes back reads as a decision the composition pinned.
     */
    @Test
    public void theClocksOwnPhysicsIsNotAProgramDecision() {
        String smt = "(assert (! (and (<= (- 9223372036854775808) " + CLOCK
                + ") (<= " + CLOCK + " 9223372036854775807))"
                + " :named java_integral_domain_1_x))\n"
                + "(assert (! (and (>= " + CLOCK + " 5) (<= " + CLOCK
                + " 9)) :named clock_window__a))\n"
                + "(assert (! (<= " + CLOCK + " other) :named"
                + " clock_monotonic__b))\n"
                + "(assert (= dag (< expiry " + CLOCK + ")))\n";

        assertEquals(Arrays.asList("(< expiry " + CLOCK + ")"),
                BooleanReachConditionExtractor.clockComparisonAtoms(
                        smt, Arrays.asList(CLOCK), 8));
    }

    /** Dropping leaves the clock unbounded, which widening never does. */
    @Test
    public void droppingRemovesTheWindowAltogether() {
        Map<String, JsonObject> clocks = new LinkedHashMap<>();
        JsonObject read = new JsonObject();
        read.addProperty("recordedValue", 1000L);
        clocks.put(CLOCK, read);
        String base = "(assert (! " + ClockRootPhysics.window(CLOCK, 1000L,
                300L) + " :named clock_window__x))\n";

        String dropped = BooleanReachConditionExtractor.dropClockWindows(
                base, clocks, 300L);

        assertTrue(dropped.contains("(! true :named clock_window__x)"));
        assertFalse(dropped.contains(CLOCK));
    }

    /** Widening rewrites exactly the window the composer emitted. */
    @Test
    public void wideningReplacesTheEmittedWindowBody() {
        Map<String, JsonObject> clocks = new LinkedHashMap<>();
        JsonObject read = new JsonObject();
        read.addProperty("recordedValue", 1000L);
        clocks.put(CLOCK, read);
        String base = "(assert (! " + ClockRootPhysics.window(CLOCK, 1000L,
                300L) + " :named clock_window__x))\n";
        String widened = BooleanReachConditionExtractor.widenClockWindows(
                base, clocks, 300L, 1200L);
        assertTrue(widened.contains("(>= " + CLOCK + " (- 200))"));
        assertTrue(widened.contains("(<= " + CLOCK + " 2200)"));
        assertFalse(widened.contains("1300"));
    }

    /**
     * A guarded read arm consumes a merged boundary under its read selector
     * and a merge consumes another under the arm's case selector; the
     * boundary's own definition is not a consumer of it.
     */
    @Test
    public void consumersAreTheSelectorsThatReadTheBoundary() {
        JsonObject manifest = new JsonObject();
        JsonArray totality = new JsonArray();
        JsonObject dispatch = new JsonObject();
        dispatch.addProperty("solverTerm", "merged_boundary__a");
        dispatch.addProperty("totalDispatch", false);
        totality.add(dispatch);
        JsonObject total = new JsonObject();
        total.addProperty("solverTerm", "merged_boundary__t");
        total.addProperty("totalDispatch", true);
        totality.add(total);
        manifest.add(ConcolicSmtComposer.BOUNDARY_DISPATCH_TOTALITY,
                totality);
        String smt = "(assert (= merged_boundary__a (ite case_observation__1"
                + " rf_value__x unbound_boundary__a)))\n"
                + "(assert (! (=> read_selector__r (and dag (= rf_value__y"
                + " merged_boundary__a))) :named guarded_read_value__1))\n"
                + "(assert (= merged_boundary__b (ite case_selector__c"
                + " merged_boundary__a unbound_boundary__b)))\n"
                + "(assert (= merged_boundary__t (ite case_selector__d"
                + " merged_boundary__a 0)))\n";
        Map<String, List<String>> consumers = BooleanReachConditionExtractor
                .boundaryConsumers(smt, manifest);
        assertEquals(Arrays.asList("read_selector__r", "case_selector__c",
                "case_selector__d"), consumers.get("merged_boundary__a"));
        assertFalse(consumers.containsKey("merged_boundary__t"));
    }

    /**
     * The fatal predicate's boundary is bound to its guarded read through a
     * single-arm dispatch now that the arm carries its own guard; the arms
     * of that read are still resolved.
     */
    @Test
    public void fatalReadArmsResolveThroughASingleArmDispatch() {
        JsonObject manifest = new JsonObject();
        JsonObject model = new JsonObject();
        JsonArray reads = new JsonArray();
        JsonObject read = new JsonObject();
        JsonArray arms = new JsonArray();
        JsonObject arm = new JsonObject();
        arm.addProperty("valueTerm", "rf_value__RFC_f__1");
        arm.addProperty("selector", "read_selector__a");
        arm.addProperty("readIdentity", "RFC.f");
        arm.addProperty("writerCaseOwner", "region:R/instance:i");
        arms.add(arm);
        read.add("arms", arms);
        reads.add(read);
        model.add("reads", reads);
        manifest.add("guardedReadModel", model);
        String smt = "(assert (= merged_boundary__m (ite case_selector__c"
                + " rf_value__RFC_f__1 unbound_boundary__m)))\n"
                + "(assert (! (and case_selector__c (= merged_boundary__m"
                + " nullRef)) :named fatal_path))\n";
        List<JsonObject> resolved = BooleanReachConditionExtractor
                .fatalReadArms(smt, manifest);
        assertEquals(1, resolved.size());
        assertEquals("read_selector__a",
                resolved.get(0).get("selector").getAsString());
    }
}
