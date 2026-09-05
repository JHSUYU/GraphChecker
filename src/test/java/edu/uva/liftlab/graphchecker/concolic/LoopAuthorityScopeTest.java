package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.junit.Test;

/**
 * A retained loop decides acceptance only when it lies inside the slice the
 * witness is built from.
 *
 * <p>Every site below is a real loop site id from HDFS-11741's campaign-run14,
 * where 48 retained loops named {@code BOUNDED_LOOP_BODY_BOUND_UNDECLARED} and
 * all 48 became acceptance blockers.  Only a handful are in any selected
 * relation's definition methods; the rest are configuration parsing, metrics
 * registration, reflection and protobuf validation that the run walked and the
 * model never had to hold.
 */
public class LoopAuthorityScopeTest {

    private static final String ADD_KEYS =
            "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: void addKeys(org.apache.hadoop"
                    + ".hdfs.security.token.block.ExportedBlockKeys)>";
    private static final String SUBSTITUTE_VARS =
            "<org.apache.hadoop.conf.Configuration: java.lang.String "
                    + "substituteVars(java.lang.String)>";
    private static final String REMOVE_EXPIRED =
            "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: void removeExpiredKeys()>";

    private static Set<String> scope(String... methods) {
        return new LinkedHashSet<>(Arrays.asList(methods));
    }

    @Test
    public void aLoopInsideTheSelectedSliceStillDecidesAcceptance() {
        assertTrue(ConcolicSmtComposer.touchesSelectedScope(
                ADD_KEYS + "#u20", scope(ADD_KEYS, REMOVE_EXPIRED)));
    }

    @Test
    public void aLoopOutsideEverySelectedSliceDoesNot() {
        assertFalse(ConcolicSmtComposer.touchesSelectedScope(
                SUBSTITUTE_VARS + "#u10", scope(ADD_KEYS, REMOVE_EXPIRED)));
    }

    @Test
    public void aNestCountsWhenAnyMemberIsInTheSlice() {
        String nest = "L(" + SUBSTITUTE_VARS + "#u10+" + ADD_KEYS + "#u20)";
        assertTrue(ConcolicSmtComposer.touchesSelectedScope(
                nest, scope(ADD_KEYS)));
        String outside = "L(" + SUBSTITUTE_VARS + "#u10+"
                + SUBSTITUTE_VARS + "#u23)";
        assertFalse(ConcolicSmtComposer.touchesSelectedScope(
                outside, scope(ADD_KEYS)));
    }

    @Test
    public void anEmptyScopeKeepsEveryLoopDeciding() {
        // Nothing lowered means no slice to compare against.  Silently
        // dropping every loop authority there would turn "the composition
        // selected nothing" into "no loop mattered".
        assertTrue(ConcolicSmtComposer.touchesSelectedScope(
                SUBSTITUTE_VARS + "#u10", Collections.<String>emptySet()));
    }

    @Test
    public void missingFixedCardinalityDecidesOnlyInsideTheSelectedSlice() {
        assertTrue(ConcolicSmtComposer.loopAuthorityRefuses(
                LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                ADD_KEYS + "#u20", scope(ADD_KEYS)));
        assertFalse(ConcolicSmtComposer.loopAuthorityRefuses(
                LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                SUBSTITUTE_VARS + "#u10", scope(ADD_KEYS)));
    }

    /**
     * A constructor's loop decides exactly like any other loop's.
     *
     * <p>The scope test used to scan the subject for {@code <...>}, which on
     * {@code <C: void <init>(..)>#u17} matches only {@code <init>} -- a name
     * no slice ever holds.  Every loop-authority gap inside a constructor
     * therefore stopped deciding acceptance, silently.</p>
     */
    @Test
    public void aConstructorLoopInsideTheSliceStillDecides() {
        String constructor =
                "<org.apache.hadoop.metrics2.lib.MetricsSourceBuilder: "
                        + "void <init>(java.lang.Object)>";
        assertTrue(ConcolicSmtComposer.touchesSelectedScope(
                constructor + "#u17", scope(constructor, ADD_KEYS)));
        assertFalse(ConcolicSmtComposer.touchesSelectedScope(
                constructor + "#u17", scope(ADD_KEYS, REMOVE_EXPIRED)));
        // And the same through a gap subject, which carries the occurrence
        // on its own line ahead of the site.
        assertTrue(ConcolicSmtComposer.touchesSelectedScope(
                "cluster0/dn0#epoch1/region/REGION.X#1\n" + constructor
                        + "#u17", scope(constructor)));
    }

    @Test
    public void targetMethodJoinsProducerMethodsInAcceptanceScope() {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("targetSiteId", ADD_KEYS + "#u40");

        Set<String> selected =
                ConcolicSmtComposer.withTargetScopeMethod(
                        scope(REMOVE_EXPIRED), fatal);

        assertTrue(selected.contains(REMOVE_EXPIRED));
        assertTrue(selected.contains(ADD_KEYS));
        assertTrue(ConcolicSmtComposer.loopAuthorityRefuses(
                LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                ADD_KEYS + "#u20", selected));
    }

    @Test
    public void unsatClosureFiltersOnlyOffSliceLoopTelemetry() {
        BoundedLoopComposition loops = BoundedLoopComposition.empty();
        loops.gap(BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                "cluster0/worker0#epoch0/region/REGION.OUTSIDE#1\n"
                        + SUBSTITUTE_VARS + "#u10",
                "retained loop has no selected task-derived authority");

        List<JsonObject> coverage = new ArrayList<>(loops.gaps());
        int closureGapCount = ConcolicSmtComposer
                .unsatClosureCoverageGapCount(coverage, scope(ADD_KEYS));
        assertEquals(0, closureGapCount);
        assertEquals(1, coverage.size());
        JsonObject fatal = new JsonObject();
        fatal.add("coverageGaps", new JsonArray());
        assertTrue(ConcolicSmtComposer.unsatClosureEvidence(true,
                Collections.emptyList(), fatal, true, closureGapCount).get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());

        loops.gap(BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                "cluster0/nn0#epoch0/region/REGION.SELECTED#1\n"
                        + ADD_KEYS + "#u20",
                "selected loop has no task-derived authority");
        coverage = new ArrayList<>(loops.gaps());
        coverage.add(CoverageDivergence.of(CoverageDivergence.Kind.FLOW,
                "RECORDED_FLOW_OPEN", "EDGE.OTHER", "unclosed flow"));

        closureGapCount = ConcolicSmtComposer
                .unsatClosureCoverageGapCount(coverage, scope(ADD_KEYS));
        assertEquals(2, closureGapCount);
        assertFalse(ConcolicSmtComposer.unsatClosureEvidence(true,
                Collections.emptyList(), fatal, true, closureGapCount).get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
        // The decision count is scope-filtered; the raw telemetry is intact.
        assertEquals(3, coverage.size());
    }
}
