package edu.uva.liftlab.graphchecker.concolic;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
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
}
