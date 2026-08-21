package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * README section 5's {@code K_L} is per loop, and the executor limit is
 * derived from the declarations rather than fixed beside them.
 *
 * <pre>
 * Every loop L retained by an accepted model must declare K_L, the maximum
 * number of loop-body executions.  GraphChecker translates it to the
 * executor's internal backedge limit and rejects an observed count above K_L.
 * </pre>
 *
 * <p>The one property these cases exist for is the direction the bounded
 * semantics may not fail in: the backedge limit the executor is instrumented
 * with is never below a bound the model states.  A limit below it would cut a
 * replay before the prefix the model holds and produce a relation for a
 * prefix the run never completed.</p>
 */
public class PerLoopBodyBoundTest {

    private static final String LOOKUP =
            "<example.DataNode: java.lang.Object lookup(int)>#u12";
    private static final String ROTATION =
            "<example.NameNode: void rotate()>#u3";

    // ------------------------------------------------------------------
    // The declaration
    // ------------------------------------------------------------------

    /** A loop that declares nothing inherits the workload default. */
    @Test
    public void undeclaredLoopInheritsTheDefault() {
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                LoopBoundPolicy.bodyBound(null));
        assertEquals(LoopBoundPolicy.BOUND_FROM_POLICY,
                LoopBoundPolicy.boundAuthority(null));
    }

    /**
     * A loop may now declare more than it would inherit.
     *
     * <p>This is the whole decision: a global bound of
     * {@code MAX_LOOP_BODY_ITERATIONS} contains rotation only, and a lookup
     * loop whose trip count is a property of the recorded state cannot be
     * fitted into it by the workload.</p>
     */
    @Test
    public void aLoopMayDeclareMoreThanItWouldInherit() {
        int declared = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS * 4;
        assertTrue(declared
                <= LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS);
        assertEquals(declared,
                LoopBoundPolicy.bodyBound(Integer.valueOf(declared)));
        assertEquals(LoopBoundPolicy.BOUND_FROM_DECLARATION,
                LoopBoundPolicy.boundAuthority(Integer.valueOf(declared)));
        assertEquals(LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS,
                LoopBoundPolicy.bodyBound(Integer.valueOf(
                        LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS)));
    }

    /** A loop may still narrow below what it would inherit. */
    @Test
    public void aLoopMayStillNarrow() {
        assertEquals(2, LoopBoundPolicy.bodyBound(Integer.valueOf(2)));
        assertEquals(1, LoopBoundPolicy.bodyBound("1"));
    }

    /**
     * A declaration outside the per-loop ceiling is refused by name.
     *
     * <p>Refused and not clamped: a clamp would emit a model over a bound
     * nobody declared, and the loop's own prefix is what
     * {@code BOUND_EXHAUSTED} is stated over.</p>
     */
    @Test
    public void aDeclarationOutsideTheCeilingIsRefusedByName() {
        refusesBound(Integer.valueOf(
                LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS + 1));
        refusesBound(Integer.valueOf(0));
        refusesBound(Integer.valueOf(-1));
        refusesBound("not-a-bound");
    }

    private static void refusesBound(Object declared) {
        try {
            LoopBoundPolicy.bodyBound(declared);
            fail("expected a refusal for declared bound " + declared);
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    LoopBoundPolicy.DECLARED_BOUND_OUT_OF_RANGE));
        }
    }

    // ------------------------------------------------------------------
    // The translation to the executor
    // ------------------------------------------------------------------

    /** With nothing declared the executor limit is the inherited bound. */
    @Test
    public void anUndeclaredCampaignKeepsTheInheritedLimit() {
        LoopBoundPolicy policy = LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals());
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals(LOOKUP));
        assertTrue(policy.declaredBounds().isEmpty());
    }

    /**
     * The executor limit is never below a bound the model states.
     *
     * <p>This is the coupling the per-loop declaration creates.  The
     * instrumenter stamps one constant on a loop it cannot narrow, so that
     * constant has to accommodate the widest declaration of the campaign;
     * anything smaller would cut a replay short of a prefix the model holds
     * and hand back a relation for a run that never finished it.</p>
     */
    @Test
    public void theExecutorLimitAccommodatesEveryDeclaredBound() {
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(ROTATION, Integer.valueOf(4));
        declared.put(LOOKUP, Integer.valueOf(
                LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS));
        LoopBoundPolicy policy = LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared);

        assertEquals(LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals());
        for (Map.Entry<String, Integer> entry
                : policy.declaredBounds().entrySet()) {
            assertTrue(entry.getKey(), entry.getValue().intValue()
                    <= policy.maxBackedgeTraversals());
        }
        assertTrue(policy.defaultBackedgeTraversals()
                <= policy.maxBackedgeTraversals());
    }

    /** Each loop's own {@code K_L} is what the instrumenter can narrow to. */
    @Test
    public void eachLoopAnswersWithItsOwnBound() {
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(LOOKUP, Integer.valueOf(60));
        LoopBoundPolicy policy = LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared);

        assertEquals(60, policy.maxBackedgeTraversals(LOOKUP));
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals(ROTATION));
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                policy.maxBackedgeTraversals(null));
    }

    /** A declared bound outside the ceiling never reaches the executor. */
    @Test
    public void thePolicyRefusesADeclarationOutsideTheCeiling() {
        refusesPolicy(LOOKUP, LoopBoundPolicy
                .MAX_DECLARED_LOOP_BODY_ITERATIONS + 1,
                LoopBoundPolicy.DECLARED_BOUND_OUT_OF_RANGE);
        refusesPolicy(LOOKUP, 0,
                LoopBoundPolicy.DECLARED_BOUND_OUT_OF_RANGE);
        refusesPolicy("", 4,
                LoopBoundPolicy.DECLARED_BOUND_SITE_UNDECLARED);
    }

    private static void refusesPolicy(String loopSiteId, int bound,
                                      String reason) {
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(loopSiteId, Integer.valueOf(bound));
        try {
            LoopBoundPolicy.cfgBackedges(
                    LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared);
            fail("expected a refusal for " + loopSiteId + "=" + bound);
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().startsWith(reason));
        }
    }

    // ------------------------------------------------------------------
    // The encoded contract
    // ------------------------------------------------------------------

    /** A campaign that declares nothing encodes exactly as it did before. */
    @Test
    public void anUndeclaredContractKeepsItsEncoding() {
        LoopBoundPolicy policy = LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
        JsonObject encoded = policy.toJson();
        assertEquals(5, encoded.entrySet().size());
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                encoded.get("maxBackedgeTraversals").getAsInt());
        assertEquals("CFG_BACKEDGE:"
                        + LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS
                        + ":CUT_PATH", policy.identity());
    }

    /** Declarations travel with the contract and survive the round trip. */
    @Test
    public void declarationsRoundTrip() {
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(LOOKUP, Integer.valueOf(60));
        declared.put(ROTATION, Integer.valueOf(4));
        LoopBoundPolicy policy = LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared);

        JsonObject owner = new JsonObject();
        policy.writeTo(owner);
        LoopBoundPolicy decoded = LoopBoundPolicy.decode(owner);

        assertEquals(policy.identity(), decoded.identity());
        assertEquals(60, decoded.maxBackedgeTraversals());
        assertEquals(60, decoded.maxBackedgeTraversals(LOOKUP));
        assertEquals(4, decoded.maxBackedgeTraversals(ROTATION));
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                decoded.defaultBackedgeTraversals());
    }

    /**
     * The declarations decide the limit, so a row stating another is refused.
     *
     * <p>Fail-closed: a row whose limit does not follow from its own
     * declarations was written against a different rule, and honouring
     * either half of it would state an executor the run did not use.</p>
     */
    @Test
    public void anEncodedLimitThatIsNotDerivedIsRefused() {
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(LOOKUP, Integer.valueOf(60));
        JsonObject owner = new JsonObject();
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                declared).writeTo(owner);
        owner.getAsJsonObject(LoopBoundPolicy.FIELD)
                .addProperty("maxBackedgeTraversals",
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
        try {
            LoopBoundPolicy.decode(owner);
            fail("expected a refusal for an underived executor limit");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    LoopBoundPolicy.EXECUTOR_LIMIT_MISMATCH));
        }
    }

    /** A row written before per-loop bounds existed still decodes. */
    @Test
    public void aContractWithoutDeclarationsStillDecodes() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("schemaVersion", 1);
        encoded.addProperty("kind", "CFG_BACKEDGE");
        encoded.addProperty("scope", "ALL_EXECUTION_SCOPE_LOOPS");
        encoded.addProperty("maxBackedgeTraversals",
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS);
        encoded.addProperty("onLimit", "CUT_PATH");
        JsonObject owner = new JsonObject();
        owner.add(LoopBoundPolicy.FIELD, encoded);

        LoopBoundPolicy decoded = LoopBoundPolicy.decode(owner);
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                decoded.maxBackedgeTraversals());
        assertTrue(decoded.declaredBounds().isEmpty());
    }

    /** One set of declarations has one identity, whatever order it arrived in. */
    @Test
    public void declarationOrderDoesNotChangeTheContract() {
        Map<String, Integer> forward = new LinkedHashMap<>();
        forward.put(LOOKUP, Integer.valueOf(60));
        forward.put(ROTATION, Integer.valueOf(4));
        Map<String, Integer> reversed = new LinkedHashMap<>();
        reversed.put(ROTATION, Integer.valueOf(4));
        reversed.put(LOOKUP, Integer.valueOf(60));

        assertEquals(LoopBoundPolicy.cfgBackedges(
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                        forward).identity(),
                LoopBoundPolicy.cfgBackedges(
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                        reversed).identity());
    }
}
