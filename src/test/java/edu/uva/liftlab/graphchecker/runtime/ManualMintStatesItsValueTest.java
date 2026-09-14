package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.SharedExpressionTable;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionIr;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import org.junit.Before;
import static java.util.Collections.singletonList;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.fail;

/**
 * The mint is the unit: what it publishes, and what it owes.
 *
 * <p>A configured-source mint publishes {@code recordedValue} on its
 * evidence row; a manual one published none, so a root the composer met
 * through a manual input had no recorded value to lower. On lane VM12 that
 * is {@code DelegationKey.expiryDate}, minted as
 * {@code M_J_field_REGION.aaa1cfd7...}, and RECORDED_ROOT_VALUE_UNSTATED was
 * the anchor's last refusal on a bug3 corpus whose twelve paths were
 * otherwise composed.</p>
 *
 * <p>The suppression rule is the configured source's too, and is what the
 * second case pins: a replay that wrote a model into the value read the
 * model back, and publishing that as "recorded" is how a counterfactual
 * becomes the recording.</p>
 */
public class ManualMintStatesItsValueTest {
    private static final String METHOD = "<a.B: void run()>";

    @After
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    /** A manual mint publishes the value it read. */
    @Test
    public void manualMintStatesItsValueRules() throws Exception {
        aManualMintStatesItsRecordedValue();
        aClockMintStatesTheRecordingsReadingAndItsOwn();
        aModelledMintStatesNoRecordedValue();
        anActivationThatNeverMintedThePhaseOwesNothing();
        anActivationThatMintedThePhaseStillOwesTheModel();
        anActivationThatReusedTheRootOwesNothing();
        DeclaredSymbolicRootMintTest t0 =
                new DeclaredSymbolicRootMintTest();
        t0.declaredSymbolicRootMintRules();
        ConfiguredSourceMintEpochTest t1 =
                new ConfiguredSourceMintEpochTest();
        try {
            t1.configuredSourceMintEpochRules();
        } finally {
            t1.releaseRegion();
        }
        RuntimeSourceAnchorReplacementTest t2 =
                new RuntimeSourceAnchorReplacementTest();
        t2.clearRegistry();
        try {
            t2.aReplacedAnchorStillNamesTheSourceItRegistered();
        } finally {
            t2.clearRegistryAfter();
        }
        ConcolicRegionRuntimeSourceAnchorTest t3 =
                new ConcolicRegionRuntimeSourceAnchorTest();
        try {
            t3.repeatedLoopPortIsDeliveredInMessageOrder();
        } finally {
            t3.clearMessageState();
        }
        DeclaredClockRootFlipReplayTest t4 =
                new DeclaredClockRootFlipReplayTest();
        t4.declaredClockRootFlipReplayRules();
        ExplicitFaultReplaySelectionTest t5 =
                new ExplicitFaultReplaySelectionTest();
        t5.twoFiringsInOneActivationSelectByRecordedOccurrence();
    }

    private void aManualMintStatesItsRecordedValue() throws Exception {
        JsonObject row = manualRow("1789358343989");

        assertEquals("MANUAL_SYMBOLIC_INPUT_OBSERVATION",
                row.get("kind").getAsString());
        assertTrue("the mint states what it read",
                row.has("recordedValue"));
        assertEquals("1789358343989",
                row.get("recordedValue").getAsString());
        assertEquals("J", row.get("javaType").getAsString());
        assertTrue(row.get("minted").getAsBoolean());
    }

    /**
     * A clock mint states both readings: the recording's and this one's.
     *
     * <p>A clock is the one root every execution genuinely reads
     * differently.  {@code recordedValue} is the seed's reading, because
     * that is the centre of the window the case's declared skew allows;
     * {@code observedValue} is this execution's own instant, which the
     * per-path window is centred on instead.  Publishing only one of them
     * makes one of those two windows unstatable.</p>
     */
    private void aClockMintStatesTheRecordingsReadingAndItsOwn()
            throws Exception {
        JsonObject row = manualRow(clockAction(), "1789358344655");

        assertEquals("<org.apache.hadoop.util.Timer: long now()>",
                row.get("declaredCallee").getAsString());
        assertEquals("the seed's reading, which the window is centred on",
                "1789358343989", row.get("recordedValue").getAsString());
        assertEquals("and this execution's own instant, beside it",
                "1789358344655", row.get("observedValue").getAsString());
    }

    /** A mint that returned a model value states no recorded value. */
    private void aModelledMintStatesNoRecordedValue() throws Exception {
        JsonObject row = manualRow("");

        assertFalse("a counterfactual is not a recording",
                row.has("recordedValue"));
        assertEquals("J", row.get("javaType").getAsString());
    }

    /**
     * A model for a mint site is owed by the activation that reaches it.
     *
     * <p>Lane VM12: six companions addressed at REGION.08ab84c9 carried the
     * serialNo model whose mint site is in {@code updateKeys()} --
     * REGION.aaa1cfd7, another member of the same linked group -- and were
     * refused at their terminal for not applying a model that was never
     * theirs to apply. The site is reached by whichever activation runs it;
     * one that did not reach it minted nothing to write the model into.</p>
     */
    private void anActivationThatNeverMintedThePhaseOwesNothing()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();

        assertFalse("nothing was minted for this phase here",
                owesModel(active, "SOURCE_PHASE.0b2b2a3d"));
    }

    /** An activation that minted it fresh is asked for the model. */
    private void anActivationThatMintedThePhaseStillOwesTheModel()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        mintRow(active, "SOURCE_PHASE.0b2b2a3d", false);

        assertTrue("this activation minted it, so the model is its own",
                owesModel(active, "SOURCE_PHASE.0b2b2a3d"));
    }

    /**
     * An activation that found the root already symbolic owes nothing.
     *
     * <p>Lane VM14's remaining two: companions addressed at
     * REGION.08ab84c9#2, the second activation of a site activation #1 had
     * already minted. A model is written into the value the mint is about
     * to symbolize; a reuse has nothing to write it into, and "one variable
     * per phase" is exactly why there is nothing to mint the second
     * time.</p>
     */
    private void anActivationThatReusedTheRootOwesNothing()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        mintRow(active, "SOURCE_PHASE.0b2b2a3d", true);

        assertFalse("a reuse is not a mint",
                owesModel(active, "SOURCE_PHASE.0b2b2a3d"));
    }

    private static void mintRow(ConcolicRegionRuntime.ActiveRegion active,
                                String phaseId, boolean reused)
            throws Exception {
        JsonObject mint = new JsonObject();
        mint.addProperty("sourcePhaseId", phaseId);
        mint.addProperty("reused", reused);
        Field rows = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("symbolizedRows");
        rows.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<JsonObject> published = (List<JsonObject>) rows.get(active);
        published.add(mint);
    }

    private static boolean owesModel(
            ConcolicRegionRuntime.ActiveRegion active, String phaseId)
            throws Exception {
        Method owes = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("owesConfiguredSourceModel",
                        String.class);
        owes.setAccessible(true);
        return (Boolean) owes.invoke(active, phaseId);
    }

    /** The published row, as the runtime writes it for one manual mint. */
    private static JsonObject manualRow(String recordedValue)
            throws Exception {
        return manualRow(symbolizeAction(), recordedValue);
    }

    private static JsonObject manualRow(Object action, String recordedValue)
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "J");
        expression.addProperty("_exp",
                "M_J_field_REGION.aaa1cfd7.in.f30dbb22_java/lang/Long");

        Method record = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("recordManualSymbolization",
                        action.getClass(), String.class, List.class,
                        String.class, com.google.gson.JsonElement.class,
                        boolean.class, boolean.class, String.class);
        record.setAccessible(true);
        record.invoke(active, action, "PORT.now", Collections.emptyList(),
                "<org.apache.hadoop.security.token.delegation.DelegationKey:"
                        + " long expiryDate>", expression, true, false,
                recordedValue);

        Field rows = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("symbolizedRows");
        rows.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<JsonObject> published = (List<JsonObject>) rows.get(active);
        assertEquals(1, published.size());
        return published.get(0);
    }

    /** The same action, as the plan carries a declared clock read. */
    private static Object clockAction() throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", "REGION.aaa1cfd7.in.f30dbb22");
        encoded.addProperty("actionDigest", "DIGEST.2");
        encoded.addProperty("cell", "<org.apache.hadoop.util.Timer: long "
                + "now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        encoded.addProperty("rootKind", "CALL_RETURN");
        encoded.addProperty("declaredCallee",
                "<org.apache.hadoop.util.Timer: long now()>");
        encoded.addProperty("siteId",
                "<a.B: void updateKeys()>#u12");
        encoded.addProperty("eventSeq", 4211L);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", "1789358343989");
        return action(encoded);
    }

    /** One frozen SYMBOLIC action, as the plan carries it. */
    private static Object symbolizeAction() throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", "PORT.now");
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("cell", "<org.apache.hadoop.util.Timer: long "
                + "now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        return action(encoded);
    }

    private static Object action(JsonObject encoded) throws Exception {
        Class<?> type = Class.forName(
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                        + "$SymbolizeAction");
        java.lang.reflect.Constructor<?> constructor =
                type.getDeclaredConstructor(JsonObject.class);
        constructor.setAccessible(true);
        return constructor.newInstance(encoded);
    }

    /** One live region, as BranchDecisionRecordingTest opens one. */
    private static ConcolicRegionRuntime.ActiveRegion region()
            throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.SEED.manual");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.aaa1cfd7");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "hdfs-17899/nn0#epoch0");
        encoded.addProperty("occurrenceId",
                "hdfs-17899/nn0#epoch0/region/REGION.aaa1cfd7#1");
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", METHOD);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "hdfs-17899/nn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        ConcolicTaskPlan.RuntimeTask task =
                new ConcolicTaskPlan.RuntimeTask(
                        ExecutionTask.decode(encoded));

        java.lang.reflect.Constructor<?> constructor =
                ConcolicRegionRuntime.ActiveRegion.class
                        .getDeclaredConstructors()[0];
        constructor.setAccessible(true);
        Object[] arguments =
                new Object[constructor.getParameterTypes().length];
        Class<?>[] types = constructor.getParameterTypes();
        for (int index = 0; index < types.length; index++) {
            if (types[index] == ConcolicTaskPlan.RuntimeTask.class) {
                arguments[index] = task;
            } else if (types[index] == long.class) {
                arguments[index] = 900001L;
            } else if (types[index] == int.class) {
                arguments[index] = 1;
            } else if (types[index] == boolean.class) {
                arguments[index] = false;
            } else {
                arguments[index] = null;
            }
        }
        return (ConcolicRegionRuntime.ActiveRegion)
                constructor.newInstance(arguments);
    }

    /**
     * A field the experiment declared must mint, even over a constant.
     *
     * <p>Once a shared-state carrier is installed, every later read of a field
     * arrives wrapped in a {@code ReadFrom} -- including a field only ever
     * written from constants.  The automatic rule reads that wrapper as "already
     * propagated" and skips the mint, which is why declaring a field symbolic
     * used to leave it concrete.  A declared primitive source asks the strict
     * question instead: is anything symbolic actually inside the tree?</p>
     */
    static final class DeclaredSymbolicRootMintTest {

        public void declaredSymbolicRootMintRules() throws Exception {
            aDeclaredPrimitiveSourceMintsOverAConstant();
            theHookStillDefersToARealUpstreamSymbol();
            aMintCarriesTheValueTheFieldHeld();
            aMintOverAModelAssignmentStatesNoRecordedValue();
            aTrackedCarrierIsNotMintEligible();
        }

        private void aDeclaredPrimitiveSourceMintsOverAConstant() {
            assertFalse("nothing is retained, so the caller mints",
                    ConcolicRegionRuntime.carriesInputAuthority(
                            action("int", true), readFromConstant()));
        }

        private void theHookStillDefersToARealUpstreamSymbol() {
            assertTrue("a root minted upstream flows through this read",
                    ConcolicRegionRuntime.configuredSourceCarriesAuthority(
                            readFromSymbol()));
        }

        private static final String SERIAL_NO_PHASE =
                "SOURCE_PHASE.b6cff494-49b4-3843-afe6-6bc8564e0315";
        private static final String SERIAL_NO_SOURCE = "HDFS.BLOCK_KEY.SERIAL_NO";
        private static final String SERIAL_NO_OCCURRENCE = "hdfs-17899/nn0#epoch0"
                + "/region/REGION.aaa1cfd7-659b-3340-8d12-c81925e1de94#1#a1";
        private static final String SERIAL_NO_FIELD = "<org.apache.hadoop.hdfs"
                + ".security.token.block.BlockTokenSecretManager: int serialNo>";

        /**
         * The concrete value the field held travels with the mint.
         *
         * <p>It exists only here: a configured source has no port and no
         * {@code symbolize} row, so the plan states nothing about it, and
         * dropping it at the mint leaves every downstream reader to default the
         * polarity. HDFS-17960's {@code snapshotDeletionOrdered} is recorded
         * {@code false} on the epoch-1 NameNode, and the default of {@code true}
         * reported a witness that reproduces the recorded failure as a flip of
         * it.</p>
         */
        private void aMintCarriesTheValueTheFieldHeld() {
            String label = SymbolicSourceEvidence.engineLabelForPhase(
                    ORDERED_PHASE, ORDERED_SOURCE);
            String raw = "M_Z_field_" + label + "_org/apache/hadoop/hdfs/server/"
                    + "namenode/snapshot/SnapshotManager";
            JsonObject symbol = new JsonObject();
            symbol.addProperty("_type", "SymbolExpression");
            symbol.addProperty("_java_type", "Z");
            symbol.addProperty("_exp", raw);

            JsonObject row = SymbolicSourceEvidence.event(ORDERED_PHASE,
                    ORDERED_SOURCE, SERIAL_NO_OCCURRENCE, ORDERED_FIELD, symbol,
                    1, false, "sym__ordered__1", "false");

            assertEquals("false", SymbolicSourceEvidence.recordedValueOf(row));
            assertEquals("false", row.get(SymbolicSourceEvidence.RECORDED_VALUE)
                    .getAsString());
        }

        /**
         * A replay that overwrote the field before reading it states none.
         *
         * <p>The model assignment is written into the field before the mint
         * reads it back, so that activation observed the model's value. Calling
         * it "recorded" would publish a counterfactual as the recording, which
         * is the one way this row can be worse than absent.</p>
         */
        private void aMintOverAModelAssignmentStatesNoRecordedValue() {
            String label = SymbolicSourceEvidence.engineLabelForPhase(
                    ORDERED_PHASE, ORDERED_SOURCE);
            String raw = "M_Z_field_" + label + "_org/apache/hadoop/hdfs/server/"
                    + "namenode/snapshot/SnapshotManager";
            JsonObject symbol = new JsonObject();
            symbol.addProperty("_type", "SymbolExpression");
            symbol.addProperty("_java_type", "Z");
            symbol.addProperty("_exp", raw);

            JsonObject row = SymbolicSourceEvidence.event(ORDERED_PHASE,
                    ORDERED_SOURCE, SERIAL_NO_OCCURRENCE, ORDERED_FIELD, symbol,
                    1, false, "sym__ordered__1", null);

            assertFalse(row.has(SymbolicSourceEvidence.RECORDED_VALUE));
            assertEquals("", SymbolicSourceEvidence.recordedValueOf(row));
        }

        private static final String ORDERED_PHASE =
                "SOURCE_PHASE.f2395415-6c7d-3e1d-aa84-c9385b295a8c";
        private static final String ORDERED_SOURCE =
                "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED";
        private static final String ORDERED_FIELD = "<org.apache.hadoop.hdfs"
                + ".server.namenode.snapshot.SnapshotManager:"
                + " boolean snapshotDeletionOrdered>";

        private static JsonObject binary(String op, JsonObject left,
                                         JsonObject right) {
            JsonObject node = new JsonObject();
            node.addProperty("_type", "BinaryExpression");
            node.addProperty("_op", op);
            node.add("_left", left);
            node.add("_right", right);
            return node;
        }

        /**
         * A tracked carrier the plan did not make mint-eligible.
         *
         * <p>The scheduler now symbolizes every carrier so the VM keeps
         * publishing its candidates, and reserves the mint for the three
         * declaring authorities.  {@code mintEligible} is how that second
         * verdict reaches the replay, and it must default to the unnarrowed
         * behaviour when a plan row predates the field.</p>
         */
        private void aTrackedCarrierIsNotMintEligible() {
            JsonObject json = new JsonObject();
            json.addProperty("symbol", "port.value");
            json.addProperty("javaType", "int");
            json.addProperty("mintEligible", false);
            assertFalse(new ConcolicRegionRuntime.SymbolizeAction(json)
                    .mintEligible);
        }

        private static ConcolicRegionRuntime.SymbolizeAction action(
                String javaType, boolean declared) {
            JsonObject json = new JsonObject();
            json.addProperty("symbol", "port.serialNo");
            json.addProperty("javaType", javaType);
            json.addProperty("location", "RECEIVER_FIELD");
            json.addProperty("accessFieldSignature",
                    "<org.apache.hadoop.hdfs.security.token.block"
                            + ".BlockTokenSecretManager: int serialNo>");
            if (declared) {
                json.addProperty(InputActionCatalog.DECLARED_SYMBOLIC_ROOT, true);
                json.addProperty("mintEligible", true);
            }
            return new ConcolicRegionRuntime.SymbolizeAction(json);
        }

        private static JsonObject constant() {
            JsonObject value = new JsonObject();
            value.addProperty("_type", "ConstExpr");
            value.addProperty("_exp", "Y_I_1771181829");
            return value;
        }

        /** The shape a carrier gives a field written only from constants. */
        private static JsonObject readFromConstant() {
            return readFrom(constant());
        }

        private static JsonObject readFromSymbol() {
            JsonObject symbol = new JsonObject();
            symbol.addProperty("_type", "SymbolExpression");
            symbol.addProperty("_exp", "M_I_REGION.aaa1cfd7");
            symbol.addProperty("_java_type", "int");
            return readFrom(symbol);
        }

        private static JsonObject readFrom(JsonObject candidateExpression) {
            JsonObject candidate = new JsonObject();
            candidate.addProperty("versionKind", "INITIAL");
            candidate.add("expression", candidateExpression);
            JsonArray candidates = new JsonArray();
            candidates.add(candidate);
            JsonObject read = new JsonObject();
            read.addProperty("_type", "ReadFromExpression");
            read.addProperty("authority", "VM_GUARDED_READ_FROM_V1");
            read.add("candidates", candidates);
            return read;
        }
    }


    /**
     * A model is applied only at a mint this run can place.
     *
     * <p>An occurrence is (node, epoch, region, k-th activation).  A configured
     * source names one mint SITE, and the site is reached once per node
     * lifecycle, so the epoch is the whole of what tells two mints of that site
     * apart.  On hdfs-17960 {@code root=false} landed on the epoch-0 mint --
     * the one the recording made before the NameNode restart -- and rewrote a
     * value the solver had said nothing about.</p>
     *
     * <p>Root admission admits an activation nothing attributed, because absence
     * of evidence is not evidence of another occurrence.  A model is different in
     * kind: it rewrites the recorded execution, so it demands positive evidence
     * and an unattributed mint keeps the recorded value with a named gap.</p>
     */
    static final class ConfiguredSourceMintEpochTest {
        private static final String NODE = "hdfs/nn0";
        private static final String SOURCE_ID = "CFG.ORDERED";
        private static final String FIELD =
                "<a.Manager: boolean snapshotDeletionOrdered>";
        private static final String METHOD =
                "<a.Manager: boolean isSnapshotDeletionOrdered()>";
        private static final String CALLEE =
                "<a.Manager: boolean isSnapshotDeletionOrdered()>";
        private static final int UNIT = 1;
        private static final String REGION = "REGION.9492ec77";
        private static final String PLANNED =
                NODE + "#epoch1/region/" + REGION + "#1";

        private long token;
        private String occurrenceId = PLANNED;

        public void releaseRegion() {
            ConcolicRegionRuntime.ACTIVE.remove(token);
            RuntimeTraceContext.resetForTests();
        }

        /**
         * The mint before the restart is refused; the one after it is applied.
         *
         * <p>Same run, same site, same model: what changes is whether the
         * registry can place the mint in the epoch the plan addresses.</p>
         */
        public void configuredSourceMintEpochRules() throws Exception {
            aMintIsModelledOnlyInTheEpochThePlanAddresses();
            anUnattributedMintRefusesTheModelWithAGap();
            theRefusalIsPublishedAsAnUnresolvedInput();
            anEpochlessAddressIsUnaffected();
            everyOccurrenceOfOneSiteAnswersOneValuation();
        }

        private void aMintIsModelledOnlyInTheEpochThePlanAddresses()
                throws Exception {
            ConcolicRegionRuntime.ActiveRegion active = region();
            Object manager = new Object();

            // Epoch 0 is registered and the workload has not restarted yet: the
            // registry places this mint at epoch 0, which is not the address.
            RuntimeTraceContext.registerSource(manager,
                    new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));
            assertNull("a mint of another epoch is not modelled",
                    assignment(active, manager));
            assertEquals("EPOCH_UNMATCHED", lastGapKind(active));

            // The restart advances the same logical source; the mint that
            // follows it is the one the plan addresses.
            RuntimeTraceContext.restartSource(manager,
                    new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));
            assertNotNull("the epoch-1 mint is modelled",
                    assignment(active, manager));
        }

        /** A mint the registry cannot place keeps the value the recording made. */
        private void anUnattributedMintRefusesTheModelWithAGap() throws Exception {
            ConcolicRegionRuntime.ActiveRegion active = region();

            assertNull("nothing places this mint, so nothing rewrites it",
                    assignment(active, new Object()));

            assertEquals("MINT_UNATTRIBUTED", lastGapKind(active));
            assertTrue(lastGapDetail(active),
                    lastGapDetail(active).contains("attributes this mint to no "
                            + "node"));
            assertTrue(lastGapDetail(active),
                    lastGapDetail(active).contains("recorded value stands"));
        }

        /** The refusal is diagnostic: the activation says it, not just skips. */
        private void theRefusalIsPublishedAsAnUnresolvedInput() throws Exception {
            ConcolicRegionRuntime.ActiveRegion active = region();

            assignment(active, new Object());

            assertTrue(unresolved(active).toString(),
                    unresolved(active).toString().contains(
                            "CONFIGURED_SOURCE_PHASE_MINT_UNATTRIBUTED"));
        }

        /** An address that names no epoch is not asked the question at all. */
        private void anEpochlessAddressIsUnaffected() throws Exception {
            ConcolicRegionRuntime.ActiveRegion active =
                    region("workload/unregistered",
                            "workload/unregistered/region/" + REGION + "#1");

            assertNotNull("nothing to place, nothing to refuse",
                    assignment(active, new Object()));
        }


        /**
         * One site is one variable: every occurrence that reaches it is modelled.
         *
         * <p>Lane BG's shape.  {@code SnapshotManager.isSnapshotDeletionOrdered()
         * #u1} is reached by six regions, twice each; the solver flipped it to
         * {@code false} and the replay applied that at exactly one of the twelve
         * identities the site had -- {@code SOURCE_PHASE.f2395415…}, occurrence
         * {@code REGION.9492ec77…#1} -- so every other execution kept the
         * recorded {@code true}, the target region ran under the recorded root
         * and published {@code targetReach.outcome:false}, and COMPOSE refused
         * both target occurrences with TARGET_NOT_REACHED.</p>
         *
         * <p>A configured source is declared by site, so it is one variable per
         * replay and a flip of it is a flip everywhere it is read.</p>
         */
        private void everyOccurrenceOfOneSiteAnswersOneValuation()
                throws Exception {
            RuntimeTraceContext.resetForTests();
            Object manager = new Object();
            RuntimeTraceContext.registerSource(manager,
                    new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

            String first = NODE + "#epoch1/region/" + REGION + "#1";
            String second = NODE + "#epoch1/region/" + REGION + "#2";
            assertEquals("one site, one variable, whatever reached it",
                    phaseId(first), phaseId(second));

            ConcolicRegionRuntime.ActiveRegion one =
                    region(NODE + "#epoch1", first);
            assertNotNull("the first occurrence is modelled",
                    assignment(one, manager));

            ConcolicRegionRuntime.ActiveRegion two =
                    region(NODE + "#epoch1", second);
            assertNotNull("and so is the second, on the same valuation",
                    assignment(two, manager));
        }

        // ---------- harness ----------

        private ConcolicRegionRuntime.ActiveRegion region() throws Exception {
            return region(NODE + "#epoch1", PLANNED);
        }

        private ConcolicRegionRuntime.ActiveRegion region(String sourceKey,
                                                          String occurrenceId)
                throws Exception {
            this.occurrenceId = occurrenceId;
            ConcolicTaskPlan.RuntimeTask runtime =
                    new ConcolicTaskPlan.RuntimeTask(
                            ExecutionTask.decode(task(sourceKey, occurrenceId)));
            token = 970000L + occurrenceId.hashCode() % 1000L;
            ConcolicRegionRuntime.ActiveRegion active =
                    new ConcolicRegionRuntime.ActiveRegion(token, runtime, null,
                            Thread.currentThread(), false);
            ConcolicRegionRuntime.ACTIVE.put(token, active);
            return active;
        }

        private Object assignment(
                ConcolicRegionRuntime.ActiveRegion active, Object mintOwner)
                throws Exception {
            Method method = active.getClass().getDeclaredMethod(
                    "configuredSourceAssignment", String.class, String.class,
                    String.class, Object.class);
            method.setAccessible(true);
            return method.invoke(active, phaseId(occurrenceId),
                    SOURCE_ID, FIELD, mintOwner);
        }

        @SuppressWarnings("unchecked")
        private static JsonObject lastGap(
                ConcolicRegionRuntime.ActiveRegion active) throws Exception {
            Field field = active.getClass().getDeclaredField(
                    "configuredSourcePhaseGaps");
            field.setAccessible(true);
            List<JsonObject> gaps = (List<JsonObject>) field.get(active);
            return gaps.isEmpty() ? new JsonObject()
                    : gaps.get(gaps.size() - 1);
        }

        private static String lastGapKind(
                ConcolicRegionRuntime.ActiveRegion active) throws Exception {
            return lastGap(active).has("gapKind")
                    ? lastGap(active).get("gapKind").getAsString() : "";
        }

        private static String lastGapDetail(
                ConcolicRegionRuntime.ActiveRegion active) throws Exception {
            return lastGap(active).has("detail")
                    ? lastGap(active).get("detail").getAsString() : "";
        }

        @SuppressWarnings("unchecked")
        private static Collection<String> unresolved(
                ConcolicRegionRuntime.ActiveRegion active) throws Exception {
            Field field = active.getClass().getDeclaredField("unresolved");
            field.setAccessible(true);
            return (Collection<String>) field.get(active);
        }

        private static String phaseId(String occurrenceId) {
            return ConfiguredSourcePhaseContract.phaseId(SOURCE_ID,
                    edu.uva.liftlab.graphchecker.contract.SiteId.of(METHOD, UNIT),
                    ConfiguredSourcePhaseContract.Phase.PUBLISH);
        }

        private static JsonObject task(String sourceKey, String occurrenceId) {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("taskId", "TASK.1");
            encoded.addProperty("goalId", "GOAL.1");
            encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
            encoded.addProperty("regionId", REGION);
            encoded.addProperty("relationKey", "REL.1");
            encoded.addProperty("sourceKey", sourceKey);
            encoded.addProperty("occurrenceId", occurrenceId);
            encoded.addProperty("rootMethod", "<a.B: void run()>");
            encoded.addProperty("instrumentationSelector", "sel");
            JsonObject admission = new JsonObject();
            admission.addProperty("state", "EXECUTABLE");
            encoded.add("admission", admission);
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "GLOBAL_INVOCATION");
            selector.addProperty("invocationOrdinal", 1);
            JsonObject anchor = new JsonObject();
            anchor.addProperty("sourceKey", sourceKey);
            anchor.addProperty("kind", "REGISTERED_SOURCE");
            selector.add("causalAnchor", anchor);
            encoded.add("rootSelector", selector);
            encoded.add("branches", new JsonArray());
            encoded.add("inputActions", new JsonArray());
            JsonObject loopBound = new JsonObject();
            loopBound.addProperty("schemaVersion", 1);
            encoded.add("loopBound", loopBound);

            JsonObject declaration = ConfiguredSourcePhaseContract.declaration(
                    ConfiguredSourcePhaseContract.Phase.PUBLISH, SOURCE_ID,
                    FIELD, METHOD, UNIT);
            JsonArray declarations = new JsonArray();
            declarations.add(declaration);
            JsonArray phases = new JsonArray();
            phases.add(ConfiguredSourcePhaseContract.occurrence(
                    ConfiguredSourcePhaseContract.declarationsOf(declarations)
                            .get(0),
                    occurrenceId, 1, 11L, 7L, 3L, CALLEE, Arrays.asList(7L, 5L)));
            encoded.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);

            JsonObject model = new JsonObject();
            model.addProperty("modelAssignmentKey", "MODEL.1");
            model.addProperty("inputSymbol",
                    "SOURCE_PHASE:" + phaseId(occurrenceId));
            model.addProperty("valueType", "BOOLEAN");
            model.addProperty("value", "false");
            model.addProperty("configuredSourcePhaseId",
                    phaseId(occurrenceId));
            model.addProperty("configuredSourceId", SOURCE_ID);
            model.addProperty("configuredSourceFieldSignature", FIELD);
            JsonArray models = new JsonArray();
            models.add(model);
            encoded.add("modelAssignments", models);
            return encoded;
        }
    }


    /**
     * An application may replace the anchor object it registered with a
     * value-equal successor.  HDFS does exactly that: {@code DataNode.id} is
     * reassigned to a fresh {@code DatanodeRegistration} on every DataNode
     * re-registration, so a workload that registered {@code getDatanodeId()}
     * before a block-report lease expired passes a different object afterwards.
     */
    static final class RuntimeSourceAnchorReplacementTest {
        private static final SourceRef DN0 =
                new SourceRef("CLUSTER_NODE", "DATANODE", "hdfs-11741/dn0", 0L);
        private static final SourceRef DN1 =
                new SourceRef("CLUSTER_NODE", "DATANODE", "hdfs-11741/dn1", 0L);

        public void clearRegistry() {
            RuntimeTraceContext.resetForTests();
        }

        public void clearRegistryAfter() {
            RuntimeTraceContext.resetForTests();
        }

        public void aReplacedAnchorStillNamesTheSourceItRegistered() {
            NodeAnchor registered = new NodeAnchor("127.0.0.1:50010", "uuid-0");
            RuntimeTraceContext.registerSource(registered, DN0);

            NodeAnchor reregistered = new NodeAnchor("127.0.0.1:50010", "uuid-0");
            long request = RuntimeTraceContext.beginRequest(
                    reregistered, "refresh-block-keys");
            assertEquals("hdfs-11741/dn0#epoch0/request/refresh-block-keys#1",
                    RuntimeTraceContext.current().requestKey);
            assertEquals(DN0, RuntimeTraceContext.current().source);
            RuntimeTraceContext.endRequest(request);

            // The successor is the identity every later lookup carries, so the
            // rebind happens once rather than on each request.
            assertSame(DN0, RuntimeTraceContext.sourceFor(reregistered));
        }

        /** A DatanodeID-shaped anchor: equal by transfer address and uuid. */
        private static final class NodeAnchor {
            private final String address;
            private final String uuid;

            NodeAnchor(String address, String uuid) {
                this.address = address;
                this.uuid = uuid;
            }

            @Override
            public boolean equals(Object other) {
                if (this == other) return true;
                if (!(other instanceof NodeAnchor)) return false;
                NodeAnchor value = (NodeAnchor) other;
                return address.equals(value.address) && uuid.equals(value.uuid);
            }

            @Override
            public int hashCode() {
                return address.hashCode() * 31 + uuid.hashCode();
            }
        }

        /** Value equality too coarse to separate the sources registered on it. */
        private static final class AddressOnlyAnchor {
            private final String address;

            AddressOnlyAnchor(String address) {
                this.address = address;
            }

            @Override
            public boolean equals(Object other) {
                return other instanceof AddressOnlyAnchor
                        && address.equals(((AddressOnlyAnchor) other).address);
            }

            @Override
            public int hashCode() {
                return address.hashCode();
            }
        }
    }


    /** Source evidence used to replay one exact region occurrence. */
    static final class ConcolicRegionRuntimeSourceAnchorTest {
        private static final String EXPECTED = "dn0#epoch0";
        private static final SourceRef DN0_REPLAY =
                new SourceRef("DATANODE", "dn", "dn0", 7L);
        private static final SourceRef NN0_REPLAY =
                new SourceRef("NAMENODE", "nn", "nn0", 7L);

        public void clearMessageState() {
            SymbolicMessageEnvelope.clear();
        }

        public void repeatedLoopPortIsDeliveredInMessageOrder() {
            assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                    "producer", "producer#1",
                    singletonList("consumer#1")));
            assertTrue(SymbolicMessageEnvelope.stage("block-key", 42L,
                    "producer", "producer#2",
                    singletonList("consumer#1")));

            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());
            assertEquals(41L,
                    SymbolicMessageEnvelope.take("block-key").handle());
            assertEquals(42L,
                    SymbolicMessageEnvelope.take("block-key").handle());
            assertFalse(SymbolicMessageEnvelope.take("block-key").present());
        }

        /** One address of a region on one node, at the given activation. */
        private static edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
                planned(int ordinal) {
            return edu.uva.liftlab.graphchecker.contract.OccurrenceAddress.of(
                    "hdfs-17899/target-dn#epoch0", "REGION.r", ordinal);
        }

        private static JsonObject variable(String name) {
            JsonObject result = new JsonObject();
            result.addProperty("_type", "SymbolExpression");
            result.addProperty("_java_type", "I");
            result.addProperty("_exp", name);
            return result;
        }

        private static JsonObject integer(int value) {
            JsonObject result = new JsonObject();
            result.addProperty("_type", "ConstExpr");
            result.addProperty("_java_type", "I");
            result.addProperty("_exp", "Y_I_" + value);
            return result;
        }

        private static JsonObject binary(JsonObject left, String operator,
                                         JsonObject right) {
            JsonObject result = new JsonObject();
            result.addProperty("_type", "BinaryExpression");
            result.addProperty("_java_type", "Z");
            result.addProperty("_op", operator);
            result.add("_left", left);
            result.add("_right", right);
            return result;
        }
    }


    /**
     * A declared wall-clock root is replay-injectable, and its model is a skew.
     *
     * <p>EXPLORE could flip a clock-dependent branch on paper and never on the
     * VM.  The solver answered {@code SAT_MODEL_READY} and the plan carried a
     * model assignment for the {@code Timer.now()} root, so the value did reach
     * the replay -- but as an <em>absolute</em> millisecond stamp taken from the
     * seed recording's own constants.  A flip replay is a fresh JVM that mints
     * its expiries minutes later, so that stamp lands in the past, the compared
     * branch keeps its recorded outcome, and the linked replay is refused:
     * {@code REPLAY_PREFIX_UNMATCHED -- still waiting for
     * removeExpiredKeys()#u15#1 (the flipped source decision)}.  With no flipped
     * case recorded, the composition keeps asserting
     * the recorded polarity of that branch for every key and no clock window
     * admits the removal.</p>
     *
     * <p>The numbers below are the ones the laneU corpus actually carries.</p>
     */
    static final class DeclaredClockRootFlipReplayTest {

        /** hdfs-17897 nn0: what {@code Timer.now()} returned in the recording. */
        private static final long RECORDED_CLOCK = 1789284077460L;
        /** The model the flip solver published: the key's expiry, plus one. */
        private static final long MODEL_CLOCK = 1789284356381L;
        /** The same key's recorded expiry, which the model is one millisecond
         *  past. */
        private static final long RECORDED_EXPIRY = 1789284356380L;

        /** The replay JVM started 846 s after the recording. */
        private static final long LIVE_CLOCK = 1789284923800L;
        /** So it minted its own copy of that key 846 s later too. */
        private static final long LIVE_EXPIRY =
                RECORDED_EXPIRY + (LIVE_CLOCK - RECORDED_CLOCK);

        private static final String TIMER_NOW =
                "<org.apache.hadoop.util.Timer: long now()>";

        /** Every other declared root replays its model value verbatim. */
        public void declaredClockRootFlipReplayRules() throws Exception {
            anIdentityRootReplaysTheModelValueVerbatim();
            aReplayThatReproducesItsRecordingReadsTheModelValue();
            theFlipReplayTakesTheFlippedBranch();
        }

        private void anIdentityRootReplaysTheModelValueVerbatim() {
            JsonObject row = clockRow();
            row.addProperty("declaredCallee",
                    "<org.apache.hadoop.hdfs.security.token.block.BlockKey: "
                            + "int getKeyId()>");
            ConcolicRegionRuntime.SymbolizeAction action =
                    new ConcolicRegionRuntime.SymbolizeAction(row);
            assertFalse(action.declaresWallClockRead());
            assertEquals(Long.toString(MODEL_CLOCK),
                    ConcolicRegionRuntime.replayModelLiteral(action,
                            model(MODEL_CLOCK), LIVE_CLOCK));
        }

        /**
         * A replay that reproduces its recording reads exactly the model value,
         * so nothing changes for a same-timeline replay.
         */
        private void aReplayThatReproducesItsRecordingReadsTheModelValue() {
            assertEquals(Long.toString(MODEL_CLOCK),
                    ConcolicRegionRuntime.replayModelLiteral(clockAction(),
                            model(MODEL_CLOCK), RECORDED_CLOCK));
        }

        /**
         * The regression this fixes, stated as arithmetic: the model value the
         * solver published cannot expire this run's key, and the offset it
         * actually chose can.
         */
        private void theFlipReplayTakesTheFlippedBranch() {
            assertFalse("the stamp lands 567 s before this run's expiry",
                    RECORDED_EXPIRY + (LIVE_CLOCK - RECORDED_CLOCK)
                            < MODEL_CLOCK);

            String replayed = ConcolicRegionRuntime.replayModelLiteral(
                    clockAction(), model(MODEL_CLOCK), LIVE_CLOCK);
            long injected = Long.parseLong(replayed);

            assertEquals("this run's clock, moved by the offset the model chose",
                    LIVE_CLOCK + (MODEL_CLOCK - RECORDED_CLOCK), injected);
            assertTrue("expiryDate < now, which is the decision EXPLORE asked for",
                    LIVE_EXPIRY < injected);
            assertTrue("and it stays ahead of this run's own clock",
                    injected > LIVE_CLOCK);
        }

        private static ConcolicRegionRuntime.SymbolizeAction clockAction() {
            return new ConcolicRegionRuntime.SymbolizeAction(clockRow());
        }

        /**
         * The shape of the laneU plan row for
         * {@code REGION.aaa1cfd7...in.1cdfc335}: the {@code Timer.now()} return
         * that {@code removeExpiredKeys()} compares every key's expiry against.
         */
        private static JsonObject clockRow() {
            JsonObject row = new JsonObject();
            row.addProperty("symbol", "REGION.aaa1cfd7.in.1cdfc335");
            row.addProperty("location", "CALL_RETURN");
            row.addProperty("bindingMode", "LOCAL_DEFINITION");
            row.addProperty("cell", TIMER_NOW + ".return");
            row.addProperty("declaredCallee", TIMER_NOW);
            row.addProperty("javaType", "long");
            row.addProperty("method",
                    "<org.apache.hadoop.hdfs.security.token.block."
                            + "BlockTokenSecretManager: void removeExpiredKeys()>");
            row.addProperty("local", "$l0");
            row.addProperty("unitIndex", 2);
            row.addProperty("mode", "SYMBOLIC");
            row.addProperty("declaredSymbolicRoot", true);
            row.addProperty("observed", true);
            row.addProperty("primitiveValue", Long.toString(RECORDED_CLOCK));
            row.addProperty("replayOccurrence", 1);
            return row;
        }

        private static ConcolicRegionRuntime.ModelAssignment model(long value) {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("engineSymbol", "M_J_field_REGION.aaa1cfd7"
                    + ".in.1cdfc335.occ.0a591271_java/lang/Long");
            encoded.addProperty("inputSymbol", "REGION.aaa1cfd7.in.1cdfc335");
            encoded.addProperty("valueType", "INT");
            encoded.addProperty("value", Long.toString(value));
            return new ConcolicRegionRuntime.ModelAssignment(encoded);
        }
    }


    /**
     * Replay-side selection of a workload-declared fault marker.
     *
     * <p>Two defects met here.  The gate read {@code symbolicDemand}, which no
     * producer ever stamps with the fault classification, so every marker
     * resolved to nothing and {@code Debug.makeSymbolicBoolean} returned a
     * concrete {@code false} on every replay.  And the match ignored the
     * recorded {@code replayOccurrence}, so two in-scope requests inside one
     * activation collapsed into one ambiguous name.</p>
     */
    static final class ExplicitFaultReplaySelectionTest {

        private static final String NAME = "hadoopIpcRequestFails";

        /** Two firings of one marker inside one activation stay two roots. */
        public void twoFiringsInOneActivationSelectByRecordedOccurrence() {
            ConcolicRegionRuntime.SymbolizeAction first = action(
                    RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT,
                    NAME, 1);
            ConcolicRegionRuntime.SymbolizeAction second = action(
                    RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT,
                    NAME, 2);
            List<ConcolicRegionRuntime.SymbolizeAction> both =
                    Arrays.asList(first, second);

            assertSame(first, only(ConcolicRegionRuntime
                    .explicitFaultCandidates(both, NAME, 1)));
            assertSame(second, only(ConcolicRegionRuntime
                    .explicitFaultCandidates(both, NAME, 2)));
            assertTrue("a firing the recording never saw models nothing",
                    ConcolicRegionRuntime.explicitFaultCandidates(both, NAME, 3)
                            .isEmpty());
            assertTrue(ConcolicRegionRuntime.explicitFaultCandidates(
                    both, "otherMarker", 1).isEmpty());

            // Without the ordinal both rows answer to the name, which is the
            // ambiguity the caller refuses on.
            List<ConcolicRegionRuntime.SymbolizeAction> unordinaled =
                    Arrays.asList(
                            action(RuntimeSelectedRegionFinalizer
                                    .EXPLICIT_SYMBOLIC_FAULT, NAME, -1),
                            action(RuntimeSelectedRegionFinalizer
                                    .EXPLICIT_SYMBOLIC_FAULT, NAME, -1));
            assertEquals(2, ConcolicRegionRuntime.explicitFaultCandidates(
                    unordinaled, NAME, 1).size());
        }

        private static ConcolicRegionRuntime.SymbolizeAction only(
                List<ConcolicRegionRuntime.SymbolizeAction> candidates) {
            assertEquals(1, candidates.size());
            return candidates.get(0);
        }

        private static ConcolicRegionRuntime.SymbolizeAction action(
                String sourceKind, String name, int replayOccurrence) {
            JsonObject json = json(name, replayOccurrence);
            json.addProperty("sourceKind", sourceKind);
            return new ConcolicRegionRuntime.SymbolizeAction(json);
        }

        private static JsonObject json(String name, int replayOccurrence) {
            JsonObject json = new JsonObject();
            json.addProperty("symbol", "REGION.ipc.in." + name + "."
                    + replayOccurrence);
            json.addProperty("javaType", "boolean");
            json.addProperty("location", "CALL_RETURN");
            json.addProperty("rootKind", "ACTIVATION_LOCAL");
            json.addProperty("symbolicName", name);
            if (replayOccurrence >= 1) {
                json.addProperty("replayOccurrence", replayOccurrence);
            }
            return json;
        }
    }

}
