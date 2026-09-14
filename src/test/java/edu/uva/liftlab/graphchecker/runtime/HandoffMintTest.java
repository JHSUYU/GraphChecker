package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import com.google.gson.JsonArray;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.After;
import static org.junit.Assert.fail;

/**
 * The handoff mint: one variable at one occurrence, answered like a source.
 *
 * <p>At a wire attach the consumer's element stops denoting the producer's
 * whole expression and starts denoting a fresh variable v_H. The producer's
 * expression travels on the row as one member of H's family, so the two sides
 * can be explored independently and joined offline at H instead of being
 * re-run in combination.</p>
 *
 * <p>Three things have to hold for that to work, and they are what this
 * pins: H is the same string in every replay, the row states v_H and what it
 * delivered, and an obligation assignment for H answers the mint through the
 * configured-source mechanism rather than a second one. The attach itself
 * runs inside the custom JDK -- {@code ConcolicVmBroker} binds to
 * {@code java.lang.System} entry points that exist only there -- so what is
 * exercised here is every seam on this side of that call.</p>
 */
public class HandoffMintTest {
    private static final String PORT =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70.req"
                    + ".data-encryption-key-id";
    private static final String CONSUMER =
            "hdfs-17899/target-dn#epoch0/region/REGION.53092d3e#1";
    private static final String ELEMENT =
            "<org.apache.hadoop.ipc.Client$Call: int id>";

    /** H is (port, consumer address, k, element) -- and no event id. */
    @Test
    public void handoffMintRules() throws Exception {
        theHandoffOccurrenceIsTheSameStringInEveryReplay();
        theRowStatesTheHandoffVariableAndItsDeliveredValue();
        aRowMissingAnyOfThemIsRefused();
        anAssignmentForTheHandoffAnswersTheMint();
        aDeliveryWithNoElementStillMintsTheConsumersVariable();
        anAssignmentAnswersAMintWithNoElement();
        aPlanAnsweringAHandoffThisTaskReceivesLoads();
        aPlanAnsweringAHandoffThisTaskCannotIsRefused();
        HandoffLeavesOfOneAttachTest t0 =
                new HandoffLeavesOfOneAttachTest();
        t0.handoffLeavesOfOneAttachRules();
        ExportPortConsumerOccurrencesTest t1 =
                new ExportPortConsumerOccurrencesTest();
        try {
            t1.exportPortConsumerOccurrencesRules();
        } finally {
            t1.clearEnvelope();
        }
        OneCaptureSiteOneConsumerTest t2 =
                new OneCaptureSiteOneConsumerTest();
        t2.oneCaptureSiteOneConsumerRules();
        SymbolicMessageEnvelopeTest t3 =
                new SymbolicMessageEnvelopeTest();
        try {
            t3.symbolicMessageEnvelopeRules();
        } finally {
            t3.clearThread();
        }
        WireValueIsNotARootTest t4 =
                new WireValueIsNotARootTest();
        t4.wireValueIsNotARootRules();
    }

    private void theHandoffOccurrenceIsTheSameStringInEveryReplay() {
        String first = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        assertEquals("nothing per-replay is in the identity", first,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT));
        assertTrue(first.startsWith("HANDOFF_PHASE."));
        assertNotEquals("a loop's second turn is a second variable", first,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 2, ELEMENT));
        assertNotEquals("another element is another handoff", first,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                        "<org.apache.hadoop.ipc.Client$Call: int retry>"));
        assertNotEquals("another consumer occurrence is another handoff",
                first, HandoffPhaseContract.phaseId(PORT,
                        "hdfs-17899/source-dn#epoch0/region/REGION.53092d3e#1",
                        1, ELEMENT));
        assertNotEquals("the handoff label is not a configured source label",
                "SRC.", HandoffPhaseContract.engineLabelForPhase(first,
                        PORT).substring(0, 4));
    }

    /** The row states v_H, what it delivered, and its domain. */
    private void theRowStatesTheHandoffVariableAndItsDeliveredValue() {
        JsonObject row = row("");

        assertEquals(7, row.get("schemaVersion").getAsInt());
        assertEquals("H is the consumer the plan declares, not the row",
                CONSUMER,
                row.get(VmHandoffEvidence.CONSUMER_OCCURRENCE_ID)
                        .getAsString());
        assertEquals(HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                row.get(VmHandoffEvidence.HANDOFF_PHASE_ID).getAsString());
        assertEquals("M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                row.get(VmHandoffEvidence.HANDOFF_SYMBOL).getAsString());
        assertEquals("119982",
                row.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertEquals("I", row.get(VmHandoffEvidence.JAVA_TYPE).getAsString());
        assertFalse(row.get(VmHandoffEvidence.ANSWERED).getAsBoolean());
        assertTrue("e_p stays on the row as a family member, not a shadow",
                row.has(VmHandoffEvidence.EXPRESSION));
        assertTrue(VmHandoffEvidence.eventFault(row),
                VmHandoffEvidence.isEvent(row));
    }

    /** Every new member is required; none is completed from another. */
    private void aRowMissingAnyOfThemIsRefused() {
        for (String member : new String[]{
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID,
                VmHandoffEvidence.HANDOFF_PHASE_ID,
                VmHandoffEvidence.HANDOFF_SYMBOL,
                VmHandoffEvidence.RECORDED_VALUE,
                VmHandoffEvidence.JAVA_TYPE}) {
            JsonObject row = row("");
            row.remove(member);
            assertFalse(member + " must be required",
                    VmHandoffEvidence.isEvent(row));
        }
        JsonObject unanswered = row("");
        unanswered.addProperty(VmHandoffEvidence.ANSWERED, true);
        assertFalse("an answered row without its value is refused",
                VmHandoffEvidence.isEvent(unanswered));
    }

    /**
     * An obligation assignment for H answers the mint, through the
     * configured-source mechanism and not a second one.
     */
    private void anAssignmentForTheHandoffAnswersTheMint() {
        String phaseId = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        JsonObject encoded = new JsonObject();
        encoded.addProperty("engineSymbol", "M_I_field_HOFF.9c1d");
        encoded.addProperty("inputSymbol", "SOURCE_PHASE:" + phaseId);
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "119981");
        encoded.addProperty("configuredSourcePhaseId", phaseId);
        // The phase id is the whole identity of H, so it is also the source
        // id, and there is no field signature beside it: the element path is
        // already inside the hash.  This is the row the solver emits.
        encoded.addProperty("configuredSourceId", phaseId);
        encoded.addProperty("configuredSourceFieldSignature", "");
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);

        assertTrue("the configured-source matcher is the one mechanism",
                assignment.matchesConfiguredSource(phaseId, phaseId, ""));
        assertFalse("and it is keyed on the handoff occurrence",
                assignment.matchesConfiguredSource(
                        HandoffPhaseContract.phaseId(PORT, CONSUMER, 2,
                                ELEMENT), phaseId, ""));

        JsonObject answered = row(assignment.value);
        assertTrue(answered.get(VmHandoffEvidence.ANSWERED).getAsBoolean());
        assertEquals("119981",
                answered.get(VmHandoffEvidence.ANSWERED_VALUE).getAsString());
        assertEquals("what the wire delivered is still stated", "119982",
                answered.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(answered),
                VmHandoffEvidence.isEvent(answered));
    }

    /**
     * A message with no element for this decode still mints the consumer's
     * variable, on the value that arrived.
     *
     * <p>e_p is a member of H's family, not a condition of H existing.  The
     * mint used to be refused with {@code RPC_HANDOFF_MISSING_METADATA}, and
     * the consequence was not a missing family arm but a replay that ignored
     * its own obligation: on hdfs-17899 bug3 the flip replay of the target
     * ran with nn0 concrete, published zero handoff rows, read the recorded
     * key, and the obligation ended REPLAY_NOT_ADMITTED.</p>
     */
    private void aDeliveryWithNoElementStillMintsTheConsumersVariable() {
        JsonObject row = arrivedRow("");

        assertTrue("the row says what it does not have",
                row.get(VmHandoffEvidence.ELEMENT_ABSENT).getAsBoolean());
        assertTrue(VmHandoffEvidence.isElementAbsent(row));
        assertFalse("no producer expression travels on it",
                row.has(VmHandoffEvidence.EXPRESSION));
        assertEquals("what arrived is stated", "119982",
                row.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertEquals("and v_H is minted all the same",
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                row.get(VmHandoffEvidence.HANDOFF_SYMBOL).getAsString());
        assertEquals(HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                row.get(VmHandoffEvidence.HANDOFF_PHASE_ID).getAsString());
        assertFalse(row.get(VmHandoffEvidence.ANSWERED).getAsBoolean());
        assertTrue(VmHandoffEvidence.eventFault(row),
                VmHandoffEvidence.isEvent(row));

        JsonObject claiming = arrivedRow("");
        claiming.addProperty(VmHandoffEvidence.PRODUCER_TASK_ID, "TASK.X");
        assertFalse("a row with no element may not name a producer",
                VmHandoffEvidence.isEvent(claiming));

        // And it reaches the result row.  Admission is not publication:
        // writeTo anchored every row's expression by content, and a row
        // with none threw "content anchor requires one expression object"
        // out of that loop -- which dropped the whole vmHandoffEvents array
        // AND the rpcHandoffGaps written after it.  On hdfs-17899 bug3
        // laneVM21 the flip replay minted v_H at all four consumer
        // activations (their sharedExpressionTable carries the HOFF
        // symbols) and published neither a handoff row nor a gap, so an
        // answer that had been applied looked unapplied.
        JsonObject published = new JsonObject();
        VmHandoffEvidence.writeTo(published,
                java.util.Collections.singletonList(row));
        assertEquals("the row a delivery with no element mints is published",
                1, published.getAsJsonArray(
                        VmHandoffEvidence.FIELD).size());
        assertFalse("and it carries no content anchor to a value it has not",
                published.getAsJsonArray(VmHandoffEvidence.FIELD).get(0)
                        .getAsJsonObject().has(VmHandoffEvidence.EXPRESSION));

        JsonObject both = new JsonObject();
        VmHandoffEvidence.writeTo(both,
                java.util.Arrays.asList(row, row("")));
        assertEquals("beside a delivery that did carry one", 2,
                both.getAsJsonArray(VmHandoffEvidence.FIELD).size());
    }

    /**
     * The assignment answers that mint, and the receiving frame reads the
     * answered value back off the carrier leaf.
     */
    private void anAssignmentAnswersAMintWithNoElement() {
        JsonObject answered = arrivedRow("119981");

        assertTrue(answered.get(VmHandoffEvidence.ANSWERED).getAsBoolean());
        assertEquals("119981", answered.get(
                VmHandoffEvidence.ANSWERED_VALUE).getAsString());
        assertEquals("what arrived is still stated", "119982",
                answered.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(answered),
                VmHandoffEvidence.isEvent(answered));

        // The one write the mint performs: instrumentation reads the leaf
        // back into the receiving frame's own local right after the hook, so
        // writing the carrier IS the receiver seeing the value.
        ConcolicRegionRuntime.HandoffLeafCarrier carrier =
                new ConcolicRegionRuntime.HandoffLeafCarrier();
        carrier.i = 119982;
        assertEquals("the value that arrived", "119982",
                ConcolicRegionRuntime.recordedScalar(carrier.i));
        assertTrue(ConcolicRegionRuntime.writeModeledField(carrier,
                "<" + ConcolicRegionRuntime.HandoffLeafCarrier.class.getName()
                        + ": int i>", answer()));
        assertEquals("the receiving frame reads back the answer",
                119981, carrier.i);
    }

    /** The obligation assignment for this handoff occurrence. */
    private static ConcolicRegionRuntime.ModelAssignment answer() {
        String phaseId = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        JsonObject encoded = new JsonObject();
        encoded.addProperty("engineSymbol", "M_I_field_HOFF.9c1d");
        encoded.addProperty("inputSymbol", "SOURCE_PHASE:" + phaseId);
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "119981");
        encoded.addProperty("configuredSourcePhaseId", phaseId);
        encoded.addProperty("configuredSourceId", phaseId);
        encoded.addProperty("configuredSourceFieldSignature", "");
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    /** One row as the runtime writes it when the message had no element. */
    private static JsonObject arrivedRow(String answeredValue) {
        return VmHandoffEvidence.event(PORT, 0L, 0L, null, "", "",
                CONSUMER,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                "119982", "I", answeredValue, true);
    }

    /** One published row, as the runtime writes it after the mint. */
    private static JsonObject row(String answeredValue) {
        JsonObject producerExpression = new JsonObject();
        producerExpression.addProperty("_type", "ConsumerBoundaryExpression");
        producerExpression.addProperty("boundaryKind", "RPC_ATTACH");
        producerExpression.addProperty("eventId", 468);
        producerExpression.addProperty("_java_type", "I");
        JsonObject payload = new JsonObject();
        payload.addProperty("_type", "SymbolExpression");
        payload.addProperty("_java_type", "I");
        payload.addProperty("_exp", "M_I_field_SRC.8c6c_BlockTokenSecretManager");
        producerExpression.add("expression", payload);
        return VmHandoffEvidence.event(PORT, 466L, 468L, producerExpression,
                "TASK.SEED.78bb59b2", "hdfs-17899/source-dn#epoch0/region/"
                        + "REGION.d930c3a2#1#a1",
                CONSUMER,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                "119982", "I", answeredValue, false);
    }

    /**
     * A plan carrying the answer to a handoff this task receives loads.
     *
     * <p>The model names no publish site of the frozen catalog -- H is not
     * a configured source site -- so the load used to refuse the whole
     * obligation: on laneVM19 every flip replay of bug3's target exited 1
     * with "model assignment names an undeclared or unsupported configured
     * source ... M_I_field_HOFF.68d851c9...".  It is admitted on the one
     * thing the task can check: the phase belongs to a port it receives
     * on, which the mint's own VM label proves.</p>
     */
    private void aPlanAnsweringAHandoffThisTaskReceivesLoads()
            throws Exception {
        String phaseId = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        ConcolicTaskPlan.RuntimeTask task = new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(taskRow(phaseId, PORT)));

        assertEquals(PORT, task.communicationHandoff(PORT, false).portId());
    }

    /** A phase no port of this task reproduces is refused, by name. */
    private void aPlanAnsweringAHandoffThisTaskCannotIsRefused() {
        String otherPort = "XCH.1174244c-3118-3892-a173-6cc5895259bf"
                + ".resp.block-key-id";
        String phaseId = HandoffPhaseContract.phaseId(otherPort, CONSUMER, 1,
                ELEMENT);
        try {
            new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                    taskRow(phaseId, otherPort)));
            org.junit.Assert.fail("a handoff of another port is not this"
                    + " task's to answer");
        } catch (IllegalArgumentException refused) {
            String said = String.valueOf(refused.getMessage());
            assertTrue(said, said.contains("undeclared or unsupported"));
            assertTrue("the row is named", said.contains("HOFF."));
        }
    }

    /**
     * One task row receiving on {@code PORT}, answering {@code phaseId}
     * with a model whose engine symbol is the label of {@code labelPort}.
     */
    private static JsonObject taskRow(String phaseId, String labelPort) {
        JsonObject row = new JsonObject();
        row.addProperty("taskId", "TASK.REPLAY.handoff");
        row.addProperty("goalId", "GOAL.1");
        row.addProperty("goalKind", "REGION_PATH_CLOSURE");
        row.addProperty("regionId", "REGION.53092d3e");
        row.addProperty("relationKey", "REL.1");
        row.addProperty("sourceKey", "hdfs-17899/target-dn#epoch0");
        row.addProperty("occurrenceId", CONSUMER);
        row.addProperty("rootMethod", "<a.B: void run()>");
        row.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        row.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", "<a.B: void run()>");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        anchor.addProperty("sourceKey", "hdfs-17899/target-dn#epoch0");
        selector.add("causalAnchor", anchor);
        row.add("rootSelector", selector);
        row.add("branches", new com.google.gson.JsonArray());
        row.add("inputActions", new com.google.gson.JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        row.add("loopBound", loopBound);

        JsonObject handoff = new JsonObject();
        handoff.addProperty("portId", PORT);
        handoff.addProperty("handoffLeafPath", PORT);
        handoff.addProperty("side", "IN");
        handoff.addProperty("direction", "REQUEST");
        handoff.addProperty("captureKind", "CALL_RETURN");
        handoff.addProperty("javaType", "int");
        handoff.addProperty("declaredCallee", "<a.P: int id()>");
        handoff.addProperty("definitionMethod", "<a.B: void run()>");
        handoff.addProperty("definitionUnitIndex", 2);
        com.google.gson.JsonArray handoffs = new com.google.gson.JsonArray();
        handoffs.add(handoff);
        row.add("communicationHandoffs", handoffs);

        JsonObject model = new JsonObject();
        model.addProperty("engineSymbol", "M_I_field_"
                + HandoffPhaseContract.engineLabelForPhase(phaseId, labelPort)
                + "_a/B$Carrier");
        model.addProperty("inputSymbol", "SOURCE_PHASE:" + phaseId);
        model.addProperty("valueType", "INT");
        model.addProperty("value", "119980");
        model.addProperty("configuredSourcePhaseId", phaseId);
        model.addProperty("configuredSourceId", phaseId);
        model.addProperty("configuredSourceFieldSignature", "");
        com.google.gson.JsonArray models = new com.google.gson.JsonArray();
        models.add(model);
        row.add("modelAssignments", models);
        return row;
    }

    /**
     * A port that crosses on a reference is one attach and several variables.
     *
     * <p>Lane 17897 and lane 11741: {@code exportAllKeys} delivers a
     * {@code BlockKey[]} on {@code XCH....resp.block-key-array}, and the mint
     * refused it for not being a primitive, so the port published no row and the
     * planned handoff read as "not reproduced" 12 and 55 times. What the
     * consumer's formula actually reads are the leaves -- {@code [i].keyId},
     * {@code [i].expiryDate} -- so each leaf is its own handoff occurrence, with
     * the leaf in its element path, and each joins its own family.</p>
     */
    static final class HandoffLeavesOfOneAttachTest {
        /** Two keys, each with an int and a long leaf, as the wire delivers. */
        public static final class Key {
            public int keyId;
            public long expiryDate;
            public Object unusedReference;

            Key(int keyId, long expiryDate) {
                this.keyId = keyId;
                this.expiryDate = expiryDate;
            }
        }

        /** The carrier field one declared port crosses on. */
        public static final class Carrier {
            public Object o;
            public int i;
        }

        /** An array of two objects with two primitive leaves each: four rows. */
        public void handoffLeavesOfOneAttachRules() throws Exception {
            anArrayPortMintsOneVariablePerPrimitiveLeaf();
            aPrimitivePortIsStillOneLeaf();
            anArrayOfPrimitivesExposesNoLeaf();
        }

        private void anArrayPortMintsOneVariablePerPrimitiveLeaf()
                throws Exception {
            Carrier carrier = new Carrier();
            carrier.o = new Key[] {new Key(119980, 7L), new Key(119981, 9L)};

            List<String> paths = leafPaths(carrier, "o");

            assertEquals("two elements, two primitive leaves each", 4,
                    paths.size());
            assertTrue(paths.toString(), paths.get(0).startsWith("[0]"));
            assertTrue(paths.toString(), paths.get(2).startsWith("[1]"));
            assertTrue(paths.toString(), paths.get(0).contains("int keyId"));
            assertTrue(paths.toString(),
                    paths.get(1).contains("long expiryDate"));
            assertTrue("a reference leaf is not one the VM can mint on",
                    paths.toString().indexOf("unusedReference") < 0);

            // Four leaves, four handoff occurrences: one variable each.
            Set<String> phases = new LinkedHashSet<>();
            for (int index = 0; index < paths.size(); index++) {
                phases.add(HandoffPhaseContract.phaseId("XCH.port",
                        "hdfs-17897/nn0#epoch0/region/REGION.a56f78d6#1",
                        1, paths.get(index)));
            }
            assertEquals("one variable per leaf", 4, phases.size());
        }

        /** A primitive destination is one leaf: itself, unchanged. */
        private void aPrimitivePortIsStillOneLeaf() throws Exception {
            Carrier carrier = new Carrier();
            carrier.i = 119982;

            List<String> paths = leafPaths(carrier, "i");

            assertEquals(1, paths.size());
            assertTrue(paths.get(0), paths.get(0).contains("int i"));
            assertTrue("its own signature, unprefixed",
                    paths.get(0).startsWith("<"));
        }

        /** An array of primitives addresses no field, and says so by silence. */
        private void anArrayOfPrimitivesExposesNoLeaf() throws Exception {
            Carrier carrier = new Carrier();
            carrier.o = new int[] {1, 2, 3};

            assertTrue("the caller names this loss rather than minting",
                    leafPaths(carrier, "o").isEmpty());
        }

        private static List<String> leafPaths(Object owner, String fieldName)
                throws Exception {
            Field element = Carrier.class.getDeclaredField(fieldName);
            Method leaves = ConcolicRegionRuntime.class.getDeclaredMethod(
                    "handoffLeaves", Object.class, Field.class);
            leaves.setAccessible(true);
            List<?> found = (List<?>) leaves.invoke(null, owner, element);
            List<String> paths = new ArrayList<>();
            for (Object leaf : found) {
                Field path = leaf.getClass().getDeclaredField("path");
                path.setAccessible(true);
                paths.add((String) path.get(leaf));
            }
            return paths;
        }
    }


    /**
     * How many consumers one exported communication port may address.
     *
     * <p>A wire producer rooted at a loop body is entered once per <em>message</em>
     * and exports one value per iteration, so one outgoing port addresses one
     * consumer occurrence per element the delivery carries.  These transcripts pin
     * the two recorded campaigns that first hit it -- hdfs-17899 bug3, where the
     * NameNode answers one DataNode's heartbeat with four block keys, and
     * hdfs-17897, where it answers one refresh with five -- and pin the one thing
     * that is still refused: consumers on two execution sources, which no single
     * message could reach.  The refusal fires in the decode both the PLAN stage
     * and the replay JVM pass through, so a plan the runtime cannot execute never
     * reaches REPLAY.</p>
     */
    static final class ExportPortConsumerOccurrencesTest {
        private static final String KEY_ID_PORT =
                "XCH.1174244c-3118-3892-a173-6cc5895259bf.resp.block-key-id";
        private static final String EXPIRY_PORT =
                "XCH.cfba8c05-3dcb-3577-aec4-79db5ccfe24e.resp.block-key-expiry-date";

        public void clearEnvelope() {
            SymbolicMessageEnvelope.clear();
        }

        /** bug3: one heartbeat answer frame, four per-key consumer occurrences. */
        public void exportPortConsumerOccurrencesRules() throws Exception {
            oneHeartbeatAnswerAddressesEveryPerKeyConsumer();
            eachStagedValueIsTakenOnce();
        }

        private void oneHeartbeatAnswerAddressesEveryPerKeyConsumer() {
            ConcolicTaskPlan.RuntimeTask task = task(
                    "plans/hdfs-17899-bug3-loop-body-producer.json");

            assertEquals("hdfs-17899/nn0#epoch0/region/"
                            + "REGION.2392e4b7-aa01-3487-85a3-ac776965f7f7#1",
                    task.occurrenceId);
            assertEquals(consumers("hdfs-17899/target-dn", 2, 3, 4, 5),
                    task.exportConsumerOccurrences(KEY_ID_PORT));
            assertEquals(consumers("hdfs-17899/target-dn", 2, 3, 4, 5),
                    task.exportConsumerOccurrences(EXPIRY_PORT));
            // One response frame carrying four keys, not four responses.
            assertEquals(1, exchangeLegs(
                    row("plans/hdfs-17899-bug3-loop-body-producer.json"),
                    KEY_ID_PORT).size());
        }

        /** One staged value per iteration; the queue hands out one each. */
        private void eachStagedValueIsTakenOnce() {
            ConcolicTaskPlan.RuntimeTask task = task(
                    "plans/hdfs-17899-bug3-loop-body-producer.json");
            List<String> addressed = task.exportConsumerOccurrences(KEY_ID_PORT);
            for (int iteration = 1; iteration <= addressed.size(); iteration++) {
                assertTrue(SymbolicMessageEnvelope.stage(KEY_ID_PORT, iteration,
                        task.taskId, task.occurrenceId + "#a" + iteration,
                        addressed));
            }
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            for (int iteration = 1; iteration <= addressed.size(); iteration++) {
                SymbolicMessageEnvelope.Entry taken =
                        SymbolicMessageEnvelope.take(KEY_ID_PORT);
                assertTrue(taken.present());
                assertEquals(iteration, taken.handle());
            }
            assertFalse(SymbolicMessageEnvelope.take(KEY_ID_PORT).present());
        }

        private static List<String> consumers(String source, int... ordinals) {
            List<String> ids = new ArrayList<>();
            for (int ordinal : ordinals) {
                ids.add(source + "#epoch0/region/"
                        + "REGION.1f6914ec-f8dc-3369-8f6a-dbfcccdb2762#"
                        + ordinal);
            }
            return ids;
        }

        private static Set<String> exchangeLegs(JsonObject row, String portId) {
            Set<String> legs = new LinkedHashSet<>();
            for (com.google.gson.JsonElement element
                    : row.getAsJsonArray("edgeBindings")) {
                JsonObject binding = element.getAsJsonObject();
                if (portId.equals(optional(binding, "fromOutputPort"))) {
                    legs.add(optional(binding, "exchangeLeg"));
                }
            }
            return legs;
        }

        private static String optional(JsonObject row, String field) {
            return row.has(field) && row.get(field).isJsonPrimitive()
                    ? row.get(field).getAsString() : "";
        }

        private static ConcolicTaskPlan.RuntimeTask task(String resource) {
            ExecutionTask task = ExecutionTask.decode(row(resource));
            List<String> outgoing = new ArrayList<>();
            for (CommunicationHandoffSpec site : task.communicationHandoffs()) {
                if (site.outgoing()) outgoing.add(site.portId());
            }
            assertEquals(Arrays.asList(KEY_ID_PORT, EXPIRY_PORT), outgoing);
            return new ConcolicTaskPlan.RuntimeTask(task);
        }

        private static JsonObject row(String resource) {
            try (InputStream bytes = ExportPortConsumerOccurrencesTest.class
                    .getClassLoader().getResourceAsStream(resource)) {
                if (bytes == null) {
                    throw new IllegalStateException("missing " + resource);
                }
                return new JsonParser().parse(new InputStreamReader(bytes,
                        StandardCharsets.UTF_8)).getAsJsonObject();
            } catch (Exception failure) {
                throw new IllegalStateException(failure);
            }
        }
    }


    /**
     * A capture site is declared on exactly one consumer region.
     *
     * <p>A site inside a helper lies inside every selected region whose code
     * reaches it, and each of them declared the port. The value crosses the wire
     * once, so the attach files it on one of them -- the innermost live
     * occurrence that declares it -- and every other declaring occurrence was
     * then reported at IMPORT as PLANNED_HANDOFF_NOT_REPRODUCED. On hdfs-17899
     * bug2 that is {@code resp.block-key-id} and
     * {@code resp.block-key-expiry-date}, declared both by the per-call region
     * rooted at {@code PBHelper.convert(BlockKeyProto)} and by the loop-body
     * region rooted at the enclosing {@code convert(ExportedBlockKeysProto)}:
     * 18 handoff events, every one naming the per-call region, and 12
     * not-reproduced rows, every one on the loop-body region.</p>
     *
     * <p>The plan now says what the attach does. H is (portId, consumer
     * occurrence, k-th attach, element path), so two consumers for one wire
     * value would be two variables for one value.</p>
     */
    static final class OneCaptureSiteOneConsumerTest {
        private static final String INNER = "<a.PBHelper: a.Key convert(a.KeyProto)>";
        private static final String OUTER =
                "<a.PBHelper: a.Keys convert(a.KeysProto)>";
        private static final String PORT = "XCH.1.resp.block-key-id";

        /** The region whose own root is the capture's method keeps it. */
        public void oneCaptureSiteOneConsumerRules() throws Exception {
            onlyTheInnermostSelectedRegionDeclaresTheSite();
            anUncontestedSiteStaysWhereItIs();
            anOutgoingSiteIsNeverReassigned();
        }

        private void onlyTheInnermostSelectedRegionDeclaresTheSite()
                throws Exception {
            List<Map<String, Object>> plans = new ArrayList<>();
            plans.add(plan("REGION.inner", INNER, PORT, "IN", INNER));
            plans.add(plan("REGION.outer", OUTER, PORT, "IN", INNER));

            retain(plans);

            assertTrue("the per-call region keeps its own site",
                    plans.get(0).containsKey(CommunicationHandoffSpec.FIELD));
            assertEquals("the enclosing region declares it no longer",
                    null, plans.get(1).get(CommunicationHandoffSpec.FIELD));
        }

        /** With no inner region selected, the enclosing one keeps it. */
        private void anUncontestedSiteStaysWhereItIs() throws Exception {
            List<Map<String, Object>> plans = new ArrayList<>();
            plans.add(plan("REGION.outer", OUTER, PORT, "IN", INNER));

            retain(plans);

            assertTrue("nothing inner is selected, so nobody else owns it",
                    plans.get(0).containsKey(CommunicationHandoffSpec.FIELD));
        }

        /** An OUT site is the producer's own act and is never moved. */
        private void anOutgoingSiteIsNeverReassigned() throws Exception {
            List<Map<String, Object>> plans = new ArrayList<>();
            plans.add(plan("REGION.inner", INNER, PORT, "OUT", INNER));
            plans.add(plan("REGION.outer", OUTER, PORT, "OUT", INNER));

            retain(plans);

            assertTrue(plans.get(0).containsKey(CommunicationHandoffSpec.FIELD));
            assertTrue("an export is not a consumer declaration",
                    plans.get(1).containsKey(CommunicationHandoffSpec.FIELD));
        }

        @SuppressWarnings("unchecked")
        private static void retain(List<Map<String, Object>> plans)
                throws Exception {
            Method retain = RuntimeRegionPlanner.class.getDeclaredMethod(
                    "retainInnermostCommunicationConsumers", List.class);
            retain.setAccessible(true);
            retain.invoke(null, plans);
        }

        /** One region plan row with one declared communication handoff. */
        private static Map<String, Object> plan(String regionId, String rootMethod,
                                                String portId, String side,
                                                String definitionMethod) {
            Map<String, Object> plan = new LinkedHashMap<>();
            plan.put("regionId", regionId);
            Map<String, Object> selector = new LinkedHashMap<>();
            selector.put("method", rootMethod);
            plan.put("rootSelector", selector);
            Map<String, Object> site = new LinkedHashMap<>();
            site.put(CommunicationCatalogContract.PORT_ID, portId);
            site.put(CommunicationHandoffSpec.SIDE, side);
            site.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                    definitionMethod);
            List<Map<String, Object>> sites = new ArrayList<>();
            sites.add(site);
            plan.put(CommunicationHandoffSpec.FIELD, sites);
            return plan;
        }
    }


    /**
     * An expression belongs to a value inside the message, not to a queue.
     *
     * <p>One declared port carries many unrelated values of one shape in one
     * message, so each is addressed by its element ordinal and a decode looks its
     * own element up.  What these tests pin down is that addressing: the element
     * a decode asks for is the element it gets, an element the sender never
     * staged answers absent instead of handing over the next one along, and an
     * element nothing looked up is still countable when the message closes.</p>
     */
    static final class SymbolicMessageEnvelopeTest {
        private static final String PORT = "XCH.port.resp.key-id";
        private static final String OTHER = "XCH.port.resp.expiry";
        private static final List<String> CONSUMERS =
                Collections.singletonList("node/region/R#1#a1");

        public void clearThread() {
            SymbolicMessageEnvelope.clear();
        }

        /** Element n of a message is taken by the decode of element n. */
        public void symbolicMessageEnvelopeRules() throws Exception {
            eachElementIsTakenByItsOwnDecode();
            aConcreteLeafArrivesPresentWithNoHandle();
            ordinalsAreCountedWithinOnePort();
            aDecodeOfAnElementTheSenderNeverStagedIsAbsent();
            anElementIsNotHandedOutTwice();
            elementsNothingLookedUpAreCounted();
            theOrdinalTravelsOnTheWire();
            try {
                anOlderWireIsRefused();
                org.junit.Assert.fail("expected IllegalArgumentException");
            } catch (IllegalArgumentException expected) {
                org.junit.Assert.assertNotNull(expected);
            }
            aFrameKeepsTwoGroupsOfOneShapeApart();
            aFrameNobodyDecodesLeavesItsElementsUnclaimed();
            anUnframedPortIsAddressedWithinTheMessage();
        }

        private void eachElementIsTakenByItsOwnDecode() {
            stage(PORT, 11L);
            stage(PORT, 22L);
            stage(PORT, 33L);
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(33L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(0, SymbolicMessageEnvelope.inboundUnattached());
        }

        /**
         * A concrete leaf arrives present, carrying no expression.
         *
         * <p>{@code exportCommunicationLeaf} stages handle 0 for a leaf the VM
         * answered {@code NOT_SYMBOLIC} -- a concrete leaf is still a leaf the
         * message carried -- so the consumer takes an element that is
         * {@code present()} with no live handle.  For the consumer that is the
         * same fact as no element at all: there is an arrived value and no
         * producer expression, so it mints v_H from the arrival and the row
         * states {@code elementAbsent}.  It used to be refused with
         * RPC_HANDOFF_UNKNOWN_HANDLE, which left the obligation's assignment
         * unapplied exactly as the no-element refusal did.</p>
         */
        private void aConcreteLeafArrivesPresentWithNoHandle() {
            assertTrue("a concrete leaf is still staged",
                    SymbolicMessageEnvelope.stage(PORT, 0L, "TASK.SEED.1",
                            "node/region/R#1", CONSUMERS));
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            SymbolicMessageEnvelope.Entry arrived =
                    SymbolicMessageEnvelope.take(PORT);
            assertTrue("the element is there", arrived.present());
            assertEquals("and it carries no expression", 0L, arrived.handle());
            assertEquals("nothing is left unlooked-up", 0,
                    SymbolicMessageEnvelope.inboundUnattached());
        }

        /** Ordinals are per port, so two ports do not shift each other. */
        private void ordinalsAreCountedWithinOnePort() {
            stage(PORT, 11L);
            stage(OTHER, 91L);
            stage(PORT, 22L);
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            assertEquals(91L, SymbolicMessageEnvelope.take(OTHER).handle());
            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
        }

        /**
         * A decode past the end of a message is told so.
         *
         * <p>The head of a queue would have handed it the next port's value or
         * the next message's; an ordinal has nothing to hand over.</p>
         */
        private void aDecodeOfAnElementTheSenderNeverStagedIsAbsent() {
            stage(PORT, 11L);
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
            assertFalse(SymbolicMessageEnvelope.take(PORT).present());
            assertFalse(SymbolicMessageEnvelope.take(PORT).present());
        }

        /** An element is handed out once; a repeat decode is absent. */
        private void anElementIsNotHandedOutTwice() {
            stage(PORT, 11L);
            String wire = SymbolicMessageEnvelope.takeOutbound();
            SymbolicMessageEnvelope.installInbound(wire);
            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());

            SymbolicMessageEnvelope.installInbound(wire);
            assertEquals("a fresh message starts at its own first element",
                    11L, SymbolicMessageEnvelope.take(PORT).handle());
        }

        /** What no decode looked up is still countable while the message lives. */
        private void elementsNothingLookedUpAreCounted() {
            stage(PORT, 11L);
            stage(PORT, 22L);
            stage(PORT, 33L);
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            assertEquals(3, SymbolicMessageEnvelope.inboundUnattached());
            SymbolicMessageEnvelope.take(PORT);
            assertEquals(2, SymbolicMessageEnvelope.inboundUnattached());
            SymbolicMessageEnvelope.clearInbound();
            assertEquals(0, SymbolicMessageEnvelope.inboundUnattached());
        }

        /** The ordinal the sender stamped travels with the element. */
        private void theOrdinalTravelsOnTheWire() {
            stage(PORT, 11L);
            stage(PORT, 22L);
            String wire = SymbolicMessageEnvelope.takeOutbound();
            assertTrue(wire.startsWith("CSE4;"));
            SymbolicMessageEnvelope.installInbound(wire);

            assertEquals(0, SymbolicMessageEnvelope.peek(PORT).ordinal());
            assertEquals(0, SymbolicMessageEnvelope.take(PORT).ordinal());
            assertEquals(1, SymbolicMessageEnvelope.take(PORT).ordinal());
        }

        /** A wire this vocabulary did not write is refused, not guessed at. */
        private void anOlderWireIsRefused() {
            SymbolicMessageEnvelope.installInbound("CSE3;cG9ydA,1,dA,bw,Yw,0");
        }

        /**
         * Two groups of the same shape in one message do not run together.
         *
         * <p>The frame is the thing whose one construction builds one instance of
         * the value the port belongs to.  Without it a receiver decoding the
         * second group would take the first group's leaves; with it each group's
         * elements are counted inside their own frame.</p>
         */
        private void aFrameKeepsTwoGroupsOfOneShapeApart() {
            SymbolicMessageEnvelope.pushOutboundFrame();
            stage(PORT, 11L);
            stage(PORT, 12L);
            SymbolicMessageEnvelope.popOutboundFrame();
            SymbolicMessageEnvelope.pushOutboundFrame();
            stage(PORT, 21L);
            stage(PORT, 22L);
            SymbolicMessageEnvelope.popOutboundFrame();
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            SymbolicMessageEnvelope.pushInboundFrame();
            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(12L, SymbolicMessageEnvelope.take(PORT).handle());
            assertFalse("a frame holds only its own elements",
                    SymbolicMessageEnvelope.take(PORT).present());
            SymbolicMessageEnvelope.popInboundFrame();

            SymbolicMessageEnvelope.pushInboundFrame();
            assertEquals(21L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
            SymbolicMessageEnvelope.popInboundFrame();
            assertEquals(0, SymbolicMessageEnvelope.inboundUnattached());
        }

        /** A decode that opens fewer frames leaves the rest unclaimed, by name. */
        private void aFrameNobodyDecodesLeavesItsElementsUnclaimed() {
            SymbolicMessageEnvelope.pushOutboundFrame();
            stage(PORT, 11L);
            SymbolicMessageEnvelope.popOutboundFrame();
            SymbolicMessageEnvelope.pushOutboundFrame();
            stage(PORT, 21L);
            SymbolicMessageEnvelope.popOutboundFrame();
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            SymbolicMessageEnvelope.pushInboundFrame();
            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
            SymbolicMessageEnvelope.popInboundFrame();

            assertEquals(1, SymbolicMessageEnvelope.inboundUnattached());
        }

        /** A port that declares no frame is addressed within the message. */
        private void anUnframedPortIsAddressedWithinTheMessage() {
            stage(PORT, 11L);
            stage(PORT, 22L);
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            assertEquals(0, SymbolicMessageEnvelope.peek(PORT).frame());
            assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
            assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
        }

        private static void stage(String portId, long handle) {
            assertTrue(SymbolicMessageEnvelope.stage(portId, handle,
                    "TASK.SEED.0", "node/region/R#1#a1",
                    Arrays.asList(CONSUMERS.get(0))));
        }
    }


    /**
     * A value the wire delivered is a carrier, never a root.
     *
     * <p>HDFS-17899 cuts the block-key export at
     * {@code PBHelper.convert(BlockKeyProto)}: the consumer reads
     * {@code getKeyId()} / {@code getExpiryDate()} off the received proto and
     * builds a {@code BlockKey} from them.  Those two reads are declared
     * {@code WIRE_FLOW} cut ports, so the expression that gives them meaning is
     * the NameNode's, installed by {@code attachCommunicationLeaf}.</p>
     *
     * <p>The attach runs <em>after</em> the materialization hook in the
     * instrumented frame -- both passes insert after the cut statement, so the
     * later pass lands closer to it -- which means nothing symbolic has reached
     * the local when the hook asks.  Treating that as "mint one" gives the
     * formula a free existential per port per consumer that the attach then
     * overwrites: four extra roots on the two DataNodes, a reach condition that
     * degenerates to {@code true}, and both fault valuations sat.  The reference
     * corpus never minted there -- it recorded the port as reused 57 times --
     * and only because a neighbouring accessor read happened to leave an
     * expression on the getter's return.  This pins the policy instead of the
     * luck.</p>
     */
    static final class WireValueIsNotARootTest {

        private static final String CONVERT =
                "<org.apache.hadoop.hdfs.protocolPB.PBHelper:"
                        + " org.apache.hadoop.hdfs.security.token.block.BlockKey"
                        + " convert(org.apache.hadoop.hdfs.protocol.proto"
                        + ".HdfsServerProtos$BlockKeyProto)>";
        private static final String KEY_ID_PORT =
                "XCH.1174244c.resp.block-key-id";
        private static final String EXPIRY_PORT =
                "XCH.cfba8c05.resp.block-key-expiry-date";

        public void wireValueIsNotARootRules() throws Exception {
            aPortStampedByTheFinalizerIsACutPort();
            aCutPortWithNothingPropagatedStillRefusesToMint();
            aCutPortReusesTheProducerExpression();
        }

        private void aPortStampedByTheFinalizerIsACutPort() {
            assertTrue(ConcolicRegionRuntime.declaredCommunicationCutPort(
                    cutPort(KEY_ID_PORT, "int", true)));
        }

        /**
         * The mint the bug produced: the consumer's copy carried nothing yet.
         *
         * <p>{@code carriesInputAuthority} answering false is what sends the
         * caller towards {@code api.symbolizeField(fresh, "value", ...)}.  It
         * still answers false -- there really is nothing to reuse at that
         * instant -- so the refusal has to be the second half of the decision,
         * which is what {@code declaredCommunicationCutPort} supplies inside
         * {@code observeWithoutMinting}.</p>
         */
        private void aCutPortWithNothingPropagatedStillRefusesToMint() {
            ConcolicRegionRuntime.SymbolizeAction port =
                    cutPort(KEY_ID_PORT, "int", true);

            assertFalse("nothing has reached the local yet",
                    ConcolicRegionRuntime.carriesInputAuthority(port, null));
            assertTrue("so the caller must leave it to the attach",
                    ConcolicRegionRuntime.declaredCommunicationCutPort(port));
        }

        /** Once the attach has landed, the ordinary reuse path takes it. */
        private void aCutPortReusesTheProducerExpression() {
            assertTrue(ConcolicRegionRuntime.carriesInputAuthority(
                    cutPort(KEY_ID_PORT, "int", true), senderSymbol()));
        }

        private static ConcolicRegionRuntime.SymbolizeAction cutPort(
                String portId, String javaType, boolean stampedByFinalizer) {
            return new ConcolicRegionRuntime.SymbolizeAction(portJson(
                    portId, javaType, stampedByFinalizer));
        }

        private static JsonObject portJson(String portId, String javaType,
                                           boolean stampedByFinalizer) {
            JsonObject json = new JsonObject();
            json.addProperty("symbol", portId);
            json.addProperty("portId", portId);
            json.addProperty("javaType", javaType);
            json.addProperty("location", "CALL_RETURN");
            json.addProperty("method", CONVERT);
            if (stampedByFinalizer) {
                json.addProperty("sourceKind", "COMMUNICATION_SITE_PORT");
            }
            return json;
        }

        /** What the attach installs: the producer's own symbol. */
        private static JsonObject senderSymbol() {
            JsonObject symbol = new JsonObject();
            symbol.addProperty("_type", "SymbolExpression");
            symbol.addProperty("_exp", "M_I_REGION.aaa1cfd7");
            symbol.addProperty("_java_type", "int");
            return symbol;
        }
    }

}
