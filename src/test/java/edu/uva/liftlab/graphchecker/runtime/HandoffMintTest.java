package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The handoff mint: one variable at one occurrence, answered like a source.
 *
 * <p>At a wire attach the consumer's element stops denoting the producer's
 * expression and starts denoting a fresh variable v_H, joined to the
 * producer's family offline.  H is the same string in every replay, the row
 * states v_H and what it delivered, and an assignment answers the mint as a
 * configured source would.</p>
 */
public class HandoffMintTest {
    private static final String PORT =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70.req"
                    + ".data-encryption-key-id";
    private static final String CONSUMER =
            "hdfs-17899/target-dn#epoch0/region/REGION.53092d3e#1";
    private static final String ELEMENT =
            "<org.apache.hadoop.ipc.Client$Call: int id>";
    private static final String CUT_PORT = "XCH.1174244c.resp.block-key-id";
    private static final String SOURCE = "hdfs-17899/target-dn#epoch0";
    private static final String RUN = "<a.B: void run()>";
    private static final String CONVERT = "<org.apache.hadoop.hdfs"
            + ".protocolPB.PBHelper: org.apache.hadoop.hdfs.security.token"
            + ".block.BlockKey convert(org.apache.hadoop.hdfs.protocol.proto"
            + ".HdfsServerProtos$BlockKeyProto)>";

    /** H is (port, consumer address, k, element) -- and no event id. */
    @Test
    public void theHandoffOccurrenceIsTheSameStringInEveryReplay() {
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

    /**
     * The row states v_H, what it delivered, and its domain; every member is
     * required and none is completed from another.
     *
     * <p>e_p is a member of H's family, not a condition of H existing: a
     * message with no element still mints the variable and publishes its
     * row.</p>
     */
    @Test
    public void theRowStatesTheHandoffVariableAndItsDeliveredValue() {
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

        for (String member : new String[]{
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID,
                VmHandoffEvidence.HANDOFF_PHASE_ID,
                VmHandoffEvidence.HANDOFF_SYMBOL,
                VmHandoffEvidence.RECORDED_VALUE,
                VmHandoffEvidence.JAVA_TYPE}) {
            JsonObject missing = row("");
            missing.remove(member);
            assertFalse(member + " must be required",
                    VmHandoffEvidence.isEvent(missing));
        }
        JsonObject unanswered = row("");
        unanswered.addProperty(VmHandoffEvidence.ANSWERED, true);
        assertFalse("an answered row without its value is refused",
                VmHandoffEvidence.isEvent(unanswered));

        JsonObject arrived = arrivedRow("");
        assertTrue("the row says what it does not have",
                arrived.get(VmHandoffEvidence.ELEMENT_ABSENT).getAsBoolean());
        assertTrue(VmHandoffEvidence.isElementAbsent(arrived));
        assertFalse("no producer expression travels on it",
                arrived.has(VmHandoffEvidence.EXPRESSION));
        assertEquals("what arrived is stated", "119982",
                arrived.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertEquals("and v_H is minted all the same",
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                arrived.get(VmHandoffEvidence.HANDOFF_SYMBOL).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(arrived),
                VmHandoffEvidence.isEvent(arrived));

        JsonObject claiming = arrivedRow("");
        claiming.addProperty(VmHandoffEvidence.PRODUCER_TASK_ID, "TASK.X");
        assertFalse("a row with no element may not name a producer",
                VmHandoffEvidence.isEvent(claiming));

        // Admission is not publication.
        JsonObject published = new JsonObject();
        VmHandoffEvidence.writeTo(published,
                java.util.Arrays.asList(arrived, row));
        assertEquals("the row a delivery with no element mints is published,"
                        + " beside one that did carry an expression", 2,
                published.getAsJsonArray(VmHandoffEvidence.FIELD).size());
        assertFalse("and it carries no content anchor to a value it has not",
                published.getAsJsonArray(VmHandoffEvidence.FIELD).get(0)
                        .getAsJsonObject().has(VmHandoffEvidence.EXPRESSION));
    }

    /**
     * An obligation assignment for H answers the mint, through the
     * configured-source mechanism and not a second one.
     *
     * <p>H is not a configured source site, so the model is admitted on the
     * one thing the task can check: the phase belongs to a port it
     * receives on.</p>
     */
    @Test
    public void anAssignmentForTheHandoffAnswersTheMint() throws Exception {
        String phaseId = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        ConcolicRegionRuntime.ModelAssignment assignment = answer();
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

        // A plan carrying that answer loads when the phase belongs to a port
        // this task receives on, and is refused by name when it does not.
        ConcolicTaskPlan.RuntimeTask task = new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(taskRow(phaseId, PORT)));
        assertEquals(PORT, task.communicationHandoff(PORT, false).portId());

        String otherPort = "XCH.1174244c.resp.block-key-array";
        try {
            new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(taskRow(
                    HandoffPhaseContract.phaseId(otherPort, CONSUMER, 1,
                            ELEMENT), otherPort)));
            fail("a handoff of another port is not this task's to answer");
        } catch (IllegalArgumentException refused) {
            String said = String.valueOf(refused.getMessage());
            assertTrue(said, said.contains("undeclared or unsupported"));
            assertTrue("the row is named", said.contains("HOFF."));
        }
    }

    /**
     * A port that crosses on a reference is one attach and several variables.
     *
     * <p>Lanes 17897 and 11741: {@code exportAllKeys} delivers a
     * {@code BlockKey[]}, the mint refused it for not being a primitive, and
     * the planned handoff read as "not reproduced" 12 and 55 times.  What the
     * consumer's formula reads are the leaves, so each leaf is its own
     * handoff occurrence with the leaf in its element path.</p>
     */
    @Test
    public void oneAttachMintsOneVariablePerPrimitiveLeaf() throws Exception {
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

        // A primitive destination is one leaf: itself, unchanged.
        Carrier primitive = new Carrier();
        primitive.i = 119982;
        List<String> own = leafPaths(primitive, "i");
        assertEquals(1, own.size());
        assertTrue(own.get(0), own.get(0).contains("int i"));
        assertTrue("its own signature, unprefixed", own.get(0).startsWith("<"));

        // An array of primitives addresses no field, and says so by silence.
        Carrier primitives = new Carrier();
        primitives.o = new int[] {1, 2, 3};
        assertTrue("the caller names this loss rather than minting",
                leafPaths(primitives, "o").isEmpty());
    }

    /**
     * A value the wire delivered is a carrier, never a root.
     *
     * <p>A cut port gets its meaning from the producer's expression, which
     * the attach installs after the materialization hook asks, so nothing
     * symbolic has reached the local at that moment.  Minting one there
     * would give the formula a free existential per port per consumer;
     * {@code declaredCommunicationCutPort} supplies the refusal.</p>
     */
    @Test
    public void aCutPortWithNothingPropagatedStillRefusesToMint() {
        ConcolicRegionRuntime.SymbolizeAction port = cutPort();
        assertFalse("nothing has reached the local yet",
                ConcolicRegionRuntime.carriesInputAuthority(port, null));
        assertTrue("so the caller must leave it to the attach",
                ConcolicRegionRuntime.declaredCommunicationCutPort(port));
        // Once the attach has landed, the ordinary reuse path takes it.
        assertTrue(ConcolicRegionRuntime.carriesInputAuthority(cutPort(),
                senderSymbol()));
    }

    /** One published row, as the runtime writes it after the mint. */
    private static JsonObject row(String answeredValue) {
        JsonObject producerExpression = new JsonParser().parse(
                "{'_type':'ConsumerBoundaryExpression','eventId':468,"
                + "'boundaryKind':'RPC_ATTACH','_java_type':'I','expression'"
                + ":{'_type':'SymbolExpression','_java_type':'I','_exp':"
                + "'M_I_field_SRC.8c6c_BlockTokenSecretManager'}}")
                .getAsJsonObject();
        return VmHandoffEvidence.event(PORT, 466L, 468L, producerExpression,
                "TASK.SEED.78bb59b2", "hdfs-17899/source-dn#epoch0/region/"
                        + "REGION.d930c3a2#1#a1", CONSUMER,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                "119982", "I", answeredValue, false);
    }

    /** One row as the runtime writes it when the message had no element. */
    private static JsonObject arrivedRow(String answeredValue) {
        return VmHandoffEvidence.event(PORT, 0L, 0L, null, "", "", CONSUMER,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                "119982", "I", answeredValue, true);
    }

    /**
     * The obligation assignment for this handoff occurrence: the phase id is
     * the whole identity of H, so it is also the source id and there is no
     * field signature beside it -- the element path is inside the hash.
     */
    private static ConcolicRegionRuntime.ModelAssignment answer() {
        String phaseId = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        return new ConcolicRegionRuntime.ModelAssignment(new JsonParser()
                .parse("{'engineSymbol':'M_I_field_HOFF.9c1d','inputSymbol':"
                + "'SOURCE_PHASE:" + phaseId + "','valueType':'INT',"
                + "'value':'119981','configuredSourcePhaseId':'" + phaseId
                + "','configuredSourceId':'" + phaseId + "',"
                + "'configuredSourceFieldSignature':''}").getAsJsonObject());
    }

    /**
     * One task row receiving on {@code PORT}, answering {@code phaseId}
     * with a model whose engine symbol is the label of {@code labelPort}.
     */
    private static JsonObject taskRow(String phaseId, String labelPort) {
        return new JsonParser().parse(
                "{'taskId':'TASK.REPLAY.handoff','goalId':'GOAL.1',"
                + "'goalKind':'REGION_PATH_CLOSURE',"
                + "'regionId':'REGION.53092d3e','relationKey':'REL.1',"
                + "'sourceKey':'" + SOURCE + "','occurrenceId':'" + CONSUMER
                + "','rootMethod':'" + RUN + "',"
                + "'instrumentationSelector':'sel',"
                + "'admission':{'state':'EXECUTABLE'},"
                + "'rootSelector':{'kind':'GLOBAL_INVOCATION',"
                + "'invocationOrdinal':1,'method':'" + RUN + "',"
                + "'causalAnchor':{'kind':'REGISTERED_SOURCE',"
                + "'sourceKey':'" + SOURCE + "'}},"
                + "'branches':[],'inputActions':[],"
                + "'loopBound':{'schemaVersion':1},"
                + "'communicationHandoffs':[{'portId':'" + PORT + "',"
                + "'handoffLeafPath':'" + PORT + "','side':'IN',"
                + "'direction':'REQUEST','captureKind':'CALL_RETURN',"
                + "'javaType':'int','declaredCallee':'<a.P: int id()>',"
                + "'definitionMethod':'" + RUN + "',"
                + "'definitionUnitIndex':2}],"
                + "'modelAssignments':[{'engineSymbol':'M_I_field_"
                + HandoffPhaseContract.engineLabelForPhase(phaseId, labelPort)
                + "_a/B$Carrier','inputSymbol':'SOURCE_PHASE:" + phaseId
                + "','valueType':'INT','value':'119980',"
                + "'configuredSourcePhaseId':'" + phaseId + "',"
                + "'configuredSourceId':'" + phaseId + "',"
                + "'configuredSourceFieldSignature':''}]}").getAsJsonObject();
    }

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

    /** One declared cut port, as the finalizer stamps it. */
    private static ConcolicRegionRuntime.SymbolizeAction cutPort() {
        return new ConcolicRegionRuntime.SymbolizeAction(
                new JsonParser().parse("{'symbol':'" + CUT_PORT + "',"
                + "'portId':'" + CUT_PORT + "','javaType':'int',"
                + "'location':'CALL_RETURN','method':'" + CONVERT + "',"
                + "'sourceKind':'COMMUNICATION_SITE_PORT'}")
                .getAsJsonObject());
    }

    /** What the attach installs: the producer's own symbol. */
    private static JsonObject senderSymbol() {
        return new JsonParser().parse("{'_type':'SymbolExpression',"
                + "'_exp':'M_I_REGION.aaa1cfd7','_java_type':'int'}")
                .getAsJsonObject();
    }
}
