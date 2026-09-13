package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.SharedExpressionTable;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Test;

import static java.util.Collections.singletonList;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Source evidence used to replay one exact region occurrence. */
public class ConcolicRegionRuntimeSourceAnchorTest {
    private static final String EXPECTED = "dn0#epoch0";
    private static final SourceRef DN0_REPLAY =
            new SourceRef("DATANODE", "dn", "dn0", 7L);
    private static final SourceRef NN0_REPLAY =
            new SourceRef("NAMENODE", "nn", "nn0", 7L);

    @After
    public void clearMessageState() {
        SymbolicMessageEnvelope.clear();
    }

    @Test
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

    @Test
    public void messageProducerCanAddressConsumerBeforeAttachConsumesIt() {
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 0L,
                "task-1", "producer#1#a3",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 42L,
                "task-2", "producer#2#a1",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertFalse(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#2", "consumer#1"));
        assertTrue(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#1", "consumer#1"));
        assertTrue(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#1", "consumer#1"));
        assertFalse(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#1", "consumer#2"));
        assertEquals(0L, SymbolicMessageEnvelope.take("block-key").handle());
        assertTrue(ConcolicRegionRuntime.inboundMessageMatches(
                "block-key", "producer#2", "consumer#1"));
    }

    @Test
    public void everyPlannedInputMustBeInTheCurrentMessage() {
        Map<String, String> producers = new LinkedHashMap<>();
        producers.put("block-key", "block-producer#1");
        producers.put("data-key", "data-producer#1");

        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "block-task", "block-producer#1",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, producers, "consumer#1", false));

        SymbolicMessageEnvelope.clear();
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "block-task", "block-producer#1",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("data-key", 42L,
                "data-task", "wrong-producer#1",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertFalse(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, producers, "consumer#1", false));

        SymbolicMessageEnvelope.clear();
        assertTrue(SymbolicMessageEnvelope.stage("block-key", 41L,
                "block-task", "block-producer#1",
                singletonList("consumer#1")));
        assertTrue(SymbolicMessageEnvelope.stage("data-key", 42L,
                "data-task", "data-producer#1#a2",
                singletonList("consumer#1")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertTrue(ConcolicRegionRuntime.rootInvocationAddressMatches(
                99, 1, producers, "consumer#1", false));
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
