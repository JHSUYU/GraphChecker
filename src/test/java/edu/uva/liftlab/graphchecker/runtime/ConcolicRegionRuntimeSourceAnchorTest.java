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
