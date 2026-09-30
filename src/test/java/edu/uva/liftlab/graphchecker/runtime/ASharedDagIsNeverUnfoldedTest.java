package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The replay decodes a VM expression as a shared DAG, and a
 * FieldAccessExpression names its owner twice, so a chain of them is 2^depth
 * nodes as a tree.  Every question the runtime asks of one walks each node
 * once: at depth 40 anything that unfolds it never returns (SOLR-18413's
 * verifyProp selector, 1,060 nodes, was 7.4e10 as a tree).
 */
public class ASharedDagIsNeverUnfoldedTest {
    private static final int DEPTH = 40;
    private static final long SESSION = 7L;

    @Test(timeout = 20000)
    public void aDoublingChainFortyDeepIsAnsweredAtOnce() {
        // Three conditions of one lookupswitch's default arm: the first and
        // third name one selector node, the second an equal chain decoded
        // apart -- one selector either way.
        String envelope = envelope(new int[] {0, 1000, 0},
                chain(0, "s"), chain(1000, "s"), chain(2000, "t"));
        PathConditionWindow window = PathConditionWindow.window(envelope, 0,
                new VmExpressionTable.Store());
        JsonObject event = JsonParser.parseString(
                "{\"opcode\":171,\"codePosition\":\"p\"}").getAsJsonObject();
        JsonArray indices = new JsonArray();
        for (int index = 0; index < 3; index++) indices.add(index);
        VmBranchAttestation.Attestation attested =
                VmBranchAttestation.attestSwitchConditions(event,
                        BranchObservation.SwitchExpectation.parse(
                                "LOOKUP_SWITCH", "1,2,3", 3),
                        indices, window);
        assertTrue(attested.error, attested.valid);
        assertEquals(Arrays.asList(0, 1, 2), attested.conditionIndices);

        JsonObject one = selector(window, 0);
        assertFalse("the two chains are two nodes", one == selector(window, 1));
        assertTrue(VmBranchAttestation.sameExpression(one,
                selector(window, 1)));
        // Another leaf symbol is another selector.
        String other = envelope(new int[] {0, 2000, 0},
                chain(0, "s"), chain(1000, "s"), chain(2000, "t"));
        PathConditionWindow apart = PathConditionWindow.window(other, 0,
                new VmExpressionTable.Store());
        assertFalse(VmBranchAttestation.sameExpression(selector(apart, 0),
                selector(apart, 1)));

        // A refusal quotes the member it refused, cut, not whole.
        try {
            JsonFields.optionalString(one, "owner");
            fail("an object member is not a string");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().length() < 1024);
            assertTrue(refused.getMessage().contains("...,"));
        }
    }

    private static JsonObject selector(PathConditionWindow window, int index) {
        return window.get(index).getAsJsonObject().getAsJsonObject("_left");
    }

    /** One chain's definitions: a symbol, then DEPTH field accesses, each
     *  naming the one below as owner and concrete owner. */
    private static String chain(int base, String symbol) {
        StringBuilder definitions = new StringBuilder(definition(base + 1,
                "{\"_type\":\"SymbolExpression\",\"_exp\":\"" + symbol
                        + "\",\"_java_type\":\"I\"}"));
        for (int level = 2; level <= DEPTH + 1; level++) {
            definitions.append(',').append(definition(base + level,
                    "{\"_type\":\"FieldAccessExpression\",\"owner\":"
                            + reference(base + level - 1)
                            + ",\"concreteOwner\":"
                            + reference(base + level - 1)
                            + ",\"_java_type\":\"I\"}"));
        }
        return definitions.toString();
    }

    /** A CONCOLIC_PATH_CONDITION_RANGE of {@code selector != k}, k = 1.., the
     *  i-th over the chain based at {@code bases[i]}. */
    private static String envelope(int[] bases, String... chains) {
        StringBuilder conditions = new StringBuilder();
        for (int index = 0; index < bases.length; index++) {
            if (index > 0) conditions.append(',');
            conditions.append("{\"_type\":\"BinaryExpression\",\"_op\":\"!=\","
                    + "\"_left\":").append(reference(bases[index] + DEPTH + 1))
                    .append(",\"_right\":{\"_type\":\"ConstExpr\",\"_exp\":"
                            + "\"Y_I_").append(index + 1).append("\"}}");
        }
        return "{\"startIndex\":0,\"endIndex\":" + bases.length
                + ",\"pathConditionWatermark\":" + bases.length
                + ",\"conditionCount\":" + bases.length
                + ",\"conditions\":[" + conditions + "],"
                + "\"vmExpressionTable\":{\"schemaVersion\":1,"
                + "\"kind\":\"" + VmExpressionTable.KIND + "\",\"authority\":\""
                + VmExpressionTable.AUTHORITY + "\",\"sessionId\":" + SESSION
                + ",\"definitionCount\":" + chains.length * (DEPTH + 1)
                + ",\"definitions\":[" + String.join(",", chains) + "]}}";
    }

    private static String definition(int id, String expression) {
        return "{\"_type\":\"" + VmExpressionTable.DEFINITION_TYPE
                + "\",\"sessionId\":" + SESSION + ",\"expressionId\":" + id
                + ",\"expression\":" + expression + "}";
    }

    private static String reference(int id) {
        return "{\"_type\":\"" + VmExpressionTable.REFERENCE_TYPE
                + "\",\"sessionId\":" + SESSION + ",\"expressionId\":" + id
                + "}";
    }
}
