package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

/** Content-addressed container identity and materialization. */
public class MapStateContentAddressTest {

    @Test
    public void initialReadTraversesConditionalRemoval() {
        String stateSymbol = "MAP_STATE.v1."
                + "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                + "bbbbbbbbbbbbbbbb";
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "java/util/Map");
        identity.addProperty("_exp", stateSymbol);
        JsonObject state = relation("ASSOCIATIVE", "STATE", identity);
        JsonObject removal = relation("ASSOCIATIVE", "REMOVE_IF", state);
        JsonObject read = relation("ASSOCIATIVE", "READ", removal);
        JsonArray arguments = new JsonArray();
        arguments.add(integer(7));
        read.add("arguments", arguments);

        InitialContainerObservation.Read observation =
                InitialContainerObservation.initialRead(read);
        assertNotNull(observation);
        assertEquals(stateSymbol, observation.inputPort);
    }

    private static JsonObject relation(String shape, String operation,
                                       JsonObject receiver) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ContainerRelation");
        result.addProperty("_java_type", "L");
        result.addProperty("shape", shape);
        result.addProperty("operation", operation);
        result.add("receiver", receiver);
        result.add("arguments", new JsonArray());
        return result;
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }
}
