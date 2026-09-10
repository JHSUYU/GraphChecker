package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class ConcolicContainerMaterializationTest {
    @Test
    public void writesHashMapValueAtItsCurrentIterationFrontier() {
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("selectorKind", "ITERATION_INDEX");
        target.addProperty("index", 1);
        target.addProperty("projection", "VALUE");
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "container.cell");
        encoded.addProperty("engineSymbol", "container.cell");
        encoded.addProperty("inputSymbol", "map.input");
        encoded.addProperty("valueType", "NULL");
        encoded.addProperty("value", "null");
        encoded.add("containerTarget", target);

        Map<String, Object> values = new HashMap<>();
        values.put("first", new Object());
        values.put("second", new Object());
        String selectedKey = new ArrayList<>(values.keySet()).get(1);
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(
                values, assignment));
        assertNull(values.get(selectedKey));
    }
}
