package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
import com.google.gson.Gson;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;

public class MaterializationSpecTest {
    private static final String FIELD = "<example.Box: int value>";
    private static final String METHOD = "<example.Box: int read()>";

    @Test
    public void flatAccessorPortDecodesWithoutDuplicateMaterialization() {
        JsonObject port = new JsonObject();
        port.addProperty("sourceKind", "ACCESSOR_RETURN");
        port.addProperty("javaType", "int");
        port.addProperty("cell", FIELD);
        port.addProperty("declaredFieldSignature", FIELD);
        port.add("fieldPath", new Gson().toJsonTree(
                Collections.singletonList("value")));
        port.addProperty("callerMethod", METHOD);
        port.addProperty("unitIndex", 5);
        port.addProperty("declaredCallee",
                "<example.Box: int read()>");
        port.addProperty("accessorImplementationMethod",
                "<example.Box: int read()>");

        MaterializationSpec decoded = MaterializationSpec.decode(port);

        assertEquals(MaterializationSpec.Kind.ACCESSOR_RETURN,
                decoded.kind());
        assertEquals(FIELD, decoded.leafField());
        assertEquals(Collections.singletonList("value"), decoded.path());
        assertEquals("FIELD_ACCESS", decoded.actionFields().get(
                "bindingMode"));
        assertEquals("int", MaterializationSpec.logicalJavaType(port));
    }
}
