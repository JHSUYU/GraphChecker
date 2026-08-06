package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
import com.google.gson.Gson;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class MaterializationSpecTest {
    private static final String FIELD = "<example.Box: int value>";
    private static final String METHOD = "<example.Box: int read()>";

    @Test
    public void fieldReadSitesAreCanonicalAndReplaceSingleSiteFields() {
        MaterializationSpec spec = MaterializationSpec.fieldRead(
                "int", FIELD, FIELD,
                Collections.singletonList("value"),
                Collections.<String>emptyList(),
                Arrays.asList(METHOD + "#u7", METHOD + "#u5",
                        METHOD + "#u7"));

        Map<String, Object> encoded = spec.toMap();
        assertEquals(Arrays.asList(METHOD + "#u5", METHOD + "#u7"),
                encoded.get("accessSites"));
        assertFalse(encoded.containsKey("method"));
        assertFalse(encoded.containsKey("unitIndex"));
        assertTrue(spec.matchesAccessSite(METHOD, 5));
        assertTrue(spec.matchesAccessSite(METHOD, 7));
        assertFalse(spec.matchesAccessSite(METHOD, 6));
    }

    @Test(expected = IllegalArgumentException.class)
    public void oldSingleSiteFieldReadSchemaIsRejected() {
        JsonObject port = new JsonObject();
        JsonObject materialization = new JsonObject();
        materialization.addProperty("kind", "FIELD_READ");
        materialization.addProperty("javaType", "int");
        materialization.addProperty("rootField", FIELD);
        materialization.addProperty("leafField", FIELD);
        materialization.addProperty("method", METHOD);
        materialization.addProperty("unitIndex", 5);
        port.add("materialization", materialization);

        MaterializationSpec.decode(port);
    }

    @Test
    public void nestedAccessorPreservesExactRootLeafAndFullPath() {
        String root = "<wire.Response: model.Key currentKey>";
        String leaf = "<model.KeyBase: int keyId>";
        MaterializationSpec spec = MaterializationSpec.accessorReturn(
                "int", root, leaf,
                Arrays.asList("currentKey", "keyId"), METHOD, 9,
                "<wire.Response: model.Key currentKey()>",
                "<wire.Response: model.Key currentKey()>");

        assertEquals(root, spec.rootField());
        assertEquals(leaf, spec.leafField());
        assertEquals(Arrays.asList("currentKey", "keyId"), spec.path());
        assertEquals(root, spec.actionFields().get(
                "accessFieldSignature"));
        assertEquals(leaf, spec.actionFields().get(
                "leafFieldSignature"));
        assertEquals(Arrays.asList("currentKey", "keyId"),
                spec.actionFields().get("fieldPath"));

        JsonObject port = new JsonObject();
        port.add("materialization", new Gson().toJsonTree(
                spec.toMap()).getAsJsonObject());
        MaterializationSpec decoded = MaterializationSpec.decode(port);
        assertEquals(root, decoded.rootField());
        assertEquals(leaf, decoded.leafField());
        assertEquals(spec.path(), decoded.path());
    }

    @Test(expected = IllegalArgumentException.class)
    public void nestedAccessorRejectsTruncatedPath() {
        MaterializationSpec.accessorReturn(
                "int", "<wire.Response: model.Key currentKey>",
                "<model.KeyBase: int keyId>",
                Collections.singletonList("keyId"), METHOD, 9,
                "<wire.Response: model.Key currentKey()>",
                "<wire.Response: model.Key currentKey()>");
    }
}
