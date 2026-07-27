package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
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
}
