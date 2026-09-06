package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;

public class ConfiguredSourcePhaseContractTest {
    private static final String METHOD = "<example.Keys: void rotate()>";
    private static final String FIELD = "<example.Key: int keyId>";

    @Test
    public void occurrenceCarriesStableExactPhaseAndCallAncestry() {
        JsonObject encoded = ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "ROTATING.KEY", FIELD, METHOD, 7);
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(
                        rows(encoded)).get(0);

        JsonObject first = ConfiguredSourcePhaseContract.occurrence(
                declaration, "node/nn0#epoch1/region/REGION.KEYS#3",
                2, 101, 30, 91, "<example.Hook: void publish()>",
                Arrays.asList(30L, 20L, 10L));
        JsonObject repeated =
                ConfiguredSourcePhaseContract.occurrence(
                        declaration,
                        "node/nn0#epoch1/region/REGION.KEYS#3",
                        2, 201, 30, 191,
                        "<example.Hook: void publish()>",
                        Arrays.asList(30L, 20L, 10L));

        assertEquals(first.get("phaseId"), repeated.get("phaseId"));
        assertEquals("PUBLISH", first.get("phaseKind").getAsString());
        assertEquals("ROTATING.KEY", first.get("sourceId").getAsString());
        assertEquals(FIELD, first.get("fieldSignature").getAsString());
        assertEquals(METHOD + "#u7", first.get("siteId").getAsString());
        assertEquals(101L, first.get("eventSeq").getAsLong());
        assertEquals(30L, first.get("ownerCallId").getAsLong());
        assertEquals(91L, first.get("invocationId").getAsLong());
        assertEquals(Arrays.asList(30L, 20L, 10L),
                callIds(first.getAsJsonArray("enclosingCallIds")));
        ConfiguredSourcePhaseContract.Occurrence decoded =
                ConfiguredSourcePhaseContract.occurrencesOf(
                        rows(first)).get(0);
        assertEquals("PUBLISH", decoded.phase().name());
        assertEquals(first.get("phaseId").getAsString(), decoded.phaseId());
        assertEquals("ROTATING.KEY", decoded.sourceId());
        assertEquals(FIELD, decoded.fieldSignature());
        assertEquals(Arrays.asList(30L, 20L, 10L),
                decoded.enclosingCallIds());
    }

    /** The one wire form a phase catalog is decoded from. */
    private static JsonArray rows(JsonObject... phases) {
        JsonArray encoded = new JsonArray();
        for (JsonObject phase : phases) encoded.add(phase);
        return encoded;
    }

    private static java.util.List<Long> callIds(JsonArray encoded) {
        java.util.List<Long> result = new java.util.ArrayList<>();
        for (com.google.gson.JsonElement value : encoded) {
            result.add(value.getAsLong());
        }
        return result;
    }

}
