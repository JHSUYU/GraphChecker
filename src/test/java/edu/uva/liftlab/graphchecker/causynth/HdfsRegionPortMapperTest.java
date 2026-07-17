package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class HdfsRegionPortMapperTest {
    @Test
    public void explicitContractRegistryCannotMasqueradeAsAutomaticResults() {
        JsonObject registry = HdfsExplicitContracts.registry();
        assertFalse(registry.get("eligibleForAutomaticDerivation")
                .getAsBoolean());
        assertFalse(registry.get("includedInSmt").getAsBoolean());
        assertFalse(registry.getAsJsonArray("contracts").isEmpty());
        for (JsonElement element : registry.getAsJsonArray("contracts")) {
            JsonObject contract = element.getAsJsonObject();
            assertTrue("EXPLICIT_CONTRACT".equals(
                    contract.get("kind").getAsString()));
            assertFalse(contract.get("eligibleForAutomaticDerivation")
                    .getAsBoolean());
            assertFalse(contract.get("includedInSmt").getAsBoolean());
            assertFalse(contract.get(
                    "mayBeReportedAsSymbolicExecutionResult")
                    .getAsBoolean());
        }
    }

    @Test
    public void datanodeMapPortUsesExactDeclaredFieldNotRpcProjection() {
        String exact = "<org.apache.hadoop.hdfs.security.token.block."
                + "BlockTokenSecretManager: java.util.Map allKeys>";
        JsonObject region = new JsonObject();
        JsonArray inputs = new JsonArray();
        inputs.add(port("REGION.0.in.21",
                "<org.apache.hadoop.hdfs.server.protocol.NamenodeProtocol: "
                        + "org.apache.hadoop.hdfs.security.token.block."
                        + "ExportedBlockKeys getBlockKeys()>.return"
                        + "#field:allKeys"));
        inputs.add(port("REGION.0.in.22", exact));
        inputs.add(port("REGION.0.in.23", exact + "#field:size"));
        region.add("symbolicInputs", inputs);

        assertEquals("REGION.0.in.22",
                HdfsRegionPortMapper.findExactCellPort(region,
                        "symbolicInputs", exact));

        inputs.add(port("REGION.0.in.24", exact));
        assertEquals("", HdfsRegionPortMapper.findExactCellPort(region,
                "symbolicInputs", exact));
    }

    private static JsonObject port(String id, String cell) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", id);
        result.addProperty("cell", cell);
        return result;
    }
}
