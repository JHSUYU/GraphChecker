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
        JsonObject registry = HdfsExplicitContracts.registry(
                mapperArguments().researchScope());
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
    public void cliScopeIsSharedWithoutLegacyHostDefaults() {
        JsonObject mapperScope = mapperArguments().researchScope().toJson();
        HdfsExplicitContracts.Arguments contractArguments =
                HdfsExplicitContracts.Arguments.parse(contractArguments());
        JsonObject contractScope = HdfsExplicitContracts.registry(
                contractArguments.researchScope())
                .getAsJsonObject("researchScope");

        assertEquals(mapperScope, contractScope);
        assertEquals("/opt/hadoop",
                mapperScope.get("repository").getAsString());
        assertEquals("ece33208b89a6a06c1b362d10fab31343fe5df13",
                mapperScope.get("commit").getAsString());
        assertEquals("org.apache.hadoop.hdfs.server.balancer."
                        + "TestBalancerWithEncryptedTransfer"
                        + "#testEncryptedBalancer1",
                mapperScope.get("test").getAsString());
        assertEquals("UPSTREAM_PRE_HDFS_11741",
                mapperScope.get("experimentalSourcePatch").getAsString());
        assertEquals(
                "be9ce1a57980fdab5612abed1886362842099e1df657b0cdb8c95dbb0a480093",
                mapperScope.get("experimentalSourceSha256").getAsString());
        assertFalse(mapperScope.toString().contains("/Users/"));
    }

    @Test
    public void cliScopeRequiresEveryProvenanceValue() {
        String[] incomplete = {
                "--output", "contracts.json",
                "--scope-repository", "/opt/hadoop",
                "--scope-commit", "commit",
                "--scope-workload", "test",
                "--scope-patch", "patch"
        };
        try {
            HdfsExplicitContracts.Arguments.parse(incomplete);
        } catch (IllegalArgumentException exception) {
            assertEquals("Missing --scope-source-sha256",
                    exception.getMessage());
            return;
        }
        throw new AssertionError("missing scope SHA must be rejected");
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

    private static HdfsRegionPortMapper.Arguments mapperArguments() {
        return HdfsRegionPortMapper.Arguments.parse(new String[]{
                "--regions", "regions.jsonl",
                "--runtime-report", "runtime.json",
                "--fatal-query", "queries.jsonl",
                "--merge-plan", "merge.json",
                "--output", "port-map.json",
                "--scope-repository", "/opt/hadoop",
                "--scope-commit",
                "ece33208b89a6a06c1b362d10fab31343fe5df13",
                "--scope-workload", "org.apache.hadoop.hdfs.server.balancer."
                        + "TestBalancerWithEncryptedTransfer"
                        + "#testEncryptedBalancer1",
                "--scope-patch", "UPSTREAM_PRE_HDFS_11741",
                "--scope-source-sha256",
                "be9ce1a57980fdab5612abed1886362842099e1df657b0cdb8c95dbb0a480093"
        });
    }

    private static String[] contractArguments() {
        return new String[]{
                "--output", "contracts.json",
                "--scope-repository", "/opt/hadoop",
                "--scope-commit",
                "ece33208b89a6a06c1b362d10fab31343fe5df13",
                "--scope-workload", "org.apache.hadoop.hdfs.server.balancer."
                        + "TestBalancerWithEncryptedTransfer"
                        + "#testEncryptedBalancer1",
                "--scope-patch", "UPSTREAM_PRE_HDFS_11741",
                "--scope-source-sha256",
                "be9ce1a57980fdab5612abed1886362842099e1df657b0cdb8c95dbb0a480093"
        };
    }
}
