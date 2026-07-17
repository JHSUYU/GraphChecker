package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

/**
 * Human-authored hypotheses that are deliberately outside automatic symbolic
 * execution.  This registry is separate from the HDFS port mapper so the
 * mapper cannot silently attach domain semantics to a region or edge.
 */
public final class HdfsExplicitContracts {
    private HdfsExplicitContracts() {
    }

    public static void main(String[] argv) throws Exception {
        Path output = null;
        for (int index = 0; index < argv.length; index++) {
            if ("--output".equals(argv[index]) && index + 1 < argv.length) {
                output = Paths.get(argv[++index]);
            }
        }
        if (output == null) {
            throw new IllegalArgumentException("Missing --output");
        }
        Path parent = output.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        JsonObject registry = registry();
        String json = new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(registry);
        Files.write(output, (json + System.lineSeparator()).getBytes(
                        StandardCharsets.UTF_8), StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
        System.out.println(json);
    }

    static JsonObject registry() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "EXPLICIT_CONTRACT_REGISTRY");
        result.addProperty("eligibleAsRegionSummary", false);
        result.addProperty("eligibleForAutomaticDerivation", false);
        result.addProperty("includedInSmt", false);
        JsonArray contracts = new JsonArray();
        contracts.add(contract("HDFS.CODEC.ROUND_TRIP",
                "Codec round-trip preserves the transported key id"));
        contracts.add(contract("HDFS.CACHE.REFRESH_POLICY",
                "Cached encryption-key refresh policy"));
        contracts.add(contract("HDFS.MAP.EXPIRY_MEMBERSHIP",
                "Map membership as a function of observation and expiry time"));
        result.add("contracts", contracts);
        JsonObject scope = new JsonObject();
        scope.addProperty("repository", "/Users/lizhenyu/Desktop/study/hadoop");
        scope.addProperty("commit",
                "ece33208b89a6a06c1b362d10fab31343fe5df13");
        scope.addProperty("test", "org.apache.hadoop.hdfs.server.balancer."
                + "TestBalancerWithEncryptedTransfer#testEncryptedBalancer1");
        scope.addProperty("experimentalSourcePatch",
                "CAUSYNTH_FIXED_MINIDFSCLUSTER_LOOP_FREE_V1");
        scope.addProperty("experimentalSourceSha256",
                "352efc4dd9a3d4e0df4d0840754d63fce1a09509ad947f9c232e24f35372bb93");
        scope.addProperty("executionBoundary", "LOCAL_MINIDFSCLUSTER_ONLY");
        scope.addProperty("thirdPartySystemsProhibited", true);
        result.add("researchScope", scope);
        return result;
    }

    private static JsonObject contract(String id, String hypothesis) {
        JsonObject result = new JsonObject();
        result.addProperty("contractId", id);
        result.addProperty("kind", "EXPLICIT_CONTRACT");
        result.addProperty("hypothesis", hypothesis);
        result.addProperty("status", "REQUIRES_REAL_REGION_SUMMARIES");
        result.addProperty("reason",
                "NOT_AUTOMATICALLY_DERIVED_BY_CURRENT_CONCOLIC_CLOSURE");
        result.addProperty("eligibleForAutomaticDerivation", false);
        result.addProperty("includedInSmt", false);
        result.addProperty("mayBeReportedAsSymbolicExecutionResult", false);
        return result;
    }
}
