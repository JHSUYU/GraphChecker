package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Human-authored hypotheses that are deliberately outside automatic symbolic
 * execution.  This registry is separate from the HDFS port mapper so the
 * mapper cannot silently attach domain semantics to a region or edge.
 */
public final class HdfsExplicitContracts {
    private HdfsExplicitContracts() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Path parent = arguments.output.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        JsonObject registry = registry(arguments.scope);
        String json = new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create().toJson(registry);
        Files.write(arguments.output,
                (json + System.lineSeparator()).getBytes(
                        StandardCharsets.UTF_8), StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
        System.out.println(json);
    }

    static JsonObject registry(HdfsRegionPortMapper.ResearchScope scope) {
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
        result.add("researchScope", scope.toJson());
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

    static final class Arguments {
        private final Path output;
        private final HdfsRegionPortMapper.ResearchScope scope;

        private Arguments(Path output,
                          HdfsRegionPortMapper.ResearchScope scope) {
            this.output = output;
            this.scope = scope;
        }

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; argv != null && index < argv.length; index++) {
                String key = argv[index];
                if (!key.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + key);
                }
                values.put(key.substring(2), argv[++index]);
            }
            String output = values.get("output");
            if (output == null || output.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --output");
            }
            return new Arguments(Paths.get(output),
                    HdfsRegionPortMapper.ResearchScope.parse(values));
        }

        HdfsRegionPortMapper.ResearchScope researchScope() {
            return scope;
        }
    }
}
