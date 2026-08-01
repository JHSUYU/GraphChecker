package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.zip.GZIPInputStream;

/** Builds executable region state exclusively from a runtime-refined graph. */
public final class RuntimeSelectedRegionFinalizer {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();
    private static final String REFINED_KIND = "RUNTIME_REFINED_DATAFLOW";

    private RuntimeSelectedRegionFinalizer() {
    }

    public static void finalizeRegions(
            File refinedGraph, File selectedSkeletons, File regions,
            File regionEdges, Collection<String> observedMethods)
            throws IOException {
        List<Map<String, Object>> graph = read(refinedGraph);
        List<Map<String, Object>> skeletons = read(selectedSkeletons);
        requireRefinedGraph(graph, refinedGraph);
        Set<String> observed = new LinkedHashSet<>();
        if (observedMethods != null) {
            observed.addAll(observedMethods);
        }

        StaticProgram result = new StaticProgram();
        Map<String, Map<String, Object>> skeletonById = new LinkedHashMap<>();
        Map<String, List<Map<String, Object>>> edgesByRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> skeleton : skeletons) {
            requireSkeleton(skeleton, selectedSkeletons);
            skeletonById.put(text(skeleton.get("regionId")), skeleton);
        }
        for (Map<String, Object> edge : graph) {
            for (String region : strings(edge.get("regionIds"))) {
                edgesByRegion.computeIfAbsent(region,
                        ignored -> new ArrayList<>()).add(edge);
            }
        }

        for (Map.Entry<String, Map<String, Object>> entry
                : skeletonById.entrySet()) {
            String regionId = entry.getKey();
            Map<String, Object> skeleton = entry.getValue();
            List<String> methods = strings(skeleton.get("methods"));
            if (!observed.isEmpty()) {
                methods.removeIf(method -> !observed.contains(method));
            }
            if (methods.isEmpty()) {
                continue;
            }
            Map<String, Object> region = new LinkedHashMap<>();
            region.put("schemaVersion", 3);
            region.put("kind", "SYMBOLIC_REGION");
            region.put("graphKind", REFINED_KIND);
            region.put("regionId", regionId);
            region.put("rootMethod", skeleton.get("rootMethod"));
            region.put("anchorMethod", skeleton.get("anchorMethod"));
            region.put("selection", skeleton.get("selection"));
            region.put("methods", methods);

            List<Map<String, Object>> regionGraph = edgesByRegion.getOrDefault(
                    regionId, Collections.emptyList());
            List<Map<String, Object>> inputs = statePorts(regionId,
                    regionGraph, "HEAP_READ", "IN");
            inputs.addAll(protocolPorts(regionId, regionGraph, "IN"));
            List<Map<String, Object>> outputs = statePorts(regionId,
                    regionGraph, "HEAP_WRITE", "OUT");
            outputs.addAll(protocolPorts(regionId, regionGraph, "OUT"));
            region.put("symbolicInputs", inputs);
            region.put("outputs", outputs);
            region.put("branchPolicies", branches(regionGraph));
            result.regions.add(region);
        }
        result.regionEdges.addAll(fieldFlows(result.regions));
        result.regionEdges.addAll(protocolFlows(graph));
        CausynthArtifactWriter.writeRegions(regions.toPath(),
                regionEdges.toPath(), result);
    }

    private static List<Map<String, Object>> protocolPorts(
            String regionId, List<Map<String, Object>> edges,
            String direction) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"PROTOCOL_TRANSFER".equals(
                    text(edge.get("transferKind")))) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeProtocolBindings"))) {
                String boundRegion = "OUT".equals(direction)
                        ? text(binding.get("fromRegionId"))
                        : text(binding.get("toRegionId"));
                if (!regionId.equals(boundRegion)) {
                    continue;
                }
                String cellKey = "OUT".equals(direction)
                        ? "fromCell" : "toCell";
                String key = text(binding.get("mappingId")) + "\n"
                        + text(binding.get("wireId")) + "\n"
                        + text(binding.get("port")) + "\n"
                        + text(binding.get(cellKey)) + "\n"
                        + text(binding.get("fromRootCallId")) + "\n"
                        + text(binding.get("toRootCallId"));
                Map<String, Object> port = new LinkedHashMap<>(binding);
                port.put("portId", protocolPortId(regionId, direction,
                        binding));
                port.put("cell", binding.get(cellKey));
                port.put("sourceKind", "PROTOCOL_INPUT");
                port.put("transportKind", binding.get("transport"));
                port.put("protocolDirection", binding.get("direction"));
                if ("IN".equals(direction)
                        && "REQUEST".equals(text(binding.get("direction")))) {
                    port.put("argumentIndex",
                            edge.get("protocolServerParameter"));
                }
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    private static String protocolPortId(String regionId, String direction,
                                         Map<String, Object> binding) {
        String identity = regionId + "\n" + direction + "\n"
                + text(binding.get("mappingId")) + "\n"
                + text(binding.get("wireId")) + "\n"
                + text(binding.get("port")) + "\n"
                + text(binding.get("fromRootCallId")) + "\n"
                + text(binding.get("toRootCallId"));
        return regionId + ("IN".equals(direction) ? ".in." : ".out.")
                + UUID.nameUUIDFromBytes(identity.getBytes(
                StandardCharsets.UTF_8));
    }

    private static List<Map<String, Object>> protocolFlows(
            List<Map<String, Object>> graph) {
        List<Map<String, Object>> result = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (Map<String, Object> edge : graph) {
            if (!"PROTOCOL_TRANSFER".equals(
                    text(edge.get("transferKind")))) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeProtocolBindings"))) {
                String fromRegion = text(binding.get("fromRegionId"));
                String toRegion = text(binding.get("toRegionId"));
                if (fromRegion.isEmpty() || toRegion.isEmpty()) {
                    continue;
                }
                String identity = text(binding.get("mappingId")) + "\n"
                        + text(binding.get("wireId")) + "\n"
                        + text(binding.get("port")) + "\n"
                        + text(binding.get("fromCell")) + "\n"
                        + text(binding.get("toCell")) + "\n"
                        + text(binding.get("fromRootCallId")) + "\n"
                        + text(binding.get("toRootCallId"));
                if (!seen.add(identity)) {
                    continue;
                }
                Map<String, Object> flow = new LinkedHashMap<>(binding);
                flow.put("schemaVersion", 3);
                flow.put("kind", "RUNTIME_PROTOCOL_FLOW");
                flow.put("transportKind", binding.get("transport"));
                flow.put("edgeId", "RP." + UUID.nameUUIDFromBytes(
                        identity.getBytes(StandardCharsets.UTF_8)));
                flow.put("fromRegion", fromRegion);
                flow.put("toRegion", toRegion);
                flow.put("fromPort", protocolPortId(fromRegion, "OUT",
                        binding));
                flow.put("toPort", protocolPortId(toRegion, "IN", binding));
                result.add(flow);
            }
        }
        return result;
    }

    private static List<Map<String, Object>> statePorts(
            String regionId, List<Map<String, Object>> edges,
            String transfer, String prefix) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!transfer.equals(text(edge.get("transferKind")))) {
                continue;
            }
            for (Map<String, Object> binding
                    : rows(edge.get("runtimeFieldBindings"))) {
                if (!regionId.equals(text(binding.get("regionId")))) {
                    continue;
                }
                String key = text(binding.get("rootCallId")) + "\n"
                        + text(binding.get("rootCell")) + "\n"
                        + strings(binding.get("fieldPath"));
                Map<String, Object> port = new LinkedHashMap<>(binding);
                String direction = "IN".equals(prefix) ? ".in." : ".out.";
                port.put("portId", regionId + direction
                        + UUID.nameUUIDFromBytes(
                        (regionId + "\n" + key).getBytes(
                                StandardCharsets.UTF_8)));
                port.put("cell", binding.get("rootCell"));
                port.put("transportKind", "HEAP");
                port.put("sourceKind", "PARAMETER".equals(
                        text(binding.get("rootKind")))
                        ? "ROOT_ARGUMENT" : "RECEIVER_FIELD");
                unique.put(key, port);
            }
        }
        return new ArrayList<>(unique.values());
    }

    private static List<Map<String, Object>> branches(
            List<Map<String, Object>> edges) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            if (!"GUARD".equals(text(edge.get("transferKind")))) {
                continue;
            }
            String site = first(text(edge.get("guardSiteId")),
                    text(edge.get("siteId")));
            Map<String, Object> branch = new LinkedHashMap<>();
            branch.put("siteId", site);
            branch.put("method", edge.get("method"));
            branch.put("unitIndex", number(edge.get("unitIndex"), -1));
            branch.put("requiredOutcome", edge.get("requiredOutcome"));
            branch.put("policy", "EXPLORE");
            unique.put(site, branch);
        }
        return new ArrayList<>(unique.values());
    }

    private static List<Map<String, Object>> fieldFlows(
            List<Map<String, Object>> regions) {
        List<BoundPort> writes = new ArrayList<>();
        List<BoundPort> reads = new ArrayList<>();
        for (Map<String, Object> region : regions) {
            collectPorts(writes, text(region.get("regionId")),
                    rows(region.get("outputs")));
            collectPorts(reads, text(region.get("regionId")),
                    rows(region.get("symbolicInputs")));
        }
        List<Map<String, Object>> result = new ArrayList<>();
        for (BoundPort write : writes) {
            for (BoundPort read : reads) {
                if (write.region.equals(read.region)
                        || !write.process.equals(read.process)
                        || write.receiver != read.receiver
                        || !write.declarations.equals(read.declarations)
                        || write.seq > read.seq) {
                    continue;
                }
                Map<String, Object> edge = new LinkedHashMap<>();
                edge.put("schemaVersion", 3);
                edge.put("kind", "RUNTIME_FIELD_FLOW");
                edge.put("transportKind", "HEAP");
                edge.put("edgeId", "RF." + UUID.nameUUIDFromBytes(
                        (write.region + write.port + read.region + read.port)
                                .getBytes(StandardCharsets.UTF_8)));
                edge.put("fromRegion", write.region);
                edge.put("toRegion", read.region);
                edge.put("fromPort", write.port);
                edge.put("toPort", read.port);
                edge.put("fromRootCallId", write.rootCallId);
                edge.put("toRootCallId", read.rootCallId);
                edge.put("receiverObjectId", write.receiver);
                edge.put("writerEventSeq", write.seq);
                edge.put("readerEventSeq", read.seq);
                edge.put("fieldPathDeclarations", write.declarations);
                result.add(edge);
            }
        }
        return result;
    }

    private static void collectPorts(List<BoundPort> target, String region,
                                     List<Map<String, Object>> ports) {
        for (Map<String, Object> port : ports) {
            if (!"HEAP".equals(text(port.get("transportKind")))) {
                continue;
            }
            target.add(new BoundPort(region, text(port.get("portId")),
                    text(port.get("process")),
                    longNumber(port.get("rootCallId"), 0L),
                    number(port.get("fieldReceiverObjectId"), 0),
                    longNumber(port.get("eventSeq"), 0L),
                    strings(port.get("fieldPathDeclarations"))));
        }
    }

    private static void requireRefinedGraph(
            List<Map<String, Object>> rows, File source) throws IOException {
        if (rows.isEmpty()) {
            throw new IOException("refined graph is empty: " + source);
        }
        for (Map<String, Object> row : rows) {
            if (number(row.get("schemaVersion"), -1) != 3
                    || number(row.get("refinementSchemaVersion"), -1) != 1
                    || !REFINED_KIND.equals(text(row.get("graphKind")))) {
                throw new IOException("full region planning requires a "
                        + "schema-3 runtime-refined graph: " + source);
            }
        }
    }

    private static void requireSkeleton(Map<String, Object> row, File source)
            throws IOException {
        if (number(row.get("schemaVersion"), -1) != 3
                || !"REGION_SKELETON".equals(text(row.get("kind")))) {
            throw new IOException("invalid selected skeleton: " + source);
        }
    }

    private static List<Map<String, Object>> read(File file)
            throws IOException {
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader reader = reader(file)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.trim().isEmpty()) {
                    Map<String, Object> row = GSON.fromJson(line, ROW);
                    if (row == null) {
                        throw new IOException("null row in " + file);
                    }
                    result.add(row);
                }
            }
        }
        return result;
    }

    private static BufferedReader reader(File file) throws IOException {
        InputStream input = Files.newInputStream(file.toPath());
        if (file.getName().endsWith(".gz")) {
            input = new GZIPInputStream(input);
        }
        return new BufferedReader(new InputStreamReader(input,
                StandardCharsets.UTF_8));
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map<?, ?>) {
                    result.add((Map<String, Object>) item);
                }
            }
        }
        return result;
    }

    private static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                String text = text(item);
                if (!text.isEmpty()) {
                    result.add(text);
                }
            }
        }
        return result;
    }

    private static int number(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue()
                : fallback;
    }

    private static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue()
                : fallback;
    }

    private static String first(String left, String right) {
        return left.isEmpty() ? right : left;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    private static final class BoundPort {
        private final String region;
        private final String port;
        private final String process;
        private final long rootCallId;
        private final int receiver;
        private final long seq;
        private final List<String> declarations;

        private BoundPort(String region, String port, String process,
                          long rootCallId, int receiver, long seq,
                          List<String> declarations) {
            this.region = region;
            this.port = port;
            this.process = process;
            this.rootCallId = rootCallId;
            this.receiver = receiver;
            this.seq = seq;
            this.declarations = declarations;
        }
    }
}
