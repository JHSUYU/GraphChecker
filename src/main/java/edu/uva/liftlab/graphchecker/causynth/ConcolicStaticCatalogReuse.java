package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Loads the small, immutable subset of a completed static catalog needed by
 * one activation-specific concolic instrumentation pass.
 *
 * <p>The loader is deliberately independent of HDFS names.  It accepts only
 * a hash-bound catalog family and a scheduler plan that was produced from the
 * same regions/static graph.  It never writes into the frozen catalog.</p>
 */
final class ConcolicStaticCatalogReuse {
    static final int SCHEMA_VERSION = 1;
    static final String KIND = "CONCOLIC_FROZEN_STATIC_CATALOG";
    static final String AUTHORITY =
            "HASHED_STATIC_CATALOG_CLASS_TREES_AND_SCHEDULE_INPUTS_V1";
    static final String SCHEDULE_KIND = "CONCOLIC_SCHEDULE_INPUT_PROVENANCE";
    static final String SCHEDULE_FILE = "schedule_input_provenance.json";

    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().setPrettyPrinting()
            .create();

    private ConcolicStaticCatalogReuse() {
    }

    static LoadedCatalog load(Path manifestPath, Path activationPlan,
                              String selectedActivationId)
            throws IOException {
        Path manifest = regularFile(manifestPath, "static reuse manifest");
        Path plan = regularFile(activationPlan, "activation plan");
        String selected = safe(selectedActivationId);
        if (selected.isEmpty() || "ALL".equals(selected)) {
            throw new IOException("Frozen static reuse v1 requires one exact "
                    + "activation id");
        }

        JsonObject manifestJson = readObject(manifest, "static reuse manifest");
        requireInt(manifestJson, "schemaVersion", SCHEMA_VERSION,
                "static reuse manifest");
        requireString(manifestJson, "kind", KIND,
                "static reuse manifest");
        requireString(manifestJson, "authority", AUTHORITY,
                "static reuse manifest");
        requireBoolean(manifestJson, "complete", true,
                "static reuse manifest");
        String sourceRevision = requiredString(manifestJson,
                "sourceRevision", "static reuse manifest");

        JsonObject artifacts = object(manifestJson, "artifacts",
                "static reuse manifest");
        FileArtifact regions = readFileArtifact(artifacts, "regions");
        FileArtifact coverage = readFileArtifact(artifacts, "coverage");
        FileArtifact staticGraph = readFileArtifact(artifacts, "staticGraph");
        FileArtifact regionEdges = readFileArtifact(artifacts, "regionEdges");
        FileArtifact targetSpec = readFileArtifact(artifacts, "targetSpec");
        FileArtifact processProvenance = readFileArtifact(artifacts,
                "staticProcessProvenance");
        TreeArtifact originalClasses = readTreeArtifact(manifestJson,
                "originalClasses");
        List<TreeArtifact> supplementalTrees = readTreeArtifacts(manifestJson,
                "supplementalTrees");
        List<Path> supplementalPaths = supplementalTrees.stream()
                .map(tree -> tree.path).collect(Collectors.toList());
        JsonObject recordedStaticValidation = object(manifestJson,
                "staticProcessValidation", "static reuse manifest");
        JsonObject actualStaticValidation = validateStaticProcessProvenance(
                processProvenance.path, originalClasses.path,
                supplementalPaths, targetSpec.path, targetSpec.sha256,
                sourceRevision);
        if (!recordedStaticValidation.equals(actualStaticValidation)) {
            throw new IOException("Static process validation does not match "
                    + "the frozen manifest inputs");
        }

        verifyFileArtifact(regions);
        verifyFileArtifact(coverage);
        verifyFileArtifact(staticGraph);
        verifyFileArtifact(regionEdges);
        verifyFileArtifact(targetSpec);
        verifyFileArtifact(processProvenance);
        verifyTreeArtifact(originalClasses);
        for (TreeArtifact tree : supplementalTrees) {
            verifyTreeArtifact(tree);
        }

        Path schedulePath = plan.getParent() == null
                ? null : plan.getParent().resolve(SCHEDULE_FILE);
        Path schedule = regularFile(schedulePath,
                "schedule input provenance");
        JsonObject scheduleJson = readObject(schedule,
                "schedule input provenance");
        requireInt(scheduleJson, "schemaVersion", 2,
                "schedule input provenance");
        requireString(scheduleJson, "kind", SCHEDULE_KIND,
                "schedule input provenance");
        requireBoolean(scheduleJson, "complete", true,
                "schedule input provenance");
        requireArtifactBinding(scheduleJson, "scheduledActivationPlan",
                "scheduledActivationPlanSha256", plan, sha256(plan),
                "schedule activation plan");
        requireArtifactBinding(scheduleJson, "regions", "regionsSha256",
                regions.path, regions.sha256, "schedule regions");
        requireArtifactBinding(scheduleJson, "staticGraph",
                "staticGraphSha256", staticGraph.path, staticGraph.sha256,
                "schedule static graph");

        JsonObject activation = uniqueActivation(plan, selected);
        String regionId = requiredString(activation, "regionId",
                "selected activation");
        String staticRoot = requiredString(activation, "staticRootMethod",
                "selected activation");
        String instrumentationRoot = firstNonBlank(string(activation,
                "rootMethod"), string(activation, "observedRootMethod"));
        if (instrumentationRoot.isEmpty()) {
            throw new IOException("selected activation has no runtime "
                    + "instrumentation root");
        }
        String selection = requiredString(activation,
                "activationSelectionRequired", "selected activation");
        if (!selected.equals(selection)) {
            throw new IOException("Selected activation belongs to a bundle or "
                    + "different selection authority: " + selection);
        }

        JsonObject compactRegion = uniqueCompactRegion(regions.path, regionId);
        String catalogRoot = firstNonBlank(string(compactRegion,
                "staticRootCandidate"), string(compactRegion, "rootMethod"));
        if (!staticRoot.equals(catalogRoot)) {
            throw new IOException("Activation/catalog static root mismatch for "
                    + regionId + ": " + staticRoot + " != " + catalogRoot);
        }
        boolean instrumentationRootInRegion = false;
        for (JsonElement method : compactRegion.getAsJsonArray("methods")) {
            if (instrumentationRoot.equals(method.getAsString())) {
                instrumentationRootInRegion = true;
                break;
            }
        }
        if (!instrumentationRootInRegion) {
            throw new IOException("Activation instrumentation root is not a "
                    + "method in " + regionId + ": "
                    + instrumentationRoot);
        }
        validateTargetBranch(activation, compactRegion);

        JsonObject coverageJson = readObject(coverage.path,
                "symbolic coverage");
        JsonElement complete = coverageJson.get("complete");
        if (complete == null || !complete.isJsonPrimitive()
                || !complete.getAsJsonPrimitive().isBoolean()) {
            throw new IOException("symbolic coverage has no Boolean complete");
        }

        List<Map<String, Object>> selectedRegions = new ArrayList<>();
        selectedRegions.add(map(compactRegion));
        Map<String, Object> coverageMap = map(coverageJson);
        Map<String, Object> report = new LinkedHashMap<>();
        report.put("schemaVersion", SCHEMA_VERSION);
        report.put("kind", "CONCOLIC_STATIC_CATALOG_REUSE");
        report.put("authority", AUTHORITY);
        report.put("manifest", artifactMap(manifest, sha256(manifest)));
        report.put("scheduleInputProvenance",
                artifactMap(schedule, sha256(schedule)));
        report.put("activationPlan", artifactMap(plan, sha256(plan)));
        report.put("regions", artifactMap(regions.path, regions.sha256));
        report.put("coverage", artifactMap(coverage.path, coverage.sha256));
        report.put("staticGraph", artifactMap(staticGraph.path,
                staticGraph.sha256));
        report.put("regionEdges", artifactMap(regionEdges.path,
                regionEdges.sha256));
        report.put("selectedActivationId", selected);
        report.put("selectedRegionId", regionId);
        report.put("selectedStaticRootMethod", staticRoot);
        report.put("selectedInstrumentationRootMethod",
                instrumentationRoot);
        report.put("loadedRegionCount", selectedRegions.size());
        report.put("loadedMethodCount", compactRegion.getAsJsonArray("methods")
                .size());
        report.put("loadedBranchPolicyCount",
                compactRegion.getAsJsonArray("branchPolicies").size());

        return new LoadedCatalog(selectedRegions, coverageMap, report,
                targetSpec.path, originalClasses, supplementalTrees,
                manifest, regions.path, instrumentationRoot);
    }

    static JsonObject createManifest(Path regions, Path coverage,
                                     Path staticGraph, Path regionEdges,
                                     Path targetSpec, Path originalClasses,
            Collection<Path> supplementalTrees,
                                     Path staticProcessProvenance,
                                     String sourceRevision)
            throws IOException {
        List<Path> orderedSupplementalTrees = canonicalUniquePaths(
                supplementalTrees, "supplemental class trees");
        Path frozenTargetSpec = regularFile(targetSpec,
                "manifest target spec");
        String targetSpecSha256 = sha256(frozenTargetSpec);
        JsonObject staticProcessValidation = validateStaticProcessProvenance(
                staticProcessProvenance, originalClasses,
                orderedSupplementalTrees, frozenTargetSpec, targetSpecSha256,
                sourceRevision);
        if (safe(sourceRevision).isEmpty()) {
            throw new IOException("Static reuse source revision is empty");
        }
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("authority", AUTHORITY);
        result.addProperty("sourceRevision", safe(sourceRevision));
        JsonObject artifacts = new JsonObject();
        artifacts.add("regions", fileArtifactJson(regions));
        artifacts.add("coverage", fileArtifactJson(coverage));
        artifacts.add("staticGraph", fileArtifactJson(staticGraph));
        artifacts.add("regionEdges", fileArtifactJson(regionEdges));
        artifacts.add("targetSpec", fileArtifactJson(targetSpec));
        artifacts.add("staticProcessProvenance",
                fileArtifactJson(staticProcessProvenance));
        result.add("artifacts", artifacts);
        result.add("originalClasses", treeArtifactJson(originalClasses));
        JsonArray supplemental = new JsonArray();
        for (Path tree : orderedSupplementalTrees) {
            supplemental.add(treeArtifactJson(tree));
        }
        result.add("supplementalTrees", supplemental);
        result.add("staticProcessValidation", staticProcessValidation);
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject validateStaticProcessProvenance(
            Path provenancePath, Path originalClasses,
            Collection<Path> supplementalTrees, Path targetSpec,
            String targetSpecSha256, String sourceRevision)
            throws IOException {
        Path provenance = regularFile(provenancePath,
                "static process provenance");
        JsonObject recorded = readObject(provenance,
                "static process provenance");
        requireInt(recorded, "schemaVersion", 1,
                "static process provenance");
        requireString(recorded, "mode", "PINNED_STATIC_PROCESS_INPUTS",
                "static process provenance");
        requireBoolean(recorded, "complete", true,
                "static process provenance");

        Path recordedOriginal = canonical(java.nio.file.Paths.get(
                requiredString(recorded, "originalClasses",
                        "static process provenance")));
        Path expectedOriginal = canonical(originalClasses);
        if (!expectedOriginal.equals(recordedOriginal)) {
            throw new IOException("Static process provenance primary class "
                    + "tree mismatch: " + recordedOriginal + " != "
                    + expectedOriginal);
        }

        JsonElement supplemental = recorded.get("supplementalProcessDirs");
        if (supplemental == null || !supplemental.isJsonArray()) {
            throw new IOException("static process provenance has no "
                    + "supplementalProcessDirs array");
        }
        List<Path> recordedSupplemental = new ArrayList<>();
        Set<Path> recordedSupplementalUnique = new LinkedHashSet<>();
        for (JsonElement element : supplemental.getAsJsonArray()) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IOException("static process provenance has an "
                        + "invalid supplemental process directory");
            }
            Path path = canonical(java.nio.file.Paths.get(
                    element.getAsString()));
            if (!recordedSupplementalUnique.add(path)) {
                throw new IOException("static process provenance contains "
                        + "duplicate supplemental process directory " + path);
            }
            recordedSupplemental.add(path);
        }
        List<Path> expectedSupplemental = canonicalUniquePaths(
                supplementalTrees, "expected supplemental class trees");
        if (!expectedSupplemental.equals(recordedSupplemental)) {
            throw new IOException("Static process provenance supplemental "
                    + "class trees mismatch: " + recordedSupplemental
                    + " != " + expectedSupplemental);
        }

        Path expectedTargetSpec = regularFile(targetSpec,
                "frozen target spec");
        String expectedTargetSpecHash = safe(targetSpecSha256);
        String actualTargetSpecHash = sha256(expectedTargetSpec);
        if (expectedTargetSpecHash.isEmpty()
                || !expectedTargetSpecHash.equals(actualTargetSpecHash)) {
            throw new IOException("Frozen target spec SHA-256 mismatch: "
                    + expectedTargetSpec);
        }
        Path recordedTargetSpec = canonical(java.nio.file.Paths.get(
                requiredString(recorded, "targetSpec",
                        "static process provenance")));
        String recordedTargetSpecHash = requiredString(recorded,
                "targetSpecSha256", "static process provenance");
        if (!expectedTargetSpec.equals(recordedTargetSpec)
                || !expectedTargetSpecHash.equals(recordedTargetSpecHash)) {
            throw new IOException("Static process provenance target spec "
                    + "mismatch: " + recordedTargetSpec + " != "
                    + expectedTargetSpec);
        }

        Path producerJar = regularFile(java.nio.file.Paths.get(requiredString(
                recorded, "graphCheckerJar", "static process provenance")),
                "static producer GraphChecker jar");
        String producerJarHash = requiredString(recorded,
                "graphCheckerJarSha256", "static process provenance");
        if (!producerJarHash.equals(sha256(producerJar))) {
            throw new IOException("Static producer GraphChecker jar SHA-256 "
                    + "mismatch: " + producerJar);
        }

        String expectedRevision = safe(sourceRevision);
        String recordedRevision = requiredString(recorded,
                "sourceRevision", "static process provenance");
        if (!recordedRevision.equals(expectedRevision)) {
            throw new IOException("Static process provenance source revision "
                    + "mismatch: " + recordedRevision + " != "
                    + expectedRevision);
        }
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("mode", "PINNED_STATIC_PROCESS_INPUTS");
        result.addProperty("producerGraphCheckerJar", producerJar.toString());
        result.addProperty("producerGraphCheckerJarSha256", producerJarHash);
        result.addProperty("targetSpec", expectedTargetSpec.toString());
        result.addProperty("targetSpecSha256", expectedTargetSpecHash);
        result.addProperty("targetSpecMatched", true);
        result.addProperty("sourceRevision", expectedRevision);
        result.addProperty("sourceRevisionAuthority",
                "STATIC_PROCESS_PROVENANCE");
        result.addProperty("legacySourceRevisionAttestation", false);
        result.addProperty("primaryClassPathMatched", true);
        result.addProperty("supplementalClassPathsMatched", true);
        result.addProperty("complete", true);
        return result;
    }

    static void writeManifest(Path output, JsonObject manifest)
            throws IOException {
        if (output == null) {
            throw new IOException("Static reuse manifest output is null");
        }
        Path absolute = output.toAbsolutePath().normalize();
        Path parent = absolute.getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        Path temporary = Files.createTempFile(parent,
                ".concolic-static-reuse-", ".json.tmp");
        try {
            Files.write(temporary,
                    (GSON.toJson(manifest) + System.lineSeparator())
                            .getBytes(StandardCharsets.UTF_8),
                    StandardOpenOption.TRUNCATE_EXISTING,
                    StandardOpenOption.WRITE);
            try {
                Files.move(temporary, absolute,
                        StandardCopyOption.ATOMIC_MOVE,
                        StandardCopyOption.REPLACE_EXISTING);
            } catch (java.nio.file.AtomicMoveNotSupportedException ignored) {
                Files.move(temporary, absolute,
                        StandardCopyOption.REPLACE_EXISTING);
            }
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    static String treeSha256(Path directory) throws IOException {
        return treeDigest(directory).sha256;
    }

    static TreeDigest treeDigest(Path directory) throws IOException {
        Path root = directory == null ? null
                : directory.toAbsolutePath().normalize();
        if (root == null || !Files.isDirectory(root,
                LinkOption.NOFOLLOW_LINKS) || Files.isSymbolicLink(root)) {
            throw new IOException("Class tree is not a non-symlink directory: "
                    + root);
        }
        List<Path> files;
        try (Stream<Path> stream = Files.walk(root)) {
            files = stream.peek(path -> {
                if (Files.isSymbolicLink(path)) {
                    throw new SymlinkInTree(path);
                }
            }).filter(path -> Files.isRegularFile(path,
                    LinkOption.NOFOLLOW_LINKS)).sorted(Comparator.comparing(
                    path -> portableRelative(root, path))).collect(
                    Collectors.toList());
        } catch (SymlinkInTree symlink) {
            throw new IOException("Class tree contains a symlink: "
                    + symlink.path);
        }
        MessageDigest digest = digest();
        for (Path file : files) {
            digest.update(portableRelative(root, file).getBytes(
                    StandardCharsets.UTF_8));
            digest.update((byte) 0);
            digest.update(sha256(file).getBytes(StandardCharsets.US_ASCII));
            digest.update((byte) '\n');
        }
        return new TreeDigest(hex(digest.digest()), files.size());
    }

    private static JsonObject uniqueActivation(Path plan, String selected)
            throws IOException {
        JsonObject match = null;
        int count = 0;
        try (BufferedReader reader = Files.newBufferedReader(plan,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonObject row = parseObject(line, "activation plan row "
                        + lineNumber);
                if (selected.equals(string(row, "activationId"))) {
                    count++;
                    match = row;
                }
            }
        }
        if (count != 1 || match == null) {
            throw new IOException("Activation plan contains " + count
                    + " rows for " + selected + "; expected exactly one");
        }
        return match;
    }

    private static JsonObject uniqueCompactRegion(Path regions,
                                                  String regionId)
            throws IOException {
        JsonObject match = null;
        int count = 0;
        try (BufferedReader reader = Files.newBufferedReader(regions,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonObject row = parseObject(line, "symbolic region row "
                        + lineNumber);
                String id = requiredString(row, "regionId",
                        "symbolic region row " + lineNumber);
                if (regionId.equals(id)) {
                    count++;
                    match = compactRegion(row);
                }
            }
        }
        if (count != 1 || match == null) {
            throw new IOException("Static catalog contains " + count
                    + " rows for " + regionId + "; expected exactly one");
        }
        return match;
    }

    private static JsonObject compactRegion(JsonObject source)
            throws IOException {
        JsonObject result = new JsonObject();
        copyRequiredString(source, result, "regionId", "symbolic region");
        copyRequiredString(source, result, "rootMethod", "symbolic region");
        copyString(source, result, "staticRootCandidate");
        JsonElement methods = source.get("methods");
        if (methods == null || !methods.isJsonArray()) {
            throw new IOException("symbolic region methods is not an array");
        }
        JsonArray compactMethods = new JsonArray();
        for (JsonElement method : methods.getAsJsonArray()) {
            if (!method.isJsonPrimitive()
                    || !method.getAsJsonPrimitive().isString()
                    || method.getAsString().trim().isEmpty()) {
                throw new IOException("symbolic region has an invalid method");
            }
            compactMethods.add(method.getAsString());
        }
        result.add("methods", compactMethods);

        JsonArray policies = new JsonArray();
        JsonElement sourcePolicies = source.get("branchPolicies");
        if (sourcePolicies != null && !sourcePolicies.isJsonArray()) {
            throw new IOException("symbolic region branchPolicies is not an array");
        }
        if (sourcePolicies != null) {
            for (JsonElement element : sourcePolicies.getAsJsonArray()) {
                if (!element.isJsonObject()) {
                    throw new IOException("symbolic region branch policy is not an object");
                }
                JsonObject policy = element.getAsJsonObject();
                JsonObject compact = new JsonObject();
                copyRequiredString(policy, compact, "siteId",
                        "branch policy");
                copyRequiredString(policy, compact, "method",
                        "branch policy");
                JsonElement unit = policy.get("unitIndex");
                if (unit == null || !unit.isJsonPrimitive()
                        || !unit.getAsJsonPrimitive().isNumber()
                        || unit.getAsInt() < 0) {
                    throw new IOException("branch policy has invalid unitIndex");
                }
                compact.addProperty("unitIndex", unit.getAsInt());
                copyString(policy, compact, "guard");
                policies.add(compact);
            }
        }
        result.add("branchPolicies", policies);
        return result;
    }

    private static void validateTargetBranch(JsonObject activation,
                                             JsonObject region)
            throws IOException {
        JsonElement targetElement = activation.get("targetBranch");
        if (targetElement == null || targetElement.isJsonNull()) {
            return;
        }
        if (!targetElement.isJsonObject()) {
            throw new IOException("selected activation targetBranch is not an object");
        }
        JsonObject target = targetElement.getAsJsonObject();
        String site = requiredString(target, "siteId", "target branch");
        int marker = site.lastIndexOf("#u");
        if (marker <= 0) {
            throw new IOException("target branch has an invalid siteId: " + site);
        }
        String method = site.substring(0, marker);
        int unit;
        try {
            unit = Integer.parseInt(site.substring(marker + 2));
        } catch (NumberFormatException invalid) {
            throw new IOException("target branch has an invalid siteId: " + site,
                    invalid);
        }
        int matches = 0;
        for (JsonElement element : region.getAsJsonArray("branchPolicies")) {
            JsonObject policy = element.getAsJsonObject();
            if (site.equals(string(policy, "siteId"))
                    && method.equals(string(policy, "method"))
                    && unit == integer(policy, "unitIndex", -1)) {
                matches++;
            }
        }
        if (matches != 1) {
            throw new IOException("Target branch " + site + " has " + matches
                    + " exact policies in the selected region");
        }
    }

    private static void requireArtifactBinding(JsonObject provenance,
                                               String pathField,
                                               String hashField,
                                               Path expectedPath,
                                               String expectedHash,
                                               String label)
            throws IOException {
        Path recorded = canonical(java.nio.file.Paths.get(requiredString(
                provenance, pathField, label)));
        String recordedHash = requiredString(provenance, hashField, label);
        if (!recorded.equals(canonical(expectedPath))
                || !recordedHash.equals(expectedHash)) {
            throw new IOException(label + " does not match the frozen catalog");
        }
        String actual = sha256(recorded);
        if (!recordedHash.equals(actual)) {
            throw new IOException(label + " SHA-256 mismatch: " + recorded);
        }
    }

    private static FileArtifact readFileArtifact(JsonObject artifacts,
                                                 String name)
            throws IOException {
        JsonObject artifact = object(artifacts, name,
                "static reuse manifest artifacts");
        Path path = canonical(java.nio.file.Paths.get(requiredString(artifact,
                "path", name + " artifact")));
        String hash = requiredString(artifact, "sha256", name + " artifact");
        return new FileArtifact(path, hash);
    }

    private static TreeArtifact readTreeArtifact(JsonObject owner, String name)
            throws IOException {
        JsonObject artifact = object(owner, name, "static reuse manifest");
        Path path = canonical(java.nio.file.Paths.get(requiredString(artifact,
                "path", name)));
        String hash = requiredString(artifact, "treeSha256", name);
        long fileCount = requiredLong(artifact, "fileCount", name);
        return new TreeArtifact(path, hash, fileCount);
    }

    private static List<TreeArtifact> readTreeArtifacts(JsonObject owner,
                                                        String name)
            throws IOException {
        JsonElement value = owner.get(name);
        if (value == null || !value.isJsonArray()) {
            throw new IOException("static reuse manifest " + name
                    + " is not an array");
        }
        List<TreeArtifact> result = new ArrayList<>();
        Set<Path> paths = new LinkedHashSet<>();
        for (JsonElement element : value.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IOException(name + " contains a non-object");
            }
            JsonObject artifact = element.getAsJsonObject();
            Path path = canonical(java.nio.file.Paths.get(requiredString(
                    artifact, "path", name)));
            String hash = requiredString(artifact, "treeSha256", name);
            long fileCount = requiredLong(artifact, "fileCount", name);
            if (!paths.add(path)) {
                throw new IOException(name + " contains duplicate tree " + path);
            }
            result.add(new TreeArtifact(path, hash, fileCount));
        }
        return result;
    }

    private static void verifyFileArtifact(FileArtifact artifact)
            throws IOException {
        regularFile(artifact.path, "frozen catalog artifact");
        String actual = sha256(artifact.path);
        if (!artifact.sha256.equals(actual)) {
            throw new IOException("Frozen artifact SHA-256 mismatch: "
                    + artifact.path);
        }
    }

    private static void verifyTreeArtifact(TreeArtifact artifact)
            throws IOException {
        TreeDigest actual = treeDigest(artifact.path);
        if (!artifact.treeSha256.equals(actual.sha256)
                || artifact.fileCount != actual.fileCount) {
            throw new IOException("Frozen class tree SHA-256 mismatch: "
                    + artifact.path);
        }
    }

    private static JsonObject fileArtifactJson(Path path) throws IOException {
        Path file = regularFile(path, "manifest artifact");
        JsonObject result = new JsonObject();
        result.addProperty("path", file.toString());
        result.addProperty("sha256", sha256(file));
        result.addProperty("sizeBytes", Files.size(file));
        return result;
    }

    private static JsonObject treeArtifactJson(Path path) throws IOException {
        Path tree = canonical(path);
        TreeDigest digest = treeDigest(tree);
        JsonObject result = new JsonObject();
        result.addProperty("path", tree.toString());
        result.addProperty("treeSha256", digest.sha256);
        result.addProperty("fileCount", digest.fileCount);
        return result;
    }

    private static Map<String, Object> artifactMap(Path path, String hash) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("path", canonical(path).toString());
        result.put("sha256", hash);
        return result;
    }

    private static List<Path> canonicalUniquePaths(Collection<Path> paths,
                                                   String label)
            throws IOException {
        List<Path> result = new ArrayList<>();
        Set<Path> unique = new LinkedHashSet<>();
        if (paths == null) {
            return result;
        }
        for (Path path : paths) {
            Path normalized = canonical(path);
            if (normalized == null || !unique.add(normalized)) {
                throw new IOException(label + " contains duplicate path "
                        + normalized);
            }
            result.add(normalized);
        }
        return result;
    }

    private static JsonObject readObject(Path path, String label)
            throws IOException {
        byte[] bytes = Files.readAllBytes(path);
        return parseObject(new String(bytes, StandardCharsets.UTF_8), label);
    }

    private static JsonObject parseObject(String json, String label)
            throws IOException {
        JsonElement parsed;
        try {
            parsed = JsonParser.parseString(json);
        } catch (RuntimeException malformed) {
            throw new IOException("Malformed " + label, malformed);
        }
        if (!parsed.isJsonObject()) {
            throw new IOException(label + " is not a JSON object");
        }
        return parsed.getAsJsonObject();
    }

    private static Map<String, Object> map(JsonObject object) {
        @SuppressWarnings("unchecked")
        Map<String, Object> converted = (Map<String, Object>) value(object);
        return converted;
    }

    private static Object value(JsonElement element) {
        if (element == null || element.isJsonNull()) {
            return null;
        }
        if (element.isJsonObject()) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (Map.Entry<String, JsonElement> entry
                    : element.getAsJsonObject().entrySet()) {
                result.put(entry.getKey(), value(entry.getValue()));
            }
            return result;
        }
        if (element.isJsonArray()) {
            List<Object> result = new ArrayList<>();
            for (JsonElement item : element.getAsJsonArray()) {
                result.add(value(item));
            }
            return result;
        }
        JsonPrimitive primitive = element.getAsJsonPrimitive();
        if (primitive.isBoolean()) {
            return primitive.getAsBoolean();
        }
        if (primitive.isNumber()) {
            return primitive.getAsNumber();
        }
        return primitive.getAsString();
    }

    private static JsonObject object(JsonObject owner, String field,
                                     String label) throws IOException {
        JsonElement value = owner == null ? null : owner.get(field);
        if (value == null || !value.isJsonObject()) {
            throw new IOException(label + " " + field + " is not an object");
        }
        return value.getAsJsonObject();
    }

    private static String requiredString(JsonObject owner, String field,
                                         String label) throws IOException {
        String value = string(owner, field);
        if (value.isEmpty()) {
            throw new IOException(label + " has no " + field);
        }
        return value;
    }

    private static String string(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()) {
            return "";
        }
        return safe(value.getAsString());
    }

    private static int integer(JsonObject owner, String field, int fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isNumber()
                    ? value.getAsInt() : fallback;
        } catch (RuntimeException invalid) {
            return fallback;
        }
    }

    private static long requiredLong(JsonObject owner, String field,
                                     String label) throws IOException {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            if (value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isNumber()) {
                long result = value.getAsLong();
                if (result >= 0) {
                    return result;
                }
            }
        } catch (RuntimeException ignored) {
        }
        throw new IOException(label + " has invalid " + field);
    }

    private static void requireInt(JsonObject owner, String field,
                                   int expected, String label)
            throws IOException {
        if (integer(owner, field, Integer.MIN_VALUE) != expected) {
            throw new IOException(label + " has unsupported " + field);
        }
    }

    private static void requireString(JsonObject owner, String field,
                                      String expected, String label)
            throws IOException {
        if (!expected.equals(string(owner, field))) {
            throw new IOException(label + " has unsupported " + field);
        }
    }

    private static void requireBoolean(JsonObject owner, String field,
                                       boolean expected, String label)
            throws IOException {
        JsonElement value = owner == null ? null : owner.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isBoolean()
                || value.getAsBoolean() != expected) {
            throw new IOException(label + " has invalid " + field);
        }
    }

    private static void copyRequiredString(JsonObject source,
                                           JsonObject target, String field,
                                           String label) throws IOException {
        target.addProperty(field, requiredString(source, field, label));
    }

    private static void copyString(JsonObject source, JsonObject target,
                                   String field) {
        String value = string(source, field);
        if (!value.isEmpty()) {
            target.addProperty(field, value);
        }
    }

    private static Path regularFile(Path path, String label)
            throws IOException {
        Path canonical = canonical(path);
        if (!Files.isRegularFile(canonical, LinkOption.NOFOLLOW_LINKS)
                || Files.isSymbolicLink(canonical)) {
            throw new IOException(label + " is not a non-symlink regular file: "
                    + canonical);
        }
        return canonical;
    }

    private static Path canonical(Path path) {
        return path == null ? null : path.toAbsolutePath().normalize();
    }

    private static String sha256(Path path) throws IOException {
        MessageDigest digest = digest();
        try (java.io.InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[64 * 1024];
            int read;
            while ((read = input.read(buffer)) >= 0) {
                if (read > 0) {
                    digest.update(buffer, 0, read);
                }
            }
        }
        return hex(digest.digest());
    }

    private static MessageDigest digest() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 unavailable", impossible);
        }
    }

    private static String hex(byte[] bytes) {
        StringBuilder result = new StringBuilder(bytes.length * 2);
        for (byte value : bytes) {
            result.append(String.format("%02x", value & 0xff));
        }
        return result.toString();
    }

    private static String portableRelative(Path root, Path file) {
        return root.relativize(file).toString().replace(File.separatorChar, '/');
    }

    private static String safe(String value) {
        return value == null ? "" : value.trim();
    }

    private static String firstNonBlank(String first, String second) {
        return !safe(first).isEmpty() ? safe(first) : safe(second);
    }

    private static final class FileArtifact {
        private final Path path;
        private final String sha256;

        private FileArtifact(Path path, String sha256) {
            this.path = path;
            this.sha256 = sha256;
        }
    }

    private static final class TreeArtifact {
        private final Path path;
        private final String treeSha256;
        private final long fileCount;

        private TreeArtifact(Path path, String treeSha256, long fileCount) {
            this.path = path;
            this.treeSha256 = treeSha256;
            this.fileCount = fileCount;
        }
    }

    static final class TreeDigest {
        final String sha256;
        final long fileCount;

        private TreeDigest(String sha256, long fileCount) {
            this.sha256 = sha256;
            this.fileCount = fileCount;
        }
    }

    private static final class SymlinkInTree extends RuntimeException {
        private final Path path;

        private SymlinkInTree(Path path) {
            this.path = path;
        }
    }

    static final class LoadedCatalog {
        final List<Map<String, Object>> regions;
        final Map<String, Object> coverage;
        final Map<String, Object> reportMetadata;
        final Path targetSpec;
        final Path manifest;
        final Path regionsPath;
        final String instrumentationRoot;
        private final TreeArtifact originalClasses;
        private final List<TreeArtifact> supplementalTrees;

        private LoadedCatalog(List<Map<String, Object>> regions,
                              Map<String, Object> coverage,
                              Map<String, Object> reportMetadata,
                              Path targetSpec,
                              TreeArtifact originalClasses,
                              List<TreeArtifact> supplementalTrees,
                              Path manifest, Path regionsPath,
                              String instrumentationRoot) {
            this.regions = Collections.unmodifiableList(regions);
            this.coverage = Collections.unmodifiableMap(coverage);
            this.reportMetadata = Collections.unmodifiableMap(reportMetadata);
            this.targetSpec = targetSpec;
            this.originalClasses = originalClasses;
            this.supplementalTrees = Collections.unmodifiableList(
                    new ArrayList<>(supplementalTrees));
            this.manifest = manifest;
            this.regionsPath = regionsPath;
            this.instrumentationRoot = instrumentationRoot;
        }

        void validateCurrentInputs(Path currentTargetSpec,
                                   List<String> currentOriginalInputs,
                                   String configuredSupplementalDirs)
                throws IOException {
            if (!targetSpec.equals(canonical(currentTargetSpec))) {
                throw new IOException("Current target spec differs from frozen "
                        + "catalog: " + currentTargetSpec);
            }
            List<String> inputs = currentOriginalInputs == null
                    ? Collections.emptyList() : currentOriginalInputs;
            if (inputs.size() != 1 || !originalClasses.path.equals(canonical(
                    java.nio.file.Paths.get(inputs.get(0))))) {
                throw new IOException("Current Soot primary input differs from "
                        + "frozen class tree: " + inputs);
            }
            List<Path> currentSupplemental = new ArrayList<>();
            Set<Path> currentSupplementalUnique = new LinkedHashSet<>();
            String configured = safe(configuredSupplementalDirs);
            if (!configured.isEmpty()) {
                for (String value : configured.split(java.util.regex.Pattern
                        .quote(File.pathSeparator))) {
                    if (!safe(value).isEmpty()) {
                        Path path = canonical(java.nio.file.Paths.get(value));
                        if (!currentSupplementalUnique.add(path)) {
                            throw new IOException("Current supplemental "
                                    + "process dirs contain duplicate path "
                                    + path);
                        }
                        currentSupplemental.add(path);
                    }
                }
            }
            List<Path> frozenSupplemental = supplementalTrees.stream()
                    .map(tree -> tree.path).collect(Collectors.toList());
            if (!frozenSupplemental.equals(currentSupplemental)) {
                throw new IOException("Current supplemental process dirs differ "
                        + "from frozen class trees: " + currentSupplemental
                        + " != " + frozenSupplemental);
            }
            verifyTreeArtifact(originalClasses);
            for (TreeArtifact tree : supplementalTrees) {
                verifyTreeArtifact(tree);
            }
        }
    }
}
