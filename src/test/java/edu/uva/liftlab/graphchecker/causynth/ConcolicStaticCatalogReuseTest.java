package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicStaticCatalogReuseTest {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final String ACTIVATION_ID = "ACT.EXACT.7";
    private static final String REGION_ID = "REGION.7";
    private static final String ROOT_METHOD =
            "<example.Root: void run()>";
    private static final String HELPER_METHOD =
            "<example.Helper: int key()>";
    private static final int BRANCH_UNIT = 3;
    private static final String BRANCH_SITE = ROOT_METHOD + "#u"
            + BRANCH_UNIT;

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void compactLoadPreservesBooleanCoverageAndValidatesCurrentInputs()
            throws Exception {
        Fixture fixture = fixture();

        ConcolicStaticCatalogReuse.LoadedCatalog loaded =
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID);

        assertEquals(1, loaded.regions.size());
        Map<String, Object> region = loaded.regions.get(0);
        assertEquals(REGION_ID, region.get("regionId"));
        assertEquals(ROOT_METHOD, region.get("rootMethod"));
        assertEquals(ROOT_METHOD, region.get("staticRootCandidate"));
        assertEquals(2, list(region, "methods").size());
        assertEquals(ROOT_METHOD, list(region, "methods").get(0));
        assertEquals(HELPER_METHOD, list(region, "methods").get(1));
        assertFalse("large static-only fields must not survive projection",
                region.containsKey("outputSlices"));

        List<?> policies = list(region, "branchPolicies");
        assertEquals(1, policies.size());
        @SuppressWarnings("unchecked")
        Map<String, Object> policy = (Map<String, Object>) policies.get(0);
        assertEquals(BRANCH_SITE, policy.get("siteId"));
        assertEquals(ROOT_METHOD, policy.get("method"));
        assertEquals(BRANCH_UNIT,
                ((Number) policy.get("unitIndex")).intValue());
        assertFalse("non-instrumentation policy metadata stays frozen on disk",
                policy.containsKey("ignoredProof"));

        assertEquals(Boolean.FALSE, loaded.coverage.get("complete"));
        @SuppressWarnings("unchecked")
        Map<String, Object> nested = (Map<String, Object>)
                loaded.coverage.get("nested");
        assertEquals(Boolean.TRUE, nested.get("booleanValue"));
        assertEquals(7, ((Number) nested.get("count")).intValue());
        assertEquals(1, ((Number) loaded.reportMetadata.get(
                "loadedRegionCount")).intValue());
        assertEquals(2, ((Number) loaded.reportMetadata.get(
                "loadedMethodCount")).intValue());
        assertEquals(1, ((Number) loaded.reportMetadata.get(
                "loadedBranchPolicyCount")).intValue());

        loaded.validateCurrentInputs(fixture.targetSpec,
                Collections.singletonList(fixture.originalClasses.toString()),
                fixture.supplementalClasses.toString());
    }

    @Test
    public void schedulePlanHashTamperFailsBeforeCatalogUse() throws Exception {
        Fixture fixture = fixture();
        Files.write(fixture.plan, "\n".getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.APPEND);

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure, "schedule activation plan does not match");
    }

    @Test
    public void frozenRegionsHashTamperFailsBeforeParsing() throws Exception {
        Fixture fixture = fixture();
        Files.write(fixture.regions, "\n".getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.APPEND);

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure, "Frozen artifact SHA-256 mismatch");
        assertContains(failure, fixture.regions.toString());
    }

    @Test
    public void hashValidPlanWithDifferentStaticRootFailsSemanticJoin()
            throws Exception {
        Fixture fixture = fixture();
        fixture.writePlan("<example.OtherRoot: void run()>", BRANCH_SITE);

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure, "Activation/catalog static root mismatch");
    }

    @Test
    public void hashValidPlanWithUnmappedTargetBranchFailsSemanticJoin()
            throws Exception {
        Fixture fixture = fixture();
        fixture.writePlan(ROOT_METHOD, ROOT_METHOD + "#u99");

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure, "has 0 exact policies");
    }

    @Test
    public void activationInstrumentationRootIsRequired() throws Exception {
        Fixture fixture = fixture();
        JsonObject activation = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.plan), StandardCharsets.UTF_8))
                .getAsJsonObject();
        activation.remove("rootMethod");
        activation.remove("observedRootMethod");
        writeJson(fixture.plan, activation);
        fixture.writeSchedule();

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure, "has no runtime instrumentation root");
    }

    @Test
    public void activationInstrumentationRootMustBelongToRegion()
            throws Exception {
        Fixture fixture = fixture();
        fixture.writePlan(ROOT_METHOD, BRANCH_SITE,
                "<example.Unrelated: void run()>");

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure,
                "Activation instrumentation root is not a method");
    }

    @Test
    public void classTreeTamperInvalidatesManifestAndCurrentInputValidation()
            throws Exception {
        Fixture fixture = fixture();
        ConcolicStaticCatalogReuse.LoadedCatalog loaded =
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID);
        String frozenTreeHash = ConcolicStaticCatalogReuse.treeSha256(
                fixture.originalClasses);

        Files.write(fixture.originalClasses.resolve("example/Root.class"),
                new byte[]{9, 8, 7}, StandardOpenOption.TRUNCATE_EXISTING);

        assertNotEquals(frozenTreeHash,
                ConcolicStaticCatalogReuse.treeSha256(
                        fixture.originalClasses));
        IOException validationFailure = expectIOException(() ->
                loaded.validateCurrentInputs(fixture.targetSpec,
                        Collections.singletonList(
                                fixture.originalClasses.toString()),
                        fixture.supplementalClasses.toString()));
        assertContains(validationFailure,
                "Frozen class tree SHA-256 mismatch");

        IOException loadFailure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));
        assertContains(loadFailure, "Frozen class tree SHA-256 mismatch");
    }

    @Test
    public void currentInputPathsMustMatchFrozenManifest() throws Exception {
        Fixture fixture = fixture();
        ConcolicStaticCatalogReuse.LoadedCatalog loaded =
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID);
        Path otherClasses = Files.createDirectories(
                fixture.root.resolve("other-classes"));

        IOException primaryFailure = expectIOException(() ->
                loaded.validateCurrentInputs(fixture.targetSpec,
                        Collections.singletonList(otherClasses.toString()),
                        fixture.supplementalClasses.toString()));
        assertContains(primaryFailure, "Current Soot primary input differs");

        IOException supplementalFailure = expectIOException(() ->
                loaded.validateCurrentInputs(fixture.targetSpec,
                        Collections.singletonList(
                                fixture.originalClasses.toString()), ""));
        assertContains(supplementalFailure,
                "Current supplemental process dirs differ");
    }

    @Test
    public void coverageCompleteMustRemainAJsonBoolean() throws Exception {
        Fixture fixture = fixture();
        JsonObject coverage = new JsonObject();
        coverage.addProperty("complete", "false");
        writeJson(fixture.coverage, coverage);
        fixture.writeManifest();

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID));

        assertContains(failure, "has no Boolean complete");
    }

    @Test
    public void incompleteStaticProcessProvenanceCannotBeRepackaged()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject provenance = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.processProvenance),
                StandardCharsets.UTF_8)).getAsJsonObject();
        provenance.addProperty("complete", false);
        writeJson(fixture.processProvenance, provenance);

        IOException failure = expectIOException(fixture::writeManifest);

        assertContains(failure, "static process provenance has invalid complete");
    }

    @Test
    public void staticProcessSourceRevisionMustMatchFreezeRequest()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject provenance = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.processProvenance),
                StandardCharsets.UTF_8)).getAsJsonObject();
        provenance.addProperty("sourceRevision", "different-revision");
        writeJson(fixture.processProvenance, provenance);

        IOException failure = expectIOException(fixture::writeManifest);

        assertContains(failure, "source revision mismatch");
    }

    @Test
    public void staticProcessSourceRevisionBindingIsRequired()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject provenance = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.processProvenance),
                StandardCharsets.UTF_8)).getAsJsonObject();
        provenance.remove("sourceRevision");
        writeJson(fixture.processProvenance, provenance);

        IOException failure = expectIOException(fixture::writeManifest);

        assertContains(failure,
                "static process provenance has no sourceRevision");
    }

    @Test
    public void targetSpecChangedAfterStaticProcessCannotBeFrozen()
            throws Exception {
        Fixture fixture = fixture();
        Files.write(fixture.targetSpec,
                "seed_exception: example.OtherInvalid\n".getBytes(
                        StandardCharsets.UTF_8),
                StandardOpenOption.TRUNCATE_EXISTING);

        IOException failure = expectIOException(fixture::writeManifest);

        assertContains(failure,
                "Static process provenance target spec mismatch");
    }

    @Test
    public void staticProcessTargetSpecBindingIsRequired() throws Exception {
        Fixture fixture = fixture();
        JsonObject provenance = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.processProvenance),
                StandardCharsets.UTF_8)).getAsJsonObject();
        provenance.remove("targetSpecSha256");
        writeJson(fixture.processProvenance, provenance);

        IOException failure = expectIOException(fixture::writeManifest);

        assertContains(failure,
                "static process provenance has no targetSpecSha256");
    }

    @Test
    public void duplicateSupplementalTreesCannotProduceManifest()
            throws Exception {
        Fixture fixture = fixture();

        IOException failure = expectIOException(() ->
                ConcolicStaticCatalogReuse.createManifest(
                        fixture.regions, fixture.coverage,
                        fixture.staticGraph, fixture.regionEdges,
                        fixture.targetSpec, fixture.originalClasses,
                        Arrays.asList(fixture.supplementalClasses,
                                fixture.supplementalClasses),
                        fixture.processProvenance,
                        "revision-under-test"));

        assertContains(failure,
                "supplemental class trees contains duplicate path");
    }

    @Test
    public void supplementalTreeOrderMustMatchSootProcessOrder()
            throws Exception {
        Fixture fixture = fixture();
        Path second = Files.createDirectories(
                fixture.root.resolve("supplemental-classes-second"));
        Files.write(second.resolve("Second.class"), new byte[]{10, 11});
        JsonObject provenance = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.processProvenance),
                StandardCharsets.UTF_8)).getAsJsonObject();
        JsonArray processDirs = new JsonArray();
        processDirs.add(canonical(fixture.supplementalClasses).toString());
        processDirs.add(canonical(second).toString());
        provenance.add("supplementalProcessDirs", processDirs);
        writeJson(fixture.processProvenance, provenance);
        fixture.manifestJson = ConcolicStaticCatalogReuse.createManifest(
                fixture.regions, fixture.coverage, fixture.staticGraph,
                fixture.regionEdges, fixture.targetSpec,
                fixture.originalClasses,
                Arrays.asList(fixture.supplementalClasses, second),
                fixture.processProvenance, "revision-under-test");
        ConcolicStaticCatalogReuse.writeManifest(fixture.manifest,
                fixture.manifestJson);
        fixture.writeSchedule();
        ConcolicStaticCatalogReuse.LoadedCatalog loaded =
                ConcolicStaticCatalogReuse.load(fixture.manifest,
                        fixture.plan, ACTIVATION_ID);

        IOException failure = expectIOException(() ->
                loaded.validateCurrentInputs(fixture.targetSpec,
                        Collections.singletonList(
                                fixture.originalClasses.toString()),
                        second + File.pathSeparator
                                + fixture.supplementalClasses));

        assertContains(failure,
                "Current supplemental process dirs differ");
    }

    private Fixture fixture() throws Exception {
        return new Fixture(folder.newFolder("catalog-reuse").toPath());
    }

    private static List<?> list(Map<String, Object> owner, String field) {
        return (List<?>) owner.get(field);
    }

    private static IOException expectIOException(ThrowingRunnable action)
            throws Exception {
        try {
            action.run();
            fail("Expected IOException");
            return null;
        } catch (IOException expected) {
            return expected;
        }
    }

    private static void assertContains(IOException failure, String expected) {
        assertTrue("Expected <" + expected + "> in: " + failure,
                failure.getMessage() != null
                        && failure.getMessage().contains(expected));
    }

    private static void writeJson(Path path, JsonObject object)
            throws IOException {
        Files.write(path, (GSON.toJson(object) + "\n").getBytes(
                StandardCharsets.UTF_8));
    }

    private static String sha256(Path path) throws IOException {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException impossible) {
            throw new AssertionError(impossible);
        }
        byte[] bytes = Files.readAllBytes(path);
        digest.update(bytes);
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) {
            result.append(String.format("%02x", value & 0xff));
        }
        return result.toString();
    }

    private static Path canonical(Path path) {
        return path.toAbsolutePath().normalize();
    }

    private static JsonObject fileArtifact(JsonObject manifest, String name) {
        return manifest.getAsJsonObject("artifacts").getAsJsonObject(name);
    }

    private static final class Fixture {
        private final Path root;
        private final Path regions;
        private final Path coverage;
        private final Path staticGraph;
        private final Path regionEdges;
        private final Path targetSpec;
        private final Path processProvenance;
        private final Path producerJar;
        private final Path originalClasses;
        private final Path supplementalClasses;
        private final Path plan;
        private final Path schedule;
        private final Path manifest;
        private JsonObject manifestJson;

        private Fixture(Path root) throws Exception {
            this.root = root;
            regions = root.resolve("symbolic_regions.jsonl");
            coverage = root.resolve("symbolic_coverage.json");
            staticGraph = root.resolve("static_dataflow_edges.jsonl");
            regionEdges = root.resolve("symbolic_region_edges.jsonl");
            targetSpec = root.resolve("target.yaml");
            processProvenance = root.resolve("static_process_provenance.json");
            producerJar = root.resolve("static-producer.jar");
            originalClasses = Files.createDirectories(
                    root.resolve("original-classes"));
            supplementalClasses = Files.createDirectories(
                    root.resolve("supplemental-classes"));
            Files.createDirectories(originalClasses.resolve("example"));
            Files.createDirectories(supplementalClasses.resolve("example"));
            plan = root.resolve("schedule/scheduled_activation_plan.jsonl");
            schedule = plan.getParent().resolve(
                    ConcolicStaticCatalogReuse.SCHEDULE_FILE);
            manifest = root.resolve("concolic_static_catalog_manifest.json");

            Files.createDirectories(plan.getParent());
            Files.write(originalClasses.resolve("example/Root.class"),
                    new byte[]{1, 2, 3});
            Files.write(supplementalClasses.resolve("example/Helper.class"),
                    new byte[]{4, 5, 6});
            Files.write(staticGraph,
                    "{\"id\":\"DF.0\"}\n".getBytes(StandardCharsets.UTF_8));
            Files.write(regionEdges,
                    "{\"edgeId\":\"RE.0\"}\n".getBytes(StandardCharsets.UTF_8));
            Files.write(targetSpec,
                    "seed_exception: example.Invalid\n".getBytes(
                            StandardCharsets.UTF_8));
            Files.write(producerJar, new byte[]{7, 8, 9});
            writeProcessProvenance();
            writeRegions();
            writeCoverage();
            writeManifest();
            writePlan(ROOT_METHOD, BRANCH_SITE);
        }

        private void writeRegions() throws IOException {
            JsonObject region = new JsonObject();
            region.addProperty("regionId", REGION_ID);
            region.addProperty("rootMethod", ROOT_METHOD);
            region.addProperty("staticRootCandidate", ROOT_METHOD);
            JsonArray methods = new JsonArray();
            methods.add(ROOT_METHOD);
            methods.add(HELPER_METHOD);
            region.add("methods", methods);
            JsonObject policy = new JsonObject();
            policy.addProperty("siteId", BRANCH_SITE);
            policy.addProperty("method", ROOT_METHOD);
            policy.addProperty("unitIndex", BRANCH_UNIT);
            policy.addProperty("guard", "if key == null goto throw");
            policy.addProperty("ignoredProof", "large-static-proof");
            JsonArray policies = new JsonArray();
            policies.add(policy);
            region.add("branchPolicies", policies);
            JsonArray outputSlices = new JsonArray();
            JsonObject unusedSlice = new JsonObject();
            unusedSlice.addProperty("large", "not-loaded");
            outputSlices.add(unusedSlice);
            region.add("outputSlices", outputSlices);
            Files.write(regions, (GSON.toJson(region) + "\n").getBytes(
                    StandardCharsets.UTF_8));
        }

        private void writeCoverage() throws IOException {
            JsonObject value = new JsonObject();
            value.addProperty("complete", false);
            JsonObject nested = new JsonObject();
            nested.addProperty("booleanValue", true);
            nested.addProperty("count", 7);
            value.add("nested", nested);
            writeJson(coverage, value);
        }

        private void writeProcessProvenance() throws IOException {
            JsonObject provenance = new JsonObject();
            provenance.addProperty("schemaVersion", 1);
            provenance.addProperty("mode", "PINNED_STATIC_PROCESS_INPUTS");
            provenance.addProperty("graphCheckerJar",
                    canonical(producerJar).toString());
            provenance.addProperty("graphCheckerJarSha256",
                    sha256(producerJar));
            provenance.addProperty("sourceRevision", "revision-under-test");
            provenance.addProperty("targetSpec",
                    canonical(targetSpec).toString());
            provenance.addProperty("targetSpecSha256", sha256(targetSpec));
            provenance.addProperty("originalClasses",
                    canonical(originalClasses).toString());
            JsonArray supplemental = new JsonArray();
            supplemental.add(canonical(supplementalClasses).toString());
            provenance.add("supplementalProcessDirs", supplemental);
            provenance.addProperty("complete", true);
            writeJson(processProvenance, provenance);
        }

        private void writeManifest() throws IOException {
            manifestJson = ConcolicStaticCatalogReuse.createManifest(
                    regions, coverage, staticGraph, regionEdges, targetSpec,
                    originalClasses,
                    Collections.singletonList(supplementalClasses),
                    processProvenance, "revision-under-test");
            ConcolicStaticCatalogReuse.writeManifest(manifest, manifestJson);
        }

        private void writePlan(String staticRoot, String targetSite)
                throws IOException {
            writePlan(staticRoot, targetSite, ROOT_METHOD);
        }

        private void writePlan(String staticRoot, String targetSite,
                               String instrumentationRoot)
                throws IOException {
            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", ACTIVATION_ID);
            activation.addProperty("regionId", REGION_ID);
            activation.addProperty("rootMethod", instrumentationRoot);
            activation.addProperty("staticRootMethod", staticRoot);
            activation.addProperty("observedRootMethod",
                    instrumentationRoot);
            activation.addProperty("activationSelectionRequired",
                    ACTIVATION_ID);
            JsonObject target = new JsonObject();
            target.addProperty("siteId", targetSite);
            activation.add("targetBranch", target);
            writeJson(plan, activation);
            writeSchedule();
        }

        private void writeSchedule() throws IOException {
            JsonObject provenance = new JsonObject();
            provenance.addProperty("schemaVersion", 2);
            provenance.addProperty("kind",
                    ConcolicStaticCatalogReuse.SCHEDULE_KIND);
            provenance.addProperty("complete", true);
            provenance.addProperty("scheduledActivationPlan",
                    canonical(plan).toString());
            provenance.addProperty("scheduledActivationPlanSha256",
                    sha256(plan));
            JsonObject regionsArtifact = fileArtifact(manifestJson, "regions");
            provenance.addProperty("regions",
                    canonical(regions).toString());
            provenance.addProperty("regionsSha256",
                    regionsArtifact.get("sha256").getAsString());
            JsonObject graphArtifact = fileArtifact(manifestJson,
                    "staticGraph");
            provenance.addProperty("staticGraph",
                    canonical(staticGraph).toString());
            provenance.addProperty("staticGraphSha256",
                    graphArtifact.get("sha256").getAsString());
            writeJson(schedule, provenance);
        }
    }

    private interface ThrowingRunnable {
        void run() throws Exception;
    }
}
