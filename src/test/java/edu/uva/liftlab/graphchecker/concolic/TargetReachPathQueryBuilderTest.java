package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class TargetReachPathQueryBuilderTest {
    private static final String REGION = "REGION.T";
    private static final String CANONICAL = "REGION.T@test#call1";
    private static final String SELECTED = "REGION.T@test#call2";
    private static final String CANONICAL_PORT = "REGION.T.in.canonical";
    private static final String EXACT_PORT = "REGION.T.in.exact";
    private static final String SITE = "<T: void run()>#u4";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void canonicalVmPathIsInstantiatedAtSelectedExactOccurrence()
            throws Exception {
        File summaries = jsonl("summaries.jsonl", summary(true));
        File manifest = json("manifest.json", manifest());
        File seed = jsonl("seed.jsonl", seedQuery());
        File output = folder.newFile("reach.jsonl");

        JsonObject query = TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", summaries.getPath(),
                        "--path-manifest", manifest.getPath(),
                        "--seed-query", seed.getPath(),
                        "--target-instance", SELECTED,
                        "--exception-type", "example.InvalidKey",
                        "--output", output.getPath()}));

        assertEquals(SELECTED,
                query.get("regionInstanceId").getAsString());
        assertEquals(CANONICAL,
                query.get("canonicalRegionInstanceId").getAsString());
        String constraints = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject().get("constraints").toString();
        assertTrue(constraints.contains(EXACT_PORT));
        assertTrue(!constraints.contains(CANONICAL_PORT));
        JsonObject relation = query.getAsJsonObject("symbolicContext")
                .getAsJsonArray("equalityRelations").get(0)
                .getAsJsonObject();
        assertEquals(EXACT_PORT,
                relation.get("toEndpoint").getAsString());
        assertEquals(1, query.getAsJsonObject("selectedTargetOccurrence")
                .getAsJsonArray("bindingIds").size());
    }

    @Test
    public void oppositeOutcomeWitnessStatesFatalBranchAsComplement()
            throws Exception {
        // The flip that would have concretely taken the fatal direction can
        // be abandoned as an UNSUPPORTED exploration gap.  The closed path
        // still proves its decided prefix; the fatal branch condition itself
        // stays symbolic as the complement of the witnessed predicate.
        JsonObject summary = summary(true);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                witness(false, predicate(CANONICAL_PORT)), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        summary.add("branchMappings", mappings);
        File summaries = jsonl("complement-summaries.jsonl", summary);
        File manifest = json("complement-manifest.json", manifest());
        File seed = jsonl("complement-seed.jsonl", seedQuery());
        File output = folder.newFile("complement-reach.jsonl");

        JsonObject query = TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", summaries.getPath(),
                        "--path-manifest", manifest.getPath(),
                        "--seed-query", seed.getPath(),
                        "--target-instance", SELECTED,
                        "--exception-type", "example.InvalidKey",
                        "--output", output.getPath()}));

        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals("SYMBOLIC_COMPLEMENT_OF_WITNESSED_TARGET_V1",
                path.get("fatalBranchConditionAuthority").getAsString());
        String constraints = path.get("constraints").toString();
        assertTrue(constraints, constraints.contains("\"!=\""));
        assertTrue(constraints, constraints.contains(EXACT_PORT));

        // A path that already witnessed the fatal outcome keeps its own
        // complete witnessed condition set.
        JsonObject witnessed = TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", jsonl("witnessed-summaries.jsonl",
                                summary(true)).getPath(),
                        "--path-manifest", json("witnessed-manifest.json",
                                manifest()).getPath(),
                        "--seed-query", jsonl("witnessed-seed.jsonl",
                                seedQuery()).getPath(),
                        "--target-instance", SELECTED,
                        "--exception-type", "example.InvalidKey",
                        "--output", folder.newFile("witnessed-reach.jsonl")
                                .getPath()}))
                .getAsJsonArray("paths").get(0).getAsJsonObject();
        assertEquals("WITNESSED_TARGET_OUTCOME_V1",
                witnessed.get("fatalBranchConditionAuthority")
                        .getAsString());
    }

    @Test
    public void fatalOutcomeIsIndependentOfExplorationFlip()
            throws Exception {
        JsonObject reached = summary(true);
        JsonObject condition = reached.getAsJsonArray("pathCondition")
                .get(0).getAsJsonObject();
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                witness(false, condition), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        reached.add("branchMappings", mappings);

        JsonObject query = TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", jsonl("fatal-summaries.jsonl",
                                reached).getPath(),
                        "--path-manifest", json("fatal-manifest.json",
                                manifest()).getPath(),
                        "--seed-query", jsonl("fatal-seed.jsonl",
                                seedQuery(false)).getPath(),
                        "--target-instance", SELECTED,
                        "--exception-type", "example.InvalidKey",
                        "--output", folder.newFile("fatal-reach.jsonl")
                                .getPath()}));

        assertFalse(query.get("requiredTakenOutcome").getAsBoolean());
        assertEquals("WITNESSED_TARGET_OUTCOME_V1",
                query.getAsJsonArray("paths").get(0).getAsJsonObject()
                        .get("fatalBranchConditionAuthority").getAsString());
        assertTrue(BranchReplayContract.fromJson(query.getAsJsonObject(
                "seedReplayContract")).requiredTakenOutcome());
    }

    @Test
    public void missingSelectedSummaryOccurrenceFailsClosed()
            throws Exception {
        File summaries = jsonl("missing-summaries.jsonl", summary(false));
        File manifest = json("missing-manifest.json", manifest());
        File seed = jsonl("missing-seed.jsonl", seedQuery());
        File output = folder.newFile("missing-reach.jsonl");

        try {
            TargetReachPathQueryBuilder.build(
                    TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                            "--summaries", summaries.getPath(),
                            "--path-manifest", manifest.getPath(),
                            "--seed-query", seed.getPath(),
                            "--target-instance", SELECTED,
                            "--exception-type", "example.InvalidKey",
                            "--output", output.getPath()}));
            fail("missing selected occurrence must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "selected exact occurrence"));
        }
    }

    @Test
    public void incompleteSelectedDemandLedgerFailsClosed()
            throws Exception {
        JsonObject malformed = summary(true);
        malformed.add("edgeBindings", new JsonArray());
        File summaries = jsonl("ledger-summaries.jsonl", malformed);
        File manifest = json("ledger-manifest.json", manifest());
        File seed = jsonl("ledger-seed.jsonl", seedQuery());
        File output = folder.newFile("ledger-reach.jsonl");

        try {
            TargetReachPathQueryBuilder.build(
                    TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                            "--summaries", summaries.getPath(),
                            "--path-manifest", manifest.getPath(),
                            "--seed-query", seed.getPath(),
                            "--target-instance", SELECTED,
                            "--exception-type", "example.InvalidKey",
                            "--output", output.getPath()}));
            fail("incomplete exact demand ledger must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "demand ledger"));
        }
    }

    private static JsonObject seedQuery() {
        return seedQuery(true);
    }

    private static JsonObject seedQuery(boolean fatalRequiredOutcome) {
        JsonObject seed = new JsonObject();
        seed.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        seed.addProperty("readyForSolver", true);
        seed.addProperty("regionId", REGION);
        seed.addProperty("regionInstanceId", SELECTED);
        seed.addProperty("canonicalRegionInstanceId", CANONICAL);
        seed.addProperty("goalId", "GOAL.TARGET");
        seed.addProperty("targetSiteId", SITE);
        seed.addProperty("fatalRequiredTakenOutcome",
                fatalRequiredOutcome);
        seed.add("selectedTargetOccurrence", occurrence(SELECTED, 2,
                true));
        BranchWitness source = witness(false, predicate(CANONICAL_PORT));
        seed.add("replayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), source).toJson());

        JsonObject relation = new JsonObject();
        relation.addProperty("edgeId", "EDGE.1");
        relation.addProperty("fromEndpoint", "REGION.P.out.value");
        relation.addProperty("toEndpoint", CANONICAL_PORT);
        JsonArray selected = new JsonArray();
        selected.add(binding());
        relation.add("selectedBindings", selected);
        JsonObject context = new JsonObject();
        context.addProperty("regionInstanceId", SELECTED);
        JsonArray equality = new JsonArray();
        equality.add(relation);
        context.add("equalityRelations", equality);
        context.add("equalityClasses", new JsonArray());
        context.add("versionedStateMerges", new JsonArray());
        context.add("alternativeWriterGroups", new JsonArray());
        seed.add("symbolicContext", context);
        return seed;
    }

    private static JsonObject summary(boolean includeSelected) {
        JsonObject summary = new JsonObject();
        summary.addProperty("schemaVersion", 1);
        summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        summary.addProperty("summaryId", "SUMMARY.TARGET");
        summary.addProperty("goalId", "GOAL.TARGET");
        summary.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        summary.addProperty("regionId", REGION);
        summary.addProperty("regionInstanceId", CANONICAL);
        summary.addProperty("logicalRegionId", "REGION.T@owner7");
        summary.addProperty("summaryReuseKey", "REGION.T@owner7");
        summary.addProperty("relationallyComplete", true);
        summary.addProperty("normalExit", true);
        summary.add("loopBound", loopBound());

        JsonObject condition = predicate(CANONICAL_PORT);
        JsonArray path = new JsonArray();
        path.add(condition);
        summary.add("pathCondition", path);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                witness(true, condition), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        summary.add("branchMappings", mappings);
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", SITE);
        branch.addProperty("policy", "EXPLORE");
        JsonArray branches = new JsonArray();
        branches.add(branch);
        summary.add("branches", branches);
        JsonArray edges = new JsonArray();
        edges.add(binding());
        summary.add("edgeBindings", edges);

        JsonObject catalog = new JsonObject();
        catalog.addProperty("schemaVersion", 1);
        catalog.addProperty("kind",
                "LOGICAL_SUMMARY_OCCURRENCE_CATALOG");
        catalog.addProperty("logicalRegionId", "REGION.T@owner7");
        catalog.addProperty("summaryReuseKey", "REGION.T@owner7");
        catalog.addProperty("canonicalRegionInstanceId", CANONICAL);
        catalog.addProperty("canonicalRootCallId", 1);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence(CANONICAL, 1, false));
        if (includeSelected) {
            occurrences.add(occurrence(SELECTED, 2, true));
        }
        catalog.add("occurrences", occurrences);
        summary.add("occurrenceInstantiationCatalog", catalog);
        return summary;
    }

    private static JsonObject occurrence(
            String instance, long rootCallId, boolean selected) {
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("regionInstanceId", instance);
        occurrence.addProperty("rootCallId", rootCallId);
        JsonObject input = new JsonObject();
        input.addProperty("canonicalPort", CANONICAL_PORT);
        input.addProperty("exactPort",
                selected ? EXACT_PORT : CANONICAL_PORT);
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        occurrence.add("inputPortMap", inputs);
        occurrence.add("outputPortMap", new JsonArray());
        JsonArray ids = new JsonArray();
        if (selected) ids.add("EDGE.1");
        occurrence.add("bindingIds", ids);
        return occurrence;
    }

    private static JsonObject binding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE.1");
        binding.addProperty("fromRegion", "REGION.P");
        binding.addProperty("toRegion", REGION);
        binding.addProperty("fromRegionInstance", "REGION.P@test#call9");
        binding.addProperty("toRegionInstance", SELECTED);
        binding.addProperty("fromOutputPort", "REGION.P.out.value");
        binding.addProperty("toInputPort", EXACT_PORT);
        return binding;
    }

    private static JsonObject manifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("state", "CLOSED");
        manifest.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        manifest.addProperty("regionId", REGION);
        manifest.addProperty("regionInstanceId", CANONICAL);
        manifest.addProperty("goalId", "GOAL.TARGET");
        manifest.add("gaps", new JsonArray());
        return manifest;
    }

    private static JsonObject loopBound() {
        JsonObject bound = new JsonObject();
        bound.addProperty("schemaVersion", 1);
        bound.addProperty("kind", "CFG_BACKEDGE");
        bound.addProperty("scope", "ALL_EXECUTION_SCOPE_LOOPS");
        bound.addProperty("maxBackedgeTraversals", 8);
        bound.addProperty("onLimit", "CUT_PATH");
        return bound;
    }

    private static BranchWitness witness(
            boolean outcome, JsonObject predicate) {
        JsonObject metadata = new JsonObject();
        metadata.addProperty("eventId", outcome ? 2 : 1);
        metadata.addProperty("contextId", 7);
        return BranchWitness.vmPc(SITE, "<T: void run()>", 4, 1,
                outcome, predicate, 1, metadata);
    }

    private static JsonObject predicate(String port) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", port);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_1");
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", "==");
        result.add("_right", right);
        return result;
    }

    private File jsonl(String name, JsonObject row) throws Exception {
        return json(name, row);
    }

    private File json(String name, JsonObject row) throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.singletonList(row.toString()),
                StandardCharsets.UTF_8);
        return file;
    }
}
