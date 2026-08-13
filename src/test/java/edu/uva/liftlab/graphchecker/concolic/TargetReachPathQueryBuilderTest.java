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
    private static final String SOURCE = "cluster0/nn0#epoch1";
    private static final String OCCURRENCE = SOURCE + "/region/T#2";
    private static final String PORT = "REGION.T.in.value";
    private static final String SITE = "<T: void run()>#u4";
    private static final String EDGE = "EDGE.1";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void buildsQueryForOneDirectOccurrence() throws Exception {
        JsonObject query = build("direct", summary(true), seedQuery(true));

        assertEquals(OCCURRENCE, query.get("occurrenceId").getAsString());
        assertEquals(SOURCE, query.get("sourceKey").getAsString());
        assertTrue(query.getAsJsonArray("paths").get(0).toString()
                .contains(PORT));
        JsonObject relation = query.getAsJsonObject("symbolicContext")
                .getAsJsonArray("equalityRelations").get(0)
                .getAsJsonObject();
        assertEquals(PORT, relation.get("toEndpoint").getAsString());
        assertEquals(EDGE, query.getAsJsonObject("selectedTargetOccurrence")
                .getAsJsonArray("bindingIds").get(0).getAsString());
    }

    @Test
    public void oppositeWitnessUsesFatalComplement() throws Exception {
        JsonObject opposite = summary(false);
        JsonObject query = build("complement", opposite, seedQuery(true));
        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();

        assertEquals("SYMBOLIC_COMPLEMENT_OF_WITNESSED_TARGET_V1",
                path.get("fatalBranchConditionAuthority").getAsString());
        assertTrue(path.get("constraints").toString().contains("\"!=\""));
        assertTrue(path.get("constraints").toString().contains(PORT));
    }

    @Test
    public void fatalOutcomeIsIndependentOfExplorationFlip()
            throws Exception {
        JsonObject query = build("polarity", summary(false),
                seedQuery(false));

        assertFalse(query.get("requiredTakenOutcome").getAsBoolean());
        assertEquals("WITNESSED_TARGET_OUTCOME_V1",
                query.getAsJsonArray("paths").get(0).getAsJsonObject()
                        .get("fatalBranchConditionAuthority").getAsString());
        assertTrue(BranchReplayContract.fromJson(query.getAsJsonObject(
                "seedReplayContract")).requiredTakenOutcome());
    }

    @Test
    public void differentOccurrenceIsNotMerged() throws Exception {
        JsonObject other = summary(true);
        other.addProperty("occurrenceId", SOURCE + "/region/T#3");
        try {
            build("other", other, seedQuery(true));
            fail("another occurrence must not satisfy this target query");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "contains no path reaching"));
        }
    }

    @Test
    public void incompleteDemandLedgerFailsClosed() throws Exception {
        JsonObject malformed = summary(true);
        malformed.add("edgeBindings", new JsonArray());
        try {
            build("ledger", malformed, seedQuery(true));
            fail("incomplete demand ledger must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("demand ledger"));
        }
    }

    private JsonObject build(String prefix, JsonObject summary,
                             JsonObject seed) throws Exception {
        return TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", jsonl(prefix + "-summaries", summary)
                        .getPath(),
                        "--path-manifest", json(prefix + "-manifest",
                        manifest()).getPath(),
                        "--seed-query", jsonl(prefix + "-seed", seed)
                        .getPath(),
                        "--target-instance", OCCURRENCE,
                        "--exception-type", "example.ExpectedState",
                        "--output", folder.newFile(prefix + "-reach.jsonl")
                        .getPath()}));
    }

    private static JsonObject seedQuery(boolean fatalRequiredOutcome) {
        JsonObject seed = new JsonObject();
        seed.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        seed.addProperty("readyForSolver", true);
        seed.addProperty("sourceKey", SOURCE);
        seed.addProperty("regionId", REGION);
        seed.addProperty("occurrenceId", OCCURRENCE);
        seed.addProperty("goalId", "GOAL.TARGET");
        seed.addProperty("targetSiteId", SITE);
        seed.addProperty("fatalRequiredTakenOutcome", fatalRequiredOutcome);
        seed.add("selectedTargetOccurrence", selectedOccurrence());
        seed.add("replayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(),
                witness(false, predicate())).toJson());

        JsonObject relation = new JsonObject();
        relation.addProperty("edgeId", EDGE);
        relation.addProperty("fromEndpoint", "REGION.P.out.value");
        relation.addProperty("toEndpoint", PORT);
        JsonArray selected = new JsonArray();
        selected.add(binding());
        relation.add("selectedBindings", selected);
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", OCCURRENCE);
        JsonArray equality = new JsonArray();
        equality.add(relation);
        context.add("equalityRelations", equality);
        context.add("equalityClasses", new JsonArray());
        context.add("versionedStateMerges", new JsonArray());
        context.add("alternativeWriterGroups", new JsonArray());
        seed.add("symbolicContext", context);
        return seed;
    }

    private static JsonObject summary(boolean witnessedOutcome) {
        JsonObject summary = new JsonObject();
        summary.addProperty("schemaVersion", 1);
        summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        summary.addProperty("summaryId", "SUMMARY.TARGET");
        summary.addProperty("goalId", "GOAL.TARGET");
        summary.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        summary.addProperty("sourceKey", SOURCE);
        summary.addProperty("regionId", REGION);
        summary.addProperty("occurrenceId", OCCURRENCE);
        summary.addProperty("relationallyComplete", true);
        summary.addProperty("normalExit", true);
        summary.add("loopBound", loopBound());

        JsonObject condition = predicate();
        JsonArray path = new JsonArray();
        path.add(condition);
        summary.add("pathCondition", path);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                witness(witnessedOutcome, condition), 0,
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
        return summary;
    }

    private static JsonObject selectedOccurrence() {
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrenceId", OCCURRENCE);
        JsonArray inputs = new JsonArray();
        inputs.add(PORT);
        occurrence.add("inputPorts", inputs);
        JsonArray ids = new JsonArray();
        ids.add(EDGE);
        occurrence.add("bindingIds", ids);
        return occurrence;
    }

    private static JsonObject binding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", EDGE);
        binding.addProperty("fromRegion", "REGION.P");
        binding.addProperty("toRegion", REGION);
        binding.addProperty("fromOccurrenceId",
                "cluster0/nn0#epoch1/region/P#1");
        binding.addProperty("toOccurrenceId", OCCURRENCE);
        binding.addProperty("fromOutputPort", "REGION.P.out.value");
        binding.addProperty("toInputPort", PORT);
        return binding;
    }

    private static JsonObject manifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("state", "CLOSED");
        manifest.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        manifest.addProperty("regionId", REGION);
        manifest.addProperty("occurrenceId", OCCURRENCE);
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

    private static BranchWitness witness(boolean outcome,
                                         JsonObject predicate) {
        JsonObject metadata = new JsonObject();
        metadata.addProperty("eventId", outcome ? 2 : 1);
        metadata.addProperty("contextId", 7);
        return BranchWitness.vmPc(SITE, "<T: void run()>", 4, 1,
                outcome, predicate, 1, metadata);
    }

    private static JsonObject predicate() {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", PORT);
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
        return json(name + ".jsonl", row);
    }

    private File json(String name, JsonObject row) throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.singletonList(row.toString()),
                StandardCharsets.UTF_8);
        return file;
    }
}
