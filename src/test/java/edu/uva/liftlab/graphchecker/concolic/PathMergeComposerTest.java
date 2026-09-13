package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.TargetAnchorEvidence;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import org.junit.Assume;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The merge, on three recordings small enough to read.
 *
 * <p>One root, one anchored target, and paths that differ only in what the
 * root made their fatal predicate: the disjunction must be satisfiable
 * exactly where some path's own condition is, and the gates must refuse
 * rather than guess where a value is missing.</p>
 */
public class PathMergeComposerTest {
    private static final String SITE =
            "<com.example.Service: void serve()>#u17";
    private static final String PHASE = "SOURCE_PHASE.example";
    private static final String SOURCE = "EXAMPLE.ROOT";
    private static final String FIELD_SIGNATURE =
            "<com.example.Service: boolean enabled>";
    private static final String RAW_ROOT = "M_Z_field_"
            + SymbolicSourceEvidence.engineLabelForPhase(PHASE, SOURCE)
            + "_com/example/Service";
    private static final String ROOT_TERM = "sym__EXAMPLE_ROOT__1";

    /**
     * Two replays of one site: the seed the root kept healthy and the flip
     * the root made fatal.  Only the flipped path's root valuation may
     * satisfy the disjunction.
     */
    @Test
    public void disjunctionIsSatisfiableOnlyOnTheFlippedPath()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-flip");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(1), constant(1))));
        query.getAsJsonArray("paths").add(path("flip", "GROUP.FLIP",
                rootIs(false), notEqual(constant(1), constant(0))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        assertEquals("CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertEquals(2, merge.getAsJsonArray("paths").size());
        assertEquals(2, result.manifest.getAsJsonArray(
                "caseSelectorPartitions").get(0).getAsJsonArray().size());
        assertTrue(result.smtLib.contains(ROOT_TERM));

        // The root must be free, and free only where the flip put it.
        assertEquals("sat", solve(result.smtLib));
        assertEquals("sat", solve(result.smtLib
                + "(assert (= " + ROOT_TERM + " false))\n(check-sat)\n"));
        assertEquals("unsat", solve(result.smtLib
                + "(assert (= " + ROOT_TERM + " true))\n(check-sat)\n"));
    }

    /**
     * The healthy recording alone.  The site executed, so the target is
     * reached and nothing is refused; the failure simply is not reachable
     * from what that one replay showed.
     */
    @Test
    public void healthyPathAloneReachesTheTargetAndIsNotFatal()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("path-merge-healthy");
        JsonObject query = query();
        query.getAsJsonArray("paths").add(path("seed", "GROUP.SEED",
                rootIs(true), notEqual(constant(2), constant(2))));
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        assertEquals(0, merge.getAsJsonArray("gates").size());
        assertEquals(1, result.manifest.getAsJsonArray(
                "targetReachLedger").size());
        assertTrue(merge.getAsJsonArray("paths").get(0).getAsJsonObject()
                .get("admitted").getAsBoolean());
        assertEquals("unsat", solve(result.smtLib));
    }

    /**
     * A predicate the replay published already concrete, at an activation
     * whose slice declares carriers: the value was owed as an expression
     * and arrived as a literal, which is the cut.
     */
    @Test
    public void literalPredicateOverDeclaredCarriersIsAPropagationCut()
            throws Exception {
        Path directory = Files.createTempDirectory("path-merge-cut");
        JsonObject query = query();
        JsonObject path = path("seed", "GROUP.SEED", rootIs(true),
                notEqual(constant(1), constant(0)));
        JsonArray carriers = new JsonArray();
        carriers.add("INSTANCE_FIELD/2#24");
        path.getAsJsonObject(TargetAnchorEvidence.FIELD)
                .add(TargetAnchorEvidence.CARRIERS, carriers);
        query.getAsJsonArray("paths").add(path);
        PathMergeComposer.Result result = compose(directory, query);

        JsonObject merge = result.manifest.getAsJsonObject(
                PathMergeComposer.MANIFEST_FIELD);
        JsonArray gates = merge.getAsJsonArray("gates");
        assertFalse(gates.size() == 0);
        assertEquals(PathMergeComposer.PROPAGATION_CUT,
                gates.get(0).getAsJsonObject().get("kind").getAsString());
        assertFalse(merge.getAsJsonArray("paths").get(0).getAsJsonObject()
                .get("admitted").getAsBoolean());
        assertEquals("FINAL_REFUSED", result.manifest.get(
                ComposedManifest.FINAL_STATUS).getAsString());
    }

    // ------------------------------------------------------------------
    // Fixtures.
    // ------------------------------------------------------------------

    private static PathMergeComposer.Result compose(Path directory,
                                                    JsonObject query)
            throws IOException {
        Path queryFile = directory.resolve("reach_query.jsonl");
        write(queryFile, JsonFields.WRITER.toJson(
                SharedExpressionTable.compact(query)));
        Path summaries = directory.resolve("summaries.jsonl");
        StringBuilder rows = new StringBuilder();
        for (String group : new String[]{"GROUP.SEED", "GROUP.FLIP"}) {
            rows.append(JsonFields.WRITER.toJson(
                    SharedExpressionTable.compact(summary(group))))
                    .append('\n');
        }
        write(summaries, rows.toString());
        PathMergeComposer.Arguments arguments =
                PathMergeComposer.Arguments.parse(new String[]{
                        "--fatal-query", queryFile.toString(),
                        "--summaries", summaries.toString(),
                        "--output",
                        directory.resolve("candidate.smt2").toString(),
                        "--manifest",
                        directory.resolve("manifest.json").toString()});
        return PathMergeComposer.compose(arguments);
    }

    private static JsonObject query() {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 2);
        query.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        query.addProperty("regionId", "REGION.example");
        query.addProperty("occurrenceId", "node0/region/REGION.example#1");
        query.addProperty("sourceKey", "node0");
        query.addProperty("targetSiteId", SITE);
        query.addProperty("targetOccurrence", 1);
        query.addProperty("requiredTakenOutcome", false);
        query.add("paths", new JsonArray());
        return query;
    }

    /** One replay's row: its path condition and its fatal predicate. */
    private static JsonObject path(String caseId, String group,
                                   JsonObject pathCondition,
                                   JsonObject fatalPredicate) {
        JsonObject path = new JsonObject();
        path.addProperty(LocalCaseIdentity.FIELD, "LOCAL_CASE." + caseId);
        path.addProperty("replayGroupId", group);
        path.addProperty("occurrenceId",
                "node0/region/REGION.example#1#a1");
        path.addProperty("topologyEpoch", "iteration-0000");
        path.addProperty("pathSetClosed", true);
        JsonArray constraints = new JsonArray();
        constraints.add(pathCondition);
        constraints.add(fatalPredicate);
        path.add("constraints", constraints);
        path.add(TargetAnchorEvidence.FIELD, TargetAnchorEvidence.build(
                SITE, 1, "node0", "REGION.example",
                "node0/region/REGION.example#1#a1", "iteration-0000",
                false, false, constraints, new JsonObject(),
                new ArrayList<JsonObject>(), new ArrayList<String>()));
        return path;
    }

    /** One replay's summary: the root inventory and what it recorded. */
    private static JsonObject summary(String group) {
        JsonObject summary = new JsonObject();
        summary.addProperty("replayGroupId", group);
        List<JsonObject> events = new ArrayList<>();
        events.add(SymbolicSourceEvidence.event(PHASE, SOURCE,
                "node0/region/REGION.source#1#a1", FIELD_SIGNATURE,
                rootSymbol(), 1, false, ROOT_TERM,
                "GROUP.SEED".equals(group) ? "true" : null));
        SymbolicSourceEvidence.writeTo(summary, events);
        return summary;
    }

    private static JsonObject rootSymbol() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Z");
        symbol.addProperty("_exp", RAW_ROOT);
        return symbol;
    }

    private static JsonObject rootIs(boolean value) {
        JsonObject symbol = rootSymbol();
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", "Z");
        constant.addProperty("_exp", value ? "Y_Z_1" : "Y_Z_0");
        return binary("==", symbol, constant);
    }

    private static JsonObject notEqual(JsonObject left, JsonObject right) {
        return binary("!=", left, right);
    }

    private static JsonObject binary(String operator, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", operator);
        node.add("_left", left);
        node.add("_right", right);
        return node;
    }

    private static JsonObject constant(int value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_java_type", "I");
        node.addProperty("_exp", "Y_I_" + value);
        return node;
    }

    private static void write(Path path, String body) throws IOException {
        Files.write(path, body.getBytes(StandardCharsets.UTF_8));
    }

    // ------------------------------------------------------------------
    // z3.
    // ------------------------------------------------------------------

    private static String solve(String query) throws Exception {
        Process process = new ProcessBuilder("z3", "-in", "-smt2")
                .redirectErrorStream(true).start();
        try (Writer input = new OutputStreamWriter(
                process.getOutputStream(), StandardCharsets.UTF_8)) {
            input.write(query);
        }
        String last = "";
        try (BufferedReader output = new BufferedReader(
                new InputStreamReader(process.getInputStream(),
                        StandardCharsets.UTF_8))) {
            String line;
            while ((line = output.readLine()) != null) {
                if (!line.trim().isEmpty()) last = line.trim();
            }
        }
        process.waitFor();
        return last;
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor()
                    == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
