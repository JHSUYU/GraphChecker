package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** Focused contract tests for whole-path loop counts. */
public class PathLocalLoopCountTest {
    private static final String OCCURRENCE = "occurrence/1";
    private static final String SITE = "<example.Work: void run()>#u4";

            @Test
    public void fixedArrayNeedsOccurrenceLocalExactCardinality() {
        BoundedLoopComposition missing = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)));
        missing.observeCase(OCCURRENCE, pathCase(2, -1));
        assertTrue(missing.gaps().toString().contains(
                LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING));

        BoundedLoopComposition exact = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)));
        exact.observeCase(OCCURRENCE, pathCase(2, 5));
        assertEquals(0, exact.gaps().size());
        JsonObject retained = exact.manifest()
                .getAsJsonArray("boundedLoops").get(0).getAsJsonObject()
                .getAsJsonArray("caseCounts").get(0).getAsJsonObject();
        assertEquals(5, retained
                .getAsJsonArray(LoopBoundPolicy.LOOP_CARDINALITIES)
                .get(0).getAsJsonObject()
                .get(LoopBoundPolicy.LOOP_CARDINALITY).getAsInt());

        BoundedLoopComposition notReached =
                BoundedLoopComposition.ofPlanRows(
                        Collections.singletonList(plan(
                                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)),
                        Collections.singletonList(plan(
                                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)));
        JsonObject skipped = pathCase(0, -1);
        skipped.getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNTS)
                .get(0).getAsJsonObject().addProperty(
                LoopBoundPolicy.PATH_LOOP_REACHED, false);
        notReached.observeCase(OCCURRENCE, skipped);
        assertEquals(notReached.gaps().toString(), 0,
                notReached.gaps().size());
    }

    @Test
    public void composerAuditsEachFatalPathLoopCount() {
        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)));
        JsonObject fatal = new JsonObject();
        fatal.addProperty("occurrenceId", OCCURRENCE);
        JsonArray paths = new JsonArray();
        JsonObject targetPath = pathCase(2, -1);
        targetPath.remove("caseId");
        paths.add(targetPath);
        fatal.add("paths", paths);

        ConcolicSmtComposer.observeFatalLoopCases(model, fatal);

        JsonObject retained = model.manifest()
                .getAsJsonArray("boundedLoops").get(0).getAsJsonObject();
        assertEquals(1, retained.getAsJsonArray("caseCounts").size());
        JsonObject count = retained.getAsJsonArray("caseCounts").get(0)
                .getAsJsonObject();
        assertEquals("TARGET_PATH.0", count.get("caseId").getAsString());
        assertEquals(2, count.get(LoopBoundPolicy.LOOP_BODY_COUNT).getAsInt());
    }

            private static JsonObject plan(String classification, int bound) {
        JsonObject loop = new JsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, SITE);
        loop.addProperty("enclosingMethod", "<example.Work: void run()>");
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID,
                "<example.Work: void run()>#loop:u4");
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                classification);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED);
        if (bound > 0) {
            loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, bound);
            loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                    LoopBoundPolicy.BOUND_FROM_DECLARATION);
        }
        JsonArray sites = new JsonArray();
        sites.add(SITE);
        loop.add(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, sites);
        JsonArray loops = new JsonArray();
        loops.add(loop);
        JsonObject plan = new JsonObject();
        plan.addProperty("occurrenceId", OCCURRENCE);
        plan.add(BoundedLoopComposition.PLAN_FIELD, loops);
        Map<String, Integer> declared = bound > 0
                ? Collections.singletonMap(SITE, Integer.valueOf(bound))
                : Collections.<String, Integer>emptyMap();
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared)
                .writeTo(plan);
        return plan;
    }

    private static JsonObject pathCase(int count, int cardinality) {
        JsonObject row = new JsonObject();
        row.addProperty(LoopBoundPolicy.LOOP_SITE_ID, SITE);
        row.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, count);
        row.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, true);
        if (cardinality >= 0) {
            JsonObject exact = new JsonObject();
            exact.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID,
                    "<example.Work: void run()>#loop:u4");
            exact.addProperty(LoopBoundPolicy.DYNAMIC_OCCURRENCE, 1);
            exact.addProperty(LoopBoundPolicy.LOOP_CARDINALITY, cardinality);
            exact.addProperty("cardinalityAuthority",
                    LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY);
            JsonArray exactRows = new JsonArray();
            exactRows.add(exact);
            row.add(LoopBoundPolicy.LOOP_CARDINALITIES, exactRows);
        }
        JsonArray counts = new JsonArray();
        counts.add(row);
        JsonObject item = new JsonObject();
        item.addProperty("caseId", "CASE." + count + "." + cardinality);
        item.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        item.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        return item;
    }
}
