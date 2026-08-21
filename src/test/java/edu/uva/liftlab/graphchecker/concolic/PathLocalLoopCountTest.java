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
    public void countQualifiesOneGuardedCaseWithoutCreatingSlots() {
        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)));
        model.observeCase(OCCURRENCE, pathCase(2, -1));

        JsonObject loop = model.manifest().getAsJsonArray("boundedLoops")
                .get(0).getAsJsonObject();
        assertEquals(1, loop.getAsJsonArray("caseCounts").size());
        assertEquals(2, loop.getAsJsonArray("caseCounts").get(0)
                .getAsJsonObject().get(LoopBoundPolicy.LOOP_BODY_COUNT)
                .getAsInt());
        assertEquals(0, model.gaps().size());
    }

    @Test
    public void inheritedBoundAcceptsZeroButStillRejectsAboveK() {
        BoundedLoopComposition zero = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)));
        zero.observeCase(OCCURRENCE, pathCase(0, -1));

        assertEquals(0, zero.gaps().size());
        JsonObject retained = zero.manifest()
                .getAsJsonArray("boundedLoops").get(0).getAsJsonObject();
        assertEquals(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                retained.get(LoopBoundPolicy.LOOP_BODY_BOUND).getAsInt());
        assertEquals(LoopBoundPolicy.BOUND_FROM_POLICY,
                retained.get(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY)
                        .getAsString());

        BoundedLoopComposition beyond = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)));
        beyond.observeCase(OCCURRENCE, pathCase(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS + 1, -1));
        assertTrue(beyond.gaps().toString().contains(
                LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND));
    }

    @Test
    public void missingCountIsCoverageAndOutOfBoundIsNamed() {
        BoundedLoopComposition missing = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)));
        JsonObject noCount = new JsonObject();
        noCount.addProperty("caseId", "CASE.missing");
        missing.observeCase(OCCURRENCE, noCount);
        assertTrue(missing.gaps().toString().contains(
                LoopBoundPolicy.PATH_LOOP_COUNT_MISSING));

        BoundedLoopComposition beyond = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3)));
        beyond.observeCase(OCCURRENCE, pathCase(4, -1));
        assertTrue(beyond.gaps().toString().contains(
                LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND));
    }

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
    }

    @Test
    public void planWithoutRetainedLoopsNeedsNoLoopBoundAuthority() {
        JsonObject plan = new JsonObject();
        plan.addProperty("occurrenceId", OCCURRENCE);

        BoundedLoopComposition model =
                BoundedLoopComposition.ofPlanRows(
                        Collections.singletonList(plan),
                        Collections.<JsonObject>emptyList());

        assertEquals(0, model.boundedLoops().size());
        assertEquals(0, model.gaps().size());
    }

    @Test
    public void runtimePlanJoinsSameOccurrenceSummaryBound() {
        JsonObject runtimePlan = plan(
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3);
        runtimePlan.remove(LoopBoundPolicy.FIELD);
        JsonObject selectedSummary = new JsonObject();
        selectedSummary.addProperty("occurrenceId", OCCURRENCE);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                Collections.singletonMap(SITE, 3))
                .writeTo(selectedSummary);

        BoundedLoopComposition model =
                BoundedLoopComposition.ofPlanRows(
                        Collections.singletonList(runtimePlan),
                        Collections.singletonList(selectedSummary));

        assertEquals(0, model.gaps().size());
        assertEquals(3, model.loopOf(OCCURRENCE, SITE).bodyBound);
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
        item.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        return item;
    }
}
