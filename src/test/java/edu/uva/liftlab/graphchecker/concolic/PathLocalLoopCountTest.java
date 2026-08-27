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

    /**
     * A retained condition loop that declares no {@code K_L} is refused.
     *
     * <p>README {@code LOOP-1}: no retained condition loop inherits the core
     * default.  So the zero-body case is no longer accepted for free, and the
     * above-K case never reaches its count check - the loop is named
     * undeclared where the plan is read, and nothing is admitted for it.</p>
     */
    @Test
    public void anInheritedBoundIsRefusedForZeroAndAboveK() {
        BoundedLoopComposition zero = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)));
        zero.observeCase(OCCURRENCE, pathCase(0, -1));

        assertEquals(zero.gaps().toString(), 1, zero.gaps().size());
        JsonObject undeclared = zero.gaps().get(0);
        assertEquals(BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                undeclared.get("reason").getAsString());
        assertTrue(undeclared.toString(),
                undeclared.get("detail").getAsString().contains("K_L="
                        + LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS));
        assertEquals(0, zero.manifest()
                .getAsJsonArray("boundedLoops").size());

        BoundedLoopComposition beyond = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0)));
        beyond.observeCase(OCCURRENCE, pathCase(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS + 1, -1));
        assertTrue(beyond.gaps().toString().contains(
                BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED));
        assertEquals(0, beyond.manifest()
                .getAsJsonArray("boundedLoops").size());
    }

    /**
     * A declared {@code K_L} that equals the core default is a declaration.
     *
     * <p>Four of HDFS-11741's thirteen rows declare exactly
     * {@link LoopBoundPolicy#MAX_LOOP_BODY_ITERATIONS} for the
     * {@code offerService()} nest.  A stage that dropped them as redundant
     * with the inherited bound would hand this model a loop that declares
     * nothing, and every case of that loop would then be refused as
     * undeclared - so an explicit bound has to survive as its own
     * declaration whatever its value.</p>
     */
    @Test
    public void anExplicitlyDeclaredDefaultStaysADeclaration() {
        int declared = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, declared)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_CONDITION_BOUNDED, declared)));
        model.observeCase(OCCURRENCE, pathCase(declared, -1));

        assertEquals(model.gaps().toString(), 0, model.gaps().size());
        JsonObject retained = model.manifest()
                .getAsJsonArray("boundedLoops").get(0).getAsJsonObject();
        assertEquals(declared,
                retained.get(LoopBoundPolicy.LOOP_BODY_BOUND).getAsInt());
        assertEquals(LoopBoundPolicy.BOUND_FROM_DECLARATION,
                retained.get(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY)
                        .getAsString());
        assertEquals(declared, retained.getAsJsonArray("caseCounts").get(0)
                .getAsJsonObject().get(LoopBoundPolicy.LOOP_BODY_COUNT)
                .getAsInt());
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
        noCount.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
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
    public void retainedLoopReachabilityMarkerIsMandatory() {
        BoundedLoopComposition missing = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)),
                Collections.singletonList(plan(
                        LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, 0)));
        JsonObject path = pathCase(0, -1);
        path.getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNTS)
                .get(0).getAsJsonObject().remove(
                LoopBoundPolicy.PATH_LOOP_REACHED);

        missing.observeCase(OCCURRENCE, path);

        assertTrue(missing.gaps().toString(), missing.gaps().toString()
                .contains(LoopBoundPolicy
                        .PATH_LOOP_REACHABILITY_MISSING));
    }

    @Test
    public void planWithoutRetainedLoopsNeedsNoLoopBoundAuthority() {
        JsonObject plan = new JsonObject();
        plan.addProperty("occurrenceId", OCCURRENCE);

        BoundedLoopComposition model =
                BoundedLoopComposition.ofPlanRows(
                        Collections.singletonList(plan),
                        Collections.<JsonObject>emptyList());

        assertEquals(0, model.manifest()
                .getAsJsonArray("boundedLoops").size());
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
        assertEquals(3, model.manifest().getAsJsonArray("boundedLoops")
                .get(0).getAsJsonObject()
                .get(LoopBoundPolicy.LOOP_BODY_BOUND).getAsInt());
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

    /**
     * README {@code LOOP-1} is a statement about the witness, not about every
     * loop the run walked: a retained condition loop whose trip count nothing
     * the failure reads can observe states no bound obligation, so its
     * missing declaration is not a coverage gap.  Only an explicit decision
     * under the planner's authority says so; silence stays required.
     */
    @Test
    public void anUndeclaredBoundOutsideTheFailureDemandIsNotAGap() {
        JsonObject undeclared = plan(
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0);
        assertEquals(1, BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(undeclared),
                Collections.singletonList(undeclared)).gaps().size());

        JsonObject immaterial = plan(
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 0);
        JsonObject loop = immaterial.getAsJsonArray(
                BoundedLoopComposition.PLAN_FIELD).get(0).getAsJsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT, false);
        loop.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                LoopBoundPolicy.FAILURE_DEMANDED_LOOP_SCOPE);

        assertEquals(0, BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(immaterial),
                Collections.singletonList(immaterial)).gaps().size());

        // A decision under an unknown authority relaxes nothing.
        loop.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                "SOMETHING_ELSE_V9");
        assertEquals(1, BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(immaterial),
                Collections.singletonList(immaterial)).gaps().size());
    }

    /** The same answer never silences a missing bound authority for a loop
     * the failure does read, nor a disagreement about any loop at all. */
    @Test
    public void anImmaterialLoopStillNamesADisagreement() {
        JsonObject immaterial = plan(
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 3);
        JsonObject loop = immaterial.getAsJsonArray(
                BoundedLoopComposition.PLAN_FIELD).get(0).getAsJsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT, false);
        loop.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                LoopBoundPolicy.FAILURE_DEMANDED_LOOP_SCOPE);
        JsonObject other = plan(LoopBoundPolicy.LOOP_CONDITION_BOUNDED, 4);

        BoundedLoopComposition model = BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(immaterial),
                java.util.Arrays.asList(immaterial, other));

        assertEquals(model.gaps().toString(), 1, model.gaps().size());
        assertEquals(BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES,
                model.gaps().get(0).get("reason").getAsString());
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
