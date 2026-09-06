package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/** Focused contract tests for closing a bounded loop-body occurrence axis. */
public class BoundedLoopOccurrenceClosureTest {
    private static final String OCCURRENCE =
            "cluster0/nn0#epoch1/region/REGION.update#1";
    private static final String METHOD =
            "<example.HeartbeatMonitor: void run()>";
    private static final String SITE = METHOD + "#u4";
    private static final String RUNTIME_LOOP = METHOD + "#loop:u1";

    private static final String ADD_KEYS_SITE = METHOD + "#u20";
    private static final String ADD_KEYS_RUNTIME = METHOD + "#loop:u20";
    private static final String REMOVE_EXPIRED_SITE = METHOD + "#u40";
    private static final String REMOVE_EXPIRED_RUNTIME =
            METHOD + "#loop:u40";

    @Test
    public void hdfsAddKeysSixAndRemoveFiveOfFourteenCloseAtK2() {
        BoundedLoopComposition model = hdfsModel(true, true);
        observe(model, hdfsActivation(1,
                fixedCount(0, false), conditionCount(0, false), "NORMAL"));
        observe(model, hdfsActivation(2,
                fixedCount(6, true, cardinality(1, 6)),
                conditionCount(5, true), "NORMAL"));

        assertEquals(Collections.singleton(OCCURRENCE),
                model.closedOccurrenceAddresses());
    }

    @Test
    public void aConditionLoopThatReachesItsBoundStaysOpen() {
        BoundedLoopComposition model = hdfsModel(true, true);
        observe(model, hdfsActivation(1,
                fixedCount(0, false), conditionCount(0, false), "NORMAL"));
        observe(model, hdfsActivation(2,
                fixedCount(6, true, cardinality(1, 6)),
                conditionCount(14, true), "NORMAL"));

        assertFalse(model.closedOccurrenceAddresses().contains(OCCURRENCE));
    }

    private static BoundedLoopComposition hdfsModel(
            boolean fixedRelevant, boolean conditionRelevant) {
        return BoundedLoopComposition.ofPlanRows(
                Collections.singletonList(hdfsPlan(
                        fixedRelevant, conditionRelevant)),
                Collections.singletonList(hdfsSummary()));
    }

    private static void observe(BoundedLoopComposition model,
                                JsonObject pathCase) {
        model.observeCase(OCCURRENCE, pathCase);
    }

    private static JsonObject hdfsPlan(boolean fixedRelevant,
                                       boolean conditionRelevant) {
        JsonObject plan = new JsonObject();
        plan.addProperty("occurrenceId", OCCURRENCE);
        JsonArray retained = new JsonArray();
        retained.add(retainedCondition(SITE, RUNTIME_LOOP, 2, true));
        retained.add(retainedFixed(fixedRelevant));
        retained.add(retainedCondition(REMOVE_EXPIRED_SITE,
                REMOVE_EXPIRED_RUNTIME, 14, conditionRelevant));
        plan.add(BoundedLoopComposition.PLAN_FIELD, retained);

        Map<String, Integer> bounds = new LinkedHashMap<>();
        bounds.put(SITE, Integer.valueOf(2));
        bounds.put(REMOVE_EXPIRED_SITE, Integer.valueOf(14));
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, bounds)
                .writeTo(plan);
        plan.addProperty(LoopBoundPolicy.ROOT_AUTHORITY,
                LoopBoundPolicy.LOOP_BODY_ROOT);
        JsonObject root = new JsonObject();
        root.addProperty("authority", LoopBoundPolicy.LOOP_BODY_ROOT);
        root.addProperty(LoopBoundPolicy.ROOT_LOOP_METHOD, METHOD);
        root.addProperty(LoopBoundPolicy.HEADER_UNIT_INDEX, 1);
        root.addProperty(LoopBoundPolicy.LOOP_SITE_ID, SITE);
        root.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, RUNTIME_LOOP);
        root.add(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, strings(SITE));
        plan.add(LoopBoundPolicy.ROOT_LOOP, root);
        return plan;
    }

    private static JsonObject hdfsSummary() {
        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", OCCURRENCE);
        summary.addProperty("pathCoverageState", "SEED_ONLY");
        summary.addProperty("relationallyComplete", true);
        Map<String, Integer> bounds = new LinkedHashMap<>();
        bounds.put(SITE, Integer.valueOf(2));
        bounds.put(REMOVE_EXPIRED_SITE, Integer.valueOf(14));
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, bounds)
                .writeTo(summary);
        return summary;
    }

    private static JsonObject retainedCondition(String site, String runtime,
                                                int bound,
                                                boolean relevant) {
        JsonObject loop = new JsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, site);
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, runtime);
        loop.addProperty("enclosingMethod", METHOD);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED);
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, bound);
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                LoopBoundPolicy.BOUND_FROM_DECLARATION);
        loop.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT, relevant);
        loop.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                LoopBoundPolicy.FAILURE_DEMANDED_LOOP_SCOPE);
        loop.add(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, strings(site));
        return loop;
    }

    private static JsonObject retainedFixed(boolean relevant) {
        JsonObject loop = new JsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, ADD_KEYS_SITE);
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, ADD_KEYS_RUNTIME);
        loop.addProperty("enclosingMethod", METHOD);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED);
        loop.addProperty(LoopBoundPolicy.LOOP_FAILURE_RELEVANT, relevant);
        loop.addProperty(LoopBoundPolicy.LOOP_RELEVANCE_AUTHORITY,
                LoopBoundPolicy.FAILURE_DEMANDED_LOOP_SCOPE);
        loop.add(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS,
                strings(ADD_KEYS_SITE));
        return loop;
    }

    private static JsonObject hdfsActivation(int ordinal, JsonObject fixed,
                                             JsonObject condition,
                                             String terminalKind) {
        JsonObject root = retainedCondition(SITE, RUNTIME_LOOP, 2, true);
        root.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, 1);
        root.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, true);

        JsonArray counts = new JsonArray();
        counts.add(root);
        counts.add(fixed);
        counts.add(condition);
        JsonObject pathCase = new JsonObject();
        pathCase.addProperty("caseId", "CASE.hdfs.a" + ordinal);
        pathCase.addProperty("occurrenceId", OCCURRENCE + "#a" + ordinal);
        pathCase.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                OCCURRENCE);
        pathCase.addProperty(PathObservation.ACTIVATION_ORDINAL, ordinal);
        pathCase.addProperty("relationallyComplete", true);
        pathCase.add("terminal", terminal(terminalKind));
        pathCase.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        return pathCase;
    }

    private static JsonObject fixedCount(int bodyCount, boolean reached,
                                         JsonObject... cardinalities) {
        JsonObject row = retainedFixed(true);
        row.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
        row.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, reached);
        if (cardinalities.length > 0) {
            JsonArray exact = new JsonArray();
            for (JsonObject cardinality : cardinalities) {
                exact.add(cardinality);
            }
            row.add(LoopBoundPolicy.LOOP_CARDINALITIES, exact);
        }
        return row;
    }

    private static JsonObject cardinality(int ordinal, int value) {
        JsonObject row = new JsonObject();
        row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, ADD_KEYS_RUNTIME);
        row.addProperty(LoopBoundPolicy.DYNAMIC_OCCURRENCE, ordinal);
        row.addProperty(LoopBoundPolicy.LOOP_CARDINALITY, value);
        row.addProperty("cardinalityAuthority",
                LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY);
        return row;
    }

    private static JsonObject conditionCount(int bodyCount,
                                             boolean reached) {
        JsonObject row = retainedCondition(REMOVE_EXPIRED_SITE,
                REMOVE_EXPIRED_RUNTIME, 14, true);
        row.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
        row.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, reached);
        return row;
    }

    private static JsonObject terminal(String kind) {
        JsonObject terminal = new JsonObject();
        terminal.addProperty("kind", kind);
        return terminal;
    }

    private static JsonArray strings(String... values) {
        JsonArray encoded = new JsonArray();
        for (String value : Arrays.asList(values)) encoded.add(value);
        return encoded;
    }
}
