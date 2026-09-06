package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * README {@code PC-1}: "A case guard contains the relevant decisions and
 * nothing from transport/startup noise."
 *
 * <p>Both halves of that sentence are pinned here for the fatal target case,
 * which is where the guard is consumed verbatim.  The relevant decisions are
 * the branch decisions this execution recorded on its way to the target -
 * dropping one would weaken the reachability query into admitting a model
 * that never reaches the target.  The noise is the other channel: the
 * container and method relations the VM recorded while transport, SASL and
 * startup library frames ran under the same occurrence.  Those reach the
 * guard only through a dependency edge from a decision, never by position.
 *
 * <p>The second test pins the reader side of the same item: the ambient VM
 * path condition has no reader left at all, so an older or patched VM that
 * still serialises one cannot silently re-admit that noise.</p>
 */
public class TargetCaseGuardSliceTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();


    private static final String REGION = "REGION.GUARD.SLICE";
    private static final String OCCURRENCE =
            "slice/target#epoch0/region/" + REGION + "#1";
    private static final String GOAL = "GOAL.TARGET_REACH.GUARD_SLICE";
    private static final String METHOD = "<example.Target: void run()>";
    private static final String GUARD_SITE = METHOD + "#u4";
    private static final String TARGET_SITE = METHOD + "#u9";
    private static final String GATE = "M_I_field_example/Target_gate";
    private static final String KEY = "M_I_field_example/Target_keyId";
    private static final String SASL = "M_I_field_sasl/Negotiation_state";
    private static final String TRANSPORT_RELATION = "AUX.SASL.NEGOTIATION";
    private static final String DEMANDED_RELATION = "AUX.KEY.MAP.READ";

        /**
     * The same slice, taken by the class that owns it, so a consumer that is
     * not the fatal query cannot read the wide prefix back either.
     */
    @Test
    public void theProjectedTargetGuardIsTheSameSlice() {
        PathObservation observation = PathObservation.decode(
                targetSummary(), null);

        JsonArray projected = observation.relationPathCondition();
        assertEquals(projected.toString(), 3, projected.size());
        assertFalse(projected.toString(),
                projected.toString().contains(TRANSPORT_RELATION));
        // The kept rows keep their recorded positions, because the query
        // cuts its prefix on them and row 2 is no longer at offset 2.
        assertEquals(Arrays.asList(0, 2, 3),
                observation.relationPathConditionPositions());
    }

        // --------------------------------------------------------------- fixtures

    /**
     * One imported target case in the shape the current VM produces: the
     * selected branch witnesses plus the bounded auxiliary constraints, all
     * at their recorded positions in one compact array.
     */
    private static JsonObject targetSummary() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE + "#a1");
        row.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        row.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("relationallyComplete", true);
        row.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        row.addProperty("taskId", "TASK.SEED.GUARD.SLICE");
        row.addProperty("sourceKey", "slice/target#epoch0");
        row.addProperty("pathConditionAuthority",
                "VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1");
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);

        JsonArray pathCondition = new JsonArray();
        pathCondition.add(predicate(GATE, ">", 0));
        pathCondition.add(containerRelation(TRANSPORT_RELATION, SASL));
        pathCondition.add(containerRelation(DEMANDED_RELATION, KEY));
        pathCondition.add(predicate(KEY, "<=", 10));
        row.add("pathCondition", pathCondition);

        JsonArray mappings = new JsonArray();
        mappings.add(mapping("PATH_ASSUMPTION", 0, witness(GUARD_SITE, 4,
                true, predicate(GATE, ">", 0), 0)));
        mappings.add(mapping("EXPLORE", 3, witness(TARGET_SITE, 9, true,
                predicate(KEY, "<=", 10), 3)));
        row.add("branchMappings", mappings);

        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", TARGET_SITE);
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        row.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        row.add("edgeBindings", new JsonArray());
        return row;
    }

            private static JsonObject mapping(String policy, int summaryPcIndex,
                                      JsonObject witness) {
        JsonObject row = new JsonObject();
        row.addProperty("policy", policy);
        row.addProperty("summaryPcIndex", summaryPcIndex);
        row.add("witness", witness);
        return row;
    }

    private static JsonObject witness(String siteId, int unitIndex,
                                      boolean outcome, JsonObject predicate,
                                      int vmPcIndex) {
        JsonObject site = new JsonObject();
        site.addProperty("method", METHOD);
        site.addProperty("occurrence", 1);
        site.addProperty("siteId", siteId);
        site.addProperty("unitIndex", unitIndex);
        JsonObject witness = new JsonObject();
        witness.addProperty("kind", "BINARY_BRANCH_WITNESS");
        witness.addProperty("schemaVersion", 1);
        witness.addProperty("predicateNormalization", "IDENTITY");
        witness.add("site", site);
        witness.add("sourceSatisfiedPredicate", predicate);
        witness.addProperty("sourceTakenOutcome", outcome);
        witness.addProperty("vmPcIndex", vmPcIndex);
        return witness;
    }

    /**
     * One bounded auxiliary constraint, as the VM's separate channel carries
     * it: a container relation over exactly one symbol.
     */
    private static JsonObject containerRelation(String relationId,
                                                String symbol) {
        JsonObject operand = new JsonObject();
        operand.addProperty("_type", "SymbolExpression");
        operand.addProperty("_java_type", "I");
        operand.addProperty("_exp", symbol);
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", "ContainerRelation");
        relation.addProperty("relationId", relationId);
        relation.addProperty("kind", "ASSOCIATIVE_READ");
        relation.add("member", operand);
        return relation;
    }

    private static JsonObject predicate(String symbol, String operator,
                                        int constant) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", symbol);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_code_position", METHOD + ":42");
        predicate.add("_left", left);
        predicate.addProperty("_op", operator);
        predicate.add("_right", right);
        return predicate;
    }
}
