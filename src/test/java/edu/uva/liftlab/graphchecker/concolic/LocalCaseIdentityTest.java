package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;

/** The local control identity is independent of execution observations. */
public class LocalCaseIdentityTest {

    @Test
    public void runtimeAndExpressionFieldsDoNotSplitOneLocalCase() {
        JsonObject first = summary("R/occurrence-1#a1", true,
                "M_value_1");
        JsonObject second = first.deepCopy();
        second.addProperty("summaryId", "SUMMARY.second");
        second.addProperty("taskId", "TASK.second");
        second.addProperty("replayGroupId", "REPLAY.second");
        second.addProperty("boundarySessionScope", "SESSION.second");
        second.addProperty("familySnapshotDigest", "FAMILY.second");
        second.addProperty("topologyEpoch", "EPOCH.second");
        JsonObject nested = second.getAsJsonArray("pathCondition").get(0)
                .getAsJsonObject().getAsJsonObject("_left");
        nested.addProperty("_exp", "M_value_2");
        nested.addProperty(SharedExpressionTable.ANCHOR, "EXPR.changed");
        nested.addProperty("eventId", 999L);
        nested.addProperty("javaThreadId", 42L);

        assertEquals(LocalCaseIdentity.compute(first),
                LocalCaseIdentity.compute(second));
        assertFalse(CanonicalJson.render(LocalCaseIdentity.payload(first))
                .contains("pathConditionIndex"));
    }

    private static JsonObject summary(String occurrence, boolean outcome,
                                      String symbol) {
        JsonObject row = new JsonObject();
        row.addProperty("sourceKey", "SOURCE.R");
        row.addProperty("regionId", "REGION.R");
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("normalExit", true);
        row.addProperty("boundedExit", false);
        row.addProperty("exceptionType", "");

        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", symbol);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_0");
        JsonObject condition = new JsonObject();
        condition.addProperty("_code_position",
                "<fixture.R: void run()>:7");
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_java_type", "Z");
        condition.addProperty("_op", outcome ? ">" : "<=");
        condition.add("_left", left);
        condition.add("_right", right);
        JsonArray path = new JsonArray();
        path.add(condition);
        row.add("pathCondition", path);

        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attested("SITE.R",
                        "<fixture.R: void run()>", 7, 1, outcome),
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        row.add("branchMappings", mappings);
        return row;
    }
}
