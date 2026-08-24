package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Assignment overlay is keyed only by an explicit key or engine symbol. */
public class PathReplayTaskFactoryTest {
    private static final String SOURCE_PHASE = "SOURCE_PHASE.TEST.VALUE";

    @Test
    public void rejectsPrimitiveAssignmentFromSourceAndCurrent() {
        assertRejectedFromSourceAndCurrent(new JsonPrimitive(7));
    }

    @Test
    public void rejectsNullAssignmentFromSourceAndCurrent() {
        assertRejectedFromSourceAndCurrent(JsonNull.INSTANCE);
    }

    @Test
    public void rejectsInputSymbolAndMaterializationPathWithoutStableKey() {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:" + SOURCE_PHASE);
        JsonArray path = new JsonArray();
        path.add("holder");
        path.add("value");
        assignment.add("materializationPath", path);

        assertRejectedFromSourceAndCurrent(assignment);
    }

    @Test
    public void rejectsEmptyAssignmentFromSourceAndCurrent() {
        assertRejectedFromSourceAndCurrent(new JsonObject());
    }

    @Test
    public void engineSymbolWithoutExplicitKeyOverlaysSolverAssignment() {
        JsonObject source = source(one(solverAssignment("M_I_value", "1")));
        JsonArray current = one(solverAssignment("M_I_value", "9"));

        JsonObject replay = PathReplayTaskFactory.create(task(), source,
                current, contract(), null);

        JsonArray assignments = replay.getAsJsonArray("modelAssignments");
        assertEquals(1, assignments.size());
        JsonObject merged = assignments.get(0).getAsJsonObject();
        assertEquals("M_I_value", merged.get("engineSymbol").getAsString());
        assertEquals("9", merged.get("value").getAsString());
        assertFalse(merged.has("modelAssignmentKey"));
    }

    @Test
    public void rejectsDuplicateNormalizedKeyWithinSourceArray() {
        JsonArray assignments = new JsonArray();
        assignments.add(withExplicitKey(
                solverAssignment("M_I_first", "1"), " MODEL.VALUE "));
        assignments.add(withExplicitKey(
                solverAssignment("M_I_second", "2"), "MODEL.VALUE"));

        expectRejected(source(assignments), new JsonArray(), "source");
    }

    @Test
    public void rejectsDuplicateNormalizedKeyWithinCurrentArray() {
        JsonArray assignments = new JsonArray();
        assignments.add(solverAssignment(" M_I_value ", "1"));
        assignments.add(solverAssignment("M_I_value", "2"));

        expectRejected(source(new JsonArray()), assignments, "current");
    }

    @Test
    public void normalizedSourceKeyMayBeOverlaidByCurrentKey() {
        JsonObject prior = withExplicitKey(
                solverAssignment("M_I_prior", "1"), " MODEL.VALUE ");
        JsonObject replacement = withExplicitKey(
                solverAssignment("M_I_current", "9"), "MODEL.VALUE");

        JsonObject replay = PathReplayTaskFactory.create(task(),
                source(one(prior)), one(replacement), contract(), null);

        JsonArray assignments = replay.getAsJsonArray("modelAssignments");
        assertEquals(1, assignments.size());
        JsonObject merged = assignments.get(0).getAsJsonObject();
        assertEquals("MODEL.VALUE",
                merged.get("modelAssignmentKey").getAsString());
        assertEquals("M_I_current",
                merged.get("engineSymbol").getAsString());
        assertEquals("9", merged.get("value").getAsString());
    }

    @Test
    public void whitespaceExplicitKeyFallsBackToTrimmedEngineSymbol() {
        JsonObject assignment = solverAssignment(" M_I_value ", "9");
        assignment.addProperty("modelAssignmentKey", " \t ");

        JsonObject replay = PathReplayTaskFactory.create(task(),
                source(new JsonArray()), one(assignment), contract(), null);

        JsonObject merged = replay.getAsJsonArray("modelAssignments")
                .get(0).getAsJsonObject();
        assertEquals("M_I_value", merged.get("engineSymbol").getAsString());
        assertFalse(merged.has("modelAssignmentKey"));
    }

    @Test
    public void rejectsWhitespaceOnlyExplicitAndEngineKeys() {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", " \t ");
        assignment.addProperty("engineSymbol", "  ");

        assertRejectedFromSourceAndCurrent(assignment);
    }

    private static void assertRejectedFromSourceAndCurrent(
            JsonElement malformed) {
        expectRejected(source(one(malformed)), new JsonArray(), "source");
        expectRejected(source(new JsonArray()), one(malformed), "current");
    }

    private static void expectRejected(JsonObject source,
                                       JsonArray current,
                                       String location) {
        try {
            PathReplayTaskFactory.create(task(), source, current,
                    contract(), null);
            fail(location + " assignment without a stable key was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains("model assignment"));
        }
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", "QUERY.path-replay-assignment");
        task.addProperty("goalId", "GOAL.path-replay-assignment");
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        return task;
    }

    private static JsonObject source(JsonArray assignments) {
        JsonObject source = new JsonObject();
        source.addProperty("goalId", "GOAL.path-replay-assignment");
        source.add("modelAssignments", assignments);
        return source;
    }

    private static JsonObject solverAssignment(String engineSymbol,
                                               String value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", engineSymbol);
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:" + SOURCE_PHASE);
        assignment.addProperty("configuredSourceId", "VALUE");
        assignment.addProperty("configuredSourcePhaseId", SOURCE_PHASE);
        assignment.addProperty("configuredSourceFieldSignature",
                "<example.Holder: int value>");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", value);
        return assignment;
    }

    private static JsonObject withExplicitKey(JsonObject assignment,
                                              String key) {
        assignment.addProperty("modelAssignmentKey", key);
        return assignment;
    }

    private static BranchReplayContract contract() {
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        BranchWitness source = BranchWitness.vmPc(
                "<example.Holder: void run()>#u1",
                "<example.Holder: void run()>", 1, 1, true,
                predicate(), 0, metadata);
        return BranchReplayContract.flip(Collections.<BranchWitness>emptyList(),
                source);
    }

    private static JsonObject predicate() {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_value");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_0");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_code_position",
                "<example.Holder: void run()>:1");
        predicate.add("_left", left);
        predicate.addProperty("_op", ">");
        predicate.add("_right", right);
        return predicate;
    }

    private static JsonArray one(JsonElement element) {
        JsonArray result = new JsonArray();
        result.add(element);
        return result;
    }
}
