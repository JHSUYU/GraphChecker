package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class InitialContainerObservationTest {
    @Test
    public void recognizesOnlyConcreteReadsOfInitialRegionState() {
        JsonObject equality = equality("REGION.2.in.4", "int", "int");
        assertTrue(InitialContainerObservation.isConcreteEquality(equality));

        assertFalse(InitialContainerObservation.isConcreteEquality(
                equality("LOCAL.container", "int", "int")));
        assertFalse(InitialContainerObservation.isConcreteEquality(
                equality("REGION.2.in.4", "int", "boolean")));
    }

    @Test
    public void recognizesCanonicalFieldMaterializationByExactInputPort() {
        String symbol = "M_L_field_REGION.12.in.34.payloads_owner.Type";
        JsonObject equality = equality(symbol, "int", "int");
        assertTrue(InitialContainerObservation.isConcreteEquality(equality));
        assertTrue("REGION.12.in.34".equals(
                InitialContainerObservation.initialRead(
                        equality.getAsJsonObject("_left")).inputPort));

        assertFalse(InitialContainerObservation.isConcreteEquality(
                equality("M_L_field_REGION.12.in.34$x", "int", "int")));
        assertFalse(InitialContainerObservation.isConcreteEquality(
                equality("M_I_field_REGION.12.in.34", "int", "int")));
        assertFalse(InitialContainerObservation.isConcreteEquality(
                equality("M_L_field_REGION.$.in.34", "int", "int")));
    }

    @Test
    public void recognizesStableUuidRegionAndPortIds() {
        String port = "REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838"
                + ".in.fc915256-5ad9-3272-977b-2ccd8a7699a9";
        JsonObject equality = equality("M_L_field_" + port,
                "int", "int");
        InitialContainerObservation.Read read =
                InitialContainerObservation.initialRead(
                        equality.getAsJsonObject("_left"));

        assertTrue(read != null);
        assertTrue(port.equals(read.inputPort));
    }

    @Test
    public void recognizesCanonicalPrimitiveArrayMaterialization() {
        String symbol = "M_[_field_REGION.12.in.34";
        JsonObject equality = equality(symbol, "int", "int");
        assertTrue(InitialContainerObservation.isConcreteEquality(equality));
        assertTrue("REGION.12.in.34".equals(
                InitialContainerObservation.initialRead(
                        equality.getAsJsonObject("_left")).inputPort));
    }

    @Test
    public void recognizesConcreteOrderedAssociativeIteration() {
        JsonObject equality = iterationEquality(
                "M_L_field_REGION.4.in.2", "KEY_VIEW", 0);

        assertTrue(InitialContainerObservation.isConcreteEquality(equality));
        InitialContainerObservation.Read read =
                InitialContainerObservation.initialRead(
                        equality.getAsJsonObject("_left"));
        assertTrue(read.concreteSelector());
        assertTrue("KEY".equals(read.iterationProjection));
        assertTrue("ITERATION:KEY:0".equals(read.selectorIdentity()));

        assertFalse(InitialContainerObservation.isConcreteEquality(
                iterationEquality("LOCAL.container", "KEY_VIEW", 0)));
        assertFalse(InitialContainerObservation.isConcreteEquality(
                iterationEquality("M_L_field_REGION.4.in.2",
                        "ENTRY_VIEW", 0)));
    }

    @Test
    public void relevanceSelectedSnapshotAllowsTheCapacityOnly() {
        int capacity = LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY;
        JsonArray atCapacity = new JsonArray();
        JsonArray beyond = new JsonArray();
        for (int index = 0; index < capacity + 1; index++) {
            JsonObject cell = equality("REGION.container.in.values",
                    "int", "int", index);
            beyond.add(cell);
            if (index < capacity) atCapacity.add(cell.deepCopy());
        }

        assertTrue(InitialContainerObservation
                .failureRelevantCapacityIssue(atCapacity).isEmpty());
        assertTrue(InitialContainerObservation
                .failureRelevantCapacityIssue(beyond).contains(
                        "SYMBOLIC_CONTAINER_RELEVANT_CELL_"
                                + "CAPACITY_EXCEEDED"));
    }

    @Test
    public void pathObservationRejectsOneCellBeyondTheCapacity() {
        JsonObject summary = new JsonObject();
        summary.addProperty("goalId", "GOAL.container.capacity");
        summary.addProperty("regionId", "REGION.container");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(8).writeTo(summary);
        JsonArray path = new JsonArray();
        for (int index = 0; index
                < LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY + 1;
                index++) {
            path.add(equality("REGION.container.in.values",
                    "int", "int", index));
        }
        summary.add("pathCondition", path);
        summary.add("branchMappings", new JsonArray());
        summary.add("outputExpressions", new JsonObject());

        try {
            PathObservation.decode(summary, null);
            fail("oversized relevant snapshot must fail closed");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains(
                    "SYMBOLIC_CONTAINER_RELEVANT_CELL_"
                            + "CAPACITY_EXCEEDED"));
        }
    }

    private static JsonObject equality(String symbol, String readType,
                                       String valueType) {
        return equality(symbol, readType, valueType, 1);
    }

    private static JsonObject equality(String symbol, String readType,
                                       String valueType, int cellIndex) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_exp", symbol);

        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "INDEXED");
        state.addProperty("operation", "STATE");
        state.add("receiver", identity);

        JsonObject index = new JsonObject();
        index.addProperty("_type", "ConstExpr");
        index.addProperty("_java_type", "int");
        index.addProperty("_exp", "CONST_INT_" + cellIndex);

        JsonObject read = new JsonObject();
        read.addProperty("_type", "ContainerRelation");
        read.addProperty("shape", "INDEXED");
        read.addProperty("operation", "READ");
        read.addProperty("_java_type", readType);
        read.add("receiver", state);
        JsonArray arguments = new JsonArray();
        arguments.add(index);
        read.add("arguments", arguments);

        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConSymbolExp");
        value.addProperty("_java_type", valueType);
        value.addProperty("_exp", "CONST_INT_7");

        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", "==");
        result.add("_left", read);
        result.add("_right", value);
        return result;
    }

    private static JsonObject iterationEquality(
            String symbol, String viewKind, int cursor) {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_exp", symbol);

        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.add("receiver", identity);

        JsonObject view = new JsonObject();
        view.addProperty("_type", "ContainerRelation");
        view.addProperty("shape", "ASSOCIATIVE");
        view.addProperty("operation", viewKind);
        view.add("receiver", state);

        JsonObject index = new JsonObject();
        index.addProperty("_type", "ConstExpr");
        index.addProperty("_java_type", "int");
        index.addProperty("_exp", "CONST_INT_" + cursor);

        JsonObject next = new JsonObject();
        next.addProperty("_type", "ContainerRelation");
        next.addProperty("shape", "ASSOCIATIVE");
        next.addProperty("operation", "NEXT");
        next.addProperty("_java_type", "int");
        next.add("receiver", view);
        JsonArray arguments = new JsonArray();
        arguments.add(index);
        next.add("arguments", arguments);

        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConSymbolExp");
        value.addProperty("_java_type", "int");
        value.addProperty("_exp", "CONST_INT_-7");

        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", "==");
        result.add("_left", next);
        result.add("_right", value);
        return result;
    }
}
