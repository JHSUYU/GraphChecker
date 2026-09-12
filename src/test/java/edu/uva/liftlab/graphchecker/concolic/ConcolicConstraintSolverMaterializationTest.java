package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicConstraintSolverMaterializationTest {
    @Test
    public void materializesOccurrenceScopedBoundedScalarAction()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String input = "REGION.timer.in.now";
        String raw = "M_J_field_" + input
                + ".occ.deadbeef_java/lang/Long";
        JsonObject target = binary(symbol(raw), ">", constant(10));
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 1L);
        event.addProperty("contextId", 1L);
        BranchWitness source = BranchWitness.vmPcImmutable("TEST#u1",
                "<test.Timer: void run()>", 1, 1, false,
                BranchPredicateAlgebra.complement(target), 0, event);

        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("timer-query"));
        query.addProperty("regionId", "REGION.timer");
        query.addProperty("sourceActivationOccurrenceId",
                "test/node#epoch0/region/REGION.timer#1#a1");
        query.add("replayContract",
                BranchReplayContract.atSource(source).toJson());
        JsonObject context = new JsonObject();
        context.addProperty("schemaVersion", SolverPathContext.SCHEMA_VERSION);
        context.addProperty("kind", SolverPathContext.KIND);
        context.addProperty("authority", SolverPathContext.AUTHORITY);
        context.add("constraints", new JsonArray());
        query.add("solverPathContext", context);
        query.add("consumerAnchorCaseDependencies", new JsonArray());

        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("symbolicDemand", "BOUNDED_STATE_FRONTIER");
        action.addProperty("symbol", input);
        action.addProperty("javaType", "long");
        action.addProperty("observed", true);
        action.addProperty("primitiveValue", "0");
        JsonArray actions = new JsonArray();
        actions.add(action);
        JsonObject activation = new JsonObject();
        activation.add("inputActions", actions);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(query,
                        Collections.singletonList(activation), activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        assertEquals(input, result.modelAssignments.get(0).getAsJsonObject()
                .get("inputSymbol").getAsString());
    }

    @Test
    public void projectsPropagatedTargetMapReadToExactLiveAccess()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String mapInput = "REGION.map.in.values";
        String keyInput = "REGION.map.in.key";
        JsonObject mapAction = new JsonObject();
        mapAction.addProperty("mode", "SYMBOLIC");
        mapAction.addProperty("symbolicDemand",
                "BOUNDED_CONTAINER_STATE");
        mapAction.addProperty("symbol", mapInput);
        mapAction.addProperty("javaType", "java.util.Map");
        mapAction.addProperty("sourceKey", "test/node#epoch0");
        mapAction.addProperty("fieldReceiverObjectId", 17L);
        String field = "<test.Holder: java.util.Map values>";
        JsonArray path = new JsonArray();
        path.add("values");
        mapAction.add("fieldPath", path);
        JsonArray declarations = new JsonArray();
        declarations.add(field);
        mapAction.add("fieldPathDeclarations", declarations);
        mapAction.addProperty("leafFieldSignature", field);
        String stateSymbol = SharedStateEvidence
                .mapStateSymbolForAction(mapAction);

        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.addProperty("_java_type", "L");
        JsonObject stateIdentity = symbol(stateSymbol);
        stateIdentity.addProperty("_java_type", "java/util/HashMap");
        state.add("receiver", stateIdentity);
        state.add("arguments", new JsonArray());

        JsonObject mapRead = new JsonObject();
        mapRead.addProperty("_type", "ContainerRelation");
        mapRead.addProperty("shape", "ASSOCIATIVE");
        mapRead.addProperty("operation", "READ");
        mapRead.addProperty("_java_type", "L");
        mapRead.add("receiver", state);
        JsonArray readArguments = new JsonArray();
        JsonObject key = symbol(keyInput);
        key.addProperty("_java_type", "I");
        readArguments.add(key);
        mapRead.add("arguments", readArguments);

        String family = "CBF." + CanonicalJson.sha256("initial-map");
        String owner = "INITIAL_SOURCE."
                + CanonicalJson.sha256("initial-map-owner");
        String writerSelector = LocalCaseIdentity.selector(owner);
        String readIdentity = "RFC."
                + CanonicalJson.sha256("target-map-read");
        String candidateIdentity = "RFC_ARM."
                + CanonicalJson.sha256("target-map-candidate");
        String readSelector = "read_selector__" + CanonicalJson.sha256(
                readIdentity + "\n" + candidateIdentity);
        JsonObject candidate = new JsonObject();
        candidate.addProperty("selector", readSelector);
        candidate.addProperty("fieldVersionId", 1L);
        candidate.addProperty("versionKind", "INITIAL");
        candidate.add("expression", mapRead);
        candidate.add("pathGuard", SharedStateEvidence.emptyConjunction());
        candidate.addProperty(
                SymbolicPropagationClosure.WRITER_CASE_FAMILY, family);
        candidate.addProperty(
                SymbolicPropagationClosure.WRITER_CASE_OWNER, owner);
        candidate.addProperty(
                SymbolicPropagationClosure.WRITER_CASE_SELECTOR,
                writerSelector);
        JsonObject closureCase = new JsonObject();
        closureCase.addProperty(
                SymbolicPropagationClosure.WRITER_CASE_FAMILY, family);
        closureCase.addProperty(
                SymbolicPropagationClosure.WRITER_CASE_OWNER, owner);
        closureCase.addProperty(
                SymbolicPropagationClosure.WRITER_CASE_SELECTOR,
                writerSelector);
        JsonArray closure = new JsonArray();
        closure.add(closureCase);
        candidate.add(SymbolicPropagationClosure.WRITER_CASE_CLOSURE,
                closure);
        candidate.addProperty(
                SymbolicPropagationClosure.READ_CANDIDATE_IDENTITY,
                candidateIdentity);

        JsonObject guardedRead = new JsonObject();
        guardedRead.addProperty("_type",
                SharedStateEvidence.GUARDED_READ_TYPE);
        guardedRead.addProperty("_java_type", "L");
        guardedRead.addProperty("expressionAuthority",
                SharedStateEvidence.GUARDED_READ_AUTHORITY);
        guardedRead.addProperty("readEventId", 1L);
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 17L);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        guardedRead.add("location", location);
        guardedRead.addProperty("writerSetComplete", true);
        JsonArray exactlyOne = new JsonArray();
        exactlyOne.add(readSelector);
        guardedRead.add("exactlyOne", exactlyOne);
        JsonArray candidates = new JsonArray();
        candidates.add(candidate);
        guardedRead.add("candidates", candidates);
        guardedRead.addProperty(
                SymbolicPropagationClosure.READ_CHOICE_IDENTITY,
                readIdentity);

        JsonObject sourcePredicate = binary(guardedRead, "!=",
                nullReference());
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 1L);
        event.addProperty("contextId", 1L);
        BranchWitness source = BranchWitness.vmPcImmutable("TEST#u1",
                "<test.Holder: void run()>", 1, 1, true,
                sourcePredicate, 0, event);

        JsonObject query = query(source);
        JsonObject dependency = new JsonObject();
        dependency.addProperty(VmExpressionIr.FAMILY_KEY, family);
        dependency.addProperty("selectionPolicy",
                SymbolicPropagationClosure.READ_FROM_DEPENDENCY_POLICY);
        JsonObject arm = new JsonObject();
        arm.addProperty("selector", writerSelector);
        arm.addProperty("caseSelector", writerSelector);
        arm.addProperty("occurrenceId", owner);
        arm.add("pathCondition", new JsonArray());
        JsonArray arms = new JsonArray();
        arms.add(arm);
        dependency.add("arms", arms);
        query.getAsJsonArray("consumerAnchorCaseDependencies")
                .add(dependency);

        JsonObject keyAction = new JsonObject();
        keyAction.addProperty("mode", "SYMBOLIC");
        keyAction.addProperty("symbolicDemand", "BOUNDED_STATE_FRONTIER");
        keyAction.addProperty("symbol", keyInput);
        keyAction.addProperty("javaType", "int");
        keyAction.addProperty("observed", true);
        keyAction.addProperty("primitiveValue", "1");
        JsonArray actions = new JsonArray();
        actions.add(mapAction);
        actions.add(keyAction);
        JsonObject activation = new JsonObject();
        activation.add("inputActions", actions);
        JsonArray linkedActions = new JsonArray();
        linkedActions.add(mapAction.deepCopy());
        JsonObject linkedActivation = new JsonObject();
        linkedActivation.add("inputActions", linkedActions);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(query,
                        Arrays.asList(activation, linkedActivation), activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        JsonObject projected = null;
        for (int index = 0; index < result.modelAssignments.size(); index++) {
            JsonObject assignment = result.modelAssignments.get(index)
                    .getAsJsonObject();
            if (assignment.has("containerTarget")) projected = assignment;
        }
        assertTrue(result.modelAssignments.toString(), projected != null);
        assertEquals(mapInput, projected.get("inputSymbol").getAsString());
        assertEquals("NULL", projected.get("valueType").getAsString());
        JsonObject target = projected.getAsJsonObject("containerTarget");
        assertEquals("ACCESS_ORDINAL",
                target.get("selectorKind").getAsString());
        assertEquals(1, target.get("accessOrdinal").getAsInt());
    }

    private static JsonObject query(BranchWitness source) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("map-query"));
        query.addProperty("regionId", "REGION.map");
        query.addProperty("sourceActivationOccurrenceId",
                "test/node#epoch0/region/REGION.map#1#a1");
        query.add("replayContract",
                BranchReplayContract.atSource(source).toJson());
        JsonObject context = new JsonObject();
        context.addProperty("schemaVersion", SolverPathContext.SCHEMA_VERSION);
        context.addProperty("kind", SolverPathContext.KIND);
        context.addProperty("authority", SolverPathContext.AUTHORITY);
        context.add("constraints", new JsonArray());
        query.add("solverPathContext", context);
        query.add("consumerAnchorCaseDependencies", new JsonArray());
        return query;
    }

    private static JsonObject symbol(String raw) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "J");
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject constant(long value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "J");
        result.addProperty("_exp", "Y_J_" + value);
        return result;
    }

    private static JsonObject nullReference() {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "");
        result.addProperty("_exp", "N");
        return result;
    }

    private static JsonObject binary(JsonObject left, String operator,
                                     JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
