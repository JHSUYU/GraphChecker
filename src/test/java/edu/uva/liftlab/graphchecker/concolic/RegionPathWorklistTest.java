package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RegionPathWorklistTest {

                                @Test
    public void targetWorklistFlipsOnlyLocalPrefixBeforeExactFatal() {
        String id = "ACT.TARGET.LOCAL.PREFIX";
        JsonObject summary = summary(id,
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        JsonObject task = executionTask(id,
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        String sourceId = "TARGET.LOCAL";
        String sourceField = "<example.Target: int localValue>";
        String sourcePhaseId = sourcePhaseId(
                task.get("occurrenceId").getAsString(), sourceId);
        String localRaw = "M_I_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                sourcePhaseId, sourceId)
                + "_example/Target";
        String remoteRaw = "M_I_field_REMOTE.RPC.VALUE_example/Reply";

        JsonArray conditions = new JsonArray();
        conditions.add(binarySymbol(remoteRaw, ">", 0));
        conditions.add(binarySymbol(localRaw, ">", 0));
        conditions.add(binarySymbol(remoteRaw, "<", 10));
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        JsonObject remotePrefix = mapping("SITE.REMOTE", 0);
        remotePrefix.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(remotePrefix);
        JsonObject localPrefix = mapping("SITE.LOCAL", 1);
        localPrefix.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(localPrefix);
        JsonObject fatal = mapping("SITE.FATAL", 2);
        fatal.addProperty("policy", "EXPLORE");
        mappings.add(fatal);
        summary.add("branchMappings", mappings);
        authorizeVmPcMappings(summary);
        JsonObject reach = new JsonObject();
        reach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        reach.addProperty("siteId", "SITE.FATAL");
        reach.addProperty("occurrence", 1);
        reach.addProperty("outcome", true);
        summary.add(PathObservation.TargetReachEvent.FIELD, reach);

        JsonArray branches = new JsonArray();
        branches.add(taskBranch("SITE.REMOTE", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.LOCAL", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.FATAL", "EXPLORE"));
        task.add("branches", branches);
        JsonObject target = new JsonObject();
        target.addProperty("siteId", "SITE.FATAL");
        target.addProperty("occurrence", 1);
        task.add("targetBranch", target);
        JsonArray actions = new JsonArray();
        JsonObject localAction = new JsonObject();
        localAction.addProperty("symbol", "REGION.3.in.local");
        localAction.addProperty("portId", "REGION.3.in.local");
        localAction.addProperty("mode", "CONCRETE");
        localAction.addProperty("location", "HEAP_OBJECT_FIELD");
        localAction.addProperty("bindingMode", "FIELD_ACCESS");
        localAction.addProperty("accessFieldSignature", sourceField);
        localAction.addProperty("javaType", "int");
        actions.add(localAction);
        JsonObject remoteAction = new JsonObject();
        remoteAction.addProperty("symbol", "REGION.3.in.rpc");
        remoteAction.addProperty("portId", "REGION.3.in.rpc");
        remoteAction.addProperty("mode", "CONCRETE");
        remoteAction.addProperty("location", "CALL_RETURN");
        remoteAction.addProperty("bindingMode", "LOCAL_DEFINITION");
        remoteAction.addProperty("javaType", "int");
        remoteAction.addProperty("symbolicDemand",
                "EXACT_INCOMING_COMPOSITION");
        remoteAction.addProperty("selectedIncomingEdgeId", "EDGE.remote");
        actions.add(remoteAction);
        task.add("inputActions", actions);
        addMintSite(task, task.get("occurrenceId").getAsString(), sourceId,
                sourceField, 1);
        JsonObject handoff = new JsonObject();
        handoff.addProperty("role", "ATTACH");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("portId", "REGION.3.in.rpc");
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        task.add("communicationHandoffs", handoffs);
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.remote");
        edge.addProperty("toInputPort", "REGION.3.in.rpc");
        JsonArray bindings = new JsonArray();
        bindings.add(edge);
        task.add("edgeBindings", bindings.deepCopy());
        summary.add("edgeBindings", bindings.deepCopy());
        VmHandoffEvidence.writeTo(summary, Collections.singletonList(
                VmHandoffEvidence.event("REGION.3.in.rpc", 41L, 42L,
                        intSymbol(remoteRaw), "TASK.PRODUCER",
                        "REGION.PRODUCER/occurrence-1")));

        RegionPathWorklist.Result result = worklist(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject query = result.tasks.get(0);
        BranchReplayContract replay = replayContract(query);
        assertEquals("SITE.LOCAL", replay.source().siteId());
        assertEquals(2, replay.requiredPathPredicates().size());
        assertTrue(CanonicalJson.render(replay.requiredPathPredicates())
                .contains(remoteRaw));
        assertFalse(CanonicalJson.render(replay.requiredPathPredicates())
                .contains("Y_I_10"));
        assertEquals(1, VmHandoffEvidence.eventsOf(query).size());
        assertEquals(1, query.getAsJsonArray("edgeBindings").size());

        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL.target.local");
        assignment.addProperty("engineSymbol", localRaw);
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:"
                + sourcePhaseId);
        assignment.addProperty("configuredSourceId", sourceId);
        assignment.addProperty("configuredSourcePhaseId", sourcePhaseId);
        assignment.addProperty("configuredSourceFieldSignature",
                sourceField);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "1");
        JsonArray assignments = new JsonArray();
        assignments.add(assignment);
        JsonObject replayTask = PathReplayTaskFactory.create(query, task,
                assignments, replay, null);
        assertEquals(1, replayTask.getAsJsonArray(
                "communicationHandoffs").size());
        assertEquals(1, replayTask.getAsJsonArray("edgeBindings").size());
        assertEquals(1, replayTask.getAsJsonArray("modelAssignments").size());
        assertEquals(2, replayContract(replayTask)
                .requiredPathPredicates().size());

        JsonObject opposite = summary.deepCopy();
        opposite.addProperty("summaryId",
                "SUMMARY.ACT.TARGET.LOCAL.PREFIX.OPPOSITE");
        opposite.getAsJsonArray("pathCondition").set(1,
                binarySymbol(localRaw, "<=", 0));
        JsonArray oppositeMappings = new JsonArray();
        JsonObject oppositeRemote = mapping("SITE.REMOTE", 0);
        oppositeRemote.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeRemote);
        JsonObject oppositeLocal = mapping("SITE.LOCAL", 1);
        oppositeLocal.addProperty("outcome", false);
        oppositeLocal.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeLocal);
        JsonObject oppositeFatal = mapping("SITE.FATAL", 2);
        oppositeFatal.addProperty("policy", "EXPLORE");
        oppositeMappings.add(oppositeFatal);
        opposite.add("branchMappings", oppositeMappings);
        authorizeVmPcMappings(opposite);

        RegionPathWorklist.Result bothOutcomes = worklist(
                Arrays.asList(summary, opposite),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertTrue(bothOutcomes.tasks.toString(),
                bothOutcomes.tasks.isEmpty());
    }

        /**
     * OCC-1: a task's address may be entered several times, and every
     * compatible activation is published as its own occurrence instead of one
     * being answered and the rest reported as an ambiguous address (which is
     * what HDFS-11741 run 24 did for four of six tasks).
     *
     * <p>The activations are cases of ONE relation, closed on the planned
     * address, and they are not alternatives: each carries its own occurrence
     * so the composer can give it its own selector, ports and event scope.
     * They are also one obligation -- a second activation of the same address
     * ran the same code path again and buys no new exploration.</p>
     */
    @Test
    public void severalActivationsAreOneRelationOfSeveralOccurrences() {
        String planned = "REGION.3/occurrence-1";
        JsonObject first = activation(planned, 1, true, "Y_I_7");
        JsonObject second = first.deepCopy();
        second.addProperty("summaryId", "SUMMARY.ACT.OCC.A2");
        second.addProperty("occurrenceId", planned + "#a2");
        second.addProperty("activationOrdinal", 2);
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = worklist(
                Arrays.asList(first, second), Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));
        // The same task with only its first activation: the obligations the
        // planner proposes must not grow because the address was entered a
        // second time.
        RegionPathWorklist.Result alone = worklist(
                Collections.singletonList(first),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));

        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
        assertEquals("a task with several occurrence cases is still one "
                        + "obligation",
                alone.tasks.size(), result.tasks.size());
        assertEquals("the planned address, not one activation of it",
                planned, result.manifest.get("occurrenceId").getAsString());
        assertEquals("two activations are one relation",
                1, result.relations.size());

        JsonObject relation = result.relations.get(0);
        assertEquals(planned, relation.get("occurrenceId").getAsString());
        JsonArray cases = relation.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        assertEquals("one case per activation", 2, cases.size());
        Set<String> occurrences = new LinkedHashSet<>();
        for (int index = 0; index < cases.size(); index++) {
            JsonObject item = cases.get(index).getAsJsonObject();
            occurrences.add(item.get("occurrenceId").getAsString());
            assertTrue("every case names its activation",
                    item.has("activationOrdinal"));
        }
        assertEquals("each case is its own occurrence",
                new LinkedHashSet<>(Arrays.asList(planned + "#a1",
                        planned + "#a2")), occurrences);
    }

    /** Distinct paths of one address each plan once; a duplicate plans none. */
    @Test
    public void distinctActivationPathsEachOwnTheirFlipObligations() {
        String planned = "REGION.3/occurrence-1";
        JsonObject first = activation(planned, 1, true, "Y_I_7");
        JsonObject second = activation(planned, 2, true, "Y_I_9");
        second.getAsJsonArray("pathCondition").set(0, binary(">=", 0));
        JsonArray secondMappings = new JsonArray();
        secondMappings.add(mapping("SITE.0", 0));
        secondMappings.add(mapping("SITE.1", 1));
        second.add("branchMappings", secondMappings);
        authorizeVmPcMappings(second);
        JsonObject duplicate = second.deepCopy();
        duplicate.addProperty("summaryId", "SUMMARY.ACT.OCC.A3");
        duplicate.addProperty("occurrenceId", planned + "#a3");
        duplicate.addProperty("activationOrdinal", 3);
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        RegionPathWorklist.Bounds bounds =
                new RegionPathWorklist.Bounds(64, 32, 256);

        RegionPathWorklist.Result firstOnly = worklist(
                Collections.singletonList(first),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), bounds);
        RegionPathWorklist.Result secondOnly = worklist(
                Collections.singletonList(second),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), bounds);
        RegionPathWorklist.Result combined = worklist(
                Arrays.asList(first, second, duplicate),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), bounds);
        RegionPathWorklist.Result distinct = worklist(
                Arrays.asList(first, second),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), bounds);

        assertTrue(firstOnly.tasks.size() > 0);
        assertTrue(secondOnly.tasks.size() > 0);
        assertTrue("a second semantic path contributes obligations",
                distinct.tasks.size() > Math.max(firstOnly.tasks.size(),
                        secondOnly.tasks.size()));
        assertEquals("a duplicate activation path is deduplicated",
                distinct.tasks.size(), combined.tasks.size());
    }

    /**
     * An activation that satisfied only part of its output boundary becomes a
     * case of exactly what it captured, marked and named -- never dropped --
     * as long as another activation of the task did satisfy it.
     */
    @Test
    public void aPartialActivationIsAMarkedCaseNotADiscardedRelation() {
        String planned = "REGION.3/occurrence-1";
        JsonObject complete = activation(planned, 1, true, "Y_I_7");
        JsonObject partial = activation(planned, 2, false, "Y_I_9");
        partial.add("outputExpressions", new JsonObject());
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = worklist(
                Arrays.asList(complete, partial),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));

        assertEquals("one partial activation does not gap the relation",
                RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
        assertTrue("and it is named",
                result.manifest.getAsJsonArray("coverageGaps").toString()
                        .contains("ACTIVATION_BOUNDARY_NOT_COMPLETE"));
        assertEquals(1, result.relations.size());
        JsonArray cases = result.relations.get(0)
                .getAsJsonObject("regionRelation").getAsJsonArray("cases");
        assertEquals("the partial activation is still a case",
                2, cases.size());
        boolean marked = false;
        for (int index = 0; index < cases.size(); index++) {
            JsonObject item = cases.get(index).getAsJsonObject();
            if (!item.get("relationallyComplete").getAsBoolean()) {
                marked = true;
                assertEquals("it carries only what it captured",
                        0, item.getAsJsonObject("outputExpressions").size());
            }
        }
        assertTrue("the partial case is marked", marked);
    }

        /** One published activation of a task's planned address. */
    private static JsonObject activation(String planned, int ordinal,
                                         boolean complete, String value) {
        JsonObject summary = summary("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        summary.addProperty("summaryId", "SUMMARY.ACT.OCC.A" + ordinal);
        summary.addProperty("occurrenceId", planned + "#a" + ordinal);
        summary.addProperty("plannedOccurrenceId", planned);
        summary.addProperty("activationOrdinal", ordinal);
        summary.addProperty("relationallyComplete", complete);
        JsonObject outputs = new JsonObject();
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", "I");
        constant.addProperty("_exp", value);
        outputs.add("REGION.3.out.0", constant);
        summary.add("outputExpressions", outputs);
        return summary;
    }

                    private static JsonObject outputClosure(
            String port, String cell, String proofTag, String... sites) {
        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", "RELATION.REGION.3");
        producer.addProperty("regionId", "REGION.3");

        JsonObject output = new JsonObject();
        output.addProperty("portId", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "REGION_OUTPUT");
        output.addProperty("javaTypeDescriptor", "I");
        output.addProperty("selectionAuthority", "TEST_EXACT_DEMAND");

        JsonArray siteArray = new JsonArray();
        for (String site : sites) siteArray.add(site);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", siteArray.deepCopy());
        slice.add("staticSites", siteArray.deepCopy());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("proofTag", proofTag);

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static void attachClosure(JsonObject artifact,
                                      JsonObject closure) {
        artifact.remove("requestedOutput");
        artifact.addProperty("relationKey", closure.getAsJsonObject(
                "producer").get("relationKey").getAsString());
        artifact.add("outputClosure", closure.deepCopy());
    }

    private static JsonObject executionTask(String id,
                                            ClosureGoalKind goal) {
        JsonObject task = new JsonObject();
        task.addProperty("goalId", id + ".GOAL");
        task.addProperty("taskId", "TASK." + id);
        task.addProperty("regionId", "REGION.3");
        task.addProperty("sourceKey", "NAMENODE/active/epoch-0");
        task.addProperty("occurrenceId", "REGION.3/occurrence-1");
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        goal.writeToTask(task);
        attachClosure(task, outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.DEFAULT", "SITE.0", "SITE.1"));
        return task;
    }

    private static JsonObject summary(String id,
                                      ClosureGoalKind goal) {
        String plannedOccurrence = "REGION.3/occurrence-1";
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + id);
        summary.addProperty("goalId", id + ".GOAL");
        summary.addProperty("taskId", "TASK." + id);
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("sourceKey", "NAMENODE/active/epoch-0");
        summary.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                plannedOccurrence);
        summary.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        summary.addProperty("occurrenceId", plannedOccurrence + "#a1");
        LoopBoundPolicy.cfgBackedges(8).writeTo(summary);
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        // C2: the census is required, never optional - a summary that
        // never stated it is refused, so every fixture states it.
        summary.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        goal.writeToTask(summary);
        attachClosure(summary, outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.DEFAULT", "SITE.0", "SITE.1"));

        JsonArray conditions = new JsonArray();
        conditions.add(binary(">", 0));
        conditions.add(binary("<", 5));
        summary.add("pathCondition", conditions);

        JsonArray mappings = new JsonArray();
        mappings.add(mapping("SITE.0", 0));
        mappings.add(mapping("SITE.1", 1));
        summary.add("branchMappings", mappings);
        JsonObject outputs = new JsonObject();
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_java_type", "I");
        value.addProperty("_exp", "Y_I_0");
        outputs.add("REGION.3.out.0", value);
        summary.add("outputExpressions", outputs);
        authorizeVmPcMappings(summary);
        return summary;
    }

    private static void authorizeVmPcMappings(JsonObject summary) {
        JsonArray conditions = summary.getAsJsonArray("pathCondition");
        JsonArray canonical = new JsonArray();
        for (com.google.gson.JsonElement element
                : summary.getAsJsonArray("branchMappings")) {
            JsonObject mapping = element.getAsJsonObject();
            int conditionIndex = mapping.get("conditionIndex").getAsInt();
            SummaryBranchMapping.Policy policy =
                    SummaryBranchMapping.Policy.fromWire(
                            mapping.has("policy")
                                    ? mapping.get("policy").getAsString()
                                    : "EXPLORE");
            if (conditionIndex < 0 || conditionIndex >= conditions.size()) {
                canonical.add(SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                mapping.get("siteId").getAsString(),
                                "<test.Region: void run()>", 0,
                                mapping.get("occurrence").getAsInt(),
                                mapping.get("outcome").getAsBoolean()),
                        policy).toJson());
                continue;
            }
            JsonObject event = new JsonObject();
            event.addProperty("eventId", conditionIndex + 1L);
            event.addProperty("contextId", 7L);
            event.addProperty("predicateNormalization", "IDENTITY");
            BranchWitness witness = BranchWitness.vmPc(
                    mapping.get("siteId").getAsString(),
                    "<test.Region: void run()>", conditionIndex,
                    mapping.get("occurrence").getAsInt(),
                    mapping.get("outcome").getAsBoolean(),
                    conditions.get(conditionIndex), conditionIndex, event);
            canonical.add(SummaryBranchMapping.witnessed(witness,
                    conditionIndex, policy).toJson());
        }
        summary.add("branchMappings", canonical);
    }

    private static JsonObject taskBranch(String site, String policy) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", site);
        branch.addProperty("policy", policy);
        branch.addProperty("selectedOccurrence", 1);
        return branch;
    }


    private static String sourcePhaseId(
            String occurrence, String sourceId) {
        return ConfiguredSourcePhaseContract.phaseId(occurrence,
                "<fixture.Source." + sourceId + ": void publish()>#u0",
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    /** The task's frozen catalog of declared mint SITES -- what a recorded
     * VM source root is resolved against now that nothing predicts it. */
    private static void addMintSite(JsonObject task, String occurrence,
                                    String sourceId, String field,
                                    int ordinal) {
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                sourceId, field,
                "<fixture.Source." + sourceId + ": void publish()>", 0));
        JsonObject row = ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0),
                occurrence, 1, ordinal, 10L, 100L + ordinal,
                "<example.Hook: boolean symbolize(java.lang.String,"
                        + "java.lang.Object,java.lang.String)>",
                Collections.singletonList(10L));
        JsonArray phases = task.has(
                ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? task.getAsJsonArray(
                        ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        phases.add(row);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        return BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract"));
    }

    private static JsonObject mapping(String site, int condition) {
        return mapping(site, condition, 1);
    }

    private static JsonObject mapping(String site, int condition,
                                      int occurrence) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("conditionIndex", condition);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", true);
        return mapping;
    }

    private static JsonObject binary(String operator, int constant) {
        return binarySymbol(
                "M_I_field_REGION.3.in.0_java/lang/Integer",
                operator, constant);
    }

    private static JsonObject binarySymbol(
            String raw, String operator, int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = intSymbol(raw);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }

    private static JsonObject intSymbol(String raw) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", raw);
        return symbol;
    }

                private static RegionPathWorklist.Result worklist(
            List<JsonObject> summaries, List<JsonObject> executionTasks,
            List<JsonObject> explorationRecords,
            RegionPathWorklist.Bounds bounds) {
        return RegionPathWorklist.plan(summaries, executionTasks,
                explorationRecords, bounds,
                Collections.<JsonObject>emptyList());
    }
}
