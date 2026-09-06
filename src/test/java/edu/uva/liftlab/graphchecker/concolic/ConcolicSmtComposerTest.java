package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import org.junit.Assume;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSmtComposerTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();








    @Test
    public void repeatedMapUpdatesConsumeThePreviousSemanticOccurrence()
            throws Exception {
        String target = "TEST_DRIVER/test#epoch0/region/REGION.0#target";
        String planned = "TEST_DRIVER/test#epoch0/region/REGION.1#1";
        String output = "REGION.1.out.0";
        JsonObject edge = binding("EDGE.MAP.TIMELINE", planned, output,
                target, "REGION.0.in.0", 1, 2);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_INITIAL_BOUNDARY);

        JsonObject a1State = assocPut(assocStateSymbol(
                "M_L'java/util/HashMap'_59"), 1, 101);
        JsonObject row = summary("MAP.TIMELINE", planned, a1State,
                Collections.<String>emptyList(),
                Collections.singletonList(edge), "java.util.Map").toJson();
        JsonArray encoded = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject a1 = encoded.get(0).getAsJsonObject();
        decorateMapOccurrence(a1, planned, 1, a1State);

        JsonObject a2State = assocPut(a1State, 2, 102);
        JsonObject a2 = a1.deepCopy();
        a2.getAsJsonObject("outputExpressions").add(output, a2State);
        decorateMapOccurrence(a2, planned, 2, a2State);

        JsonObject a3State = assocPut(a2State, 3, 103);
        JsonObject a3 = a1.deepCopy();
        a3.getAsJsonObject("outputExpressions").add(output, a3State);
        decorateMapOccurrence(a3, planned, 3, a3State);

        // Deliberately not activation order: the composer must use the
        // authoritative ordinal, not merge-array position.
        encoded.remove(0);
        encoded.add(a2);
        encoded.add(a1);
        encoded.add(a3);

        JsonArray constraints = new JsonArray();
        constraints.add(binary(mapGet(assocStateSymbol(
                "REGION.0.in.0"), 99), "==", nullRef()));
        ConcolicSmtComposer.Result result = compose(target,
                Collections.singletonList(RelationSummary.decode(row)),
                Arrays.asList(region("REGION.0", "java.util.Map", ""),
                        region("REGION.1", "", "java.util.Map")),
                constraints, edge);

        JsonArray predecessors = result.manifest
                .getAsJsonArray("occurrenceMapPredecessors");
        assertEquals(result.manifest.toString(), 2, predecessors.size());
        String a1Port = predecessors.get(0).getAsJsonObject()
                .get("fromPortTerm").getAsString();
        String a2Port = predecessors.get(1).getAsJsonObject()
                .get("fromPortTerm").getAsString();
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assoc_put " + a1Port + " "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assoc_put " + a2Port + " "));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("OccurrenceMap"));
    }

        @Test
    public void transportedObjectFieldKeepsItsConfiguredSourceValue()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#transported-field-target";
        String producerOccurrence = "REGION.1@Test#transported-field-source";
        String targetPort = "REGION.0.in.0";
        String sourceId = "TEST.NAMENODE.KEY_EXPIRY";
        String sourcePhase = publishPhase(producerOccurrence);
        String expiryRaw = configuredRaw(sourcePhase, sourceId, "expiry");
        JsonObject producerOwner = reference(
                "M_L_example_State_transport_owner", "Lexample/State;");
        JsonObject producerField = fieldAccess(producerOwner,
                "example/State", 24, "J");

        JsonObject rpc = protocolBinding("EDGE.TRANSPORTED.FIELD",
                producerOccurrence, "REGION.1.out.0", targetOccurrence,
                targetPort);
        RelationSummary producer = summary("TRANSPORTED_FIELD_SOURCE",
                producerOccurrence, producerOwner,
                Collections.<String>emptyList(),
                Collections.singletonList(rpc), "example.State");
        JsonObject producerRow = producer.toJson();
        JsonObject producerCase = producerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, producerOccurrence,
                        "<TestNameNode: long keyExpiry>",
                        reference(expiryRaw, "J"), 1, false, null)));
        producer = withProducerGuardAndInteraction(
                RelationSummary.decode(producerRow),
                binary(producerField, "==", reference(expiryRaw, "J")),
                targetPort, 41L);

        JsonObject targetOwner = reference(
                "M_L_field_" + targetPort + "_example/State",
                "Lexample/State;");
        JsonArray constraints = new JsonArray();
        constraints.add(binary(fieldAccess(targetOwner, "example/State", 24,
                "J"), "<", integer(100)));
        JsonObject fatal = fatalQuery(targetOccurrence, constraints, rpc);
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        markRequiredTargetPath(targetPath);
        VmHandoffEvidence.writeTo(targetPath,
                Collections.singletonList(VmHandoffEvidence.event(
                        targetPort, 41L, 42L, producerOwner,
                        "TASK.TRANSPORTED_FIELD_SOURCE",
                        producerOccurrence)));
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.0"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        targetPath.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        events, order),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));

        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", "example.State", ""),
                        region("REGION.1", "", "example.State")),
                fatal, Collections.singletonList(rpc));

        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        String expiryTerm = roots.get(0).getAsJsonObject()
                .get("solverTerm").getAsString();
        assertEquals(result.smtLib, ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
            assertEquals(result.smtLib, "unsat", z3(assuming(result.smtLib,
                    "(>= " + expiryTerm + " 100)")));
        }
    }

    @Test
    public void fieldDeclaredLongOutputUsesVLongWithoutFlatJavaType()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#long-field-target";
        String producerOccurrence = "REGION.1@Test#long-field-source";
        JsonObject edge = binding("EDGE.LONG.FIELD", producerOccurrence,
                "REGION.1.out.0", targetOccurrence, "REGION.0.in.0", 20,
                30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_INITIAL_BOUNDARY);

        long expiry = 1_788_748_288_832L;
        RelationSummary producer = summary("LONG_FIELD_SOURCE",
                producerOccurrence, longInteger(expiry),
                Collections.<String>emptyList(),
                Collections.singletonList(edge), "long");

        JsonObject producerRegion = region("REGION.1", "", "long");
        JsonObject output = producerRegion.getAsJsonArray("outputs").get(0)
                .getAsJsonObject();
        output.remove("javaType");
        output.addProperty("cell", "<ExampleKey: void write(long)>#u7"
                + ".fieldReceiver");
        JsonArray declarations = new JsonArray();
        declarations.add("<ExampleKey: long expiryDate>");
        output.add("fieldPathDeclarations", declarations);

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference("REGION.0.in.0", "J"), "==",
                longInteger(expiry)));
        ConcolicSmtComposer.Result result = compose(targetOccurrence,
                Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", "long", ""),
                        producerRegion), constraints, edge);

        String producerPort = "port__REGION_1_out_0__instance__"
                + "REGION_1_Test_long_field_source";
        assertTrue(result.smtLib, result.smtLib.contains(
                "(= " + producerPort + " (VLong " + expiry + "))"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= " + producerPort + " (VInt " + expiry + "))"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
        }
    }

    @Test
    public void twoRpcProducersAndMultipleTargetSourcesShareOneFatalFormula()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#nested-target";
        String producerAOccurrence = "REGION.1@Test#producer-A";
        String producerBOccurrence = "REGION.1@Test#producer-B";
        String portA = "REGION.0.in.0";
        String portB = "REGION.0.in.1";

        String sourceA = "TEST.RPC.PRODUCER.A";
        String sourceB = "TEST.RPC.PRODUCER.B";
        String sourceGate = "TEST.TARGET.GATE";
        String sourceOffset = "TEST.TARGET.OFFSET";
        String phaseA = publishPhase(producerAOccurrence);
        String phaseB = publishPhase(producerBOccurrence);
        String phaseGate = publishPhase(targetOccurrence) + ".GATE";
        String phaseOffset = publishPhase(targetOccurrence) + ".OFFSET";
        String rawA = configuredRaw(phaseA, sourceA, "a");
        String rawB = configuredRaw(phaseB, sourceB, "b");
        String rawGate = configuredRaw(phaseGate, sourceGate, "gate");
        String rawOffset = configuredRaw(phaseOffset, sourceOffset,
                "offset");

        RelationSummary producerA = summary("NESTED_PRODUCER_A",
                producerAOccurrence, reference(rawA, "I"),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        RelationSummary producerB = summary("NESTED_PRODUCER_B",
                producerBOccurrence, reference(rawB, "I"),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject producerARow = producerA.toJson();
        JsonObject producerACase = producerARow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerACase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        phaseA, sourceA, producerAOccurrence,
                        "<TestDataNode: int valueA>",
                        reference(rawA, "I"), 1, false, null)));
        producerA = withProducerGuardAndInteraction(
                RelationSummary.decode(producerARow),
                binary(reference(rawA, "I"), ">=", integer(0)), portA, 141L);

        JsonObject producerBRow = producerB.toJson();
        JsonObject producerBCase = producerBRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerBCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        phaseB, sourceB, producerBOccurrence,
                        "<TestDataNode: int valueB>",
                        reference(rawB, "I"), 1, false, null)));
        producerB = withProducerGuardAndInteraction(
                RelationSummary.decode(producerBRow),
                binary(reference(rawB, "I"), ">=", integer(0)), portB, 151L);

        // This is the nested target shape: the first two conditions are
        // NameNode-local prefix gates, while the final fatal predicate uses
        // both values attached from independent DataNode RPC producers.
        JsonArray targetConstraints = new JsonArray();
        targetConstraints.add(binary(reference(rawGate, "I"), ">",
                integer(0)));
        targetConstraints.add(binary(reference(rawOffset, "I"), ">=",
                integer(0)));
        targetConstraints.add(binary(
                binary(reference(portA, "I"), "+",
                        reference(rawGate, "I")),
                ">",
                binary(reference(portB, "I"), "+",
                        reference(rawOffset, "I"))));
        JsonObject fatal = fatalQuery(targetOccurrence, targetConstraints);
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        markRequiredTargetPath(targetPath);
        // TargetReachPathQueryBuilder retains target-local declarations on
        // the fatal query root: they apply to every retained nested path for
        // this exact target occurrence, while handoffs remain path-local.
        SymbolicSourceEvidence.writeTo(fatal, Arrays.asList(
                SymbolicSourceEvidence.event(phaseGate, sourceGate,
                        targetOccurrence, "<TestNameNode: int gate>",
                        reference(rawGate, "I"), 1, false, null),
                SymbolicSourceEvidence.event(phaseOffset, sourceOffset,
                        targetOccurrence, "<TestNameNode: int offset>",
                        reference(rawOffset, "I"), 1, false, null)));
        VmHandoffEvidence.writeTo(targetPath, Arrays.asList(
                VmHandoffEvidence.event(portA, 141L, 142L,
                        reference(rawA, "I"), "TASK.NESTED_PRODUCER_A",
                        producerAOccurrence),
                VmHandoffEvidence.event(portB, 151L, 152L,
                        reference(rawB, "I"), "TASK.NESTED_PRODUCER_B",
                        producerBOccurrence)));

        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(141L,
                "HANDOFF_EXPORT", 201L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(142L,
                "HANDOFF_ATTACH", 202L, "REGION.0"));
        events.add(RecordedSharedStateFixtures.event(151L,
                "HANDOFF_EXPORT", 203L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(152L,
                "HANDOFF_ATTACH", 204L, "REGION.0"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(141L, 142L,
                "VALUE_HANDOFF"));
        order.add(RecordedSharedStateFixtures.edge(151L, 152L,
                "VALUE_HANDOFF"));
        targetPath.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        events, order),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));

        JsonObject targetRegion = region("REGION.0", true, false);
        targetRegion.getAsJsonArray("symbolicInputs")
                .add(port(portB, true, "int"));
        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Arrays.asList(producerA, producerB),
                Arrays.asList(targetRegion,
                        region("REGION.1", false, true)), fatal, null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 4, roots.size());
        String termA = "";
        String termB = "";
        String termGate = "";
        String termOffset = "";
        for (JsonElement element : roots) {
            JsonObject root = element.getAsJsonObject();
            String sourceId = root.get("sourceId").getAsString();
            String solverTerm = root.get("solverTerm").getAsString();
            if (sourceA.equals(sourceId)) termA = solverTerm;
            if (sourceB.equals(sourceId)) termB = solverTerm;
            if (sourceGate.equals(sourceId)) termGate = solverTerm;
            if (sourceOffset.equals(sourceId)) termOffset = solverTerm;
        }
        assertFalse(roots.toString(), termA.isEmpty());
        assertFalse(roots.toString(), termB.isEmpty());
        assertFalse(roots.toString(), termGate.isEmpty());
        assertFalse(roots.toString(), termOffset.isEmpty());
        if (z3Available()) {
            JsonObject reach = BooleanReachConditionExtractor.extract(
                    result.smtLib, result.manifest,
                    Arrays.asList(targetRegion,
                            region("REGION.1", false, true)),
                    new BooleanReachConditionExtractor.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);
            JsonArray models = reach.getAsJsonArray(
                    BooleanReachConditionExtractor
                            .SYMBOLIC_VARIABLE_MODELS);
            assertEquals(models.toString(), 1, models.size());
            JsonArray reported = models.get(0).getAsJsonObject()
                    .getAsJsonArray("variables");
            assertEquals(reported.toString(), 4, reported.size());
            Set<String> reportedSources = new LinkedHashSet<>();
            for (JsonElement element : reported) {
                JsonObject variable = element.getAsJsonObject();
                assertEquals("TEST_DRIVER/test#epoch0",
                        variable.get("sourceKey").getAsString());
                assertTrue(variable.toString(), variable.has("value"));
                reportedSources.add(
                        variable.get("sourceId").getAsString());
            }
            assertEquals(new LinkedHashSet<>(Arrays.asList(
                    sourceA, sourceB, sourceGate, sourceOffset)),
                    reportedSources);
            assertEquals(result.smtLib, "sat", z3(assuming(result.smtLib,
                    "(= " + termA + " 8)",
                    "(= " + termB + " 3)",
                    "(= " + termGate + " 1)",
                    "(= " + termOffset + " 0)")));
            // If either RPC handoff were merely correlated in a trace rather
            // than expression-connected, Z3 could choose unrelated target
            // port values and this deliberately false witness would be SAT.
            assertEquals(result.smtLib, "unsat", z3(assuming(result.smtLib,
                    "(= " + termA + " 1)",
                    "(= " + termB + " 8)",
                    "(= " + termGate + " 1)",
                    "(= " + termOffset + " 0)")));
        }
    }

    @Test
    public void onlyExactWireDeliveryLowersAsEquality() throws Exception {
        String target = "REGION.0@Test#wire-target";
        String producer = "REGION.1@Test#wire-producer";
        String port = "REGION.1.out.0";
        JsonObject wire = exactWireBinding("EDGE.WIRE", producer, port,
                target, port, "node/request/fetch#1", "7", "RESPONSE",
                40, 41);

        assertTrue(AutomaticRegionEdge.trustedWireEquality(wire));
        assertTrue(AutomaticRegionEdge
                .trustedRuntimeCompositionBinding(wire));

        JsonObject weak = wire.deepCopy();
        weak.addProperty("receiverEventSeq", 40);
        assertTrue(AutomaticRegionEdge.tracedExchangeCandidate(weak));
        assertFalse(AutomaticRegionEdge.trustedWireEquality(weak));
        assertFalse(AutomaticRegionEdge
                .trustedRuntimeCompositionBinding(weak));

        JsonObject targetRegion = region("REGION.0", true, false);
        targetRegion.getAsJsonArray("symbolicInputs").get(0)
                .getAsJsonObject().addProperty("portId", port);
        RelationSummary source = summary("WIRE", producer, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(wire));
        ConcolicSmtComposer.Result result = compose(target,
                Collections.singletonList(source),
                Arrays.asList(targetRegion,
                        region("REGION.1", false, true)), wire);

        assertEquals(result.manifest.toString(), 1,
                result.manifest.getAsJsonArray(
                        "resolvedEdgeBindings").size());
        assertTrue(result.smtLib, result.smtLib.contains(
                "edge_binding_REGION_1_to_REGION_0_0"));
    }

    @Test
    public void trustedTopologyReadFromSelectsASuppliedProducerOnly()
            throws Exception {
        for (String provenance : Arrays.asList(
                RecordedReadFrom.PROVENANCE_CANDIDATE,
                RecordedReadFrom.PROVENANCE_EXCLUDED)) {
            String fatalInstance = "REGION.0@Test#target";
            String consumerInstance = "REGION.1@Test#consumer";
            String producerInstance = "REGION.1@Test#producer";
            JsonObject firstHop = protocolBinding("EDGE.RPC",
                    consumerInstance, "REGION.1.out.0", fatalInstance,
                    "REGION.0.in.0");
            JsonObject upstream = binding("EDGE.UPSTREAM",
                    producerInstance, "REGION.1.out.0",
                    consumerInstance, "REGION.1.in.0", 1, 2);
            upstream.addProperty("fromRegion", "REGION.1");
            upstream.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                    provenance);
            RelationSummary consumer = summary("CONSUMER",
                    consumerInstance, 10,
                    Collections.singletonList("REGION.1.in.0"),
                    Arrays.asList(firstHop, upstream));
            RelationSummary producer = summary("PRODUCER",
                    producerInstance, 20,
                    Collections.<String>emptyList(),
                    Collections.<JsonObject>emptyList());

            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Arrays.asList(consumer, producer), firstHop);

            assertTrue(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "EDGE.UPSTREAM"));
            assertFalse("topology-only RF must not become a value equality\n"
                            + result.manifest,
                    result.manifest.getAsJsonArray("recordedValueBindings")
                            .toString().contains("EDGE.UPSTREAM"));
        }
    }

                /**
     * The four recorded read-from shapes, each solved by z3.
     *
     * <p>Each golden is a complete composition, and each row of its truth
     * table is a real solve of the emitted query with one extra assumption.
     * Reading the formula text would only prove that some string was written;
     * what has to hold is that the recorded model <em>decides</em> the target,
     * and only a solver can say that.</p>
     *
     * <table>
     *   <tr><td>exact</td><td>the proven writer's value, and no other</td></tr>
     *   <tr><td>guarded</td><td>each arm's own value; a false writer guard
     *   makes its arm infeasible</td></tr>
     *   <tr><td>unknown</td><td>a writer the order domain does not hold is
     *   not selectable, and the unknown arm constrains no value</td></tr>
     *   <tr><td>no candidate</td><td>the unknown arm is the only arm, and
     *   exactly-one forces it</td></tr>
     * </table>
     */
    @Test
    public void goldenRecordedModelsMatchTheirZ3TruthTables()
            throws Exception {
        Assume.assumeTrue(z3Available());

        // Exact: the session proved which write the read took, so the value
        // is an equality and there is no selector to choose.
        ConcolicSmtComposer.Result exact = exactGolden();
        assertEquals(exact.manifest.toString(), "CANDIDATE_READY",
                exact.manifest.get("state").getAsString());
        assertTrue(exact.smtLib, exact.smtLib.contains(
                ":named recorded_exact_order__11__21"));
        assertFalse(exact.smtLib, exact.smtLib.contains("rf_selector__"));
        // The port the recorded answer decided is bound once, by that answer.
        // The competing trace candidate is not composed beside it - which
        // would equate the two producers - and is not promoted into a
        // composition divergence merely because the trace retained it.
        assertFalse(exact.smtLib,
                exact.smtLib.contains("state_version_choice__"));
        assertFalse(exact.manifest.toString(), exact.manifest.toString()
                .contains("RECORDED_EVIDENCE_DECIDED_CONSUMER_PORT"));
        assertTrue(exact.manifest.toString(), exact.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals("sat", z3(exact.smtLib));
        assertEquals("unsat", z3(ready(exactGolden(11)).smtLib));

        // Guarded: one selector family decides value, guard and cut.
        ConcolicSmtComposer.Result guarded = guardedGolden(1, true, true);
        // The selector family is composed and solved over recorded writers.
        // The selected edge still advertises unknown-writer provenance, so
        // that edge remains a final-artifact refusal.
        assertEquals(guarded.manifest.toString(), "CANDIDATE_READY",
                guarded.manifest.get("state").getAsString());
        assertEquals(guarded.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                guarded.manifest.get(
                        ConcolicSmtComposer.FINAL_STATUS).getAsString());
        assertFalse(guarded.manifest.toString(), guarded.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals("sat", z3(guarded.smtLib));
        assertEquals("sat", z3(assuming(guarded.smtLib,
                "rf_selector__21__rf1")));
        // Changing the selected writer changes the target value formula: the
        // same target is unreachable through the other writer's expression.
        assertEquals("unsat", z3(assuming(guarded.smtLib,
                "rf_selector__21__rf2")));
        assertEquals("sat", z3(assuming(ready(guardedGolden(2, true, true))
                .smtLib, "rf_selector__21__rf2")));
        // The exported SAT query may not invent a writer for a value no
        // recorded writer produces.
        assertEquals("unsat", z3(assuming(ready(guardedGolden(99, true, true))
                .smtLib, "rf_selector__21__rf_unknown")));

        // A false guard makes the only recorded writer for value 2
        // infeasible; the unknown arm cannot rescue the witness.
        ConcolicSmtComposer.Result refuted = ready(
                guardedGolden(2, false, true));
        assertTrue(refuted.smtLib, refuted.smtLib.contains(
                ":named recorded_write_guard__21__rf2"));
        assertEquals("unsat", z3(assuming(refuted.smtLib,
                "rf_selector__21__rf2")));
        assertEquals("unsat", z3(refuted.smtLib));

        // Neither recorded write is in the order domain, and the existential
        // SAT query also excludes the unknown arm.
        ConcolicSmtComposer.Result unknown = ready(
                guardedGolden(1, true, false));
        assertTrue(unknown.smtLib, unknown.smtLib.contains(
                ":named recorded_write_absent__21__11"));
        assertEquals("unsat", z3(assuming(unknown.smtLib,
                "rf_selector__21__rf1")));
        assertEquals("unsat", z3(assuming(unknown.smtLib,
                "rf_selector__21__rf_unknown")));

        // No candidate: the location was watched and named no addressable
        // writer, so the only arm is the unknown one and it is forced.
        ConcolicSmtComposer.Result noCandidate = ready(noCandidateGolden());
        assertEquals("sat", z3(noCandidate.smtLib));
        assertEquals("unsat", z3(assuming(noCandidate.smtLib,
                "(not rf_selector__21__rf_unknown)")));


        // A partial recorded model can still be unsatisfiable, and the result
        // vocabulary must not read that as unreachability.  The same query
        // read as a closed model would say the opposite, which is exactly why
        // the closure facts have to travel with it.
        ConcolicSmtComposer.Result partial = ready(
                unsatisfiablePartialGolden());
        assertFalse(partial.manifest.toString(), partial.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertEquals("unsat", z3(partial.smtLib));
        JsonObject inconclusive = reachCondition(partial, partial.manifest);
        assertEquals("UNKNOWN",
                inconclusive.get("reachability").getAsString());
        assertEquals("INCONCLUSIVE_UNDERAPPROXIMATION",
                inconclusive.get("coverageConclusion").getAsString());
        JsonObject asClosed = partial.manifest.deepCopy();
        asClosed.addProperty("recordedModelComplete", true);
        JsonObject closedEvidence = new JsonObject();
        closedEvidence.addProperty("schemaVersion", 1);
        closedEvidence.addProperty("kind", "UNSAT_CLOSURE_EVIDENCE");
        closedEvidence.addProperty("authority",
                ConcolicSmtComposer.UNSAT_CLOSURE_AUTHORITY);
        closedEvidence.addProperty("recordedModelComplete", true);
        closedEvidence.addProperty("producerPathsClosed", true);
        closedEvidence.addProperty("targetPathsClosed", true);
        closedEvidence.addProperty("compositionCoverageClosed", true);
        closedEvidence.addProperty("finalStatusReady", true);
        closedEvidence.addProperty("targetCoverageGapCount", 0);
        closedEvidence.addProperty("compositionCoverageGapCount", 0);
        closedEvidence.add("partialProducerSummaryIds", new JsonArray());
        closedEvidence.addProperty(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE, true);
        asClosed.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE,
                true);
        asClosed.add(ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE,
                closedEvidence);
        asClosed.addProperty(ConcolicSmtComposer.FINAL_STATUS,
                ConcolicSmtComposer.FINAL_READY);
        assertEquals("UNREACHABLE", reachCondition(partial, asClosed)
                .get("reachability").getAsString());
    }

                    /** One unsatisfiable composition whose recorded model stays partial. */
    private ConcolicSmtComposer.Result unsatisfiablePartialGolden()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.PARTIAL", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        edge.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        RelationSummary producer = withRecordedSharedState(
                summary("PARTIAL", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(edge)));
        return composeTarget(fatalInstance, producer,
                binary(integer(0), "==", integer(1)), edge);
    }

    private static JsonObject reachCondition(
            ConcolicSmtComposer.Result result, JsonObject manifest)
            throws Exception {
        return BooleanReachConditionExtractor.extract(result.smtLib, manifest,
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1),
                8, 64).getAsJsonObject("reachCondition");
    }


    /**
     * The same result, once it is known to carry no composition gap.
     *
     * <p>A gapped query fails closed with a literal {@code false}, so every
     * row of a truth table read off one would be unsat for a reason that has
     * nothing to do with the recorded model. Pinning the state here is what
     * makes the unsat rows below evidence about read-from semantics.</p>
     */
    private static ConcolicSmtComposer.Result ready(
            ConcolicSmtComposer.Result result) {
        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.smtLib, result.smtLib.contains("(assert false)"));
        return result;
    }

    private ConcolicSmtComposer.Result exactGolden() throws Exception {
        return exactGolden(10);
    }

    private ConcolicSmtComposer.Result exactGolden(int value)
            throws Exception {
        return exactGolden(value, "CLOSED");
    }

    /**
     * One proven read-from, with the target asking for {@code value} and the
     * producer declaring {@code coverageState} about its own path set. A
     * {@code null} state is the relation that declared nothing.
     */
    private ConcolicSmtComposer.Result exactGolden(int value,
                                                   String coverageState)
            throws Exception {
        return exactGolden(value, coverageState, false);
    }

    private ConcolicSmtComposer.Result exactGolden(int value,
                                                   String coverageState,
                                                   boolean targetFrontier)
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject edge = binding("EDGE.EXACT", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        edge.addProperty("fieldVersionId", 11);
        edge.addProperty("readEventId", 21);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        // A second writer of the same consumer port that nothing decided.
        // The recorded answer names the first one, so this candidate must be
        // dropped rather than composed - as an alternative it would contradict
        // the proof, and beside it the port would be bound twice and the two
        // producers equated.
        JsonObject competing = binding("EDGE.COMPETING", outerInstance,
                "REGION.1.out.1", fatalInstance, "REGION.0.in.0", 20, 30);
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_EXACT, "UNIQUE_VERSION", 11L);
        // The selected edge and the VM version must name the same exact
        // producer occurrence; region/type similarity is not provenance.
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                        outerInstance);
        JsonObject read = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        read.addProperty("regionId", "REGION.0");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        RelationSummary producer = declaring(withRecorded(
                withCompetingOutput(summary("EXACT", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Arrays.asList(edge, competing))), envelope,
                RecordedSharedStateFixtures.twoWriterLedger()),
                coverageState);
        JsonObject producerRegion = region("REGION.1", true, true);
        producerRegion.getAsJsonArray("outputs").add(
                statePort("REGION.1.out.1", "int",
                        "<Test: int competing>"));
        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference("REGION.0.in.0", "I"), "==",
                integer(value)));
        JsonObject targetRegion = region("REGION.0", true, false);
        if (targetFrontier) {
            targetRegion.getAsJsonArray("symbolicInputs").get(0)
                    .getAsJsonObject().addProperty("dependencyRole",
                            DependencyRole.VALUE_FRONTIER);
        }
        return compose(fatalInstance, Collections.singletonList(producer),
                Arrays.asList(targetRegion, producerRegion), constraints, edge,
                competing);
    }

    /**
     * One undecided read of two competing writers.
     *
     * @param value        the value the target predicate asks the read for
     * @param satisfiable  whether the second writer's recorded path guard can
     *                     hold
     * @param orderedWrites whether the recorded ledger holds the two writes
     */
    private ConcolicSmtComposer.Result guardedGolden(
            int value, boolean satisfiable, boolean orderedWrites)
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonArray candidates = new JsonArray();
        candidates.add(RecordedSharedStateFixtures.candidate("rf1", 11L,
                RecordedSharedStateFixtures.constant(1), null, 21L, 12L));
        candidates.add(RecordedSharedStateFixtures.candidate("rf2", 12L,
                RecordedSharedStateFixtures.constant(2), satisfiable
                        ? RecordedSharedStateFixtures.guard("G")
                        : RecordedSharedStateFixtures.unsatisfiableGuard(),
                21L, 11L));
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));
        return guardedGolden(fatalInstance, outerInstance, candidates, value,
                orderedWrites);
    }

    /** A watched location whose writers none of the evidence can name. */
    private ConcolicSmtComposer.Result noCandidateGolden() throws Exception {
        JsonArray candidates = new JsonArray();
        candidates.add(RecordedSharedStateFixtures.unknownCandidate(21L,
                "M_I_unknownWriter_7_24_r21"));
        return guardedGolden("REGION.0@Test#call30", "REGION.1@Test#call20",
                candidates, 7, true);
    }

    private ConcolicSmtComposer.Result guardedGolden(
            String fatalInstance, String outerInstance, JsonArray candidates,
            int value, boolean orderedWrites) throws Exception {
        JsonObject edge = binding("EDGE.GUARDED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        edge.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        ownWriterVersions(envelope, "REGION.0", fatalInstance,
                "TASK.TARGET");
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24, candidates);
        ownGuardedCandidates(guarded, "REGION.0", "TASK.TARGET");
        SharedStateEvidence.normalizeGuards(guarded);
        RelationSummary producer = summary("GUARDED",
                outerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(edge));
        JsonObject ledger = orderedWrites
                ? RecordedSharedStateFixtures.twoWriterLedger()
                : readOnlyLedger();
        JsonArray constraints = new JsonArray();
        constraints.add(binary(guarded, "==", integer(value)));
        JsonObject fatal = fatalQuery(fatalInstance, constraints, edge);
        JsonObject fatalPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        fatalPath.addProperty("sourceTaskId", "TASK.TARGET");
        fatalPath.add(SharedStateEvidence.RECORDED_FIELD,
                        RecordedSharedStateFixtures.recordedMember(envelope,
                                ledger, "example.State#value"));
        return composeFatal(fatalInstance, Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), fatal,
                Collections.singletonList(edge));
    }

    /** A ledger that holds the read and neither of the two writes. */
    private static JsonObject readOnlyLedger() {
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(21L, "FIELD_READ", 103L,
                "REGION.reader"));
        return RecordedSharedStateFixtures.ledgerEnvelope(events,
                new JsonArray());
    }


    private static String publishPhase(String occurrence) {
        return "SOURCE_PHASE.PUBLISH."
                + CanonicalJson.sha256(occurrence).substring(0, 16);
    }

    private static String configuredRaw(String phase, String source,
                                        String suffix) {
        return "M_I_field_" + SymbolicSourceEvidence.engineLabelForPhase(
                phase, source) + "_" + suffix;
    }

    /**
     * A second output of the same producer, carrying a different value.
     *
     * <p>It is what makes the competing candidate observable: if the recorded
     * answer's port were bound twice, the two producers would be equated and
     * 10 = 20 would make the whole query unsatisfiable.</p>
     */
    private static RelationSummary withCompetingOutput(
            RelationSummary summary) {
        JsonObject row = summary.toJson();
        JsonObject slice = emptySlice("REGION.1.out.1",
                "<Test: int competing>");
        OutputClosureContract second = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1", Collections.<String>emptyList(),
                "REGION.1.out.1", "<Test: int competing>", "REGION_OUTPUT",
                "int", slice);
        OutputClosureCodec.writeTo(row, OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(row), second)));
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject().getAsJsonObject("outputExpressions")
                .add("REGION.1.out.1", integer(20));
        return RelationSummary.decode(row);
    }

    /** The same relation, restating - or dropping - its declared coverage. */
    private static RelationSummary declaring(RelationSummary summary,
                                             String coverageState) {
        JsonObject row = summary.toJson();
        if (coverageState == null) {
            row.remove("pathCoverageState");
        } else {
            row.addProperty("pathCoverageState", coverageState);
        }
        return RelationSummary.decode(row);
    }

    private static RelationSummary withRecorded(RelationSummary summary,
                                                JsonObject envelope,
                                                JsonObject ledger) {
        JsonObject row = summary.toJson();
        row.add(SharedStateEvidence.RECORDED_FIELD,
                RecordedSharedStateFixtures.recordedMember(envelope, ledger,
                        "example.State#value"));
        return RelationSummary.decode(row);
    }

    private ConcolicSmtComposer.Result composeTarget(
            String fatalInstance, RelationSummary producer,
            JsonObject targetPredicate, JsonObject firstHop)
            throws Exception {
        JsonArray constraints = new JsonArray();
        constraints.add(targetPredicate);
        return compose(fatalInstance, Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), constraints,
                firstHop);
    }

    /** The same query with one extra assumption, for one truth-table row. */
    private static String assuming(String smtLib, String... assumptions) {
        int check = smtLib.lastIndexOf("(check-sat)");
        StringBuilder query = new StringBuilder(smtLib.substring(0, check));
        for (String assumption : assumptions) {
            query.append("(assert ").append(assumption).append(')')
                    .append(System.lineSeparator());
        }
        return query.append("(check-sat)").append(System.lineSeparator())
                .toString();
    }

    /** Runs one query through the real solver and returns its answer. */
    private static String z3(String smtLib) throws Exception {
        Process process = new ProcessBuilder("z3", "-smt2", "-in")
                .redirectErrorStream(true).start();
        process.getOutputStream().write(
                smtLib.getBytes(StandardCharsets.UTF_8));
        process.getOutputStream().close();
        String output = new String(readAll(process.getInputStream()),
                StandardCharsets.UTF_8).trim();
        process.waitFor();
        int newline = output.indexOf('\n');
        return newline < 0 ? output : output.substring(0, newline).trim();
    }

    private static byte[] readAll(java.io.InputStream stream)
            throws java.io.IOException {
        java.io.ByteArrayOutputStream buffer =
                new java.io.ByteArrayOutputStream();
        byte[] chunk = new byte[8192];
        int read;
        while ((read = stream.read(chunk)) >= 0) buffer.write(chunk, 0, read);
        return buffer.toByteArray();
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start()
                    .waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }

    /**
     * Decorates one merged relation with the shared state its executions
     * recorded: two competing writers of one location, a guarded read of it
     * in the target region, and the ledger that orders the two writers.
     */
    private static RelationSummary withRecordedSharedState(
            RelationSummary summary) {
        return withRecordedSharedState(summary,
                RecordedSharedStateFixtures.twoWriterLedger());
    }

    private static RelationSummary withRecordedSharedState(
            RelationSummary summary, JsonObject ledger) {
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        JsonObject summaryRow = summary.toJson();
        JsonObject selectedCase = summaryRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        ownWriterVersions(envelope, "REGION.1", summary.occurrenceId(),
                selectedCase.get("sourceTaskId").getAsString());
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty("regionId", "REGION.0");
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        "REGION.0@Test#call30");
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24);
        ownGuardedCandidates(guarded, "REGION.1",
                selectedCase.get("sourceTaskId").getAsString());
        SharedStateEvidence.normalizeGuards(guarded);
        // The guarded term rides with the writer's value, which is where the
        // composer's expression scan finds it.
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .add("expression", guarded);
        // The runtime records the declared field beside the VM's own location
        // identity, and a gate needs it: the location key does not survive
        // into a second session, and the field does.
        selectedCase.add(SharedStateEvidence.RECORDED_FIELD,
                RecordedSharedStateFixtures.recordedMember(envelope, ledger,
                        "example.State#value"));
        return RelationSummary.decode(summaryRow);
    }

    /** Gives the fixture's copied versions one exact selected case owner. */
    private static void ownWriterVersions(JsonObject envelope,
                                          String regionId,
                                          String occurrenceId,
                                          String taskId) {
        for (JsonElement element : envelope.getAsJsonArray("versions")) {
            JsonObject version = element.getAsJsonObject();
            version.addProperty("regionId", regionId);
            version.addProperty("taskId", taskId);
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    occurrenceId);
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    "TEST_DRIVER/test#epoch0");
        }
    }

    /** Aligns copied RF arms with the selected case owning their versions. */
    private static void ownGuardedCandidates(JsonObject guarded,
                                             String regionId,
                                             String taskId) {
        for (JsonElement element : guarded.getAsJsonArray("candidates")) {
            JsonObject candidate = element.getAsJsonObject();
            if (candidate.get("unknown").getAsBoolean()) continue;
            candidate.addProperty("regionId", regionId);
            candidate.addProperty("taskId", taskId);
        }
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries,
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries, regionRows,
                targetConstraints(), firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonArray constraints,
            JsonObject... firstHops) throws Exception {
        return compose(fatalInstance, summaries, regionRows, constraints,
                null, firstHops);
    }

    private ConcolicSmtComposer.Result compose(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonArray constraints,
            java.util.List<JsonObject> edgeValidations,
            JsonObject... firstHops) throws Exception {
        return composeFatal(fatalInstance, summaries, regionRows,
                fatalQuery(fatalInstance, constraints, firstHops),
                edgeValidations);
    }

            /** {@code (VRef nullRef)} as a recorded null literal. */
    private static JsonObject nullRef() {
        JsonObject n = new JsonObject();
        n.addProperty("_type", "ConstExpr");
        n.addProperty("_java_type", "L");
        n.addProperty("_exp", "N");
        return n;
    }

    private static JsonObject assocStateSymbol(String symbol) {
        JsonObject id = new JsonObject();
        id.addProperty("_type", "SymbolExpression");
        id.addProperty("_java_type", "java/util/HashMap");
        id.addProperty("_exp", symbol);
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.add("arguments", new JsonArray());
        state.add("receiver", id);
        state.addProperty("_java_type", "L");
        return state;
    }

    private static JsonObject assocPut(JsonElement receiver, int key,
                                       int value) {
        JsonArray arguments = new JsonArray();
        arguments.add(integer(key));
        arguments.add(integer(value));
        JsonObject put = new JsonObject();
        put.addProperty("_type", "ContainerRelation");
        put.addProperty("shape", "ASSOCIATIVE");
        put.addProperty("operation", "PUT");
        put.addProperty("_java_type", "java/util/Map");
        put.add("receiver", receiver.deepCopy());
        put.add("arguments", arguments);
        return put;
    }

    private static void decorateMapOccurrence(
            JsonObject pathCase, String planned, int ordinal,
            JsonObject expression) {
        String occurrence = planned + "#a" + ordinal;
        String task = "TASK.MAP.TIMELINE.A" + ordinal;
        pathCase.addProperty("caseId", "CASE.MAP.TIMELINE.A" + ordinal);
        pathCase.addProperty("sourceTaskId", task);
        pathCase.addProperty("occurrenceId", occurrence);
        pathCase.addProperty(PathObservation.ACTIVATION_ORDINAL, ordinal);
        pathCase.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, planned);

        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", 59L);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 100L + ordinal);
        version.addProperty("versionKind", "STATE_PUT");
        version.addProperty("writerContextId", 200L + ordinal);
        version.addProperty("writerJavaThreadId", 300L + ordinal);
        version.addProperty("writerStep", ordinal);
        version.addProperty("regionId", "REGION.1");
        version.addProperty("taskId", task);
        version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                "TEST_DRIVER/test#epoch0");
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                occurrence);
        version.addProperty("volatileWrite", false);
        version.addProperty("fingerprintKind", "NONE");
        version.addProperty("fingerprint", 0L);
        version.add("expression", expression.deepCopy());
        version.add("pathGuard", null);
        version.addProperty("versionOrdinal", 1);
        version.addProperty("writerEventId", 100L + ordinal);
        JsonArray versions = new JsonArray();
        versions.add(version);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", true);
        envelope.addProperty("versionsDropped", 0);
        envelope.addProperty("serializationTruncated", false);
        envelope.addProperty("readsDropped", 0);
        envelope.addProperty("readLogTruncated", false);
        envelope.add("versions", versions);
        envelope.add("reads", new JsonArray());
        JsonObject record = SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                RecordedEvidenceIdentity.of("", "workload#1", task,
                        occurrence, "TEST_DRIVER/test#epoch0", ordinal));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        carrier.addProperty("declaringClass", "example.State");
        carrier.addProperty("fieldName", "values");
        carrier.addProperty("descriptor", "Ljava/util/Map;");
        carrier.addProperty("index", -1);
        carrier.addProperty("receiverObjectId", 77L);
        carrier.addProperty("fieldKey",
                "example.State#values:Ljava/util/Map;");
        record.add("carrier", carrier);
        pathCase.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.singletonList(record), null));
    }

    /** {@code get(key)} over a map version expression. */
    private static JsonObject mapGet(JsonElement mapState, int key) {
        JsonObject keyExpr = new JsonObject();
        keyExpr.addProperty("_type", "ConstExpr");
        keyExpr.addProperty("_java_type", "I");
        keyExpr.addProperty("_exp", "Y_I_" + key);
        JsonArray args = new JsonArray();
        args.add(keyExpr);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ContainerRelation");
        read.addProperty("shape", "ASSOCIATIVE");
        read.addProperty("operation", "READ");
        read.add("arguments", args);
        read.add("receiver", mapState);
        read.addProperty("_java_type", "L");
        return read;
    }

    private ConcolicSmtComposer.Result composeFatal(
            String fatalInstance, java.util.List<RelationSummary> summaries,
            java.util.List<JsonObject> regionRows, JsonObject fatalRow,
            java.util.List<JsonObject> edgeValidations) throws Exception {
        Path directory = temporary.newFolder().toPath();
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaryFile = directory.resolve("summaries.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("candidate.smt2");
        Path manifest = directory.resolve("manifest.json");

        writeJsonl(fatal, fatalRow);
        StringBuilder encoded = new StringBuilder();
        for (RelationSummary summary : summaries) {
            encoded.append(summary.toJson()).append('\n');
        }
        Files.write(summaryFile, encoded.toString().getBytes(
                StandardCharsets.UTF_8));
        writeJsonl(regions, regionRows.toArray(
                new JsonObject[regionRows.size()]));

        Path runtimePlan = directory.resolve("runtime_plan.jsonl");
        Files.write(runtimePlan, RuntimePlanArtifact.encode(
                java.util.Collections.<JsonObject>emptyList(),
                edgeValidations == null
                        ? java.util.Collections.<JsonObject>emptyList()
                        : edgeValidations,
                regionRows).getBytes(StandardCharsets.UTF_8));
        java.util.List<String> argv = new java.util.ArrayList<>(
                Arrays.asList(
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaryFile.toString(),
                        "--runtime-plan", runtimePlan.toString(),
                        "--output", output.toString(),
                        "--manifest", manifest.toString(),
                        "--fatal-region", "REGION.0",
                        "--occurrence-id", fatalInstance));
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(
                        argv.toArray(new String[argv.size()])));
    }

        private static RelationSummary summary(
            String id, String instance, int value,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, integer(value), inputPorts, bindings);
    }

    private static RelationSummary summary(
            String id, String instance, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings) {
        return summary(id, instance, output, inputPorts, bindings, "int");
    }

    private static RelationSummary summary(
            String id, String instance, JsonObject output,
            java.util.List<String> inputPorts,
            java.util.List<JsonObject> bindings, String outputJavaType) {
        JsonObject slice = emptySlice("REGION.1.out.0",
                "<Test: " + outputJavaType + " output>");
        JsonArray inputs = new JsonArray();
        for (String input : inputPorts) inputs.add(input);
        slice.add("inputPorts", inputs);
        JsonArray causalEdges = slice.getAsJsonArray("causalEdgeIds");
        for (JsonObject binding : bindings) {
            if ("REGION.1.out.0".equals(
                    binding.get("fromOutputPort").getAsString())) {
                causalEdges.add(binding.get("edgeId").getAsString());
            }
        }
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1", Collections.<String>emptyList(), "REGION.1.out.0",
                "<Test: " + outputJavaType + " output>", "REGION_OUTPUT",
                outputJavaType, slice);

        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", RelationSummary.SCHEMA_VERSION);
        row.addProperty("kind", RelationSummary.KIND);
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
        row.addProperty("regionId", "REGION.1");
        row.addProperty("occurrenceId", instance);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(row);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray encodedBindings = new JsonArray();
        for (JsonObject binding : bindings) {
            encodedBindings.add(binding.deepCopy());
        }
        row.add("edgeBindings", encodedBindings);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE." + id);
        path.addProperty("occurrenceId", instance);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        path.addProperty("sourceTaskId", "TASK." + id);
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", output);
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        // What a closed worklist's merge declares, and what the acceptance
        // gate reads: this relation's own path set is the one it published.
        row.addProperty("pathCoverageState", "CLOSED");
        return RelationSummary.decode(row);
    }

    private static JsonObject emptySlice(String port, String cell) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        return slice;
    }

    private static JsonObject fatalQuery(
            String fatalInstance, JsonArray constraints,
            JsonObject... firstHops) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion",
                TargetReachPathQueryBuilder.SCHEMA_VERSION);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("queryKey", "QUERY.TEST.FATAL");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", fatalInstance);
        fatal.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("targetOccurrence", 1);
        fatal.addProperty("requiredTakenOutcome", false);
        fatal.addProperty("constraintAuthority",
                "RECORDED_TARGET_PREFIX_V1");
        JsonObject path = new JsonObject();
        path.add("constraints", constraints.deepCopy());
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        path.addProperty("desiredTakenOutcome", false);
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.SOURCE_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder.SOURCE_FATAL_BRANCH_AUTHORITY);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", "<Test: void consume()>#u1");
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        path.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        JsonArray paths = new JsonArray();
        paths.add(path);
        fatal.add("paths", paths);
        fatal.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        if (constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "test fatal query requires a target predicate");
        }
        JsonElement requiredPredicate = constraints.get(
                constraints.size() - 1);
        BranchWitness witness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>",
                1, 1, true, BranchPredicateAlgebra.complement(
                requiredPredicate),
                0, metadata);
        path.add(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS,
                witness.toJson());
        fatal.add("seedReplayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), witness).toJson());
        LoopBoundPolicy.cfgBackedges(8).writeTo(fatal);

        JsonArray selectedTargetBindings = new JsonArray();
        for (JsonObject firstHop : firstHops) {
            selectedTargetBindings.add(firstHop.deepCopy());
        }
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", fatalInstance);
        fatal.add("symbolicContext", context);
        fatal.add("selectedTargetBindings", selectedTargetBindings);
        return fatal;
    }

    /** Converts the fixture's seed-side attestation into an exact hit. */
    private static void markRequiredTargetPath(JsonObject path) {
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder.REQUIRED_FATAL_BRANCH_AUTHORITY);
        path.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);
        JsonArray constraints = path.getAsJsonArray("constraints");
        JsonObject witness = path.getAsJsonObject(
                TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS);
        witness.addProperty("sourceTakenOutcome", false);
        witness.add("sourceSatisfiedPredicate",
                constraints.get(constraints.size() - 1).deepCopy());
    }

    /** One non-constant target predicate for fixtures without a region port. */
    private static JsonArray targetConstraints() {
        JsonArray result = new JsonArray();
        result.add(binary(reference("M_I_field_TEST_TARGET_GATE", "I"),
                ">", integer(0)));
        return result;
    }

    private static JsonObject binding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, long writer, long reader) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("fromOccurrenceId", fromInstance);
        binding.addProperty("toOccurrenceId", toInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        binding.addProperty("writerEventSeq", writer);
        binding.addProperty("readerEventSeq", reader);
        binding.addProperty("receiverObjectId", 7);
        return binding;
    }

    private static JsonObject protocolBinding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("state", "CANDIDATE_TRACED_RPC_EXCHANGE");
        binding.addProperty("evidenceKind",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        binding.addProperty("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        binding.addProperty("transportKind", "HADOOP_IPC");
        binding.addProperty("fromRegion", regionOf(fromPort));
        binding.addProperty("fromOccurrenceId", fromInstance);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toRegion", regionOf(toPort));
        binding.addProperty("toOccurrenceId", toInstance);
        binding.addProperty("toInputPort", toPort);
        return binding;
    }

    private static JsonObject exactWireBinding(
            String edgeId, String fromInstance, String fromPort,
            String toInstance, String toPort, String request, String attempt,
            String direction, long sent, long received) {
        JsonObject binding = protocolBinding(edgeId, fromInstance, fromPort,
                toInstance, toPort);
        int targetSeparator = toInstance.indexOf('@');
        if (targetSeparator > 0) {
            binding.addProperty("toRegion",
                    toInstance.substring(0, targetSeparator));
        }
        binding.addProperty("transportKind", "HTTP");
        binding.addProperty("exchangeSiteKey", "REGION.1");
        binding.addProperty("exchangeLeg", edgeId + "\n" + attempt + "\n"
                + direction);
        binding.addProperty("attemptId", attempt);
        binding.addProperty("requestKey", request);
        binding.addProperty("javaType", "int");
        binding.addProperty("direction", direction);
        binding.addProperty("protocolDirection", direction);
        binding.addProperty("handoffLeafPath", fromPort);
        binding.addProperty("senderEventSeq", sent);
        binding.addProperty("receiverEventSeq", received);
        return binding;
    }

    private static JsonObject region(
            String id, boolean hasInput, boolean hasOutput) {
        return region(id, hasInput ? "int" : "",
                hasOutput ? "int" : "");
    }

    private static JsonObject region(
            String id, String inputType, String outputType) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (!inputType.isEmpty()) {
            inputs.add(port(id + ".in.0", true, inputType));
        }
        region.add("symbolicInputs", inputs);
        JsonArray outputs = new JsonArray();
        if (!outputType.isEmpty()) {
            outputs.add(port(id + ".out.0", false, outputType));
        }
        region.add("outputs", outputs);
        return region;
    }

    private static JsonObject port(
            String id, boolean input, String javaType) {
        return statePort(id, javaType, input
                ? "<Test: " + javaType + " input>"
                : "<Test: " + javaType + " output>");
    }

    private static JsonObject statePort(
            String id, String javaType, String cell) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", id);
        port.addProperty("cell", cell);
        port.addProperty("javaType", javaType);
        return port;
    }



    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject longInteger(long value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "J");
        result.addProperty("_exp", "Y_J_" + value);
        return result;
    }

    private static JsonObject reference(String symbol, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", symbol);
        return result;
    }

    private static JsonObject fieldAccess(JsonObject owner,
                                          String ownerClass,
                                          int fieldOffset,
                                          String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "FieldAccessExpression");
        result.add("owner", owner.deepCopy());
        result.addProperty("ownerClass", ownerClass);
        result.addProperty("fieldOffset", fieldOffset);
        result.addProperty("_java_type", javaType);
        return result;
    }

    private static RelationSummary withProducerGuardAndInteraction(
            RelationSummary summary, JsonObject condition, String portId,
            long exportEventId) {
        JsonObject row = summary.toJson();
        JsonObject path = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        path.getAsJsonObject("guard").getAsJsonArray("conditions")
                .add(condition);
        JsonObject interaction = new JsonObject();
        interaction.addProperty("outputSiteId",
                "COMMUNICATION_EFFECT:test:" + portId);
        interaction.addProperty("outputOccurrence", 1);
        interaction.addProperty("outputVersionOrdinal", 1);
        interaction.addProperty("replayOccurrence", 1);
        interaction.addProperty("interactionKind", "COMMUNICATION_EFFECT");
        interaction.addProperty("authority",
                "INSTRUMENTED_INTERACTION_SITE_V1");
        interaction.addProperty("portId", portId);
        // README RPC-1: the producer's own export event is what identifies
        // this case as the sender, so the fixture has to carry the id the
        // matching handoff reference exports.
        interaction.addProperty("exportEventId", exportEventId);
        JsonArray interactions = new JsonArray();
        interactions.add(interaction);
        path.add(RelationSummary.INTERACTION_EVENTS, interactions);
        return RelationSummary.decode(row);
    }

    private static JsonObject binary(
            JsonObject left, String operator, JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static String regionOf(String port) {
        int marker = port.indexOf(".in.");
        return marker < 0 ? port.substring(0, port.indexOf(".out."))
                : port.substring(0, marker);
    }

    private static void writeJsonl(Path path, JsonObject... rows)
            throws Exception {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) value.append(row).append('\n');
        Files.write(path, value.toString().getBytes(StandardCharsets.UTF_8));
    }
}
