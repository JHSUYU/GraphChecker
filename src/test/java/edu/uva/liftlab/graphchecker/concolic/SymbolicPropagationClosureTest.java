package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Core receiver-boundary contracts: additive merging and stable lineage. */
public class SymbolicPropagationClosureTest {
    private static final String EPOCH = "epoch-1";

    @Test
    public void sameLocalCaseWithDifferentPayloadUsesReplayObservations() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String suffix = replay == 1 ? "FIRST" : "SECOND";
            String scope = "replay-group:conflict-" + replay;
            String producerTask = "TASK.P." + suffix;
            JsonObject value = symbol("M_VALUE_" + replay);
            JsonObject producer = summary("P", "P#a1", producerTask,
                    scope, value);
            JsonObject input = boundary(VmExpressionIr.RPC_ATTACH,
                    920 + replay, value);
            JsonObject receiver = summary("R", "R#a1",
                    "TASK.R." + suffix, scope, input);
            handoff(receiver, "FAMILY.CONFLICT", "R.in", 920 + replay,
                    producerTask, "P#a1", input);
            rows.add(producer);
            rows.add(receiver);
        }

        SymbolicPropagationClosure.Result result = rewrite(rows);

        assertTrue(result.complete());
        JsonObject merge = merge(result, "FAMILY.CONFLICT");
        assertEquals(2, merge.getAsJsonArray("arms").size());
        Set<String> selectors = dependencySelectors(result);
        assertEquals(2, selectors.size());
        Set<String> baseCases = new LinkedHashSet<>();
        for (JsonElement encoded : dependency(result,
                "FAMILY.CONFLICT").getAsJsonArray("arms")) {
            JsonObject arm = encoded.getAsJsonObject();
            assertEquals(string(arm,
                            SymbolicPropagationClosure.OBSERVATION_SELECTOR),
                    string(arm, "selector"));
            baseCases.add(string(arm, "caseSelector"));
        }
        assertEquals(1, baseCases.size());
    }

    @Test
    public void stablePayloadKeepsBaseMergeButPublishesFlatObservations() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String suffix = replay == 1 ? "FIRST" : "SECOND";
            String scope = "replay-group:mixed-" + replay;
            String producerTask = "TASK.P." + suffix;
            JsonObject producer = summary("P", "P#a1", producerTask,
                    scope, constant(1));
            JsonObject varying = boundary(VmExpressionIr.RPC_ATTACH,
                    940 + replay, symbol("M_VALUE_" + replay));
            JsonObject stable = boundary(VmExpressionIr.RPC_ATTACH,
                    950 + replay, symbol("M_STABLE"));
            JsonObject receiver = summary("R", "R#a1",
                    "TASK.R." + suffix, scope, binary(varying, stable));
            handoff(receiver, "FAMILY.VARYING", "R.varying",
                    940 + replay, producerTask, "P#a1", varying);
            handoff(receiver, "FAMILY.STABLE", "R.stable",
                    950 + replay, producerTask, "P#a1", stable);
            rows.add(producer);
            rows.add(receiver);
        }

        SymbolicPropagationClosure.Result result = rewrite(rows);

        assertTrue(result.complete());
        assertEquals(1, merge(result, "FAMILY.STABLE")
                .getAsJsonArray("arms").size());
        JsonArray dependencyArms = dependency(result, "FAMILY.STABLE")
                .getAsJsonArray("arms");
        assertEquals(2, dependencyArms.size());
        Set<String> baseCases = new LinkedHashSet<>();
        for (JsonElement encoded : dependencyArms) {
            JsonObject arm = encoded.getAsJsonObject();
            assertEquals(string(arm,
                            SymbolicPropagationClosure.OBSERVATION_SELECTOR),
                    string(arm, "selector"));
            assertTrue(arm.has("pathCondition"));
            assertFalse(arm.has("pathObservations"));
            baseCases.add(string(arm, "caseSelector"));
        }
        assertEquals(1, baseCases.size());
    }

    @Test
    public void fanInMergesTwoPlusTwoWithoutCartesianCases() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String scope = "replay-group:g" + replay;
            rows.add(summary("B", "B#a1", "TASK.B." + replay, scope,
                    symbol("M_B_" + replay)));
            rows.add(summary("C", "C#a1", "TASK.C." + replay, scope,
                    symbol("M_C_" + replay)));
            JsonObject b = boundary(VmExpressionIr.RPC_ATTACH,
                    100 + replay, symbol("M_B_" + replay));
            JsonObject c = boundary(VmExpressionIr.RPC_ATTACH,
                    200 + replay, symbol("M_C_" + replay));
            JsonObject a = summary("A", "A#a1", "TASK.A." + replay,
                    scope, binary(b, c));
            handoff(a, "FAMILY.B", "B.in", 100 + replay,
                    "TASK.B." + replay, "B#a1", b);
            handoff(a, "FAMILY.C", "C.in", 200 + replay,
                    "TASK.C." + replay, "C#a1", c);
            rows.add(a);
        }

        SymbolicPropagationClosure.Result result =
                rewrite(rows);

        assertTrue(result.complete());
        assertEquals(2, merge(result, "FAMILY.B")
                .getAsJsonArray("arms").size());
        assertEquals(2, merge(result, "FAMILY.C")
                .getAsJsonArray("arms").size());
        assertEquals(4, dependencySelectors(result).size());
        assertEquals(2, mergeIds(result.summaries()).size());
    }

    @Test
    public void nestedChainReusesInnerFamilyAndRewritesOuterCasePcs() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String scope = "replay-group:n" + replay;
            rows.add(summary("C", "C#a1", "TASK.C." + replay, scope,
                    symbol("M_C_" + replay)));
            JsonObject fromC = boundary(VmExpressionIr.RPC_ATTACH,
                    300 + replay, symbol("M_C_" + replay));
            JsonObject bValue = add(fromC, constant(replay));
            JsonObject b = summary("B", "B#a1", "TASK.B." + replay,
                    scope, binary(fromC, constant(10)));
            handoff(b, "FAMILY.C", "B.fromC", 300 + replay,
                    "TASK.C." + replay, "C#a1", fromC);
            rows.add(b);
            JsonObject fromB = boundary(VmExpressionIr.RPC_ATTACH,
                    400 + replay, bValue);
            JsonObject a = summary("A", "A#a1", "TASK.A." + replay,
                    scope, binary(fromB, constant(12)));
            handoff(a, "FAMILY.B", "A.fromB", 400 + replay,
                    "TASK.B." + replay, "B#a1", fromB);
            rows.add(a);
        }

        SymbolicPropagationClosure.Result result =
                rewrite(rows);

        assertTrue(result.complete());
        Set<String> expected = new LinkedHashSet<>(Arrays.asList(
                "CONSUMER." + CanonicalJson.sha256("FAMILY.B"),
                "CONSUMER." + CanonicalJson.sha256("FAMILY.C")));
        assertEquals(expected, mergeIds(result.summaries()));
        assertTrue(containsType(dependency(result, "FAMILY.B"),
                SymbolicPropagationClosure.ITE_TYPE));
        for (String family : Arrays.asList("FAMILY.B", "FAMILY.C")) {
            JsonObject merge = merge(result, family);
            assertEquals("I", merge.get("_java_type")
                    .getAsString());
            assertTrue(VmExpressionIr.isPrimitiveIntExpression(merge));
        }
        assertEquals(4, dependencySelectors(result).size());
    }

    @Test
    public void guardedReadCarriesEveryWriterCase() {
        String scope = "replay-group:guarded-writer-cases";
        JsonObject positive = summary("W", "W#a1", "TASK.W.POS", scope,
                binary(symbol("M_INPUT"), constant(0)));
        JsonObject negative = summary("W", "W#a1", "TASK.W.NEG", scope,
                binary(symbol("M_INPUT"), constant(1)));
        JsonObject first = candidate("rf_positive", 691L,
                symbol("M_POSITIVE"), positive, 1);
        JsonObject second = candidate("rf_negative", 692L,
                symbol("M_NEGATIVE"), negative, 2);
        JsonObject read = guardedRead(701L, first, second);
        read.addProperty("writerSetComplete", false);
        JsonObject reader = summary("R", "R#a1", "TASK.R", scope,
                boundary(VmExpressionIr.FIELD_READ, 701L, read));
        addGuardedReadEvidence(reader, read, positive, negative);

        SymbolicPropagationClosure.Result result = rewrite(Arrays.asList(
                positive, negative, reader));

        assertFalse(result.complete());
        assertTrue(result.gaps().toString(), result.gaps().toString()
                .contains("READ_FROM_SNAPSHOT_INCOMPLETE"));
        JsonObject rewritten = firstExpressionOfType(result.summaries(),
                SharedStateEvidence.GUARDED_READ_TYPE);
        assertEquals(2, rewritten.getAsJsonArray("candidates").size());
        Set<String> families = new LinkedHashSet<>();
        for (JsonElement encoded : rewritten.getAsJsonArray("candidates")) {
            JsonObject arm = encoded.getAsJsonObject();
            families.add(string(arm,
                    SymbolicPropagationClosure.WRITER_CASE_FAMILY));
            assertTrue(arm.has(SymbolicPropagationClosure.WRITER_CASE_OWNER));
            assertTrue(arm.has(
                    SymbolicPropagationClosure.WRITER_CASE_SELECTOR));
        }
        assertEquals(1, families.size());
        JsonObject dependency = dependency(result,
                families.iterator().next());
        assertEquals(SymbolicPropagationClosure.READ_FROM_DEPENDENCY_POLICY,
                string(dependency, "selectionPolicy"));
        assertEquals(2, dependency.getAsJsonArray("arms").size());

    }

    @Test
    public void readTimeCandidateCountDoesNotIncludeLaterWriters() {
        String scope = "replay-group:read-time-candidates";
        JsonObject writer = summary("W", "W#a1", "TASK.W", scope,
                symbol("M_WRITER"));
        JsonObject firstRead = guardedRead(701L,
                candidate("rf_before", 691L, symbol("M_BEFORE"),
                        writer, 1));
        JsonObject secondRead = guardedRead(711L,
                candidate("rf_before", 691L, symbol("M_BEFORE"),
                        writer, 1),
                candidate("rf_after", 706L, symbol("M_AFTER"),
                        writer, 2));
        JsonObject reader = summary("R", "R#a1", "TASK.R", scope,
                binary(boundary(VmExpressionIr.FIELD_READ, 701L, firstRead),
                        boundary(VmExpressionIr.FIELD_READ, 711L,
                                secondRead)));
        addGuardedReadEvidence(reader, secondRead, writer, writer);

        JsonObject envelope = reader.getAsJsonObject(
                SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .getAsJsonObject("envelope");
        JsonObject observedSecond = envelope.getAsJsonArray("reads")
                .get(0).getAsJsonObject();
        JsonObject observedFirst = observedSecond.deepCopy();
        observedFirst.addProperty("readEventId", 701L);
        observedFirst.addProperty("candidateCount", 1);
        JsonArray reads = new JsonArray();
        reads.add(observedFirst);
        reads.add(observedSecond);
        envelope.add("reads", reads);

        SymbolicPropagationClosure.Result result = rewrite(Arrays.asList(
                writer, reader));

        assertTrue(result.gaps().toString(), result.complete());
    }

    @Test
    public void replayedWriterArmKeepsItsPhysicalEnclosingCase() {
        String falseScope = "replay-group:outer-false";
        JsonObject outerFalse = summary("O", "O#a1", "TASK.O.NEG",
                falseScope, binary(symbol("M_CONFIG"), constant(0)));
        JsonObject writerFalse = summary("W", "W#a1", "TASK.W.FALSE",
                falseScope, binary(symbol("M_VALUE"), constant(1)));
        JsonObject decrement = candidate("rf_decrement", 801L,
                add(symbol("M_VALUE"), constant(-1)), writerFalse, 1);
        JsonObject read = guardedRead(811L, decrement);
        JsonObject reader = summary("R", "R#a1", "TASK.R.FALSE",
                falseScope, boundary(VmExpressionIr.FIELD_READ, 811L,
                        read));
        addGuardedReadEvidence(reader, read, writerFalse);
        JsonObject recordedVersion = reader.getAsJsonObject(
                SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .getAsJsonObject("envelope").getAsJsonArray("versions")
                .get(0).getAsJsonObject();
        recordedVersion.add(
                SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE,
                activationClosure(writerFalse, outerFalse));

        String trueScope = "replay-group:outer-true";
        JsonObject outerTrue = summary("O", "O#a1", "TASK.O.POS",
                trueScope, binary(symbol("M_CONFIG"), constant(1)));
        JsonObject writerTrue = summary("W", "W#a1", "TASK.W.TRUE",
                trueScope, binary(symbol("M_VALUE"), constant(1)));

        SymbolicPropagationClosure.Result result = rewrite(Arrays.asList(
                outerFalse, writerFalse, reader, outerTrue, writerTrue));

        assertTrue(result.gaps().toString(), result.complete());
        JsonObject rewritten = firstExpressionOfType(result.summaries(),
                SharedStateEvidence.GUARDED_READ_TYPE);
        JsonObject arm = rewritten.getAsJsonArray("candidates")
                .get(0).getAsJsonObject();
        JsonArray closure = arm.getAsJsonArray(
                SymbolicPropagationClosure.WRITER_CASE_CLOSURE);
        Set<String> owners = new LinkedHashSet<>();
        for (JsonElement encoded : closure) {
            owners.add(string(encoded.getAsJsonObject(),
                    SymbolicPropagationClosure.WRITER_CASE_OWNER));
        }
        String falseOwner = LocalCaseIdentity.owner(outerFalse);
        String trueOwner = LocalCaseIdentity.owner(outerTrue);
        assertEquals(2, owners.size());
        assertTrue(owners.contains(LocalCaseIdentity.owner(writerFalse)));
        assertTrue(owners.contains(falseOwner));
        assertFalse(owners.contains(trueOwner));
        assertEquals(falseScope, string(arm,
                SymbolicPropagationClosure.OBSERVATION_SCOPE));
        assertFalse(string(arm,
                SymbolicPropagationClosure.OBSERVATION_SELECTOR).isEmpty());

        String outerFamily = "";
        for (JsonElement encoded : closure) {
            JsonObject localCase = encoded.getAsJsonObject();
            if (falseOwner.equals(string(localCase,
                    SymbolicPropagationClosure.WRITER_CASE_OWNER))) {
                outerFamily = string(localCase,
                        SymbolicPropagationClosure.WRITER_CASE_FAMILY);
            }
        }
        JsonObject outerDependency = dependency(result, outerFamily);
        assertEquals(2, outerDependency.getAsJsonArray("arms").size());
        assertEquals(SymbolicPropagationClosure.READ_FROM_DEPENDENCY_POLICY,
                string(outerDependency, "selectionPolicy"));
    }

    @Test
    public void mapReadCandidateProjectsItsRecordedState() {
        String scope = "replay-group:map-projection";
        JsonObject state = containerRelation("STATE", symbol("M_MAP"));
        JsonObject query = containerRelation("READ", state);
        JsonObject writer = summary("W", "W#a1", "TASK.W", scope,
                state);
        JsonObject arm = candidate("rf_map", 693L, query, writer, 1);
        arm.addProperty("versionKind", "STATE_PUT");
        JsonObject read = guardedRead(702L, arm);
        JsonObject location = read.getAsJsonObject("location");
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        JsonObject reader = summary("R", "R#a1", "TASK.R", scope,
                boundary(VmExpressionIr.FIELD_READ, 702L, read));
        addGuardedReadEvidence(reader, read, writer);
        JsonObject record = reader.getAsJsonObject(
                SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject();
        record.addProperty("locationKey", "MAP_STATE/17#-3");
        record.getAsJsonObject("carrier").addProperty("kind", "MAP_STATE");
        JsonObject recordedVersion = record.getAsJsonObject("envelope")
                .getAsJsonArray("versions").get(0).getAsJsonObject();
        recordedVersion.addProperty("versionKind", "STATE_PUT");
        recordedVersion.add("expression", state.deepCopy());

        SymbolicPropagationClosure.Result result = rewrite(Arrays.asList(
                writer, reader));

        assertTrue(result.gaps().toString(), result.complete());
        JsonObject rewritten = firstExpressionOfType(result.summaries(),
                SharedStateEvidence.GUARDED_READ_TYPE);
        assertEquals("READ", rewritten.getAsJsonArray("candidates").get(0)
                .getAsJsonObject().getAsJsonObject("expression")
                .get("operation").getAsString());
    }

    @Test
    public void initialReadUsesStableSourceWithoutProducerSummary() {
        String scope = "replay-group:initial-source";
        JsonObject absentInstaller = summary("W", "W#a1", "TASK.W", scope,
                symbol("M_INITIAL"));
        JsonObject initial = candidate("rf_initial", 24L,
                symbol("M_INITIAL"), absentInstaller, 1);
        initial.addProperty("versionKind", "INITIAL");
        JsonObject read = guardedRead(28L, initial);
        JsonObject reader = summary("R", "R#a2", "TASK.R", scope,
                boundary(VmExpressionIr.FIELD_READ, 28L, read));
        addGuardedReadEvidence(reader, read, absentInstaller);
        reader.getAsJsonObject(SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .getAsJsonObject("envelope").getAsJsonArray("versions")
                .get(0).getAsJsonObject().addProperty("versionKind",
                        "INITIAL");

        // The installer task is intentionally absent: its INITIAL snapshot is
        // source evidence, and the propagated expression remains the value.
        SymbolicPropagationClosure.Result result = rewrite(
                Arrays.asList(reader));

        assertTrue(result.gaps().toString(), result.complete());
        JsonObject rewritten = firstExpressionOfType(result.summaries(),
                SharedStateEvidence.GUARDED_READ_TYPE);
        JsonObject candidate = rewritten.getAsJsonArray("candidates")
                .get(0).getAsJsonObject();
        assertTrue(string(candidate,
                SymbolicPropagationClosure.WRITER_CASE_OWNER).startsWith(
                SymbolicPropagationClosure.INITIAL_SOURCE_CASE_PREFIX));
        assertEquals("M_INITIAL",
                candidate.getAsJsonObject("expression").get("_exp")
                        .getAsString());
        JsonObject dependency = dependency(result, string(candidate,
                SymbolicPropagationClosure.WRITER_CASE_FAMILY));
        assertEquals(1, dependency.getAsJsonArray("arms").size());
        JsonObject dependencyArm = dependency.getAsJsonArray("arms").get(0)
                .getAsJsonObject();
        assertEquals(0, dependencyArm.getAsJsonArray("pathCondition")
                .size());
        assertEquals(scope, string(dependencyArm,
                SymbolicPropagationClosure.OBSERVATION_SCOPE));

        JsonObject replayedInitial = initial.deepCopy();
        JsonObject replayedRead = guardedRead(29L, replayedInitial);
        JsonObject replayedReader = summary("R", "R#a2", "TASK.R.2",
                "replay-group:initial-source-2",
                boundary(VmExpressionIr.FIELD_READ, 29L, replayedRead));
        addGuardedReadEvidence(replayedReader, replayedRead, absentInstaller);
        replayedReader.getAsJsonObject(SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .getAsJsonObject("envelope").getAsJsonArray("versions")
                .get(0).getAsJsonObject().addProperty("versionKind",
                        "INITIAL");
        SymbolicPropagationClosure.Result replayed = rewrite(
                Arrays.asList(replayedReader));
        assertTrue(replayed.gaps().toString(), replayed.complete());
        JsonObject replayedCandidate = firstExpressionOfType(
                replayed.summaries(), SharedStateEvidence.GUARDED_READ_TYPE)
                .getAsJsonArray("candidates").get(0).getAsJsonObject();
        assertEquals(string(candidate,
                        SymbolicPropagationClosure.WRITER_CASE_OWNER),
                string(replayedCandidate,
                        SymbolicPropagationClosure.WRITER_CASE_OWNER));
    }

    @Test
    public void missingProducerEvidenceFailsClosed() {
        JsonObject wrapped = boundary(VmExpressionIr.RPC_ATTACH, 701,
                symbol("M_missing"));
        JsonObject reader = summary("A", "A#a1", "TASK.A",
                "replay-group:missing", wrapped);
        handoff(reader, "FAMILY.MISSING", "A.in", 701,
                "TASK.NOT_PRESENT", "B#a1", wrapped);

        SymbolicPropagationClosure.Result result = rewrite(
                Arrays.asList(reader));

        assertFalse(result.complete());
        assertTrue(containsReason(result.gaps(),
                "CONSUMER_BOUNDARY_PRODUCER_CASE_MISSING"));
    }

    private static JsonObject summary(String region, String occurrence,
                                      String task, String scope,
                                      JsonElement condition) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("summaryId", "SUMMARY." + task);
        row.addProperty("relationKey", "REL." + region);
        row.addProperty("regionId", region);
        row.addProperty("sourceKey", "SOURCE." + region);
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("plannedOccurrenceId",
                edu.uva.liftlab.graphchecker.contract.PathObservation
                        .plannedOccurrenceOf(occurrence));
        row.addProperty("taskId", task);
        row.addProperty("sourceTaskId", task);
        row.addProperty("boundarySessionScope", scope);
        row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, EPOCH);
        row.addProperty("pathSetClosed", true);
        JsonArray pc = new JsonArray();
        pc.add(condition.deepCopy());
        row.add("pathCondition", pc);
        boolean outcome = !task.endsWith(".2") && !task.endsWith(".NEG");
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attested("SITE." + region,
                        "<fixture." + region + ": void run()>", 0, 1,
                        outcome),
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        row.add("branchMappings", mappings);
        row.addProperty(LocalCaseIdentity.FIELD,
                LocalCaseIdentity.compute(row));
        return row;
    }

    private static SymbolicPropagationClosure.Result rewrite(
            List<JsonObject> rows) {
        List<JsonObject> portable = new ArrayList<>();
        for (JsonObject row : rows) {
            row.remove(LocalCaseIdentity.FIELD);
            row.addProperty(LocalCaseIdentity.FIELD,
                    LocalCaseIdentity.compute(row));
            portable.add(SharedExpressionTable.compact(row));
        }
        return SymbolicPropagationClosure.rewriteSummaryRows(portable);
    }

    private static void handoff(JsonObject receiver, String family,
                                String port, long attachEvent,
                                String producerTask,
                                String producerOccurrence,
                                JsonObject wrapper) {
        JsonObject event = VmHandoffEvidence.event(port, attachEvent - 1,
                attachEvent, wrapper, producerTask, producerOccurrence);
        event = VmHandoffEvidence.withBoundaryFamily(event, family, EPOCH, 1);
        event.addProperty("boundarySessionScope",
                receiver.get("boundarySessionScope").getAsString());
        JsonArray events = receiver.has(VmHandoffEvidence.FIELD)
                ? receiver.getAsJsonArray(VmHandoffEvidence.FIELD)
                : new JsonArray();
        events.add(event);
        receiver.add(VmHandoffEvidence.FIELD, events);
    }

    private static JsonObject candidate(String selector, long version,
                                        JsonElement expression,
                                        JsonObject writer, int ordinal) {
        String owner = LocalCaseIdentity.owner(writer);
        JsonObject result = new JsonObject();
        result.addProperty("selector", selector);
        result.addProperty("fieldVersionId", version);
        result.addProperty("versionKind", "WRITE");
        result.addProperty("writerContextId", ordinal);
        result.addProperty("regionEnterEventId", ordinal + 500L);
        result.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                string(writer, "sourceKey"));
        result.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                string(writer, "occurrenceId"));
        result.add("expression", expression.deepCopy());
        result.add("pathGuard", SharedStateEvidence.emptyConjunction());
        result.addProperty(SymbolicPropagationClosure.WRITER_CASE_OWNER,
                owner);
        result.addProperty(SymbolicPropagationClosure.WRITER_CASE_SELECTOR,
                LocalCaseIdentity.selector(owner));
        return result;
    }

    private static JsonObject guardedRead(long event,
                                          JsonObject... candidates) {
        JsonObject read = new JsonObject();
        read.addProperty("_type", SharedStateEvidence.GUARDED_READ_TYPE);
        read.addProperty("_java_type", "I");
        read.addProperty("readEventId", event);
        read.addProperty("expressionAuthority",
                SharedStateEvidence.GUARDED_READ_AUTHORITY);
        read.addProperty("writerSetComplete", true);
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 17L);
        location.addProperty("slot", 8);
        read.add("location", location);
        JsonArray arms = new JsonArray();
        JsonArray selectors = new JsonArray();
        for (JsonObject candidate : candidates) {
            arms.add(candidate);
            selectors.add(string(candidate, "selector"));
        }
        read.add("candidates", arms);
        read.add("exactlyOne", selectors);
        return read;
    }

    private static void addGuardedReadEvidence(JsonObject reader,
                                               JsonObject read,
                                               JsonObject... writers) {
        JsonArray versions = new JsonArray();
        long enter = 500L;
        for (int index = 0; index < writers.length; index++) {
            JsonObject writer = writers[index];
            JsonObject candidate = read.getAsJsonArray("candidates")
                    .get(index).getAsJsonObject();
            JsonObject version = candidate.deepCopy();
            version.addProperty("versionKind", "WRITE");
            version.addProperty("writerContextId", index + 1L);
            version.addProperty("regionEnterEventId", enter + index);
            version.addProperty("taskId", string(writer, "taskId"));
            version.addProperty("regionId", string(writer, "regionId"));
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    string(writer, "sourceKey"));
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    string(writer, "occurrenceId"));
            version.add(SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE,
                    activationClosure(writer));
            versions.add(version);
        }
        JsonObject observedRead = new JsonObject();
        observedRead.addProperty("readEventId",
                read.get("readEventId").getAsLong());
        observedRead.addProperty("readerContextId", 9L);
        observedRead.addProperty("regionEnterEventId", 509L);
        observedRead.addProperty("regionId", string(reader, "regionId"));
        observedRead.addProperty("taskId", string(reader, "taskId"));
        observedRead.addProperty(SharedStateEvidence.READER_SOURCE_KEY,
                string(reader, "sourceKey"));
        observedRead.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                string(reader, "occurrenceId"));
        observedRead.addProperty(SharedStateEvidence.CONSUMER_SITE_ID,
                "example.Reader#u11");
        observedRead.addProperty(
                SharedStateEvidence.CONSUMER_SITE_OCCURRENCE, 1);
        observedRead.addProperty("candidateCount",
                read.getAsJsonArray("candidates").size());
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("schemaVersion", SharedStateEvidence.SCHEMA_VERSION);
        envelope.addProperty("selected", true);
        envelope.add("location", read.get("location").deepCopy());
        envelope.addProperty("writerSetComplete",
                read.get("writerSetComplete").getAsBoolean());
        envelope.addProperty("serializationTruncated", false);
        JsonArray reads = new JsonArray();
        reads.add(observedRead);
        envelope.add("reads", reads);
        envelope.addProperty("readLogTruncated", false);
        envelope.add("versions", versions);

        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "INSTANCE_FIELD");
        carrier.addProperty("declaringClass", "example.State");
        carrier.addProperty("fieldName", "value");
        carrier.addProperty("descriptor", "I");
        carrier.addProperty("receiverObjectId", 0L);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", "INSTANCE_FIELD/17#8");
        record.add("carrier", carrier);
        record.add("envelope", envelope);
        JsonArray records = new JsonArray();
        records.add(record);
        JsonObject state = new JsonObject();
        state.add("versions", records);
        reader.add(SharedStateEvidence.RECORDED_FIELD, state);
    }

    private static JsonObject activationClosure(JsonObject... cases) {
        JsonObject closure = new JsonObject();
        closure.addProperty("authority", SymbolicPropagationClosure
                .WRITER_ACTIVATION_CLOSURE_AUTHORITY);
        closure.addProperty("complete", true);
        JsonArray encoded = new JsonArray();
        for (JsonObject localCase : cases) {
            JsonObject address = new JsonObject();
            address.addProperty("taskId", string(localCase, "taskId"));
            address.addProperty("regionId", string(localCase, "regionId"));
            address.addProperty("occurrenceId",
                    string(localCase, "occurrenceId"));
            encoded.add(address);
        }
        closure.add("cases", encoded);
        return closure;
    }

    private static JsonObject firstExpressionOfType(
            JsonElement value, String type) {
        if (value == null || value.isJsonNull()
                || value.isJsonPrimitive()) return new JsonObject();
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                JsonObject found = firstExpressionOfType(child, type);
                if (found.size() > 0) return found;
            }
            return new JsonObject();
        }
        JsonObject object = value.getAsJsonObject();
        if (type.equals(string(object, "_type"))) return object;
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            JsonObject found = firstExpressionOfType(field.getValue(), type);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject firstExpressionOfType(
            List<JsonObject> rows, String type) {
        for (JsonObject row : rows) {
            JsonObject found = firstExpressionOfType(row, type);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject boundary(String kind, long event,
                                       JsonElement payload) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", VmExpressionIr.CONSUMER_BOUNDARY_TYPE);
        result.addProperty(VmExpressionIr.BOUNDARY_KIND, kind);
        result.addProperty(VmExpressionIr.EVENT_ID, event);
        result.addProperty("_java_type", "I");
        result.add(VmExpressionIr.EXPRESSION, payload.deepCopy());
        return result;
    }

    private static JsonObject symbol(String name) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", name);
        return result;
    }

    private static JsonObject constant(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "C_I_" + value);
        return result;
    }

    private static JsonObject containerRelation(String operation,
                                                JsonElement receiver) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", ContainerSmtCodec.EXPRESSION_TYPE);
        result.addProperty("_java_type", "L");
        result.addProperty("shape", "ASSOCIATIVE");
        result.addProperty("operation", operation);
        result.add("receiver", receiver.deepCopy());
        result.add("arguments", new JsonArray());
        return result;
    }

    private static JsonObject add(JsonElement left, JsonElement right) {
        JsonObject result = binary(left, right);
        result.addProperty("_op", "+");
        return result;
    }

    private static JsonObject binary(JsonElement left, JsonElement right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_op", "==");
        result.add("_left", left.deepCopy());
        result.add("_right", right.deepCopy());
        return result;
    }

    private static Set<String> dependencySelectors(
            SymbolicPropagationClosure.Result result) {
        Set<String> selectors = new LinkedHashSet<>();
        for (JsonElement encoded : result.caseDependencies()) {
            for (JsonElement arm : encoded.getAsJsonObject()
                    .getAsJsonArray("arms")) {
                selectors.add(arm.getAsJsonObject().get("selector")
                        .getAsString());
            }
        }
        return selectors;
    }

    private static JsonObject dependency(
            SymbolicPropagationClosure.Result result, String family) {
        for (JsonElement encoded : result.caseDependencies()) {
            JsonObject row = encoded.getAsJsonObject();
            if (family.equals(string(row, VmExpressionIr.FAMILY_KEY))) {
                return row;
            }
        }
        return new JsonObject();
    }

    private static JsonObject merge(
            SymbolicPropagationClosure.Result result, String family) {
        for (JsonObject summary : result.summaries()) {
            JsonObject found = firstMergeForFamily(summary, family);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject firstMergeForFamily(JsonElement value,
                                                   String family) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return new JsonObject();
        }
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                JsonObject found = firstMergeForFamily(child, family);
                if (found.size() > 0) return found;
            }
            return new JsonObject();
        }
        JsonObject object = value.getAsJsonObject();
        if (SymbolicPropagationClosure.ITE_TYPE.equals(
                string(object, "_type"))
                && family.equals(string(object,
                VmExpressionIr.FAMILY_KEY))) {
            return object;
        }
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            JsonObject found = firstMergeForFamily(field.getValue(), family);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static Set<String> mergeIds(List<JsonObject> summaries) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject summary : summaries) collectMergeIds(summary, result);
        return result;
    }

    private static void collectMergeIds(JsonElement value,
                                        Set<String> result) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                collectMergeIds(child, result);
            }
        } else if (value.isJsonObject()) {
            JsonObject object = value.getAsJsonObject();
            if (SymbolicPropagationClosure.ITE_TYPE.equals(
                    string(object, "_type"))) {
                result.add(string(object, "mergeId"));
            }
            for (Map.Entry<String, JsonElement> field : object.entrySet()) {
                collectMergeIds(field.getValue(), result);
            }
        }
    }

    private static boolean containsType(JsonElement value, String type) {
        Set<String> ids = new LinkedHashSet<>();
        collectMergeIds(value, ids);
        return !ids.isEmpty()
                && SymbolicPropagationClosure.ITE_TYPE.equals(type);
    }

    private static boolean containsReason(JsonArray rows, String reason) {
        for (JsonElement encoded : rows) {
            JsonObject row = encoded.getAsJsonObject();
            if (reason.equals(string(row, "reason"))) return true;
        }
        return false;
    }
}
