package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
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

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicSmtComposerTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void canonicalCoverageKeepsStableCodeAndPerQueryIdentity() {
        JsonObject manifest = new JsonObject();
        JsonArray coverage = new JsonArray();
        String detail = "REGION_TARGET_EVENT_NOT_REACHED: free text";
        coverage.add(CoverageDivergence.of(CoverageDivergence.Kind.TARGET,
                "PATH_FLIP_REPLAY_NOT_ADMITTED", "QUERY.A", detail));
        coverage.add(CoverageDivergence.of(CoverageDivergence.Kind.TARGET,
                "PATH_FLIP_REPLAY_NOT_ADMITTED", "QUERY.B", detail));
        manifest.add("coverageGaps", coverage);
        manifest.add("recordedValueBindings", new JsonArray());
        manifest.add("recordedSessionModel", new JsonObject());

        JsonObject canonical = CanonicalSessionModel.of(manifest,
                new JsonArray(), new JsonArray(), "REGION.target",
                "SOURCE/region/target#1");

        JsonArray gaps = canonical.getAsJsonArray("gaps");
        Set<String> subjects = new LinkedHashSet<>();
        int matching = 0;
        for (JsonElement element : gaps) {
            JsonObject gap = element.getAsJsonObject();
            if (!"COVERAGE".equals(gap.get("source").getAsString())) {
                continue;
            }
            matching++;
            assertEquals("PATH_FLIP_REPLAY_NOT_ADMITTED",
                    gap.get("code").getAsString());
            assertEquals(detail, gap.get("detail").getAsString());
            subjects.add(gap.get("subject").getAsString());
        }
        assertEquals(gaps.toString(), 2, matching);
        assertEquals(new LinkedHashSet<>(Arrays.asList("QUERY.A", "QUERY.B")),
                subjects);

        JsonObject summary = CoverageDivergence.summary(
                Arrays.asList(coverage.get(0).getAsJsonObject(),
                        coverage.get(1).getAsJsonObject()), true);
        assertEquals(2, summary.getAsJsonObject("classes")
                .get("TARGET").getAsInt());
        assertEquals(0, summary.get("unclassifiedCount").getAsInt());

        JsonObject unknown = new JsonObject();
        unknown.addProperty("kind", "FUTURE_COVERAGE_GAP");
        JsonObject unclassified = CoverageDivergence.summary(
                Collections.singletonList(unknown), true);
        assertEquals(0, unclassified.get("divergenceCount").getAsInt());
        assertEquals(1, unclassified.get("unclassifiedCount").getAsInt());
        assertEquals(CoverageDivergence.PARTIAL,
                unclassified.get("coverageState").getAsString());
        assertTrue(unclassified.get("retainedPartialRelation")
                .getAsBoolean());
    }

    @Test
    public void canonicalModelRetainsEveryCaseScopedSharedBinding() {
        JsonObject manifest = new JsonObject();
        JsonArray bindings = new JsonArray();
        for (int index = 0; index < 2; index++) {
            JsonObject exact = new JsonObject();
            exact.addProperty("kind", "RECORDED_EXACT_VALUE_BINDING");
            exact.addProperty("edgeId", "EDGE.EXACT.COLLISION");
            exact.addProperty("fromOccurrenceId",
                    "SOURCE/region/producer#1");
            exact.addProperty("toOccurrenceId",
                    "SOURCE/region/target#1");
            exact.addProperty("fromOutputPort", "P.out");
            exact.addProperty("toInputPort", "T.in");
            exact.addProperty("readEventId", 101L + index);
            exact.addProperty("fieldVersionId", 201L + index);
            exact.addProperty("caseGuard", "case_" + index);
            exact.addProperty("valueAssertion", "exact_" + index);
            bindings.add(exact);

            JsonObject guarded = new JsonObject();
            guarded.addProperty("kind",
                    "RECORDED_GUARDED_READ_PORT_BINDING");
            guarded.addProperty("edgeId", "EDGE.GUARDED.COLLISION");
            guarded.addProperty("toOccurrenceId",
                    "SOURCE/region/target#1");
            guarded.addProperty("toInputPort", "T.map");
            guarded.addProperty("readEventId", 301L + index);
            guarded.addProperty("caseGuard", "case_" + index);
            guarded.addProperty("valueAssertion", "guarded_" + index);
            bindings.add(guarded);
        }
        manifest.add("recordedValueBindings", bindings);
        manifest.add("recordedSessionModel", new JsonObject());

        JsonObject canonical = CanonicalSessionModel.of(manifest,
                new JsonArray(), new JsonArray(), "REGION.target",
                "SOURCE/region/target#1");
        JsonArray retained = canonical.getAsJsonArray("valueBindings");
        assertEquals(canonical.toString(), 4, retained.size());
        Set<String> keys = new LinkedHashSet<>();
        for (JsonElement element : retained) {
            keys.add(element.getAsJsonObject().get("bindingKey")
                    .getAsString());
        }
        assertEquals(canonical.toString(), 4, keys.size());
    }

    @Test
    public void caseLocalLetCseSharesOneClosedLargeTermDeterministically() {
        String shared = largeSmtTerm("global_value");
        String expression = "(and (= " + shared + " " + shared + ")"
                + " (= " + shared + " " + shared + "))";

        String compressed = ConcolicSmtComposer
                .caseLocalLetCseForTests(expression);

        assertTrue(compressed, compressed.startsWith(
                "(let ((gc_case_cse__"));
        assertEquals(compressed, 1, occurrences(compressed, shared));
        assertEquals(compressed, compressed, ConcolicSmtComposer
                .caseLocalLetCseForTests(expression));
        assertTrue(compressed.length() < expression.length() / 2);
    }

    @Test
    public void caseLocalLetCseDoesNotHoistAnAncestorBoundIdentifier() {
        String scoped = largeBoundSmtTerm("s");
        String equality = "(= " + scoped + " " + scoped + ")";
        String expression = "(and (let ((s left)) " + equality + ")"
                + " (let ((s right)) " + equality + ") )";

        assertEquals(expression, expression, ConcolicSmtComposer
                .caseLocalLetCseForTests(expression));
    }

    @Test
    public void caseLocalLetCseMayShareAClosedTermBelowDifferentLets() {
        String shared = largeSmtTerm("global_value");
        String equality = "(= " + shared + " " + shared + ")";
        String expression = "(and (let ((s left)) " + equality + ")"
                + " (let ((s right)) " + equality + ") )";

        String compressed = ConcolicSmtComposer
                .caseLocalLetCseForTests(expression);

        assertTrue(compressed, compressed.startsWith(
                "(let ((gc_case_cse__"));
        assertEquals(compressed, 1, occurrences(compressed, shared));
    }

    @Test
    public void caseLocalLetCseLeavesSmallTermsAndQuotedParensAlone() {
        String small = "(and (= (f x) (f x))"
                + " (= (str.++ \"(\" \")\") \"()\"))";

        assertEquals(small, small, ConcolicSmtComposer
                .caseLocalLetCseForTests(small));
    }

    @Test
    public void caseLocalLetCseStaysBoundedOnAMegabyteAssertion() {
        String shared = largeSmtTerm("global_value");
        StringBuilder expression = new StringBuilder("(and");
        for (int index = 0; index < 300; index++) {
            expression.append(" (= ").append(shared).append(" unit)");
        }
        expression.append(')');
        assertTrue(expression.length() > 1_000_000);

        long started = System.nanoTime();
        String compressed = ConcolicSmtComposer
                .caseLocalLetCseForTests(expression.toString());
        long elapsedMillis = (System.nanoTime() - started) / 1_000_000L;

        assertTrue("CSE took " + elapsedMillis + "ms",
                elapsedMillis < 10_000L);
        assertTrue(compressed.length() < expression.length() / 10);
    }

    @Test
    public void targetScopeExcludesTheWorkloadCatalogWhenRelationsAreEmpty() {
        String targetOccurrence = "cluster/dn#epoch1/region/REGION.0#38";
        String producerOccurrence = "cluster/driver#epoch0/region/REGION.1#3";
        JsonObject target = occurrencePlan("REGION.0", targetOccurrence);
        JsonObject producer = occurrencePlan("REGION.1", producerOccurrence);
        JsonObject unrelated = occurrencePlan("REGION.2",
                "cluster/other#epoch0/region/REGION.2#9");

        JsonObject fatal = new JsonObject();
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", targetOccurrence);
        // The target query may embed session evidence from many occurrences.
        // It is evidence for the target formula, not authority to re-admit an
        // unrelated runtime-plan occurrence into this composition.
        JsonObject embeddedEvidence = new JsonObject();
        embeddedEvidence.add("unrelated", unrelated.deepCopy());
        fatal.add("recordedSharedState", embeddedEvidence);

        List<JsonObject> scoped = ConcolicSmtComposer.targetScopedPlanRows(
                Arrays.asList(unrelated, producer, target), fatal,
                Collections.<JsonObject>emptyList(),
                Collections.<RelationSummary>emptyList());

        List<String> occurrences = new ArrayList<>();
        for (JsonObject row : scoped) {
            occurrences.add(row.get("occurrenceId").getAsString());
        }
        assertEquals(occurrences.toString(), 1, occurrences.size());
        assertTrue(occurrences.contains(targetOccurrence));
    }

    @Test
    public void configuredSourceInSuppliedButUnloweredSummaryIsGlobal()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target";
        String sourceOccurrence = "REGION.1@Test#source";
        String sourceId = "TEST.CONFIGURED.SOURCE";
        String sourcePhase = publishPhase(sourceOccurrence);
        String raw = configuredRaw(sourcePhase, sourceId, "configured");
        RelationSummary source = summary("SOURCE", sourceOccurrence, 7,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject sourceRow = source.toJson();
        JsonObject sourceCase = sourceRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        SymbolicSourceEvidence.writeTo(sourceCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        sourcePhase, sourceId, sourceOccurrence,
                        "<Test: int source>", reference(raw, "I"))));

        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference(raw, "I"), "==", integer(7)));
        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(RelationSummary.decode(sourceRow)),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)),
                fatalQuery(fatalOccurrence, constraints), null);

        assertEquals(result.smtLib, 1, occurrences(result.smtLib,
                "(declare-const source__"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(declare-const sym__fatal_"));
        JsonArray roots = result.manifest.getAsJsonArray(
                ConcolicSmtComposer
                        .CONFIGURED_SOURCE_MATERIALIZATION_FIELD);
        assertEquals(roots.toString(), 1, roots.size());
        JsonObject root = roots.get(0).getAsJsonObject();
        assertEquals("TEST_DRIVER/test#epoch0",
                root.get("sourceKey").getAsString());
        assertEquals(sourceId,
                root.get("sourceId").getAsString());
        assertEquals(sourcePhase,
                root.get("sourcePhaseId").getAsString());
        assertEquals(sourceOccurrence,
                root.get("sourceOccurrenceId").getAsString());
        assertEquals("<Test: int source>",
                root.get("fieldSignature").getAsString());
        assertEquals("I", root.get("javaTypeDescriptor").getAsString());
        assertEquals("INT", root.get("sort").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const " + root.get("solverTerm").getAsString()
                        + " Int)"));
        JsonObject fatalAssertion = result.manifest.getAsJsonObject(
                "fatalPathAssertion");
        assertEquals("fatal_path", fatalAssertion.get("name").getAsString());
        assertFalse(fatalAssertion.get("solverTerm").getAsString().isEmpty());
        assertFalse(result.manifest.has("operandBindingLedger"));
        JsonObject canonical = result.manifest.getAsJsonObject(
                CanonicalSessionModel.MANIFEST_FIELD);
        assertEquals(fatalAssertion,
                canonical.getAsJsonObject("target")
                        .getAsJsonObject("fatalPathAssertion"));
        JsonObject graph = CausalGraphWriter.graph(canonical,
                new JsonObject());
        assertEquals(fatalAssertion,
                graph.getAsJsonObject("target")
                        .getAsJsonObject("fatalPathAssertion"));
    }

    @Test
    public void configuredSelectorForcesExactProducerCaseAndSelectedInt()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-selector";
        String consumerOccurrence = "REGION.1@Test#consumer-selector";
        String sourceOccurrence = "REGION.1@Test#source-selector";
        String sourceId = "TEST.SELECTOR.KEY";
        String field = "<Test: int keyId>";
        String producerPhaseId = publishPhase(sourceOccurrence);
        String raw = ConfiguredSourceSelectorContract
                .expectedRawSymbolPrefix(producerPhaseId, sourceId, field)
                + "Test";
        JsonObject firstHop = protocolBinding("EDGE.SELECTOR",
                consumerOccurrence, "REGION.1.out.0", fatalOccurrence,
                "REGION.0.in.0");

        RelationSummary producer = configuredSourceProducer(
                sourceOccurrence, sourceId, field, raw);
        RelationSummary consumer = summary("SELECTOR.CONSUMER",
                consumerOccurrence, 1,
                Collections.<String>emptyList(),
                Collections.singletonList(firstHop));
        JsonObject consumerRow = consumer.toJson();
        JsonObject consumerCase = consumerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        writeConfiguredSelector(consumerCase, sourceOccurrence, sourceId,
                field, "TASK.SOURCE.9", raw, 9);

        ConcolicSmtComposer.Result result = compose(fatalOccurrence,
                Arrays.asList(RelationSummary.decode(consumerRow), producer),
                firstHop);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonArray ledger = result.manifest.getAsJsonArray(
                ConfiguredSourceSelectorContract.EVIDENCE_FIELD);
        assertEquals(ledger.toString(), 1, ledger.size());
        JsonObject selected = ledger.get(0).getAsJsonObject();
        assertEquals("TASK.SOURCE.9",
                selected.get("sourceTaskId").getAsString());
        assertEquals(9, selected.get("selectedIntValue").getAsInt());
        assertEquals(producerPhaseId,
                selected.get("producerPhaseId").getAsString());
        assertEquals(consumePhase(sourceOccurrence),
                selected.get("consumePhaseId").getAsString());
        String consumerOwner = RecordedSessionModel.caseOwner("REGION.1",
                consumerOccurrence, "CASE.SELECTOR.CONSUMER", 0);
        String consumerSelector = RecordedSessionModel.caseSelector(
                consumerOwner);
        String producerOwner = RecordedSessionModel.caseOwner("REGION.1",
                sourceOccurrence, "CASE.SOURCE.9", 1);
        String producerSelector = RecordedSessionModel.caseSelector(
                producerOwner);
        String valueAssertion = selected.get("valueAssertion").getAsString();
        assertTrue(valueAssertion, valueAssertion.startsWith(
                "configured_source_selector_"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> " + consumerSelector + " (and "
                        + producerSelector));
        assertTrue(result.smtLib, result.smtLib.contains(" 9)"));
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
            assertEquals(result.smtLib, "unsat", z3(assuming(result.smtLib,
                    "(not " + producerSelector + ")")));
        }
    }

    @Test
    public void configuredSelectorBindsOnlyNamedPublishPhase()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-phase-selector";
        String consumerOccurrence =
                "REGION.1@Test#consumer-phase-selector";
        String sourceOccurrence = "REGION.1@Test#source-phase-selector";
        String sourceId = "TEST.SELECTOR.PHASED.KEY";
        String field = "<Test: int keyId>";
        String firstPhase = publishPhase(sourceOccurrence);
        String secondPhase = firstPhase + ".SECOND";
        String firstRaw = configuredRaw(firstPhase, sourceId, "first");
        String secondRaw = configuredRaw(secondPhase, sourceId, "second");
        JsonObject firstHop = protocolBinding("EDGE.SELECTOR.PHASED",
                consumerOccurrence, "REGION.1.out.0", fatalOccurrence,
                "REGION.0.in.0");

        JsonObject producerRow = configuredSourceProducer(sourceOccurrence,
                sourceId, field, firstRaw).toJson();
        JsonObject selectedProducerCase = producerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(1)
                .getAsJsonObject();
        JsonArray sourceEvents = selectedProducerCase.getAsJsonArray(
                SymbolicSourceEvidence.FIELD);
        sourceEvents.add(SymbolicSourceEvidence.event(secondPhase, sourceId,
                sourceOccurrence, field, reference(secondRaw, "I")));
        RelationSummary consumer = summary("SELECTOR.PHASE.CONSUMER",
                consumerOccurrence, 1, Collections.<String>emptyList(),
                Collections.singletonList(firstHop));
        JsonObject consumerRow = consumer.toJson();
        writeConfiguredSelector(consumerRow.getAsJsonObject(
                        "regionRelation").getAsJsonArray("cases").get(0)
                        .getAsJsonObject(), sourceOccurrence, sourceId,
                field, "TASK.SOURCE.9", secondRaw, 11,
                consumePhase(consumerOccurrence), secondPhase);

        ConcolicSmtComposer.Result result = compose(fatalOccurrence,
                Arrays.asList(RelationSummary.decode(consumerRow),
                        RelationSummary.decode(producerRow)), firstHop);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonObject selected = result.manifest.getAsJsonArray(
                ConfiguredSourceSelectorContract.EVIDENCE_FIELD)
                .get(0).getAsJsonObject();
        assertEquals(secondPhase,
                selected.get("producerPhaseId").getAsString());
        assertEquals(secondRaw, selected.get("rawSymbol").getAsString());
    }

    @Test
    public void configuredSelectorMissingAmbiguousAndMismatchFailClosed()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-selector-gaps";
        String consumerOccurrence = "REGION.1@Test#consumer-selector-gaps";
        String sourceOccurrence = "REGION.1@Test#source-selector-gaps";
        String sourceId = "TEST.SELECTOR.KEY";
        String field = "<Test: int keyId>";
        String producerPhaseId = publishPhase(sourceOccurrence);
        String raw = ConfiguredSourceSelectorContract
                .expectedRawSymbolPrefix(producerPhaseId, sourceId, field)
                + "Test";
        JsonObject firstHop = protocolBinding("EDGE.SELECTOR.GAPS",
                consumerOccurrence, "REGION.1.out.0", fatalOccurrence,
                "REGION.0.in.0");
        RelationSummary producer = configuredSourceProducer(
                sourceOccurrence, sourceId, field, raw);

        ConcolicSmtComposer.Result missing = composeSelectorFailure(
                fatalOccurrence, consumerOccurrence, sourceOccurrence,
                sourceId, field, raw, "TASK.MISSING", producer, firstHop);
        assertSelectorRefused(missing,
                ConcolicSmtComposer.SOURCE_SELECTOR_PRODUCER_CASE_MISSING);

        JsonObject ambiguousRow = producer.toJson();
        JsonArray producerCases = ambiguousRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases");
        JsonObject duplicate = producerCases.get(1).getAsJsonObject()
                .deepCopy();
        duplicate.addProperty("caseId", "CASE.SOURCE.9.DUPLICATE");
        producerCases.add(duplicate);
        ConcolicSmtComposer.Result ambiguous = composeSelectorFailure(
                fatalOccurrence, consumerOccurrence, sourceOccurrence,
                sourceId, field, raw, "TASK.SOURCE.9",
                RelationSummary.decode(ambiguousRow), firstHop);
        assertSelectorRefused(ambiguous,
                ConcolicSmtComposer
                        .SOURCE_SELECTOR_PRODUCER_CASE_AMBIGUOUS);

        JsonObject mismatchedProducer = producer.toJson();
        JsonObject sourceNine = mismatchedProducer.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(1)
                .getAsJsonObject();
        sourceNine.getAsJsonArray(SymbolicSourceEvidence.FIELD).get(0)
                .getAsJsonObject().addProperty("fieldSignature",
                        "<Test: int anotherKey>");
        ConcolicSmtComposer.Result mismatch = composeSelectorFailure(
                fatalOccurrence, consumerOccurrence, sourceOccurrence,
                sourceId, field, raw, "TASK.SOURCE.9",
                RelationSummary.decode(mismatchedProducer), firstHop);
        assertSelectorRefused(mismatch,
                ConcolicSmtComposer
                        .SOURCE_SELECTOR_PRODUCER_EVIDENCE_MISMATCH);
    }

    @Test
    public void configuredSelectorOnTargetIsGuardedByThatTargetPath()
            throws Exception {
        String fatalOccurrence = "REGION.0@Test#target-selector-path";
        String sourceOccurrence = "REGION.1@Test#source-selector-path";
        String sourceId = "TEST.TARGET.SELECTOR.KEY";
        String field = "<Test: int keyId>";
        String producerPhaseId = publishPhase(sourceOccurrence);
        String raw = ConfiguredSourceSelectorContract
                .expectedRawSymbolPrefix(producerPhaseId, sourceId, field)
                + "Test";
        RelationSummary producer = configuredSourceProducer(
                sourceOccurrence, sourceId, field, raw);
        JsonObject fatal = fatalQuery(fatalOccurrence,
                targetConstraints());
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        writeConfiguredSelector(targetPath, sourceOccurrence, sourceId,
                field, "TASK.SOURCE.9", raw, 9);

        ConcolicSmtComposer.Result result = composeFatal(fatalOccurrence,
                Collections.singletonList(producer),
                Arrays.asList(region("REGION.0", false, false),
                        region("REGION.1", false, true)), fatal, null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonObject selected = result.manifest.getAsJsonArray(
                ConfiguredSourceSelectorContract.EVIDENCE_FIELD)
                .get(0).getAsJsonObject();
        String targetOwner = RecordedSessionModel.caseOwner("REGION.0",
                fatalOccurrence, "TARGET_PATH.0", 0);
        String targetSelector = RecordedSessionModel.caseSelector(
                targetOwner);
        String producerOwner = RecordedSessionModel.caseOwner("REGION.1",
                sourceOccurrence, "CASE.SOURCE.9", 1);
        String producerSelector = RecordedSessionModel.caseSelector(
                producerOwner);
        assertEquals(targetOwner,
                selected.get("consumerCaseOwner").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> " + targetSelector + " (and "
                        + producerSelector));
    }

    @Test
    public void missingCaseLocalTargetEventIsRejectedByCanonicalSchema()
            throws Exception {
        String occurrence = "REGION.0@Test#target";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        fatal.getAsJsonArray("paths").get(0).getAsJsonObject()
                .remove(PathObservation.TargetReachEvent.FIELD);

        try {
            composeFatal(occurrence,
                    Collections.<RelationSummary>emptyList(),
                    Arrays.asList(region("REGION.0", true, false)),
                    fatal, null);
            fail("a target path without its event must be malformed");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "attestation authority"));
        }
    }

    @Test
    public void directlyWitnessedRequiredTargetOutcomeIsAdmitted()
            throws Exception {
        String occurrence = "REGION.0@Test#target";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject path = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder
                        .REQUIRED_FATAL_BRANCH_AUTHORITY);
        path.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal, null);

        assertEquals(ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        JsonObject attestation = result.manifest.getAsJsonArray(
                "targetReachLedger").get(0).getAsJsonObject();
        assertEquals(TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT,
                attestation.get("attestationRole").getAsString());
        assertFalse(attestation.get("outcome").getAsBoolean());
        assertFalse(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void targetPredicateMustEqualTheReplayRequiredPredicate()
            throws Exception {
        String occurrence = "REGION.0@Test#predicate-mismatch";
        JsonObject fatal = fatalQuery(occurrence, targetConstraints());
        JsonObject path = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        JsonArray mismatched = new JsonArray();
        mismatched.add(binary(reference("M_I_field_OTHER_GATE", "I"),
                ">", integer(0)));
        path.add("constraints", mismatched);

        ConcolicSmtComposer.Result result = composeFatal(occurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal,
                null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("SelectedTargetPredicateMismatch:path:0"));
    }

    @Test
    public void recordedSharedStateBecomesOneOrderDomainAndAReadCut()
            throws Exception {
        // Recorded writes, reads and ledger events reach the formula as one
        // order domain, rather than as one integer domain per channel.
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject outerToFatal = binding("EDGE.SHARED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        outerToFatal.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        outerToFatal.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        outerToFatal.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        RelationSummary outer = withRecordedSharedState(
                summary("OUTER", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(outerToFatal)));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(outer), outerToFatal);

        assertEquals(1, result.manifest.getAsJsonArray(
                "targetReachLedger").size());
        JsonObject targetAttestation = result.manifest.getAsJsonArray(
                "targetReachLedger").get(0).getAsJsonObject();
        assertTrue(targetAttestation.get("outcome").getAsBoolean());
        assertTrue(targetAttestation.get(
                "sourceObservedOutcome").getAsBoolean());
        assertFalse(targetAttestation.get(
                "desiredTakenOutcome").getAsBoolean());
        assertEquals("SOURCE_TARGET_REACH_EVENT",
                targetAttestation.get("attestationRole").getAsString());
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named target_reach_event"));
        // One position per recorded event, in one domain.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__11 Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__12 Int)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const event_position__21 Int)"));
        // Two writes related by a recorded cross-thread order stay ordered in
        // the projected slice.
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_order__11__12"));
        // The guarded read becomes an exactly-one choice plus a sparse cut.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const rf_selector__21__rf1 Bool)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(declare-const rf_selector__21__rf_unknown Bool)"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_cut__21__11"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_cut_outside__21__11__12"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_choice__21"));
        // The same selectors decide the value and the writer's path guard,
        // so the choice is one family rather than an order model beside a
        // value model.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> rf_selector__21__rf1 (= rf_value__21"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_value__21__rf_unknown"));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> rf_selector__21__rf2 (> "));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_write_guard__21__rf2"));
        // The VM serializes the same choice as a nested ite chain over those
        // selectors, and the emitter lowers that too rather than building the
        // formula from half of an admitted node.
        assertTrue(result.smtLib, result.smtLib.contains(
                "(ite rf_selector__21__rf1 "));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(ite rf_selector__21__rf2 "));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_read_term__21"));

        // Every value binding points back to the evidence it came from, in
        // members a reader can check rather than in prose.
        JsonArray bindings = result.manifest.getAsJsonArray(
                "recordedValueBindings");
        assertEquals(bindings.toString(), 4, bindings.size());
        JsonObject firstArm = bindings.get(0).getAsJsonObject();
        assertEquals("rf_selector__21__rf1",
                firstArm.get("selector").getAsString());
        assertEquals(21L, firstArm.get("readEventId").getAsLong());
        assertEquals(11L, firstArm.get("fieldVersionId").getAsLong());
        assertEquals("INSTANCE_FIELD/7#24",
                firstArm.get("locationKey").getAsString());
        assertEquals("recorded_read_value__21__rf1",
                firstArm.get("valueAssertion").getAsString());
        assertTrue(firstArm.toString(),
                firstArm.get("writerExists").getAsBoolean());
        assertEquals("recorded_write_guard__21__rf2",
                bindings.get(1).getAsJsonObject()
                        .get("writerGuardAssertion").getAsString());
        assertFalse(bindings.get(2).toString(), bindings.get(2)
                .getAsJsonObject().get("writerExists").getAsBoolean());
        // An unknown arm makes the model an under-approximation, and the
        // closure member says that as the fact it is.
        assertFalse(result.manifest.toString(), result.manifest
                .get("recordedModelComplete").getAsBoolean());

        JsonObject recorded = result.manifest.getAsJsonObject(
                "recordedSessionModel");
        assertTrue(recorded.toString(),
                recorded.get("partial").getAsBoolean());
        assertEquals(RecordedSessionModel.KIND,
                recorded.get("kind").getAsString());
        assertEquals(3, recorded.get("orderedEvents").getAsInt());
        assertEquals(1, recorded.get("orderConstraints").getAsInt());
        assertEquals(1, recorded.get("guardedReads").getAsInt());
        assertTrue(recorded.getAsJsonObject("targetSlice")
                .get("reachesTarget").getAsBoolean());
        // Coverage findings never disable the downstream reach stage.
        assertEquals(result.manifest.toString(), "CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        // README SMT-1 still refuses to call it final while this read keeps
        // its unknown arm: the query is emitted and solved, and it may not be
        // accepted as the milestone artifact.
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(
                        ConcolicSmtComposer.FINAL_STATUS).getAsString());
        assertTrue(result.manifest.toString(),
                result.manifest.getAsJsonArray("finalStatusRefusals")
                        .toString().contains(
                        ConcolicSmtComposer.SELECTED_READ_FROM_UNKNOWN_ARM));

        // Which arms replay could enforce is decided before the solve.
        JsonObject plan = recorded.getAsJsonArray("readCutGates").get(0)
                .getAsJsonObject();
        assertEquals(SparseReadCutGate.KIND, plan.get("kind").getAsString());
        assertTrue(plan.get("enforceable").getAsBoolean());
        assertEquals(2, plan.getAsJsonArray("gates").size());
        assertEquals(SparseReadCutGate.UNKNOWN_WRITER_SELECTED,
                plan.getAsJsonArray("refusals").get(0).getAsJsonObject()
                        .get("reason").getAsString());
        JsonObject choice = recorded.getAsJsonArray("readChoices").get(0)
                .getAsJsonObject();
        assertTrue(choice.getAsJsonArray("candidates").get(0)
                .getAsJsonObject().get("enforceable").getAsBoolean());
        assertFalse(choice.getAsJsonArray("candidates").get(2)
                .getAsJsonObject().get("enforceable").getAsBoolean());

        // The formula is emitted, and it says how complete it is.
        JsonObject divergence = result.manifest.getAsJsonObject(
                "divergence");
        assertEquals("PARTIAL",
                divergence.get("coverageState").getAsString());
        assertTrue(divergence.get("targetRelationUsable").getAsBoolean());
        assertTrue(divergence.get("retainedPartialRelation").getAsBoolean());
        assertEquals(1, divergence.getAsJsonObject("classes")
                .get("GATE").getAsInt());
    }

    @Test
    public void anAbsentRecordedSessionIsReportedNotAssumed()
            throws Exception {
        String fatalInstance = "REGION.0@Test#call30";
        String outerInstance = "REGION.1@Test#call20";
        JsonObject outerToFatal = binding("EDGE.SHARED", outerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 20, 30);
        RelationSummary outer = summary("OUTER", outerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(outerToFatal));

        JsonArray concreteTarget = new JsonArray();
        concreteTarget.add(binary(integer(1), ">", integer(0)));
        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Collections.singletonList(outer),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true)), concreteTarget,
                outerToFatal);

        JsonObject recorded = result.manifest.getAsJsonObject(
                "recordedSessionModel");
        assertEquals(0, recorded.get("orderedEvents").getAsInt());
        assertFalse(recorded.getAsJsonObject("targetSlice")
                .get("reachesTarget").getAsBoolean());
        // The absence is a named coverage finding, not a silent empty model.
        assertEquals(1,
                result.manifest.getAsJsonArray("coverageGaps").size());
        assertEquals(SessionTargetSlice.NO_RECORDED_TARGET_REFERENCE,
                result.manifest.getAsJsonArray("coverageGaps").get(0)
                        .getAsJsonObject().get("reason").getAsString());
        assertEquals("CANDIDATE_READY",
                result.manifest.get("state").getAsString());
        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("UnresolvedRecordedEdgeBinding:EDGE.SHARED"));
        assertFalse(result.smtLib,
                result.smtLib.contains("event_position__"));

        // Folded from aCrossChannelOrderCycleIsRefusedBeforeSolving: a ledger
        // whose delivered relation closes a cycle through a field read-from,
        // program order and two value-handoff edges is one relation and one
        // cycle, not four channels that happen to disagree.  It is refused
        // before the solve rather than reasoned over.
        JsonObject cyclicToFatal = outerToFatal.deepCopy();
        cyclicToFatal.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        RelationSummary cyclic = withRecordedSharedState(
                summary("CYCLE", outerInstance, 10,
                        Collections.singletonList("REGION.1.in.0"),
                        Collections.singletonList(cyclicToFatal)),
                crossChannelCycleLedger());

        ConcolicSmtComposer.Result refused = compose(fatalInstance,
                Collections.singletonList(cyclic), cyclicToFatal);

        JsonObject cyclicModel = refused.manifest.getAsJsonObject(
                "recordedSessionModel");
        assertTrue(cyclicModel.toString(), cyclicModel
                .get("orderDomainFault").getAsString().contains("cycle"));
        assertEquals(0, cyclicModel.get("orderedEvents").getAsInt());
        assertEquals("CANDIDATE_WITH_GAPS",
                refused.manifest.get("state").getAsString());
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains("RecordedOrderDomainCycle"));
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains(RecordedSessionModel.ORDER_DOMAIN_CYCLE));
        assertTrue(refused.smtLib, refused.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void vmHandoffBindsTheExactConsumerCaseExpression()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.VMH", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        RelationSummary consumer = summary("VMH", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Collections.singletonList(firstHop));
        JsonObject row = consumer.toJson();
        JsonObject path = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        JsonArray handoffs = new JsonArray();
        handoffs.add(VmHandoffEvidence.event("REGION.1.in.0", 41L,
                reference("producer_guard_x", "I"), "TASK.VMHP",
                producerInstance));
        path.add(VmHandoffEvidence.FIELD, handoffs);

        // This producer is deliberately not in the ordinary lowered edge
        // closure.  Its exact task/case can only be recovered from the v3
        // RPC-header provenance carried beside the VM handle.
        RelationSummary producer = summary("VMHP", producerInstance, 10,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject producerRow = producer.toJson();
        JsonObject producerPath = producerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases")
                .get(0).getAsJsonObject();
        producerPath.getAsJsonObject("guard")
                .getAsJsonArray("conditions").add(binary(
                        reference("producer_guard_x", "I"), ">",
                        integer(0)));
        JsonObject interaction = new JsonObject();
        interaction.addProperty("outputSiteId", "COMMUNICATION_EFFECT:test");
        interaction.addProperty("outputOccurrence", 1);
        interaction.addProperty("outputVersionOrdinal", 1);
        interaction.addProperty("replayOccurrence", 1);
        interaction.addProperty("interactionKind", "COMMUNICATION_EFFECT");
        interaction.addProperty("authority",
                "INSTRUMENTED_INTERACTION_SITE_V1");
        interaction.addProperty("portId", "REGION.1.in.0");
        JsonArray interactions = new JsonArray();
        interactions.add(interaction);
        producerPath.add(RelationSummary.INTERACTION_EVENTS, interactions);
        producer = RelationSummary.decode(producerRow);

        JsonArray ledgerEvents = new JsonArray();
        ledgerEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.sender"));
        ledgerEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.1"));
        JsonArray ledgerOrder = new JsonArray();
        ledgerOrder.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        JsonObject ledger = RecordedSharedStateFixtures.ledgerEnvelope(
                ledgerEvents, ledgerOrder);
        path.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(ledger,
                                RecordedSharedStateFixtures.identity(
                                        "REGION.1", 1L))));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(row), producer),
                firstHop);

        String owner = RecordedSessionModel.caseOwner("REGION.1",
                consumerInstance, "CASE.VMH", 0);
        String selector = RecordedSessionModel.caseSelector(owner);
        assertTrue(result.smtLib, result.smtLib.contains(
                "(=> " + selector + " (= port__REGION_1_in_0__instance__"));
        assertTrue(result.smtLib, result.smtLib.contains(
                ":named recorded_order__41__42"));
        String producerGuardLine = "";
        for (String line : result.smtLib.split("\\R")) {
            if (line.contains(":named vm_handoff_producer_guard_")) {
                producerGuardLine = line;
                break;
            }
        }
        assertFalse(result.smtLib, producerGuardLine.isEmpty());
        assertTrue(producerGuardLine, producerGuardLine.contains("(> "));
        assertTrue(producerGuardLine, producerGuardLine.contains(
                "(=> " + selector + " "));
        String producerOwner = RecordedSessionModel.caseOwner("REGION.1",
                producerInstance, "CASE.VMHP", 0);
        String producerSelector = RecordedSessionModel.caseSelector(
                producerOwner);
        assertTrue(producerGuardLine, producerGuardLine.contains(
                producerSelector));
        if (z3Available()) {
            assertEquals("unsat", z3(assuming(result.smtLib,
                    selector,
                    "(not " + producerSelector + ")")));
        }
        JsonArray bindings = result.manifest.getAsJsonArray(
                "recordedValueBindings");
        JsonObject vmBinding = null;
        for (JsonElement element : bindings) {
            JsonObject candidate = element.getAsJsonObject();
            if (VmHandoffEvidence.BINDING_KIND.equals(
                    candidate.get("kind").getAsString())) {
                vmBinding = candidate;
                break;
            }
        }
        assertTrue(bindings.toString(), vmBinding != null);
        assertTrue(vmBinding.get("valueAssertion").getAsString()
                .startsWith("bind_REGION_1_in_0"));
        assertEquals("recorded_order__41__42",
                vmBinding.get("orderAssertion").getAsString());
        assertEquals("TASK.VMHP", vmBinding
                .get(VmHandoffEvidence.PRODUCER_TASK_ID).getAsString());
        assertEquals(producerInstance, vmBinding
                .get(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID).getAsString());
        assertEquals(41L, vmBinding.get("localExportEventId").getAsLong());
        assertEquals(producerSelector,
                vmBinding.get("producerCaseSelector").getAsString());
        assertTrue(vmBinding.get("producerGuardAssertion").getAsString()
                .startsWith("vm_handoff_producer_guard_"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "VM_HANDOFF_SOURCE_EQUALITY"));

        JsonObject canonical = result.manifest.getAsJsonObject(
                CanonicalSessionModel.MANIFEST_FIELD);
        JsonObject canonicalHandoff = null;
        for (JsonElement element : canonical.getAsJsonArray(
                "valueBindings")) {
            JsonObject candidate = element.getAsJsonObject();
            if (VmHandoffEvidence.BINDING_KIND.equals(
                    candidate.get("kind").getAsString())) {
                canonicalHandoff = candidate;
                break;
            }
        }
        assertTrue(canonical.toString(), canonicalHandoff != null);
        assertEquals(producerInstance, canonicalHandoff
                .get("fromOccurrenceId").getAsString());
        assertEquals(producerInstance, canonicalHandoff
                .get(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID)
                .getAsString());
        assertFalse(canonicalHandoff.get("fromNodeId").getAsString()
                .isEmpty());
        assertFalse(canonicalHandoff.get("toNodeId").getAsString()
                .isEmpty());
        assertFalse(canonical.toString(), canonical.getAsJsonArray("gaps")
                .toString().contains(CanonicalSessionModel
                        .BINDING_ENDPOINT_UNAVAILABLE));
        assertFalse(canonical.toString(), canonical
                .getAsJsonArray("valueBindings").toString().contains(
                        CanonicalSessionModel.CANDIDATE));
        assertTrue(canonical.toString(), canonical
                .getAsJsonArray("structuralEdges").toString().contains(
                        CanonicalSessionModel.TRACE_CONNECTS_REGIONS));

        JsonObject missingOrderRow = row.deepCopy();
        JsonArray noOrderEvents = new JsonArray();
        noOrderEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.sender"));
        noOrderEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.1"));
        JsonObject noOrderLedger = RecordedSharedStateFixtures.ledgerEnvelope(
                noOrderEvents, new JsonArray());
        missingOrderRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(noOrderLedger,
                                RecordedSharedStateFixtures.identity(
                                        "REGION.1", 1L))));
        ConcolicSmtComposer.Result missingOrder = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(missingOrderRow),
                        producer), firstHop);
        assertEquals(missingOrder.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                missingOrder.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertFalse(missingOrder.manifest.toString(), missingOrder.manifest
                .get("recordedModelComplete").getAsBoolean());
        assertTrue(missingOrder.manifest.toString(), missingOrder.manifest
                .getAsJsonArray("finalStatusRefusals").toString().contains(
                        ConcolicSmtComposer.HANDOFF_ORDER_UNRECORDED));
        assertTrue(missingOrder.smtLib, missingOrder.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));

        JsonObject missingProducerRow = row.deepCopy();
        missingProducerRow.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .getAsJsonArray(VmHandoffEvidence.FIELD).get(0)
                .getAsJsonObject().addProperty(
                        VmHandoffEvidence.PRODUCER_TASK_ID, "TASK.MISSING");
        ConcolicSmtComposer.Result missing = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(missingProducerRow),
                        producer), firstHop);
        assertEquals(missing.manifest.toString(), "CANDIDATE_WITH_GAPS",
                missing.manifest.get("state").getAsString());
        assertTrue(missing.manifest.toString(), missing.manifest.toString()
                .contains(ConcolicSmtComposer
                        .HANDOFF_PRODUCER_CASE_MISSING));

        JsonObject ambiguousProducerRow = producer.toJson();
        JsonArray producerCases = ambiguousProducerRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases");
        JsonObject duplicate = producerCases.get(0).getAsJsonObject()
                .deepCopy();
        duplicate.addProperty("caseId", "CASE.VMHP.DUPLICATE");
        producerCases.add(duplicate);
        ConcolicSmtComposer.Result ambiguous = compose(fatalInstance,
                Arrays.asList(RelationSummary.decode(row),
                        RelationSummary.decode(ambiguousProducerRow)),
                firstHop);
        assertEquals("CANDIDATE_WITH_GAPS",
                ambiguous.manifest.get("state").getAsString());
        assertTrue(ambiguous.manifest.toString(), ambiguous.manifest
                .toString().contains(ConcolicSmtComposer
                        .HANDOFF_PRODUCER_CASE_AMBIGUOUS));
    }

    @Test
    public void independentRpcProducerCasesDoNotShareARawHeapProjection()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#target";
        String producerAOccurrence = "REGION.1@Test#producerA";
        String producerBOccurrence = "REGION.1@Test#producerB";
        String portA = "REGION.0.in.0";
        String portB = "REGION.0.in.1";

        // These summaries came from separate JVM replay executions.  Their
        // serialized raw owner happens to have the same spelling, but that
        // does not make their heaps one snapshot.  A global field accessor
        // would state field(sharedOwner)=1 and field(sharedOwner)=2 and make
        // the otherwise legal pair of RPC producer paths inconsistent.
        JsonObject owner = constantReference("SHARED_REPLAY_OWNER",
                "Lexample/State;");
        JsonObject field = fieldAccess(owner, "example/State", 24, "J");
        RelationSummary producerA = summary("PRODUCER_A",
                producerAOccurrence, integer(1),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        RelationSummary producerB = summary("PRODUCER_B",
                producerBOccurrence, integer(2),
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        producerA = withProducerGuardAndInteraction(producerA,
                binary(field.deepCopy(), "==", integer(1)), portA);
        producerB = withProducerGuardAndInteraction(producerB,
                binary(field.deepCopy(), "==", integer(2)), portB);

        JsonArray targetConstraints = new JsonArray();
        targetConstraints.add(binary(reference(portA, "I"), "<",
                reference(portB, "I")));
        JsonObject fatal = fatalQuery(targetOccurrence, targetConstraints);
        JsonObject targetPath = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        targetPath.addProperty(
                TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT);
        targetPath.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder
                        .REQUIRED_FATAL_BRANCH_AUTHORITY);
        targetPath.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);
        VmHandoffEvidence.writeTo(targetPath, Arrays.asList(
                VmHandoffEvidence.event(portA, 41L, integer(1),
                        "TASK.PRODUCER_A", producerAOccurrence),
                VmHandoffEvidence.event(portB, 51L, integer(2),
                        "TASK.PRODUCER_B", producerBOccurrence)));

        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.0"));
        events.add(RecordedSharedStateFixtures.event(51L,
                "HANDOFF_EXPORT", 103L, "REGION.1"));
        events.add(RecordedSharedStateFixtures.event(52L,
                "HANDOFF_ATTACH", 104L, "REGION.0"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        order.add(RecordedSharedStateFixtures.edge(51L, 52L,
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
        assertEquals(result.smtLib, 2, occurrences(result.smtLib,
                "(declare-fun container_field__"));
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
                        reference(rawA, "I"))));
        producerA = withProducerGuardAndInteraction(
                RelationSummary.decode(producerARow),
                binary(reference(rawA, "I"), ">=", integer(0)), portA);

        JsonObject producerBRow = producerB.toJson();
        JsonObject producerBCase = producerBRow.getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        SymbolicSourceEvidence.writeTo(producerBCase,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        phaseB, sourceB, producerBOccurrence,
                        "<TestDataNode: int valueB>",
                        reference(rawB, "I"))));
        producerB = withProducerGuardAndInteraction(
                RelationSummary.decode(producerBRow),
                binary(reference(rawB, "I"), ">=", integer(0)), portB);

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
        targetPath.addProperty(
                TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT);
        targetPath.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder
                        .REQUIRED_FATAL_BRANCH_AUTHORITY);
        targetPath.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);
        // TargetReachPathQueryBuilder retains target-local declarations on
        // the fatal query root: they apply to every retained nested path for
        // this exact target occurrence, while handoffs remain path-local.
        SymbolicSourceEvidence.writeTo(fatal, Arrays.asList(
                SymbolicSourceEvidence.event(phaseGate, sourceGate,
                        targetOccurrence, "<TestNameNode: int gate>",
                        reference(rawGate, "I")),
                SymbolicSourceEvidence.event(phaseOffset, sourceOffset,
                        targetOccurrence, "<TestNameNode: int offset>",
                        reference(rawOffset, "I"))));
        VmHandoffEvidence.writeTo(targetPath, Arrays.asList(
                VmHandoffEvidence.event(portA, 141L,
                        reference(rawA, "I"), "TASK.NESTED_PRODUCER_A",
                        producerAOccurrence),
                VmHandoffEvidence.event(portB, 151L,
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
                            "z3", 20_000L), 8, 64);
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
    public void targetPrefixPathsOwnTheirRpcHandoffsSeparately()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#two-paths";
        String producerAOccurrence = "REGION.1@Test#pathA";
        String producerBOccurrence = "REGION.1@Test#pathB";
        String port = "REGION.0.in.0";
        RelationSummary producerA = withProducerGuardAndInteraction(
                summary("TARGET_PATH_A", producerAOccurrence, 1,
                        Collections.<String>emptyList(),
                        Collections.<JsonObject>emptyList()),
                binary(integer(1), "==", integer(1)), port);
        RelationSummary producerB = withProducerGuardAndInteraction(
                summary("TARGET_PATH_B", producerBOccurrence, 2,
                        Collections.<String>emptyList(),
                        Collections.<JsonObject>emptyList()),
                binary(integer(1), "==", integer(1)), port);

        JsonObject portValue = reference(
                "M_I_field_" + port + "_example/Reply", "I");
        JsonObject replayOwner = constantReference(
                "SHARED_TARGET_REPLAY_OWNER", "Lexample/Target;");
        JsonObject replayField = fieldAccess(replayOwner,
                "example/Target", 24, "I");
        JsonArray firstConstraints = new JsonArray();
        firstConstraints.add(binary(replayField.deepCopy(), "==", integer(1)));
        firstConstraints.add(binary(portValue.deepCopy(), ">", integer(0)));
        JsonObject fatal = fatalQuery(targetOccurrence, firstConstraints);
        JsonObject first = fatal.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        first.addProperty("caseId", "TARGET.PATH.A");
        VmHandoffEvidence.writeTo(first,
                Collections.singletonList(VmHandoffEvidence.event(port, 41L,
                        integer(1), "TASK.TARGET_PATH_A",
                        producerAOccurrence)));

        JsonObject second = first.deepCopy();
        second.addProperty("caseId", "TARGET.PATH.B");
        JsonArray secondConstraints = new JsonArray();
        secondConstraints.add(binary(replayField.deepCopy(), "==", integer(2)));
        secondConstraints.add(binary(portValue.deepCopy(), ">", integer(0)));
        second.add("constraints", secondConstraints);
        second.remove(VmHandoffEvidence.FIELD);
        VmHandoffEvidence.writeTo(second,
                // A fresh target replay starts its VM ledger from the same
                // small ids as path A.  Scope, not the raw integer, must keep
                // these two deliveries distinct through SMT and manifests.
                Collections.singletonList(VmHandoffEvidence.event(port, 41L,
                        integer(2), "TASK.TARGET_PATH_B",
                        producerBOccurrence)));
        fatal.getAsJsonArray("paths").add(second);

        JsonArray firstEvents = new JsonArray();
        firstEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 101L, "REGION.1"));
        firstEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 102L, "REGION.0"));
        JsonArray secondEvents = new JsonArray();
        secondEvents.add(RecordedSharedStateFixtures.event(41L,
                "HANDOFF_EXPORT", 103L, "REGION.1"));
        secondEvents.add(RecordedSharedStateFixtures.event(42L,
                "HANDOFF_ATTACH", 104L, "REGION.0"));
        JsonArray firstOrder = new JsonArray();
        firstOrder.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        JsonArray secondOrder = new JsonArray();
        secondOrder.add(RecordedSharedStateFixtures.edge(41L, 42L,
                "VALUE_HANDOFF"));
        first.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        firstEvents, firstOrder),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 1L))));
        second.add(SharedStateEvidence.RECORDED_FIELD,
                SharedStateEvidence.recorded(
                        Collections.<JsonObject>emptyList(),
                        SharedStateEvidence.ledgerRecord(
                                RecordedSharedStateFixtures.ledgerEnvelope(
                                        secondEvents, secondOrder),
                                RecordedSharedStateFixtures.identity(
                                        "REGION.0", 2L))));

        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Arrays.asList(producerA, producerB),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", false, true)), fatal, null);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("HANDOFF_CASE_SCOPE_MISSING"));
        assertEquals(result.manifest.toString(), 2,
                result.manifest.getAsJsonArray("recordedValueBindings")
                        .size());
        Set<Long> scopedExports = new LinkedHashSet<>();
        Set<String> handoffKeys = new LinkedHashSet<>();
        for (JsonElement element : result.manifest.getAsJsonArray(
                "recordedValueBindings")) {
            JsonObject binding = element.getAsJsonObject();
            assertEquals(41L,
                    binding.get("localExportEventId").getAsLong());
            scopedExports.add(binding.get("exportEventId").getAsLong());
            handoffKeys.add(binding.get("bindingKey").getAsString());
        }
        assertEquals(result.manifest.toString(), 2, scopedExports.size());
        assertEquals(result.manifest.toString(), 2, handoffKeys.size());
        JsonArray canonicalBindings = result.manifest.getAsJsonObject(
                CanonicalSessionModel.MANIFEST_FIELD).getAsJsonArray(
                "valueBindings");
        Set<String> canonicalHandoffKeys = new LinkedHashSet<>();
        for (JsonElement element : canonicalBindings) {
            JsonObject binding = element.getAsJsonObject();
            if (VmHandoffEvidence.BINDING_KIND.equals(
                    binding.get("kind").getAsString())) {
                canonicalHandoffKeys.add(
                        binding.get("bindingKey").getAsString());
            }
        }
        assertEquals(result.manifest.toString(), 2,
                canonicalHandoffKeys.size());
        assertEquals(result.smtLib, 2, occurrences(result.smtLib,
                "(declare-fun container_field__"));
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_READY,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        if (z3Available()) {
            assertEquals(result.smtLib, "sat", z3(result.smtLib));
        }
    }

    @Test
    public void rootLevelTargetHandoffWithoutCaseOwnerFailsClosed()
            throws Exception {
        String targetOccurrence = "REGION.0@Test#root-handoff";
        JsonObject fatal = fatalQuery(targetOccurrence,
                targetConstraints());
        VmHandoffEvidence.writeTo(fatal,
                Collections.singletonList(VmHandoffEvidence.event(
                        "REGION.0.in.0", 41L, integer(1),
                        "TASK.PRODUCER", "REGION.1@Test#producer")));

        ConcolicSmtComposer.Result result = composeFatal(targetOccurrence,
                Collections.<RelationSummary>emptyList(),
                Arrays.asList(region("REGION.0", true, false)), fatal,
                null);

        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("HANDOFF_CASE_SCOPE_MISSING"));
    }

    @Test
    public void composerTraversalUsesOnlyVmSelectedReadFromButKeepsRpc() {
        String fatalInstance = "REGION.0@Test#target";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject concrete = binding("EDGE.CONCRETE", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 1, 2);
        JsonObject candidate = concrete.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        JsonObject excluded = concrete.deepCopy();
        excluded.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXCLUDED);
        JsonObject exact = concrete.deepCopy();
        exact.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        JsonObject guarded = concrete.deepCopy();
        guarded.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        JsonObject rpc = protocolBinding("EDGE.RPC", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");

        // Replay scheduling keeps all observed channels available.
        assertTrue(AutomaticRegionEdge.summaryTraversalBinding(concrete));
        assertTrue(AutomaticRegionEdge.summaryTraversalBinding(candidate));
        assertTrue(AutomaticRegionEdge.summaryTraversalBinding(excluded));
        // SMT traversal is the provenance-aware, narrower gate.
        assertFalse(AutomaticRegionEdge.composerTraversalBinding(concrete));
        assertFalse(AutomaticRegionEdge.composerTraversalBinding(candidate));
        assertFalse(AutomaticRegionEdge.composerTraversalBinding(excluded));
        assertTrue(AutomaticRegionEdge.composerTraversalBinding(exact));
        assertTrue(AutomaticRegionEdge.composerTraversalBinding(guarded));
        assertTrue(AutomaticRegionEdge.composerTraversalBinding(rpc));
    }

    @Test
    public void unselectedRecursiveReadFromDoesNotDemandAProducer()
            throws Exception {
        for (String provenance : Arrays.asList("",
                RecordedReadFrom.PROVENANCE_CANDIDATE,
                RecordedReadFrom.PROVENANCE_EXCLUDED)) {
            String fatalInstance = "REGION.0@Test#target";
            String consumerInstance = "REGION.1@Test#consumer";
            JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                    "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
            JsonObject upstream = binding("EDGE.UPSTREAM", "REGION.2@Test#p",
                    "REGION.2.out.0", consumerInstance,
                    "REGION.1.in.0", 1, 2);
            upstream.addProperty("fromRegion", "REGION.2");
            if (!provenance.isEmpty()) {
                upstream.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                        provenance);
            }
            RelationSummary consumer = summary("CONSUMER", consumerInstance,
                    10, Collections.singletonList("REGION.1.in.0"),
                    Arrays.asList(firstHop, upstream));

            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Collections.singletonList(consumer), firstHop);

            assertFalse(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "MissingExactProducerSummary:REGION.2"));
            assertFalse(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "DROPPED_CONFIRMED_EDGE_EVIDENCE"));
        }
    }

    @Test
    public void vmSelectedRecursiveReadFromStillDemandsItsProducer()
            throws Exception {
        for (String provenance : Arrays.asList(
                RecordedReadFrom.PROVENANCE_EXACT,
                RecordedReadFrom.PROVENANCE_GUARDED)) {
            String fatalInstance = "REGION.0@Test#target";
            String consumerInstance = "REGION.1@Test#consumer";
            JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                    "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
            JsonObject upstream = binding("EDGE.UPSTREAM", "REGION.2@Test#p",
                    "REGION.2.out.0", consumerInstance,
                    "REGION.1.in.0", 1, 2);
            upstream.addProperty("fromRegion", "REGION.2");
            upstream.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                    provenance);
            RelationSummary consumer = summary("CONSUMER", consumerInstance,
                    10, Collections.singletonList("REGION.1.in.0"),
                    Arrays.asList(firstHop, upstream));

            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Collections.singletonList(consumer), firstHop);

            assertTrue(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "MissingExactProducerSummary:REGION.2"));
        }
    }

    @Test
    public void readerSelectedReadFromUsesTheProducerCausalClosure()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER", producerInstance,
                "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject producerCopy = selected.deepCopy();
        producerCopy.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary producer = summary("PRODUCER", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(producerCopy));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, producer), firstHop);

        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("SelectedSummaryMissingExactEdgeBinding"));
        assertFalse(result.manifest.toString(), result.manifest.toString()
                .contains("SelectedReadFromMissingProducerCausalEdge"));
        assertTrue(result.manifest.toString(), result.manifest
                .getAsJsonArray("resolvedEdgeBindings").toString()
                .contains("EDGE.READER"));
    }

    @Test
    public void readerSelectedReadFromRejectsAnIncompleteProducerTuple()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER", producerInstance,
                "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject candidate = selected.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary producerWithoutEdge = withoutCausalEdges(summary(
                "PRODUCER", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate)),
                "REGION.1.out.0");

        ConcolicSmtComposer.Result noEdge = compose(fatalInstance,
                Arrays.asList(consumer, producerWithoutEdge), firstHop);
        assertTrue(noEdge.manifest.toString(), noEdge.manifest.toString()
                .contains("SelectedReadFromMissingProducerCausalEdge:"
                        + "EDGE.READER"));

        RelationSummary wrongOccurrence = summary("WRONG",
                producerInstance + ".other", 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));
        ConcolicSmtComposer.Result noOccurrence = compose(fatalInstance,
                Arrays.asList(consumer, wrongOccurrence), firstHop);
        assertTrue(noOccurrence.manifest.toString(),
                noOccurrence.manifest.toString().contains(
                        "MissingExactProducerSummary:REGION.1"));

        JsonObject missingOccurrence = selected.deepCopy();
        missingOccurrence.remove("fromOccurrenceId");
        missingOccurrence.addProperty("edgeId", "EDGE.NO_OCCURRENCE");
        RelationSummary missingOccurrenceConsumer = summary(
                "NO_OCCURRENCE_CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, missingOccurrence));
        ConcolicSmtComposer.Result noOccurrenceId = compose(fatalInstance,
                Arrays.asList(missingOccurrenceConsumer,
                        producerWithoutEdge), firstHop);
        assertTrue(noOccurrenceId.manifest.toString(),
                noOccurrenceId.manifest.toString().contains(
                        "UntrustedRecursiveEdgeBinding:EDGE.NO_OCCURRENCE"));

        JsonObject wrongPort = selected.deepCopy();
        wrongPort.addProperty("edgeId", "EDGE.WRONG_PORT");
        wrongPort.addProperty("fromOutputPort", "REGION.1.out.missing");
        RelationSummary wrongPortConsumer = summary("WRONG_PORT_CONSUMER",
                consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, wrongPort));
        ConcolicSmtComposer.Result noPort = compose(fatalInstance,
                Arrays.asList(wrongPortConsumer, producerWithoutEdge),
                firstHop);
        assertTrue(noPort.manifest.toString(), noPort.manifest.toString()
                .contains("MissingExactProducerSummary:REGION.1"));
    }

    @Test
    public void readerSelectedReadFromRejectsAmbiguousProducerSummaries()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        String consumerInstance = "REGION.1@Test#consumer";
        String producerInstance = "REGION.1@Test#producer";
        JsonObject firstHop = protocolBinding("EDGE.RPC", consumerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0");
        JsonObject selected = binding("EDGE.READER", producerInstance,
                "REGION.1.out.0", consumerInstance,
                "REGION.1.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        selected.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.State#value");
        JsonObject candidate = selected.deepCopy();
        candidate.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        RelationSummary consumer = summary("CONSUMER", consumerInstance, 10,
                Collections.singletonList("REGION.1.in.0"),
                Arrays.asList(firstHop, selected));
        RelationSummary first = summary("PRODUCER_A", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));
        RelationSummary second = summary("PRODUCER_B", producerInstance, 7,
                Collections.<String>emptyList(),
                Collections.singletonList(candidate));

        ConcolicSmtComposer.Result result = compose(fatalInstance,
                Arrays.asList(consumer, first, second), firstHop);

        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains("AmbiguousExactProducerSummary:REGION.1"));
        assertFalse(result.manifest.toString(), result.manifest
                .getAsJsonArray("resolvedEdgeBindings").toString()
                .contains("EDGE.READER"));
    }

    @Test
    public void droppedAuditIgnoresRuntimeCandidatesButRefusesSelectedExact()
            throws Exception {
        String fatalInstance = "REGION.0@Test#target";
        JsonArray constraints = new JsonArray();
        constraints.add(binary(reference("REGION.0.in.0", "I"), "==",
                integer(1)));
        for (String provenance : Arrays.asList("",
                RecordedReadFrom.PROVENANCE_CANDIDATE,
                RecordedReadFrom.PROVENANCE_EXCLUDED)) {
            JsonObject runtimeOnly = binding("EDGE.RUNTIME", "REGION.1@Test#p",
                    "REGION.1.out.0", fatalInstance,
                    "REGION.0.in.0", 1, 2);
            if (!provenance.isEmpty()) {
                runtimeOnly.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                        provenance);
            }
            ConcolicSmtComposer.Result result = compose(fatalInstance,
                    Collections.<RelationSummary>emptyList(),
                    Arrays.asList(region("REGION.0", true, false),
                            region("REGION.1", false, true)), constraints,
                    Collections.singletonList(runtimeOnly));
            assertFalse(provenance + "\n" + result.manifest,
                    result.manifest.toString().contains(
                            "DROPPED_CONFIRMED_EDGE_EVIDENCE"));
        }

        String producerInstance = "REGION.1@Test#producer";
        JsonObject selected = binding("EDGE.SELECTED", producerInstance,
                "REGION.1.out.0", fatalInstance, "REGION.0.in.0", 1, 2);
        selected.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        RelationSummary producer = summary("SELECTED", producerInstance, 10,
                Collections.<String>emptyList(),
                Collections.singletonList(selected));
        ConcolicSmtComposer.Result refused = compose(fatalInstance,
                Collections.singletonList(producer),
                Collections.singletonList(
                        region("REGION.0", true, false)), constraints,
                selected);
        assertTrue(refused.manifest.toString(), refused.manifest.toString()
                .contains("DROPPED_CONFIRMED_EDGE_EVIDENCE:"));
        assertEquals(ConcolicSmtComposer.FINAL_REFUSED,
                refused.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
    }

    /**
     * A ledger that claims a partial order and delivers a cycle spanning a
     * field read-from, program order and an RPC value handoff.
     */
    private static JsonObject crossChannelCycleLedger() {
        JsonArray events = new JsonArray();
        events.add(RecordedSharedStateFixtures.event(11L, "FIELD_WRITE", 101L,
                "REGION.writerA"));
        events.add(RecordedSharedStateFixtures.event(21L, "FIELD_READ", 103L,
                "REGION.reader"));
        events.add(RecordedSharedStateFixtures.event(31L, "HANDOFF_EXPORT",
                103L, "REGION.reader"));
        events.add(RecordedSharedStateFixtures.event(32L, "HANDOFF_ATTACH",
                101L, "REGION.writerA"));
        JsonArray order = new JsonArray();
        order.add(RecordedSharedStateFixtures.edge(11L, 21L,
                "FIELD_READ_FROM"));
        order.add(RecordedSharedStateFixtures.edge(21L, 31L,
                "PROGRAM_ORDER"));
        order.add(RecordedSharedStateFixtures.edge(31L, 32L,
                "VALUE_HANDOFF"));
        order.add(RecordedSharedStateFixtures.edge(32L, 11L,
                "VALUE_HANDOFF"));
        return RecordedSharedStateFixtures.ledgerEnvelope(events, order);
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
        // The selector family is composed and solved, but this read keeps an
        // unknown arm, so README SMT-1 refuses it as a final artifact.  The
        // exact case above is FINAL_READY, which is what makes the refusal
        // here a statement about this model and not about the gate.
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
        // The unknown arm constrains no value, which is what keeps the model
        // satisfiable for a target no recorded writer produces.
        assertEquals("sat", z3(assuming(ready(guardedGolden(99, true, true))
                .smtLib, "rf_selector__21__rf_unknown")));

        // A false writer guard makes that arm infeasible, and only that arm.
        ConcolicSmtComposer.Result refuted = ready(
                guardedGolden(2, false, true));
        assertTrue(refuted.smtLib, refuted.smtLib.contains(
                ":named recorded_write_guard__21__rf2"));
        assertEquals("unsat", z3(assuming(refuted.smtLib,
                "rf_selector__21__rf2")));
        assertEquals("sat", z3(refuted.smtLib));

        // Unknown: neither recorded write is in the order domain, so writer
        // existence refuses both arms and the read keeps its unknown value.
        ConcolicSmtComposer.Result unknown = ready(
                guardedGolden(1, true, false));
        assertTrue(unknown.smtLib, unknown.smtLib.contains(
                ":named recorded_write_absent__21__11"));
        assertEquals("unsat", z3(assuming(unknown.smtLib,
                "rf_selector__21__rf1")));
        assertEquals("sat", z3(assuming(unknown.smtLib,
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

    @Test
    public void selectedInputAuthorityIsCaseLocal() {
        assertFalse(ConcolicSmtComposer.authorityCasesDefinitelyAmbiguous(
                Arrays.asList("case_a", "case_b")));
        assertTrue(ConcolicSmtComposer.authorityCasesDefinitelyAmbiguous(
                Arrays.asList("case_a", "case_a")));
        assertTrue(ConcolicSmtComposer.authorityCasesDefinitelyAmbiguous(
                Arrays.asList("true", "case_a")));
        assertEquals("(= (+ (ite case_a 1 0) (ite case_b 1 0)) 1)",
                ConcolicSmtComposer.exactlyOneAuthority(
                        Arrays.asList("case_a", "case_b")));
    }

    @Test
    public void recordedReadSupersedesValueFrontierRoot()
            throws Exception {
        ConcolicSmtComposer.Result result = exactGolden(10, "CLOSED", true);

        JsonObject target = null;
        for (JsonElement element
                : result.manifest.getAsJsonArray("selectedInputLedger")) {
            JsonObject row = element.getAsJsonObject();
            if ("REGION.0.in.0".equals(row.get("portId").getAsString())) {
                target = row;
                break;
            }
        }
        assertTrue(result.manifest.toString(), target != null);
        assertEquals(ConcolicSmtComposer.READ_FROM_ARM,
                target.get("authority").getAsString());
        assertEquals(target.toString(), 1,
                target.getAsJsonArray("evidence").size());
        assertEquals(target.toString(), ConcolicSmtComposer.READ_FROM_ARM,
                target.getAsJsonArray("evidence").get(0).getAsJsonObject()
                        .get("authority").getAsString());
        assertTrue(target.toString(), target.getAsJsonArray("uses")
                .get(0).getAsJsonObject().get("caseGuard").getAsString()
                .startsWith("case_selector__"));
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= (+ (ite true 1 0) (ite true 1 0)) 1)"));
        assertFalse(result.manifest.toString(), result.manifest
                .getAsJsonArray("gaps").toString().contains(
                        ConcolicSmtComposer.INPUT_AUTHORITY_AMBIGUOUS));
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
                new BooleanReachConditionExtractor.Z3Solver("z3", 20_000L),
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
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        fatalInstance);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24, candidates);
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
        fatal.getAsJsonArray("paths").get(0).getAsJsonObject()
                .add(SharedStateEvidence.RECORDED_FIELD,
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

    private RelationSummary configuredSourceProducer(
            String occurrence, String sourceId, String field, String raw) {
        JsonObject row = summary("SOURCE.SELECTOR", occurrence, 9,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList()).toJson();
        JsonArray cases = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        JsonObject sourceSeven = cases.get(0).getAsJsonObject();
        sourceSeven.addProperty("caseId", "CASE.SOURCE.7");
        sourceSeven.addProperty("sourceTaskId", "TASK.SOURCE.7");
        sourceSeven.getAsJsonObject("guard")
                .getAsJsonArray("conditions").add(binary(
                        reference(raw, "I"), "==", integer(7)));
        SymbolicSourceEvidence.writeTo(sourceSeven,
                Collections.singletonList(SymbolicSourceEvidence.event(
                        publishPhase(occurrence), sourceId, occurrence,
                        field, reference(raw, "I"))));
        JsonObject sourceNine = sourceSeven.deepCopy();
        sourceNine.addProperty("caseId", "CASE.SOURCE.9");
        sourceNine.addProperty("sourceTaskId", "TASK.SOURCE.9");
        JsonArray nineGuard = new JsonArray();
        nineGuard.add(binary(reference(raw, "I"), "==", integer(9)));
        sourceNine.getAsJsonObject("guard").add("conditions", nineGuard);
        cases.add(sourceNine);
        return RelationSummary.decode(row);
    }

    private ConcolicSmtComposer.Result composeSelectorFailure(
            String fatalOccurrence, String consumerOccurrence,
            String sourceOccurrence, String sourceId, String field,
            String raw, String sourceTaskId, RelationSummary producer,
            JsonObject firstHop) throws Exception {
        RelationSummary consumer = summary("SELECTOR.CONSUMER",
                consumerOccurrence, 1,
                Collections.<String>emptyList(),
                Collections.singletonList(firstHop));
        JsonObject row = consumer.toJson();
        writeConfiguredSelector(row.getAsJsonObject("regionRelation")
                        .getAsJsonArray("cases").get(0).getAsJsonObject(),
                sourceOccurrence, sourceId, field, sourceTaskId, raw, 9);
        return compose(fatalOccurrence,
                Arrays.asList(RelationSummary.decode(row), producer),
                firstHop);
    }

    private static void writeConfiguredSelector(
            JsonObject owner, String sourceOccurrence, String sourceId,
            String field, String sourceTaskId, String raw, int value) {
        writeConfiguredSelector(owner, sourceOccurrence, sourceId, field,
                sourceTaskId, raw, value, consumePhase(sourceOccurrence),
                publishPhase(sourceOccurrence));
    }

    private static void writeConfiguredSelector(
            JsonObject owner, String sourceOccurrence, String sourceId,
            String field, String sourceTaskId, String raw, int value,
            String consumePhaseId, String producerPhaseId) {
        JsonObject task = new JsonObject();
        JsonArray selectors = new JsonArray();
        selectors.add(ConfiguredSourceSelectorContract.exactInt(
                consumePhaseId, producerPhaseId, sourceOccurrence,
                sourceId, field));
        task.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        JsonObject evidence = ConfiguredSourceSelectorContract.evidence(
                ConfiguredSourceSelectorContract.decode(task).get(0),
                sourceTaskId, raw, value);
        JsonArray rows = new JsonArray();
        rows.add(evidence);
        owner.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD, rows);
    }

    private static String publishPhase(String occurrence) {
        return "SOURCE_PHASE.PUBLISH."
                + CanonicalJson.sha256(occurrence).substring(0, 16);
    }

    private static String consumePhase(String occurrence) {
        return "SOURCE_PHASE.CONSUME."
                + CanonicalJson.sha256(occurrence).substring(0, 16);
    }

    private static String configuredRaw(String phase, String source,
                                        String suffix) {
        return "M_I_field_" + SymbolicSourceEvidence.engineLabelForPhase(
                phase, source) + "_" + suffix;
    }

    private static void assertSelectorRefused(
            ConcolicSmtComposer.Result result, String reason) {
        assertEquals(result.manifest.toString(),
                ConcolicSmtComposer.FINAL_REFUSED,
                result.manifest.get(ConcolicSmtComposer.FINAL_STATUS)
                        .getAsString());
        assertTrue(result.manifest.toString(), result.manifest.toString()
                .contains(reason));
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert false) ; fail closed: unsupported"));
    }

    @Test
    public void observedCoverageRootAndProvenanceMustNameOneState()
            throws Exception {
        assertObservedCoverage("PARTIAL", "PARTIAL", true);
        assertObservedCoverage("SEED_ONLY", "SEED_ONLY", true);
        assertObservedCoverage("CLOSED", "PARTIAL", false);
        assertObservedCoverage("PARTIAL", "SEED_ONLY", false);
        assertObservedCoverage("CLOSED", "CLOSED", false);
    }

    @Test
    public void unsatClosureRequiresClosedProducerAndTargetPathSets() {
        RelationSummary closed = summary("UNSAT.CLOSED",
                "REGION.1@Test#closed", 1,
                Collections.<String>emptyList(),
                Collections.<JsonObject>emptyList());
        JsonObject fatal = new JsonObject();
        fatal.add("coverageGaps", new JsonArray());
        JsonObject complete = ConcolicSmtComposer.unsatClosureEvidence(
                true, Collections.singletonList(closed), fatal, true, 0);
        assertTrue(complete.toString(), complete.get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());

        RelationSummary partial = declaring(closed, "PARTIAL");
        JsonObject producerOpen = ConcolicSmtComposer.unsatClosureEvidence(
                true, Collections.singletonList(partial), fatal, true, 0);
        assertFalse(producerOpen.toString(), producerOpen.get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
        assertEquals(1, producerOpen.getAsJsonArray(
                "partialProducerSummaryIds").size());

        JsonObject targetOpen = new JsonObject();
        JsonArray targetGaps = new JsonArray();
        targetGaps.add(CoverageDivergence.of(
                CoverageDivergence.Kind.TARGET,
                "PATH_FLIP_REPLAY_NOT_ADMITTED", "QUERY.TARGET", "miss"));
        targetOpen.add("coverageGaps", targetGaps);
        JsonObject targetIncomplete = ConcolicSmtComposer
                .unsatClosureEvidence(true,
                        Collections.singletonList(closed), targetOpen, true,
                        1);
        assertFalse(targetIncomplete.toString(), targetIncomplete.get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
        assertEquals(1, targetIncomplete.get(
                "targetCoverageGapCount").getAsInt());

        assertFalse(ConcolicSmtComposer.unsatClosureEvidence(true,
                Collections.singletonList(closed), fatal, false, 0).get(
                ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE).getAsBoolean());
    }

    private static void assertObservedCoverage(String rootState,
                                               String nestedState,
                                               boolean accepted)
            throws Exception {
        JsonObject summary = new JsonObject();
        summary.addProperty("pathCoverageState", rootState);
        JsonObject relation = new JsonObject();
        relation.addProperty("guardProjection",
                "SELECTIVE_SYMBOLIC_BRANCH_SLICE");
        JsonArray cases = new JsonArray();
        cases.add(new JsonObject());
        relation.add("cases", cases);
        summary.add("regionRelation", relation);

        JsonObject coverage = new JsonObject();
        coverage.addProperty("schemaVersion", 1);
        coverage.addProperty("kind", "OBSERVED_PATH_COVERAGE");
        coverage.addProperty("authority",
                "IMPORTED_VM_PATH_UNDERAPPROX_V1");
        coverage.addProperty("complete", false);
        coverage.addProperty("coverageState", nestedState);
        coverage.addProperty("constraintProjectionAuthority",
                "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1");
        coverage.addProperty("observedCaseCount", 1);
        coverage.addProperty("observedPathCount", 1);
        coverage.addProperty("observedPathSetHash", "HASH.ONE.PATH");
        try {
            ConcolicSmtComposer.requireObservedCoverage(summary, coverage);
            if (!accepted) fail("inconsistent observed coverage was accepted");
        } catch (IOException rejected) {
            if (accepted) throw rejected;
            assertTrue(rejected.getMessage(), rejected.getMessage().contains(
                    "Malformed observed-path"));
        }
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
                "REL.REGION.1", "REGION.1",
                "REGION.1.out.1", "<Test: int competing>", "REGION_OUTPUT",
                "int", slice);
        OutputClosureCodec.writeTo(row, OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(row), second)));
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject().getAsJsonObject("outputExpressions")
                .add("REGION.1.out.1", integer(20));
        return RelationSummary.decode(row);
    }

    private static RelationSummary withoutCausalEdges(
            RelationSummary summary, String outputPort) {
        JsonObject row = summary.toJson();
        for (JsonElement element : row.getAsJsonObject(
                OutputClosureContract.FIELD).getAsJsonArray("members")) {
            JsonObject member = element.getAsJsonObject();
            if (outputPort.equals(member.getAsJsonObject("output")
                    .get("portId").getAsString())) {
                member.getAsJsonObject("slice").add("causalEdgeIds",
                        new JsonArray());
            }
        }
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
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty("regionId", "REGION.0");
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        "REGION.0@Test#call30");
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedSharedStateFixtures.guardedRead(21L, 7L,
                24);
        SharedStateEvidence.normalizeGuards(guarded);
        // The guarded term rides with the writer's value, which is where the
        // composer's expression scan finds it.
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .add("expression", guarded);
        JsonObject row = summary.toJson();
        // The runtime records the declared field beside the VM's own location
        // identity, and a gate needs it: the location key does not survive
        // into a second session, and the field does.
        row.add(SharedStateEvidence.RECORDED_FIELD,
                RecordedSharedStateFixtures.recordedMember(envelope, ledger,
                        "example.State#value"));
        return RelationSummary.decode(row);
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
                "REL.REGION.1", "REGION.1", "REGION.1.out.0",
                "<Test: " + outputJavaType + " output>", "REGION_OUTPUT",
                outputJavaType, slice);

        JsonObject row = new JsonObject();
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
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
        fatal.addProperty("schemaVersion", 1);
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

    private static JsonObject region(
            String id, boolean hasInput, boolean hasOutput) {
        return region(id, hasInput ? "int" : "",
                hasOutput ? "int" : "");
    }

    private static JsonObject region(
            String id, String inputType, String outputType) {
        JsonObject region = new JsonObject();
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

    private static JsonObject occurrencePlan(String region,
                                             String occurrence) {
        JsonObject row = new JsonObject();
        row.addProperty("regionId", region);
        row.addProperty("occurrenceId", occurrence);
        return row;
    }

    private static int occurrences(String value, String needle) {
        int count = 0;
        int at = 0;
        while ((at = value.indexOf(needle, at)) >= 0) {
            count++;
            at += needle.length();
        }
        return count;
    }

    private static String largeSmtTerm(String leaf) {
        StringBuilder result = new StringBuilder("(snapshot");
        for (int index = 0; index < 260; index++) {
            result.append(' ').append(leaf).append('_').append(index);
        }
        return result.append(')').toString();
    }

    private static String largeBoundSmtTerm(String bound) {
        StringBuilder result = new StringBuilder("(snapshot ")
                .append(bound);
        for (int index = 0; index < 300; index++) {
            result.append(" padding_").append(index);
        }
        return result.append(')').toString();
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    private static JsonObject reference(String symbol, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", symbol);
        return result;
    }

    private static JsonObject constantReference(String symbol,
                                                String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
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
            RelationSummary summary, JsonObject condition, String portId) {
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
