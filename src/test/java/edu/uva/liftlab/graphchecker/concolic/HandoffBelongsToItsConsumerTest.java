package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import org.junit.Assume;
import static org.junit.Assert.assertFalse;

/**
 * A handoff belongs to the occurrence whose port it is.
 *
 * <p>Lane B2d's shape. The port is declared IN as a CALL_RETURN on
 * {@code PBHelper.convert(BlockKeyProto)} -- the decode, REGION.16ba41cf --
 * and a CALL_RETURN attach runs in the CALLER's frame, after the callee's
 * activation has closed and published. The row therefore rides on the
 * caller, REGION.b7266d53, and one attach was reported twice: unplanned
 * there, unreproduced here.</p>
 *
 * <p>So H names the consumer the plan declares, the row says which, and the
 * reproduction question is asked of the corpus rather than of the row that
 * happened to carry the evidence.</p>
 */
public class HandoffBelongsToItsConsumerTest {
    private static final String PORT =
            "XCH.1174244c.resp.block-key-id";
    private static final String CONSUMER =
            "hdfs-17899/sps#epoch0/region/REGION.16ba41cf#1";
    private static final String CARRIER =
            "hdfs-17899/sps#epoch0/region/REGION.b7266d53#1#a1";

    /** The row names the consumer, not the activation carrying it. */
    @Test
    public void handoffBelongsToItsConsumerRules() throws Exception {
        theRowNamesTheConsumerNotItsCarrier();
        aHandoffThatNamesItsConsumerIsPlanned();
        aHandoffThatNamesNoConsumerIsUnplanned();
        aDeliveryWithNoElementReproducedItsPort();
        HandoffControlBySymbolTest t0 =
                new HandoffControlBySymbolTest();
        t0.handoffControlBySymbolRules();
        SourcePhaseCatalogBySiteTest t1 =
                new SourcePhaseCatalogBySiteTest();
        t1.sourcePhaseCatalogBySiteRules();
        ConcolicSummaryImporterManualInputEvidenceTest t2 =
                new ConcolicSummaryImporterManualInputEvidenceTest();
        t2.concolicSummaryImporterManualInputEvidenceRules();
        ConcolicConstraintSolverMaterializationTest t3 =
                new ConcolicConstraintSolverMaterializationTest();
        t3.concolicConstraintSolverMaterializationRules();
    }

    private void theRowNamesTheConsumerNotItsCarrier() {
        JsonObject row = handoff(CONSUMER);

        assertEquals(CONSUMER, row.get(
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(row),
                VmHandoffEvidence.isEvent(row));
    }

    /** A row that names its consumer is not an unplanned handoff. */
    private void aHandoffThatNamesItsConsumerIsPlanned() {
        assertEquals("", unplanned(handoff(CONSUMER)));
    }

    /** One that names none still is, which is what the code is for. */
    private void aHandoffThatNamesNoConsumerIsUnplanned() {
        JsonObject row = handoff(CONSUMER);
        row.addProperty(VmHandoffEvidence.CONSUMER_OCCURRENCE_ID, "");
        assertTrue("a row naming no consumer is refused by admission",
                !VmHandoffEvidence.isEvent(row));
    }

    /**
     * A delivery that carried no element reproduced its planned port.
     *
     * <p>The mint is the consumer's, so it happens whether or not the
     * message carried the producer's expression, and the row it publishes is
     * the reproduction.  While the attach refused to mint on a message with
     * no element, the importer saw no row and said the planned handoff had
     * not reproduced: on hdfs-17899 bug3's flip replay, eight of them, on
     * ports the replay did attach.</p>
     */
    private void aDeliveryWithNoElementReproducedItsPort() {
        JsonObject arrived = VmHandoffEvidence.event(PORT, 0L, 0L, null,
                "", "", CONSUMER,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                        "<a.BlockKey: int keyId>"),
                "M_I_field_HOFF.9c1d_a/BlockKey", "119982", "I", "", true);
        assertTrue(VmHandoffEvidence.eventFault(arrived),
                VmHandoffEvidence.isEvent(arrived));

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("taskId", "task");
        raw.addProperty("occurrenceId", CARRIER);
        JsonArray events = new JsonArray();
        events.add(arrived);
        raw.add(VmHandoffEvidence.FIELD, events);

        java.util.List<JsonObject> rows = new java.util.ArrayList<>();
        ConcolicSummaryImporter.topologyDivergences(
                new ConcolicSummaryImporter.ResultRow(raw, 0),
                consumerTask(), rows);

        for (JsonObject row : rows) {
            assertTrue(String.valueOf(row), !"PLANNED_HANDOFF_NOT_REPRODUCED"
                    .equals(row.get("code").getAsString()));
        }

        // The control: with no row at all the question is still asked, so
        // the assertion above is about the mint and not about the fold.
        raw.add(VmHandoffEvidence.FIELD, new JsonArray());
        rows.clear();
        ConcolicSummaryImporter.topologyDivergences(
                new ConcolicSummaryImporter.ResultRow(raw, 0),
                consumerTask(), rows);
        boolean reported = false;
        for (JsonObject row : rows) {
            reported |= "PLANNED_HANDOFF_NOT_REPRODUCED".equals(
                    row.get("code").getAsString());
        }
        assertTrue("a port nothing attached is still reported", reported);
    }

    /** One task that declares {@code PORT} as its own IN site. */
    private static edu.uva.liftlab.graphchecker.contract.ExecutionTask
            consumerTask() {
        JsonObject task = new JsonObject();
        task.addProperty("sourceKey", "hdfs-17899/sps#epoch0");
        task.addProperty("occurrenceId", CONSUMER);
        task.addProperty("relationKey", "relation");
        task.addProperty("regionId", "REGION.16ba41cf");
        task.addProperty("taskId", "task");
        task.addProperty("goalId", "goal");
        task.add("inputActions", new JsonArray());
        JsonObject handoff = new JsonObject();
        handoff.addProperty("portId", PORT);
        handoff.addProperty("handoffLeafPath", PORT);
        handoff.addProperty("side", "IN");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("captureKind", "CALL_RETURN");
        handoff.addProperty("javaType", "int");
        handoff.addProperty("declaredCallee", "<a.P: int keyId()>");
        handoff.addProperty("definitionMethod", "<a.PBHelper: a.Key c()>");
        handoff.addProperty("definitionUnitIndex", 2);
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        task.add("communicationHandoffs", handoffs);
        edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy.cfgBackedges(
                edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy
                        .MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        return edu.uva.liftlab.graphchecker.contract.ExecutionTask.decode(
                task);
    }

    /** Which port the corpus attached, for which consumer occurrence. */
    private static String unplanned(JsonObject row) {
        // The importer's own question, asked the way the fold asks it.
        String consumer = row.get(
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID).getAsString();
        return consumer.isEmpty() ? "UNPLANNED_HANDOFF" : "";
    }

    private static JsonObject handoff(String consumerOccurrenceId) {
        JsonObject payload = new JsonObject();
        payload.addProperty("_type", "SymbolExpression");
        payload.addProperty("_java_type", "I");
        payload.addProperty("_exp", "M_I_field_SRC.root");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConsumerBoundaryExpression");
        expression.addProperty("boundaryKind", "RPC_ATTACH");
        expression.addProperty("eventId", 63);
        expression.addProperty("_java_type", "I");
        expression.add("expression", payload);
        return VmHandoffEvidence.event(PORT, 55L, 63L, expression,
                "TASK.SEED.1d0b713e",
                "hdfs-17899/nn0#epoch0/region/REGION.2392e4b7#1#a1",
                consumerOccurrenceId,
                HandoffPhaseContract.phaseId(PORT,
                        "hdfs-17899/sps#epoch0/region/REGION.16ba41cf#1", 1,
                        "<a.BlockKey: int keyId>"),
                "M_I_field_HOFF.9c1d_a/BlockKey", "119982", "I", "",
                false);
    }

    /**
     * A handoff variable is answered by the attach that minted it, wherever in
     * this replay that attach happened.
     *
     * <p>The label {@code HOFF.<sha>} IS the identity of its attach, and the
     * attach happened in this same replay run -- in whichever region
     * activation's summary made it. Looking only at the flipped path's own
     * summary found one attach where the model assigned five, and every such
     * model was refused as not materializable.</p>
     */
    static final class HandoffControlBySymbolTest {
        private static final String LABEL = "M_I_field_HOFF.abc123"
                + "_edu/uva/liftlab/graphchecker/runtime/"
                + "ConcolicRegionRuntime$HandoffLeafCarrier";
        private static final String PHASE =
                "HANDOFF_PHASE.11111111-2222-3333-4444-555555555555";
        private static final String REPLAY = "REPLAY.GROUP.ONE";

        public void handoffControlBySymbolRules() throws Exception {
            aSymbolMintedInASiblingSummaryIsTheObligationsControl();
            aSymbolNoSummaryMintedIsNamed();
        }

        private void aSymbolMintedInASiblingSummaryIsTheObligationsControl() {
            JsonObject task = flipTask();
            JsonObject manifest = manifest();

            ConcolicPathFlipPlanner.Wave.controlBySymbol(task, REPLAY,
                    Arrays.asList(pathSummary(), siblingSummary()), manifest);

            JsonArray controls = task.getAsJsonArray(
                    RegionPathWorklist.HANDOFF_CONTROLS);
            assertEquals("the attach that minted it answers it", 1,
                    controls.size());
            JsonObject control = controls.get(0).getAsJsonObject();
            assertEquals(LABEL, control.get("rawSymbol").getAsString());
            assertEquals(PHASE, control.get(
                    InSessionReadResolver.HANDOFF_PHASE_ID).getAsString());
            assertEquals("and names the activation it happened in",
                    "node0/region/REGION.sibling#2#a1",
                    control.get("consumerOccurrenceId").getAsString());
            assertEquals(0, manifest.getAsJsonArray("gaps").size());
        }

        private void aSymbolNoSummaryMintedIsNamed() {
            JsonObject task = flipTask();
            JsonObject manifest = manifest();

            ConcolicPathFlipPlanner.Wave.controlBySymbol(task, REPLAY,
                    Arrays.asList(pathSummary()), manifest);

            assertFalse("nothing to carry", task.has(
                    RegionPathWorklist.HANDOFF_CONTROLS));
            JsonArray gaps = manifest.getAsJsonArray("gaps");
            assertEquals(1, gaps.size());
            assertEquals("HANDOFF_CONTROL_ROW_ABSENT",
                    gaps.get(0).getAsJsonObject().get("kind").getAsString());
            assertTrue(gaps.get(0).getAsJsonObject().get("subject")
                    .getAsString().contains("HOFF.abc123"));
        }

        /** One obligation whose resolved flip mentions the arrived value. */
        private static JsonObject flipTask() {
            JsonObject symbol = new JsonObject();
            symbol.addProperty("_type", "SymbolExpression");
            symbol.addProperty("_java_type", "I");
            symbol.addProperty("_exp", LABEL);
            JsonArray predicates = new JsonArray();
            predicates.add(symbol);
            JsonObject resolved = new JsonObject();
            resolved.addProperty("schemaVersion",
                    ResolvedFlipQuery.SCHEMA_VERSION);
            resolved.addProperty("kind", ResolvedFlipQuery.KIND);
            resolved.addProperty("authority", ResolvedFlipQuery.AUTHORITY);
            resolved.add("predicates", predicates);
            resolved.add("context", new JsonArray());
            resolved.add("unresolved", new JsonArray());
            JsonObject task = new JsonObject();
            task.addProperty("queryKey", "0123456789abcdef");
            task.add(ResolvedFlipQuery.FIELD, resolved);
            return task;
        }

        /** The flipped path's own summary: it minted no handoff. */
        private static JsonObject pathSummary() {
            JsonObject summary = new JsonObject();
            summary.addProperty("replayGroupId", REPLAY);
            summary.addProperty("occurrenceId",
                    "node0/region/REGION.target#1#a1");
            return summary;
        }

        /** Another activation of the same replay, where the attach happened. */
        private static JsonObject siblingSummary() {
            JsonObject event = new JsonObject();
            event.addProperty("kind", "VM_HANDOFF_EVENT");
            event.addProperty("attachEventId", 77L);
            event.addProperty(InSessionReadResolver.HANDOFF_SYMBOL, LABEL);
            event.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID, PHASE);
            event.addProperty("javaType", "I");
            event.addProperty("recordedValue", "119982");
            JsonArray events = new JsonArray();
            events.add(event);
            JsonObject summary = new JsonObject();
            summary.addProperty("replayGroupId", REPLAY);
            summary.addProperty("occurrenceId",
                    "node0/region/REGION.sibling#2#a1");
            summary.add(VmHandoffEvidence.FIELD, events);
            return summary;
        }

        private static JsonObject manifest() {
            JsonObject manifest = new JsonObject();
            manifest.add("gaps", new JsonArray());
            return manifest;
        }
    }


    /**
     * One phase id across two executions is a catalog, not a malformed one.
     *
     * <p>A configured source is declared by SITE, so it is one variable per
     * replay and its catalog carries one id for every execution of that site.
     * The importer indexed the catalog by id and raised on the second row, which
     * rejected every region path whose site ran more than once: lane BH's 50
     * {@code REGION_PATH_ADMISSION_REJECTED}, every one of them naming
     * {@code SOURCE_PHASE.05975245-3fb5-356a-913e-d5e369ce3b2e}.</p>
     */
    static final class SourcePhaseCatalogBySiteTest {
        private static final String SOURCE_ID = "HDFS.CONFIG.ORDERED";
        private static final String METHOD =
                "<a.Manager: boolean isSnapshotDeletionOrdered()>";
        private static final String FIELD =
                "<a.Manager: boolean snapshotDeletionOrdered>";
        private static final int UNIT = 1;
        private static final String OCCURRENCE =
                "hdfs/nn0#epoch1/region/REGION.r#1";

        /** Two executions of one site, one id, and the mint is admitted. */
        public void sourcePhaseCatalogBySiteRules() throws Exception {
            aRepeatedPhaseIdIsOneVariableNotAMalformedCatalog();
            aSecondObservationOfOneSiteIsNotASecondRoot();
            anUndeclaredPhaseIsStillRefused();
        }

        private void aRepeatedPhaseIdIsOneVariableNotAMalformedCatalog() {
            List<ConfiguredSourcePhaseContract.Occurrence> catalog = catalog();
            assertEquals("the catalog holds both executions", 2, catalog.size());
            assertEquals("under one identity", catalog.get(0).phaseId(),
                    catalog.get(1).phaseId());

            List<String> issues = new ArrayList<>();
            JsonArray admitted = ConcolicSummaryImporter.symbolicSourceEvidence(
                    row(catalog.get(0).phaseId(), 1), catalog, issues);

            assertEquals(issues.toString(), 0, issues.size());
            assertEquals("the mint is admitted", 1, admitted.size());
        }

        /** A second observation of one site is the same root, admitted once. */
        private void aSecondObservationOfOneSiteIsNotASecondRoot() {
            List<ConfiguredSourcePhaseContract.Occurrence> catalog = catalog();
            List<String> issues = new ArrayList<>();

            JsonArray admitted = ConcolicSummaryImporter.symbolicSourceEvidence(
                    row(catalog.get(0).phaseId(), 2), catalog, issues);

            assertEquals(issues.toString(), 0, issues.size());
            assertEquals("one variable, admitted once", 1, admitted.size());
        }

        /** A mint naming no declared site is still refused. */
        private void anUndeclaredPhaseIsStillRefused() {
            List<String> issues = new ArrayList<>();

            ConcolicSummaryImporter.symbolicSourceEvidence(
                    row("SOURCE_PHASE.00000000-0000-3000-8000-000000000000", 1),
                    catalog(), issues);

            assertEquals(1, issues.size());
            assertTrue(issues.get(0),
                    issues.get(0).startsWith("SYMBOLIC_SOURCE_EVIDENCE_NOT_"
                            + "DECLARED"));
        }

        // ---------- fixtures ----------

        private static List<ConfiguredSourcePhaseContract.Occurrence> catalog() {
            JsonObject declaration = ConfiguredSourcePhaseContract.declaration(
                    ConfiguredSourcePhaseContract.Phase.PUBLISH, SOURCE_ID,
                    FIELD, METHOD, UNIT);
            JsonArray declarations = new JsonArray();
            declarations.add(declaration);
            ConfiguredSourcePhaseContract.Declaration declared =
                    ConfiguredSourcePhaseContract.declarationsOf(declarations)
                            .get(0);
            JsonArray phases = new JsonArray();
            phases.add(ConfiguredSourcePhaseContract.occurrence(declared,
                    OCCURRENCE, 1, 11L, 7L, 3L, METHOD, Arrays.asList(7L, 5L)));
            phases.add(ConfiguredSourcePhaseContract.occurrence(declared,
                    OCCURRENCE, 2, 12L, 7L, 4L, METHOD, Arrays.asList(7L, 5L)));
            return ConfiguredSourcePhaseContract.occurrencesOf(phases);
        }

        /** One replay row publishing {@code mints} mint events of one site. */
        private static ConcolicSummaryImporter.ResultRow row(String phaseId,
                                                             int mints) {
            // The mint's root carries this phase's own engine label, which is
            // what makes it this phase's mint rather than a value that only
            // travelled here.
            String raw = "M_Z_field_" + SymbolicSourceEvidence
                    .engineLabelForPhase(phaseId, SOURCE_ID) + "_1";
            JsonObject symbol = new JsonObject();
            symbol.addProperty("_type", "SymbolExpression");
            symbol.addProperty("_exp", raw);
            symbol.addProperty("_java_type", "boolean");
            JsonArray events = new JsonArray();
            for (int index = 1; index <= mints; index++) {
                events.add(SymbolicSourceEvidence.event(phaseId, SOURCE_ID,
                        OCCURRENCE, FIELD, symbol, index, false, raw, "true"));
            }
            JsonObject result = new JsonObject();
            result.addProperty("event", "CONCOLIC_REGION_RESULT");
            result.addProperty("occurrenceId", OCCURRENCE);
            result.add(SymbolicSourceEvidence.FIELD, events);
            return new ConcolicSummaryImporter.ResultRow(result, 0);
        }
    }


    static final class ConcolicSummaryImporterManualInputEvidenceTest {
        private static final String PORT = "REGION.r.in.p";
        private static final String PLANNED =
                "hdfs-17960/nn0#epoch1/region/REGION.r#1";
        private static final String RAW =
                "M_I_field_REGION.r.in.p_java/lang/Integer";

        public void concolicSummaryImporterManualInputEvidenceRules() throws Exception {
            exactMintUsesPlannedIdentityWhileReuseAndBareLabelsDoNotMint();
            anUnplannedHandoffHoldsItsBundleForTheNextEpoch();
        }

        private void exactMintUsesPlannedIdentityWhileReuseAndBareLabelsDoNotMint()
                throws Exception {
            JsonObject action = action();
            ExecutionTask task = task(action);

            List<String> firstIssues = new ArrayList<>();
            ConcolicSummaryImporter.ManualInputEvidence first = imported(task,
                    observation(action, PLANNED + "#a1", true, false), 1,
                    firstIssues);
            assertTrue(firstIssues.toString(), firstIssues.isEmpty());
            assertEquals(1, first.observations.size());
            assertEquals(1, first.sources.size());
            JsonObject firstSource = first.sources.get(0).getAsJsonObject();
            assertEquals(PORT, firstSource.get("portId").getAsString());
            assertEquals(RAW, firstSource.get("rawSymbol").getAsString());
            assertEquals(PLANNED,
                    firstSource.get("sourceOccurrenceId").getAsString());

            List<String> secondIssues = new ArrayList<>();
            ConcolicSummaryImporter.ManualInputEvidence second = imported(task,
                    observation(action, PLANNED + "#a2", true, false), 2,
                    secondIssues);
            assertTrue(secondIssues.toString(), secondIssues.isEmpty());
            assertEquals(firstSource.get("sourceIdentity").getAsString(),
                    second.sources.get(0).getAsJsonObject()
                            .get("sourceIdentity").getAsString());

            List<String> reusedIssues = new ArrayList<>();
            ConcolicSummaryImporter.ManualInputEvidence reused = imported(task,
                    observation(action, PLANNED + "#a3", false, true), 3,
                    reusedIssues);
            assertTrue(reusedIssues.toString(), reusedIssues.isEmpty());
            assertEquals(1, reused.observations.size());
            assertEquals(0, reused.sources.size());

            JsonObject bare = new JsonObject();
            bare.addProperty("symbol", PORT);
            bare.addProperty("reused", false);
            List<String> bareIssues = new ArrayList<>();
            ConcolicSummaryImporter.ManualInputEvidence ignored = imported(task,
                    bare, 4, bareIssues);
            assertFalse(bareIssues.toString(), bareIssues.isEmpty());
            assertEquals(0, ignored.observations.size());
            assertEquals(0, ignored.sources.size());

            JsonObject forged = observation(action, PLANNED + "#a5", true,
                    false);
            forged.addProperty("actionDigest", "not-the-frozen-action");
            List<String> forgedIssues = new ArrayList<>();
            ConcolicSummaryImporter.ManualInputEvidence rejected = imported(task,
                    forged, 5, forgedIssues);
            assertEquals(0, rejected.sources.size());
            assertFalse(forgedIssues.isEmpty());
        }

        private static ConcolicSummaryImporter.ManualInputEvidence imported(
                ExecutionTask task, JsonObject observation, int activation,
                List<String> issues) {
            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("schemaVersion", 1);
            raw.addProperty("taskId", "task");
            raw.addProperty("plannedOccurrenceId", PLANNED);
            raw.addProperty("occurrenceId", PLANNED + "#a" + activation);
            raw.addProperty("activationOrdinal", activation);
            raw.add("engineSummary", new JsonObject());
            JsonArray rows = new JsonArray();
            rows.add(observation);
            raw.add("symbolizedInputs", rows);
            return ConcolicSummaryImporter.manualSymbolicSourceEvidence(
                    new ConcolicSummaryImporter.ResultRow(raw, 0), task, issues);
        }

        private static JsonObject observation(JsonObject action,
                                              String occurrence,
                                              boolean minted,
                                              boolean reused) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "SymbolExpression");
            expression.addProperty("_java_type", "I");
            expression.addProperty("_exp", RAW);

            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind",
                    ConcolicSummaryImporter.MANUAL_INPUT_OBSERVATION_KIND);
            row.addProperty("authority",
                    ConcolicSummaryImporter.MANUAL_INPUT_OBSERVATION_AUTHORITY);
            row.addProperty("portId", PORT);
            row.addProperty("actionDigest", CanonicalJson.sha256(action));
            row.addProperty("plannedOccurrenceId", PLANNED);
            row.addProperty("occurrenceId", occurrence);
            row.addProperty("symbol", PORT);
            row.add("fieldPath", new JsonArray());
            row.addProperty("fieldSignature", "");
            row.add("expression", expression);
            row.addProperty("rawSymbol", RAW);
            row.addProperty("javaType", "I");
            row.addProperty("minted", minted);
            row.addProperty("reused", reused);
            return row;
        }

        private static JsonObject action() {
            JsonObject action = new JsonObject();
            action.addProperty("mode", "SYMBOLIC");
            action.addProperty("symbol", PORT);
            action.addProperty("location", "CALL_RETURN");
            action.addProperty("javaType", "int");
            return action;
        }

        /**
         * A flip that opened a wire the plan never named is a new topology.
         *
         * <p>Its bundle is kept whole and out of this epoch: the paths it
         * published are exact about a topology this epoch does not address, and
         * the anchor's own address may shift under it, so they are not this
         * epoch's evidence.  The rows name the unplanned handoff and where the
         * bundle is, and the iteration loop plans the next epoch from them --
         * where that H' is a family of its own with the one pair this bundle
         * delivered, and its v_H' decisions are obligations.</p>
         */
        private void anUnplannedHandoffHoldsItsBundleForTheNextEpoch() {
            ExecutionTask planned = task(action());
            JsonObject raw = new JsonObject();
            raw.addProperty("event", "CONCOLIC_REGION_RESULT");
            raw.addProperty("taskId", "task");
            raw.addProperty("occurrenceId", PLANNED + "#a1");
            JsonObject handoff = new JsonObject();
            handoff.addProperty("kind", "VM_HANDOFF_EVENT");
            handoff.addProperty("portId", "REGION.r.out.opened-by-the-flip");
            handoff.addProperty("handoffPhaseId", "HANDOFF_PHASE.new");
            handoff.addProperty("exportEventId", 11);
            handoff.addProperty("attachEventId", 12);
            JsonArray events = new JsonArray();
            events.add(handoff);
            raw.add("vmHandoffEvents", events);

            List<JsonObject> rows = new ArrayList<>();
            boolean divergent = ConcolicSummaryImporter.topologyDivergences(
                    new ConcolicSummaryImporter.ResultRow(raw, 0), planned, rows);

            assertTrue("the bundle must be held for the next epoch", divergent);
            List<String> details = new ArrayList<>();
            for (JsonObject row : rows) {
                assertEquals("TOPOLOGY_DIVERGENCE",
                        row.get("code").getAsString());
                details.add(row.get("detail").getAsString());
            }
            assertTrue(details.toString(), details.get(0).startsWith(
                    "UNPLANNED_HANDOFF:HANDOFF_PHASE.new"));
            assertTrue(details.toString(),
                    details.get(details.size() - 1).startsWith("BUNDLE:task"));
        }

        private static ExecutionTask task(JsonObject action) {
            JsonObject task = new JsonObject();
            task.addProperty("sourceKey", "source");
            task.addProperty("occurrenceId", PLANNED);
            task.addProperty("relationKey", "relation");
            task.addProperty("regionId", "region");
            task.addProperty("taskId", "task");
            task.addProperty("goalId", "goal");
            JsonArray actions = new JsonArray();
            actions.add(action);
            task.add("inputActions", actions);
            LoopBoundPolicy.cfgBackedges(
                    LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
            return ExecutionTask.decode(task);
        }
    }


    static final class ConcolicConstraintSolverMaterializationTest {
        public void concolicConstraintSolverMaterializationRules() throws Exception {
            materializesOccurrenceScopedBoundedScalarAction();
            materializesAnAssignmentToAValueThatArrivedOnAWire();
        }

        private void materializesOccurrenceScopedBoundedScalarAction()
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

        /**
         * A model that assigns a value which arrived on a wire is materializable.
         *
         * <p>Such a value is minted at an attach, not at a configured source and
         * not at a task input action, so it matched neither resolver and every
         * model that assigned one was refused as
         * REPLAY_CONTROL_FRONTIER_MODEL_IS_NOT_MATERIALIZABLE -- which is what
         * left bug3's one target obligation unflipped. The obligation says which
         * handoff occurrence answers it, and a handoff assignment is a
         * configured-source assignment whose phase id is that occurrence's.</p>
         */
        private void materializesAnAssignmentToAValueThatArrivedOnAWire()
                throws Exception {
            Assume.assumeTrue(z3Available());

            String raw = "M_I_field_HOFF.abcdef0123456789"
                    + "_edu/uva/liftlab/graphchecker/runtime/"
                    + "ConcolicRegionRuntime$HandoffLeafCarrier";
            String phase = "HANDOFF_PHASE.1a2b3c4d-0000-0000-0000-000000000000";
            JsonObject target = binary(symbol(raw), ">", constant(10));
            JsonObject event = new JsonObject();
            event.addProperty("eventId", 1L);
            event.addProperty("contextId", 1L);
            BranchWitness source = BranchWitness.vmPcImmutable("TEST#u1",
                    "<test.Wire: void run()>", 1, 1, false,
                    BranchPredicateAlgebra.complement(target), 0, event);

            JsonObject query = new JsonObject();
            query.addProperty("schemaVersion", 3);
            query.addProperty("kind", "REGION_PATH_FLIP");
            query.addProperty("queryKey", CanonicalJson.sha256("wire-query"));
            query.addProperty("regionId", "REGION.wire");
            query.addProperty("sourceActivationOccurrenceId",
                    "test/node#epoch0/region/REGION.wire#1#a1");
            query.add("replayContract",
                    BranchReplayContract.atSource(source).toJson());
            JsonObject context = new JsonObject();
            context.addProperty("schemaVersion", SolverPathContext.SCHEMA_VERSION);
            context.addProperty("kind", SolverPathContext.KIND);
            context.addProperty("authority", SolverPathContext.AUTHORITY);
            context.add("constraints", new JsonArray());
            query.add("solverPathContext", context);
            query.add("consumerAnchorCaseDependencies", new JsonArray());

            JsonObject activation = new JsonObject();
            activation.add("inputActions", new JsonArray());

            ConcolicConstraintSolver.Result refused =
                    ConcolicConstraintSolver.solve(query,
                            Collections.singletonList(activation), activation,
                            Paths.get("z3"), 10_000L);
            assertEquals("with no handoff row the model is not materializable",
                    "MATERIALIZATION_GAP",
                    refused.record.get("status").getAsString());

            JsonObject control = new JsonObject();
            control.addProperty("rawSymbol", raw);
            control.addProperty("handoffPhaseId", phase);
            control.addProperty("javaType", "I");
            control.addProperty("recordedValue", "7");
            JsonArray controls = new JsonArray();
            controls.add(control);
            query.add(RegionPathWorklist.HANDOFF_CONTROLS, controls);

            ConcolicConstraintSolver.Result result =
                    ConcolicConstraintSolver.solve(query,
                            Collections.singletonList(activation), activation,
                            Paths.get("z3"), 10_000L);
            assertEquals(result.record.toString(), "SAT_MODEL_READY",
                    result.record.get("status").getAsString());
            assertEquals(1, result.modelAssignments.size());
            JsonObject assignment =
                    result.modelAssignments.get(0).getAsJsonObject();
            assertEquals("SOURCE_PHASE:" + phase,
                    assignment.get("inputSymbol").getAsString());
            assertEquals(phase,
                    assignment.get("configuredSourcePhaseId").getAsString());
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

}
