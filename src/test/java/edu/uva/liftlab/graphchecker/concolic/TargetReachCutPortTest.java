package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Collections;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The target fragment behind a communication cut takes its input through the
 * cut's declared port.
 *
 * <p>README section 3's {@code T_S(Req_in, Resp_out)} is stated over the port
 * the cut declares, and that port is named after the exchange <em>site</em>:
 * it carries no region id, so the {@code <regionId>.in.} test that recognises
 * a region-minted port says nothing about it. Before this, a server fragment
 * whose only symbolic input was {@code XCH.<site>.req.p0} was refused as
 * "ambiguous target inputPorts" and no target reach query could be built for
 * any segmented case at all.</p>
 *
 * <p>The refusal it must not have weakened is the one below it: a port that
 * neither the region nor the cut mints is still not a port of this
 * occurrence.</p>
 */
public class TargetReachCutPortTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private static final String REGION = "REGION.b29f9e3d-09e2-363a-98c0-"
            + "e79910578a9e";
    private static final String OCCURRENCE = "slice/server#epoch0/region/"
            + REGION + "#1";
    private static final String GOAL = "GOAL.TARGET_REACH.12bf3876";
    private static final String METHOD = "<Server: int serve(int)>";
    private static final String TARGET_SITE = METHOD + "#u6";
    private static final String EXCHANGE_SITE =
            "XCH.dc98a244-08b8-370c-9cc0-7cc5320c0089";
    private static final String CUT_PORT =
            CommunicationCatalogContract.requestPortId(EXCHANGE_SITE, "p0");
    /** OCC-1: the read-from edge two activations of the target both record. */
    private static final String SHARED_EDGE =
            "RF.4c7de5b1-3a02-3f6b-9d21-5ba0f1e83c74";
    /** The exchange edge a replay recorded and the frozen plan lacked. */
    private static final String ABSORBED_EDGE =
            "RPC.1d5f0b6c-7a44-3e18-8c0b-2f2e5b7a91d0";
    private static final String PRODUCER_OCCURRENCE =
            "slice/client#epoch0/region/REGION.9c1a7f20-2d61-3b55-a4de-"
            + "6f30b1c8d47e#1";
    private static final String STORE_FIELD =
            "example.store.KeyStore#allKeys";
    private static final long RECEIVER = 78517L;
    private static final long OTHER_RECEIVER = 78901L;
    private static final int SLOT = -3;
    private static final int OTHER_SLOT = -4;

    @Test
    public void theDeclaredCutPortIsAdmittedAsTheTargetFragmentsInput()
            throws Exception {
        assertTrue(CUT_PORT + " must be a port the contract mints",
                CommunicationCatalogContract.declaredPortId(CUT_PORT));

        JsonObject query = build(CUT_PORT);

        assertEquals("TARGET_REACH_PATH_SET_QUERY",
                query.get("kind").getAsString());
        assertEquals("RECORDED_TARGET_PREFIX_V1",
                query.get("constraintAuthority").getAsString());
        assertEquals(1, query.getAsJsonArray("paths").size());
        JsonObject selectedPath = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(true, selectedPath
                .getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .get("outcome").getAsBoolean());
        assertEquals(false,
                selectedPath.get("desiredTakenOutcome").getAsBoolean());
        assertEquals(">", selectedPath.getAsJsonArray("constraints")
                .get(0).getAsJsonObject().get("_op").getAsString());
        assertEquals(TARGET_SITE, selectedPath.getAsJsonObject(
                TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS)
                .getAsJsonObject("site").get("siteId").getAsString());
        JsonArray admitted = query.getAsJsonObject("selectedTargetOccurrence")
                .getAsJsonArray("inputPorts");
        assertEquals(1, admitted.size());
        assertEquals(CUT_PORT, admitted.get(0).getAsString());
        assertEquals(0, query.getAsJsonArray(
                "selectedTargetBindings").size());
        assertEquals(LoopBoundPolicy.cfgBackedges(8).identity(),
                LoopBoundPolicy.decode(query).identity());
    }

    @Test
    public void aPortNeitherTheRegionNorTheCutMintsIsStillRefused()
            throws Exception {
        try {
            build("someOtherRegion.in.0f9b882a");
            fail("a port of another region must not be admitted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains(
                            "nor a declared cut port"));
        }
    }

    @Test
    public void aRegionInputPortIsStillAdmitted() throws Exception {
        JsonObject query = build(REGION + ".in.375274cb");

        assertEquals(REGION + ".in.375274cb",
                query.getAsJsonObject("selectedTargetOccurrence")
                        .getAsJsonArray("inputPorts").get(0).getAsString());
    }

    @Test
    public void aPathWithoutTheRuntimeTargetEventCannotBecomeAQuery()
            throws Exception {
        JsonObject unattested = summary();
        unattested.remove(PathObservation.TargetReachEvent.FIELD);
        try {
            build(CUT_PORT, unattested);
            fail("an unattested path must not become a target query");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "no exact source-attested target path"));
        }
    }

    @Test
    public void theRequiredRuntimeEventBecomesADirectTargetWitness()
            throws Exception {
        JsonObject opposite = summary();
        JsonObject mapping = opposite.getAsJsonArray("branchMappings")
                .get(0).getAsJsonObject();
        JsonObject witnessed = oppositePredicate();
        mapping.getAsJsonObject("witness")
                .addProperty("sourceTakenOutcome", false);
        mapping.getAsJsonObject("witness").add(
                "sourceSatisfiedPredicate", witnessed.deepCopy());
        opposite.getAsJsonArray("pathCondition").set(0,
                witnessed.deepCopy());
        opposite.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);

        JsonObject query = build(CUT_PORT, opposite);

        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(false, path.getAsJsonObject(
                PathObservation.TargetReachEvent.FIELD)
                .get("outcome").getAsBoolean());
        assertEquals(TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT,
                path.get(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE)
                        .getAsString());
        assertEquals(">", path.getAsJsonArray("constraints").get(0)
                .getAsJsonObject().get("_op").getAsString());
    }

    @Test
    public void closedWorklistStillCarriesPartialCoverageGaps()
            throws Exception {
        JsonObject partial = manifest();
        partial.addProperty("coverageState", "PARTIAL");
        JsonObject materialization = new JsonObject();
        materialization.addProperty("kind",
                "PATH_FLIP_MATERIALIZATION_GAP");
        materialization.addProperty("queryKey", "QUERY.LOCAL.PREFIX");
        JsonArray coverage = new JsonArray();
        coverage.add(materialization);
        partial.add("coverageGaps", coverage);

        JsonObject query = build(CUT_PORT, summary(), partial);

        JsonArray propagated = query.getAsJsonArray("coverageGaps");
        assertEquals(propagated.toString(), 1, propagated.size());
        JsonObject classified = propagated.get(0).getAsJsonObject();
        assertEquals(CoverageDivergence.Kind.TARGET.name(),
                classified.get("divergenceClass").getAsString());
        assertEquals("PATH_FLIP_MATERIALIZATION_GAP",
                classified.get("reason").getAsString());
        assertEquals("QUERY.LOCAL.PREFIX",
                classified.get("subject").getAsString());
        assertFalse(propagated.toString(), propagated.toString().contains(
                "TARGET_WORKLIST_NOT_CLOSED"));
    }

    @Test
    public void unsupportedFlipIsOneClassifiedTargetCoverageGap()
            throws Exception {
        JsonObject partial = manifest();
        partial.addProperty("coverageState", "SEED_ONLY");
        JsonObject unsupported = new JsonObject();
        unsupported.addProperty("kind", "UNSUPPORTED_PATH_FLIP");
        unsupported.addProperty("queryKey", "QUERY.UNSUPPORTED.PREFIX");
        unsupported.addProperty("reason", "symbolic branch is unsupported");
        JsonArray coverage = new JsonArray();
        coverage.add(unsupported);
        partial.add("coverageGaps", coverage);

        JsonArray propagated = build(CUT_PORT, summary(), partial)
                .getAsJsonArray("coverageGaps");

        assertEquals(propagated.toString(), 1, propagated.size());
        JsonObject classified = propagated.get(0).getAsJsonObject();
        assertEquals(CoverageDivergence.Kind.TARGET.name(),
                classified.get("divergenceClass").getAsString());
        assertEquals("UNSUPPORTED_PATH_FLIP",
                classified.get("reason").getAsString());
        assertEquals("QUERY.UNSUPPORTED.PREFIX",
                classified.get("subject").getAsString());
        assertEquals("symbolic branch is unsupported",
                classified.get("detail").getAsString());
        assertFalse(propagated.toString(), propagated.toString().contains(
                "TARGET_WORKLIST_NOT_CLOSED"));
    }

    @Test
    public void partialWorklistWithoutConcreteGapKeepsAggregateFinding()
            throws Exception {
        JsonObject partial = manifest();
        partial.addProperty("coverageState", "PARTIAL");

        JsonObject query = build(CUT_PORT, summary(), partial);

        JsonArray gaps = query.getAsJsonArray("coverageGaps");
        assertEquals(gaps.toString(), 1, gaps.size());
        assertEquals("TARGET_WORKLIST_NOT_CLOSED",
                gaps.get(0).getAsJsonObject().get("reason").getAsString());
    }

    @Test
    public void targetWorklistSchemaIsRequired() throws Exception {
        JsonObject missingCoverage = manifest();
        missingCoverage.remove("coverageState");
        assertManifestRejected(missingCoverage, "coverageState");

        JsonObject wrongGaps = manifest();
        wrongGaps.add("coverageGaps", new JsonObject());
        assertManifestRejected(wrongGaps, "coverageGaps");

        JsonObject wrongKind = manifest();
        wrongKind.addProperty("kind", "LEGACY_WORKLIST");
        assertManifestRejected(wrongKind, "schema");
    }

    @Test
    public void vmHandoffEvidenceRemainsOnItsTargetPath()
            throws Exception {
        JsonObject witnessed = summary();
        JsonObject attached = new JsonObject();
        attached.addProperty("_type", "SymbolExpression");
        attached.addProperty("_java_type", "I");
        attached.addProperty("_exp", "M_I_field_REMOTE.VALUE_Test");
        VmHandoffEvidence.writeTo(witnessed,
                java.util.Collections.singletonList(VmHandoffEvidence.event(
                        CUT_PORT, 41L, 42L, attached, "TASK.PRODUCER",
                        PRODUCER_OCCURRENCE)));
        witnessed.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding(), "TASK.PRODUCER"));

        JsonObject query = build(CUT_PORT, witnessed);

        assertTrue(query.toString(), !query.has(VmHandoffEvidence.FIELD));
        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(1, path.getAsJsonArray(VmHandoffEvidence.FIELD).size());
        assertEquals(41L, path.getAsJsonArray(VmHandoffEvidence.FIELD)
                .get(0).getAsJsonObject()
                .get(VmHandoffEvidence.EXPORT_EVENT_ID).getAsLong());
        // README RPC-1: the receive endpoint travels with the export, so the
        // path keeps the whole edge rather than half of it.
        assertEquals(42L, path.getAsJsonArray(VmHandoffEvidence.FIELD)
                .get(0).getAsJsonObject()
                .get(VmHandoffEvidence.ATTACH_EVENT_ID).getAsLong());
        assertEquals(ABSORBED_EDGE,
                path.getAsJsonArray(VmHandoffEvidence.FIELD)
                        .get(0).getAsJsonObject()
                        .get(VmHandoffEvidence.SELECTED_ENDPOINT_EDGE_ID)
                        .getAsString());
    }

    @Test
    public void sameLocalPrefixKeepsDistinctRpcHandoffCases()
            throws Exception {
        JsonObject first = summary();
        JsonObject second = summary();
        JsonObject firstExpression = new JsonObject();
        firstExpression.addProperty("_type", "SymbolExpression");
        firstExpression.addProperty("_java_type", "I");
        firstExpression.addProperty("_exp", "M_I_field_REMOTE_A");
        JsonObject secondExpression = new JsonObject();
        secondExpression.addProperty("_type", "SymbolExpression");
        secondExpression.addProperty("_java_type", "I");
        secondExpression.addProperty("_exp", "M_I_field_REMOTE_B");
        VmHandoffEvidence.writeTo(first, Collections.singletonList(
                VmHandoffEvidence.event(CUT_PORT, 41L, 42L,
                        firstExpression, "TASK.PRODUCER",
                        PRODUCER_OCCURRENCE)));
        VmHandoffEvidence.writeTo(second, Collections.singletonList(
                VmHandoffEvidence.event(CUT_PORT, 51L, 52L,
                        secondExpression, "TASK.PRODUCER",
                        PRODUCER_OCCURRENCE)));
        first.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding(), "TASK.PRODUCER"));
        second.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding(), "TASK.PRODUCER"));

        JsonObject query = build(CUT_PORT, Arrays.asList(first, second));

        assertEquals(query.toString(), 2,
                query.getAsJsonArray("paths").size());
        assertFalse(query.toString(), query.has("coverageGaps"));
        java.util.Set<String> producers = new java.util.LinkedHashSet<>();
        for (com.google.gson.JsonElement encoded
                : query.getAsJsonArray("paths")) {
            producers.add(encoded.getAsJsonObject()
                    .getAsJsonArray(VmHandoffEvidence.FIELD)
                    .get(0).getAsJsonObject()
                    .get(VmHandoffEvidence.PRODUCER_TASK_ID).getAsString());
        }
        assertEquals(new java.util.LinkedHashSet<>(Arrays.asList(
                "TASK.PRODUCER")), producers);
    }

    @Test
    public void aHandoffCannotInheritAnotherProducersSelectedEdge()
            throws Exception {
        JsonObject matched = summary();
        JsonObject attached = new JsonObject();
        attached.addProperty("_type", "SymbolExpression");
        attached.addProperty("_java_type", "I");
        attached.addProperty("_exp", "M_I_field_REMOTE.VALUE_Test");
        VmHandoffEvidence.writeTo(matched,
                Collections.singletonList(VmHandoffEvidence.event(
                        CUT_PORT, 31L, 32L, attached, "TASK.PRODUCER",
                        PRODUCER_OCCURRENCE)));
        matched.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding(), "TASK.PRODUCER"));

        JsonObject witnessed = summary();
        VmHandoffEvidence.writeTo(witnessed,
                Collections.singletonList(VmHandoffEvidence.event(
                        CUT_PORT, 41L, 42L, attached, "TASK.OTHER",
                        "slice/other#epoch0/region/R#1")));
        witnessed.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding(), "TASK.PRODUCER"));

        JsonObject query = build(CUT_PORT,
                Arrays.asList(matched, witnessed));

        assertEquals(query.toString(), 1,
                query.getAsJsonArray("paths").size());
        assertEquals("TASK.PRODUCER", query.getAsJsonArray("paths")
                .get(0).getAsJsonObject()
                .getAsJsonArray(VmHandoffEvidence.FIELD)
                .get(0).getAsJsonObject()
                .get(VmHandoffEvidence.PRODUCER_TASK_ID).getAsString());
        assertTrue(query.toString(), query.getAsJsonArray("coverageGaps")
                .toString().contains(
                        "TARGET_PATH_HANDOFF_ENDPOINT_NOT_SELECTED"));
    }

    @Test
    public void sharedStateEvidenceRemainsOnItsTargetPath()
            throws Exception {
        JsonObject witnessed = summary();
        JsonObject recorded = new JsonObject();
        recorded.addProperty("pathLocalMarker", "TARGET.REPLAY.ONE");
        witnessed.add(SharedStateEvidence.RECORDED_FIELD, recorded);

        JsonObject query = build(CUT_PORT, witnessed);

        assertTrue(query.toString(), !query.has(
                SharedStateEvidence.RECORDED_FIELD));
        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals("TARGET.REPLAY.ONE", path.getAsJsonObject(
                        SharedStateEvidence.RECORDED_FIELD)
                .get("pathLocalMarker").getAsString());
    }

    @Test
    public void loopEvidenceRemainsOnItsTargetPath() throws Exception {
        JsonObject witnessed = summary();
        JsonObject count = new JsonObject();
        count.addProperty(LoopBoundPolicy.LOOP_SITE_ID,
                METHOD + "#u2");
        count.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, 2);
        JsonArray counts = new JsonArray();
        counts.add(count);
        witnessed.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        JsonObject gap = new JsonObject();
        gap.addProperty("reason",
                LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS);
        gap.addProperty("subject", METHOD + "#u4");
        gap.addProperty("detail", "focused target loop evidence");
        JsonArray gaps = new JsonArray();
        gaps.add(gap);
        witnessed.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS, gaps);

        JsonObject query = build(CUT_PORT, witnessed);

        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(counts,
                path.getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNTS));
        assertEquals(gaps,
                path.getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS));
    }

    @Test
    public void loopPolicyDisagreementIsRefused() throws Exception {
        JsonObject seed = seedQuery(CUT_PORT);
        LoopBoundPolicy.cfgBackedges(8,
                Collections.singletonMap(METHOD + "#u2", 3))
                .writeTo(seed);
        try {
            build(CUT_PORT, summary(), manifest(), seed);
            fail("different target loop authorities must not be merged");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "same loopBound authority"));
        }
    }

    @Test
    public void repeatedTargetPathsDeduplicateTheSameConfiguredSource()
            throws Exception {
        JsonObject first = summary();
        JsonObject second = summary();
        JsonObject source = configuredSource("M_J_field_", 7L);
        SymbolicSourceEvidence.writeTo(first,
                Collections.singletonList(source));
        SymbolicSourceEvidence.writeTo(second,
                Collections.singletonList(source.deepCopy()));

        JsonObject query = build(CUT_PORT, Arrays.asList(first, second));

        assertEquals(1, SymbolicSourceEvidence.eventsOf(query).size());
    }

    @Test
    public void targetPathsCannotDisagreeOnOneConfiguredSourcePhase()
            throws Exception {
        JsonObject first = summary();
        JsonObject second = summary();
        SymbolicSourceEvidence.writeTo(first, Collections.singletonList(
                configuredSource("M_J_field_", 7L)));
        SymbolicSourceEvidence.writeTo(second, Collections.singletonList(
                configuredSource("M_J_field_", 9L)));
        try {
            build(CUT_PORT, Arrays.asList(first, second));
            fail("one source phase may not carry two expressions");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "disagree on exact configured source phase"));
        }
    }

    @Test
    public void summaryLoopPolicyDisagreementIsRefused() throws Exception {
        JsonObject witnessed = summary();
        LoopBoundPolicy.cfgBackedges(8,
                Collections.singletonMap(METHOD + "#u2", 3))
                .writeTo(witnessed);
        try {
            build(CUT_PORT, witnessed);
            fail("a summary from another loop policy must not be admitted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "same loopBound authority"));
        }
    }

    @Test
    public void twoActivationsOfOneLocationAreOneRuntimeBinding()
            throws Exception {
        JsonObject query = buildActivations(
                activation(1, location(1, RECEIVER, SLOT)),
                activation(2, location(2, RECEIVER, SLOT)));

        JsonArray bound = query.getAsJsonArray("selectedTargetBindings");
        assertEquals(bound.toString(), 1, bound.size());
        // The recorded name travels as recorded: only the comparison reads
        // the location at its planned address.
        assertEquals(location(1, RECEIVER, SLOT),
                bound.get(0).getAsJsonObject().get("locationKey")
                        .getAsString());
    }

    @Test
    public void activationsOnDifferentReceiversAreStillContested()
            throws Exception {
        assertContested(activation(1, location(1, RECEIVER, SLOT)),
                activation(2, location(2, OTHER_RECEIVER, SLOT)));
    }

    @Test
    public void activationsOnDifferentSlotsAreStillContested()
            throws Exception {
        assertContested(activation(1, location(1, RECEIVER, SLOT)),
                activation(2, location(2, RECEIVER, OTHER_SLOT)));
    }

    @Test
    public void activationsThatDisagreeOffTheLocationAreStillContested()
            throws Exception {
        JsonObject second = activation(2, location(2, RECEIVER, SLOT));
        second.getAsJsonArray("edgeBindings").get(0).getAsJsonObject()
                .addProperty("primitiveValue", "13");
        assertContested(activation(1, location(1, RECEIVER, SLOT)), second);
    }

    @Test
    public void theSessionLocalNameIsStillNotCompared() throws Exception {
        JsonObject second = activation(2, location(2, RECEIVER, SLOT));
        second.getAsJsonArray("edgeBindings").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.SESSION_LOCATION_FIELD,
                        "MAP_STATE/611#-3");

        JsonArray bound = buildActivations(
                activation(1, location(1, RECEIVER, SLOT)), second)
                .getAsJsonArray("selectedTargetBindings");

        assertEquals(bound.toString(), 1, bound.size());
    }

    /**
     * An exchange pairing a replay recorded and the scheduler absorbed is
     * demand this ledger cannot hold: the ledger is what the baseline
     * discovery saw, and the absorbed pairing is what it did not.  It is
     * still published, so composition sees the producer the VM named rather
     * than the one the frozen plan guessed.
     */
    @Test
    public void anAbsorbedPairingIsDemandTheLedgerNeedNotHold()
            throws Exception {
        JsonObject summary = summary();
        summary.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding()));

        JsonArray bound = build(CUT_PORT, summary)
                .getAsJsonArray("selectedTargetBindings");

        assertEquals(bound.toString(), 1, bound.size());
        JsonObject row = bound.get(0).getAsJsonObject();
        assertEquals(ABSORBED_EDGE, row.get("edgeId").getAsString());
        assertTrue(row.toString(), VmHandoffEvidence.absorbed(row));
    }

    /** Without the stamps the same row is a ledger the plan grew on its own. */
    @Test
    public void anUnstampedPairingOutsideTheLedgerIsStillRefused()
            throws Exception {
        assertLedgerRefused(exchangeBinding());
    }

    /** Three of the four stamps state no send and no receive, so they decide
     * nothing: the row is judged as any other binding. */
    @Test
    public void aPartiallyStampedPairingIsStillRefused() throws Exception {
        JsonObject noAttach = absorbed(exchangeBinding());
        noAttach.remove(VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID);
        assertLedgerRefused(noAttach);

        JsonObject noExport = absorbed(exchangeBinding());
        noExport.remove(VmHandoffEvidence.ABSORBED_EXPORT_EVENT_ID);
        assertLedgerRefused(noExport);

        JsonObject noTask = absorbed(exchangeBinding());
        noTask.addProperty(VmHandoffEvidence.ABSORBED_FROM_TASK_ID, "");
        assertLedgerRefused(noTask);

        JsonObject otherAuthority = absorbed(exchangeBinding());
        otherAuthority.addProperty(
                VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD, "SOMETHING_ELSE");
        assertLedgerRefused(otherAuthority);
    }

    private void assertLedgerRefused(JsonObject binding) throws Exception {
        JsonObject summary = summary();
        summary.getAsJsonArray("edgeBindings").add(binding);
        try {
            build(CUT_PORT, summary);
            fail("a binding outside the demand ledger must be refused");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "selected target demand ledger does not exactly cover"));
        }
    }

    /** One traced exchange row feeding the selected occurrence's cut port. */
    private static JsonObject exchangeBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", ABSORBED_EDGE);
        binding.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        binding.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        binding.addProperty("fromOutputPort", CUT_PORT);
        binding.addProperty("toOccurrenceId", OCCURRENCE);
        binding.addProperty("toInputPort", CUT_PORT);
        return binding;
    }

    /** The four fields that re-derive one row from the carry file. */
    private static JsonObject absorbed(JsonObject binding) {
        return absorbed(binding, "TASK.SEED.PRODUCER");
    }

    private static JsonObject absorbed(JsonObject binding,
                                       String producerTaskId) {
        binding.addProperty(VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD,
                VmHandoffEvidence.ABSORBED_AUTHORITY);
        binding.addProperty(VmHandoffEvidence.ABSORBED_FROM_TASK_ID,
                producerTaskId);
        binding.addProperty(VmHandoffEvidence.ABSORBED_EXPORT_EVENT_ID, 217L);
        binding.addProperty(VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID, 220L);
        return binding;
    }

    private void assertContested(JsonObject first, JsonObject second)
            throws Exception {
        try {
            buildActivations(first, second);
            fail("two locations must not be read as one");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "binding " + SHARED_EDGE + " has no runtime evidence"));
        }
    }

    private JsonObject buildActivations(JsonObject first, JsonObject second)
            throws IOException {
        JsonObject seed = seedQuery(CUT_PORT);
        JsonArray demanded = new JsonArray();
        demanded.add(SHARED_EDGE);
        seed.getAsJsonObject("selectedTargetOccurrence")
                .add("bindingIds", demanded);
        return build(CUT_PORT, Arrays.asList(first, second), manifest(),
                seed);
    }

    /** One activation of the selected occurrence reading {@code location}. */
    private static JsonObject activation(int ordinal, String location) {
        JsonObject row = summary();
        row.addProperty("occurrenceId", OCCURRENCE + "#a" + ordinal);
        row.addProperty(PathObservation.ACTIVATION_ORDINAL, ordinal);
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", SHARED_EDGE);
        binding.addProperty("kind", "RUNTIME_FIELD_FLOW");
        binding.addProperty("toOccurrenceId", OCCURRENCE);
        binding.addProperty("toInputPort", CUT_PORT);
        binding.addProperty("locationKey", location);
        binding.addProperty(SharedStateEvidence.SESSION_LOCATION_FIELD,
                "MAP_STATE/229#-3");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        row.add("edgeBindings", bindings);
        return row;
    }

    /** The canonical name one activation records for a map's whole state. */
    private static String location(int ordinal, long receiver, int slot) {
        return "MAP_STATE/" + OCCURRENCE + "#a" + ordinal + "@receiver:"
                + receiver + "@" + STORE_FIELD + "#" + slot;
    }

    private JsonObject build(String inputPort) throws IOException {
        return build(inputPort, summary());
    }

    private JsonObject build(String inputPort, JsonObject summary)
            throws IOException {
        return build(inputPort, summary, manifest());
    }

    private JsonObject build(String inputPort, JsonObject summary,
                             JsonObject pathManifest) throws IOException {
        return build(inputPort, summary, pathManifest,
                seedQuery(inputPort));
    }

    private void assertManifestRejected(JsonObject pathManifest,
                                        String message) throws Exception {
        try {
            build(CUT_PORT, summary(), pathManifest);
            fail("malformed target worklist was accepted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains(message));
        }
    }

    private JsonObject build(String inputPort, JsonObject summary,
                             JsonObject pathManifest, JsonObject seedQuery)
            throws IOException {
        return build(inputPort, Collections.singletonList(summary),
                pathManifest, seedQuery);
    }

    private JsonObject build(String inputPort, List<JsonObject> summaries)
            throws IOException {
        return build(inputPort, summaries, manifest(), seedQuery(inputPort));
    }

    private JsonObject build(String inputPort, List<JsonObject> summaryRows,
                             JsonObject pathManifest, JsonObject seedQuery)
            throws IOException {
        File root = folder.newFolder(Integer.toHexString(
                31 * inputPort.hashCode() + summaryRows.hashCode()
                        + pathManifest.hashCode() + seedQuery.hashCode()));
        File manifest = new File(root, "path_closure.json");
        File seed = new File(root, "branch_queries.jsonl");
        File summaries = new File(root, "observed_path_summaries.jsonl");
        File output = new File(root, "reach_query.jsonl");
        write(manifest, pathManifest);
        write(seed, seedQuery);
        write(summaries, summaryRows);
        return TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", summaries.getAbsolutePath(),
                        "--path-manifest", manifest.getAbsolutePath(),
                        "--seed-query", seed.getAbsolutePath(),
                        "--output", output.getAbsolutePath()}));
    }

    private static void write(File file, JsonObject row) throws IOException {
        Files.write(file.toPath(),
                (JSON.toJson(row) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static void write(File file, List<JsonObject> rows)
            throws IOException {
        StringBuilder encoded = new StringBuilder();
        for (JsonObject row : rows) {
            encoded.append(JSON.toJson(row)).append(System.lineSeparator());
        }
        Files.write(file.toPath(), encoded.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static JsonObject configuredSource(String rawPrefix,
                                                long constant) {
        String phase = "SOURCE_PHASE.target-local";
        String sourceId = "TARGET.LOCAL";
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "J");
        expression.addProperty("_exp", rawPrefix
                + SymbolicSourceEvidence.engineLabelForPhase(
                phase, sourceId) + "_Target_" + constant);
        return SymbolicSourceEvidence.event(phase, sourceId, OCCURRENCE,
                "<Target: long local>", expression, 1, false, null);
    }

    private static JsonObject manifest() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "REGION_PATH_WORKLIST");
        row.addProperty("state", "CLOSED");
        row.addProperty("coverageState", "CLOSED");
        row.add("gaps", new JsonArray());
        row.add("coverageGaps", new JsonArray());
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("regionId", REGION);
        row.addProperty("goalId", GOAL);
        row.addProperty("occurrenceId", OCCURRENCE);
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);
        return row;
    }

    private static JsonObject seedQuery(String inputPort) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        row.addProperty("readyForSolver", true);
        row.addProperty("queryKey", "QUERY.TARGET.CUT.PORT");
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty("sourceKey", "slice/server#epoch0");
        row.addProperty("targetSiteId", TARGET_SITE);
        row.addProperty("fatalRequiredTakenOutcome", false);
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);

        JsonObject contract = new JsonObject();
        contract.addProperty("kind", "BINARY_BRANCH_REPLAY_CONTRACT");
        contract.addProperty("schemaVersion", 2);
        contract.add("orderedPrefix", new JsonArray());
        contract.add("source", witness(TARGET_SITE, 6, true));
        row.add("replayContract", contract);

        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", OCCURRENCE);
        row.add("symbolicContext", context);

        JsonObject selected = new JsonObject();
        selected.addProperty("occurrenceId", OCCURRENCE);
        JsonArray ports = new JsonArray();
        ports.add(inputPort);
        selected.add("inputPorts", ports);
        selected.add("bindingIds", new JsonArray());
        row.add("selectedTargetOccurrence", selected);
        return row;
    }

    private static JsonObject summary() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("regionId", REGION);
        row.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, OCCURRENCE);
        row.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        row.addProperty("occurrenceId", OCCURRENCE + "#a1");
        row.addProperty("goalId", GOAL);
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("relationallyComplete", true);
        row.addProperty("taskId", "TASK.SEED.TARGET");
        row.addProperty("sourceKey", "slice/server#epoch0");
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("kind", "CFG_BACKEDGE");
        loopBound.addProperty("scope", "ALL_EXECUTION_SCOPE_LOOPS");
        loopBound.addProperty("maxBackedgeTraversals", 8);
        loopBound.addProperty("onLimit", "CUT_PATH");
        row.add("loopBound", loopBound);
        JsonArray pathCondition = new JsonArray();
        pathCondition.add(predicate());
        row.add("pathCondition", pathCondition);
        JsonObject mapping = new JsonObject();
        mapping.addProperty("policy", "EXPLORE");
        mapping.addProperty("summaryPcIndex", 0);
        mapping.add("witness", witness(TARGET_SITE, 6, true));
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        row.add("branchMappings", mappings);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", TARGET_SITE);
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        row.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        row.add("edgeBindings", new JsonArray());
        row.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        return row;
    }

    private static JsonObject witness(String siteId, int unitIndex,
                                      boolean outcome) {
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
        witness.add("sourceSatisfiedPredicate", predicate());
        witness.addProperty("sourceTakenOutcome", outcome);
        witness.addProperty("vmPcIndex", 0);
        return witness;
    }

    /** {@code Req_in <= 20}, stated over the declared cut port's symbol. */
    private static JsonObject predicate() {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_field_" + CUT_PORT
                + "_java/lang/Integer");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_20");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_code_position", METHOD + ":149");
        predicate.add("_left", left);
        predicate.addProperty("_op", "<=");
        predicate.add("_right", right);
        return predicate;
    }

    private static JsonObject oppositePredicate() {
        JsonObject result = predicate();
        result.addProperty("_op", ">");
        return result;
    }
}
