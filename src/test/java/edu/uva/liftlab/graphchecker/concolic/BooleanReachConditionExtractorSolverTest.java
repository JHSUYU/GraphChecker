package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Focused authority tests for Boolean reach-condition extraction. */
public class BooleanReachConditionExtractorSolverTest {

    @Test
    public void manualTaskRootIsPublishedWithItsWitness() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray manual = new JsonArray();
        manual.add(manualBoolean());
        manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                manual);

        String smt = "(set-logic ALL)\n"
                + "(declare-const manual_enabled Bool)\n"
                + "(assert manual_enabled)\n(check-sat)\n";
        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        JsonArray roots = report.getAsJsonObject("roots")
                .getAsJsonArray("booleanInputs");
        assertEquals(1, roots.size());
        assertEquals("REGION.0.in.enabled", roots.get(0).getAsJsonObject()
                .get("portId").getAsString());
        assertTrue(report.getAsJsonArray(
                BooleanReachConditionExtractor.SYMBOLIC_VARIABLE_MODELS)
                .get(0).getAsJsonObject().getAsJsonArray("variables")
                .get(0).getAsJsonObject().get("value").getAsBoolean());
    }

    /**
     * A clock the target cannot reach without is the finding it names.
     *
     * <p>Nothing is flipped here -- the marker sits at what it recorded --
     * and the window the recording anchors the clock in is what lets the
     * comparison go the other way. The probe pins the clock back and the
     * formula dies, which is the only evidence that the move carried the
     * witness rather than accompanied it.</p>
     */
    @Test
    public void aNecessaryClockInsideItsWindowIsTheFinding() throws Exception {
        Assume.assumeTrue(z3Available());
        // A configured source, not a planted marker: nothing was injected,
        // so the run is not asked to show a flip and the clock is the whole
        // of what it claims.
        JsonObject manifest = clockManifest("true");
        manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                singleton(manualClock()));
        manifest.add(ComposedManifest
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                singleton(configuredBoolean()));
        String smt = "(set-logic ALL)\n"
                + "(declare-const sym_enabled Bool)\n"
                + "(declare-const clock_now Int)\n"
                + "(assert (and sym_enabled (> clock_now 5000)"
                + " (< clock_now 6000)))\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        JsonObject claim = report.getAsJsonObject(ClaimPolicy.CLAIM);
        JsonObject rootSpace = claim.getAsJsonObject("rootSpace");
        assertEquals(claim.getAsJsonArray("blockers").toString(),
                ClaimPolicy.SAT_CANDIDATE, claim.get("claim").getAsString());
        assertEquals(WitnessLegitimacy.CLOCK_SKEW,
                rootSpace.get("acceptedFindingKind").getAsString());
    }

    /** One Boolean marker and one wall clock, each with what it recorded. */
    private static JsonObject clockManifest(String recordedMarker) {
        JsonObject manifest = candidateManifest();
        JsonArray manual = new JsonArray();
        manual.add(manualBoolean());
        manual.add(manualClock());
        manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                manual);
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES,
                recordedRoots(recordedMarker));
        JsonObject physics = new JsonObject();
        physics.addProperty("schemaVersion", 1);
        physics.addProperty("kind", "CLOCK_ROOT_PHYSICS");
        physics.addProperty("clockSkewMillis", 300000);
        physics.add("clockReads", new JsonArray());
        manifest.add(ClockRootPhysics.MANIFEST_FIELD, physics);
        return manifest;
    }

    /** The configured Boolean root the necessary-clock fixture reads. */
    private static JsonObject configuredBoolean() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind",
                ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_KIND);
        row.addProperty("authority", ComposedManifest
                .CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY);
        row.addProperty("sourceKey", "hdfs/nn0#epoch1");
        row.addProperty("sourceId", "TEST.CONFIG.ENABLED");
        row.addProperty("sourcePhaseId", "SOURCE_PHASE.fixture");
        row.addProperty("sourceOccurrenceId",
                "node/nn0#1/region/REGION.0#1#a1");
        row.addProperty("fieldSignature", "<Test: boolean enabled>");
        row.addProperty("javaTypeDescriptor", "Z");
        row.addProperty("sort", "BOOL");
        row.addProperty("smtSort", "Bool");
        row.addProperty("solverTerm", "sym_enabled");
        row.addProperty(ComposedManifest.RECORDED_SOURCE_VALUE, "true");
        return row;
    }

    private static JsonArray singleton(JsonObject row) {
        JsonArray rows = new JsonArray();
        rows.add(row);
        return rows;
    }

    private static JsonArray recordedRoots(String recordedMarker) {
        JsonObject marker = new JsonObject();
        marker.addProperty("portId", "REGION.0.in.enabled");
        marker.addProperty("siteId", "<Test: boolean enabled>");
        marker.addProperty("recordedValue", recordedMarker);
        marker.addProperty("solverTerm", "manual_enabled");
        marker.addProperty("wallClock", false);
        JsonObject clock = new JsonObject();
        clock.addProperty("portId", "REGION.0.in.now");
        clock.addProperty("siteId", "<Test: long now>");
        clock.addProperty("recordedValue", "1000");
        clock.addProperty("solverTerm", "clock_now");
        clock.addProperty("wallClock", true);
        JsonArray rows = new JsonArray();
        rows.add(marker);
        rows.add(clock);
        return rows;
    }

    private static JsonObject manualClock() {
        JsonObject row = manualBoolean();
        row.addProperty("portId", "REGION.0.in.now");
        row.addProperty("fieldSignature", "<Test: long now>");
        row.addProperty("javaTypeDescriptor", "J");
        row.addProperty("sort", "INT");
        row.addProperty("smtSort", "Int");
        row.addProperty("solverTerm", "clock_now");
        row.addProperty("sourceIdentity", "manual-root-now");
        return row;
    }

    /** The classified witness row at one valuation ordinal. */
    private static JsonObject witnessAt(JsonObject claim, int ordinal) {
        for (com.google.gson.JsonElement element
                : claim.getAsJsonArray(WitnessLegitimacy.FINDINGS)) {
            JsonObject row = element.getAsJsonObject();
            if (row.get("valuationOrdinal").getAsInt() == ordinal) {
                return row;
            }
        }
        throw new AssertionError("no witness row at ordinal " + ordinal);
    }

    /** The one freedom code a witness row names, or "". */
    private static String freedomCode(JsonObject witness) {
        JsonArray freedoms = witness.getAsJsonArray("freedoms");
        return freedoms.size() == 0 ? ""
                : freedoms.get(0).getAsJsonObject().get("code").getAsString();
    }

    private static JsonObject candidateManifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("state", "CANDIDATE_READY");
        manifest.addProperty("guardedReadModelComplete", true);
        manifest.addProperty(ComposedManifest.FINAL_STATUS,
                ComposedManifest.FINAL_READY);
        manifest.addProperty("symbolicPropagationComplete", true);
        manifest.add("symbolicPropagationGaps", new JsonArray());
        JsonObject guardedReads = new JsonObject();
        guardedReads.addProperty("schemaVersion", 1);
        guardedReads.addProperty("kind", "DIRECT_GUARDED_READ_MODEL");
        guardedReads.addProperty("authority",
                "VM_READ_TIME_CANDIDATE_SNAPSHOT_V1");
        guardedReads.addProperty("complete", true);
        guardedReads.add("reads", new JsonArray());
        manifest.add("guardedReadModel", guardedReads);
        manifest.add("casePathConditionDependencies", new JsonArray());
        manifest.add("caseSelectorPartitions", new JsonArray());
        manifest.add("targetReachLedger", new JsonArray());
        manifest.add(ComposedManifest
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, new JsonArray());
        manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                new JsonArray());
        return manifest;
    }

    private static JsonObject manualBoolean() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind",
                ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_KIND);
        row.addProperty("authority",
                ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
        row.addProperty("portId", "REGION.0.in.enabled");
        row.addProperty("occurrenceId", "node/nn0#1/region/REGION.0#1#a1");
        row.addProperty("fieldSignature", "<Test: boolean enabled>");
        row.addProperty("javaTypeDescriptor", "Z");
        row.addProperty("sort", "BOOL");
        row.addProperty("smtSort", "Bool");
        row.addProperty("solverTerm", "manual_enabled");
        row.addProperty("sourceIdentity", "manual-root-enabled");
        row.addProperty("sourceIdentityAuthority",
                SymbolicSourceEvidence.MANUAL_AUTHORITY);
        return row;
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }

    /**
     * HDFS-17897's witness sat on its clock's own window floor: the recorded
     * read 1789234993718 with the window collapsed onto it. The probe then
     * tried 1789234993717, the solver refused it because it leaves the
     * window, and that refusal was credited as proof that the target depends
     * on the clock. It proves only that {@link ClockRootPhysics} works.
     */
    @Test
    public void windowBoundaryPerturbationIsNotFaultSensitivity()
            throws Exception {
        Assume.assumeTrue(z3Available());
        long recorded = 1789234993718L;
        JsonObject manifest = clockRootManifest(recorded, 0L);
        String smt = "(set-logic ALL)\n"
                + "(declare-const " + CLOCK_TERM + " Int)\n"
                + "(assert (and (>= " + CLOCK_TERM + " " + recorded + ")"
                + " (<= " + CLOCK_TERM + " " + recorded + ")))\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        JsonObject probe = report.getAsJsonObject("existentialRootProbe");
        assertFalse("a window-boundary refusal is not fault sensitivity",
                probe.get("constrainsRootSpace").getAsBoolean());
        JsonArray perturbations = probe.getAsJsonArray("perturbations");
        assertTrue(perturbations.size() > 0);
        boolean sawBoundary = false;
        for (int index = 0; index < perturbations.size(); index++) {
            JsonObject row = perturbations.get(index).getAsJsonObject();
            assertEquals("skipped", row.get("status").getAsString());
            assertEquals(BooleanReachConditionExtractor.WINDOW_BOUNDARY,
                    row.get("rejectedBy").getAsString());
            sawBoundary |= String.valueOf(recorded - 1L).equals(
                    row.get("perturbedValue").getAsString());
        }
        assertTrue("the 1789234993717 neighbour is named and not solved",
                sawBoundary);
        assertTrue(report.getAsJsonObject("reachCondition")
                .get("degeneracyCheck").getAsString()
                .startsWith("UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS"));
    }

    private static JsonObject readArm(String valueTerm, String owner,
                                      String carrier, String selector) {
        JsonObject arm = new JsonObject();
        arm.addProperty("selector", selector);
        arm.addProperty("valueTerm", valueTerm);
        arm.addProperty("writerCaseOwner", owner);
        arm.addProperty("sessionLocationKey", carrier);
        arm.addProperty("locationKey", carrier + "/full");
        arm.addProperty("readIdentity", "RFC.a1");
        arm.addProperty("candidateIdentity", "RFC_ARM." + selector);
        return arm;
    }

    private static final String CLOCK_TERM = "manual__clock";

    /** A manifest with one symbolized wall clock and its declared window. */
    private static JsonObject clockRootManifest(long recorded,
                                                long skewMillis) {
        JsonObject manifest = candidateManifest();
        JsonObject root = new JsonObject();
        root.addProperty("schemaVersion", 1);
        root.addProperty("kind", ComposedManifest
                .MANUAL_SOURCE_MATERIALIZATION_KIND);
        root.addProperty("authority", ComposedManifest
                .MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
        root.addProperty("portId", "REGION.clock.in.now");
        root.addProperty("occurrenceId",
                "hdfs/nn0#epoch0/region/REGION.clock#1");
        root.addProperty("javaTypeDescriptor", "J");
        root.addProperty("sort", "INT");
        root.addProperty("smtSort", "Int");
        root.addProperty("solverTerm", CLOCK_TERM);
        root.addProperty("sourceIdentity", "MANUAL.clock");
        root.addProperty("sourceIdentityAuthority",
                "PLANNED_MANUAL_SYMBOLIZATION_V1");
        JsonArray roots = new JsonArray();
        roots.add(root);
        manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                roots);

        JsonObject clockRead = new JsonObject();
        clockRead.addProperty("sourceKey", "hdfs/nn0#epoch0");
        clockRead.addProperty("portId", "REGION.clock.in.now");
        clockRead.addProperty("recordedValue", recorded);
        clockRead.addProperty("solverTerm", CLOCK_TERM);
        JsonArray clockReads = new JsonArray();
        clockReads.add(clockRead);
        manifest.add(ClockRootPhysics.MANIFEST_FIELD,
                ClockRootPhysics.manifest(skewMillis,
                        java.util.Collections.singletonList(clockRead)));
        return manifest;
    }

    /**
     * hdfs-17899-bug3's witness named ten CLOCK_SKEW rows for the polarity
     * with no fault, six of them strictly inside the window -- and the target
     * was still reachable with every clock back at its recorded value. The
     * necessity probe asks exactly that, once per named mechanism.
     */
    @Test
    public void necessaryMechanismIsTheOneThePolarityCannotDoWithout()
            throws Exception {
        Assume.assumeTrue(z3Available());
        long recorded = 1789234993718L;

        // The target needs the fault, or a clock that moved: pinning the clock
        // back to what it read leaves the no-fault polarity unsatisfiable.
        JsonObject necessary = BooleanReachConditionExtractor.extract(
                markerAndClockSmt(recorded, "(> " + CLOCK_TERM + " "
                        + recorded + ")"),
                markerAndClockManifest(recorded),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);
        assertTrue(mechanismNecessary(necessary));

        // The same shape with the clock free of the target: it moves because
        // nothing holds it, and pinning it changes nothing.
        JsonObject decoration = BooleanReachConditionExtractor.extract(
                markerAndClockSmt(recorded, "true"),
                markerAndClockManifest(recorded),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);
        assertFalse(mechanismNecessary(decoration));
    }

    private static boolean mechanismNecessary(JsonObject report) {
        JsonObject probe = report.getAsJsonObject(
                BooleanReachConditionExtractor.MECHANISM_NECESSITY);
        JsonArray rows = probe.getAsJsonArray("mechanisms");
        for (int index = 0; index < rows.size(); index++) {
            JsonObject row = rows.get(index).getAsJsonObject();
            if (!row.get("polarity").getAsBoolean()
                    && row.get("necessary").getAsBoolean()) {
                return true;
            }
        }
        return false;
    }

    private static final String MARKER_TERM = "manual__fault";

    /** Reach the target with the fault, or with {@code without} instead. */
    private static String markerAndClockSmt(long recorded, String without) {
        return "(set-logic ALL)\n"
                + "(declare-const " + MARKER_TERM + " Bool)\n"
                + "(declare-const " + CLOCK_TERM + " Int)\n"
                + "(assert (and (>= " + CLOCK_TERM + " " + (recorded - 300000L)
                + ") (<= " + CLOCK_TERM + " " + (recorded + 300000L) + ")))\n"
                + "(assert (or " + MARKER_TERM + " " + without + "))\n"
                + "(check-sat)\n";
    }

    private static JsonObject markerAndClockManifest(long recorded) {
        JsonObject manifest = clockRootManifest(recorded, 300000L);
        JsonArray roots = manifest.getAsJsonArray(ComposedManifest
                .MANUAL_SOURCE_MATERIALIZATION_FIELD);
        JsonObject marker = roots.get(0).getAsJsonObject().deepCopy();
        marker.addProperty("portId", "REGION.rpc.in.fault");
        marker.addProperty("occurrenceId",
                "hdfs/dn0#epoch0/region/REGION.rpc#1");
        marker.addProperty("javaTypeDescriptor", "Z");
        marker.addProperty("sort", "BOOL");
        marker.addProperty("smtSort", "Bool");
        marker.addProperty("solverTerm", MARKER_TERM);
        marker.addProperty("sourceIdentity", "MANUAL.fault");
        roots.add(marker);

        JsonArray ledger = new JsonArray();
        ledger.add(recordedRoot(CLOCK_TERM, Long.toString(recorded), true));
        ledger.add(recordedRoot(MARKER_TERM, "false", false));
        manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, ledger);
        return manifest;
    }

    private static JsonObject recordedRoot(String term, String value,
                                           boolean wallClock) {
        JsonObject row = new JsonObject();
        row.addProperty("solverTerm", term);
        row.addProperty("recordedValue", value);
        row.addProperty("wallClock", wallClock);
        return row;
    }

}
