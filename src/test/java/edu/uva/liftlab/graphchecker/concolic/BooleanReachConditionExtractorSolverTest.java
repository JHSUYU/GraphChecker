package edu.uva.liftlab.graphchecker.concolic;

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
    public void caseOwnerAcceptsPhysicalOrPlannedOccurrence() {
        String region = "REGION.target";
        String planned = "hdfs/nn0#epoch1/region/REGION.target#2";
        String physical = planned + "#a1";
        String plannedOwner = LocalCaseIdentity.owner(
                region, planned, "TARGET_PATH.0", 0);
        String physicalOwner = LocalCaseIdentity.owner(
                region, physical, "TARGET_PATH.0", 0);

        assertTrue(BooleanReachConditionExtractor.caseOwnerMatchesOccurrence(
                plannedOwner, region, physical));
        assertTrue(BooleanReachConditionExtractor.caseOwnerMatchesOccurrence(
                physicalOwner, region, physical));
        assertFalse(BooleanReachConditionExtractor.caseOwnerMatchesOccurrence(
                plannedOwner, region, planned + "0#a1"));

    }

    @Test
    public void targetArmUsesTargetLedgerAuthority() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        String region = "REGION.target";
        String planned = "hdfs/nn0#epoch1/region/REGION.target#2";
        String owner = LocalCaseIdentity.owner(
                region, planned, "TARGET_PATH.0", 0);
        String selector = LocalCaseIdentity.selector(owner);

        JsonObject arm = new JsonObject();
        arm.addProperty("selector", selector);
        arm.addProperty("caseOwner", owner);
        arm.addProperty("caseSelector", selector);
        arm.addProperty("regionId", region);
        arm.addProperty("occurrenceId", planned + "#a1");
        arm.add("pathCondition", new JsonArray());
        JsonObject dependency = new JsonObject();
        dependency.addProperty("schemaVersion",
                SymbolicPropagationClosure.SCHEMA_VERSION);
        dependency.addProperty("kind",
                SymbolicPropagationClosure.DEPENDENCY_KIND);
        dependency.addProperty("authority", "REGION_CASE_PC_V1");
        dependency.addProperty(VmExpressionIr.FAMILY_KEY, "CBF.target");
        dependency.addProperty("boundaryKind", VmExpressionIr.FIELD_READ);
        dependency.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                "iteration-0000");
        JsonArray arms = new JsonArray();
        arms.add(arm);
        dependency.add("arms", arms);
        JsonArray dependencies = new JsonArray();
        dependencies.add(dependency);
        manifest.add("casePathConditionDependencies", dependencies);

        JsonObject target = new JsonObject();
        target.addProperty("caseGuard", selector);
        JsonArray targetLedger = new JsonArray();
        targetLedger.add(target);
        manifest.add("targetReachLedger", targetLedger);

        String smt = "(set-logic ALL)\n"
                + "(declare-const " + selector + " Bool)\n"
                + "(assert (! (=> " + selector + " true) :named "
                + "target_path_selector_definition_0))\n"
                + "(assert " + selector + ")\n(check-sat)\n";
        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        assertEquals(0, report.getAsJsonArray("gaps").size());
        // Every report carries the one claim decided from it, so no caller
        // can read a reach condition without the verdict it justifies.
        assertEquals("CAMPAIGN_CLAIM",
                report.getAsJsonObject(ClaimPolicy.CLAIM).get("kind")
                        .getAsString());
    }

    @Test
    public void unusedInitialReadArmRequiresNoSelectorDeclaration()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        String digest = CanonicalJson.sha256("initial-source");
        String owner = SymbolicPropagationClosure
                .INITIAL_SOURCE_CASE_PREFIX + digest;
        String region = SymbolicPropagationClosure
                .INITIAL_SOURCE_CASE_PREFIX
                + CanonicalJson.sha256("initial-location");
        String selector = LocalCaseIdentity.selector(owner);

        JsonObject arm = new JsonObject();
        arm.addProperty("selector", selector);
        arm.addProperty("caseOwner", owner);
        arm.addProperty("caseSelector", selector);
        arm.addProperty("regionId", region);
        arm.addProperty("occurrenceId", owner);
        arm.add("pathCondition", new JsonArray());
        JsonArray arms = new JsonArray();
        arms.add(arm);
        JsonObject dependency = new JsonObject();
        dependency.addProperty("schemaVersion",
                SymbolicPropagationClosure.SCHEMA_VERSION);
        dependency.addProperty("kind",
                SymbolicPropagationClosure.DEPENDENCY_KIND);
        dependency.addProperty("authority", "REGION_CASE_PC_V1");
        dependency.addProperty(VmExpressionIr.FAMILY_KEY, "CBF.initial");
        dependency.addProperty("boundaryKind", VmExpressionIr.FIELD_READ);
        dependency.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                "iteration-0000");
        dependency.addProperty("selectionPolicy",
                SymbolicPropagationClosure.READ_FROM_DEPENDENCY_POLICY);
        dependency.add("arms", arms);
        JsonArray dependencies = new JsonArray();
        dependencies.add(dependency);
        manifest.add("casePathConditionDependencies", dependencies);

        String smt = "(set-logic ALL)\n(check-sat)\n";
        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        assertEquals(0, report.getAsJsonArray("gaps").size());
    }

    @Test
    public void observationArmsMayBelongToDifferentOccurrencePartitions()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray dependencyArms = new JsonArray();
        JsonArray partitions = new JsonArray();
        StringBuilder smt = new StringBuilder("(set-logic ALL)\n");
        for (int index = 1; index <= 2; index++) {
            String region = "REGION.producer." + index;
            String occurrence = "hdfs/nn" + index
                    + "#epoch1/region/" + region + "#1#a1";
            String owner = LocalCaseIdentity.owner(region,
                    occurrence, "LOCAL_CASE." + index, 0);
            String base = LocalCaseIdentity.selector(owner);
            String observation = "case_observation__fixture_" + index;

            JsonObject arm = new JsonObject();
            arm.addProperty("selector", observation);
            arm.addProperty("caseSelector", base);
            arm.addProperty("caseOwner", owner);
            arm.addProperty("regionId", region);
            arm.addProperty("occurrenceId", occurrence);
            arm.addProperty(SymbolicPropagationClosure.OBSERVATION_SELECTOR,
                    observation);
            arm.add("pathCondition", new JsonArray());
            dependencyArms.add(arm);

            JsonArray partition = new JsonArray();
            partition.add(base);
            partitions.add(partition);
            smt.append("(declare-const ").append(base)
                    .append(" Bool)\n(declare-const ").append(observation)
                    .append(" Bool)\n")
                    .append("(assert (! (=> ").append(observation)
                    .append(" true) :named case_selector_definition_")
                    .append(index).append("))\n")
                    .append("(assert (! (= (+ (ite ").append(observation)
                    .append(" 1 0)) (ite ").append(base)
                    .append(" 1 0)) :named region_case_observation_partition_")
                    .append(base).append("))\n")
                    .append("(assert ").append(base).append(")\n");
        }
        smt.append("(check-sat)\n");

        JsonObject dependency = new JsonObject();
        dependency.addProperty("schemaVersion",
                SymbolicPropagationClosure.SCHEMA_VERSION);
        dependency.addProperty("kind",
                SymbolicPropagationClosure.DEPENDENCY_KIND);
        dependency.addProperty("authority", "REGION_CASE_PC_V1");
        dependency.addProperty(VmExpressionIr.FAMILY_KEY,
                "CBF.concurrent-read");
        dependency.addProperty("boundaryKind", VmExpressionIr.FIELD_READ);
        dependency.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                "iteration-0000");
        dependency.add("arms", dependencyArms);
        JsonArray dependencies = new JsonArray();
        dependencies.add(dependency);
        manifest.add("casePathConditionDependencies", dependencies);
        manifest.add("caseSelectorPartitions", partitions);

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt.toString(), manifest,
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, partitions, 1), 8, 64);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        assertEquals(0, report.getAsJsonArray("gaps").size());
    }

    @Test
    public void manualTaskRootIsPublishedWithItsWitness() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray manual = new JsonArray();
        manual.add(manualBoolean());
        manifest.add(ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_FIELD,
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

    @Test
    public void unconstrainedManualRootRefusesCandidateAuthority()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray manual = new JsonArray();
        manual.add(manualBoolean());
        manifest.add(ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                manual);

        String smt = "(set-logic ALL)\n"
                + "(declare-const manual_enabled Bool)\n"
                + "(assert true)\n(check-sat)\n";
        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        assertEquals("REACHABLE", report.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());
        assertEquals("DEGENERATE_UNCONSTRAINED_ROOT_SPACE",
                report.getAsJsonObject("reachCondition")
                        .get("degeneracyCheck").getAsString());
        assertEquals("CANDIDATE_WITH_GAPS",
                report.get("state").getAsString());
        assertEquals("DEGENERATE_UNCONSTRAINED_ROOT_SPACE",
                report.getAsJsonArray("gaps").get(0).getAsString());
        assertEquals(2, report.getAsJsonArray("valuations").size());
    }

    @Test
    public void reusedActionsAliasOneVmRoot() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonObject first = manualBoolean();
        first.addProperty("sourceIdentity", "manual-action-first");
        first.addProperty("sourceIdentityAuthority",
                ConcolicSummaryImporter.MANUAL_INPUT_OBSERVATION_AUTHORITY);
        first.addProperty(SymbolicSourceEvidence.REUSED, true);
        JsonObject second = first.deepCopy();
        second.addProperty("portId", "REGION.1.in.enabled");
        second.addProperty("occurrenceId",
                "node/nn0#1/region/REGION.1#1#a1");
        second.addProperty("sourceIdentity", "manual-action-second");
        JsonArray manual = new JsonArray();
        manual.add(first);
        manual.add(second);
        manifest.add(ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_FIELD,
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
        assertEquals(2, roots.get(0).getAsJsonObject()
                .getAsJsonArray("aliases").size());
    }

    private static JsonObject candidateManifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("state", "CANDIDATE_READY");
        manifest.addProperty("guardedReadModelComplete", true);
        manifest.addProperty(ConcolicSmtComposer.FINAL_STATUS,
                ConcolicSmtComposer.FINAL_READY);
        manifest.addProperty("symbolicPropagationComplete", true);
        manifest.add("symbolicPropagation", new JsonArray());
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
        manifest.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, new JsonArray());
        manifest.add(ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                new JsonArray());
        return manifest;
    }

    private static JsonObject manualBoolean() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind",
                ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_KIND);
        row.addProperty("authority",
                ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
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

    /** A rejection the formula itself makes, inside the window, still counts. */
    @Test
    public void inWindowPerturbationStillProvesSensitivity()
            throws Exception {
        Assume.assumeTrue(z3Available());
        long recorded = 1789234993718L;
        JsonObject manifest = clockRootManifest(recorded, 300000L);
        String smt = "(set-logic ALL)\n"
                + "(declare-const " + CLOCK_TERM + " Int)\n"
                + "(assert (and (>= " + CLOCK_TERM + " " + (recorded - 300000L)
                + ") (<= " + CLOCK_TERM + " " + (recorded + 300000L) + ")))\n"
                + "(assert (= " + CLOCK_TERM + " " + recorded + "))\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        JsonObject probe = report.getAsJsonObject("existentialRootProbe");
        assertTrue("an in-window rejection is the formula's own",
                probe.get("constrainsRootSpace").getAsBoolean());
        assertEquals("CONSTRAINED_ROOT_SPACE",
                report.getAsJsonObject("reachCondition")
                        .get("degeneracyCheck").getAsString());
    }

    /**
     * The fatal predicate's value comes from one guarded read, and which of
     * that read's arms supplied it is what tells an initial-state hole from a
     * reconstructed write.
     */
    @Test
    public void fatalReadArmsResolveThroughTheBoundaryBinding() {
        String value = "rf_value__RFC_a1__b2";
        JsonObject manifest = candidateManifest();
        JsonObject read = new JsonObject();
        read.addProperty("readIdentity", "RFC.a1");
        JsonArray arms = new JsonArray();
        arms.add(readArm(value, "INITIAL_SOURCE.deadbeef", "MAP_STATE/7#-3",
                "read_selector__initial"));
        arms.add(readArm(value, "region:REGION.writer", "MAP_STATE/7#-3",
                "read_selector__writer"));
        arms.add(readArm("rf_value__RFC_other__c3", "region:REGION.other",
                "MAP_STATE/9#-3", "read_selector__unrelated"));
        read.add("arms", arms);
        JsonArray reads = new JsonArray();
        reads.add(read);
        manifest.getAsJsonObject("guardedReadModel").add("reads", reads);
        String smt = "(declare-const merged_boundary__f0 Ref)\n"
                + "(assert (= merged_boundary__f0 " + value + "))\n"
                + "(assert (! (= merged_boundary__f0 nullRef)"
                + " :named fatal_path))\n";

        java.util.List<JsonObject> resolved = BooleanReachConditionExtractor
                .fatalReadArms(smt, manifest);

        assertEquals(2, resolved.size());
        assertEquals("read_selector__initial",
                resolved.get(0).get("selector").getAsString());
        assertTrue(resolved.get(0).get("initialState").getAsBoolean());
        assertFalse(resolved.get(1).get("initialState").getAsBoolean());
        assertEquals("MAP_STATE/7#-3",
                resolved.get(0).get("sessionLocationKey").getAsString());
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
        root.addProperty("kind", ConcolicSmtComposer
                .MANUAL_SOURCE_MATERIALIZATION_KIND);
        root.addProperty("authority", ConcolicSmtComposer
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
        manifest.add(ConcolicSmtComposer.MANUAL_SOURCE_MATERIALIZATION_FIELD,
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
        JsonArray roots = manifest.getAsJsonArray(ConcolicSmtComposer
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
        manifest.add(ConcolicSmtComposer.RECORDED_ROOT_VALUES, ledger);
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


    /**
     * A composition the Composer refused is still solved, because the
     * valuations and the arm the model picks are how anyone finds out why it
     * was refused. What it may never do is carry authority: the report stays
     * CANDIDATE_WITH_GAPS, keeps the eligibility gap, and every row it
     * publishes says so.
     */
    @Test
    public void aRefusedCompositionIsSolvedForEvidenceOnly() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        manifest.addProperty("state", "CANDIDATE_WITH_GAPS");
        manifest.addProperty(ConcolicSmtComposer.FINAL_STATUS,
                "FINAL_REFUSED");
        // A refusal fails the formula closed, so without lifting that marker
        // every valuation of it is unsat and answers nothing.
        String smt = "(set-logic ALL)\n(declare-const x Int)\n"
                + "(assert (> x 0))\n"
                + "(assert false) ; fail closed: unsupported\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        assertTrue(report.get(BooleanReachConditionExtractor.EVIDENCE_ONLY)
                .getAsBoolean());
        assertEquals(1, report.get("failClosedMarkersLifted").getAsInt());
        // Solved, and the valuation is real rather than the refusal's own.
        assertEquals(1, report.getAsJsonArray("valuations").size());
        JsonObject valuation = report.getAsJsonArray("valuations").get(0)
                .getAsJsonObject();
        assertEquals("sat", valuation.get("status").getAsString());
        assertTrue(valuation.get(BooleanReachConditionExtractor.EVIDENCE_ONLY)
                .getAsBoolean());
        // And it can never be believed.
        assertEquals("CANDIDATE_WITH_GAPS", report.get("state").getAsString());
        assertTrue(report.getAsJsonArray("gaps").toString().contains(
                "COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE"));
        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                report.getAsJsonObject(ClaimPolicy.CLAIM).get("claim")
                        .getAsString());
        assertEquals(ClaimPolicy.COMPOSER_NOT_FINAL_READY,
                report.getAsJsonObject(ClaimPolicy.CLAIM)
                        .getAsJsonArray("blockers").get(0).getAsJsonObject()
                        .get("code").getAsString());
    }

    /** A composition nobody refused keeps its fail-closed marker. */
    @Test
    public void anEligibleCompositionKeepsItsFailClosedMarker()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String smt = "(set-logic ALL)\n(declare-const x Int)\n"
                + "(assert (> x 0))\n"
                + "(assert false) ; fail closed: unsupported\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                candidateManifest(),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L, new JsonArray(), 1), 8, 64);

        assertFalse(report.get(BooleanReachConditionExtractor.EVIDENCE_ONLY)
                .getAsBoolean());
        assertEquals(0, report.get("failClosedMarkersLifted").getAsInt());
        assertEquals("unsat", report.getAsJsonArray("valuations").get(0)
                .getAsJsonObject().get("status").getAsString());
    }

}
