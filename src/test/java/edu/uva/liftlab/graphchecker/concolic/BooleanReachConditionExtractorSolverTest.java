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
        dependency.addProperty("pathSetClosed", false);
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

}
