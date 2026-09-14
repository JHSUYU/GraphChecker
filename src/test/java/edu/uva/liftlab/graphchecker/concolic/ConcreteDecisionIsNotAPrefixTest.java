package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * The prefix a replay must reproduce is pi: root-dependent decisions only.
 *
 * <p>Lane B2's shape. {@code REGION.763d087e} is
 * {@code Client$Connection.sendRpcRequest}, and every decision its seed
 * activation published is concrete -- ten rows, each a
 * {@code concreteObservation} with {@code rawPathConditionSize 0}, no
 * witness and no VM event id. One of them, {@code #u16}, came out
 * {@code true} where the recording had {@code false}, and the seed wave was
 * refused with {@code BRANCH_REPLAY_MISMATCH} for it.</p>
 *
 * <p>A decision the VM contributed no path condition for has no predicate at
 * all, so no root occurs in it: it is the IPC client's own state, not a step
 * of this region's path, and it varies between two runs of one recording
 * because the connection does. Recording it is right; refusing a replay for
 * it is not. The plan cannot make this call -- every branch of a region is
 * planned with policy EXPLORE -- so the observation is asked instead.</p>
 */
public class ConcreteDecisionIsNotAPrefixTest {
    private static final String SEND =
            "<org.apache.hadoop.ipc.Client$Connection: void sendRpcRequest("
                    + "org.apache.hadoop.ipc.Client$Call)>";
    private static final String U16 = SEND + "#u16";
    private static final String U4 = SEND + "#u4";
    private static final String U18 = SEND + "#u18";

    /** Lane B2: the recorded outcome differs and nothing is refused. */
    @Test
    public void aConcreteDecisionThatFlippedIsNotAMismatch() {
        assertEquals("", mismatch(concrete(U16, 1, true),
                concrete(U18, 1, true)));
    }

    /** A root-dependent decision that flipped is still a mismatch. */
    @Test
    public void aRootDependentDecisionThatFlippedIsStillAMismatch() {
        String refusal = mismatch(witnessed(U16, 1, true),
                concrete(U18, 1, true));
        assertTrue(refusal, refusal.contains("wrong decision at " + U16));
    }

    /** A concrete decision at its recorded outcome is admitted as before. */
    @Test
    public void aConcreteDecisionThatMatchesIsAdmitted() {
        assertEquals("", mismatch(concrete(U16, 1, false),
                concrete(U18, 1, true)));
    }

    /** A site the plan never named is evidence when it is concrete. */
    @Test
    public void anUnplannedConcreteSiteIsNotUnexpected() {
        assertEquals("", mismatch(concrete(U16, 1, false),
                concrete(U18, 1, true),
                concrete(SEND + "#u49", 1, true)));
    }

    /** ... and still refused when it carried a path condition. */
    @Test
    public void anUnplannedRootDependentSiteIsUnexpected() {
        String refusal = mismatch(concrete(U16, 1, false),
                concrete(U18, 1, true),
                witnessed(SEND + "#u49", 1, true));
        assertTrue(refusal, refusal.contains("unexpected " + SEND + "#u49"));
    }

    /**
     * A site a concrete divergence never reached is not missing from pi.
     *
     * <p>Lane B2c, after the concrete sites stopped refusing: the plan
     * declares {@code #u18} and the replay published no decision there at
     * all, because {@code #u16} -- the IPC client's own connection state,
     * concrete -- went the other way and the path never reached it. An
     * activation that decided nothing over a root has an empty pi, so no
     * site can be missing from it.</p>
     */
    @Test
    public void aSiteAConcreteDivergenceNeverReachedIsNotMissing() {
        assertEquals("", mismatch(concrete(U16, 1, true)));
    }

    /** With a root-dependent decision in the activation, missing refuses. */
    @Test
    public void aMissingSiteStillRefusesWhenThePathHasRoots() {
        String refusal = mismatch(witnessed(U16, 1, false));
        assertTrue(refusal, refusal.contains("missing " + U18));
    }

    /**
     * The refusal, as the importer computes it for one seed activation whose
     * plan declares {@code #u4=true} and {@code #u16=false}.
     */
    private static String mismatch(JsonObject... observed) {
        JsonArray mappings = new JsonArray();
        mappings.add(concrete(U4, 1, true));
        for (JsonObject mapping : observed) mappings.add(mapping);
        return ConcolicSummaryImporter.seedBranchMismatchForTest(
                task(), mappings);
    }

    /** One published decision the VM contributed no path condition for. */
    private static JsonObject concrete(String site, int occurrence,
                                       boolean outcome) {
        return SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attested(site,
                        method(site), unit(site), occurrence, outcome),
                SummaryBranchMapping.Policy.EXPLORE).toJson();
    }

    /** One published decision that carried a path condition. */
    private static JsonObject witnessed(String site, int occurrence,
                                        boolean outcome) {
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "SymbolExpression");
        predicate.addProperty("_java_type", "Z");
        predicate.addProperty("_exp", "M_Z_field_SRC.root");
        JsonObject normalization = new JsonObject();
        normalization.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        return SummaryBranchMapping.witnessed(
                BranchWitness.vmPcImmutable(site, method(site), unit(site),
                        occurrence, outcome, predicate, 0, normalization),
                0, SummaryBranchMapping.Policy.EXPLORE).toJson();
    }

    private static String method(String siteId) {
        return siteId.substring(0, siteId.lastIndexOf("#u"));
    }

    private static int unit(String siteId) {
        return Integer.parseInt(
                siteId.substring(siteId.lastIndexOf("#u") + 2));
    }

    /** The seed task, with lane B2's two declared branches. */
    private static ExecutionTask task() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.SEED.5cfc9e86");
        encoded.addProperty("goalId", "GOAL.REGION_PATH.76bb19d1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.763d087e");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "hdfs-17899/sps#epoch0");
        encoded.addProperty("occurrenceId",
                "hdfs-17899/sps#epoch0/region/REGION.763d087e#1");
        encoded.addProperty("rootMethod", SEND);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("receiverClass",
                "org.apache.hadoop.ipc.Client$Connection");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", SEND);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "hdfs-17899/sps#epoch0");
        anchor.addProperty("kind", "INHERITED_CONTEXT");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        JsonArray branches = new JsonArray();
        branches.add(branch(U4, 1, true));
        branches.add(branch(U16, 1, false));
        branches.add(branch(U18, 1, true));
        encoded.add("branches", branches);
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        return ExecutionTask.decode(encoded);
    }

    private static JsonObject branch(String site, int occurrence,
                                     boolean outcome) {
        JsonObject row = new JsonObject();
        row.addProperty("siteId", site);
        row.addProperty("policy", "EXPLORE");
        JsonArray occurrences = new JsonArray();
        JsonObject one = new JsonObject();
        one.addProperty("occurrence", occurrence);
        one.addProperty("outcome", outcome);
        occurrences.add(one);
        row.add("occurrences", occurrences);
        return row;
    }
}
