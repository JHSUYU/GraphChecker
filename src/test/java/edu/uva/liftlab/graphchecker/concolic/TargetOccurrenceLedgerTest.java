package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Every observed occurrence of the annotated target is named, and the ones
 * a composition did not lower are reported.
 *
 * <p>The planner plants a {@code TARGET_REACH_CLOSURE} goal on every
 * execution of the annotated site -- hdfs-17897's SASL handshake is observed
 * twice, hdfs-11741's site four times.  Everything after it narrows to one:
 * {@code RuntimeWorkflowDiscovery} elects a single {@code TARGET} member, the
 * campaign builds a reach query for that member alone, and the composition
 * lowers that query.  Nothing published said so, so a verdict about one
 * execution of the site read as a verdict about the site.  hdfs-17897 elected
 * {@code REGION.53092d3e#2}, the DataNode's own handshake, leaving the
 * client's handshake -- where the bug's chain ends -- off the slice with
 * nothing naming why.</p>
 */
public class TargetOccurrenceLedgerTest {

    private static final String SITE =
            "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: "
                    + "org.apache.hadoop.hdfs.security.token.block."
                    + "DataEncryptionKey retrieveDataEncryptionKey(int,"
                    + "byte[])>#u12";
    private static final String CLIENT_HANDSHAKE =
            "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#1";
    private static final String DATANODE_HANDSHAKE =
            "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#2";

    /** Both handshakes are named, and exactly the elected one is composed. */
    @Test
    public void everyObservedTargetOccurrenceIsNamed() {
        JsonArray ledger = ConcolicSmtComposer.targetReachOccurrences(
                bothHandshakes(), fatalQuery(DATANODE_HANDSHAKE,
                        "GOAL.TARGET_REACH.2"));
        assertEquals(2, ledger.size());
        assertEquals(CLIENT_HANDSHAKE, occurrence(ledger, 0));
        assertEquals(DATANODE_HANDSHAKE, occurrence(ledger, 1));
        assertTrue(composed(ledger, 1));
        assertTrue("the client's handshake is not in this formula",
                !composed(ledger, 0));
        assertEquals(SITE, ledger.get(0).getAsJsonObject()
                .getAsJsonArray("failureSites").get(0).getAsString());
    }

    /**
     * The schedule names every target occurrence as one, not only the one it
     * elects.
     *
     * <p>Exactly one member carries the {@code TARGET} role -- that is the
     * replay closure this bundle is built around and every stage still
     * dispatches on it -- but each occurrence of the annotated site is
     * flagged as carrying a target-reach goal.  That flag is what EXPLORE
     * builds a reach query per occurrence from and what COMPOSE composes per
     * occurrence from; without it the other occurrences are indistinguishable
     * from an ordinary causal dependency.</p>
     */
    @Test
    public void everyTargetOccurrenceIsScheduledAsATargetReachMember()
            throws java.io.IOException {
        List<RuntimeWorkflowDiscovery.Selection> selections =
                RuntimeWorkflowDiscovery.rankedWorkflow(distinctHandshakes())
                        .selections();
        assertEquals(2, selections.size());
        int elected = 0;
        for (RuntimeWorkflowDiscovery.Selection selection : selections) {
            assertTrue("occurrence " + selection.occurrenceId
                    + " is not named as a target occurrence",
                    selection.targetReach);
            if (selection.target) elected++;
        }
        assertEquals("one member carries the replay closure", 1, elected);
    }

    private static List<RegionInstancePlan> bothHandshakes() {
        return Arrays.asList(
                plan(CLIENT_HANDSHAKE, "REGION.53092d3e",
                        "GOAL.TARGET_REACH.1", true),
                plan(DATANODE_HANDSHAKE, "REGION.53092d3e",
                        "GOAL.TARGET_REACH.2", true));
    }

    /** The same two handshakes, with the runtime event that separates them:
     *  the ranking refuses evidence that does not distinguish occurrences. */
    private static List<RegionInstancePlan> distinctHandshakes() {
        return Arrays.asList(
                plan(CLIENT_HANDSHAKE, "REGION.53092d3e",
                        "GOAL.TARGET_REACH.1", true, 11L),
                plan(DATANODE_HANDSHAKE, "REGION.53092d3e",
                        "GOAL.TARGET_REACH.2", true, 27L));
    }

    private static String occurrence(JsonArray ledger, int index) {
        return ledger.get(index).getAsJsonObject()
                .get("occurrenceId").getAsString();
    }

    private static boolean composed(JsonArray ledger, int index) {
        return ledger.get(index).getAsJsonObject()
                .get("composed").getAsBoolean();
    }

    private static JsonObject fatalQuery(String occurrence, String goal) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("occurrenceId", occurrence);
        fatal.addProperty("goalId", goal);
        return fatal;
    }

    private static RegionInstancePlan plan(String occurrence, String region,
                                           String goal, boolean target) {
        return plan(occurrence, region, goal, target, -1L);
    }

    private static RegionInstancePlan plan(String occurrence, String region,
                                           String goal, boolean target,
                                           long runtimeEventSeq) {
        JsonObject branch = new JsonObject();
        branch.addProperty("failureTarget", target);
        branch.addProperty("loopControlGuard", false);
        branch.addProperty("observed", target);
        branch.addProperty("siteId", SITE);
        if (runtimeEventSeq >= 0) {
            branch.addProperty("selectedRuntimeEventSeq", runtimeEventSeq);
        }
        if (target) branch.addProperty("requiredOutcome", false);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        JsonObject closure = new JsonObject();
        closure.addProperty("goalId", goal);
        closure.addProperty("kind", target
                ? "TARGET_REACH_CLOSURE" : "REGION_PATH_CLOSURE");
        closure.add("admission", admission);
        closure.add("branches", branches);
        closure.add("runtimeDefinitionMethods", new JsonArray());
        closure.add("edgeBindings", new JsonArray());
        JsonArray closures = new JsonArray();
        closures.add(closure);
        JsonObject encoded = new JsonObject();
        encoded.addProperty("sourceKey", "hdfs-17897/dn0#epoch0");
        encoded.addProperty("occurrenceId", occurrence);
        encoded.addProperty("relationKey",
                "hdfs-17897/dn0/relation/" + region);
        encoded.addProperty("regionId", region);
        encoded.add("closureGoals", closures);
        return RegionInstancePlan.decode(encoded);
    }
}
