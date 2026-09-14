package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The campaign claim rests on one occurrence of the annotated target, and it
 * is the best-supported one.
 *
 * <p>The election turns one {@link ClaimPolicy} decision per observed
 * occurrence into one campaign claim, ranking explained over unexplained
 * over closed over inconclusive over refused.</p>
 */
public class TargetOccurrenceElectionTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String CLIENT_HANDSHAKE =
            "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#1";
    private static final String DATANODE_HANDSHAKE =
            "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#2";

    /**
     * The recording observed the site twice and the closure composed one:
     * that occurrence is elected and the other reported with its reason.
     */
    @Test
    public void anUnobservedOccurrenceIsReportedAndNeverElected()
            throws IOException {
        JsonObject skipped = new JsonObject();
        skipped.addProperty("occurrenceId", DATANODE_HANDSHAKE);
        skipped.addProperty("regionId", "REGION.53092d3e");
        skipped.addProperty("status",
                TargetOccurrenceElection.SKIPPED_UNOBSERVED);
        skipped.addProperty("detail", "no linked summary carried its read");
        JsonObject ledger = TargetOccurrenceElection.elect(Arrays.asList(
                composed(CLIENT_HANDSHAKE), skipped));
        assertEquals(CLIENT_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
        assertEquals(1, ledger.get("composedCount").getAsInt());
        assertEquals(TargetOccurrenceElection.SKIPPED_UNOBSERVED,
                row(ledger, 1).get("status").getAsString());
        assertEquals("no linked summary carried its read",
                row(ledger, 1).get("detail").getAsString());
        assertEquals(TargetOccurrenceElection.NOT_COMPOSED,
                row(ledger, 1).get("support").getAsString());

        // The same pair with the unscheduled occurrence first in anchor
        // order: hdfs-17899 bug1 round 1, where the run composed exactly the
        // occurrence its case declares and then elected an unscheduled one
        // that sorted ahead of it -- and stopped, because the elected row
        // had no artifacts at all.  Neither carries an accepted claim, so
        // the rule that decides is that a composition states something
        // about its occurrence and no composition states nothing.
        JsonObject first = new JsonObject();
        first.addProperty("occurrenceId", CLIENT_HANDSHAKE);
        first.addProperty("regionId", "REGION.53092d3e");
        first.addProperty("status",
                TargetOccurrenceElection.SKIPPED_UNOBSERVED);
        first.addProperty("detail", "no linked summary carried its read");
        JsonObject refused = refused(DATANODE_HANDSHAKE);
        JsonObject bug1 = TargetOccurrenceElection.elect(
                Arrays.asList(first, refused));
        assertEquals("a row with no artifacts cannot be elected over one"
                        + " that has them", DATANODE_HANDSHAKE,
                bug1.get("chosenOccurrenceId").getAsString());

        // And a declared occurrence is elected whatever its own row says
        // and whatever the others concluded: the campaign is about that
        // execution of the site and no other.
        JsonObject declared = TargetOccurrenceElection.elect(
                Arrays.asList(composed(CLIENT_HANDSHAKE), refused),
                DATANODE_HANDSHAKE);
        assertEquals(DATANODE_HANDSHAKE,
                declared.get("chosenOccurrenceId").getAsString());
        assertEquals(DATANODE_HANDSHAKE,
                declared.get("declaredOccurrenceId").getAsString());
        assertTrue(declared.get("electionReason").getAsString()
                .contains("the case declares " + DATANODE_HANDSHAKE));
        try {
            TargetOccurrenceElection.elect(
                    Collections.singletonList(composed(CLIENT_HANDSHAKE)),
                    DATANODE_HANDSHAKE);
            throw new AssertionError("a run that never reported the declared"
                    + " occurrence must not elect another one");
        } catch (IOException unreported) {
            assertTrue(unreported.getMessage()
                    .contains(DATANODE_HANDSHAKE));
        }
    }

    /** A composition the Composer refused: artifacts, and a named reason. */
    private JsonObject refused(String occurrence) {
        JsonObject report = composed(occurrence);
        try {
            Path manifestPath = java.nio.file.Paths.get(
                    report.get("manifest").getAsString());
            JsonObject manifest = ArtifactIO.readObject(manifestPath);
            manifest.addProperty("finalStatus", "FINAL_REFUSED");
            JsonArray refusals = new JsonArray();
            JsonObject gate = new JsonObject();
            gate.addProperty("kind", "TARGET_NOT_REACHED");
            refusals.add(gate);
            manifest.add("finalStatusRefusals", refusals);
            Files.write(manifestPath, JsonFields.WRITER.toJson(manifest)
                    .getBytes(StandardCharsets.UTF_8));
        } catch (IOException failure) {
            throw new IllegalStateException(failure);
        }
        return report;
    }

    /** One occurrence is the ordinary case and says so without a comparison. */
    @Test
    public void oneOccurrenceIsItsOwnClaim() throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(
                Collections.singletonList(composed(CLIENT_HANDSHAKE)));
        assertEquals(1, ledger.get("occurrenceCount").getAsInt());
        assertTrue(row(ledger, 0).get("chosen").getAsBoolean());
        assertTrue(ledger.get("electionReason").getAsString()
                .contains("one occurrence"));

        // And which occurrence a campaign is about is the case's to
        // declare, as the whole address.  A declaration that named the
        // request family and k instead is no longer one: the family is not
        // part of an occurrence's identity, and an id that spells one names
        // the occurrence it always named with the suffix discarded.
        String at = "hdfs-17897/dn0#epoch0/region/REGION.53092d3e"
                + "@hdfs-17897/client#epoch0/striped-file-checksum#2";
        assertTrue(RuntimeWorkflowDiscovery.declares(at, at));
        assertTrue("with or without the retired family suffix",
                RuntimeWorkflowDiscovery.declares(
                        "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#2",
                        at));
        assertFalse("a family and k declares no occurrence",
                RuntimeWorkflowDiscovery.declares(
                        "hdfs-17897/client#epoch0/striped-file-checksum#2",
                        at));

        // And every closure mode has to read it: lane11741i declared dn0
        // balance-block#1 and composed four occurrences, because PLAN's
        // candidate and seed-replay schedules discovered the workflow
        // through entry points that took no declaration at all.
        for (Method entry
                : RuntimeWorkflowDiscovery.class.getDeclaredMethods()) {
            if (!entry.getName().endsWith("Workflow")) continue;
            Class<?>[] parameters = entry.getParameterTypes();
            assertEquals(entry.getName()
                            + " must take the declared occurrence",
                    String.class, parameters[parameters.length - 1]);
        }
    }

    private static JsonObject row(JsonObject ledger, int index) {
        return ledger.getAsJsonArray("occurrences").get(index)
                .getAsJsonObject();
    }

    /**
     * One occurrence's report, with the composition manifest and the solver
     * report it names actually written: the election reads its verdicts from
     * those artifacts and never from the report row.
     */
    private JsonObject composed(String occurrence) {
        try {
            Path dir = folder.newFolder().toPath();
            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", 2);
            manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
            manifest.addProperty("finalStatus", "FINAL_READY");
            manifest.add("finalStatusRefusals", new JsonArray());

            JsonObject rootSpace = new JsonObject();
            rootSpace.addProperty("acceptedValuationOrdinal", 0);
            rootSpace.addProperty("acceptedWitnessKind",
                    "FLIPPED_PLANTED_MARKER");
            JsonObject campaignClaim = new JsonObject();
            campaignClaim.addProperty("claim", ClaimPolicy.SAT_CANDIDATE);
            campaignClaim.addProperty("claimReason",
                    ClaimPolicy.SAT_CANDIDATE + " on " + occurrence);
            campaignClaim.addProperty("blockerCount", 0);
            campaignClaim.add("blockers", new JsonArray());
            campaignClaim.add("rootSpace", rootSpace);
            JsonObject reach = new JsonObject();
            reach.addProperty("state", "sat");
            reach.addProperty("reachability", "REACHABLE");
            reach.add("campaignClaim", campaignClaim);
            // SOLVE publishes into the manifest it solved: one occurrence,
            // one artifact.
            manifest.add(ComposedManifest.SOLVER, reach);

            Path manifestPath = dir.resolve(
                    "candidate_composition_manifest.json");
            Files.write(manifestPath, JsonFields.WRITER.toJson(manifest)
                    .getBytes(StandardCharsets.UTF_8));

            JsonObject report = new JsonObject();
            report.addProperty("occurrenceId", occurrence);
            report.addProperty("regionId", "REGION.53092d3e");
            report.addProperty("goalId", "GOAL.TARGET_REACH." + occurrence);
            report.addProperty("taskId", "TASK.SEED." + occurrence.hashCode());
            report.addProperty("artifactDir", dir.toString());
            report.addProperty("status", TargetOccurrenceElection.COMPOSED);
            report.addProperty("detail", "");
            report.addProperty("manifest", manifestPath.toString());
            return report;
        } catch (IOException failure) {
            throw new IllegalStateException(failure);
        }
    }
}
