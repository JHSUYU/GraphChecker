package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The campaign claim rests on one occurrence of the annotated target, and it
 * is the best-supported one.
 *
 * <p>A run composes and solves every observed occurrence of the site, so it
 * finishes with one {@link ClaimPolicy} decision per occurrence.  The
 * election is the outer loop that turns that set into one campaign claim.
 * It compares published claims only: a satisfying witness the policy
 * explained beats one it did not, which beats a closed refutation, which
 * beats an inconclusive run, which beats a composition the Composer refused
 * and an occurrence that was never composed at all.</p>
 */
public class TargetOccurrenceElectionTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String CLIENT_HANDSHAKE =
            "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#1";
    private static final String DATANODE_HANDSHAKE =
            "hdfs-17897/dn0#epoch0/region/REGION.53092d3e#2";

    /**
     * hdfs-17897's shape: the elected member is the DataNode handshake and
     * concludes nothing, while the client handshake -- where the chain ends
     * -- carries an explained satisfying witness.  The claim follows the
     * evidence and not the election order.
     */
    @Test
    public void theExplainedWitnessOutranksTheElectedInconclusiveMember()
            throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(Arrays.asList(
                composed(DATANODE_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.INCONCLUSIVE_PARTIAL, 2, -1),
                composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.SAT_CANDIDATE, 0, 3)));
        assertEquals(CLIENT_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
        assertEquals(TargetOccurrenceElection.SAT_CANDIDATE_EXPLAINED_WITNESS,
                ledger.get("chosenSupport").getAsString());
        assertEquals(2, ledger.get("occurrenceCount").getAsInt());
        assertEquals(2, ledger.get("composedCount").getAsInt());
        assertFalse(chosen(ledger, 0));
        assertTrue(chosen(ledger, 1));
        // Every occurrence keeps its own verdict beside the elected one.
        assertEquals(ClaimPolicy.INCONCLUSIVE_PARTIAL,
                row(ledger, 0).get("claim").getAsString());
        assertTrue(ledger.get("electionReason").getAsString()
                .contains(DATANODE_HANDSHAKE));
    }

    /** A satisfying witness nobody explained is still better than none. */
    @Test
    public void anUnexplainedWitnessOutranksAnInconclusiveRun()
            throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(Arrays.asList(
                composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.INCONCLUSIVE_PARTIAL, 1, -1),
                composed(DATANODE_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.SAT_CANDIDATE, 0, -1)));
        assertEquals(DATANODE_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
        assertEquals(TargetOccurrenceElection.SAT_CANDIDATE,
                ledger.get("chosenSupport").getAsString());
    }

    /** A closed refutation is a result; an inconclusive run is not. */
    @Test
    public void aClosedRefutationOutranksAnInconclusiveRun()
            throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(Arrays.asList(
                composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.INCONCLUSIVE_PARTIAL, 4, -1),
                composed(DATANODE_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.UNSAT_CLOSED, 0, -1)));
        assertEquals(DATANODE_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
    }

    /**
     * A refused composition states nothing about its occurrence, whatever
     * claim the solver stage then computed over the refusal stub, so it
     * ranks with the occurrence nobody composed.
     */
    @Test
    public void aRefusedCompositionRanksWithAnUncomposedOccurrence()
            throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(Arrays.asList(
                composed(CLIENT_HANDSHAKE, "FINAL_REFUSED", 1,
                        ClaimPolicy.SAT_CANDIDATE, 0, 0),
                composed(DATANODE_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.INCONCLUSIVE_PARTIAL, 3, -1)));
        assertEquals(DATANODE_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
        assertEquals(TargetOccurrenceElection.REFUSED,
                row(ledger, 0).get("support").getAsString());
    }

    /**
     * hdfs-17960's shape: the recording observed the site twice and the
     * active observed closure scheduled a replay member for one of them, so
     * the other is reported and never composed.  The composed occurrence is
     * elected and the skip keeps its stated reason.
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
                composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.SAT_CANDIDATE, 0, 0),
                skipped));
        assertEquals(CLIENT_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
        assertEquals(1, ledger.get("composedCount").getAsInt());
        assertEquals(TargetOccurrenceElection.SKIPPED_UNOBSERVED,
                row(ledger, 1).get("status").getAsString());
        assertEquals("no linked summary carried its read",
                row(ledger, 1).get("detail").getAsString());
        assertEquals(TargetOccurrenceElection.REFUSED,
                row(ledger, 1).get("support").getAsString());
    }

    /**
     * Equal evidence leaves the schedule order deciding, so the same corpus
     * always elects the same occurrence and a composed formula never changes
     * because two verdicts arrived in a different order.
     */
    @Test
    public void equalEvidenceElectsTheFirstScheduledOccurrence()
            throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(Arrays.asList(
                composed(DATANODE_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.SAT_CANDIDATE, 0, 1),
                composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.SAT_CANDIDATE, 0, 1)));
        assertEquals(DATANODE_HANDSHAKE,
                ledger.get("chosenOccurrenceId").getAsString());
        // The tie-break before order is the blocker count.
        JsonObject fewer = TargetOccurrenceElection.elect(Arrays.asList(
                composed(DATANODE_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.INCONCLUSIVE_PARTIAL, 4, -1),
                composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                        ClaimPolicy.INCONCLUSIVE_PARTIAL, 1, -1)));
        assertEquals(CLIENT_HANDSHAKE,
                fewer.get("chosenOccurrenceId").getAsString());
    }

    /** One occurrence is the ordinary case and says so without a comparison. */
    @Test
    public void oneOccurrenceIsItsOwnClaim() throws IOException {
        JsonObject ledger = TargetOccurrenceElection.elect(
                Collections.singletonList(composed(CLIENT_HANDSHAKE,
                        "FINAL_READY", 0, ClaimPolicy.SAT_CANDIDATE, 0, 0)));
        assertEquals(1, ledger.get("occurrenceCount").getAsInt());
        assertTrue(chosen(ledger, 0));
        assertTrue(ledger.get("electionReason").getAsString()
                .contains("one occurrence"));
    }

    /** The per-occurrence stage times are carried into the ledger. */
    @Test
    public void theLedgerCarriesPerOccurrenceStageTimes() throws IOException {
        JsonObject report = composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                ClaimPolicy.SAT_CANDIDATE, 0, 0);
        report.addProperty("composeWallMillis", 51234L);
        report.addProperty("solveWallMillis", 9001L);
        JsonObject ledger = TargetOccurrenceElection.elect(
                Collections.singletonList(report));
        assertEquals(51234L, row(ledger, 0).get("composeWallMillis")
                .getAsLong());
        assertEquals(9001L, row(ledger, 0).get("solveWallMillis")
                .getAsLong());
    }

    /** A report set that names one occurrence twice is not a ledger. */
    @Test
    public void anOccurrenceIsReportedOnce() {
        try {
            TargetOccurrenceElection.elect(Arrays.asList(
                    composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                            ClaimPolicy.SAT_CANDIDATE, 0, 0),
                    composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                            ClaimPolicy.SAT_CANDIDATE, 0, 0)));
            fail("one occurrence was reported twice");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("reported twice"));
        }
    }

    /**
     * A solver report with no ClaimPolicy decision is a report this stage may
     * not elect from: the shell used to be able to fall back to its own
     * verdict, and this is the same gate one layer up.
     */
    @Test
    public void aComposedOccurrenceWithoutAClaimIsRefused() throws Exception {
        JsonObject report = composed(CLIENT_HANDSHAKE, "FINAL_READY", 0,
                ClaimPolicy.SAT_CANDIDATE, 0, 0);
        Path reach = Paths.get(report.get("reachReport").getAsString());
        Files.write(reach, "{\"state\":\"sat\"}"
                .getBytes(StandardCharsets.UTF_8));
        try {
            TargetOccurrenceElection.elect(
                    Collections.singletonList(report));
            fail("a claimless reach report was elected from");
        } catch (IOException expected) {
            assertTrue(expected.getMessage()
                    .contains("no ClaimPolicy decision"));
        }
    }

    private static JsonObject row(JsonObject ledger, int index) {
        return ledger.getAsJsonArray("occurrences").get(index)
                .getAsJsonObject();
    }

    private static boolean chosen(JsonObject ledger, int index) {
        return row(ledger, index).get("chosen").getAsBoolean();
    }

    /**
     * One occurrence's report, with the composition manifest and the solver
     * report it names actually written: the election reads its verdicts from
     * those artifacts and never from the report row.
     */
    private JsonObject composed(String occurrence, String finalStatus,
                                int refusals, String claim, int blockers,
                                int acceptedValuationOrdinal) {
        try {
            Path dir = folder.newFolder().toPath();
            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", 2);
            manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
            manifest.addProperty("finalStatus", finalStatus);
            JsonArray refusalRows = new JsonArray();
            for (int index = 0; index < refusals; index++) {
                JsonObject refusal = new JsonObject();
                refusal.addProperty("reason", "TARGET_REACH_QUERY_ABSENT");
                refusalRows.add(refusal);
            }
            manifest.add("finalStatusRefusals", refusalRows);

            JsonObject rootSpace = new JsonObject();
            rootSpace.addProperty("acceptedValuationOrdinal",
                    acceptedValuationOrdinal);
            rootSpace.addProperty("acceptedWitnessKind",
                    acceptedValuationOrdinal < 0 ? ""
                            : "FLIPPED_PLANTED_MARKER");
            JsonObject campaignClaim = new JsonObject();
            campaignClaim.addProperty("claim", claim);
            campaignClaim.addProperty("claimReason", claim + " on "
                    + occurrence);
            campaignClaim.addProperty("blockerCount", blockers);
            campaignClaim.add("blockers", new JsonArray());
            campaignClaim.add("rootSpace", rootSpace);
            JsonObject reachCondition = new JsonObject();
            reachCondition.addProperty("reachability",
                    ClaimPolicy.SAT_CANDIDATE.equals(claim)
                            ? "REACHABLE" : "UNREACHABLE");
            JsonObject reach = new JsonObject();
            reach.addProperty("state", "sat");
            reach.add("reachCondition", reachCondition);
            reach.add("campaignClaim", campaignClaim);

            Path manifestPath = dir.resolve(
                    "candidate_composition_manifest.json");
            Path reachPath = dir.resolve("z3-result.json");
            write(manifestPath, manifest);
            write(reachPath, reach);

            JsonObject report = new JsonObject();
            report.addProperty("occurrenceId", occurrence);
            report.addProperty("regionId", "REGION.53092d3e");
            report.addProperty("goalId", "GOAL.TARGET_REACH." + occurrence);
            report.addProperty("taskId", "TASK.SEED." + occurrence.hashCode());
            report.addProperty("artifactDir", dir.toString());
            report.addProperty("status", TargetOccurrenceElection.COMPOSED);
            report.addProperty("detail", "");
            report.addProperty("manifest", manifestPath.toString());
            report.addProperty("reachReport", reachPath.toString());
            return report;
        } catch (IOException failure) {
            throw new IllegalStateException(failure);
        }
    }

    private static void write(Path path, JsonObject value)
            throws IOException {
        Files.write(path, JsonFields.WRITER.toJson(value)
                .getBytes(StandardCharsets.UTF_8));
    }
}
