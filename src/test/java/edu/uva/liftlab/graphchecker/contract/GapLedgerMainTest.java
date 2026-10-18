package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * EMIT's gap ledger ({@link GapLedgerMain}): over a session's, a round's, a
 * worker's and the campaign's gap rows, the composer's refusals and gaps,
 * the static catalog's and the plan's, final/gaps.json is the document the
 * jq it replaced published, byte for byte (its text below is that jq's
 * output over this fixture, jq 1.6); EMIT's read of it keeps every BLOCKING
 * row and the DIAGNOSTIC rows EMIT selects, and names the ledger's digest.
 */
public class GapLedgerMainTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    /** The main computes on its host's cores; the tests after it on one. */
    @After
    public void oneCore() {
        Parallel.width(1);
    }

    /** The case's layout as EMIT reads it, under {@code root}. */
    static void fixture(Path root) throws IOException {
        Path iteration = root.resolve("iteration-0000");
        // A replay session's rows: a string with every escape jq writes, a
        // row repeated with another class (the first raised is kept), an
        // undeclared hook, a bound in a subject, a row stating nothing.
        gzip(iteration.resolve("sessions/S1/gaps.jsonl.gz"),
                "{\"schemaVersion\":1,\"sessionId\":\"S1\",\"kind\":\"UNSTATED_VALUE\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"reads.jsonl seq\\u003d5 field\\u003dobservedVersion\",\"detail\":\"tab\\there \\\"quoted\\\" back\\\\slash \\u00e9 \\u2713 \\ud83d\\ude00 del\\u007f bell\\u0007\",\"topologyEpoch\":\"iteration-0000\"}",
                "{\"sessionId\":\"S1\",\"kind\":\"ADMISSION_GAP\",\"cls\":\"BLOCKING\",\"subject\":\"OCC.kept\",\"detail\":\"anchor never observed\"}",
                "{\"sessionId\":\"S1\",\"kind\":\"UNSTATED_VALUE\",\"cls\":\"BLOCKING\",\"subject\":\"reads.jsonl seq=5 field=observedVersion\",\"detail\":\"tab\\there \\\"quoted\\\" back\\\\slash \\u00e9 \\u2713 \\ud83d\\ude00 del\\u007f bell\\u0007\"}",
                "",
                "{\"sessionId\":\"S1\",\"kind\":\"HOOK_UNDECLARED\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"hook.a\",\"detail\":\"ran concrete\"}",
                "{\"sessionId\":\"S1\",\"kind\":\"HOOK_UNDECLARED\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"hook.b\",\"detail\":\"ran concrete\"}",
                "{\"sessionId\":\"\",\"kind\":\"UNATTESTED_ARM\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"IXN.7 max-world-depth=0\",\"detail\":\"d\"}",
                "{\"subject\":\"no kind\",\"cls\":\"DIAGNOSTIC\"}");
        // A round's: a stated stage, a bound on a subject's first line, a
        // row that states no class.
        gzip(iteration.resolve("obligations-0000/gaps.jsonl.gz"),
                "{\"sessionId\":\"\",\"stage\":\"EXPLORE\",\"kind\":\"TASK_UNANSWERED\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"task.1 view-hold-max=3000\\nsecond line\",\"detail\":\"x\"}",
                "{\"sessionId\":\"W1\",\"kind\":\"ADMISSION_GAP\",\"subject\":\"OCC.x\",\"detail\":\"no cls\"}");
        // A worker's, plain, read before the session's: its row naming the
        // session's hook at REPLAY is the one kept, BLOCKING.
        write(iteration.resolve("obligations-0000/abc123/gaps.jsonl"),
                "{\"sessionId\":\"W1\",\"kind\":\"UNPRODUCIBLE_ANSWER\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"OBL.slow\",\"detail\":\"SOLVER_TIMEOUT\"}",
                "{\"sessionId\":\"S1\",\"stage\":\"REPLAY\",\"kind\":\"HOOK_UNDECLARED\",\"cls\":\"BLOCKING\",\"subject\":\"hook.a\",\"detail\":\"ran concrete\"}");
        // The campaign's own: IMPORT's gate states no stage, the others do.
        write(iteration.resolve("campaign_gaps.jsonl"),
                "{\"schemaVersion\":1,\"sessionId\":\"seed-1\",\"kind\":\"UNSTATED_VALUE\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"s\",\"detail\":\"d\",\"topologyEpoch\":\"iteration-0000\"}",
                "{\"sessionId\":\"\",\"stage\":\"EXPLORE\",\"kind\":\"ADMISSION_GAP\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"EXPLORATION_CUT\",\"detail\":\"owing work\"}",
                "{\"sessionId\":\"\",\"stage\":\"COMPOSE\",\"kind\":\"OPEN_ARM_UNANSWERED\",\"cls\":\"BLOCKING\",\"subject\":\"arm\",\"detail\":\"no verdict\"}");
        // The composer's refusals (BLOCKING by construction), a gap named by
        // its reason, one stating an empty class, and a claim's gap.
        write(root.resolve("final/candidate_composition_manifest.json"),
                "{\"finalStatus\":\"FINAL_READY\",\"finalStatusRefusals\":[{\"kind\":\"COMPOSE_HEAP_BOUND\",\"subject\":\"paths\",\"detail\":\"1 of 309\"},{\"subject\":\"nokind\"}],\"gaps\":[{\"reason\":\"LOOP_BOUND_OPEN\",\"subject\":\"loop.fixture\",\"detail\":\"invented\"},{\"kind\":\"X\",\"cls\":\"\",\"subject\":\"s\"}],\"claim\":{\"gaps\":[{\"kind\":\"CLAIM_GAP\",\"cls\":\"DIAGNOSTIC\",\"subject\":\"c\",\"detail\":\"d\"}]}}");
        gzip(root.resolve("causynth/communication_gaps.jsonl.gz"),
                "{\"schemaVersion\":4,\"kind\":\"BOUNDED_LOOP_BODY_BOUND_UNDECLARED\",\"cls\":\"DIAGNOSTIC\",\"reason\":\"INHERITED_K_L_8\",\"siteId\":\"<C: void m()>#u3\",\"detail\":\"[<C: void m()>#u3]\"}");
        write(root.resolve("causynth/runtime/concolic_region_plan.jsonl"),
                "{\"schemaVersion\":2,\"kind\":\"CONCOLIC_RUNTIME_MODEL_CATALOG\",\"gaps\":[{\"kind\":\"BOUND_INSUFFICIENT\",\"cls\":\"BLOCKING\",\"subject\":\"port\\nsite\",\"detail\":\"static site\",\"source\":\"FINALIZER\"}]}",
                "{\"kind\":\"A_TASK_ROW\",\"gaps\":[{\"kind\":\"NOT_READ\"}]}");
        write(root.resolve("provenance.json"), PROVENANCE);
    }

    static final String PROVENANCE = "{\"jar\":{\"path\":\"/x.jar\",\"sha256\":\"ab\"},\"n\":3,\"f\":0.5,\"big\":1e17,\"neg\":-2,\"small\":1e-5,\"arr\":[1,\"two\",{\"k\":null},[],{}],\"t\":true}";

    private static void write(Path file, String... lines) throws IOException {
        Files.createDirectories(file.getParent());
        Files.write(file, text(lines));
    }

    private static void gzip(Path file, String... lines) throws IOException {
        Files.createDirectories(file.getParent());
        Files.write(file, ArtifactIO.gzip(text(lines)));
    }

    private static byte[] text(String... lines) {
        StringBuilder text = new StringBuilder();
        for (String line : lines) text.append(line).append('\n');
        return text.toString().getBytes(StandardCharsets.UTF_8);
    }

    private static void ledger(Path root) throws Exception {
        GapLedgerMain.main(new String[] {
            "--iteration", root.resolve("iteration-0000").toString(),
            "--composition", root.resolve(
                    "final/candidate_composition_manifest.json").toString(),
            "--static", root.resolve(
                    "causynth/communication_gaps.jsonl.gz").toString(),
            "--plan", root.resolve(
                    "causynth/runtime/concolic_region_plan.jsonl").toString(),
            "--provenance", PROVENANCE,
            "--out", root.resolve("final/gaps.json").toString(),
            "--read", root.resolve("iteration-0000/emit_gaps.json")
                    .toString()});
    }

    @Test
    public void emitReadsEveryBlockingRowAndTheDiagnosticRowsItSelects()
            throws Exception {
        Path root = folder.getRoot().toPath();
        fixture(root);
        ledger(root);
        JsonObject whole = JsonParser.parseString(new String(
                Files.readAllBytes(root.resolve("final/gaps.json")),
                StandardCharsets.UTF_8)).getAsJsonObject();
        JsonObject read = JsonParser.parseString(new String(
                Files.readAllBytes(root.resolve(
                        "iteration-0000/emit_gaps.json")),
                StandardCharsets.UTF_8)).getAsJsonObject();
        for (String same : new String[] {"schemaVersion", "kind",
                "provenance", "gaps", "gapCount", "telemetryCount", "byStage",
                "byCode"}) {
            assertEquals(same, whole.get(same), read.get(same));
        }
        // The bounds on a subject's line, the undeclared hook: in jq's order,
        // as the ledger has them.
        List<String> selected = new ArrayList<String>();
        for (JsonElement row : read.getAsJsonArray("telemetryGaps")) {
            selected.add(row.getAsJsonObject().get("subject").getAsString());
        }
        assertEquals("[task.1 view-hold-max=3000\nsecond line,"
                + " IXN.7 max-world-depth=0, hook.b]", selected.toString());
        assertEquals(whole.getAsJsonArray("telemetryGaps").size(),
                whole.get("telemetryCount").getAsInt());
        JsonObject published = read.getAsJsonObject("published");
        Path gaps = root.resolve("final/gaps.json");
        assertEquals(Files.size(gaps), published.get("bytes").getAsLong());
        assertEquals(ArtifactIO.sha256(gaps),
                published.get("sha256").getAsString());
    }

    @Test
    public void aGapFileWhereNoStageWritesFailsTheLedger() throws Exception {
        Path root = folder.getRoot().toPath();
        fixture(root);
        write(root.resolve("iteration-0000/planner/gaps.jsonl"),
                "{\"kind\":\"STRAY\"}");
        try {
            ledger(root);
            fail("a stray gaps file was read");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "a gaps file at a path no stage of this campaign writes"));
        }
        assertTrue(!Files.exists(root.resolve("final/gaps.json")));
    }
}
