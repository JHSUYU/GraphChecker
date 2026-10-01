package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.management.ManagementFactory;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * One host's solver for one wave: the questions its workers put in its
 * directory are answered oldest first, each into its own output directory
 * and marked answered last; one whose worker is gone is dropped; a failure is
 * that question's answer, never the service's end; and the service ends
 * once idle with none waiting, naming no service any more.
 */
public class SolverServiceTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void answersEachLiveQuestionOnceOldestFirstThenEnds()
            throws Exception {
        Path dir = folder.newFolder("solver").toPath();
        Files.createDirectories(dir.resolve(SolverService.REQUESTS));
        Files.write(dir.resolve(SolverService.SERVER),
                "4242\n".getBytes(StandardCharsets.UTF_8));
        String live = ManagementFactory.getRuntimeMXBean().getName()
                .split("@")[0];
        // name, waiter, what the answerer does
        String[][] questions = {
                {"3.b", live, "ok"},
                {"1.a", live, "fail"},
                {"2.gone", "2147483646", "ok"},
        };
        for (String[] question : questions) {
            JsonObject asked = new JsonObject();
            asked.addProperty("obligationId", question[0]);
            asked.addProperty("waiter", question[1]);
            asked.addProperty("does", question[2]);
            Files.write(dir.resolve(SolverService.REQUESTS)
                    .resolve(question[0] + SolverService.ASKED),
                    asked.toString().getBytes(StandardCharsets.UTF_8));
        }
        List<String> order = new ArrayList<String>();
        SolverService.serve(dir, 200L, (question, out) -> {
            String id = question.get("obligationId").getAsString();
            order.add(id);
            if ("fail".equals(question.get("does").getAsString())) {
                throw new IllegalStateException("no path " + id);
            }
            Files.createDirectories(out);
            Files.write(out.resolve("obligation_result.jsonl"),
                    id.getBytes(StandardCharsets.UTF_8));
        });

        assertEquals("oldest first, the gone worker's dropped",
                java.util.Arrays.asList("1.a", "3.b"), order);
        assertEquals(1, answer(dir, "1.a").get("exit").getAsInt());
        assertTrue(answer(dir, "1.a").get("error").getAsString()
                .contains("no path 1.a"));
        assertEquals(0, answer(dir, "3.b").get("exit").getAsInt());
        assertEquals("3.b", new String(Files.readAllBytes(dir.resolve(
                SolverService.OUT).resolve("3.b")
                .resolve("obligation_result.jsonl")), StandardCharsets.UTF_8));
        assertFalse(Files.exists(dir.resolve(SolverService.ANSWERS)
                .resolve("2.gone" + SolverService.ASKED)));
        assertTrue("nothing waits or is taken once it ended",
                SolverService.waiting(dir, SolverService.ASKED).isEmpty()
                        && SolverService.waiting(dir, SolverService.TAKEN)
                        .isEmpty());
        assertFalse("an ended service names none",
                Files.exists(dir.resolve(SolverService.SERVER)));
        assertFalse(Files.exists(dir.resolve(SolverService.LOCK)));
    }

    private static JsonObject answer(Path dir, String name) throws Exception {
        return ExploreCodec.readObject(dir.resolve(SolverService.ANSWERS)
                .resolve(name + SolverService.ASKED));
    }
}
