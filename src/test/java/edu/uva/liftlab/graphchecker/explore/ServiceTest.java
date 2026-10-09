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
 * One service of an exploration: the questions put in its directory are
 * answered oldest first, each into its own output directory and marked
 * answered last; one whose asker is gone is dropped; a failure is that
 * question's answer, its deepest throwable, never the service's end; a
 * service given an idle time ends once idle with none waiting, naming no
 * service any more, and one given none goes on serving.
 */
public class ServiceTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void answersEachLiveQuestionOnceOldestFirstThenEnds()
            throws Exception {
        Path dir = folder.newFolder("solver").toPath();
        Files.createDirectories(dir.resolve(Service.REQUESTS));
        Files.write(dir.resolve(Service.SERVER),
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
            Files.write(dir.resolve(Service.REQUESTS)
                    .resolve(question[0] + Service.ASKED),
                    asked.toString().getBytes(StandardCharsets.UTF_8));
        }
        List<String> order = new ArrayList<String>();
        Service.serve(dir, 200L, (question, out) -> {
            String id = question.get("obligationId").getAsString();
            order.add(id);
            if ("fail".equals(question.get("does").getAsString())) {
                throw new IllegalStateException("round",
                        new java.io.IOException("no path " + id));
            }
            Files.createDirectories(out);
            Files.write(out.resolve("obligation_result.jsonl"),
                    id.getBytes(StandardCharsets.UTF_8));
        });

        assertEquals("oldest first, the gone worker's dropped",
                java.util.Arrays.asList("1.a", "3.b"), order);
        assertEquals(1, answer(dir, "1.a").get("exit").getAsInt());
        assertEquals("the deepest throwable",
                "java.io.IOException: no path 1.a",
                answer(dir, "1.a").get("error").getAsString());
        assertEquals(0, answer(dir, "3.b").get("exit").getAsInt());
        assertEquals("3.b", new String(Files.readAllBytes(dir.resolve(
                Service.OUT).resolve("3.b")
                .resolve("obligation_result.jsonl")), StandardCharsets.UTF_8));
        assertFalse(Files.exists(dir.resolve(Service.ANSWERS)
                .resolve("2.gone" + Service.ASKED)));
        assertTrue("nothing waits or is taken once it ended",
                Service.waiting(dir, Service.ASKED).isEmpty()
                        && Service.waiting(dir, Service.TAKEN)
                        .isEmpty());
        assertFalse("an ended service names none",
                Files.exists(dir.resolve(Service.SERVER)));
        assertFalse(Files.exists(dir.resolve(Service.LOCK)));
    }

    @Test
    public void aServiceGivenNoIdleTimeServesUntilEnded() throws Exception {
        Path dir = folder.newFolder("planner").toPath();
        List<String> answered = new ArrayList<String>();
        Thread service = new Thread(() -> {
            try {
                Service.serve(dir, 0L, (question, out) ->
                        answered.add(question.get("round").getAsString()));
            } catch (InterruptedException ended) {
                // Ended, as the head ends it.
            } catch (Exception failed) {
                throw new IllegalStateException(failed);
            }
        });
        service.start();
        String live = ManagementFactory.getRuntimeMXBean().getName()
                .split("@")[0];
        for (String round : new String[] {"1", "2"}) {
            JsonObject asked = new JsonObject();
            asked.addProperty("round", round);
            asked.addProperty("waiter", live);
            Path requests = dir.resolve(Service.REQUESTS);
            Files.createDirectories(requests);
            Files.write(requests.resolve(round + ".part"),
                    asked.toString().getBytes(StandardCharsets.UTF_8));
            Files.move(requests.resolve(round + ".part"),
                    requests.resolve(round + Service.ASKED));
            Path answer = dir.resolve(Service.ANSWERS)
                    .resolve(round + Service.ASKED);
            for (int tries = 0; tries < 200 && !Files.exists(answer);
                 tries++) {
                Thread.sleep(25L);
            }
            assertTrue("round " + round + " answered", Files.exists(answer));
            Thread.sleep(300L);
            assertTrue("still serving, idle", service.isAlive());
        }
        service.interrupt();
        service.join(5000L);
        assertEquals(java.util.Arrays.asList("1", "2"), answered);
    }

    private static JsonObject answer(Path dir, String name) throws Exception {
        return ExploreCodec.readObject(dir.resolve(Service.ANSWERS)
                .resolve(name + Service.ASKED));
    }
}
