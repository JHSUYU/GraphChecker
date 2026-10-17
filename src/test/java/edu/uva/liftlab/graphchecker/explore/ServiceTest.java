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
 * service any more, and one given none goes on serving; one that outgrew its
 * corpus gives its question back and ends.
 */
public class ServiceTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    @Test(timeout = 60000L)
    public void answersEachLiveQuestionOnceOldestFirstThenEnds()
            throws Exception {
        Path dir = folder.newFolder("solver").toPath();
        Files.createDirectories(dir.resolve(Service.REQUESTS));
        // Taken by a service that died mid-answer (its run stopped): never
        // this one's to wait for, so it still ends idle.
        Files.write(dir.resolve(Service.REQUESTS)
                .resolve("0.dead" + Service.TAKEN),
                "{}".getBytes(StandardCharsets.UTF_8));
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
        assertTrue("nothing waits once it ended",
                Service.waiting(dir, Service.ASKED).isEmpty());
        assertEquals("what it took it answered; the dead service's is its "
                        + "asker's", java.util.Arrays.asList(
                        "0.dead" + Service.TAKEN),
                names(Service.waiting(dir, Service.TAKEN)));
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

    /**
     * A service whose answerer cannot hold a question's corpus ({@code
     * Service.Outgrown}) gives that question back untaken and ends at once,
     * whatever else waits, naming itself retired so its askers start one
     * sized anew (solr-adhoc-39 PV7: solvers that ran out of heap lost every
     * question they held).
     */
    @Test
    public void aServiceThatOutgrewItsCorpusGivesTheQuestionBackAndEnds()
            throws Exception {
        Path dir = folder.newFolder("outgrown").toPath();
        Files.createDirectories(dir.resolve(Service.REQUESTS));
        Files.write(dir.resolve(Service.SERVER),
                "4242\n".getBytes(StandardCharsets.UTF_8));
        String live = ManagementFactory.getRuntimeMXBean().getName()
                .split("@")[0];
        for (String name : new String[] {"1.a", "2.b", "3.c"}) {
            JsonObject asked = new JsonObject();
            asked.addProperty("obligationId", name);
            asked.addProperty("waiter", live);
            Files.write(dir.resolve(Service.REQUESTS)
                    .resolve(name + Service.ASKED),
                    asked.toString().getBytes(StandardCharsets.UTF_8));
        }
        List<String> order = new ArrayList<String>();
        Service.serve(dir, 0L, (question, out) -> {
            String id = question.get("obligationId").getAsString();
            order.add(id);
            if ("2.b".equals(id)) {
                throw new Service.Outgrown("past its heap");
            }
        });
        assertEquals(java.util.Arrays.asList("1.a", "2.b"), order);
        assertEquals(0, answer(dir, "1.a").get("exit").getAsInt());
        assertEquals("the outgrown question and the one behind it wait",
                java.util.Arrays.asList("2.b" + Service.ASKED,
                        "3.c" + Service.ASKED),
                names(Service.waiting(dir, Service.ASKED)));
        assertTrue(Service.waiting(dir, Service.TAKEN).isEmpty());
        assertFalse(Files.exists(dir.resolve(Service.SERVER)));
        assertEquals("4242\n", new String(Files.readAllBytes(
                dir.resolve(Service.RETIRED)), StandardCharsets.UTF_8));
        assertFalse(Files.exists(dir.resolve(Service.LOCK)));
    }

    /**
     * A served solver reads its corpus again only for a question whose round
     * was planned over a session it did not read (of those still standing),
     * or when a session it read left; a round that names none needs every
     * session standing.  Read again after every landing, 39's host solvers
     * re-read 10-16 s before nearly every question.
     */
    @Test
    public void aServedSolverReadsAgainOnlyForWhatItsRoundNeeds()
            throws Exception {
        Path round = folder.newFolder("obligations-0003").toPath();
        Path obligations = round.resolve("obligations.jsonl");
        // what the solver read | standing now | the round's corpus.txt
        // (- none) | stale
        String[][] rows = {
                {"a b", "a b c", "a", "false"},
                {"a b", "a b c", "a b", "false"},
                {"a b", "a b c", "a c", "true"},
                {"a b", "a b c", "-", "true"},
                {"a b", "a b", "-", "false"},
                {"a b", "a c", "a", "true"},
                {"a b", "a b", "a x", "false"},
        };
        for (String[] row : rows) {
            Files.deleteIfExists(round.resolve(
                    ObligationSolverMain.ROUND_CORPUS));
            if (!"-".equals(row[2])) {
                Files.write(round.resolve(ObligationSolverMain.ROUND_CORPUS),
                        (row[2].replace(' ', '\n') + "\n")
                                .getBytes(StandardCharsets.UTF_8));
            }
            List<String> now = java.util.Arrays.asList(row[1].split(" "));
            assertEquals(java.util.Arrays.toString(row),
                    Boolean.parseBoolean(row[3]),
                    ObligationSolverMain.stale(new java.util.HashSet<String>(
                            java.util.Arrays.asList(row[0].split(" "))), now,
                            ObligationSolverMain.round(obligations, now)));
        }
    }

    private static List<String> names(List<Path> files) {
        List<String> names = new ArrayList<String>();
        for (Path file : files) names.add(file.getFileName().toString());
        return names;
    }

    private static JsonObject answer(Path dir, String name) throws Exception {
        return ExploreCodec.readObject(dir.resolve(Service.ANSWERS)
                .resolve(name + Service.ASKED));
    }
}
