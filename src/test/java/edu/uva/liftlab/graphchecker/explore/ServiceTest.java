package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.SessionDir;

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

public class ServiceTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    @Test(timeout = 60000L)
    public void answersEachLiveQuestionOnceOldestFirstThenEnds()
            throws Exception {
        Path dir = folder.newFolder("solver").toPath();
        Files.createDirectories(dir.resolve(Service.REQUESTS));
        Files.write(dir.resolve(Service.REQUESTS)
                .resolve("0.dead" + Service.TAKEN),
                "{}".getBytes(StandardCharsets.UTF_8));
        Files.write(dir.resolve(Service.SERVER),
                "4242\n".getBytes(StandardCharsets.UTF_8));
        String live = ManagementFactory.getRuntimeMXBean().getName()
                .split("@")[0];
        String[][] questions = {
                {"3.b", live, "ok"},
                {"1.a", live, "fail"},
                {"2.gone", "2147483646", "ok"},
                {"4.c", live, "past"},
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
        Service.serve(dir, 200L, 1, (question, out) -> {
            String id = question.get("obligationId").getAsString();
            order.add(id);
            if ("fail".equals(question.get("does").getAsString())) {
                throw new IllegalStateException("round",
                        new java.io.IOException("no path " + id));
            }
            if ("past".equals(question.get("does").getAsString())) {
                throw new Service.OutOfHeap("the planner needs ~9 MB of "
                        + "its 8 MB old generation");
            }
            Files.createDirectories(out);
            Files.write(out.resolve("obligation_result.jsonl"),
                    id.getBytes(StandardCharsets.UTF_8));
        });

        assertEquals("oldest first, the gone worker's dropped",
                java.util.Arrays.asList("1.a", "3.b", "4.c"), order);
        assertEquals("a round no heap holds is answered so, and the "
                + "service serves on", 3, answer(dir, "4.c").get("exit")
                .getAsInt());
        assertEquals("the planner needs ~9 MB of its 8 MB old generation",
                answer(dir, "4.c").get("error").getAsString());
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
        Service.serve(dir, 0L, 1, (question, out) -> {
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

    @Test
    public void aSolversCorpusStandsWithoutWhatGrowWithdrew()
            throws Exception {
        Path sessions = folder.newFolder("standing", "sessions").toPath();
        for (String name : new String[] {"c", "a", "b"}) {
            Files.createDirectories(sessions.resolve(name));
        }
        assertEquals(java.util.Arrays.asList("a", "b", "c"),
                ObligationSolverMain.standing(sessions));
        Files.write(sessions.resolveSibling(SessionDir.WITHDRAWN),
                "b\nx\n".getBytes(StandardCharsets.UTF_8));
        assertEquals(java.util.Arrays.asList("a", "c"),
                ObligationSolverMain.standing(sessions));
    }

    @Test
    public void aSolversReadUnderAWithdrawalIsReadAgainWithoutIt()
            throws Exception {
        String[][] rows = {
                {"named-after", "withdraw b", "a c", "1"},
                {"gone-under", "withdraw c, fail", "a b", "1"},
                {"unexplained", "fail", "thrown", "0"},
                {"elsewhere", "journal x", "a b c", "0"},
        };
        for (String[] row : rows) {
            Path sessions = folder.newFolder(row[0], "sessions").toPath();
            Path journal = sessions.resolveSibling(
                    SessionDir.WITHDRAWN);
            Files.write(journal, new byte[0]);
            for (String name : new String[] {"a", "b", "c"}) {
                Files.createDirectories(sessions.resolve(name));
            }
            int[] reads = {0};
            String said;
            int again = 0;
            try {
                ObligationSolverMain.Whole<List<String>> whole =
                        ObligationSolverMain.readWhole(sessions,
                                ObligationSolverMain.standing(sessions),
                                standing -> {
                    if (reads[0]++ == 0) {
                        String[] act = row[1].split(" ");
                        String gone = act.length > 1
                                ? act[1].replace(",", "") : "";
                        if (act[0].equals("withdraw")) {
                            Files.write(journal, (gone + "\n").getBytes(
                                    StandardCharsets.UTF_8),
                                    java.nio.file.StandardOpenOption.APPEND);
                            Files.delete(sessions.resolve(gone));
                        } else if (act[0].equals("journal")) {
                            Files.write(journal, (gone + "\n").getBytes(
                                    StandardCharsets.UTF_8),
                                    java.nio.file.StandardOpenOption.APPEND);
                        }
                        if (row[1].endsWith("fail")) {
                            throw new java.io.IOException("unreadable");
                        }
                    }
                    return new ArrayList<String>(standing);
                });
                said = String.join(" ", whole.read);
                again = whole.again;
            } catch (java.io.IOException thrown) {
                said = "thrown";
            }
            assertEquals(row[0], row[2], said);
            assertEquals(row[0], Integer.parseInt(row[3]), again);
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
