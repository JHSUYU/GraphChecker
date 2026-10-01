package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * One host's solver for one exploration: the questions its obligation workers
 * put in a directory on the host's own disk, answered in turn by one JVM over
 * the corpus as it stands ({@code ObligationSolverMain --serve}).  The directory is
 * shared with {@code run_engine.sh campaign_solve_obligation}, which asks and
 * starts the service:
 *
 * <pre>
 *   lock/                  an mkdir lock, held for the few lines that decide
 *                          who starts the service and whether it may end
 *   server                 the pid the service runs under, or "starting
 *                          &lt;pid&gt;" while the worker that starts it waits
 *                          for memory (written by that worker)
 *   requests/&lt;q&gt;.json     a question: obligations, obligationId, and the
 *                          waiting worker's pid
 *   requests/&lt;q&gt;.taken    the question being answered
 *   out/&lt;q&gt;/              its answer's files, which the waiting worker moves
 *                          into its own directory, the one writer there
 *   answers/&lt;q&gt;.json      {exit, error}: the answer is complete
 * </pre>
 *
 * <p>Questions are answered oldest first (a name starts with the instant it
 * was put in); one whose worker is gone is dropped unanswered, since nobody
 * would move its files.  The service ends once no question has come for its
 * idle time and none waits -- under the lock, so a question put in after
 * that finds no service and its worker starts one.  A question taken by a
 * service that died is its worker's to fail; one still waiting is the next
 * service's.</p>
 */
final class SolverService {
    static final String LOCK = "lock";
    static final String SERVER = "server";
    static final String REQUESTS = "requests";
    static final String ANSWERS = "answers";
    static final String OUT = "out";
    static final String ASKED = ".json";
    static final String TAKEN = ".taken";
    /** How often an idle service looks for a question. */
    private static final long POLL_MILLIS = 100L;
    /** A lock older than this was left by a holder that died holding it
     *  ({@code run_engine.sh campaign_host_lock_stale_s}). */
    private static final long LOCK_STALE_MILLIS = 30_000L;

    /** Answers one question into its own output directory. */
    interface Answerer {
        void answer(JsonObject question, Path out) throws Exception;
    }

    private SolverService() {
    }

    /**
     * Serves the questions put in {@code dir} until none has come for
     * {@code idleMillis} and none waits.
     */
    static void serve(Path dir, long idleMillis, Answerer answerer)
            throws Exception {
        for (String name : new String[] {REQUESTS, ANSWERS, OUT}) {
            Files.createDirectories(dir.resolve(name));
        }
        long idleSince = System.currentTimeMillis();
        while (true) {
            List<Path> asked = waiting(dir, ASKED);
            if (asked.isEmpty()) {
                if (System.currentTimeMillis() - idleSince >= idleMillis
                        && retire(dir)) {
                    return;
                }
                Thread.sleep(POLL_MILLIS);
                continue;
            }
            for (Path question : asked) answer(dir, question, answerer);
            idleSince = System.currentTimeMillis();
        }
    }

    /**
     * One question: taken (one another service took is not this one's),
     * answered into {@code out/<q>/} unless its worker is gone, and marked
     * answered last.  A failure is the answer's, never the service's.
     */
    private static void answer(Path dir, Path question, Answerer answerer)
            throws IOException {
        String name = stem(question, ASKED);
        Path taken = question.resolveSibling(name + TAKEN);
        try {
            Files.move(question, taken, StandardCopyOption.ATOMIC_MOVE);
        } catch (IOException takenElsewhere) {
            return;
        }
        JsonObject asked = ExploreCodec.readObject(taken);
        if (!Files.isDirectory(Paths.get("/proc",
                JsonFields.primitiveString(asked, "waiter")))) {
            Files.delete(taken);
            return;
        }
        String error = "";
        try {
            answerer.answer(asked, dir.resolve(OUT).resolve(name));
        } catch (Exception | Error failed) {
            failed.printStackTrace();
            error = failed.toString();
        }
        JsonObject answer = new JsonObject();
        answer.addProperty("exit", error.isEmpty() ? 0 : 1);
        answer.addProperty("error", error);
        Path written = dir.resolve(ANSWERS).resolve("." + name + ".part");
        Files.write(written, (answer + "\n").getBytes(StandardCharsets.UTF_8));
        Files.move(written, dir.resolve(ANSWERS).resolve(name + ASKED),
                StandardCopyOption.ATOMIC_MOVE);
        Files.delete(taken);
    }

    /**
     * Ends the service when no question waits or is being answered, under
     * the lock, so no worker puts one in between unseen: the directory then
     * names no service, and the next question's worker starts one.  It is
     * the only service of the directory -- a worker starts another only
     * when the one named there has ended.
     */
    static boolean retire(Path dir) throws IOException,
            InterruptedException {
        lock(dir);
        try {
            if (!waiting(dir, ASKED).isEmpty()
                    || !waiting(dir, TAKEN).isEmpty()) {
                return false;
            }
            Files.deleteIfExists(dir.resolve(SERVER));
            return true;
        } finally {
            Files.deleteIfExists(dir.resolve(LOCK));
        }
    }

    /** The questions in {@code requests/} with that suffix, oldest first. */
    static List<Path> waiting(Path dir, String suffix) throws IOException {
        List<Path> found = new ArrayList<Path>();
        try (DirectoryStream<Path> entries = Files.newDirectoryStream(
                dir.resolve(REQUESTS), "*" + suffix)) {
            for (Path entry : entries) found.add(entry);
        }
        Collections.sort(found);
        return found;
    }

    private static void lock(Path dir) throws IOException,
            InterruptedException {
        Path lock = dir.resolve(LOCK);
        while (true) {
            try {
                Files.createDirectory(lock);
                return;
            } catch (FileAlreadyExistsException held) {
                try {
                    if (System.currentTimeMillis() - Files
                            .getLastModifiedTime(lock).toMillis()
                            >= LOCK_STALE_MILLIS) {
                        Files.deleteIfExists(lock);
                    }
                } catch (IOException released) {
                    // Released between the two looks: try again.
                }
                Thread.sleep(10L);
            }
        }
    }

    private static String stem(Path file, String suffix) {
        String name = file.getFileName().toString();
        return name.substring(0, name.length() - suffix.length());
    }
}
