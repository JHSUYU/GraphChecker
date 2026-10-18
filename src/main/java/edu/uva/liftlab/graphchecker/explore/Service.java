package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.HeapWatch;
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
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * One JVM that answers an exploration's questions, up to its seats at once,
 * over state it keeps between them: a host's obligation solver ({@code
 * ObligationSolverMain --serve}, the questions its obligation workers ask)
 * and the exploration's planner ({@code ExploreMain --serve}, one question
 * per round).  The questions are put in a directory on the host's own disk,
 * shared with {@code run_engine.sh}, which asks (from that host) and starts
 * the service:
 *
 * <pre>
 *   lock/                  an mkdir lock, held for the few lines that decide
 *                          who starts the service and whether it may end
 *   server                 the pid the service runs under, or "starting
 *                          &lt;pid&gt;" while the asker that starts it waits
 *                          for memory (written by that asker)
 *   requests/&lt;q&gt;.json     a question: what the answerer reads, and the
 *                          waiting asker's pid ({@code waiter})
 *   requests/&lt;q&gt;.taken    the question being answered
 *   out/&lt;q&gt;/              its answer's files where the answerer writes them
 *                          there (the solver: the waiting worker moves them
 *                          into its own directory, the one writer there)
 *   answers/&lt;q&gt;.json      {exit, error}: the answer is complete
 *   retired                what {@code server} named when the service gave
 *                          its corpus up ({@link Outgrown}): its askers start
 *                          the next one, as after an idle end
 * </pre>
 *
 * <p>Questions are taken oldest first (a name starts with the instant it
 * was put in), each answered on a seat of its own, as many at once as the
 * service has seats -- and beside another only while the old generation was
 * under {@link #BESIDE} full after its last collection, so a heap that fills
 * answers one at a time ({@code HeapWatch}); one whose asker is gone is
 * dropped unanswered, since nobody would read its answer.  A failure is that question's answer -- its error
 * the deepest throwable -- never the service's end.  A service given an idle
 * time ends once no question has come for it and none waits -- under the
 * lock, so a question put in after that finds no service and its asker
 * starts one; one given none serves until it is ended.  A question taken by
 * a service that died is its asker's to fail; one still waiting is the next
 * service's.  An answerer that cannot hold what a question needs ({@link
 * Outgrown}: the corpus outgrew the heap it was started for) gives the
 * question back untaken, the service takes no more and ends once the
 * questions its other seats answer are answered, naming itself
 * {@code retired}, so its askers start one sized anew; one that no heap it
 * could be given holds ({@link OutOfHeap}) answers it so, exit {@link
 * HeapWatch#OUT_OF_HEAP}, and serves on.</p>
 */
final class Service {
    static final String LOCK = "lock";
    static final String SERVER = "server";
    static final String REQUESTS = "requests";
    static final String ANSWERS = "answers";
    static final String OUT = "out";
    static final String ASKED = ".json";
    static final String TAKEN = ".taken";
    static final String RETIRED = "retired";
    /** How often an idle service looks for a question. */
    private static final long POLL_MILLIS = 100L;
    /** How full the old generation may be after its last collection for a
     *  question to be taken beside one answering: past it the service
     *  answers one at a time, each question's own working set beside the
     *  state it keeps ({@code HeapWatch#FULL} ends a JVM that only
     *  collects). */
    static final double BESIDE = 0.75;
    /** A lock older than this was left by a holder that died holding it
     *  ({@code run_engine.sh campaign_host_lock_stale_s}). */
    private static final long LOCK_STALE_MILLIS = 30_000L;

    /** Answers one question, its files into {@code out} if it writes them
     *  there. */
    interface Answerer {
        void answer(JsonObject question, Path out) throws Exception;
    }

    /** An answerer's refusal to take a question it cannot hold: the
     *  question is given back and the service ends. */
    static final class Outgrown extends Exception {
        private static final long serialVersionUID = 1L;

        Outgrown(String why) {
            super(why);
        }
    }

    /** An answerer's answer that the question needs more heap than any JVM
     *  of it is given: answered {@link HeapWatch#OUT_OF_HEAP}, why its
     *  error, the service serving on (a served planner already at the
     *  engine heap, {@code ExploreMain}). */
    static final class OutOfHeap extends Exception {
        private static final long serialVersionUID = 1L;

        OutOfHeap(String why) {
            super(why);
        }
    }

    private Service() {
    }

    /**
     * Serves the questions put in {@code dir}, up to {@code seats} at once,
     * until none has come for {@code idleMillis} and none waits or is
     * answered; with {@code idleMillis} 0 or less, until the process is
     * ended.
     */
    static void serve(Path dir, long idleMillis, int seats,
                      Answerer answerer) throws Exception {
        for (String name : new String[] {REQUESTS, ANSWERS, OUT}) {
            Files.createDirectories(dir.resolve(name));
        }
        int most = Math.max(1, seats);
        ExecutorService answering = Executors.newFixedThreadPool(most,
                runnable -> {
                    Thread thread = new Thread(runnable, "service-seat");
                    thread.setDaemon(true);
                    return thread;
                });
        Seats taken = new Seats();
        long idleSince = System.currentTimeMillis();
        try {
            while (true) {
                Exception ended = taken.ended();
                if (ended != null) {
                    taken.awaitNone();
                    if (ended instanceof Outgrown) {
                        System.err.println("the service ended: "
                                + ended.getMessage());
                        retireOutgrown(dir);
                        return;
                    }
                    throw ended;
                }
                List<Path> asked = waiting(dir, ASKED);
                if (asked.isEmpty() && taken.count() == 0) {
                    if (idleMillis > 0L
                            && System.currentTimeMillis() - idleSince
                            >= idleMillis && retire(dir)) {
                        return;
                    }
                    taken.awaitChange(POLL_MILLIS);
                    continue;
                }
                for (Path question : asked) {
                    int busy = taken.count();
                    if (busy >= most || busy > 0
                            && HeapWatch.oldGenerationSwept() >= BESIDE) {
                        break;
                    }
                    Path held = take(question);
                    if (held == null) continue;
                    taken.add();
                    answering.execute(() -> {
                        Exception failed = null;
                        try {
                            answer(dir, held, answerer);
                        } catch (Outgrown | IOException | RuntimeException
                                thrown) {
                            failed = thrown;
                        } finally {
                            taken.done(failed);
                        }
                    });
                }
                idleSince = System.currentTimeMillis();
                taken.awaitChange(POLL_MILLIS);
            }
        } finally {
            answering.shutdownNow();
        }
    }

    /** The questions the service's seats answer now, and the first end one
     *  of them asked for (an {@link Outgrown}, or a failure no answer is). */
    private static final class Seats {
        private int count;
        private Exception ended;

        synchronized void add() {
            count++;
        }

        synchronized void done(Exception failed) {
            count--;
            if (failed != null && ended == null) ended = failed;
            notifyAll();
        }

        synchronized int count() {
            return count;
        }

        synchronized Exception ended() {
            return ended;
        }

        /** Waits for a seat to free, at most {@code millis}. */
        synchronized void awaitChange(long millis)
                throws InterruptedException {
            wait(millis);
        }

        /** Waits for every seat to free. */
        synchronized void awaitNone() throws InterruptedException {
            while (count > 0) wait();
        }
    }

    /** One question taken: its file moved to {@code .taken}; null when
     *  another service took it. */
    private static Path take(Path question) {
        Path taken = question.resolveSibling(stem(question, ASKED) + TAKEN);
        try {
            Files.move(question, taken, StandardCopyOption.ATOMIC_MOVE);
        } catch (IOException takenElsewhere) {
            return null;
        }
        return taken;
    }

    /**
     * One question taken ({@link #take}): answered unless its asker is gone,
     * and marked answered last.  A failure is the answer's, never the
     * service's.
     */
    private static void answer(Path dir, Path taken, Answerer answerer)
            throws IOException, Outgrown {
        String name = stem(taken, TAKEN);
        Path question = taken.resolveSibling(name + ASKED);
        JsonObject asked = ExploreCodec.readObject(taken);
        if (!Files.isDirectory(Paths.get("/proc",
                JsonFields.primitiveString(asked, "waiter")))) {
            Files.delete(taken);
            return;
        }
        String error = "";
        int exit = 0;
        try {
            answerer.answer(asked, dir.resolve(OUT).resolve(name));
        } catch (Outgrown outgrown) {
            // Untaken: its asker sees it still waiting.
            Files.move(taken, question, StandardCopyOption.ATOMIC_MOVE);
            throw outgrown;
        } catch (OutOfHeap past) {
            error = past.getMessage();
            exit = HeapWatch.OUT_OF_HEAP;
        } catch (Exception | Error failed) {
            failed.printStackTrace();
            error = deepest(failed).toString();
            exit = 1;
        }
        JsonObject answer = new JsonObject();
        answer.addProperty("exit", exit);
        answer.addProperty("error", error);
        Path written = dir.resolve(ANSWERS).resolve("." + name + ".part");
        Files.write(written, (answer + "\n").getBytes(StandardCharsets.UTF_8));
        Files.move(written, dir.resolve(ANSWERS).resolve(name + ASKED),
                StandardCopyOption.ATOMIC_MOVE);
        Files.delete(taken);
    }

    /** The cause at the bottom of a failure's chain: what failed first. */
    private static Throwable deepest(Throwable failed) {
        Throwable cause = failed;
        while (cause.getCause() != null && cause.getCause() != cause) {
            cause = cause.getCause();
        }
        return cause;
    }

    /**
     * Ends the service when no question waits, under the lock, so no asker
     * puts one in between unseen: the directory then names no service, and
     * the next question's asker starts one.  It is the only service of the
     * directory -- an asker starts another only when the one named there has
     * ended -- and it retires only while none of its seats answers, so a
     * question taken here then was taken by a service that died: its asker's
     * to fail, never this one's to wait for (a run stopped mid-answer left
     * one, and the next run of that corpus path kept its solver 2 h past its
     * end, holding its charge).
     */
    static boolean retire(Path dir) throws IOException,
            InterruptedException {
        lock(dir);
        try {
            if (!waiting(dir, ASKED).isEmpty()) {
                return false;
            }
            Files.deleteIfExists(dir.resolve(SERVER));
            return true;
        } finally {
            Files.deleteIfExists(dir.resolve(LOCK));
        }
    }

    /**
     * Ends the service now, whatever waits ({@link Outgrown}): under the
     * lock, what {@code server} named is written to {@code retired} before
     * {@code server} goes, so an asker that saw this service may start the
     * next one ({@code run_engine.sh campaign_solve_obligation}).
     */
    static void retireOutgrown(Path dir) throws IOException,
            InterruptedException {
        lock(dir);
        try {
            Path server = dir.resolve(SERVER);
            byte[] named = Files.isRegularFile(server)
                    ? Files.readAllBytes(server) : new byte[0];
            Path written = dir.resolve("." + RETIRED + ".part");
            Files.write(written, named);
            Files.move(written, dir.resolve(RETIRED),
                    StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
            Files.deleteIfExists(server);
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
