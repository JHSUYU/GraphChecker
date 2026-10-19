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

final class Service {
    static final String LOCK = "lock";
    static final String SERVER = "server";
    static final String REQUESTS = "requests";
    static final String ANSWERS = "answers";
    static final String OUT = "out";
    static final String ASKED = ".json";
    static final String TAKEN = ".taken";
    static final String RETIRED = "retired";
    private static final long POLL_MILLIS = 100L;
    static final double BESIDE = 0.75;
    private static final long LOCK_STALE_MILLIS = 30_000L;

    interface Answerer {
        void answer(JsonObject question, Path out) throws Exception;
    }

    static final class Outgrown extends Exception {
        private static final long serialVersionUID = 1L;

        Outgrown(String why) {
            super(why);
        }
    }

    static final class OutOfHeap extends Exception {
        private static final long serialVersionUID = 1L;

        OutOfHeap(String why) {
            super(why);
        }
    }

    private Service() {
    }

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

        synchronized void awaitChange(long millis)
                throws InterruptedException {
            wait(millis);
        }

        synchronized void awaitNone() throws InterruptedException {
            while (count > 0) wait();
        }
    }

    private static Path take(Path question) {
        Path taken = question.resolveSibling(stem(question, ASKED) + TAKEN);
        try {
            Files.move(question, taken, StandardCopyOption.ATOMIC_MOVE);
        } catch (IOException takenElsewhere) {
            return null;
        }
        return taken;
    }

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

    private static Throwable deepest(Throwable failed) {
        Throwable cause = failed;
        while (cause.getCause() != null && cause.getCause() != cause) {
            cause = cause.getCause();
        }
        return cause;
    }

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
