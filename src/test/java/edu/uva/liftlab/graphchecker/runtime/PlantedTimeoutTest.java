package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A timed wait's planted timeout takes only where the real call could time
 * out (SYMBOL-SCOPE §4.2): where it returns or throws at once the world is
 * impossible, refused by name, and the call runs.
 */
public class PlantedTimeoutTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Before
    public void openSession() throws Exception {
        RowRuntime.resetForTests();
        Path results = folder.getRoot().toPath().resolve("iteration-0000")
                .resolve("seed-result").resolve(
                        "concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
    }

    @After
    public void clear() {
        Thread.interrupted();
        RowRuntime.resetForTests();
    }

    @Test
    public void aTimeoutTheCallCouldNotReachIsRefused() throws Exception {
        CountDownLatch open = new CountDownLatch(0);
        CountDownLatch closed = new CountDownLatch(1);
        ArrayBlockingQueue<String> holding = new ArrayBlockingQueue<>(1);
        holding.add("x");
        ReentrantLock free = new ReentrantLock();
        ReentrantLock heldHere = new ReentrantLock();
        heldHere.lock();
        ReentrantReadWriteLock rw = new ReentrantReadWriteLock();
        rw.writeLock().lock();
        Object[][] rows = {
            // what is waited on, the permits asked, why it answers at once
            {open, 1, "the latch is open"},
            {closed, 1, null},
            {CompletableFuture.completedFuture("x"), 1, "the future is done"},
            {new CompletableFuture<String>(), 1, null},
            {holding, 1, "the queue holds an element"},
            {new ArrayBlockingQueue<String>(1), 1, null},
            {free, 1, "the lock is free or held by this thread"},
            {heldHere, 1, "the lock is free or held by this thread"},
            {rw.writeLock(), 1, "the write lock is held by this thread"},
            {new Semaphore(2), 2, "the semaphore has the permits"},
            {new Semaphore(1), 2, null},
            {null, 1, null},
        };
        for (Object[] row : rows) {
            assertEquals(String.valueOf(row[0]), row[2],
                    TimedWaits.answeredAtOnce(row[0], (Integer) row[1]));
        }
        Thread.currentThread().interrupt();
        assertEquals("the thread is interrupted, so the wait throws at once",
                TimedWaits.answeredAtOnce(closed, 1));
        Thread.interrupted();

        // A replay: the call runs, and the plant is refused, BLOCKING.
        assertTrue(TimedWaits.timesOut(closed, 1, "FAULT:TIMED_WAIT:AWAIT"));
        assertFalse(TimedWaits.timesOut(open, 1, "FAULT:TIMED_WAIT:AWAIT"));
        List<GapRow> gaps = RowCodec.readAll(SessionDir.of(folder.getRoot()
                        .toPath().resolve("iteration-0000"),
                RowRuntime.sessionId()).gaps(), RowCodec::readGap);
        assertEquals(1, gaps.size());
        assertEquals(GapKind.ASSIGNMENT_UNPLANTED, gaps.get(0).kind());
        assertEquals(GapClass.BLOCKING, gaps.get(0).cls());
        assertTrue(gaps.get(0).detail(),
                gaps.get(0).detail().contains("the latch is open"));
    }
}
