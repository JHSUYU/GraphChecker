package edu.uva.liftlab.graphchecker.plan;

import org.junit.Test;
import org.objectweb.asm.ClassReader;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.LinkedBlockingDeque;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** The lineage scope keeps every class that starts, hands off or runs work,
 *  waits, draws, or reads a JVM clock. */
public class LineageScanTest {

    /** The DataNode actor's shape: a command put at the head of a deque. */
    static final class HeadOfDeque {
        void enqueueFirst(LinkedBlockingDeque<Runnable> queue, Runnable work)
                throws InterruptedException {
            queue.putFirst(work);
        }
    }

    /** The command processor's: the work taken off a queue. */
    static final class Taker {
        Object next(BlockingQueue<Object> queue) throws InterruptedException {
            return queue.take();
        }
    }

    static final class Starter {
        void begin(Thread thread) {
            thread.start();
        }
    }

    static final class Submitter {
        void submit(ExecutorService pool, Runnable work) {
            pool.execute(work);
        }
    }

    /** A work entry is kept even when nothing in it hands anything off. */
    static final class Work implements Runnable {
        @Override
        public void run() {
        }
    }

    /** The DataNode actor's pacing: a timed wait on its own monitor. */
    static final class Waiter {
        synchronized void pace(long millis) throws InterruptedException {
            wait(millis);
        }
    }

    /** A list's add is a write, not a handoff. */
    static final class ListWriter {
        void write(List<Object> list, Object value) {
            list.add(value);
        }
    }

    /** DFSNetworkTopology's shape: a pick from one shared static Random. */
    static final class Drawer {
        private static final java.util.Random RANDOM = new java.util.Random();

        int pick(int of) {
            return RANDOM.nextInt(of);
        }
    }

    /** NetworkTopology's: a Random handed to the JDK's shuffle. */
    static final class Shuffler {
        void order(List<Object> nodes, java.util.Random random) {
            java.util.Collections.shuffle(nodes, random);
        }
    }

    /** Hadoop's Time: the JVM clock every Hadoop clock reads through. */
    static final class ClockReader {
        long now() {
            return System.nanoTime() / 1_000_000L;
        }
    }

    @Test
    public void everyHandoffAndWaitIsKeptAndAListWriteIsNot()
            throws IOException {
        assertTrue(kept(HeadOfDeque.class));
        assertTrue(kept(Taker.class));
        assertTrue(kept(Starter.class));
        assertTrue(kept(Submitter.class));
        assertTrue(kept(Work.class));
        assertTrue(kept(Waiter.class));
        assertTrue(kept(Drawer.class));
        assertTrue(kept(Shuffler.class));
        assertTrue(kept(ClockReader.class));
        assertFalse(kept(ListWriter.class));
    }

    @Test
    public void aDequesEndsAreHandoffsForTheWeaveToo() {
        WorkStartSites.Types deque = LinkedBlockingDeque.class.getName()
                ::equals;
        WorkStartSites.Types queue = type -> type.equals(
                BlockingQueue.class.getName())
                || type.equals(LinkedBlockingDeque.class.getName());
        assertFalse("the receiver type decides", WorkStartSites
                .submitsToQueue("putFirst", 1, deque));
        assertTrue(WorkStartSites.submitsToQueue("putFirst", 1, queue));
        assertTrue(WorkStartSites.claimsFromQueue("takeFirst", queue));
        assertTrue(WorkStartSites.claimsFromQueue("pollLast", queue));
    }

    private static boolean kept(Class<?> type) throws IOException {
        String resource = type.getName().replace('.', '/') + ".class";
        try (InputStream in = LineageScanTest.class.getClassLoader()
                .getResourceAsStream(resource)) {
            return LineageScan.handsOffWork(new ClassReader(in));
        }
    }
}
