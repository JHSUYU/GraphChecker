package edu.uva.liftlab.graphchecker.plan;

import org.junit.Test;
import org.objectweb.asm.ClassReader;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.LinkedBlockingDeque;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class LineageScanTest {

    static final class HeadOfDeque {
        void enqueueFirst(LinkedBlockingDeque<Runnable> queue, Runnable work)
                throws InterruptedException {
            queue.putFirst(work);
        }
    }

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

    static final class Work implements Runnable {
        @Override
        public void run() {
        }
    }

    static final class Waiter {
        synchronized void pace(long millis) throws InterruptedException {
            wait(millis);
        }
    }

    static final class ListWriter {
        void write(List<Object> list, Object value) {
            list.add(value);
        }
    }

    static final class Drawer {
        private static final java.util.Random RANDOM = new java.util.Random();

        int pick(int of) {
            return RANDOM.nextInt(of);
        }
    }

    static final class Shuffler {
        void order(List<Object> nodes, java.util.Random random) {
            java.util.Collections.shuffle(nodes, random);
        }
    }

    static final class Lister {
        String[] names(java.io.File directory) {
            return directory.list();
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
        assertTrue(kept(Lister.class));
        assertFalse(kept(ListWriter.class));
    }

    @Test
    public void aRootNamingAClassScansThatClassFamilyAlone() {
        Object[][] table = {
            {"a/b/TestX.class", true},
            {"a/b/TestX$1.class", true},
            {"a/b/TestX$Worker$2.class", true},
            {"a/b/TestXY.class", false},
            {"a/b/TestY.class", false},
            {"a/TestX.class", false},
        };
        for (Object[] row : table) {
            assertEquals((String) row[0], row[1], LineageScan.ofFamily(
                    java.nio.file.Paths.get((String) row[0]), "a/b/TestX"));
        }
    }

    private static boolean kept(Class<?> type) throws IOException {
        String resource = type.getName().replace('.', '/') + ".class";
        try (InputStream in = LineageScanTest.class.getClassLoader()
                .getResourceAsStream(resource)) {
            return LineageScan.handsOffWork(new ClassReader(in));
        }
    }
}
