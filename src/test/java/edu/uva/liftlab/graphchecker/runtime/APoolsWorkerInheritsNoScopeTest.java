package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A thread starts in its creator's scope, but a pool's worker does not: the
 * pool creates it while one caller submits, and it outlives that task.
 */
public class APoolsWorkerInheritsNoScopeTest {
    private long token;

    @Before
    public void enterScope() {
        Lineage.resetForTests();
        token = Lineage.pushRoot("t/n0#epoch0", Role.of("OVERSEER_TASK"), "");
    }

    @After
    public void leaveScope() {
        Lineage.pop(token);
        Lineage.resetForTests();
    }

    @Test
    public void aThreadInheritsItsCreatorsScopeAndAPoolsWorkerDoesNot()
            throws Exception {
        final AtomicBoolean thread = new AtomicBoolean();
        Thread plain = new Thread(() -> thread.set(Lineage.named()));
        plain.start();
        plain.join(5000L);
        assertTrue("a plain thread starts in its creator's scope", thread.get());

        final AtomicBoolean worker = new AtomicBoolean(true);
        ExecutorService pool = Executors.newSingleThreadExecutor();
        try {
            // The submit grows the pool: the worker is created right here.
            pool.submit(() -> worker.set(Lineage.named())).get(5, TimeUnit.SECONDS);
        } finally {
            pool.shutdownNow();
        }
        assertFalse("the worker the submit created starts in no scope",
                worker.get());
    }
}
