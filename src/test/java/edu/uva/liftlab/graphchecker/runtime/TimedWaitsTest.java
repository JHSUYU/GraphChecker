package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.TimeUnit;
import org.junit.Test;

public class TimedWaitsTest {
    /**
     * A poll(0) is no wait: it takes what another thread offers right now.
     * A DataNode proxy's IPC sender polls its SynchronousQueue at maxIdleTime
     * 0, and the caller's offer is only ever taken that way.
     */
    @Test(timeout = 20000L)
    public void aZeroTimeoutPollTakesTheHandOff() throws Exception {
        SynchronousQueue<String> queue = new SynchronousQueue<String>();
        Thread caller = new Thread(() -> {
            try {
                while (!queue.offer("call", 1L, TimeUnit.SECONDS)) {
                    // As Client.Connection.sendRpcRequest does.
                }
            } catch (InterruptedException stopped) {
                Thread.currentThread().interrupt();
            }
        });
        caller.start();
        Object taken = null;
        long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(10L);
        while (taken == null && System.nanoTime() < end) {
            taken = TimedWaits.poll(queue, 0L, TimeUnit.MILLISECONDS,
                    "sender#u0");
        }
        caller.interrupt();
        caller.join();
        assertEquals("call", taken);
    }
}
