package edu.uva.liftlab.graphchecker.fixtures;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Small harness shared by the fixed-order three-thread fixture workloads.
 */
final class FixedOrderRpcFixtureSupport {
    // Hundreds of independent custom-JDK replays may be scheduled at once;
    // the timeout is only a deadlock guard and must not turn host load into a
    // semantic fixture failure.
    static final long TIMEOUT_MILLIS = 60_000L;

    private FixedOrderRpcFixtureSupport() {
    }

    abstract static class Worker extends Thread {
        private final CountDownLatch start;

        Worker(String name, CountDownLatch start) {
            super(name);
            this.start = start;
        }

        @Override
        public final void run() {
            try {
                if (!start.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                    throw new IllegalStateException("start gate timed out");
                }
                executeWorker();
            } catch (InterruptedException exception) {
                Thread.currentThread().interrupt();
                throw new IllegalStateException("worker interrupted",
                        exception);
            }
        }

        abstract void executeWorker() throws InterruptedException;
    }

    static final class ProducerGate {
        private final CountDownLatch entered = new CountDownLatch(2);

        void enterAndAwaitPeer() throws InterruptedException {
            entered.countDown();
            if (!entered.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException(
                        "producer rendezvous timed out");
            }
        }
    }

    static Throwable run(CountDownLatch start, Worker firstProducer,
                         Worker secondProducer, Worker consumer)
            throws InterruptedException {
        AtomicReference<Throwable> failure = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) ->
                failure.compareAndSet(null, throwable);
        firstProducer.setUncaughtExceptionHandler(handler);
        secondProducer.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        firstProducer.start();
        secondProducer.start();
        start.countDown();
        join(firstProducer);
        join(secondProducer);
        consumer.start();
        join(consumer);
        return failure.get();
    }

    static Boolean parseBoolean(String value) {
        if ("true".equalsIgnoreCase(value)) {
            return Boolean.TRUE;
        }
        if ("false".equalsIgnoreCase(value)) {
            return Boolean.FALSE;
        }
        throw new IllegalArgumentException("not a boolean: " + value);
    }

    static void propagate(Throwable failure) {
        if (failure instanceof RuntimeException) {
            throw (RuntimeException) failure;
        }
        if (failure instanceof Error) {
            throw (Error) failure;
        }
        if (failure != null) {
            throw new IllegalStateException("worker failed", failure);
        }
    }

    private static void join(Thread thread) throws InterruptedException {
        thread.join(TIMEOUT_MILLIS);
        if (thread.isAlive()) {
            thread.interrupt();
            throw new IllegalStateException("worker did not terminate: "
                    + thread.getName());
        }
    }
}
