package edu.uva.liftlab.graphchecker.fixtures.stress;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Fixed three-thread/shared-field RPC shape for generated stress fixtures.
 */
final class StressRpcFixtureSupport {
    static final long TIMEOUT_MILLIS = 10_000L;

    private StressRpcFixtureSupport() {
    }

    static final class Bus {
        private final CountDownLatch aReady = new CountDownLatch(1);
        private final CountDownLatch bReady = new CountDownLatch(1);
        private volatile int a;
        private volatile int b;
        private volatile long aPublisherThreadId;
        private volatile long bPublisherThreadId;
        private volatile int aReceivedValue;
        private volatile int bReceivedValue;
        private volatile long aConsumerThreadId;
        private volatile long bConsumerThreadId;
        private volatile int aReceiveCount;
        private volatile int bReceiveCount;

        void publishA(int value) {
            a = value;
            aPublisherThreadId = Thread.currentThread().getId();
            aReady.countDown();
        }

        void publishB(int value) {
            b = value;
            bPublisherThreadId = Thread.currentThread().getId();
            bReady.countDown();
        }

        int getRPCFromA() throws InterruptedException {
            await(aReady);
            int received = a;
            aReceivedValue = received;
            aConsumerThreadId = Thread.currentThread().getId();
            aReceiveCount++;
            return received;
        }

        int getRPCFromB() throws InterruptedException {
            await(bReady);
            int received = b;
            bReceivedValue = received;
            bConsumerThreadId = Thread.currentThread().getId();
            bReceiveCount++;
            return received;
        }

        void verifySingleExchange() {
            if (aReceiveCount != 1 || bReceiveCount != 1
                    || aPublisherThreadId <= 0L || bPublisherThreadId <= 0L
                    || aConsumerThreadId <= 0L || bConsumerThreadId <= 0L
                    || aPublisherThreadId == aConsumerThreadId
                    || bPublisherThreadId == bConsumerThreadId
                    || a != aReceivedValue || b != bReceivedValue) {
                throw new IllegalStateException("RPC exchange was not 1:1");
            }
        }

        private static void await(CountDownLatch ready)
                throws InterruptedException {
            if (!ready.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC timed out");
            }
        }
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

    static Throwable run(CountDownLatch start, Worker producerA,
                         Worker producerB, Worker consumer, Bus bus)
            throws InterruptedException {
        AtomicReference<Throwable> failure = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) ->
                failure.compareAndSet(null, throwable);
        producerA.setUncaughtExceptionHandler(handler);
        producerB.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);
        producerA.start();
        producerB.start();
        start.countDown();
        join(producerA);
        join(producerB);
        consumer.start();
        join(consumer);
        bus.verifySingleExchange();
        return failure.get();
    }

    static Boolean parseBoolean(String value) {
        if ("true".equalsIgnoreCase(value)) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(value)) return Boolean.FALSE;
        throw new IllegalArgumentException("not a boolean: " + value);
    }

    static void propagate(Throwable failure) {
        if (failure instanceof RuntimeException) {
            throw (RuntimeException) failure;
        }
        if (failure instanceof Error) throw (Error) failure;
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
