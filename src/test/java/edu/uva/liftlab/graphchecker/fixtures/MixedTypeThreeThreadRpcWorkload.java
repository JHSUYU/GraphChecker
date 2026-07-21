package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Small three-thread workload covering mixed scalar inputs and a bounded loop.
 */
public final class MixedTypeThreeThreadRpcWorkload {
    public static final String PRODUCER_A_THREAD = "mixed-producer-a";
    public static final String PRODUCER_B_THREAD = "mixed-producer-b";
    public static final String CONSUMER_THREAD = "mixed-consumer";
    private static final long TIMEOUT_MILLIS = 10_000L;

    private MixedTypeThreeThreadRpcWorkload() {
    }

    public static final class MixedProducer {
        public int compute(Boolean flag, int loopCount, long distance,
                           double ratio, String text) {
            int score = -5;
            if (flag.booleanValue()) {
                score = 1;
                if (text.contains("needle")) {
                    score = 5;
                    if (distance > 100L) {
                        score = 8;
                        if (ratio >= 1.5d) {
                            score = 11;
                            int bounded = loopCount;
                            if (bounded < 0) {
                                bounded = 0;
                            }
                            if (bounded > 3) {
                                bounded = 3;
                            }
                            for (int remaining = bounded;
                                 remaining > 0; remaining--) {
                                score++;
                            }
                        }
                    }
                }
            }
            return score;
        }
    }

    public static final class ThresholdProducer {
        public int compute(Boolean high) {
            return high.booleanValue() ? 13 : 11;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch aReady = new CountDownLatch(1);
        private final CountDownLatch bReady = new CountDownLatch(1);
        private volatile int a;
        private volatile int b;

        public void publishA(int value) {
            a = value;
            aReady.countDown();
        }

        public void publishB(int value) {
            b = value;
            bReady.countDown();
        }

        public int getRPCFromA() throws InterruptedException {
            if (!aReady.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC A timed out");
            }
            return a;
        }

        public int getRPCFromB() throws InterruptedException {
            if (!bReady.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC B timed out");
            }
            return b;
        }
    }

    public static final class MixedTypeBugReachedException
            extends RuntimeException {
        public MixedTypeBugReachedException(int a, int b) {
            super("mixed consumer reached a > b with a=" + a + ", b=" + b);
        }
    }

    private abstract static class Worker extends Thread {
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

    private static final class MixedProducerThread extends Worker {
        private final Boolean flag;
        private final int loopCount;
        private final long distance;
        private final double ratio;
        private final String text;
        private final RpcBus bus;
        private final CountDownLatch peers;

        MixedProducerThread(Boolean flag, int loopCount, long distance,
                            double ratio, String text, RpcBus bus,
                            CountDownLatch start, CountDownLatch peers) {
            super(PRODUCER_A_THREAD, start);
            this.flag = flag;
            this.loopCount = loopCount;
            this.distance = distance;
            this.ratio = ratio;
            this.text = text;
            this.bus = bus;
            this.peers = peers;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeer(peers);
            int value = new MixedProducer().compute(flag, loopCount,
                    distance, ratio, text);
            bus.publishA(value);
        }
    }

    private static final class ThresholdProducerThread extends Worker {
        private final Boolean high;
        private final RpcBus bus;
        private final CountDownLatch peers;

        ThresholdProducerThread(Boolean high, RpcBus bus,
                                CountDownLatch start,
                                CountDownLatch peers) {
            super(PRODUCER_B_THREAD, start);
            this.high = high;
            this.bus = bus;
            this.peers = peers;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeer(peers);
            int value = new ThresholdProducer().compute(high);
            bus.publishB(value);
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int receivedA;
        private volatile int receivedB;
        private volatile boolean received;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super(CONSUMER_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            receivedA = a;
            receivedB = b;
            received = true;
            if (a > b) {
                throw new @CausynthExceptionTarget("multitype")
                        MixedTypeBugReachedException(a, b);
            }
        }
    }

    public static final class RunResult {
        private final int a;
        private final int b;
        private final Throwable failure;
        private final String failureThread;

        RunResult(int a, int b, Throwable failure, String failureThread) {
            this.a = a;
            this.b = b;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public int getA() {
            return a;
        }

        public int getB() {
            return b;
        }

        public Throwable getFailure() {
            return failure;
        }

        public boolean isBugReached() {
            return failure instanceof MixedTypeBugReachedException;
        }

        public String toJson() {
            return "{\"kind\":\"MIXED_TYPE_THREE_THREAD_RESULT\","
                    + "\"a\":" + a + ",\"b\":" + b + ','
                    + "\"bugReached\":" + isBugReached() + ','
                    + "\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean flag, Boolean high,
                                    int loopCount, long distance,
                                    double ratio, String text)
            throws InterruptedException {
        if (flag == null || high == null || text == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        MixedProducerThread producerA = new MixedProducerThread(flag,
                loopCount, distance, ratio, text, bus, start, peers);
        ThresholdProducerThread producerB = new ThresholdProducerThread(
                high, bus, start, peers);
        ConsumerThread consumer = new ConsumerThread(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
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
        if (!consumer.received && failure.get() == null) {
            throw new IllegalStateException("consumer produced no result");
        }
        return new RunResult(consumer.receivedA, consumer.receivedB,
                failure.get(), failureThread.get());
    }

    private static void awaitPeer(CountDownLatch peers)
            throws InterruptedException {
        peers.countDown();
        if (!peers.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
            throw new IllegalStateException("producer rendezvous timed out");
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

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException("expected: <flag> <high>");
        }
        RunResult result = execute(parseBoolean(args[0]),
                parseBoolean(args[1]), 0, 0L, 0.5d, "plain");
        System.out.println(result.toJson());
        Throwable failure = result.getFailure();
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

    private static Boolean parseBoolean(String value) {
        if ("true".equalsIgnoreCase(value)) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(value)) return Boolean.FALSE;
        throw new IllegalArgumentException("not a boolean: " + value);
    }
}
