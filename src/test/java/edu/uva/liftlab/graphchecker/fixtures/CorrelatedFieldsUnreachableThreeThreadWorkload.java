package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Unreachable target over two correlated fields from one producer invocation.
 *
 * <p>The pair producer publishes {@code left = value} and
 * {@code right = 20 - value} together. The independent producer publishes
 * either 19 or 21, so the consumer equality is impossible. Proving that fact
 * requires one joint summary for both pair fields; independently selected
 * producer paths could invent a false combination.</p>
 */
public final class CorrelatedFieldsUnreachableThreeThreadWorkload {
    private static final long TIMEOUT_MILLIS = 10_000L;

    private CorrelatedFieldsUnreachableThreeThreadWorkload() {
    }

    static final class NumericLeaf {
        int seed;
        int delta;

        NumericLeaf(int seed, int delta) {
            this.seed = seed;
            this.delta = delta;
        }
    }

    static final class InputEnvelope {
        NumericLeaf numeric;

        InputEnvelope(int seed, int delta) {
            numeric = new NumericLeaf(seed, delta);
        }
    }

    public static final class PairProducer {
        InputEnvelope input;

        PairProducer(int seed, int delta) {
            input = new InputEnvelope(seed, delta);
        }

        public int compute(Boolean upperBand) {
            int value = input.numeric.seed + input.numeric.delta;
            if (value < 0) {
                value = 0;
            }
            if (value > 5) {
                value = 5;
            }
            return upperBand.booleanValue() ? value + 5 : value + 2;
        }
    }

    public static final class LimitProducer {
        public int compute(Boolean high) {
            return high.booleanValue() ? 21 : 19;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch pairReady = new CountDownLatch(1);
        private final CountDownLatch limitReady = new CountDownLatch(1);
        private volatile int left;
        private volatile int right;
        private volatile int limit;
        private volatile int pairPublishCount;
        private volatile int limitPublishCount;
        private volatile int leftReadCount;
        private volatile int rightReadCount;
        private volatile int limitReadCount;
        private volatile int publicationClock;
        private volatile int pairPublishOrdinal;
        private volatile int limitPublishOrdinal;
        private volatile int readClock;
        private volatile int leftReadOrdinal;
        private volatile int rightReadOrdinal;
        private volatile int limitReadOrdinal;

        public void publishPair(int value) {
            left = value;
            right = 20 - value;
            pairPublishCount++;
            pairPublishOrdinal = ++publicationClock;
            pairReady.countDown();
        }

        public void publishLimit(int value) {
            limit = value;
            limitPublishCount++;
            limitPublishOrdinal = ++publicationClock;
            limitReady.countDown();
        }

        public int getLeft() throws InterruptedException {
            pairReady.await();
            leftReadCount++;
            leftReadOrdinal = ++readClock;
            return left;
        }

        public int getRight() throws InterruptedException {
            pairReady.await();
            rightReadCount++;
            rightReadOrdinal = ++readClock;
            return right;
        }

        public int getLimit() throws InterruptedException {
            limitReady.await();
            limitReadCount++;
            limitReadOrdinal = ++readClock;
            return limit;
        }

        void requireSingleTransfer() {
            if (pairPublishCount != 1 || limitPublishCount != 1
                    || leftReadCount != 1 || rightReadCount != 1
                    || limitReadCount != 1 || pairPublishOrdinal != 1
                    || limitPublishOrdinal != 2 || leftReadOrdinal != 1
                    || rightReadOrdinal != 2 || limitReadOrdinal != 3) {
                throw new IllegalStateException(
                        "correlated field transfer order/count changed");
            }
        }

    }

    public static final class ImpossibleCorrelatedFieldsException
            extends RuntimeException {
        ImpossibleCorrelatedFieldsException(int left, int right, int limit) {
            super("correlated sum reached impossible limit: " + left + " + "
                    + right + " == " + limit);
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
                start.await();
                executeWorker();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                throw new IllegalStateException("worker interrupted",
                        interrupted);
            }
        }

        abstract void executeWorker() throws InterruptedException;
    }

    private static final class PairProducerThread extends Worker {
        private final Boolean upperBand;
        private final PairProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch pairPublished;

        PairProducerThread(Boolean upperBand, PairProducer producer,
                           RpcBus bus, CountDownLatch start,
                           CountDownLatch peers,
                           CountDownLatch pairPublished) {
            super("correlated-pair-producer", start);
            this.upperBand = upperBand;
            this.producer = producer;
            this.bus = bus;
            this.peers = peers;
            this.pairPublished = pairPublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            bus.publishPair(producer.compute(upperBand));
            pairPublished.countDown();
        }
    }

    private static final class LimitProducerThread extends Worker {
        private final Boolean high;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch pairPublished;

        LimitProducerThread(Boolean high, RpcBus bus, CountDownLatch start,
                            CountDownLatch peers,
                            CountDownLatch pairPublished) {
            super("correlated-limit-producer", start);
            this.high = high;
            this.bus = bus;
            this.peers = peers;
            this.pairPublished = pairPublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            pairPublished.await();
            bus.publishLimit(new LimitProducer().compute(high));
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int left;
        private volatile int right;
        private volatile int limit;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super("correlated-fields-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int receivedLeft = bus.getLeft();
            int receivedRight = bus.getRight();
            int receivedLimit = bus.getLimit();
            left = receivedLeft;
            right = receivedRight;
            limit = receivedLimit;
            if (receivedLeft + receivedRight == receivedLimit) {
                throw new @CausynthExceptionTarget(
                        "unreachable-correlated-fields")
                        ImpossibleCorrelatedFieldsException(receivedLeft,
                        receivedRight, receivedLimit);
            }
        }
    }

    public static final class RunResult {
        private final int left;
        private final int right;
        private final int limit;
        private final Throwable failure;
        private final String failureThread;

        RunResult(int left, int right, int limit, Throwable failure,
                  String failureThread) {
            this.left = left;
            this.right = right;
            this.limit = limit;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String toJson() {
            return "{\"kind\":\"CORRELATED_FIELDS_UNREACHABLE_RESULT\","
                    + "\"left\":" + left + ",\"right\":" + right
                    + ",\"limit\":" + limit + ",\"bugReached\":"
                    + (failure instanceof
                    ImpossibleCorrelatedFieldsException)
                    + ",\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean upperBand, Boolean high)
            throws InterruptedException {
        if (upperBand == null || high == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        CountDownLatch pairPublished = new CountDownLatch(1);
        PairProducerThread pair = new PairProducerThread(upperBand,
                new PairProducer(-2, 1), bus, start, peers, pairPublished);
        LimitProducerThread limit = new LimitProducerThread(high, bus, start,
                peers, pairPublished);
        ConsumerThread consumer = new ConsumerThread(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        pair.setUncaughtExceptionHandler(handler);
        limit.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        pair.start();
        limit.start();
        start.countDown();
        join(pair);
        join(limit);
        consumer.start();
        join(consumer);
        bus.requireSingleTransfer();
        return new RunResult(consumer.left, consumer.right, consumer.limit,
                failure.get(), failureThread.get());
    }

    private static void join(Thread thread) throws InterruptedException {
        thread.join(TIMEOUT_MILLIS);
        if (thread.isAlive()) {
            thread.interrupt();
            throw new IllegalStateException(
                    "worker did not terminate: " + thread.getName());
        }
    }

    private static void awaitPeers(CountDownLatch peers)
            throws InterruptedException {
        peers.countDown();
        peers.await();
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <upperBand> <highLimit>");
        }
        RunResult result = execute(parseBoolean(args[0]),
                parseBoolean(args[1]));
        System.out.println(result.toJson());
        rethrow(result.getFailure());
    }

    private static Boolean parseBoolean(String value) {
        if ("true".equalsIgnoreCase(value)) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(value)) return Boolean.FALSE;
        throw new IllegalArgumentException("not a boolean: " + value);
    }

    private static void rethrow(Throwable failure) {
        if (failure instanceof RuntimeException) {
            throw (RuntimeException) failure;
        }
        if (failure instanceof Error) throw (Error) failure;
        if (failure != null) {
            throw new IllegalStateException("worker failed", failure);
        }
    }
}
