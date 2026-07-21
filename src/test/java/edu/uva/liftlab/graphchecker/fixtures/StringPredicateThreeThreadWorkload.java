package edu.uva.liftlab.graphchecker.fixtures;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/** Three-thread workload for exact String predicate lowering. */
public final class StringPredicateThreeThreadWorkload {
    public static final String PRODUCER_A_THREAD = "string-producer-a";
    public static final String PRODUCER_B_THREAD = "string-producer-b";
    public static final String CONSUMER_THREAD = "string-consumer";
    private static final long TIMEOUT_MILLIS = 10_000L;

    private StringPredicateThreeThreadWorkload() {
    }

    public static final class PredicateProducer {
        public int compute(Boolean enabled, String text) {
            int score = 0;
            if (enabled.booleanValue()) {
                if (text.contains("needle")) {
                    score += 4;
                } else {
                    score -= 4;
                }
                if (text.startsWith("pre")) {
                    score += 2;
                }
                if (text.endsWith("end")) {
                    score += 2;
                }
                if (text.length() > 8) {
                    score++;
                }
            }
            return score;
        }
    }

    public static final class LimitProducer {
        public int compute(Boolean high) {
            return high.booleanValue() ? 10 : 7;
        }
    }

    public static final class RpcBus {
        private volatile int predicateValue;
        private volatile int limitValue;

        public void publishPredicate(int value) {
            predicateValue = value;
        }

        public void publishLimit(int value) {
            limitValue = value;
        }

        public int getRPCFromPredicate() {
            return predicateValue;
        }

        public int getRPCFromLimit() {
            return limitValue;
        }
    }

    public static final class StringPredicateBugReachedException
            extends RuntimeException {
        public StringPredicateBugReachedException(int value, int limit) {
            super("string predicate reached value > limit with value="
                    + value + ", limit=" + limit);
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

    private static final class PredicateThread extends Worker {
        private final Boolean enabled;
        private final String text;
        private final RpcBus bus;
        private final CountDownLatch peers;

        PredicateThread(Boolean enabled, String text, RpcBus bus,
                        CountDownLatch start, CountDownLatch peers) {
            super(PRODUCER_A_THREAD, start);
            this.enabled = enabled;
            this.text = text;
            this.bus = bus;
            this.peers = peers;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeer(peers);
            bus.publishPredicate(new PredicateProducer().compute(enabled,
                    text));
        }
    }

    private static final class LimitThread extends Worker {
        private final Boolean high;
        private final RpcBus bus;
        private final CountDownLatch peers;

        LimitThread(Boolean high, RpcBus bus, CountDownLatch start,
                    CountDownLatch peers) {
            super(PRODUCER_B_THREAD, start);
            this.high = high;
            this.bus = bus;
            this.peers = peers;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeer(peers);
            bus.publishLimit(new LimitProducer().compute(high));
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int value;
        private volatile int limit;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super(CONSUMER_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            value = bus.getRPCFromPredicate();
            limit = bus.getRPCFromLimit();
            if (value > limit) {
                throw new StringPredicateBugReachedException(value, limit);
            }
        }
    }

    public static final class RunResult {
        private final int value;
        private final int limit;
        private final Throwable failure;
        private final String failureThread;

        RunResult(int value, int limit, Throwable failure,
                  String failureThread) {
            this.value = value;
            this.limit = limit;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public int getValue() {
            return value;
        }

        public int getLimit() {
            return limit;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String getFailureThread() {
            return failureThread;
        }

        public boolean isBugReached() {
            return failure instanceof StringPredicateBugReachedException;
        }

        public String toJson() {
            return "{\"kind\":\"STRING_PREDICATE_THREE_THREAD_RESULT\","
                    + "\"value\":" + value + ",\"limit\":" + limit + ','
                    + "\"bugReached\":" + isBugReached() + ','
                    + "\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean enabled, String text,
                                    Boolean high)
            throws InterruptedException {
        if (enabled == null || text == null || high == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        PredicateThread producerA = new PredicateThread(enabled, text, bus,
                start, peers);
        LimitThread producerB = new LimitThread(high, bus, start, peers);
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
        return new RunResult(consumer.value, consumer.limit, failure.get(),
                failureThread.get());
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
            throw new IllegalArgumentException("expected: <enabled> <text>");
        }
        RunResult result = execute(parseBoolean(args[0]), args[1], false);
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
