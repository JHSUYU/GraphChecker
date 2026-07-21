package edu.uva.liftlab.graphchecker.fixtures;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/** Three-thread workload whose consumer needs both producer relations. */
public final class DependentScalarThreeThreadWorkload {
    public static final String PRODUCER_A_THREAD = "dependent-producer-a";
    public static final String PRODUCER_B_THREAD = "dependent-producer-b";
    public static final String CONSUMER_THREAD = "dependent-consumer";
    private static final long TIMEOUT_MILLIS = 10_000L;

    private DependentScalarThreeThreadWorkload() {
    }

    public static final class ArithmeticProducer {
        public int compute(Boolean add, int input) {
            int bounded = input;
            if (bounded < 0) {
                bounded = 0;
            }
            if (bounded > 4) {
                bounded = 4;
            }
            if (add.booleanValue()) {
                return bounded + 3;
            }
            return bounded - 2;
        }
    }

    public static final class TextProducer {
        public int compute(String text) {
            if (text.contains("ready")) {
                return 5;
            }
            return 9;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch arithmeticReady =
                new CountDownLatch(1);
        private final CountDownLatch textReady = new CountDownLatch(1);
        private volatile int arithmeticValue;
        private volatile int textValue;

        public void publishArithmetic(int value) {
            arithmeticValue = value;
            arithmeticReady.countDown();
        }

        public void publishText(int value) {
            textValue = value;
            textReady.countDown();
        }

        public int getRPCFromArithmetic() throws InterruptedException {
            if (!arithmeticReady.await(TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("arithmetic RPC timed out");
            }
            return arithmeticValue;
        }

        public int getRPCFromText() throws InterruptedException {
            if (!textReady.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("text RPC timed out");
            }
            return textValue;
        }
    }

    public static final class DependentScalarBugReachedException
            extends RuntimeException {
        public DependentScalarBugReachedException(int arithmetic,
                                                  int text) {
            super("dependent branch reached arithmetic > text with "
                    + "arithmetic=" + arithmetic + ", text=" + text);
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

    private static final class ArithmeticThread extends Worker {
        private final Boolean add;
        private final int input;
        private final RpcBus bus;
        private final CountDownLatch peers;

        ArithmeticThread(Boolean add, int input, RpcBus bus,
                         CountDownLatch start, CountDownLatch peers) {
            super(PRODUCER_A_THREAD, start);
            this.add = add;
            this.input = input;
            this.bus = bus;
            this.peers = peers;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeer(peers);
            int value = new ArithmeticProducer().compute(add, input);
            bus.publishArithmetic(value);
        }
    }

    private static final class TextThread extends Worker {
        private final String text;
        private final RpcBus bus;
        private final CountDownLatch peers;

        TextThread(String text, RpcBus bus, CountDownLatch start,
                   CountDownLatch peers) {
            super(PRODUCER_B_THREAD, start);
            this.text = text;
            this.bus = bus;
            this.peers = peers;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeer(peers);
            int value = new TextProducer().compute(text);
            bus.publishText(value);
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int arithmetic;
        private volatile int text;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super(CONSUMER_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int receivedArithmetic = bus.getRPCFromArithmetic();
            int receivedText = bus.getRPCFromText();
            arithmetic = receivedArithmetic;
            text = receivedText;
            if (receivedArithmetic > receivedText) {
                throw new DependentScalarBugReachedException(
                        receivedArithmetic, receivedText);
            }
        }
    }

    public static final class RunResult {
        private final int arithmetic;
        private final int text;
        private final Throwable failure;
        private final String failureThread;

        RunResult(int arithmetic, int text, Throwable failure,
                  String failureThread) {
            this.arithmetic = arithmetic;
            this.text = text;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public int getArithmetic() {
            return arithmetic;
        }

        public int getText() {
            return text;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String getFailureThread() {
            return failureThread;
        }

        public boolean isBugReached() {
            return failure instanceof DependentScalarBugReachedException;
        }

        public String toJson() {
            return "{\"kind\":\"DEPENDENT_SCALAR_THREE_THREAD_RESULT\","
                    + "\"arithmetic\":" + arithmetic + ",\"text\":"
                    + text + ",\"bugReached\":" + isBugReached() + ','
                    + "\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean add, int input, String text)
            throws InterruptedException {
        if (add == null || text == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        ArithmeticThread producerA = new ArithmeticThread(add, input, bus,
                start, peers);
        TextThread producerB = new TextThread(text, bus, start, peers);
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
        return new RunResult(consumer.arithmetic, consumer.text,
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
            throw new IllegalArgumentException("expected: <add> <text>");
        }
        RunResult result = execute(parseBoolean(args[0]), 0, args[1]);
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
