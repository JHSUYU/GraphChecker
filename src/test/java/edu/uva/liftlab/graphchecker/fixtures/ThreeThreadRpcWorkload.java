package edu.uva.liftlab.graphchecker.fixtures;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Standalone three-thread target used by the generic concolic workflow.
 *
 * <p>The application has no dependency on GraphChecker.  Producer values cross
 * thread boundaries only through {@link RpcBus}; the topology file beside the
 * generic workflow declares which producer return reaches which consumer RPC
 * result.  Values and thread identities are still observed from this concrete
 * execution rather than declared in that topology.</p>
 */
public final class ThreeThreadRpcWorkload {
    public static final String PRODUCER_A_THREAD = "rpc-producer-a";
    public static final String PRODUCER_B_THREAD = "rpc-producer-b";
    public static final String CONSUMER_THREAD = "rpc-consumer";
    private static final long JOIN_TIMEOUT_MILLIS = 10_000L;

    private ThreeThreadRpcWorkload() {
    }

    public static final class ProducerA {
        public int compute(Boolean b1) {
            int a = 0;
            if (b1.booleanValue()) {
                a = 1;
            } else {
                a = -1;
            }
            return a;
        }
    }

    public static final class ProducerB {
        public int compute(Boolean b2) {
            int b = 10;
            if (b2.booleanValue()) {
                b = 0;
            }
            return b;
        }
    }

    /** The two methods named getRPCFrom* are the consumer-side RPC boundary. */
    public static final class RpcBus {
        private final CountDownLatch aReady = new CountDownLatch(1);
        private final CountDownLatch bReady = new CountDownLatch(1);
        private volatile int a;
        private volatile int b;
        private volatile long aPublisherThreadId;
        private volatile long bPublisherThreadId;

        public void publishA(int value) {
            a = value;
            aPublisherThreadId = Thread.currentThread().getId();
            aReady.countDown();
        }

        public void publishB(int value) {
            b = value;
            bPublisherThreadId = Thread.currentThread().getId();
            bReady.countDown();
        }

        public int getRPCFromA() throws InterruptedException {
            if (!aReady.await(JOIN_TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC A timed out");
            }
            return a;
        }

        public int getRPCFromB() throws InterruptedException {
            if (!bReady.await(JOIN_TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC B timed out");
            }
            return b;
        }
    }

    public static final class BugReachedException extends RuntimeException {
        public BugReachedException(int a, int b) {
            super("consumer reached a > b with a=" + a + ", b=" + b);
        }
    }

    private abstract static class WorkerThread extends Thread {
        private final CountDownLatch start;

        WorkerThread(String name, CountDownLatch start) {
            super(name);
            this.start = start;
        }

        @Override
        public final void run() {
            try {
                if (!start.await(JOIN_TIMEOUT_MILLIS,
                        TimeUnit.MILLISECONDS)) {
                    throw new IllegalStateException("start gate timed out");
                }
                executeWorker();
            } catch (InterruptedException exception) {
                Thread.currentThread().interrupt();
                throw new IllegalStateException("worker interrupted", exception);
            }
        }

        abstract void executeWorker() throws InterruptedException;
    }

    private static final class ProducerAThread extends WorkerThread {
        private final Boolean input;
        private final RpcBus bus;

        ProducerAThread(Boolean input, RpcBus bus, CountDownLatch start) {
            super(PRODUCER_A_THREAD, start);
            this.input = input;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            int a = new ProducerA().compute(input);
            bus.publishA(a);
        }
    }

    private static final class ProducerBThread extends WorkerThread {
        private final Boolean input;
        private final RpcBus bus;

        ProducerBThread(Boolean input, RpcBus bus, CountDownLatch start) {
            super(PRODUCER_B_THREAD, start);
            this.input = input;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            int b = new ProducerB().compute(input);
            bus.publishB(b);
        }
    }

    private static final class ConsumerThread extends WorkerThread {
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
                throw new BugReachedException(a, b);
            }
        }
    }

    public static final class RpcObservation {
        private final String channel;
        private final int publishedValue;
        private final int receivedValue;
        private final long publisherThreadId;
        private final long consumerThreadId;
        private final String valueFingerprint;

        RpcObservation(String channel, int publishedValue, int receivedValue,
                       long publisherThreadId, long consumerThreadId) {
            this.channel = channel;
            this.publishedValue = publishedValue;
            this.receivedValue = receivedValue;
            this.publisherThreadId = publisherThreadId;
            this.consumerThreadId = consumerThreadId;
            this.valueFingerprint = fingerprint(channel, publishedValue,
                    receivedValue);
        }

        public String getChannel() {
            return channel;
        }

        public int getPublishedValue() {
            return publishedValue;
        }

        public int getReceivedValue() {
            return receivedValue;
        }

        public long getPublisherThreadId() {
            return publisherThreadId;
        }

        public long getConsumerThreadId() {
            return consumerThreadId;
        }

        public String getValueFingerprint() {
            return valueFingerprint;
        }

        public boolean isRuntimeValueEqualityObserved() {
            return publishedValue == receivedValue
                    && publisherThreadId != consumerThreadId;
        }

        private String toJson() {
            return "{\"channel\":\"" + channel + "\","
                    + "\"publishedValue\":" + publishedValue + ","
                    + "\"receivedValue\":" + receivedValue + ","
                    + "\"publisherThreadId\":" + publisherThreadId + ","
                    + "\"consumerThreadId\":" + consumerThreadId + ","
                    + "\"valueEqualityObserved\":"
                    + isRuntimeValueEqualityObserved() + ","
                    + "\"valueFingerprint\":\"" + valueFingerprint
                    + "\"}";
        }
    }

    public static final class RunResult {
        private final Boolean b1;
        private final Boolean b2;
        private final int a;
        private final int b;
        private final boolean bugReached;
        private final long[] workerThreadIds;
        private final String failureThread;
        private final Throwable failure;
        private final List<RpcObservation> rpcObservations;

        RunResult(Boolean b1, Boolean b2, int a, int b,
                  long[] workerThreadIds, String failureThread,
                  Throwable failure, List<RpcObservation> observations) {
            this.b1 = b1;
            this.b2 = b2;
            this.a = a;
            this.b = b;
            this.bugReached = failure instanceof BugReachedException;
            this.workerThreadIds = workerThreadIds.clone();
            this.failureThread = failureThread;
            this.failure = failure;
            this.rpcObservations = Collections.unmodifiableList(
                    new ArrayList<>(observations));
        }

        public Boolean getB1() {
            return b1;
        }

        public Boolean getB2() {
            return b2;
        }

        public int getA() {
            return a;
        }

        public int getB() {
            return b;
        }

        public boolean isBugReached() {
            return bugReached;
        }

        public long[] getWorkerThreadIds() {
            return workerThreadIds.clone();
        }

        public String getFailureThread() {
            return failureThread;
        }

        public Throwable getFailure() {
            return failure;
        }

        public List<RpcObservation> getRpcObservations() {
            return rpcObservations;
        }

        public String toJson() {
            StringBuilder observations = new StringBuilder();
            for (RpcObservation observation : rpcObservations) {
                if (observations.length() > 0) {
                    observations.append(',');
                }
                observations.append(observation.toJson());
            }
            return "{\"kind\":\"THREE_THREAD_RPC_RESULT\","
                    + "\"b1\":" + b1 + ",\"b2\":" + b2 + ","
                    + "\"a\":" + a + ",\"b\":" + b + ","
                    + "\"bugReached\":" + bugReached + ","
                    + "\"workerThreadIds\":[" + workerThreadIds[0]
                    + ',' + workerThreadIds[1] + ',' + workerThreadIds[2]
                    + "],\"failureThread\":"
                    + (failureThread == null ? "null" : "\""
                    + failureThread + "\"") + ",\"rpcObservations\":["
                    + observations + "]}";
        }
    }

    public static RunResult execute(Boolean b1, Boolean b2)
            throws InterruptedException {
        if (b1 == null || b2 == null) {
            throw new IllegalArgumentException("b1 and b2 must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        ProducerAThread producerA = new ProducerAThread(b1, bus, start);
        ProducerBThread producerB = new ProducerBThread(b2, bus, start);
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
        consumer.start();
        start.countDown();
        join(producerA);
        join(producerB);
        join(consumer);
        if (!consumer.received && failure.get() == null) {
            throw new IllegalStateException("consumer produced no observation");
        }

        int a = consumer.received ? consumer.receivedA : bus.a;
        int b = consumer.received ? consumer.receivedB : bus.b;
        List<RpcObservation> observations = new ArrayList<>();
        observations.add(new RpcObservation("A", bus.a, a,
                bus.aPublisherThreadId, consumer.getId()));
        observations.add(new RpcObservation("B", bus.b, b,
                bus.bPublisherThreadId, consumer.getId()));
        return new RunResult(b1, b2, a, b,
                new long[]{producerA.getId(), producerB.getId(),
                        consumer.getId()}, failureThread.get(), failure.get(),
                observations);
    }

    private static void join(Thread thread) throws InterruptedException {
        thread.join(JOIN_TIMEOUT_MILLIS);
        if (thread.isAlive()) {
            thread.interrupt();
            throw new IllegalStateException("worker did not terminate: "
                    + thread.getName());
        }
    }

    private static String fingerprint(String channel, int published,
                                      int received) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(("int:" + channel + ':' + published
                    + ':' + received).getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder("sha256:");
            for (byte value : bytes) {
                result.append(String.format("%02x", value & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 unavailable", impossible);
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException("expected: <b1> <b2>");
        }
        RunResult result = execute(parseBoolean(args[0]),
                parseBoolean(args[1]));
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
        if ("true".equalsIgnoreCase(value)) {
            return Boolean.TRUE;
        }
        if ("false".equalsIgnoreCase(value)) {
            return Boolean.FALSE;
        }
        throw new IllegalArgumentException("not a boolean: " + value);
    }
}
