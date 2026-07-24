package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Unreachable parity target whose inputs cross plain nested object fields and
 * helper-call parameters before reaching two shared scalar RPC fields.
 */
public final class NestedObjectPropagationUnreachableThreeThreadWorkload {
    private static final long TIMEOUT_MILLIS = 10_000L;

    private NestedObjectPropagationUnreachableThreeThreadWorkload() {
    }

    static final class SwitchLeaf {
        boolean enabled;

        SwitchLeaf(Boolean enabled) {
            this.enabled = enabled.booleanValue();
        }
    }

    static final class MeasureLeaf {
        int base;
        int adjustment;

        MeasureLeaf(int base, int adjustment) {
            this.base = base;
            this.adjustment = adjustment;
        }
    }

    static final class Payload {
        SwitchLeaf control;
        MeasureLeaf measure;

        Payload(Boolean enabled, int base, int adjustment) {
            control = new SwitchLeaf(enabled);
            measure = new MeasureLeaf(base, adjustment);
        }
    }

    static final class Envelope {
        Payload payload;

        Envelope(Boolean enabled, int base, int adjustment) {
            payload = new Payload(enabled, base, adjustment);
        }
    }

    public static final class OddProducer {
        Envelope envelope;

        OddProducer(Boolean enabled) {
            envelope = new Envelope(enabled, -1, -1);
        }

        public int compute() {
            return first(envelope);
        }

        private int first(Envelope current) {
            return second(current.payload);
        }

        private int second(Payload payload) {
            boolean enabled = payload.control.enabled;
            int value = payload.measure.base + payload.measure.adjustment;
            if (value < 0) {
                value = 0;
            }
            if (enabled && value > 4) {
                return 3;
            }
            return enabled ? 1 : -1;
        }
    }

    public static final class EvenProducer {
        Envelope envelope;

        EvenProducer(Boolean enabled) {
            envelope = new Envelope(enabled, -1, -1);
        }

        public int compute() {
            return hop(envelope.payload);
        }

        private int hop(Payload payload) {
            boolean enabled = payload.control.enabled;
            int value = payload.measure.base - payload.measure.adjustment;
            if (value < 0) {
                value = 0;
            }
            if (enabled && value > 4) {
                return 4;
            }
            return enabled ? 2 : 0;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch oddReady = new CountDownLatch(1);
        private final CountDownLatch evenReady = new CountDownLatch(1);
        private volatile int odd;
        private volatile int even;
        private volatile int oddPublishCount;
        private volatile int evenPublishCount;
        private volatile int oddReadCount;
        private volatile int evenReadCount;
        private volatile int publicationClock;
        private volatile int oddPublishOrdinal;
        private volatile int evenPublishOrdinal;
        private volatile int readClock;
        private volatile int oddReadOrdinal;
        private volatile int evenReadOrdinal;

        public void publishOdd(int value) {
            odd = value;
            oddPublishCount++;
            oddPublishOrdinal = ++publicationClock;
            oddReady.countDown();
        }

        public void publishEven(int value) {
            even = value;
            evenPublishCount++;
            evenPublishOrdinal = ++publicationClock;
            evenReady.countDown();
        }

        public int getOdd() throws InterruptedException {
            oddReady.await();
            oddReadCount++;
            oddReadOrdinal = ++readClock;
            return odd;
        }

        public int getEven() throws InterruptedException {
            evenReady.await();
            evenReadCount++;
            evenReadOrdinal = ++readClock;
            return even;
        }

        void requireSingleTransfer() {
            if (oddPublishCount != 1 || evenPublishCount != 1
                    || oddReadCount != 1 || evenReadCount != 1
                    || oddPublishOrdinal != 1 || evenPublishOrdinal != 2
                    || oddReadOrdinal != 1 || evenReadOrdinal != 2) {
                throw new IllegalStateException(
                        "nested-object RPC transfer order/count changed");
            }
        }

    }

    public static final class ImpossibleNestedObjectException
            extends RuntimeException {
        ImpossibleNestedObjectException(int odd, int even) {
            super("nested object paths produced equal parity values: "
                    + odd + " == " + even);
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

    private static final class OddProducerThread extends Worker {
        private final OddProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch oddPublished;

        OddProducerThread(OddProducer producer, RpcBus bus,
                          CountDownLatch start, CountDownLatch peers,
                          CountDownLatch oddPublished) {
            super("nested-object-odd-producer", start);
            this.producer = producer;
            this.bus = bus;
            this.peers = peers;
            this.oddPublished = oddPublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            bus.publishOdd(producer.compute());
            oddPublished.countDown();
        }
    }

    private static final class EvenProducerThread extends Worker {
        private final EvenProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch oddPublished;

        EvenProducerThread(EvenProducer producer, RpcBus bus,
                           CountDownLatch start, CountDownLatch peers,
                           CountDownLatch oddPublished) {
            super("nested-object-even-producer", start);
            this.producer = producer;
            this.bus = bus;
            this.peers = peers;
            this.oddPublished = oddPublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            oddPublished.await();
            bus.publishEven(producer.compute());
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int odd;
        private volatile int even;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super("nested-object-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int receivedOdd = bus.getOdd();
            int receivedEven = bus.getEven();
            odd = receivedOdd;
            even = receivedEven;
            if (receivedOdd == receivedEven) {
                throw new @CausynthExceptionTarget(
                        "unreachable-nested-object")
                        ImpossibleNestedObjectException(receivedOdd,
                        receivedEven);
            }
        }
    }

    public static final class RunResult {
        private final int odd;
        private final int even;
        private final Throwable failure;
        private final String failureThread;

        RunResult(int odd, int even, Throwable failure, String failureThread) {
            this.odd = odd;
            this.even = even;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String toJson() {
            return "{\"kind\":\"NESTED_OBJECT_UNREACHABLE_RESULT\","
                    + "\"odd\":" + odd + ",\"even\":" + even
                    + ",\"bugReached\":"
                    + (failure instanceof ImpossibleNestedObjectException)
                    + ",\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean oddEnabled,
                                    Boolean evenEnabled)
            throws InterruptedException {
        if (oddEnabled == null || evenEnabled == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        CountDownLatch oddPublished = new CountDownLatch(1);
        OddProducerThread odd = new OddProducerThread(
                new OddProducer(oddEnabled), bus, start, peers, oddPublished);
        EvenProducerThread even = new EvenProducerThread(
                new EvenProducer(evenEnabled), bus, start, peers,
                oddPublished);
        ConsumerThread consumer = new ConsumerThread(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        odd.setUncaughtExceptionHandler(handler);
        even.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        odd.start();
        even.start();
        start.countDown();
        join(odd);
        join(even);
        consumer.start();
        join(consumer);
        bus.requireSingleTransfer();
        return new RunResult(consumer.odd, consumer.even, failure.get(),
                failureThread.get());
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
                    "expected: <oddEnabled> <evenEnabled>");
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
