package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Unreachable parity target over nested long fields passed through helpers.
 */
public final class NestedLongFieldsUnreachableThreeThreadWorkload {
    private static final long TIMEOUT_MILLIS = 10_000L;

    private NestedLongFieldsUnreachableThreeThreadWorkload() {
    }

    static final class LongLeaf {
        long base;
        long adjustment;

        LongLeaf(long base, long adjustment) {
            this.base = base;
            this.adjustment = adjustment;
        }
    }

    static final class SwitchLeaf {
        boolean enabled;

        SwitchLeaf(Boolean enabled) {
            this.enabled = enabled.booleanValue();
        }
    }

    static final class LongPayload {
        LongLeaf numbers;
        SwitchLeaf control;

        LongPayload(Boolean enabled, long base, long adjustment) {
            numbers = new LongLeaf(base, adjustment);
            control = new SwitchLeaf(enabled);
        }
    }

    static final class LongEnvelope {
        LongPayload payload;

        LongEnvelope(Boolean enabled, long base, long adjustment) {
            payload = new LongPayload(enabled, base, adjustment);
        }
    }

    public static final class OddLongProducer {
        LongEnvelope envelope;

        OddLongProducer(Boolean enabled) {
            envelope = new LongEnvelope(enabled, -1L, -1L);
        }

        public long compute() {
            return first(envelope);
        }

        private long first(LongEnvelope current) {
            return odd(current.payload);
        }

        private long odd(LongPayload payload) {
            long value = payload.numbers.base
                    + payload.numbers.adjustment;
            if (value < 0L) {
                value = 0L;
            }
            if (payload.control.enabled && value > 4L) {
                return 3L;
            }
            return payload.control.enabled ? 1L : -1L;
        }
    }

    public static final class EvenLongProducer {
        LongEnvelope envelope;

        EvenLongProducer(Boolean enabled) {
            envelope = new LongEnvelope(enabled, -1L, -1L);
        }

        public long compute() {
            return even(identity(envelope.payload));
        }

        private LongPayload identity(LongPayload payload) {
            return payload;
        }

        private long even(LongPayload payload) {
            long value = payload.numbers.base
                    - payload.numbers.adjustment;
            if (value < 0L) {
                value = 0L;
            }
            if (payload.control.enabled && value > 4L) {
                return 4L;
            }
            return payload.control.enabled ? 2L : 0L;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch oddReady = new CountDownLatch(1);
        private final CountDownLatch evenReady = new CountDownLatch(1);
        private volatile long odd;
        private volatile long even;
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

        public void publishOdd(long value) {
            odd = value;
            oddPublishCount++;
            oddPublishOrdinal = ++publicationClock;
            oddReady.countDown();
        }

        public void publishEven(long value) {
            even = value;
            evenPublishCount++;
            evenPublishOrdinal = ++publicationClock;
            evenReady.countDown();
        }

        public long getOdd() throws InterruptedException {
            oddReady.await();
            oddReadCount++;
            oddReadOrdinal = ++readClock;
            return odd;
        }

        public long getEven() throws InterruptedException {
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
                        "nested-long RPC transfer order/count changed");
            }
        }
    }

    public static final class ImpossibleLongParityException
            extends RuntimeException {
        ImpossibleLongParityException(long odd, long even) {
            super("odd and even long outputs were equal: "
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
        private final OddLongProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch oddPublished;

        OddProducerThread(OddLongProducer producer, RpcBus bus,
                          CountDownLatch start, CountDownLatch peers,
                          CountDownLatch oddPublished) {
            super("nested-long-odd-producer", start);
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
        private final EvenLongProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch oddPublished;

        EvenProducerThread(EvenLongProducer producer, RpcBus bus,
                           CountDownLatch start, CountDownLatch peers,
                           CountDownLatch oddPublished) {
            super("nested-long-even-producer", start);
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
        private volatile long odd;
        private volatile long even;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super("nested-long-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            long receivedOdd = bus.getOdd();
            long receivedEven = bus.getEven();
            odd = receivedOdd;
            even = receivedEven;
            if (receivedOdd == receivedEven) {
                throw new @CausynthExceptionTarget(
                        "unreachable-long-fields")
                        ImpossibleLongParityException(receivedOdd,
                        receivedEven);
            }
        }
    }

    public static final class RunResult {
        private final long odd;
        private final long even;
        private final Throwable failure;
        private final String failureThread;

        RunResult(long odd, long even, Throwable failure,
                  String failureThread) {
            this.odd = odd;
            this.even = even;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String toJson() {
            return "{\"kind\":\"NESTED_LONG_UNREACHABLE_RESULT\","
                    + "\"odd\":" + odd + ",\"even\":" + even
                    + ",\"bugReached\":"
                    + (failure instanceof ImpossibleLongParityException)
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
                new OddLongProducer(oddEnabled), bus, start, peers,
                oddPublished);
        EvenProducerThread even = new EvenProducerThread(
                new EvenLongProducer(evenEnabled), bus, start, peers,
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
