package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Unreachable range target whose scalar output ignores later object mutation.
 */
public final class MutatedObjectStateUnreachableThreeThreadWorkload {
    private static final long TIMEOUT_MILLIS = 10_000L;

    private MutatedObjectStateUnreachableThreeThreadWorkload() {
    }

    static final class MutableNumbers {
        int base;
        int bias;

        MutableNumbers(int base, int bias) {
            this.base = base;
            this.bias = bias;
        }
    }

    static final class StateHolder {
        MutableNumbers numbers;

        StateHolder(int base, int bias) {
            numbers = new MutableNumbers(base, bias);
        }
    }

    public static final class MutatingProducer {
        StateHolder holder;

        MutatingProducer(int base, int staleBias) {
            holder = new StateHolder(base, staleBias);
        }

        public int compute(Boolean addBias) {
            MutableNumbers alias = resolve(holder);
            int snapshot = alias.base;
            if (snapshot < 0) {
                snapshot = 0;
            }
            if (snapshot > 4) {
                snapshot = 4;
            }
            int result = addBias.booleanValue()
                    ? snapshot + 1
                    : snapshot;
            overwriteIrrelevantState(alias);
            return result;
        }

        private MutableNumbers resolve(StateHolder source) {
            return identity(source.numbers);
        }

        private MutableNumbers identity(MutableNumbers value) {
            return value;
        }

        private void overwriteIrrelevantState(MutableNumbers value) {
            value.base = 100;
            value.bias = 99;
        }
    }

    public static final class FloorProducer {
        public int compute(Boolean high) {
            return high.booleanValue() ? 7 : 6;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch valueReady = new CountDownLatch(1);
        private final CountDownLatch floorReady = new CountDownLatch(1);
        private volatile int value;
        private volatile int floor;
        private volatile int valuePublishCount;
        private volatile int floorPublishCount;
        private volatile int valueReadCount;
        private volatile int floorReadCount;
        private volatile int publicationClock;
        private volatile int valuePublishOrdinal;
        private volatile int floorPublishOrdinal;
        private volatile int readClock;
        private volatile int valueReadOrdinal;
        private volatile int floorReadOrdinal;

        public void publishValue(int published) {
            value = published;
            valuePublishCount++;
            valuePublishOrdinal = ++publicationClock;
            valueReady.countDown();
        }

        public void publishFloor(int published) {
            floor = published;
            floorPublishCount++;
            floorPublishOrdinal = ++publicationClock;
            floorReady.countDown();
        }

        public int getValue() throws InterruptedException {
            valueReady.await();
            valueReadCount++;
            valueReadOrdinal = ++readClock;
            return value;
        }

        public int getFloor() throws InterruptedException {
            floorReady.await();
            floorReadCount++;
            floorReadOrdinal = ++readClock;
            return floor;
        }

        void requireSingleTransfer() {
            if (valuePublishCount != 1 || floorPublishCount != 1
                    || valueReadCount != 1 || floorReadCount != 1
                    || valuePublishOrdinal != 1 || floorPublishOrdinal != 2
                    || valueReadOrdinal != 1 || floorReadOrdinal != 2) {
                throw new IllegalStateException(
                        "mutated-object RPC transfer order/count changed");
            }
        }
    }

    public static final class ImpossibleMutatedStateException
            extends RuntimeException {
        ImpossibleMutatedStateException(int value, int floor) {
            super("object snapshot reached impossible floor: "
                    + value + " >= " + floor);
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

    private static final class ValueProducerThread extends Worker {
        private final Boolean addBias;
        private final MutatingProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch valuePublished;

        ValueProducerThread(Boolean addBias, MutatingProducer producer,
                            RpcBus bus, CountDownLatch start,
                            CountDownLatch peers,
                            CountDownLatch valuePublished) {
            super("mutated-object-producer", start);
            this.addBias = addBias;
            this.producer = producer;
            this.bus = bus;
            this.peers = peers;
            this.valuePublished = valuePublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            bus.publishValue(producer.compute(addBias));
            valuePublished.countDown();
        }
    }

    private static final class FloorProducerThread extends Worker {
        private final Boolean high;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch valuePublished;

        FloorProducerThread(Boolean high, RpcBus bus, CountDownLatch start,
                            CountDownLatch peers,
                            CountDownLatch valuePublished) {
            super("mutated-object-floor-producer", start);
            this.high = high;
            this.bus = bus;
            this.peers = peers;
            this.valuePublished = valuePublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            valuePublished.await();
            bus.publishFloor(new FloorProducer().compute(high));
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int value;
        private volatile int floor;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super("mutated-object-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int receivedValue = bus.getValue();
            int receivedFloor = bus.getFloor();
            value = receivedValue;
            floor = receivedFloor;
            if (receivedValue >= receivedFloor) {
                throw new @CausynthExceptionTarget(
                        "unreachable-mutated-object")
                        ImpossibleMutatedStateException(receivedValue,
                        receivedFloor);
            }
        }
    }

    public static final class RunResult {
        private final int value;
        private final int floor;
        private final Throwable failure;
        private final String failureThread;

        RunResult(int value, int floor, Throwable failure,
                  String failureThread) {
            this.value = value;
            this.floor = floor;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String toJson() {
            return "{\"kind\":\"MUTATED_OBJECT_UNREACHABLE_RESULT\","
                    + "\"value\":" + value + ",\"floor\":" + floor
                    + ",\"bugReached\":"
                    + (failure instanceof ImpossibleMutatedStateException)
                    + ",\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean addBias, Boolean high)
            throws InterruptedException {
        if (addBias == null || high == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        CountDownLatch valuePublished = new CountDownLatch(1);
        ValueProducerThread value = new ValueProducerThread(addBias,
                new MutatingProducer(-2, 99), bus, start, peers,
                valuePublished);
        FloorProducerThread floor = new FloorProducerThread(high, bus, start,
                peers, valuePublished);
        ConsumerThread consumer = new ConsumerThread(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        value.setUncaughtExceptionHandler(handler);
        floor.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        value.start();
        floor.start();
        start.countDown();
        join(value);
        join(floor);
        consumer.start();
        join(consumer);
        bus.requireSingleTransfer();
        return new RunResult(consumer.value, consumer.floor, failure.get(),
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
                    "expected: <addBias> <highFloor>");
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
