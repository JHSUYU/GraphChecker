package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Unreachable range target over an inherited object field and a same-object
 * alias returned through two helper methods.
 */
public final class InheritedObjectAliasUnreachableThreeThreadWorkload {
    private static final long TIMEOUT_MILLIS = 10_000L;

    private InheritedObjectAliasUnreachableThreeThreadWorkload() {
    }

    static class BaseRecord {
        int base;

        BaseRecord(int base) {
            this.base = base;
        }
    }

    static final class DerivedRecord extends BaseRecord {
        int delta;

        DerivedRecord(int base, int delta) {
            super(base);
            this.delta = delta;
        }
    }

    static final class RecordHolder {
        DerivedRecord record;

        RecordHolder(int base, int delta) {
            record = new DerivedRecord(base, delta);
        }
    }

    public static final class AliasProducer {
        RecordHolder holder;

        AliasProducer(int base, int delta) {
            holder = new RecordHolder(base, delta);
        }

        public int compute(Boolean upper) {
            DerivedRecord alias = resolve(holder);
            int value = alias.base + alias.delta;
            if (value < 0) {
                value = 0;
            }
            if (value > 4) {
                value = 4;
            }
            return upper.booleanValue() ? value + 1 : value;
        }

        private DerivedRecord resolve(RecordHolder source) {
            return identity(source.record);
        }

        private DerivedRecord identity(DerivedRecord value) {
            return value;
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
                        "object-alias RPC transfer order/count changed");
            }
        }

    }

    public static final class ImpossibleAliasRangeException
            extends RuntimeException {
        ImpossibleAliasRangeException(int value, int floor) {
            super("bounded object alias reached impossible floor: " + value
                    + " >= " + floor);
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

    private static final class AliasProducerThread extends Worker {
        private final Boolean upper;
        private final AliasProducer producer;
        private final RpcBus bus;
        private final CountDownLatch peers;
        private final CountDownLatch valuePublished;

        AliasProducerThread(Boolean upper, AliasProducer producer,
                            RpcBus bus, CountDownLatch start,
                            CountDownLatch peers,
                            CountDownLatch valuePublished) {
            super("inherited-alias-producer", start);
            this.upper = upper;
            this.producer = producer;
            this.bus = bus;
            this.peers = peers;
            this.valuePublished = valuePublished;
        }

        @Override
        void executeWorker() throws InterruptedException {
            awaitPeers(peers);
            bus.publishValue(producer.compute(upper));
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
            super("inherited-floor-producer", start);
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
            super("inherited-alias-consumer", start);
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
                        "unreachable-inherited-alias")
                        ImpossibleAliasRangeException(receivedValue,
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
            return "{\"kind\":\"INHERITED_OBJECT_ALIAS_UNREACHABLE_RESULT\","
                    + "\"value\":" + value + ",\"floor\":" + floor
                    + ",\"bugReached\":"
                    + (failure instanceof ImpossibleAliasRangeException)
                    + ",\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean upper, Boolean high)
            throws InterruptedException {
        if (upper == null || high == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        CountDownLatch peers = new CountDownLatch(2);
        CountDownLatch valuePublished = new CountDownLatch(1);
        AliasProducerThread value = new AliasProducerThread(upper,
                new AliasProducer(-2, 1), bus, start, peers, valuePublished);
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
                    "expected: <upperValue> <highFloor>");
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
