package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Deterministic shared-field RPC workload with a compound consumer target.
 */
public final class CompoundTargetThreeThreadRpcWorkload {
    private static final long TIMEOUT_MILLIS = 120_000L;
    private static final String VARIANT_PROPERTY = "causynth.fixture.variant";

    private CompoundTargetThreeThreadRpcWorkload() {
    }

    enum Variant {
        REACHABLE,
        UNREACHABLE;

        static Variant configured() {
            String value = System.getProperty(VARIANT_PROPERTY);
            if (value == null) {
                throw new IllegalArgumentException(
                        "missing property " + VARIANT_PROPERTY);
            }
            return Variant.valueOf(value.trim().toUpperCase());
        }
    }

    static final class AValueLeaf {
        boolean enabled;

        AValueLeaf(Boolean enabled) {
            this.enabled = enabled.booleanValue();
        }
    }

    static final class AEnvelope {
        AValueLeaf value;

        AEnvelope(Boolean enabled) {
            value = new AValueLeaf(enabled);
        }
    }

    static final class ReceivedValues {
        int a;
        int c;
        int x;
        int b;
        int d;
        int y;

        ReceivedValues(int a, int c, int x, int b, int d, int y) {
            this.a = a;
            this.c = c;
            this.x = x;
            this.b = b;
            this.d = d;
            this.y = y;
        }
    }

    static final class ProducerA {
        AEnvelope input;

        ProducerA(Boolean enabled) {
            input = new AEnvelope(enabled);
        }

        int compute() {
            return select(resolve(input));
        }

        private AValueLeaf resolve(AEnvelope envelope) {
            return envelope.value;
        }

        private int select(AValueLeaf value) {
            int selected;
            if (value.enabled && input.value.enabled) {
                selected = 3;
            } else if (value.enabled || input.value.enabled) {
                selected = 2;
            } else {
                selected = 0;
            }
            if ((value.enabled && selected == 3)
                    || (!value.enabled && selected > 0)) {
                selected += 4;
            }
            return selected;
        }
    }

    static final class BValueLeaf {
        boolean enabled;

        BValueLeaf(Boolean enabled) {
            this.enabled = enabled.booleanValue();
        }
    }

    static final class BEnvelope {
        BValueLeaf value;

        BEnvelope(Boolean enabled) {
            value = new BValueLeaf(enabled);
        }
    }

    static final class ProducerB {
        BEnvelope input;

        ProducerB(Boolean enabled) {
            input = new BEnvelope(enabled);
        }

        int compute() {
            return select(resolve(input));
        }

        private BValueLeaf resolve(BEnvelope envelope) {
            return envelope.value;
        }

        private int select(BValueLeaf value) {
            int selected;
            if (value.enabled && input.value.enabled) {
                selected = 3;
            } else if (value.enabled || input.value.enabled) {
                selected = 2;
            } else {
                selected = 1;
            }
            if ((value.enabled || selected > 2)
                    && input.value.enabled) {
                selected *= 2;
            } else if (!value.enabled && selected > 1) {
                selected = 1;
            }
            return selected;
        }
    }

    static final class RpcBus {
        private final CountDownLatch aReady = new CountDownLatch(1);
        private final CountDownLatch bReady = new CountDownLatch(1);
        private volatile int a;
        private volatile int c;
        private volatile int x;
        private volatile int b;
        private volatile int d;
        private volatile int y;
        private volatile int publishClock;
        private volatile int aPublishOrdinal;
        private volatile int bPublishOrdinal;
        private volatile int aPublishCount;
        private volatile int bPublishCount;
        private volatile int readClock;
        private volatile int aReadOrdinal;
        private volatile int cReadOrdinal;
        private volatile int xReadOrdinal;
        private volatile int bReadOrdinal;
        private volatile int dReadOrdinal;
        private volatile int yReadOrdinal;

        void publishA(int value) {
            a = value;
            c = value;
            x = value - value;
            aPublishCount++;
            aPublishOrdinal = ++publishClock;
            aReady.countDown();
        }

        void publishB(int value) {
            b = value;
            d = value;
            y = 4 - value;
            bPublishCount++;
            bPublishOrdinal = ++publishClock;
            bReady.countDown();
        }

        int getA() throws InterruptedException {
            aReady.await();
            aReadOrdinal = ++readClock;
            return a;
        }

        int getC() throws InterruptedException {
            aReady.await();
            cReadOrdinal = ++readClock;
            return c;
        }

        int getX() throws InterruptedException {
            aReady.await();
            xReadOrdinal = ++readClock;
            return x;
        }

        int getB() throws InterruptedException {
            bReady.await();
            bReadOrdinal = ++readClock;
            return b;
        }

        int getD() throws InterruptedException {
            bReady.await();
            dReadOrdinal = ++readClock;
            return d;
        }

        int getY() throws InterruptedException {
            bReady.await();
            yReadOrdinal = ++readClock;
            return y;
        }

        void requireSingleTransfer() {
            if (aPublishCount != 1 || bPublishCount != 1
                    || aPublishOrdinal != 1 || bPublishOrdinal != 2
                    || aReadOrdinal != 1 || cReadOrdinal != 2
                    || xReadOrdinal != 3 || bReadOrdinal != 4
                    || dReadOrdinal != 5 || yReadOrdinal != 6) {
                throw new IllegalStateException(
                        "compound-target RPC order/count changed");
            }
        }
    }

    public static final class ReachableCompoundTargetException
            extends RuntimeException {
        ReachableCompoundTargetException(int a, int b, int c, int d,
                                         int x, int y) {
            super("compound target reached: " + a + ',' + b + ','
                    + c + ',' + d + ',' + x + ',' + y);
        }
    }

    public static final class UnreachableCompoundTargetException
            extends RuntimeException {
        UnreachableCompoundTargetException(int a, int b, int c, int d,
                                           int x, int y) {
            super("unreachable compound target reached: " + a + ',' + b
                    + ',' + c + ',' + d + ',' + x + ',' + y);
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

    private static final class ProducerAThread extends Worker {
        private final ProducerA producer;
        private final RpcBus bus;

        ProducerAThread(ProducerA producer, RpcBus bus,
                        CountDownLatch start) {
            super("compound-producer-a", start);
            this.producer = producer;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            bus.publishA(producer.compute());
        }
    }

    private static final class ProducerBThread extends Worker {
        private final ProducerB producer;
        private final RpcBus bus;

        ProducerBThread(ProducerB producer, RpcBus bus,
                        CountDownLatch start) {
            super("compound-producer-b", start);
            this.producer = producer;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            bus.publishB(producer.compute());
        }
    }

    private abstract static class ConsumerThread extends Worker {
        final RpcBus bus;
        volatile int a;
        volatile int b;
        volatile int c;
        volatile int d;
        volatile int x;
        volatile int y;

        ConsumerThread(String name, RpcBus bus, CountDownLatch start) {
            super(name, start);
            this.bus = bus;
        }

    }

    private static final class ReachableConsumerThread
            extends ConsumerThread {
        ReachableConsumerThread(RpcBus bus, CountDownLatch start) {
            super("compound-consumer", bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int receivedA = bus.getA();
            int receivedC = bus.getC();
            int receivedX = bus.getX();
            int receivedB = bus.getB();
            int receivedD = bus.getD();
            int receivedY = bus.getY();
            ReceivedValues values = new ReceivedValues(receivedA,
                    receivedC, receivedX, receivedB, receivedD, receivedY);
            a = receivedA;
            b = receivedB;
            c = receivedC;
            d = receivedD;
            x = receivedX;
            y = receivedY;
            if ((values.a < 0 && receivedB < 0)
                    || (receivedX < -10 && values.y > 10)) {
                return;
            }
            if (((values.a > receivedB
                    && receivedC > values.d
                    && values.c >= receivedD)
                    || (values.x > receivedY
                    && (receivedA >= 0 || values.b >= 0)))
                    && ((receivedA == values.c
                    && receivedB == values.d)
                    || receivedX + values.y == 4)) {
                throw new @CausynthExceptionTarget(
                        "compound-target-reachable")
                        ReachableCompoundTargetException(receivedA,
                        receivedB, receivedC, receivedD, receivedX,
                        receivedY);
            }
        }
    }

    private static final class UnreachableConsumerThread
            extends ConsumerThread {
        UnreachableConsumerThread(RpcBus bus, CountDownLatch start) {
            super("compound-consumer", bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int receivedA = bus.getA();
            int receivedC = bus.getC();
            int receivedX = bus.getX();
            int receivedB = bus.getB();
            int receivedD = bus.getD();
            int receivedY = bus.getY();
            ReceivedValues values = new ReceivedValues(receivedA,
                    receivedC, receivedX, receivedB, receivedD, receivedY);
            a = receivedA;
            b = receivedB;
            c = receivedC;
            d = receivedD;
            x = receivedX;
            y = receivedY;
            if ((values.a < 0 && receivedB < 0)
                    || (receivedX < -10 && values.y > 10)) {
                return;
            }
            if (((values.a > receivedB
                    && receivedC > values.d
                    && values.c >= receivedD)
                    || (values.x > receivedY
                    && (receivedA >= 0 || values.b >= 0)))
                    && ((receivedA == values.c
                    && receivedB == values.d)
                    || receivedX + values.y == 4)) {
                if ((values.a <= receivedB
                        && receivedX <= values.y)
                        || (receivedC < values.d
                        && values.x > receivedY
                        && receivedA > values.b)) {
                    throw new @CausynthExceptionTarget(
                            "compound-target-unreachable")
                            UnreachableCompoundTargetException(receivedA,
                            receivedB, receivedC, receivedD, receivedX,
                            receivedY);
                }
            }
        }
    }

    public static final class RunResult {
        private final Variant variant;
        private final ConsumerThread consumer;
        private final Throwable failure;
        private final String failureThread;

        RunResult(Variant variant, ConsumerThread consumer,
                  Throwable failure, String failureThread) {
            this.variant = variant;
            this.consumer = consumer;
            this.failure = failure;
            this.failureThread = failureThread;
        }

        Throwable getFailure() {
            return failure;
        }

        String toJson() {
            return "{\"kind\":\"COMPOUND_TARGET_RESULT\","
                    + "\"variant\":\"" + variant + "\","
                    + "\"a\":" + consumer.a + ",\"b\":" + consumer.b
                    + ",\"c\":" + consumer.c + ",\"d\":" + consumer.d
                    + ",\"x\":" + consumer.x + ",\"y\":" + consumer.y
                    + ",\"bugReached\":"
                    + (failure instanceof ReachableCompoundTargetException
                    || failure
                    instanceof UnreachableCompoundTargetException)
                    + ",\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    static RunResult execute(Variant variant, Boolean aEnabled,
                             Boolean bEnabled) throws InterruptedException {
        if (variant == null || aEnabled == null || bEnabled == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        ProducerAThread producerA = new ProducerAThread(
                new ProducerA(aEnabled), bus, start);
        ProducerBThread producerB = new ProducerBThread(
                new ProducerB(bEnabled), bus, start);
        ConsumerThread consumer = variant == Variant.REACHABLE
                ? new ReachableConsumerThread(bus, start)
                : new UnreachableConsumerThread(bus, start);
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
        start.countDown();
        join(producerA);
        producerB.start();
        join(producerB);
        consumer.start();
        join(consumer);
        bus.requireSingleTransfer();
        return new RunResult(variant, consumer, failure.get(),
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

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <producerAEnabled> <producerBEnabled>");
        }
        RunResult result = execute(Variant.configured(),
                parseBoolean(args[0]), parseBoolean(args[1]));
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
