package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

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
 * Five small three-thread workloads for the generic concolic workflow.
 *
 * <p>Every variant keeps the same execution shape as the baseline fixture:
 * two concurrently-live producers publish through {@link RpcBus}, both
 * producers terminate, and one consumer then reads the two values and checks
 * a target branch.  The variant only changes producer relations and the final
 * branch.  Keeping all support classes nested lets the fixture runner isolate
 * the complete workload by one outer-class prefix. Producer-to-consumer
 * channels are discovered from runtime-confirmed shared-field read-from
 * evidence rather than a fixture-declared RPC mapping.</p>
 */
public final class ThreeThreadRpcScenarioWorkload {
    public static final String PRODUCER_A_THREAD = "scenario-producer-a";
    public static final String PRODUCER_B_THREAD = "scenario-producer-b";
    public static final String CONSUMER_THREAD = "scenario-consumer";
    public static final String VARIANT_PROPERTY = "causynth.fixture.variant";
    private static final long JOIN_TIMEOUT_MILLIS = 10_000L;

    private ThreeThreadRpcScenarioWorkload() {
    }

    public enum Variant {
        ADDITIVE_OR("additive-or"),
        XOR_ELSE_EDGE("xor-else-edge"),
        GREATER_ONE_HOT("greater-one-hot"),
        LESS_ONE_HOT("less-one-hot"),
        DEPENDENT_MERGE("dependent-merge");

        private final String directoryName;

        Variant(String directoryName) {
            this.directoryName = directoryName;
        }

        public String getDirectoryName() {
            return directoryName;
        }

        public static Variant parse(String value) {
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException(
                        "missing system property " + VARIANT_PROPERTY);
            }
            for (Variant variant : values()) {
                if (variant.name().equalsIgnoreCase(value.trim())
                        || variant.directoryName.equalsIgnoreCase(
                        value.trim())) {
                    return variant;
                }
            }
            throw new IllegalArgumentException("unknown fixture variant: "
                    + value);
        }
    }

    public interface ScenarioBug {
    }

    public static final class AdditiveOrBugReachedException
            extends RuntimeException implements ScenarioBug {
        public AdditiveOrBugReachedException(int a, int b) {
            super("additive OR reached with a=" + a + ", b=" + b);
        }
    }

    public static final class XorElseEdgeBugReachedException
            extends RuntimeException implements ScenarioBug {
        public XorElseEdgeBugReachedException(int a, int b) {
            super("XOR else edge reached with a=" + a + ", b=" + b);
        }
    }

    public static final class GreaterOneHotBugReachedException
            extends RuntimeException implements ScenarioBug {
        public GreaterOneHotBugReachedException(int a, int b) {
            super("greater one-hot reached with a=" + a + ", b=" + b);
        }
    }

    public static final class LessOneHotBugReachedException
            extends RuntimeException implements ScenarioBug {
        public LessOneHotBugReachedException(int a, int b) {
            super("less one-hot reached with a=" + a + ", b=" + b);
        }
    }

    public static final class DependentMergeBugReachedException
            extends RuntimeException implements ScenarioBug {
        public DependentMergeBugReachedException(int a, int b) {
            super("dependent merge reached with a=" + a + ", b=" + b);
        }
    }

    public static final class AdditiveOrProducerA {
        public int compute(Boolean input) {
            int value = -1;
            if (input.booleanValue()) {
                value = 2;
            }
            return value;
        }
    }

    public static final class AdditiveOrProducerB {
        public int compute(Boolean input) {
            int value = -1;
            if (input.booleanValue()) {
                value = 3;
            }
            return value;
        }
    }

    public static final class XorElseEdgeProducerA {
        public int compute(Boolean input) {
            int value = 0;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }
    }

    public static final class XorElseEdgeProducerB {
        public int compute(Boolean input) {
            int value = 0;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }
    }

    public static final class GreaterOneHotProducerA {
        public int compute(Boolean input) {
            int value = -1;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }
    }

    public static final class GreaterOneHotProducerB {
        public int compute(Boolean input) {
            int value = -1;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }
    }

    public static final class LessOneHotProducerA {
        public int compute(Boolean input) {
            int value = -1;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }
    }

    public static final class LessOneHotProducerB {
        public int compute(Boolean input) {
            int value = -1;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }
    }

    public static final class DependentMergeProducerA {
        public int compute(Boolean input) {
            int value = -3;
            if (input.booleanValue()) {
                value = 7;
            }
            return value;
        }
    }

    public static final class DependentMergeProducerB {
        public int compute(Boolean input) {
            int value = -3;
            if (input.booleanValue()) {
                value = 4;
            }
            return value;
        }
    }

    /** Runtime-observed shared-state/RPC boundary used by every variant. */
    public static final class RpcBus {
        private final CountDownLatch aReady = new CountDownLatch(1);
        private final CountDownLatch bReady = new CountDownLatch(1);
        private volatile int a;
        private volatile int b;
        private volatile long aPublisherThreadId;
        private volatile long bPublisherThreadId;
        private volatile int aReceivedValue;
        private volatile int bReceivedValue;
        private volatile long aConsumerThreadId;
        private volatile long bConsumerThreadId;
        private volatile int aReceiveCount;
        private volatile int bReceiveCount;

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
            int received = a;
            aReceivedValue = received;
            aConsumerThreadId = Thread.currentThread().getId();
            aReceiveCount++;
            return received;
        }

        public int getRPCFromB() throws InterruptedException {
            if (!bReady.await(JOIN_TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC B timed out");
            }
            int received = b;
            bReceivedValue = received;
            bConsumerThreadId = Thread.currentThread().getId();
            bReceiveCount++;
            return received;
        }
    }

    private static final class ProducerConcurrencyGate {
        private final CountDownLatch entered = new CountDownLatch(2);

        void enterAndAwaitPeer() throws InterruptedException {
            entered.countDown();
            if (!entered.await(JOIN_TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException(
                        "producer concurrency rendezvous timed out");
            }
        }

        boolean bothWorkersEnteredConcurrently() {
            return entered.getCount() == 0L;
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

    private abstract static class ProducerThread extends WorkerThread {
        protected final Boolean input;
        protected final RpcBus bus;
        protected final ProducerConcurrencyGate concurrencyGate;

        ProducerThread(String name, Boolean input, RpcBus bus,
                       CountDownLatch start,
                       ProducerConcurrencyGate concurrencyGate) {
            super(name, start);
            this.input = input;
            this.bus = bus;
            this.concurrencyGate = concurrencyGate;
        }
    }

    private abstract static class ConsumerThread extends WorkerThread {
        protected final RpcBus bus;
        private volatile int receivedA;
        private volatile int receivedB;
        private volatile boolean received;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super(CONSUMER_THREAD, start);
            this.bus = bus;
        }

        final void recordReceived(int a, int b) {
            receivedA = a;
            receivedB = b;
            received = true;
        }
    }

    private static final class AdditiveOrProducerAThread
            extends ProducerThread {
        AdditiveOrProducerAThread(Boolean input, RpcBus bus,
                                  CountDownLatch start,
                                  ProducerConcurrencyGate gate) {
            super(PRODUCER_A_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishA(new AdditiveOrProducerA().compute(input));
        }
    }

    private static final class AdditiveOrProducerBThread
            extends ProducerThread {
        AdditiveOrProducerBThread(Boolean input, RpcBus bus,
                                  CountDownLatch start,
                                  ProducerConcurrencyGate gate) {
            super(PRODUCER_B_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishB(new AdditiveOrProducerB().compute(input));
        }
    }

    private static final class AdditiveOrConsumerThread
            extends ConsumerThread {
        AdditiveOrConsumerThread(RpcBus bus, CountDownLatch start) {
            super(bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            recordReceived(a, b);
            if (a + b > -2) {
                throw new @CausynthExceptionTarget("additive-or")
                        AdditiveOrBugReachedException(a, b);
            }
        }
    }

    private static final class XorElseEdgeProducerAThread
            extends ProducerThread {
        XorElseEdgeProducerAThread(Boolean input, RpcBus bus,
                                   CountDownLatch start,
                                   ProducerConcurrencyGate gate) {
            super(PRODUCER_A_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishA(new XorElseEdgeProducerA().compute(input));
        }
    }

    private static final class XorElseEdgeProducerBThread
            extends ProducerThread {
        XorElseEdgeProducerBThread(Boolean input, RpcBus bus,
                                   CountDownLatch start,
                                   ProducerConcurrencyGate gate) {
            super(PRODUCER_B_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishB(new XorElseEdgeProducerB().compute(input));
        }
    }

    private static final class XorElseEdgeConsumerThread
            extends ConsumerThread {
        XorElseEdgeConsumerThread(RpcBus bus, CountDownLatch start) {
            super(bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            recordReceived(a, b);
            if (a + b != 1) {
                return;
            }
            throw new @CausynthExceptionTarget("xor-else-edge")
                    XorElseEdgeBugReachedException(a, b);
        }
    }

    private static final class GreaterOneHotProducerAThread
            extends ProducerThread {
        GreaterOneHotProducerAThread(Boolean input, RpcBus bus,
                                     CountDownLatch start,
                                     ProducerConcurrencyGate gate) {
            super(PRODUCER_A_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishA(new GreaterOneHotProducerA().compute(input));
        }
    }

    private static final class GreaterOneHotProducerBThread
            extends ProducerThread {
        GreaterOneHotProducerBThread(Boolean input, RpcBus bus,
                                     CountDownLatch start,
                                     ProducerConcurrencyGate gate) {
            super(PRODUCER_B_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishB(new GreaterOneHotProducerB().compute(input));
        }
    }

    private static final class GreaterOneHotConsumerThread
            extends ConsumerThread {
        GreaterOneHotConsumerThread(RpcBus bus, CountDownLatch start) {
            super(bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            recordReceived(a, b);
            if (a > b) {
                throw new @CausynthExceptionTarget("greater-one-hot")
                        GreaterOneHotBugReachedException(a, b);
            }
        }
    }

    private static final class LessOneHotProducerAThread
            extends ProducerThread {
        LessOneHotProducerAThread(Boolean input, RpcBus bus,
                                  CountDownLatch start,
                                  ProducerConcurrencyGate gate) {
            super(PRODUCER_A_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishA(new LessOneHotProducerA().compute(input));
        }
    }

    private static final class LessOneHotProducerBThread
            extends ProducerThread {
        LessOneHotProducerBThread(Boolean input, RpcBus bus,
                                  CountDownLatch start,
                                  ProducerConcurrencyGate gate) {
            super(PRODUCER_B_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishB(new LessOneHotProducerB().compute(input));
        }
    }

    private static final class LessOneHotConsumerThread
            extends ConsumerThread {
        LessOneHotConsumerThread(RpcBus bus, CountDownLatch start) {
            super(bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            recordReceived(a, b);
            if (a < b) {
                throw new @CausynthExceptionTarget("less-one-hot")
                        LessOneHotBugReachedException(a, b);
            }
        }
    }

    private static final class DependentMergeProducerAThread
            extends ProducerThread {
        DependentMergeProducerAThread(Boolean input, RpcBus bus,
                                      CountDownLatch start,
                                      ProducerConcurrencyGate gate) {
            super(PRODUCER_A_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishA(new DependentMergeProducerA().compute(input));
        }
    }

    private static final class DependentMergeProducerBThread
            extends ProducerThread {
        DependentMergeProducerBThread(Boolean input, RpcBus bus,
                                      CountDownLatch start,
                                      ProducerConcurrencyGate gate) {
            super(PRODUCER_B_THREAD, input, bus, start, gate);
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            bus.publishB(new DependentMergeProducerB().compute(input));
        }
    }

    private static final class DependentMergeConsumerThread
            extends ConsumerThread {
        DependentMergeConsumerThread(RpcBus bus, CountDownLatch start) {
            super(bus, start);
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            recordReceived(a, b);
            if (a + b > 7) {
                throw new @CausynthExceptionTarget("dependent-merge")
                        DependentMergeBugReachedException(a, b);
            }
        }
    }

    private static final class WorkerBundle {
        private final ProducerThread producerA;
        private final ProducerThread producerB;
        private final ConsumerThread consumer;

        WorkerBundle(ProducerThread producerA, ProducerThread producerB,
                     ConsumerThread consumer) {
            this.producerA = producerA;
            this.producerB = producerB;
            this.consumer = consumer;
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
        private final Variant variant;
        private final Boolean b1;
        private final Boolean b2;
        private final int a;
        private final int b;
        private final boolean bugReached;
        private final long[] workerThreadIds;
        private final String failureThread;
        private final Throwable failure;
        private final List<RpcObservation> rpcObservations;
        private final boolean producerConcurrencyObserved;
        private final boolean consumerStartedAfterProducerThreadsTerminated;

        RunResult(Variant variant, Boolean b1, Boolean b2, int a, int b,
                  long[] workerThreadIds, String failureThread,
                  Throwable failure, List<RpcObservation> observations,
                  boolean producerConcurrencyObserved,
                  boolean consumerStartedAfterProducerThreadsTerminated) {
            this.variant = variant;
            this.b1 = b1;
            this.b2 = b2;
            this.a = a;
            this.b = b;
            this.bugReached = failure instanceof ScenarioBug;
            this.workerThreadIds = workerThreadIds.clone();
            this.failureThread = failureThread;
            this.failure = failure;
            this.rpcObservations = Collections.unmodifiableList(
                    new ArrayList<>(observations));
            this.producerConcurrencyObserved = producerConcurrencyObserved;
            this.consumerStartedAfterProducerThreadsTerminated =
                    consumerStartedAfterProducerThreadsTerminated;
        }

        public Variant getVariant() {
            return variant;
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

        public boolean isProducerConcurrencyObserved() {
            return producerConcurrencyObserved;
        }

        public boolean isConsumerStartedAfterProducerThreadsTerminated() {
            return consumerStartedAfterProducerThreadsTerminated;
        }

        public String toJson() {
            StringBuilder observations = new StringBuilder();
            for (RpcObservation observation : rpcObservations) {
                if (observations.length() > 0) {
                    observations.append(',');
                }
                observations.append(observation.toJson());
            }
            return "{\"kind\":\"THREE_THREAD_RPC_SCENARIO_RESULT\","
                    + "\"variant\":\"" + variant.name() + "\","
                    + "\"b1\":" + b1 + ",\"b2\":" + b2 + ","
                    + "\"a\":" + a + ",\"b\":" + b + ","
                    + "\"bugReached\":" + bugReached + ","
                    + "\"producerConcurrencyObserved\":"
                    + producerConcurrencyObserved + ","
                    + "\"consumerStartedAfterProducerThreadsTerminated\":"
                    + consumerStartedAfterProducerThreadsTerminated + ","
                    + "\"workerThreadIds\":[" + workerThreadIds[0]
                    + ',' + workerThreadIds[1] + ',' + workerThreadIds[2]
                    + "],\"failureThread\":"
                    + (failureThread == null ? "null" : "\""
                    + failureThread + "\"") + ",\"rpcObservations\":["
                    + observations + "]}";
        }
    }

    public static RunResult execute(Variant variant, Boolean b1, Boolean b2)
            throws InterruptedException {
        if (variant == null) {
            throw new IllegalArgumentException("variant must be non-null");
        }
        if (b1 == null || b2 == null) {
            throw new IllegalArgumentException("b1 and b2 must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        ProducerConcurrencyGate concurrencyGate =
                new ProducerConcurrencyGate();
        WorkerBundle workers = createWorkers(variant, b1, b2, bus, start,
                concurrencyGate);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        workers.producerA.setUncaughtExceptionHandler(handler);
        workers.producerB.setUncaughtExceptionHandler(handler);
        workers.consumer.setUncaughtExceptionHandler(handler);

        workers.producerA.start();
        workers.producerB.start();
        start.countDown();
        join(workers.producerA);
        join(workers.producerB);
        boolean producersTerminated = workers.producerA.getState()
                == Thread.State.TERMINATED
                && workers.producerB.getState() == Thread.State.TERMINATED
                && workers.consumer.getState() == Thread.State.NEW;
        workers.consumer.start();
        join(workers.consumer);
        if (!workers.consumer.received && failure.get() == null) {
            throw new IllegalStateException("consumer produced no observation");
        }

        int a = workers.consumer.received
                ? workers.consumer.receivedA : bus.aReceivedValue;
        int b = workers.consumer.received
                ? workers.consumer.receivedB : bus.bReceivedValue;
        List<RpcObservation> observations = new ArrayList<>();
        if (bus.aReceiveCount == 1) {
            observations.add(new RpcObservation("A", bus.a,
                    bus.aReceivedValue, bus.aPublisherThreadId,
                    bus.aConsumerThreadId));
        }
        if (bus.bReceiveCount == 1) {
            observations.add(new RpcObservation("B", bus.b,
                    bus.bReceivedValue, bus.bPublisherThreadId,
                    bus.bConsumerThreadId));
        }
        return new RunResult(variant, b1, b2, a, b,
                new long[]{workers.producerA.getId(),
                        workers.producerB.getId(), workers.consumer.getId()},
                failureThread.get(), failure.get(), observations,
                concurrencyGate.bothWorkersEnteredConcurrently(),
                producersTerminated);
    }

    private static WorkerBundle createWorkers(Variant variant, Boolean b1,
                                               Boolean b2, RpcBus bus,
                                               CountDownLatch start,
                                               ProducerConcurrencyGate gate) {
        switch (variant) {
            case ADDITIVE_OR:
                return new WorkerBundle(
                        new AdditiveOrProducerAThread(b1, bus, start, gate),
                        new AdditiveOrProducerBThread(b2, bus, start, gate),
                        new AdditiveOrConsumerThread(bus, start));
            case XOR_ELSE_EDGE:
                return new WorkerBundle(
                        new XorElseEdgeProducerAThread(b1, bus, start, gate),
                        new XorElseEdgeProducerBThread(b2, bus, start, gate),
                        new XorElseEdgeConsumerThread(bus, start));
            case GREATER_ONE_HOT:
                return new WorkerBundle(
                        new GreaterOneHotProducerAThread(b1, bus, start, gate),
                        new GreaterOneHotProducerBThread(b2, bus, start, gate),
                        new GreaterOneHotConsumerThread(bus, start));
            case LESS_ONE_HOT:
                return new WorkerBundle(
                        new LessOneHotProducerAThread(b1, bus, start, gate),
                        new LessOneHotProducerBThread(b2, bus, start, gate),
                        new LessOneHotConsumerThread(bus, start));
            case DEPENDENT_MERGE:
                return new WorkerBundle(
                        new DependentMergeProducerAThread(b1, bus, start, gate),
                        new DependentMergeProducerBThread(b2, bus, start, gate),
                        new DependentMergeConsumerThread(bus, start));
            default:
                throw new IllegalArgumentException("unsupported variant: "
                        + variant);
        }
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
        Variant variant = Variant.parse(System.getProperty(VARIANT_PROPERTY));
        RunResult result = execute(variant, parseBoolean(args[0]),
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
