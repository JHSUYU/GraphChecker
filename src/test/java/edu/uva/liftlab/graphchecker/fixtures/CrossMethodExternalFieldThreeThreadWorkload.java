package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Deterministic three-thread workload with a cross-method producer slice.
 *
 * <p>Producer A crosses {@code compute -> firstHop -> secondHop -> thirdHop}.
 * Its result depends on a preconstructed external object's instance field, a
 * mutable static field, and primitive Boolean/integer parameters.  The three
 * integer roots jointly control one sign branch, keeping the cross-method
 * field projection observable without a redundant Cartesian product.
 * Consequently those fields remain useful symbolic inputs while the two
 * command-line Booleans retain the exact fatal condition
 * {@code producerAEnabled && !strictThreshold}.</p>
 *
 * <p>The producers rendezvous while both worker frames are live.  The
 * consumer remains {@link Thread.State#NEW} until both producers have
 * terminated, then reads Producer A's value and correlated witness plus
 * Producer B's threshold from the exact fields written by the publishers.</p>
 */
public final class CrossMethodExternalFieldThreeThreadWorkload {
    public static final String PRODUCER_A_THREAD =
            "cross-method-producer-a";
    public static final String PRODUCER_B_THREAD =
            "cross-method-producer-b";
    public static final String CONSUMER_THREAD = "cross-method-consumer";

    static final int DEFAULT_BASE_INPUT = 2;
    static final int RELAXED_THRESHOLD = 10;
    static final int STRICT_THRESHOLD = 20;
    private static final long JOIN_TIMEOUT_MILLIS = 60_000L;

    private CrossMethodExternalFieldThreeThreadWorkload() {
    }

    /** Object constructed by the harness before any worker starts. */
    public static final class ExternalProfile {
        int instanceWeight;

        public ExternalProfile(int instanceWeight) {
            this.instanceWeight = instanceWeight;
        }
    }

    /** Process-wide state read by Producer A rather than passed on the CLI. */
    public static final class ExternalTuning {
        static int processWeight = 2;

        private ExternalTuning() {
        }
    }

    /** Entry point for Producer A's cross-method computation. */
    public static final class ProducerA {
        private final ExternalProfile profile;
        private final SecondHop secondHop;

        public ProducerA(ExternalProfile profile) {
            if (profile == null) {
                throw new IllegalArgumentException("profile must be non-null");
            }
            this.profile = profile;
            this.secondHop = new SecondHop();
        }

        public int compute(boolean enabled, int baseInput) {
            return firstHop(enabled, baseInput);
        }

        private int firstHop(boolean enabled, int baseInput) {
            return secondHop.secondHop(profile, enabled, baseInput);
        }
    }

    /** Second helper layer; this is where both external fields are read. */
    public static final class SecondHop {
        private final ThirdHop thirdHop = new ThirdHop();

        int secondHop(ExternalProfile profile, boolean enabled,
                      int baseInput) {
            int instanceWeight = profile.instanceWeight;
            int processWeight = ExternalTuning.processWeight;
            int accumulated = baseInput + instanceWeight + processWeight;
            return thirdHop.thirdHop(enabled, accumulated);
        }
    }

    /** Third helper layer; both the Boolean and integer roots affect output. */
    public static final class ThirdHop {
        int thirdHop(boolean enabled, int accumulated) {
            int result = accumulated > 0 ? 1 : 0;
            if (enabled) {
                result += 12;
            }
            return result;
        }
    }

    /** Producer B supplies the control threshold for the terminal branch. */
    public static final class ThresholdProducer {
        public int compute(Boolean strictThreshold) {
            if (strictThreshold.booleanValue()) {
                return STRICT_THRESHOLD;
            }
            return RELAXED_THRESHOLD;
        }
    }

    /**
     * Producer A publishes the correlated pair {@code a}/{@code aWitness}
     * within one region invocation; Producer B publishes {@code b}.
     */
    public static final class RpcBus {
        private final CountDownLatch aReady = new CountDownLatch(1);
        private final CountDownLatch bReady = new CountDownLatch(1);
        private volatile int a;
        private volatile int aWitness;
        private volatile int b;
        private volatile long aPublisherThreadId;
        private volatile long bPublisherThreadId;
        private volatile long aConsumerThreadId;
        private volatile long bConsumerThreadId;
        private volatile int aReceiveCount;
        private volatile int aWitnessReceiveCount;
        private volatile int bReceiveCount;

        public void publishA(int value) {
            a = value;
            aWitness = 100 - value;
            aPublisherThreadId = Thread.currentThread().getId();
            aReady.countDown();
        }

        public void publishB(int value) {
            b = value;
            bPublisherThreadId = Thread.currentThread().getId();
            bReady.countDown();
        }

        public int getRPCFromA() throws InterruptedException {
            if (!aReady.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC A timed out");
            }
            aConsumerThreadId = Thread.currentThread().getId();
            aReceiveCount++;
            return a;
        }

        public int getRPCWitnessFromA() throws InterruptedException {
            if (!aReady.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC A witness timed out");
            }
            aWitnessReceiveCount++;
            return aWitness;
        }

        public int getRPCFromB() throws InterruptedException {
            if (!bReady.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC B timed out");
            }
            bConsumerThreadId = Thread.currentThread().getId();
            bReceiveCount++;
            return b;
        }
    }

    private static final class ProducerConcurrencyGate {
        private final CountDownLatch entered = new CountDownLatch(2);

        void enterAndAwaitPeer() throws InterruptedException {
            entered.countDown();
            if (!entered.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException(
                        "producer concurrency rendezvous timed out");
            }
        }

        boolean bothWorkersEntered() {
            return entered.getCount() == 0L;
        }
    }

    public static final class CrossMethodBugReachedException
            extends RuntimeException {
        private static final long serialVersionUID = 1L;

        CrossMethodBugReachedException(int producerValue,
                                       int thresholdValue) {
            super("cross-method consumer reached producer > threshold with "
                    + "producer=" + producerValue + ", threshold="
                    + thresholdValue);
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
                throw new IllegalStateException("worker interrupted",
                        exception);
            }
        }

        abstract void executeWorker() throws InterruptedException;
    }

    private static final class ProducerAThread extends WorkerThread {
        private final ProducerA producer;
        private final boolean enabled;
        private int baseInput;
        private final RpcBus bus;
        private final ProducerConcurrencyGate concurrencyGate;

        ProducerAThread(ProducerA producer, boolean enabled, int baseInput,
                        RpcBus bus, CountDownLatch start,
                        ProducerConcurrencyGate concurrencyGate) {
            super(PRODUCER_A_THREAD, start);
            this.producer = producer;
            this.enabled = enabled;
            this.baseInput = baseInput;
            this.bus = bus;
            this.concurrencyGate = concurrencyGate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            int value = producer.compute(enabled, baseInput);
            bus.publishA(value);
        }
    }

    private static final class ProducerBThread extends WorkerThread {
        private final ThresholdProducer producer;
        private final Boolean strictThreshold;
        private final RpcBus bus;
        private final ProducerConcurrencyGate concurrencyGate;

        ProducerBThread(Boolean strictThreshold, RpcBus bus,
                        CountDownLatch start,
                        ProducerConcurrencyGate concurrencyGate) {
            super(PRODUCER_B_THREAD, start);
            this.producer = new ThresholdProducer();
            this.strictThreshold = strictThreshold;
            this.bus = bus;
            this.concurrencyGate = concurrencyGate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            concurrencyGate.enterAndAwaitPeer();
            int value = producer.compute(strictThreshold);
            bus.publishB(value);
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
            int producerValue = bus.getRPCFromA();
            int witnessValue = bus.getRPCWitnessFromA();
            int thresholdValue = bus.getRPCFromB();
            receivedA = producerValue;
            receivedB = thresholdValue;
            received = true;
            // Keep the correlation guard first so the non-bug discovery seed
            // still executes the terminal threshold branch.
            if (producerValue + witnessValue == 100
                    && producerValue > thresholdValue) {
                throw new @CausynthExceptionTarget("cross-method-fields")
                        CrossMethodBugReachedException(producerValue,
                                thresholdValue);
            }
        }
    }

    public static final class ChannelObservation {
        private final String channel;
        private final int value;
        private final long publisherThreadId;
        private final long consumerThreadId;

        ChannelObservation(String channel, int value,
                           long publisherThreadId, long consumerThreadId) {
            this.channel = channel;
            this.value = value;
            this.publisherThreadId = publisherThreadId;
            this.consumerThreadId = consumerThreadId;
        }

        public String getChannel() {
            return channel;
        }

        public int getValue() {
            return value;
        }

        public long getPublisherThreadId() {
            return publisherThreadId;
        }

        public long getConsumerThreadId() {
            return consumerThreadId;
        }

        public boolean isCrossThread() {
            return publisherThreadId > 0L && consumerThreadId > 0L
                    && publisherThreadId != consumerThreadId;
        }
    }

    public static final class RunResult {
        private final Boolean producerAEnabled;
        private final Boolean strictThreshold;
        private final int producerValue;
        private final int thresholdValue;
        private final Throwable failure;
        private final String failureThread;
        private final long[] workerThreadIds;
        private final List<ChannelObservation> observations;
        private final boolean producerConcurrencyObserved;
        private final boolean consumerStartedAfterProducersTerminated;

        RunResult(Boolean producerAEnabled, Boolean strictThreshold,
                  int producerValue, int thresholdValue, Throwable failure,
                  String failureThread, long[] workerThreadIds,
                  List<ChannelObservation> observations,
                  boolean producerConcurrencyObserved,
                  boolean consumerStartedAfterProducersTerminated) {
            this.producerAEnabled = producerAEnabled;
            this.strictThreshold = strictThreshold;
            this.producerValue = producerValue;
            this.thresholdValue = thresholdValue;
            this.failure = failure;
            this.failureThread = failureThread;
            this.workerThreadIds = workerThreadIds.clone();
            this.observations = Collections.unmodifiableList(
                    new ArrayList<>(observations));
            this.producerConcurrencyObserved = producerConcurrencyObserved;
            this.consumerStartedAfterProducersTerminated =
                    consumerStartedAfterProducersTerminated;
        }

        public Throwable getFailure() {
            return failure;
        }

        public String getFailureThread() {
            return failureThread;
        }

        public long[] getWorkerThreadIds() {
            return workerThreadIds.clone();
        }

        public List<ChannelObservation> getObservations() {
            return observations;
        }

        public boolean isProducerConcurrencyObserved() {
            return producerConcurrencyObserved;
        }

        public boolean isConsumerStartedAfterProducersTerminated() {
            return consumerStartedAfterProducersTerminated;
        }

        public boolean isBugReached() {
            return failure instanceof CrossMethodBugReachedException;
        }

        public String toJson() {
            return "{\"kind\":\"CROSS_METHOD_EXTERNAL_FIELD_RESULT\","
                    + "\"producerAEnabled\":" + producerAEnabled + ','
                    + "\"strictThreshold\":" + strictThreshold + ','
                    + "\"producerValue\":" + producerValue + ','
                    + "\"thresholdValue\":" + thresholdValue + ','
                    + "\"bugReached\":" + isBugReached() + ','
                    + "\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean producerAEnabled,
                                    Boolean strictThreshold)
            throws InterruptedException {
        if (producerAEnabled == null || strictThreshold == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }

        ExternalProfile profile = new ExternalProfile(2);
        ProducerA producerA = new ProducerA(profile);
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        ProducerConcurrencyGate concurrencyGate =
                new ProducerConcurrencyGate();
        ProducerAThread producerAThread = new ProducerAThread(producerA,
                producerAEnabled.booleanValue(), DEFAULT_BASE_INPUT, bus,
                start, concurrencyGate);
        ProducerBThread producerBThread = new ProducerBThread(
                strictThreshold, bus, start, concurrencyGate);
        ConsumerThread consumer = new ConsumerThread(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        producerAThread.setUncaughtExceptionHandler(handler);
        producerBThread.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        producerAThread.start();
        producerBThread.start();
        start.countDown();
        join(producerAThread);
        join(producerBThread);
        boolean producersTerminated = producerAThread.getState()
                == Thread.State.TERMINATED
                && producerBThread.getState() == Thread.State.TERMINATED
                && consumer.getState() == Thread.State.NEW;
        consumer.start();
        join(consumer);
        if (!consumer.received && failure.get() == null) {
            throw new IllegalStateException("consumer produced no result");
        }

        List<ChannelObservation> observations = new ArrayList<>();
        if (bus.aReceiveCount == 1 && bus.aWitnessReceiveCount == 1) {
            observations.add(new ChannelObservation("A", bus.a,
                    bus.aPublisherThreadId, bus.aConsumerThreadId));
        }
        if (bus.bReceiveCount == 1) {
            observations.add(new ChannelObservation("B", bus.b,
                    bus.bPublisherThreadId, bus.bConsumerThreadId));
        }
        int producerValue = consumer.received ? consumer.receivedA : bus.a;
        int thresholdValue = consumer.received ? consumer.receivedB : bus.b;
        return new RunResult(producerAEnabled, strictThreshold,
                producerValue, thresholdValue, failure.get(),
                failureThread.get(),
                new long[]{producerAThread.getId(), producerBThread.getId(),
                        consumer.getId()}, observations,
                concurrencyGate.bothWorkersEntered(), producersTerminated);
    }

    private static void join(Thread thread) throws InterruptedException {
        thread.join(JOIN_TIMEOUT_MILLIS);
        if (thread.isAlive()) {
            thread.interrupt();
            throw new IllegalStateException("worker did not terminate: "
                    + thread.getName());
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <producerAEnabled> <strictThreshold>");
        }
        RunResult result = execute(parseBoolean(args[0]),
                parseBoolean(args[1]));
        System.out.println(result.toJson());
        rethrow(result.getFailure());
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

    private static void rethrow(Throwable failure) {
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
}
