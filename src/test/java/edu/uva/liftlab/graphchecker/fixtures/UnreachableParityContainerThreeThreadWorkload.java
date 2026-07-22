package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Three-thread container workload with a semantically unreachable target.
 *
 * <p>The array producer can publish only odd values and the map producer can
 * publish only even values.  Which value each producer publishes still
 * depends on a distinct nested container live-in, so proving the target
 * equality unreachable requires both complete guarded producer relations.
 * Treating either RPC result as an unconstrained integer makes the target
 * spuriously satisfiable.</p>
 */
public final class UnreachableParityContainerThreeThreadWorkload {
    public static final String ODD_PRODUCER_THREAD =
            "unreachable-odd-producer";
    public static final String EVEN_PRODUCER_THREAD =
            "unreachable-even-producer";
    public static final String CONSUMER_THREAD = "unreachable-consumer";
    private static final long TIMEOUT_MILLIS = 10_000L;

    private UnreachableParityContainerThreeThreadWorkload() {
    }

    static final class BooleanLeaf {
        boolean enabled;

        BooleanLeaf(Boolean enabled) {
            this.enabled = enabled.booleanValue();
        }
    }

    static final class GuardNode {
        BooleanLeaf guard;

        GuardNode(Boolean enabled) {
            guard = new BooleanLeaf(enabled);
        }
    }

    static final class StateNode {
        GuardNode state;

        StateNode(Boolean enabled) {
            state = new GuardNode(enabled);
        }
    }

    /** Reads index one; index zero is an intentionally opposite decoy. */
    public static final class OddArrayProducer {
        StateNode[] payloads;

        OddArrayProducer(Boolean enabled) {
            payloads = new StateNode[]{
                    new StateNode(Boolean.valueOf(!enabled.booleanValue())),
                    new StateNode(enabled)
            };
        }

        public int compute() {
            StateNode selected = payloads[1];
            boolean enabled = selected.state.guard.enabled;
            int sign;
            if (enabled) {
                sign = 1;
            } else {
                sign = -1;
            }
            return sign * 2 + 1;
        }
    }

    /** Reads the value at exact key seven through a map-entry view. */
    public static final class EvenMapProducer {
        Map<Integer, StateNode> values;

        EvenMapProducer(Boolean enabled) {
            values = new LinkedHashMap<>();
            values.put(Integer.valueOf(7), new StateNode(enabled));
        }

        public int compute() {
            Iterator<Map.Entry<Integer, StateNode>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, StateNode> entry = iterator.next();
            StateNode selected = entry.getValue();
            boolean enabled = selected.state.guard.enabled;
            int magnitude;
            if (enabled) {
                magnitude = 2;
            } else {
                magnitude = 0;
            }
            return magnitude * 2;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch oddReady = new CountDownLatch(1);
        private final CountDownLatch evenReady = new CountDownLatch(1);
        private volatile int odd;
        private volatile int even;
        private volatile long oddPublisherThreadId;
        private volatile long evenPublisherThreadId;
        private volatile long oddConsumerThreadId;
        private volatile long evenConsumerThreadId;
        private volatile int oddReceiveCount;
        private volatile int evenReceiveCount;

        public void publishOdd(int value) {
            odd = value;
            oddPublisherThreadId = Thread.currentThread().getId();
            oddReady.countDown();
        }

        public void publishEven(int value) {
            even = value;
            evenPublisherThreadId = Thread.currentThread().getId();
            evenReady.countDown();
        }

        public int getRPCFromOdd() throws InterruptedException {
            if (!oddReady.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("odd RPC timed out");
            }
            oddConsumerThreadId = Thread.currentThread().getId();
            oddReceiveCount++;
            return odd;
        }

        public int getRPCFromEven() throws InterruptedException {
            if (!evenReady.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("even RPC timed out");
            }
            evenConsumerThreadId = Thread.currentThread().getId();
            evenReceiveCount++;
            return even;
        }
    }

    private static final class ProducerGate {
        private final CountDownLatch entered = new CountDownLatch(2);

        void enterAndAwaitPeer() throws InterruptedException {
            entered.countDown();
            if (!entered.await(TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException(
                        "producer rendezvous timed out");
            }
        }

        boolean bothEntered() {
            return entered.getCount() == 0L;
        }
    }

    public static final class ImpossibleParityException
            extends RuntimeException {
        ImpossibleParityException(int odd, int even) {
            super("an odd producer value equalled an even producer value: "
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

    private static final class OddProducerThread extends Worker {
        private final OddArrayProducer producer;
        private final RpcBus bus;
        private final ProducerGate gate;

        OddProducerThread(OddArrayProducer producer, RpcBus bus,
                          CountDownLatch start, ProducerGate gate) {
            super(ODD_PRODUCER_THREAD, start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishOdd(producer.compute());
        }
    }

    private static final class EvenProducerThread extends Worker {
        private final EvenMapProducer producer;
        private final RpcBus bus;
        private final ProducerGate gate;

        EvenProducerThread(EvenMapProducer producer, RpcBus bus,
                           CountDownLatch start, ProducerGate gate) {
            super(EVEN_PRODUCER_THREAD, start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishEven(producer.compute());
        }
    }

    private static final class ConsumerThread extends Worker {
        private final RpcBus bus;
        private volatile int receivedOdd;
        private volatile int receivedEven;
        private volatile boolean received;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super(CONSUMER_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int odd = bus.getRPCFromOdd();
            int even = bus.getRPCFromEven();
            receivedOdd = odd;
            receivedEven = even;
            received = true;
            if (odd == even) {
                throw new @CausynthExceptionTarget("unreachable-parity")
                        ImpossibleParityException(odd, even);
            }
        }
    }

    public static final class RunResult {
        private final Boolean oddInput;
        private final Boolean evenInput;
        private final int oddValue;
        private final int evenValue;
        private final Throwable failure;
        private final String failureThread;
        private final long[] workerThreadIds;
        private final boolean producerConcurrencyObserved;
        private final boolean consumerStartedAfterProducersTerminated;
        private final boolean channelIdentityValid;

        RunResult(Boolean oddInput, Boolean evenInput, int oddValue,
                  int evenValue, Throwable failure, String failureThread,
                  long[] workerThreadIds,
                  boolean producerConcurrencyObserved,
                  boolean consumerStartedAfterProducersTerminated,
                  boolean channelIdentityValid) {
            this.oddInput = oddInput;
            this.evenInput = evenInput;
            this.oddValue = oddValue;
            this.evenValue = evenValue;
            this.failure = failure;
            this.failureThread = failureThread;
            this.workerThreadIds = workerThreadIds.clone();
            this.producerConcurrencyObserved = producerConcurrencyObserved;
            this.consumerStartedAfterProducersTerminated =
                    consumerStartedAfterProducersTerminated;
            this.channelIdentityValid = channelIdentityValid;
        }

        public Boolean getOddInput() {
            return oddInput;
        }

        public Boolean getEvenInput() {
            return evenInput;
        }

        public int getOddValue() {
            return oddValue;
        }

        public int getEvenValue() {
            return evenValue;
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

        public boolean isBugReached() {
            return failure instanceof ImpossibleParityException;
        }

        public boolean isProducerConcurrencyObserved() {
            return producerConcurrencyObserved;
        }

        public boolean isConsumerStartedAfterProducersTerminated() {
            return consumerStartedAfterProducersTerminated;
        }

        public boolean isChannelIdentityValid() {
            return channelIdentityValid;
        }

        public String toJson() {
            return "{\"kind\":\"UNREACHABLE_PARITY_CONTAINER_RESULT\","
                    + "\"oddInput\":" + oddInput + ','
                    + "\"evenInput\":" + evenInput + ','
                    + "\"oddValue\":" + oddValue + ','
                    + "\"evenValue\":" + evenValue + ','
                    + "\"bugReached\":" + isBugReached() + ','
                    + "\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean oddInput, Boolean evenInput)
            throws InterruptedException {
        if (oddInput == null || evenInput == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        ProducerGate gate = new ProducerGate();
        OddProducerThread odd = new OddProducerThread(
                new OddArrayProducer(oddInput), bus, start, gate);
        EvenProducerThread even = new EvenProducerThread(
                new EvenMapProducer(evenInput), bus, start, gate);
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
        boolean producersTerminated = odd.getState() == Thread.State.TERMINATED
                && even.getState() == Thread.State.TERMINATED
                && consumer.getState() == Thread.State.NEW;
        consumer.start();
        join(consumer);
        if (!consumer.received && failure.get() == null) {
            throw new IllegalStateException("consumer produced no result");
        }

        boolean channelIdentity = bus.oddReceiveCount == 1
                && bus.evenReceiveCount == 1
                && bus.oddPublisherThreadId == odd.getId()
                && bus.evenPublisherThreadId == even.getId()
                && bus.oddConsumerThreadId == consumer.getId()
                && bus.evenConsumerThreadId == consumer.getId()
                && odd.getId() != consumer.getId()
                && even.getId() != consumer.getId();
        return new RunResult(oddInput, evenInput, consumer.receivedOdd,
                consumer.receivedEven, failure.get(), failureThread.get(),
                new long[]{odd.getId(), even.getId(), consumer.getId()},
                gate.bothEntered(), producersTerminated, channelIdentity);
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
            throw new IllegalArgumentException(
                    "expected: <oddInput> <evenInput>");
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
