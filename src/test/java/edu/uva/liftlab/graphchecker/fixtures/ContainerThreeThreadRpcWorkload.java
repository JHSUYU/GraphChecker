package edu.uva.liftlab.graphchecker.fixtures;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Three-thread target whose producer inputs are nested container leaves.
 *
 * <p>The array producer reads {@code payloads[0].state.guard.enabled}.  The
 * map producer reads {@code entry.value.state.guard.enabled}.  Both container
 * graphs are constructed before either producer region starts, so the scalar
 * leaves are genuine region live-ins.  The map contains one immutable key and
 * is traversed without a loop to keep the runtime selector unique.</p>
 */
public final class ContainerThreeThreadRpcWorkload {
    public static final String ARRAY_PRODUCER_THREAD =
            "container-array-producer";
    public static final String MAP_PRODUCER_THREAD =
            "container-map-producer";
    public static final String CONSUMER_THREAD = "container-consumer";
    private static final long JOIN_TIMEOUT_MILLIS = 10_000L;

    private ContainerThreeThreadRpcWorkload() {
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

    public static final class ArrayProducer {
        StateNode[] payloads;

        ArrayProducer(Boolean enabled) {
            payloads = new StateNode[]{new StateNode(enabled)};
        }

        public int compute() {
            StateNode payload = payloads[0];
            boolean enabled = payload.state.guard.enabled;
            if (enabled) {
                return 1;
            }
            return -1;
        }
    }

    public static final class MapProducer {
        Map<Integer, StateNode> values;

        MapProducer(Boolean enabled) {
            values = new LinkedHashMap<>();
            values.put(Integer.valueOf(7), new StateNode(enabled));
        }

        public int compute() {
            Iterator<Map.Entry<Integer, StateNode>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, StateNode> entry = iterator.next();
            StateNode value = entry.getValue();
            boolean enabled = value.state.guard.enabled;
            if (enabled) {
                return 0;
            }
            return 10;
        }
    }

    public static final class RpcBus {
        private final CountDownLatch arrayReady = new CountDownLatch(1);
        private final CountDownLatch mapReady = new CountDownLatch(1);
        volatile int arrayValue;
        volatile int mapValue;
        volatile long arrayPublisherThreadId;
        volatile long mapPublisherThreadId;
        volatile long arrayConsumerThreadId;
        volatile long mapConsumerThreadId;
        volatile int arrayReceiveCount;
        volatile int mapReceiveCount;

        public void publishArray(int value) {
            arrayValue = value;
            arrayPublisherThreadId = Thread.currentThread().getId();
            arrayReady.countDown();
        }

        public void publishMap(int value) {
            mapValue = value;
            mapPublisherThreadId = Thread.currentThread().getId();
            mapReady.countDown();
        }

        public int getRPCFromArray() throws InterruptedException {
            if (!arrayReady.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("array RPC timed out");
            }
            arrayConsumerThreadId = Thread.currentThread().getId();
            arrayReceiveCount++;
            return arrayValue;
        }

        public int getRPCFromMap() throws InterruptedException {
            if (!mapReady.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("map RPC timed out");
            }
            mapConsumerThreadId = Thread.currentThread().getId();
            mapReceiveCount++;
            return mapValue;
        }
    }

    private static final class ProducerConcurrencyGate {
        private final CountDownLatch entered = new CountDownLatch(2);

        void enterAndAwaitPeer() throws InterruptedException {
            entered.countDown();
            if (!entered.await(JOIN_TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException(
                        "container producer rendezvous timed out");
            }
        }

        boolean bothWorkersEntered() {
            return entered.getCount() == 0L;
        }
    }

    public static final class ContainerBugReachedException
            extends RuntimeException {
        ContainerBugReachedException(int arrayValue, int mapValue) {
            super("container consumer reached array > map with array="
                    + arrayValue + ", map=" + mapValue);
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

    private static final class ArrayProducerThread extends WorkerThread {
        private final ArrayProducer producer;
        private final RpcBus bus;
        private final ProducerConcurrencyGate gate;

        ArrayProducerThread(ArrayProducer producer, RpcBus bus,
                            CountDownLatch start,
                            ProducerConcurrencyGate gate) {
            super(ARRAY_PRODUCER_THREAD, start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            int value = producer.compute();
            bus.publishArray(value);
        }
    }

    private static final class MapProducerThread extends WorkerThread {
        private final MapProducer producer;
        private final RpcBus bus;
        private final ProducerConcurrencyGate gate;

        MapProducerThread(MapProducer producer, RpcBus bus,
                          CountDownLatch start,
                          ProducerConcurrencyGate gate) {
            super(MAP_PRODUCER_THREAD, start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            int value = producer.compute();
            bus.publishMap(value);
        }
    }

    private static final class ConsumerThread extends WorkerThread {
        private final RpcBus bus;
        volatile int receivedArray;
        volatile int receivedMap;
        volatile boolean received;

        ConsumerThread(RpcBus bus, CountDownLatch start) {
            super(CONSUMER_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int arrayValue = bus.getRPCFromArray();
            int mapValue = bus.getRPCFromMap();
            receivedArray = arrayValue;
            receivedMap = mapValue;
            received = true;
            if (arrayValue > mapValue) {
                throw new ContainerBugReachedException(arrayValue, mapValue);
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
        private final Boolean arrayInput;
        private final Boolean mapInput;
        private final int arrayValue;
        private final int mapValue;
        private final Throwable failure;
        private final String failureThread;
        private final long[] workerThreadIds;
        private final List<ChannelObservation> observations;
        private final boolean producerConcurrencyObserved;
        private final boolean consumerStartedAfterProducersTerminated;

        RunResult(Boolean arrayInput, Boolean mapInput, int arrayValue,
                  int mapValue, Throwable failure, String failureThread,
                  long[] workerThreadIds,
                  List<ChannelObservation> observations,
                  boolean producerConcurrencyObserved,
                  boolean consumerStartedAfterProducersTerminated) {
            this.arrayInput = arrayInput;
            this.mapInput = mapInput;
            this.arrayValue = arrayValue;
            this.mapValue = mapValue;
            this.failure = failure;
            this.failureThread = failureThread;
            this.workerThreadIds = workerThreadIds.clone();
            this.observations = Collections.unmodifiableList(
                    new ArrayList<>(observations));
            this.producerConcurrencyObserved = producerConcurrencyObserved;
            this.consumerStartedAfterProducersTerminated =
                    consumerStartedAfterProducersTerminated;
        }

        public Boolean getArrayInput() {
            return arrayInput;
        }

        public Boolean getMapInput() {
            return mapInput;
        }

        public int getArrayValue() {
            return arrayValue;
        }

        public int getMapValue() {
            return mapValue;
        }

        public boolean isBugReached() {
            return failure instanceof ContainerBugReachedException;
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

        public String toJson() {
            return "{\"kind\":\"CONTAINER_THREE_THREAD_RESULT\","
                    + "\"arrayInput\":" + arrayInput + ','
                    + "\"mapInput\":" + mapInput + ','
                    + "\"arrayValue\":" + arrayValue + ','
                    + "\"mapValue\":" + mapValue + ','
                    + "\"bugReached\":" + isBugReached() + ','
                    + "\"failureThread\":" + (failureThread == null
                    ? "null" : "\"" + failureThread + "\"") + '}';
        }
    }

    public static RunResult execute(Boolean arrayInput, Boolean mapInput)
            throws InterruptedException {
        if (arrayInput == null || mapInput == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        ArrayProducer arrayProducer = new ArrayProducer(arrayInput);
        MapProducer mapProducer = new MapProducer(mapInput);
        RpcBus bus = new RpcBus();
        CountDownLatch start = new CountDownLatch(1);
        ProducerConcurrencyGate gate = new ProducerConcurrencyGate();
        ArrayProducerThread arrayThread = new ArrayProducerThread(
                arrayProducer, bus, start, gate);
        MapProducerThread mapThread = new MapProducerThread(mapProducer,
                bus, start, gate);
        ConsumerThread consumer = new ConsumerThread(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        arrayThread.setUncaughtExceptionHandler(handler);
        mapThread.setUncaughtExceptionHandler(handler);
        consumer.setUncaughtExceptionHandler(handler);

        arrayThread.start();
        mapThread.start();
        start.countDown();
        join(arrayThread);
        join(mapThread);
        boolean producersTerminated = arrayThread.getState()
                == Thread.State.TERMINATED
                && mapThread.getState() == Thread.State.TERMINATED
                && consumer.getState() == Thread.State.NEW;
        consumer.start();
        join(consumer);
        if (!consumer.received && failure.get() == null) {
            throw new IllegalStateException("consumer produced no result");
        }

        List<ChannelObservation> observations = new ArrayList<>();
        if (bus.arrayReceiveCount == 1) {
            observations.add(new ChannelObservation("ARRAY",
                    bus.arrayValue, bus.arrayPublisherThreadId,
                    bus.arrayConsumerThreadId));
        }
        if (bus.mapReceiveCount == 1) {
            observations.add(new ChannelObservation("MAP", bus.mapValue,
                    bus.mapPublisherThreadId, bus.mapConsumerThreadId));
        }
        int arrayValue = consumer.received
                ? consumer.receivedArray : bus.arrayValue;
        int mapValue = consumer.received
                ? consumer.receivedMap : bus.mapValue;
        return new RunResult(arrayInput, mapInput, arrayValue, mapValue,
                failure.get(), failureThread.get(),
                new long[]{arrayThread.getId(), mapThread.getId(),
                        consumer.getId()}, observations,
                gate.bothWorkersEntered(), producersTerminated);
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
                    "expected: <arrayInput> <mapInput>");
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
