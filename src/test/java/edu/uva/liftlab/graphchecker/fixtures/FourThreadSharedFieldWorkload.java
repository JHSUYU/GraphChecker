package edu.uva.liftlab.graphchecker.fixtures;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Four-thread shared-field target with two explicit propagation chains.
 *
 * <p>The topology is {@code thread-1 -> thread-2 -> thread-3} and
 * {@code thread-1 -> thread-4 -> thread-3}. Every edge is a declared-field
 * write/read pair guarded by a one-shot latch. This makes the concrete
 * read-from relation deterministic without declaring an RPC topology.</p>
 *
 * <p>The workload deliberately contains no loop. Thread 1 forks two values,
 * threads 2 and 4 transform their respective values, and thread 3 merges the
 * results at the exception sink.</p>
 */
public final class FourThreadSharedFieldWorkload {
    public static final String SOURCE_THREAD = "shared-field-thread-1";
    public static final String LEFT_RELAY_THREAD = "shared-field-thread-2";
    public static final String SINK_THREAD = "shared-field-thread-3";
    public static final String RIGHT_RELAY_THREAD = "shared-field-thread-4";
    private static final long JOIN_TIMEOUT_MILLIS = 10_000L;

    private FourThreadSharedFieldWorkload() {
    }

    public static final class SourceStage {
        public int valueForThreadTwo(Boolean input) {
            int value = -3;
            if (input.booleanValue()) {
                value = 1;
            }
            return value;
        }

        public int valueForThreadFour(Boolean input) {
            int value = -2;
            if (input.booleanValue()) {
                value = 2;
            }
            return value;
        }
    }

    public static final class ThreadTwoStage {
        public int transform(int valueFromThreadOne) {
            return valueFromThreadOne + 2;
        }
    }

    public static final class ThreadFourStage {
        public int transform(int valueFromThreadOne) {
            return valueFromThreadOne + 2;
        }
    }

    public static final class MergeBugReachedException
            extends RuntimeException {
        public MergeBugReachedException(int fromThreadTwo,
                                        int fromThreadFour) {
            super("thread 3 reached left > right with left="
                    + fromThreadTwo + ", right=" + fromThreadFour);
        }
    }

    /** Four deterministic shared-field channels, one for each graph edge. */
    public static final class SharedBus {
        final CountDownLatch oneToTwoReady = new CountDownLatch(1);
        final CountDownLatch oneToFourReady = new CountDownLatch(1);
        final CountDownLatch twoToThreeReady = new CountDownLatch(1);
        final CountDownLatch fourToThreeReady = new CountDownLatch(1);
        final AtomicLong eventSequence = new AtomicLong();

        volatile int oneToTwo;
        volatile int oneToFour;
        volatile int twoToThree;
        volatile int fourToThree;

        volatile long oneToTwoPublisherThreadId;
        volatile long oneToFourPublisherThreadId;
        volatile long twoToThreePublisherThreadId;
        volatile long fourToThreePublisherThreadId;
        volatile long oneToTwoConsumerThreadId;
        volatile long oneToFourConsumerThreadId;
        volatile long twoToThreeConsumerThreadId;
        volatile long fourToThreeConsumerThreadId;

        volatile long oneToTwoPublishSequence;
        volatile long oneToFourPublishSequence;
        volatile long twoToThreePublishSequence;
        volatile long fourToThreePublishSequence;
        volatile long oneToTwoReceiveSequence;
        volatile long oneToFourReceiveSequence;
        volatile long twoToThreeReceiveSequence;
        volatile long fourToThreeReceiveSequence;

        volatile int oneToTwoReceived;
        volatile int oneToFourReceived;
        volatile int twoToThreeReceived;
        volatile int fourToThreeReceived;
        volatile int oneToTwoReceiveCount;
        volatile int oneToFourReceiveCount;
        volatile int twoToThreeReceiveCount;
        volatile int fourToThreeReceiveCount;

        public void publishOneToTwo(int value) {
            oneToTwo = value;
            oneToTwoPublisherThreadId = Thread.currentThread().getId();
            oneToTwoPublishSequence = eventSequence.incrementAndGet();
            oneToTwoReady.countDown();
        }

        public void publishOneToFour(int value) {
            oneToFour = value;
            oneToFourPublisherThreadId = Thread.currentThread().getId();
            oneToFourPublishSequence = eventSequence.incrementAndGet();
            oneToFourReady.countDown();
        }

        public int readOneToTwo() throws InterruptedException {
            await(oneToTwoReady, "thread 1 -> thread 2");
            int received = oneToTwo;
            oneToTwoReceived = received;
            oneToTwoConsumerThreadId = Thread.currentThread().getId();
            oneToTwoReceiveSequence = eventSequence.incrementAndGet();
            oneToTwoReceiveCount++;
            return received;
        }

        public int readOneToFour() throws InterruptedException {
            await(oneToFourReady, "thread 1 -> thread 4");
            int received = oneToFour;
            oneToFourReceived = received;
            oneToFourConsumerThreadId = Thread.currentThread().getId();
            oneToFourReceiveSequence = eventSequence.incrementAndGet();
            oneToFourReceiveCount++;
            return received;
        }

        public void publishTwoToThree(int value) {
            twoToThree = value;
            twoToThreePublisherThreadId = Thread.currentThread().getId();
            twoToThreePublishSequence = eventSequence.incrementAndGet();
            twoToThreeReady.countDown();
        }

        public void publishFourToThree(int value) {
            fourToThree = value;
            fourToThreePublisherThreadId = Thread.currentThread().getId();
            fourToThreePublishSequence = eventSequence.incrementAndGet();
            fourToThreeReady.countDown();
        }

        public int readTwoToThree() throws InterruptedException {
            await(twoToThreeReady, "thread 2 -> thread 3");
            int received = twoToThree;
            twoToThreeReceived = received;
            twoToThreeConsumerThreadId = Thread.currentThread().getId();
            twoToThreeReceiveSequence = eventSequence.incrementAndGet();
            twoToThreeReceiveCount++;
            return received;
        }

        public int readFourToThree() throws InterruptedException {
            await(fourToThreeReady, "thread 4 -> thread 3");
            int received = fourToThree;
            fourToThreeReceived = received;
            fourToThreeConsumerThreadId = Thread.currentThread().getId();
            fourToThreeReceiveSequence = eventSequence.incrementAndGet();
            fourToThreeReceiveCount++;
            return received;
        }

        List<EdgeObservation> observations() {
            List<EdgeObservation> result = new ArrayList<>();
            if (oneToTwoReceiveCount == 1) {
                result.add(new EdgeObservation("1_TO_2", oneToTwo,
                        oneToTwoReceived, oneToTwoPublisherThreadId,
                        oneToTwoConsumerThreadId, oneToTwoPublishSequence,
                        oneToTwoReceiveSequence));
            }
            if (oneToFourReceiveCount == 1) {
                result.add(new EdgeObservation("1_TO_4", oneToFour,
                        oneToFourReceived, oneToFourPublisherThreadId,
                        oneToFourConsumerThreadId, oneToFourPublishSequence,
                        oneToFourReceiveSequence));
            }
            if (twoToThreeReceiveCount == 1) {
                result.add(new EdgeObservation("2_TO_3", twoToThree,
                        twoToThreeReceived, twoToThreePublisherThreadId,
                        twoToThreeConsumerThreadId, twoToThreePublishSequence,
                        twoToThreeReceiveSequence));
            }
            if (fourToThreeReceiveCount == 1) {
                result.add(new EdgeObservation("4_TO_3", fourToThree,
                        fourToThreeReceived,
                        fourToThreePublisherThreadId,
                        fourToThreeConsumerThreadId,
                        fourToThreePublishSequence,
                        fourToThreeReceiveSequence));
            }
            return result;
        }

        private static void await(CountDownLatch latch, String channel)
                throws InterruptedException {
            if (!latch.await(JOIN_TIMEOUT_MILLIS, TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException(channel + " timed out");
            }
        }
    }

    abstract static class WorkerThread extends Thread {
        final CountDownLatch start;

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

    static final class SourceThread extends WorkerThread {
        final Boolean leftInput;
        final Boolean rightInput;
        final SharedBus bus;
        volatile int sentToTwo;
        volatile int sentToFour;

        SourceThread(Boolean leftInput, Boolean rightInput, SharedBus bus,
                     CountDownLatch start) {
            super(SOURCE_THREAD, start);
            this.leftInput = leftInput;
            this.rightInput = rightInput;
            this.bus = bus;
        }

        @Override
        void executeWorker() {
            SourceStage stage = new SourceStage();
            int forTwo = stage.valueForThreadTwo(leftInput);
            int forFour = stage.valueForThreadFour(rightInput);
            sentToTwo = forTwo;
            sentToFour = forFour;
            bus.publishOneToTwo(forTwo);
            bus.publishOneToFour(forFour);
        }
    }

    static final class ThreadTwo extends WorkerThread {
        final SharedBus bus;
        volatile int published;

        ThreadTwo(SharedBus bus, CountDownLatch start) {
            super(LEFT_RELAY_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int fromOne = bus.readOneToTwo();
            int transformed = new ThreadTwoStage().transform(fromOne);
            published = transformed;
            bus.publishTwoToThree(transformed);
        }
    }

    static final class ThreadFour extends WorkerThread {
        final SharedBus bus;
        volatile int published;

        ThreadFour(SharedBus bus, CountDownLatch start) {
            super(RIGHT_RELAY_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int fromOne = bus.readOneToFour();
            int transformed = new ThreadFourStage().transform(fromOne);
            published = transformed;
            bus.publishFourToThree(transformed);
        }
    }

    static final class ThreadThree extends WorkerThread {
        final SharedBus bus;
        volatile int receivedFromTwo;
        volatile int receivedFromFour;
        volatile boolean received;

        ThreadThree(SharedBus bus, CountDownLatch start) {
            super(SINK_THREAD, start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int fromTwo = bus.readTwoToThree();
            int fromFour = bus.readFourToThree();
            receivedFromTwo = fromTwo;
            receivedFromFour = fromFour;
            received = true;
            if (fromTwo > fromFour) {
                throw new MergeBugReachedException(fromTwo, fromFour);
            }
        }
    }

    public static final class EdgeObservation {
        private final String channel;
        private final int publishedValue;
        private final int receivedValue;
        private final long publisherThreadId;
        private final long consumerThreadId;
        private final long publishSequence;
        private final long receiveSequence;
        private final String valueFingerprint;

        EdgeObservation(String channel, int publishedValue,
                        int receivedValue, long publisherThreadId,
                        long consumerThreadId, long publishSequence,
                        long receiveSequence) {
            this.channel = channel;
            this.publishedValue = publishedValue;
            this.receivedValue = receivedValue;
            this.publisherThreadId = publisherThreadId;
            this.consumerThreadId = consumerThreadId;
            this.publishSequence = publishSequence;
            this.receiveSequence = receiveSequence;
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

        public long getPublishSequence() {
            return publishSequence;
        }

        public long getReceiveSequence() {
            return receiveSequence;
        }

        public String getValueFingerprint() {
            return valueFingerprint;
        }

        public boolean isHappensBeforeObserved() {
            return publishedValue == receivedValue
                    && publisherThreadId != consumerThreadId
                    && publishSequence > 0L
                    && publishSequence < receiveSequence;
        }

        String toJson() {
            return "{\"channel\":\"" + channel + "\","
                    + "\"publishedValue\":" + publishedValue + ','
                    + "\"receivedValue\":" + receivedValue + ','
                    + "\"publisherThreadId\":" + publisherThreadId + ','
                    + "\"consumerThreadId\":" + consumerThreadId + ','
                    + "\"publishSequence\":" + publishSequence + ','
                    + "\"receiveSequence\":" + receiveSequence + ','
                    + "\"happensBeforeObserved\":"
                    + isHappensBeforeObserved() + ','
                    + "\"valueFingerprint\":\"" + valueFingerprint
                    + "\"}";
        }
    }

    public static final class RunResult {
        private final Boolean leftInput;
        private final Boolean rightInput;
        private final int sourceForTwo;
        private final int sourceForFour;
        private final int fromTwo;
        private final int fromFour;
        private final long[] workerThreadIds;
        private final String failureThread;
        private final Throwable failure;
        private final List<EdgeObservation> observations;

        RunResult(Boolean leftInput, Boolean rightInput, int sourceForTwo,
                  int sourceForFour, int fromTwo, int fromFour,
                  long[] workerThreadIds, String failureThread,
                  Throwable failure, List<EdgeObservation> observations) {
            this.leftInput = leftInput;
            this.rightInput = rightInput;
            this.sourceForTwo = sourceForTwo;
            this.sourceForFour = sourceForFour;
            this.fromTwo = fromTwo;
            this.fromFour = fromFour;
            this.workerThreadIds = workerThreadIds.clone();
            this.failureThread = failureThread;
            this.failure = failure;
            this.observations = Collections.unmodifiableList(
                    new ArrayList<>(observations));
        }

        public Boolean getLeftInput() {
            return leftInput;
        }

        public Boolean getRightInput() {
            return rightInput;
        }

        public int getSourceForTwo() {
            return sourceForTwo;
        }

        public int getSourceForFour() {
            return sourceForFour;
        }

        public int getFromTwo() {
            return fromTwo;
        }

        public int getFromFour() {
            return fromFour;
        }

        public boolean isBugReached() {
            return failure instanceof MergeBugReachedException;
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

        public List<EdgeObservation> getObservations() {
            return observations;
        }

        public String toJson() {
            StringBuilder edges = new StringBuilder();
            for (EdgeObservation observation : observations) {
                if (edges.length() > 0) {
                    edges.append(',');
                }
                edges.append(observation.toJson());
            }
            return "{\"kind\":\"FOUR_THREAD_SHARED_FIELD_RESULT\","
                    + "\"leftInput\":" + leftInput + ','
                    + "\"rightInput\":" + rightInput + ','
                    + "\"sourceForTwo\":" + sourceForTwo + ','
                    + "\"sourceForFour\":" + sourceForFour + ','
                    + "\"fromTwo\":" + fromTwo + ','
                    + "\"fromFour\":" + fromFour + ','
                    + "\"bugReached\":" + isBugReached() + ','
                    + "\"workerThreadIds\":[" + workerThreadIds[0] + ','
                    + workerThreadIds[1] + ',' + workerThreadIds[2] + ','
                    + workerThreadIds[3] + "],\"failureThread\":"
                    + (failureThread == null ? "null" : "\""
                    + failureThread + "\"") + ",\"edgeObservations\":["
                    + edges + "]}";
        }
    }

    public static RunResult execute(Boolean leftInput, Boolean rightInput)
            throws InterruptedException {
        if (leftInput == null || rightInput == null) {
            throw new IllegalArgumentException("inputs must be non-null");
        }
        SharedBus bus = new SharedBus();
        CountDownLatch start = new CountDownLatch(1);
        SourceThread threadOne = new SourceThread(leftInput, rightInput, bus,
                start);
        ThreadTwo threadTwo = new ThreadTwo(bus, start);
        ThreadThree threadThree = new ThreadThree(bus, start);
        ThreadFour threadFour = new ThreadFour(bus, start);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        AtomicReference<String> failureThread = new AtomicReference<>();
        Thread.UncaughtExceptionHandler handler = (thread, throwable) -> {
            if (failure.compareAndSet(null, throwable)) {
                failureThread.set(thread.getName());
            }
        };
        threadOne.setUncaughtExceptionHandler(handler);
        threadTwo.setUncaughtExceptionHandler(handler);
        threadThree.setUncaughtExceptionHandler(handler);
        threadFour.setUncaughtExceptionHandler(handler);

        threadOne.start();
        threadTwo.start();
        threadThree.start();
        threadFour.start();
        start.countDown();
        join(threadOne);
        join(threadTwo);
        join(threadFour);
        join(threadThree);
        if (!threadThree.received && failure.get() == null) {
            throw new IllegalStateException("thread 3 produced no result");
        }

        return new RunResult(leftInput, rightInput, threadOne.sentToTwo,
                threadOne.sentToFour, threadThree.receivedFromTwo,
                threadThree.receivedFromFour,
                new long[]{threadOne.getId(), threadTwo.getId(),
                        threadThree.getId(), threadFour.getId()},
                failureThread.get(), failure.get(), bus.observations());
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
            throw new IllegalArgumentException("expected: <left> <right>");
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
