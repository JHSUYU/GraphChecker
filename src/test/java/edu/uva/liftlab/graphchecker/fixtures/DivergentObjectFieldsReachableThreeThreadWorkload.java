package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
 * SAT case whose selected output follows two different nested object fields.
 */
public final class DivergentObjectFieldsReachableThreeThreadWorkload {
    private DivergentObjectFieldsReachableThreeThreadWorkload() {
    }

    static final class MutableState {
        int primary;
        int backup;

        MutableState(int primary, int backup) {
            this.primary = primary;
            this.backup = backup;
        }
    }

    static final class Envelope {
        boolean enabled;
        MutableState state;

        Envelope(Boolean enabled) {
            this.enabled = enabled.booleanValue();
            state = new MutableState(0, 0);
        }
    }

    static final class ObjectProducer {
        Envelope envelope;

        ObjectProducer(Boolean enabled) {
            envelope = new Envelope(enabled);
        }

        int compute() {
            int primary = clamp(envelope.state.primary,
                    envelope.state.backup, envelope.enabled);
            int backup = clamp(envelope.state.backup,
                    envelope.state.primary, !envelope.enabled);
            if (envelope.enabled) {
                envelope.state.primary = primary + 6;
            } else {
                envelope.state.backup = backup + 5;
            }
            int selected = envelope.enabled
                    ? envelope.state.primary : envelope.state.backup;
            for (int index = 0; index < 4; index++) {
                if ((index < 3 && envelope.enabled)
                        || (index > 0 && !envelope.enabled
                        && backup >= primary)) {
                    selected++;
                } else if ((index == 3 && envelope.enabled)
                        || (index == 0 && !envelope.enabled)) {
                    selected += primary - primary;
                } else {
                    selected--;
                }
            }
            return selected;
        }

        private static int clamp(int value, int peer, boolean preferred) {
            if ((value < 0 && peer >= 0)
                    || (value == -1 && !preferred)) {
                return 0;
            }
            if ((value > 4 && (preferred || peer <= 4))
                    || (value == 5 && peer < 0)) {
                return 4;
            }
            return value;
        }
    }

    static final class ArrayProducer {
        Envelope[] values;

        ArrayProducer(Boolean enabled) {
            values = new Envelope[]{
                    new Envelope(Boolean.valueOf(!enabled.booleanValue())),
                    new Envelope(enabled)
            };
        }

        int compute() {
            Envelope selected = values[1];
            int value = selected.state.primary;
            int peer = selected.state.backup;
            if ((value < 0 && peer >= 0)
                    || (value == -1 && !selected.enabled)) {
                value = 0;
            }
            if ((value > 3 && (selected.enabled || peer <= 3))
                    || (value == 4 && peer < 0)) {
                value = 3;
            }
            int adjustment = 0;
            for (int index = 0; index < 4; index++) {
                if ((index < 2 && selected.enabled)
                        || (index >= 2 && !selected.enabled)) {
                    adjustment++;
                } else if ((index == 3 && peer > value)
                        || (index == 0 && value > peer)) {
                    adjustment--;
                }
            }
            if (selected.enabled) {
                return value + adjustment + 2;
            }
            return value + adjustment + 5;
        }
    }

    static final class RpcBus {
        private final CountDownLatch objectReady = new CountDownLatch(1);
        private final CountDownLatch arrayReady = new CountDownLatch(1);
        volatile int objectValue;
        volatile int arrayValue;

        void publishObject(int value) {
            objectValue = value;
            objectReady.countDown();
        }

        void publishArray(int value) {
            arrayValue = value;
            arrayReady.countDown();
        }

        int receiveObject() throws InterruptedException {
            await(objectReady);
            return objectValue;
        }

        int receiveArray() throws InterruptedException {
            await(arrayReady);
            return arrayValue;
        }

        private static void await(CountDownLatch ready)
                throws InterruptedException {
            if (!ready.await(FixedOrderRpcFixtureSupport.TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC timed out");
            }
        }
    }

    public static final class DivergentFieldsBugException
            extends RuntimeException {
        DivergentFieldsBugException(int objectValue, int arrayValue) {
            super("divergent object fields reached target: " + objectValue
                    + ", " + arrayValue);
        }
    }

    static final class ObjectProducerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final ObjectProducer producer;
        private final RpcBus bus;
        private final FixedOrderRpcFixtureSupport.ProducerGate gate;

        ObjectProducerThread(CountDownLatch start, ObjectProducer producer,
                             RpcBus bus,
                             FixedOrderRpcFixtureSupport.ProducerGate gate) {
            super("divergent-object-producer", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishObject(producer.compute());
        }
    }

    static final class ArrayProducerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final ArrayProducer producer;
        private final RpcBus bus;
        private final FixedOrderRpcFixtureSupport.ProducerGate gate;

        ArrayProducerThread(CountDownLatch start, ArrayProducer producer,
                            RpcBus bus,
                            FixedOrderRpcFixtureSupport.ProducerGate gate) {
            super("divergent-array-producer", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishArray(producer.compute());
        }
    }

    static final class ConsumerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final RpcBus bus;

        ConsumerThread(CountDownLatch start, RpcBus bus) {
            super("divergent-fields-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int objectValue = bus.receiveObject();
            int arrayValue = bus.receiveArray();
            if ((objectValue > arrayValue && objectValue >= 9)
                    || (objectValue == 8 && arrayValue == 4)) {
                throw new @CausynthExceptionTarget(
                        "tricky-divergent-object-fields")
                        DivergentFieldsBugException(
                                objectValue, arrayValue);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <objectInput> <arrayInput>");
        }
        Boolean objectInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[0]);
        Boolean arrayInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[1]);
        CountDownLatch start = new CountDownLatch(1);
        FixedOrderRpcFixtureSupport.ProducerGate gate =
                new FixedOrderRpcFixtureSupport.ProducerGate();
        RpcBus bus = new RpcBus();
        ObjectProducerThread object = new ObjectProducerThread(start,
                new ObjectProducer(objectInput), bus, gate);
        ArrayProducerThread array = new ArrayProducerThread(start,
                new ArrayProducer(arrayInput), bus, gate);
        ConsumerThread consumer = new ConsumerThread(start, bus);
        Throwable failure = FixedOrderRpcFixtureSupport.run(
                start, object, array, consumer);
        System.out.println("{\"kind\":\"TRICKY_DIVERGENT_FIELDS\","
                + "\"objectValue\":" + bus.objectValue + ','
                + "\"arrayValue\":" + bus.arrayValue + '}');
        FixedOrderRpcFixtureSupport.propagate(failure);
    }
}
