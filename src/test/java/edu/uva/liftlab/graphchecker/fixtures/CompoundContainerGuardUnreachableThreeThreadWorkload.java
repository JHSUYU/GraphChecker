package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
 * UNSAT case with a pre-guard and a compound target guard.
 */
public final class CompoundContainerGuardUnreachableThreeThreadWorkload {
    private CompoundContainerGuardUnreachableThreeThreadWorkload() {
    }

    static final class Flag {
        boolean enabled;

        Flag(Boolean enabled) {
            this.enabled = enabled.booleanValue();
        }
    }

    static final class NestedState {
        Flag flag;

        NestedState(Boolean enabled) {
            flag = new Flag(enabled);
        }
    }

    static final class ArrayProducer {
        NestedState[] states;

        ArrayProducer(Boolean enabled) {
            states = new NestedState[]{
                    new NestedState(Boolean.valueOf(
                            !enabled.booleanValue())),
                    new NestedState(enabled)
            };
        }

        int compute() {
            NestedState selected = states[1];
            NestedState decoy = states[0];
            int value = 0;
            for (int index = 0; index < 4; index++) {
                if (index < 2 && (selected.flag.enabled
                        || decoy.flag.enabled)) {
                    value++;
                } else if ((index == 2 && selected.flag.enabled
                        && !decoy.flag.enabled)
                        || (index == 3 && !selected.flag.enabled
                        && decoy.flag.enabled)) {
                    value += index - index;
                } else if (index > 1 && value < 0) {
                    value--;
                }
            }
            if (selected.flag.enabled && (value == 2
                    || !decoy.flag.enabled)) {
                value += 4;
            }
            return value;
        }
    }

    static final class MapProducer {
        Map<Integer, NestedState> states;

        MapProducer(Boolean enabled) {
            states = new LinkedHashMap<>();
            states.put(Integer.valueOf(10), new NestedState(enabled));
        }

        int compute() {
            Iterator<Map.Entry<Integer, NestedState>> iterator =
                    states.entrySet().iterator();
            Map.Entry<Integer, NestedState> entry = iterator.next();
            int value = entry.getKey().intValue();
            boolean enabled = entry.getValue().flag.enabled;
            int offset = 0;
            for (int index = 0; index < 4; index++) {
                if (((index == 0 || index == 2) && enabled)
                        || ((index == 1 || index == 3) && !enabled)) {
                    offset++;
                } else {
                    offset--;
                }
            }
            if ((enabled && value >= 10)
                    || (offset > 0 && value < 0)) {
                value += 4;
            }
            return value + offset;
        }
    }

    static final class RpcBus {
        private final CountDownLatch arrayReady = new CountDownLatch(1);
        private final CountDownLatch mapReady = new CountDownLatch(1);
        volatile int arrayValue;
        volatile int mapValue;

        void publishArray(int value) {
            arrayValue = value;
            arrayReady.countDown();
        }

        void publishMap(int value) {
            mapValue = value;
            mapReady.countDown();
        }

        int receiveArray() throws InterruptedException {
            await(arrayReady);
            return arrayValue;
        }

        int receiveMap() throws InterruptedException {
            await(mapReady);
            return mapValue;
        }

        private static void await(CountDownLatch ready)
                throws InterruptedException {
            if (!ready.await(FixedOrderRpcFixtureSupport.TIMEOUT_MILLIS,
                    TimeUnit.MILLISECONDS)) {
                throw new IllegalStateException("RPC timed out");
            }
        }
    }

    public static final class ImpossibleCompoundContainerException
            extends RuntimeException {
        ImpossibleCompoundContainerException(int arrayValue, int mapValue) {
            super("compound container target reached: " + arrayValue
                    + ", " + mapValue);
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
            super("compound-array-producer", start);
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

    static final class MapProducerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final MapProducer producer;
        private final RpcBus bus;
        private final FixedOrderRpcFixtureSupport.ProducerGate gate;

        MapProducerThread(CountDownLatch start, MapProducer producer,
                          RpcBus bus,
                          FixedOrderRpcFixtureSupport.ProducerGate gate) {
            super("compound-map-producer", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishMap(producer.compute());
        }
    }

    static final class ConsumerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final RpcBus bus;

        ConsumerThread(CountDownLatch start, RpcBus bus) {
            super("compound-container-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int arrayValue = bus.receiveArray();
            int mapValue = bus.receiveMap();
            int gap = mapValue - arrayValue;
            if ((arrayValue < 0 && gap > 0)
                    || (mapValue < 0 && arrayValue >= 0)) {
                return;
            }
            if ((arrayValue > mapValue && arrayValue >= 0 && gap < 0)
                    || ((arrayValue + mapValue == 7
                    || arrayValue + mapValue == 9)
                    && gap > 3 && arrayValue <= mapValue)) {
                throw new @CausynthExceptionTarget(
                        "tricky-compound-container-guard")
                        ImpossibleCompoundContainerException(
                                arrayValue, mapValue);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <arrayInput> <mapInput>");
        }
        Boolean arrayInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[0]);
        Boolean mapInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[1]);
        CountDownLatch start = new CountDownLatch(1);
        FixedOrderRpcFixtureSupport.ProducerGate gate =
                new FixedOrderRpcFixtureSupport.ProducerGate();
        RpcBus bus = new RpcBus();
        ArrayProducerThread array = new ArrayProducerThread(start,
                new ArrayProducer(arrayInput), bus, gate);
        MapProducerThread map = new MapProducerThread(start,
                new MapProducer(mapInput), bus, gate);
        ConsumerThread consumer = new ConsumerThread(start, bus);
        Throwable failure = FixedOrderRpcFixtureSupport.run(
                start, array, map, consumer);
        System.out.println("{\"kind\":\"TRICKY_COMPOUND_CONTAINER\","
                + "\"arrayValue\":" + bus.arrayValue + ','
                + "\"mapValue\":" + bus.mapValue + '}');
        FixedOrderRpcFixtureSupport.propagate(failure);
    }
}
