package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
 * UNSAT container case joining a nested array leaf with an erased Map key.
 */
public final class NestedArrayMapKeyUnreachableThreeThreadWorkload {
    private NestedArrayMapKeyUnreachableThreeThreadWorkload() {
    }

    static final class Leaf {
        boolean enabled;
        int amount;

        Leaf(Boolean enabled, int amount) {
            this.enabled = enabled.booleanValue();
            this.amount = amount;
        }
    }

    static final class Node {
        Leaf state;

        Node(Boolean enabled, int amount) {
            state = new Leaf(enabled, amount);
        }
    }

    static final class ArrayProducer {
        Node[] nodes;

        ArrayProducer(Boolean enabled) {
            nodes = new Node[]{
                    new Node(Boolean.valueOf(!enabled.booleanValue()), 99),
                    new Node(enabled, 0)
            };
        }

        int compute() {
            Node selected = nodes[1];
            Node decoy = nodes[0];
            int amount = selected.state.amount;
            int selector = selected.state.enabled ? 2 : 1;
            if ((amount < 0 && decoy.state.amount > selector)
                    || (amount == -1 && !selected.state.enabled)) {
                amount = 0;
            }
            if ((amount > 3 && selector <= 2)
                    || (amount == 3 && decoy.state.enabled)) {
                amount = 3;
            }
            int total = 0;
            for (int index = 0; index < 4; index++) {
                if (((index == 0 || index == 2)
                        && selected.state.enabled)
                        || (index == 3
                        && decoy.state.amount > 50)) {
                    total += amount + 1;
                } else if ((index == 1 && !selected.state.enabled)
                        || amount > selector) {
                    total += amount;
                } else {
                    total += amount - 1;
                }
            }
            if (selected.state.enabled && total < 8
                    && decoy.state.amount + selector > 50) {
                total += 4;
            }
            return total + 1;
        }
    }

    static final class MapProducer {
        Map<Integer, Node> values;

        MapProducer(Boolean enabled) {
            values = new LinkedHashMap<>();
            values.put(Integer.valueOf(7), new Node(enabled, 0));
        }

        int compute() {
            Iterator<Map.Entry<Integer, Node>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, Node> entry = iterator.next();
            Integer key = entry.getKey();
            Node selected = entry.getValue();
            int amount = selected.state.amount;
            int selector = selected.state.enabled ? 2 : 1;
            if ((amount < 0 && key.intValue() == 7)
                    || (amount == -1 && !selected.state.enabled)) {
                amount = 0;
            }
            if ((amount > 3 && selector > 0)
                    || (amount == 3 && key.intValue() < 0)) {
                amount = 3;
            }
            int total = 0;
            for (int index = 0; index < 4; index++) {
                if ((index < 2 && selected.state.enabled)
                        || (index == 3 && key.intValue() == 7)) {
                    total += amount + selector;
                } else if (((index == 0 || index == 2)
                        && !selected.state.enabled)
                        || amount > selector) {
                    total += amount;
                } else {
                    total += amount - selector;
                }
            }
            if (selected.state.enabled && total > 8
                    && key.intValue() - selector > 0) {
                total -= 4;
            }
            return total + key.intValue() + 2;
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

    public static final class ImpossibleNestedContainerException
            extends RuntimeException {
        ImpossibleNestedContainerException(int arrayValue, int mapValue) {
            super("array exceeded map bound: " + arrayValue + ", "
                    + mapValue);
        }
    }

    static final class ArrayProducerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final ArrayProducer arrayProducer;
        private final RpcBus bus;
        private final FixedOrderRpcFixtureSupport.ProducerGate gate;

        ArrayProducerThread(CountDownLatch start, RpcBus bus,
                            FixedOrderRpcFixtureSupport.ProducerGate gate,
                            ArrayProducer arrayProducer) {
            super("nested-array-producer", start);
            this.bus = bus;
            this.gate = gate;
            this.arrayProducer = arrayProducer;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishArray(arrayProducer.compute());
        }
    }

    static final class MapProducerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final MapProducer mapProducer;
        private final RpcBus bus;
        private final FixedOrderRpcFixtureSupport.ProducerGate gate;

        MapProducerThread(CountDownLatch start, RpcBus bus,
                          FixedOrderRpcFixtureSupport.ProducerGate gate,
                          MapProducer mapProducer) {
            super("nested-map-producer", start);
            this.bus = bus;
            this.gate = gate;
            this.mapProducer = mapProducer;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishMap(mapProducer.compute());
        }
    }

    static final class ConsumerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final RpcBus bus;

        ConsumerThread(CountDownLatch start, RpcBus bus) {
            super("nested-container-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int arrayValue = bus.receiveArray();
            int mapValue = bus.receiveMap();
            int difference = arrayValue - mapValue;
            if ((arrayValue > mapValue + 4
                    && mapValue >= 7 && difference > 4)
                    || (difference > 8
                    && arrayValue + mapValue < 0)) {
                throw new @CausynthExceptionTarget(
                        "tricky-nested-array-map-key")
                        ImpossibleNestedContainerException(
                                arrayValue, mapValue);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        requireInputs(args);
        Boolean arrayInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[0]);
        Boolean mapInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[1]);
        CountDownLatch start = new CountDownLatch(1);
        FixedOrderRpcFixtureSupport.ProducerGate gate =
                new FixedOrderRpcFixtureSupport.ProducerGate();
        RpcBus bus = new RpcBus();
        ArrayProducerThread array = new ArrayProducerThread(
                start, bus, gate, new ArrayProducer(arrayInput));
        MapProducerThread map = new MapProducerThread(
                start, bus, gate, new MapProducer(mapInput));
        ConsumerThread consumer = new ConsumerThread(start, bus);
        Throwable failure = FixedOrderRpcFixtureSupport.run(
                start, array, map, consumer);
        System.out.println("{\"kind\":\"TRICKY_NESTED_ARRAY_MAP_KEY\","
                + "\"arrayValue\":" + bus.arrayValue + ','
                + "\"mapValue\":" + bus.mapValue + '}');
        FixedOrderRpcFixtureSupport.propagate(failure);
    }

    private static void requireInputs(String[] args) {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <arrayInput> <mapInput>");
        }
    }
}
