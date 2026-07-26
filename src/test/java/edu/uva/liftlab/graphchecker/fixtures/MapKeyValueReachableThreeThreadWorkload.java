package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
 * SAT case combining an erased Map key with nested value fields.
 */
public final class MapKeyValueReachableThreeThreadWorkload {
    private MapKeyValueReachableThreeThreadWorkload() {
    }

    static final class Metrics {
        int left;
        int right;

        Metrics(int left, int right) {
            this.left = left;
            this.right = right;
        }
    }

    static final class ValueNode {
        boolean enabled;
        Metrics metrics;

        ValueNode(Boolean enabled, int left, int right) {
            this.enabled = enabled.booleanValue();
            metrics = new Metrics(left, right);
        }
    }

    static final class MapProducer {
        Map<Integer, ValueNode> values;

        MapProducer(Boolean enabled) {
            values = new LinkedHashMap<>();
            values.put(Integer.valueOf(7),
                    new ValueNode(enabled, 0, 0));
        }

        int compute() {
            Iterator<Map.Entry<Integer, ValueNode>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, ValueNode> entry = iterator.next();
            Integer key = entry.getKey();
            ValueNode value = entry.getValue();
            int left = bounded(value.metrics.left);
            int right = bounded(value.metrics.right);
            if (value.enabled || left + right > 3) {
                return key.intValue() + left + right;
            }
            return key.intValue() - left;
        }

        private static int bounded(int value) {
            if (value < 0) {
                return 0;
            }
            if (value > 4) {
                return 4;
            }
            return value;
        }
    }

    static final class ArrayProducer {
        ValueNode[] nodes;

        ArrayProducer(Boolean enabled) {
            nodes = new ValueNode[]{
                    new ValueNode(Boolean.valueOf(
                            !enabled.booleanValue()), 20, 20),
                    new ValueNode(enabled, 0, 0)
            };
        }

        int compute() {
            ValueNode node = nodes[1];
            int score = node.metrics.left;
            if (score < 0) {
                score = 0;
            }
            if (score > 4) {
                score = 4;
            }
            if (node.enabled) {
                return score + 3;
            }
            return score + 10;
        }
    }

    static final class RpcBus {
        private final CountDownLatch mapReady = new CountDownLatch(1);
        private final CountDownLatch arrayReady = new CountDownLatch(1);
        volatile int mapValue;
        volatile int arrayValue;

        void publishMap(int value) {
            mapValue = value;
            mapReady.countDown();
        }

        void publishArray(int value) {
            arrayValue = value;
            arrayReady.countDown();
        }

        int receiveMap() throws InterruptedException {
            await(mapReady);
            return mapValue;
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

    public static final class MapKeyValueBugException
            extends RuntimeException {
        MapKeyValueBugException(int mapValue, int arrayValue) {
            super("map key/value target reached: " + mapValue + ", "
                    + arrayValue);
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
            super("key-value-map-producer", start);
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

    static final class ArrayProducerThread
            extends FixedOrderRpcFixtureSupport.Worker {
        private final ArrayProducer producer;
        private final RpcBus bus;
        private final FixedOrderRpcFixtureSupport.ProducerGate gate;

        ArrayProducerThread(CountDownLatch start, ArrayProducer producer,
                            RpcBus bus,
                            FixedOrderRpcFixtureSupport.ProducerGate gate) {
            super("key-value-array-producer", start);
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
            super("key-value-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int mapValue = bus.receiveMap();
            int arrayValue = bus.receiveArray();
            if (mapValue >= 3 && mapValue <= 15
                    && ((mapValue > arrayValue && arrayValue < 8)
                    || (arrayValue == 10 && mapValue == 8))) {
                throw new @CausynthExceptionTarget(
                        "tricky-map-key-value")
                        MapKeyValueBugException(mapValue, arrayValue);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <mapInput> <arrayInput>");
        }
        Boolean mapInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[0]);
        Boolean arrayInput =
                FixedOrderRpcFixtureSupport.parseBoolean(args[1]);
        CountDownLatch start = new CountDownLatch(1);
        FixedOrderRpcFixtureSupport.ProducerGate gate =
                new FixedOrderRpcFixtureSupport.ProducerGate();
        RpcBus bus = new RpcBus();
        MapProducerThread map = new MapProducerThread(start,
                new MapProducer(mapInput), bus, gate);
        ArrayProducerThread array = new ArrayProducerThread(start,
                new ArrayProducer(arrayInput), bus, gate);
        ConsumerThread consumer = new ConsumerThread(start, bus);
        Throwable failure = FixedOrderRpcFixtureSupport.run(
                start, map, array, consumer);
        System.out.println("{\"kind\":\"TRICKY_MAP_KEY_VALUE\","
                + "\"mapValue\":" + bus.mapValue + ','
                + "\"arrayValue\":" + bus.arrayValue + '}');
        FixedOrderRpcFixtureSupport.propagate(failure);
    }
}
