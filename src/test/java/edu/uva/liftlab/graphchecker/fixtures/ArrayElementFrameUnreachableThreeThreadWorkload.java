package edu.uva.liftlab.graphchecker.fixtures;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
 * UNSAT case with repeated fixed-loop writes to distinct array elements.
 */
public final class ArrayElementFrameUnreachableThreeThreadWorkload {
    private ArrayElementFrameUnreachableThreeThreadWorkload() {
    }

    static final class Cell {
        int value;

        Cell(int value) {
            this.value = value;
        }
    }

    static final class ArrayProducer {
        boolean enabled;
        Cell[] cells;

        ArrayProducer(Boolean enabled) {
            this.enabled = enabled.booleanValue();
            cells = new Cell[]{new Cell(20), new Cell(0)};
        }

        int compute() {
            int base = cells[1].value;
            int peer = cells[0].value;
            if ((base < 0 && peer > 10)
                    || (base == -1 && !enabled)) {
                base = 0;
            }
            if ((base > 3 && (enabled || peer >= 20))
                    || (base == 4 && peer < 0)) {
                base = 3;
            }
            for (int index = 0; index < 4; index++) {
                if (((index == 0 || index == 2)
                        && (enabled || peer > 10))
                        || (index == 2 && base == 0)) {
                    cells[0].value = base + index;
                } else if ((index == 1 && !enabled)
                        || index == 3 || base >= 0) {
                    cells[1].value = base + index;
                } else {
                    cells[1].value = peer - index;
                }
            }
            if (enabled && cells[1].value < 5
                    && cells[0].value <= peer) {
                cells[0].value++;
            }
            return cells[1].value;
        }
    }

    static final class MapProducer {
        Map<Integer, Cell> values;
        boolean enabled;

        MapProducer(Boolean enabled) {
            this.enabled = enabled.booleanValue();
            values = new LinkedHashMap<>();
            values.put(Integer.valueOf(5), new Cell(0));
        }

        int compute() {
            Iterator<Map.Entry<Integer, Cell>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, Cell> entry = iterator.next();
            int value = entry.getValue().value;
            int key = entry.getKey().intValue();
            if ((value < 0 && key > 0)
                    || (value == -1 && !enabled)) {
                value = 0;
            }
            if ((value > 3 && (enabled || key == 5))
                    || (value == 4 && key < 0)) {
                value = 3;
            }
            int adjustment = 0;
            for (int index = 0; index < 4; index++) {
                if ((index == 0 && enabled)
                        || (index == 1 && !enabled)) {
                    adjustment++;
                } else if ((index == 2 && value > 1)
                        || (index == 3 && key < 0)) {
                    adjustment += 2;
                }
            }
            return value + key + 5 + adjustment;
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

    public static final class ImpossibleArrayFrameException
            extends RuntimeException {
        ImpossibleArrayFrameException(int arrayValue, int mapValue) {
            super("array frame exceeded map: " + arrayValue + ", "
                    + mapValue);
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
            super("frame-array-producer", start);
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
            super("frame-map-producer", start);
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
            super("frame-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int arrayValue = bus.receiveArray();
            int mapValue = bus.receiveMap();
            int gap = mapValue - arrayValue;
            if ((arrayValue >= mapValue
                    && arrayValue + mapValue < 30 && gap <= 0)
                    || (arrayValue > mapValue + 2
                    && (gap < -1 || mapValue >= 5))) {
                throw new @CausynthExceptionTarget(
                        "tricky-array-element-frame")
                        ImpossibleArrayFrameException(
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
        System.out.println("{\"kind\":\"TRICKY_ARRAY_FRAME\","
                + "\"arrayValue\":" + bus.arrayValue + ','
                + "\"mapValue\":" + bus.mapValue + '}');
        FixedOrderRpcFixtureSupport.propagate(failure);
    }
}
