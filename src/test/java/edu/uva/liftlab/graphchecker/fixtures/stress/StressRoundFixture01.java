package edu.uva.liftlab.graphchecker.fixtures.stress;

import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.CountDownLatch;

/** Generated stress round 5, case 1: SAT. */
public final class StressRoundFixture01 {
    private StressRoundFixture01() {
    }


    static final class AMutableNode {
        boolean enabled;
        int value;
        AMutableNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class AProducer {
        boolean enabled;
        Map<Integer, AMutableNode> values = new LinkedHashMap<>();
        AProducer(Boolean input) {
            enabled = input.booleanValue();
            values.put(Integer.valueOf(3),
                    new AMutableNode(false, -7));
            values.put(Integer.valueOf(7),
                    new AMutableNode(false, -7));
        }
        int compute() {
            if (enabled) {
                values.put(Integer.valueOf(7),
                        new AMutableNode(true, 11));
            } else {
                values.remove(Integer.valueOf(3));
            }
            AMutableNode selected = values.get(Integer.valueOf(7));
            return selected.enabled ? selected.value : -7;
        }
    }


    static final class BProducer {
        boolean enabled;
        int low = -10;
        int high = 14;

        BProducer(Boolean input) {
            enabled = input.booleanValue();
        }

        int compute() {
            int result = low;
            if (enabled) {
                result = high;
            }
            if (result > 0 && !enabled) {
                result = low;
            }
            return result;
        }
    }

    public static final class TargetReachedException
            extends RuntimeException {
        TargetReachedException(int a, int b) {
            super("stress target reached with a=" + a + ", b=" + b);
        }
    }

    static final class ProducerAThread
            extends StressRpcFixtureSupport.Worker {
        private final AProducer producer;
        private final StressRpcFixtureSupport.Bus bus;
        private final StressRpcFixtureSupport.ProducerGate gate;

        ProducerAThread(CountDownLatch start, AProducer producer,
                        StressRpcFixtureSupport.Bus bus,
                        StressRpcFixtureSupport.ProducerGate gate) {
            super("stress-a", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishA(producer.compute());
        }
    }

    static final class ProducerBThread
            extends StressRpcFixtureSupport.Worker {
        private final BProducer producer;
        private final StressRpcFixtureSupport.Bus bus;
        private final StressRpcFixtureSupport.ProducerGate gate;

        ProducerBThread(CountDownLatch start, BProducer producer,
                        StressRpcFixtureSupport.Bus bus,
                        StressRpcFixtureSupport.ProducerGate gate) {
            super("stress-b", start);
            this.producer = producer;
            this.bus = bus;
            this.gate = gate;
        }

        @Override
        void executeWorker() throws InterruptedException {
            gate.enterAndAwaitPeer();
            bus.publishB(producer.compute());
        }
    }

    static final class ConsumerThread
            extends StressRpcFixtureSupport.Worker {
        private final StressRpcFixtureSupport.Bus bus;

        ConsumerThread(CountDownLatch start,
                       StressRpcFixtureSupport.Bus bus) {
            super("stress-consumer", start);
            this.bus = bus;
        }

        @Override
        void executeWorker() throws InterruptedException {
            int a = bus.getRPCFromA();
            int b = bus.getRPCFromB();
            boolean leftReady = a > -7 && a <= 11;
            boolean rightReady = b > -10 && b <= 14;
            if (leftReady && rightReady && a + b == 25) {
                throw new @CausynthExceptionTarget("stress-r05-c01")
                        TargetReachedException(a, b);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            throw new IllegalArgumentException(
                    "expected: <producerAInput> <producerBInput>");
        }
        Boolean inputA = StressRpcFixtureSupport.parseBoolean(args[0]);
        Boolean inputB = StressRpcFixtureSupport.parseBoolean(args[1]);
        CountDownLatch start = new CountDownLatch(1);
        StressRpcFixtureSupport.ProducerGate gate =
                new StressRpcFixtureSupport.ProducerGate();
        StressRpcFixtureSupport.Bus bus =
                new StressRpcFixtureSupport.Bus();
        ProducerAThread producerA = new ProducerAThread(start,
                new AProducer(inputA), bus, gate);
        ProducerBThread producerB = new ProducerBThread(start,
                new BProducer(inputB), bus, gate);
        ConsumerThread consumer = new ConsumerThread(start, bus);
        Throwable failure = StressRpcFixtureSupport.run(
                start, producerA, producerB, consumer, bus);
        System.out.println("{\"kind\":\"STRESS_RESULT\","
                + "\"round\":5,\"case\":1}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
