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

/** Generated stress round 5, case 8: UNSAT. */
public final class StressRoundFixture08 {
    private StressRoundFixture08() {
    }


    static final class ABox {
        Boolean enabled;
        Integer disabledValue = Integer.valueOf(-14);
        Integer enabledValue = Integer.valueOf(18);
        ABox(Boolean input) { enabled = input; }
    }

    static final class AProducer {
        ABox box;
        AProducer(Boolean input) { box = new ABox(input); }
        int compute() {
            Integer selected = box.enabled.booleanValue()
                    ? box.enabledValue : box.disabledValue;
            return selected.intValue();
        }
    }


    static final class BMapNode {
        boolean enabled;
        int value;
        BMapNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class BProducer {
        Map<Integer, BMapNode> values = new LinkedHashMap<>();
        BProducer(Boolean input) {
            boolean enabled = input.booleanValue();
            values.put(Integer.valueOf(7),
                    new BMapNode(enabled, enabled ? 28 : -24));
            values.put(Integer.valueOf(9),
                    new BMapNode(!enabled, enabled ? -24 : 28));
        }
        int compute() {
            Iterator<Map.Entry<Integer, BMapNode>> iterator =
                    values.entrySet().iterator();
            Map.Entry<Integer, BMapNode> entry = iterator.next();
            Integer key = entry.getKey();
            BMapNode node = entry.getValue();
            if (key.intValue() == 7 && node.enabled) {
                return node.value;
            }
            return -24;
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
            int left = a < 0 ? -a : a;
            int right = b < 0 ? -b : b;
            if (left == 18 && right == 28
                    && left - right == -9) {
                throw new @CausynthExceptionTarget("stress-r05-c08")
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
                + "\"round\":5,\"case\":8}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
