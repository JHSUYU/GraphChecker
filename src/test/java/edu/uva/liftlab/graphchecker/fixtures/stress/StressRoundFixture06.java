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

/** Generated stress round 5, case 6: UNSAT. */
public final class StressRoundFixture06 {
    private StressRoundFixture06() {
    }


    static final class ANestedNode {
        boolean enabled;
        int value;
        ANestedNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class ANestedPayload {
        Map<Integer, ANestedNode[]> values = new LinkedHashMap<>();
        ANestedPayload(Boolean input) {
            boolean enabled = input.booleanValue();
            values.put(Integer.valueOf(7), new ANestedNode[]{
                    new ANestedNode(!enabled, -12),
                    new ANestedNode(enabled, enabled ? 16 : -12)
            });
        }
    }

    static final class AProducer {
        ANestedPayload payload;
        AProducer(Boolean input) {
            payload = new ANestedPayload(input);
        }
        int compute() {
            return resolve(payload);
        }
        private static int resolve(ANestedPayload input) {
            ANestedNode[] row =
                    input.values.get(Integer.valueOf(7));
            ANestedNode selected = row[1];
            return selected.enabled ? selected.value : -12;
        }
    }


    static final class BArrayNode {
        boolean enabled;
        int value;
        BArrayNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class BArrayPayload {
        BArrayNode[] nodes;
        BArrayPayload(BArrayNode[] nodes) {
            this.nodes = nodes;
        }
    }

    static final class BProducer {
        BArrayPayload payload;
        BProducer(Boolean input) {
            boolean enabled = input.booleanValue();
            payload = new BArrayPayload(new BArrayNode[]{
                    new BArrayNode(!enabled, enabled ? -20 : 24),
                    new BArrayNode(enabled, enabled ? 24 : -20)
            });
        }
        int compute() {
            return select(payload.nodes[1]);
        }
        private static int select(BArrayNode selected) {
            if (selected.enabled) {
                return selected.value;
            }
            return -20;
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
            if (a > b && a <= b) {
                throw new @CausynthExceptionTarget("stress-r05-c06")
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
                + "\"round\":5,\"case\":6}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
