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

/** Generated stress round 5, case 14: UNSAT. */
public final class StressRoundFixture14 {
    private StressRoundFixture14() {
    }


    static final class AProducer {
        boolean enabled;
        int left;
        int right = 2;

        AProducer(Boolean input) {
            enabled = input.booleanValue();
            left = enabled ? 1 : 3;
        }

        int compute() {
            boolean ordered = (enabled && left < right)
                    || (!enabled && left > right);
            if (ordered && enabled) {
                return 24;
            }
            if (ordered || left == right + 1) {
                return -20;
            }
            return -20;
        }
    }


    static final class BNestedNode {
        boolean enabled;
        int value;
        BNestedNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class BNestedPayload {
        Map<Integer, BNestedNode[]> values = new LinkedHashMap<>();
        BNestedPayload(Boolean input) {
            boolean enabled = input.booleanValue();
            values.put(Integer.valueOf(7), new BNestedNode[]{
                    new BNestedNode(!enabled, -36),
                    new BNestedNode(enabled, enabled ? 40 : -36)
            });
        }
    }

    static final class BProducer {
        BNestedPayload payload;
        BProducer(Boolean input) {
            payload = new BNestedPayload(input);
        }
        int compute() {
            return resolve(payload);
        }
        private static int resolve(BNestedPayload input) {
            BNestedNode[] row =
                    input.values.get(Integer.valueOf(7));
            BNestedNode selected = row[1];
            return selected.enabled ? selected.value : -36;
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
            int score = a + b;
            for (int index = 0; index < 4; index++) {
                score++;
            }
            if (score == 68
                    && score != 68) {
                throw new @CausynthExceptionTarget("stress-r05-c14")
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
                + "\"round\":5,\"case\":14}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
