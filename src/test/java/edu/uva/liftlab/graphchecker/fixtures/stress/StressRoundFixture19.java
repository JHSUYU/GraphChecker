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

/** Generated stress round 5, case 19: SAT. */
public final class StressRoundFixture19 {
    private StressRoundFixture19() {
    }


    static final class AProducer {
        boolean enabled;
        int[] values;
        AProducer(Boolean input) {
            enabled = input.booleanValue();
            values = enabled
                    ? new int[]{1, 2, 3, 4}
                    : new int[]{-1, -2, -3, -4};
        }
        int compute() {
            int sum = 0;
            for (int index = 0; index < 4; index++) {
                sum += values[index];
            }
            if (enabled && sum == 10) {
                return 29;
            }
            return -25;
        }
    }


    static final class BAliasNode {
        boolean enabled;
        int value;
        BAliasNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class BProducer {
        BAliasNode primary;
        BAliasNode alias;
        BAliasNode decoy;
        BProducer(Boolean input) {
            boolean enabled = input.booleanValue();
            primary = new BAliasNode(enabled, enabled ? 50 : -46);
            alias = primary;
            decoy = new BAliasNode(!enabled, enabled ? -46 : 50);
        }
        int compute() {
            BAliasNode selected = alias;
            if (selected == primary && selected != decoy
                    && selected.enabled) {
                return selected.value;
            }
            return -46;
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
            if (a > 0 && b > 0 && score == 83) {
                throw new @CausynthExceptionTarget("stress-r05-c19")
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
                + "\"round\":5,\"case\":19}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
