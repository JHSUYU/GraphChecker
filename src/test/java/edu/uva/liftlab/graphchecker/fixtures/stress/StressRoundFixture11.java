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

/** Generated stress round 5, case 11: SAT. */
public final class StressRoundFixture11 {
    private StressRoundFixture11() {
    }


    static final class AAliasNode {
        boolean enabled;
        int value;
        AAliasNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class AProducer {
        AAliasNode primary;
        AAliasNode alias;
        AAliasNode decoy;
        AProducer(Boolean input) {
            boolean enabled = input.booleanValue();
            primary = new AAliasNode(enabled, enabled ? 21 : -17);
            alias = primary;
            decoy = new AAliasNode(!enabled, enabled ? -17 : 21);
        }
        int compute() {
            AAliasNode selected = alias;
            if (selected == primary && selected != decoy
                    && selected.enabled) {
                return selected.value;
            }
            return -17;
        }
    }


    static final class BIterNode {
        boolean enabled;
        int value;
        BIterNode(boolean enabled, int value) {
            this.enabled = enabled;
            this.value = value;
        }
    }

    static final class BProducer {
        List<BIterNode> nodes = new ArrayList<>();
        BProducer(Boolean input) {
            boolean enabled = input.booleanValue();
            nodes.add(new BIterNode(!enabled, -30));
            nodes.add(new BIterNode(enabled, enabled ? 34 : -30));
        }
        int compute() {
            Iterator<BIterNode> iterator = nodes.iterator();
            BIterNode decoy = iterator.next();
            BIterNode selected = iterator.next();
            if (selected.enabled && decoy != selected) {
                return selected.value;
            }
            return -30;
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
            boolean leftReady = a > -17 && a <= 21;
            boolean rightReady = b > -30 && b <= 34;
            if (leftReady && rightReady && a + b == 55) {
                throw new @CausynthExceptionTarget("stress-r05-c11")
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
                + "\"round\":5,\"case\":11}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
