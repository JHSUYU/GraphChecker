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

/** Generated stress round 5, case 5: SAT. */
public final class StressRoundFixture05 {
    private StressRoundFixture05() {
    }


    static final class AProducer {
        Queue<Integer> values = new ArrayDeque<>();
        boolean enabled;
        AProducer(Boolean input) {
            enabled = input.booleanValue();
            values.offer(Integer.valueOf(enabled ? 15 : -11));
            values.offer(Integer.valueOf(enabled ? -11 : 15));
        }
        int compute() {
            Integer first = values.peek();
            if (enabled) {
                Integer removed = values.poll();
                return removed.intValue();
            }
            return first.intValue();
        }
    }


    static class BBase {
        int value = -18;
    }

    static final class BDerived extends BBase {
        boolean enabled;
        int value;
        BDerived(Boolean input) {
            enabled = input.booleanValue();
            super.value = enabled ? 22 : -18;
            value = enabled ? -18 : 22;
        }
    }

    static final class BProducer {
        BBase base;
        BDerived derived;
        BProducer(Boolean input) {
            derived = new BDerived(input);
            base = derived;
        }
        int compute() {
            return resolve(base, derived);
        }
        private static int resolve(BBase inheritedView,
                                   BDerived concreteView) {
            int inheritedValue = inheritedView.value;
            int hiddenValue = concreteView.value;
            if (concreteView.enabled
                    && inheritedView == concreteView
                    && hiddenValue == -18) {
                return inheritedValue;
            }
            return -18;
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
            if (a == 15 && b == 22) {
                throw new @CausynthExceptionTarget("stress-r05-c05")
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
                + "\"round\":5,\"case\":5}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
