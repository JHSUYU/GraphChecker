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

/** Generated stress round 5, case 15: SAT. */
public final class StressRoundFixture15 {
    private StressRoundFixture15() {
    }


    static final class AState {
        boolean enabled;
        int result;

        AState(Boolean input) {
            enabled = input.booleanValue();
            result = -21;
        }
    }

    static final class AProducer {
        AState state;

        AProducer(Boolean input) {
            state = new AState(input);
        }

        int compute() {
            update(state);
            return finish(state);
        }

        private static void update(AState state) {
            if (state.enabled) {
                state.result = 25;
            } else {
                state.result = -21;
            }
        }

        private static int finish(AState state) {
            if (state.result > 0 && state.enabled) {
                return state.result;
            }
            return -21;
        }
    }


    static final class BMapHolder {
        Map<Integer, Integer> values = new LinkedHashMap<>();
        BMapHolder(boolean enabled) {
            values.put(Integer.valueOf(7),
                    Integer.valueOf(enabled ? 42 : -38));
        }
    }

    static final class BProducer {
        boolean enabled;
        BMapHolder[] holders;
        BProducer(Boolean input) {
            enabled = input.booleanValue();
            holders = new BMapHolder[]{
                    new BMapHolder(!enabled),
                    new BMapHolder(enabled)
            };
        }
        int compute() {
            return resolve(holders[1], enabled);
        }
        private static int resolve(BMapHolder input, boolean enabled) {
            Integer selected =
                    input.values.get(Integer.valueOf(7));
            if (enabled && selected.intValue() == 42) {
                return selected.intValue();
            }
            return -38;
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
            if (a == 25 && b == 42) {
                throw new @CausynthExceptionTarget("stress-r05-c15")
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
                + "\"round\":5,\"case\":15}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
