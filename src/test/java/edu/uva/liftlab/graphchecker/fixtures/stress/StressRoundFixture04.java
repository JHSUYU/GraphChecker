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

/** Generated stress round 5, case 4: UNSAT. */
public final class StressRoundFixture04 {
    private StressRoundFixture04() {
    }


    static final class AProducer {
        Set<Integer> values = new LinkedHashSet<>();
        AProducer(Boolean input) {
            boolean enabled = input.booleanValue();
            values.add(Integer.valueOf(enabled ? 14 : -10));
            values.add(Integer.valueOf(enabled ? -10 : 14));
        }
        int compute() {
            Iterator<Integer> iterator = values.iterator();
            Integer selected = iterator.next();
            if (values.size() == 2 && selected.intValue() > 0) {
                return selected.intValue();
            }
            return -10;
        }
    }


    static final class BFlag {
        boolean enabled;
        BFlag(Boolean input) { enabled = input.booleanValue(); }
    }

    static final class BState {
        BFlag flag;
        int disabledValue = -16;
        int enabledValue = 20;
        BState(Boolean input) { flag = new BFlag(input); }
    }

    static final class BEnvelope {
        BState state;
        BEnvelope(Boolean input) { state = new BState(input); }
    }

    static final class BProducer {
        BEnvelope envelope;
        BProducer(Boolean input) {
            envelope = new BEnvelope(input);
        }
        int compute() {
            return resolve(envelope);
        }
        private static int resolve(BEnvelope input) {
            BState state = input.state;
            if (state.flag.enabled) {
                return state.enabledValue;
            }
            return state.disabledValue;
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
            if (score == 38
                    && score != 38) {
                throw new @CausynthExceptionTarget("stress-r05-c04")
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
                + "\"round\":5,\"case\":4}");
        StressRpcFixtureSupport.propagate(failure);
    }
}
