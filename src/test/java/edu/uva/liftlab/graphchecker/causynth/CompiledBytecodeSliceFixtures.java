package edu.uva.liftlab.graphchecker.causynth;

import java.util.Map;

/**
 * Real javac bytecode for the writer/caller/mutation index.
 *
 * <p>Every other analyzer test assembles its Scene in memory, so none of them
 * covers the path where a writer, a backed-collection mutation and a caller
 * have to be recovered from a compiled class file: constant-pool field
 * resolution, javac's temporaries, and an interface invoke on a field-backed
 * map included.  The build compiles these fixtures, and
 * {@link CompiledBytecodeSliceTest} analyzes them as a Soot process directory,
 * which is the shape a workload module has.</p>
 */
final class CompiledBytecodeSliceFixtures {

    private CompiledBytecodeSliceFixtures() {
    }

    static final class Failure extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }

    static final class State {
        Map<String, String> values;
    }

    static final class Writer {
        static void setValues(State state, Map<String, String> values) {
            state.values = values;
        }

        static void clearValues(State state) {
            state.values.clear();
        }
    }

    static final class Consumer {
        static void consume(State state) {
            Map<String, String> values = state.values;
            if (values == null) {
                throw new Failure();
            }
        }
    }

    static final class Caller {
        static void callConsume(State state) {
            Consumer.consume(state);
        }
    }
}
