package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public final class Continuations {
    private static final String RUNTIME = Continuations.class.getPackage()
            .getName() + ".";

    private Continuations() {
    }

    interface Carrier {
    }

    public static <T, U> BiConsumer<T, U> carry(BiConsumer<T, U> action) {
        return action == null ? null : new CarriedBiConsumer<T, U>(action);
    }

    public static <T, U, R> BiFunction<T, U, R> carry(
            BiFunction<T, U, R> action) {
        return action == null ? null : new CarriedBiFunction<T, U, R>(action);
    }

    public static <T, R> Function<T, R> carry(Function<T, R> action) {
        return action == null ? null : new CarriedFunction<T, R>(action);
    }

    public static <T> Consumer<T> carry(Consumer<T> action) {
        return action == null ? null : new CarriedConsumer<T>(action);
    }

    public static Runnable carry(Runnable action) {
        return action == null ? null : new CarriedRunnable(action);
    }

    static String registrant() {
        StackTraceElement[] stack = new Throwable().getStackTrace();
        int at = 0;
        while (at < stack.length
                && stack[at].getClassName().startsWith(RUNTIME)) {
            at++;
        }
        if (at >= stack.length) return "";
        String registering = outer(stack[at].getClassName());
        for (int index = at + 1; index < stack.length; index++) {
            String owner = stack[index].getClassName();
            if (!outer(owner).equals(registering)
                    && !owner.startsWith(RUNTIME)
                    && !owner.startsWith("java.")
                    && !owner.startsWith("sun.")) {
                return JvmNames.stable(owner) + "."
                        + stack[index].getMethodName();
            }
        }
        return "";
    }

    private static String outer(String className) {
        int nested = className.indexOf('$');
        return nested < 0 ? className : className.substring(0, nested);
    }

    private static <R> R claimed(Object carrier, Supplier<R> work) {
        boolean paused = paused();
        long claim;
        try {
            claim = RowRuntime.claimContinuation(carrier);
        } finally {
            resumed(paused);
        }
        try {
            return work.get();
        } finally {
            paused = paused();
            try {
                RowRuntime.endClaim(claim);
            } finally {
                resumed(paused);
            }
        }
    }

    private static boolean paused() {
        try {
            return ConcolicVmBroker.pauseEngineWork();
        } catch (RuntimeException unpaused) {
            return false;
        }
    }

    private static void resumed(boolean paused) {
        if (!paused) return;
        try {
            ConcolicVmBroker.resumeEngineWork();
        } catch (RuntimeException unresumed) {
            RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.DIAGNOSTIC,
                    "continuation claim", "the VM's propagation could not"
                            + " be resumed after a continuation's claim: "
                            + unresumed);
        }
    }

    private static final class CarriedBiConsumer<T, U>
            implements BiConsumer<T, U>, Carrier {
        private final BiConsumer<T, U> action;

        private CarriedBiConsumer(BiConsumer<T, U> action) {
            this.action = action;
        }

        @Override
        public void accept(T value, U other) {
            claimed(this, () -> {
                action.accept(value, other);
                return null;
            });
        }
    }

    private static final class CarriedBiFunction<T, U, R>
            implements BiFunction<T, U, R>, Carrier {
        private final BiFunction<T, U, R> action;

        private CarriedBiFunction(BiFunction<T, U, R> action) {
            this.action = action;
        }

        @Override
        public R apply(T value, U other) {
            return claimed(this, () -> action.apply(value, other));
        }
    }

    private static final class CarriedFunction<T, R>
            implements Function<T, R>, Carrier {
        private final Function<T, R> action;

        private CarriedFunction(Function<T, R> action) {
            this.action = action;
        }

        @Override
        public R apply(T value) {
            return claimed(this, () -> action.apply(value));
        }
    }

    private static final class CarriedConsumer<T>
            implements Consumer<T>, Carrier {
        private final Consumer<T> action;

        private CarriedConsumer(Consumer<T> action) {
            this.action = action;
        }

        @Override
        public void accept(T value) {
            claimed(this, () -> {
                action.accept(value);
                return null;
            });
        }
    }

    private static final class CarriedRunnable implements Runnable, Carrier {
        private final Runnable action;

        private CarriedRunnable(Runnable action) {
            this.action = action;
        }

        @Override
        public void run() {
            claimed(this, () -> {
                action.run();
                return null;
            });
        }
    }
}
