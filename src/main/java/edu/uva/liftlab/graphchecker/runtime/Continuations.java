package edu.uva.liftlab.graphchecker.runtime;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public final class Continuations {
    private Continuations() {
    }

    public static <T, U> BiConsumer<T, U> carry(BiConsumer<T, U> action) {
        return action == null ? null : new BiConsumer<T, U>() {
            @Override
            public void accept(T value, U other) {
                claimed(this, () -> {
                    action.accept(value, other);
                    return null;
                });
            }
        };
    }

    public static <T, U, R> BiFunction<T, U, R> carry(
            BiFunction<T, U, R> action) {
        return action == null ? null : new BiFunction<T, U, R>() {
            @Override
            public R apply(T value, U other) {
                return claimed(this, () -> action.apply(value, other));
            }
        };
    }

    public static <T, R> Function<T, R> carry(Function<T, R> action) {
        return action == null ? null : new Function<T, R>() {
            @Override
            public R apply(T value) {
                return claimed(this, () -> action.apply(value));
            }
        };
    }

    public static <T> Consumer<T> carry(Consumer<T> action) {
        return action == null ? null : new Consumer<T>() {
            @Override
            public void accept(T value) {
                claimed(this, () -> {
                    action.accept(value);
                    return null;
                });
            }
        };
    }

    public static Runnable carry(Runnable action) {
        return action == null ? null : new Runnable() {
            @Override
            public void run() {
                claimed(this, () -> {
                    action.run();
                    return null;
                });
            }
        };
    }

    private static <R> R claimed(Object carrier, Supplier<R> work) {
        boolean paused = ConcolicVmBroker.pauseEngineWork();
        long claim;
        try {
            claim = RowRuntime.claimContinuation(carrier);
        } finally {
            if (paused) ConcolicVmBroker.resumeEngineWork();
        }
        try {
            return work.get();
        } finally {
            paused = ConcolicVmBroker.pauseEngineWork();
            try {
                RowRuntime.endClaim(claim);
            } finally {
                if (paused) ConcolicVmBroker.resumeEngineWork();
            }
        }
    }
}
