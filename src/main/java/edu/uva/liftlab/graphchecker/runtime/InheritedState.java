package edu.uva.liftlab.graphchecker.runtime;

abstract class InheritedState<T> extends InheritableThreadLocal<T> {
    @Override
    protected final T childValue(T parent) {
        boolean paused = ConcolicVmBroker.pauseEngineWork();
        try {
            return inherit(parent);
        } finally {
            if (paused) ConcolicVmBroker.resumeEngineWork();
        }
    }

    protected abstract T inherit(T parent);
}
