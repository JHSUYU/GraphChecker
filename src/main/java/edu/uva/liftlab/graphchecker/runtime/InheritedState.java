package edu.uva.liftlab.graphchecker.runtime;

/**
 * Engine state a new thread inherits from the thread that creates it: its
 * lineage, execution index and trace scope (IDENTITY §6).
 *
 * <p>{@code Thread.init} runs {@link #childValue} on the CREATOR, inside
 * whatever region the creator stands in, and no weave brackets a call the
 * JDK makes: unpaused, the concolic VM interprets this bookkeeping as the
 * program's own code.  Its lists over the creator's frame receivers (the
 * IPC handler thread, the namesystem) then name each receiver by a
 * container relation, every later read of any of their fields is symbolic,
 * and each store of such a value starts a tracked log: hdfs-17960 V1, where
 * a planned checkpoint handler created the image savers, read its own
 * {@code contextClassLoader} symbolically in {@code Thread.init}, and each
 * saver's {@code core-default.xml} parse recorded 23k rows the demand never
 * asked for.  So the child's value is computed with the VM's propagation
 * paused, as every hook the weave calls is: the child inherits its identity,
 * and the program's objects stay as they were.</p>
 */
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

    /**
     * The child's value, read off the creator's alone: no thread-local may be
     * touched while {@code Thread.init} copies the creator's map.
     */
    protected abstract T inherit(T parent);
}
