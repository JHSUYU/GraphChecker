package edu.uva.liftlab.graphchecker.contract;

public final class Clock extends Value {
    public static final String WALL = "currentTimeMillis";
    public static final String MONOTONIC = "nanoTime";

    private final long nanos;
    private final String source;

    private Clock(long nanos, String source) {
        this.nanos = nanos;
        this.source = source;
    }

    public static Clock of(long nanos, String source) {
        if (nanos <= 0L) {
            throw new IllegalArgumentException("a clock's tick is a positive "
                    + "number of nanoseconds: " + nanos);
        }
        String stated = source == null ? "" : source;
        if (!stated.isEmpty() && !WALL.equals(stated)
                && !MONOTONIC.equals(stated)) {
            throw new IllegalArgumentException("a clock's source is a JVM "
                    + "clock: " + stated);
        }
        return new Clock(nanos, stated);
    }

    public long nanos() {
        return nanos;
    }

    public String source() {
        return source;
    }

    public boolean same(Clock other) {
        return other != null && !source.isEmpty()
                && source.equals(other.source) && nanos == other.nanos;
    }

    @Override
    Object[] parts() {
        return new Object[] {nanos, source};
    }

    @Override
    public String toString() {
        return (source.isEmpty() ? "?" : source) + "/" + nanos;
    }
}
