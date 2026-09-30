package edu.uva.liftlab.graphchecker.contract;

/**
 * A clock a declared CLOCK root reads: the JVM clock it wraps and its tick.
 *
 * <p>ONE CLOCK is one JVM clock at one tick on one node ({@link #same}; the
 * node is the reader's): the rule COMPOSE orders a node's cells by
 * ({@code compose.Composer#clocks}) and a replay runs a plant on by
 * ({@code runtime.NodeClocks}).  A node reads more than one --
 * hdfs-11741's Balancer reads {@code Time.now()} (the wall clock) for its
 * keys and {@code Time.monotonicNow()} ({@code nanoTime}) for its SASL user,
 * both in milliseconds -- and a reading's value says nothing reliable about
 * which it came from.  {@code causynth.RootCatalog} reads the source off the
 * wrapper's body; a wrapper whose value mixes both states none, and is on no
 * clock's order.</p>
 */
public final class Clock extends Value {
    /** {@code System.currentTimeMillis()}. */
    public static final String WALL = "currentTimeMillis";
    /** {@code System.nanoTime()}. */
    public static final String MONOTONIC = "nanoTime";

    private final long nanos;
    private final String source;

    private Clock(long nanos, String source) {
        this.nanos = nanos;
        this.source = source;
    }

    /**
     * @param nanos  the nanoseconds one unit of a reading is (1 for {@code
     *               nanoTime}, 1,000,000 for {@code currentTimeMillis})
     * @param source {@link #WALL}, {@link #MONOTONIC}, or {@code ""} when
     *               nothing states which
     */
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

    /** The nanoseconds one unit of a reading is. */
    public long nanos() {
        return nanos;
    }

    /** The JVM clock it wraps, or {@code ""} when nothing states which. */
    public String source() {
        return source;
    }

    /** Whether two readings of one node read one clock: the same stated
     *  JVM clock at the same tick. */
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
