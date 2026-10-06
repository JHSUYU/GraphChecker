package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.math.BigInteger;

/**
 * CONTRACT-SPEC §4: the values an integral configuration may hold by its own
 * validation (SYMBOL-SCOPE §4.3): a branch in its getter's wrapper or its
 * field's writer comparing the value with a literal, one arm of which only
 * throws, rejects the values that take it ({@code if (minR <= 0) throw}:
 * {@code minReplication >= 1}).  A cluster holding such a value refuses to
 * start, and a plant at the window's reads would never meet the check, so
 * no world moves the root there ({@link RootDomain#resolved}).  {@code min}
 * and {@code max} are absent where unbounded; {@code by} names the branches
 * ({@code <method>#u<unit>}, comma-joined).  Stated on the static
 * declaration, carried to the mint row ({@code validMin}, {@code validMax},
 * {@code validBy}).
 */
public final class Validity extends Value {
    public static final String MIN = "validMin";
    public static final String MAX = "validMax";
    public static final String BY = "validBy";
    /** No validation: every value. */
    public static final Validity ANY = new Validity(null, null, "");

    private final BigInteger min;
    private final BigInteger max;
    private final String by;

    private Validity(BigInteger min, BigInteger max, String by) {
        this.min = min;
        this.max = max;
        this.by = by == null ? "" : by.trim();
    }

    /** {@code min}/{@code max} null where unbounded. */
    public static Validity of(BigInteger min, BigInteger max, String by) {
        return min == null && max == null ? ANY : new Validity(min, max, by);
    }

    /** What a row states ({@link #MIN}, {@link #MAX}, {@link #BY}); an
     *  absent or non-integral bound is none. */
    public static Validity read(JsonObject row) {
        return of(integral(row, MIN), integral(row, MAX), text(row, BY));
    }

    /** States this on {@code row}; nothing where it is {@link #ANY}. */
    public void write(JsonObject row) {
        if (min != null) row.addProperty(MIN, min.toString());
        if (max != null) row.addProperty(MAX, max.toString());
        if (!by.isEmpty()) row.addProperty(BY, by);
    }

    /** Both validations at once: the values each admits. */
    public Validity and(Validity other) {
        if (other == null || other == ANY) return this;
        if (this == ANY) return other;
        BigInteger low = min == null ? other.min
                : other.min == null ? min : min.max(other.min);
        BigInteger high = max == null ? other.max
                : other.max == null ? max : max.min(other.max);
        return of(low, high, joined(by, other.by));
    }

    /** Either validation: the values one of them admits (two writers of one
     *  field, each validating its own store). */
    public Validity or(Validity other) {
        if (other == null || this == ANY || other == ANY) return ANY;
        BigInteger low = min == null || other.min == null ? null
                : min.min(other.min);
        BigInteger high = max == null || other.max == null ? null
                : max.max(other.max);
        return of(low, high, joined(by, other.by));
    }

    /** Whether {@code value} lies within these bounds. */
    public boolean admits(BigInteger value) {
        return value != null && clip(value).equals(value);
    }

    /** {@code value} raised or lowered into these bounds. */
    public BigInteger clip(BigInteger value) {
        if (value == null) return null;
        if (min != null && value.compareTo(min) < 0) return min;
        if (max != null && value.compareTo(max) > 0) return max;
        return value;
    }

    /** Whether no value is admitted: a lower bound above the upper. */
    public boolean empty() {
        return min != null && max != null && min.compareTo(max) > 0;
    }

    /** The lower bound, or null. */
    public BigInteger min() {
        return min;
    }

    /** The upper bound, or null. */
    public BigInteger max() {
        return max;
    }

    /** The branches that state it, or {@code ""}. */
    public String by() {
        return by;
    }

    private static String joined(String left, String right) {
        if (left.isEmpty()) return right;
        if (right.isEmpty() || left.equals(right)) return left;
        return left + "," + right;
    }

    private static BigInteger integral(JsonObject row, String member) {
        String stated = text(row, member);
        return stated.matches("-?[0-9]+") ? new BigInteger(stated) : null;
    }

    private static String text(JsonObject row, String member) {
        return row == null || !row.has(member) || row.get(member).isJsonNull()
                ? "" : row.get(member).getAsString().trim();
    }

    @Override
    Object[] parts() {
        return new Object[] {min, max, by};
    }

    @Override
    public String toString() {
        return "[" + (min == null ? "" : min) + "," + (max == null ? ""
                : max) + "]" + (by.isEmpty() ? "" : " by " + by);
    }
}
