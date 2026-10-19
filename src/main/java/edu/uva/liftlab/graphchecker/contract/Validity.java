package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.math.BigInteger;

public final class Validity extends Value {
    public static final String MIN = "validMin";
    public static final String MAX = "validMax";
    public static final String BY = "validBy";
    public static final Validity ANY = new Validity(null, null, "");

    private final BigInteger min;
    private final BigInteger max;
    private final String by;

    private Validity(BigInteger min, BigInteger max, String by) {
        this.min = min;
        this.max = max;
        this.by = by == null ? "" : by.trim();
    }

    public static Validity of(BigInteger min, BigInteger max, String by) {
        return min == null && max == null ? ANY : new Validity(min, max, by);
    }

    public static Validity read(JsonObject row) {
        return of(integral(row, MIN), integral(row, MAX), text(row, BY));
    }

    public void write(JsonObject row) {
        if (min != null) row.addProperty(MIN, min.toString());
        if (max != null) row.addProperty(MAX, max.toString());
        if (!by.isEmpty()) row.addProperty(BY, by);
    }

    public Validity and(Validity other) {
        if (other == null || other == ANY) return this;
        if (this == ANY) return other;
        BigInteger low = min == null ? other.min
                : other.min == null ? min : min.max(other.min);
        BigInteger high = max == null ? other.max
                : other.max == null ? max : max.min(other.max);
        return of(low, high, joined(by, other.by));
    }

    public Validity or(Validity other) {
        if (other == null || this == ANY || other == ANY) return ANY;
        BigInteger low = min == null || other.min == null ? null
                : min.min(other.min);
        BigInteger high = max == null || other.max == null ? null
                : max.max(other.max);
        return of(low, high, joined(by, other.by));
    }

    public boolean admits(BigInteger value) {
        return value != null && clip(value).equals(value);
    }

    public BigInteger clip(BigInteger value) {
        if (value == null) return null;
        if (min != null && value.compareTo(min) < 0) return min;
        if (max != null && value.compareTo(max) > 0) return max;
        return value;
    }

    public BigInteger min() {
        return min;
    }

    public BigInteger max() {
        return max;
    }

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
