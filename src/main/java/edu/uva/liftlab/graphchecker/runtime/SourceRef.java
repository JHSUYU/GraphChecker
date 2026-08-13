package edu.uva.liftlab.graphchecker.runtime;

import java.util.Objects;

/** Stable logical source identity for one node/application lifecycle. */
public final class SourceRef {
    private final String kind;
    private final String role;
    private final String id;
    private final long epoch;
    private final String key;

    public SourceRef(String kind, String role, String id, long epoch) {
        this.kind = required("kind", kind);
        this.role = required("role", role);
        this.id = required("id", id);
        if (epoch < 0L) {
            throw new IllegalArgumentException("source epoch must be nonnegative");
        }
        this.epoch = epoch;
        this.key = this.id + "#epoch" + epoch;
    }

    public String kind() {
        return kind;
    }

    public String role() {
        return role;
    }

    public String id() {
        return id;
    }

    public long epoch() {
        return epoch;
    }

    public String key() {
        return key;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof SourceRef)) return false;
        SourceRef other = (SourceRef) value;
        return epoch == other.epoch
                && kind.equals(other.kind)
                && role.equals(other.role)
                && id.equals(other.id);
    }

    @Override
    public int hashCode() {
        return Objects.hash(kind, role, id, epoch);
    }

    @Override
    public String toString() {
        return key + "[" + kind + ":" + role + "]";
    }

    private static String required(String field, String value) {
        String normalized = value == null ? "" : value.trim();
        if (normalized.isEmpty()) {
            throw new IllegalArgumentException("source " + field
                    + " must be nonempty");
        }
        return normalized;
    }
}
