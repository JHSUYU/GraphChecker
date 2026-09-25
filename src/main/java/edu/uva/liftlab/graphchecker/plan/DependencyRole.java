package edu.uva.liftlab.graphchecker.plan;

/**
 * The one role a region port can have: it carries a value the solver may move.
 *
 * <p>{@link #normalize} refuses every other spelling, including the deleted
 * {@code CONCRETE_STRUCTURE_CARRIER}: older plan artifacts are not supported
 * input.</p>
 */
public final class DependencyRole {
    public static final String VALUE_FRONTIER = "VALUE_FRONTIER";

    private DependencyRole() {
    }

    /** Fail closed: a missing or misspelled role is unreadable, not a default.
     */
    public static String normalize(Object value) {
        if (value == null) {
            throw new IllegalArgumentException("dependencyRole is required");
        }
        String encoded = String.valueOf(value);
        if (encoded.length() >= 2 && encoded.startsWith("\"")
                && encoded.endsWith("\"")) {
            encoded = encoded.substring(1, encoded.length() - 1);
        }
        encoded = encoded.trim();
        if (VALUE_FRONTIER.equals(encoded)) {
            return encoded;
        }
        throw new IllegalArgumentException(
                "unsupported dependencyRole: " + encoded);
    }

    public static boolean valueFrontier(Object value) {
        return VALUE_FRONTIER.equals(normalize(value));
    }
}
