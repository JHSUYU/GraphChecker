package edu.uva.liftlab.graphchecker.plan;

/**
 * The one role a region port can have: it carries a value the solver may
 * move.
 *
 * <p>There used to be a second, {@code CONCRETE_STRUCTURE_CARRIER}, for the
 * object graph a replay needs but the formula never asks about.  It was
 * produced only by the discovered heap ports and by the carrier walk over
 * the runtime-refined graph, both deleted: a port is now a DECLARATION, and
 * a declaration the case did not make produces no port to classify.  The
 * type test that used to decide the role stayed where it belongs -- {@code
 * RuntimeRegionPlanner.symbolicLeafPort} asks whether the VM can present
 * this value at all -- and it answers a boolean rather than naming a
 * role.</p>
 *
 * <p>{@link #normalize} therefore refuses every other spelling by name,
 * including the deleted one: a plan artifact written before this change
 * states a role this engine has no meaning for, and is not a supported
 * input.</p>
 */
public final class DependencyRole {
    public static final String VALUE_FRONTIER = "VALUE_FRONTIER";

    private DependencyRole() {
    }

    /**
     * Decodes the one dependency role.  Fail closed on purpose: a missing or
     * misspelled role is a row this engine cannot read, not a default.
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
