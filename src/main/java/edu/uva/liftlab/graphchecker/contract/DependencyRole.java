package edu.uva.liftlab.graphchecker.contract;

/** Failure-directed role of one exact region input port. */
public final class DependencyRole {
    public static final String VALUE_FRONTIER = "VALUE_FRONTIER";
    public static final String CONCRETE_STRUCTURE_CARRIER =
            "CONCRETE_STRUCTURE_CARRIER";

    private DependencyRole() {
    }

    /**
     * Decodes the required two-valued dependency role.
     *
     * <p>This contract is intentionally fail closed.  Treating a missing or
     * misspelled role as a value frontier silently creates solver inputs from
     * structural owners and containers.</p>
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
        if (VALUE_FRONTIER.equals(encoded)
                || CONCRETE_STRUCTURE_CARRIER.equals(encoded)) {
            return encoded;
        }
        throw new IllegalArgumentException(
                "unsupported dependencyRole: " + encoded);
    }

    public static boolean valueFrontier(Object value) {
        return VALUE_FRONTIER.equals(normalize(value));
    }

    /** Both declared roles remain in the reverse causal closure. */
    public static boolean causalFollow(Object value) {
        normalize(value);
        return true;
    }

    /** VALUE dominates when several static uses share one runtime port. */
    public static String merge(Object left, Object right) {
        String normalizedLeft = normalize(left);
        String normalizedRight = normalize(right);
        return VALUE_FRONTIER.equals(normalizedLeft)
                || VALUE_FRONTIER.equals(normalizedRight)
                ? VALUE_FRONTIER : CONCRETE_STRUCTURE_CARRIER;
    }
}
