package edu.uva.liftlab.graphchecker.d3.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigDecimal;

/**
 * What one imported concolic path summary states about the declared target.
 */
public final class PathObservation {
    private PathObservation() {
    }

    /** Whether this activation exited through the selected target throw. */
    public static final String TARGET_REACHED = "targetReached";

    /** Canonical carrier for the runtime event that makes a target path
     *  eligible for composition.  Stricter than the generic accessors:
     *  target identity is an authority, so unknown members and coercions are
     *  schema errors. */
    public static final class TargetReachEvent {
        public static final String FIELD = "targetReach";
        public static final String KIND = "TARGET_REACH_EVENT";

        private final String siteId;
        private final int occurrence;
        private final boolean outcome;
        /**
         * The VM event sequence number at which the anchor was recorded, or
         * {@code 0} when this replay's VM assigned none.  It is the same
         * clock the branch-decision rows publish, so a composer can say which
         * decisions were taken before the anchor and order two activations'
         * decisions against each other; the other published positions
         * (unit index, path-condition index) are local to a method or to one
         * condition window and repeat across activations.
         */
        private final long vmEventId;

        private TargetReachEvent(String siteId, int occurrence,
                                 boolean outcome, long vmEventId) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.outcome = outcome;
            this.vmEventId = vmEventId;
        }

        public static TargetReachEvent decode(JsonElement encoded) {
            if (encoded == null || !encoded.isJsonObject()) {
                throw new IllegalArgumentException(
                        FIELD + " must be an object");
            }
            JsonObject event = encoded.getAsJsonObject();
            boolean clocked = event.has("vmEventId");
            if (event.size() != (clocked ? 5 : 4)
                    || !event.has("kind") || !event.has("siteId")
                    || !event.has("occurrence") || !event.has("outcome")) {
                throw new IllegalArgumentException(
                        FIELD + " must contain exactly kind, siteId, "
                                + "occurrence and outcome, and at most "
                                + "vmEventId");
            }
            JsonElement kind = event.get("kind");
            JsonElement site = event.get("siteId");
            JsonElement ordinal = event.get("occurrence");
            JsonElement taken = event.get("outcome");
            if (!kind.isJsonPrimitive()
                    || !kind.getAsJsonPrimitive().isString()
                    || !KIND.equals(kind.getAsString())) {
                throw new IllegalArgumentException(
                        FIELD + ".kind must be " + KIND);
            }
            if (!site.isJsonPrimitive()
                    || !site.getAsJsonPrimitive().isString()
                    || site.getAsString().trim().isEmpty()) {
                throw new IllegalArgumentException(
                        FIELD + ".siteId must be a nonempty string");
            }
            final int occurrence;
            try {
                if (!ordinal.isJsonPrimitive()
                        || !ordinal.getAsJsonPrimitive().isNumber()) {
                    throw new ArithmeticException("not a number");
                }
                occurrence = new BigDecimal(
                        ordinal.getAsString()).intValueExact();
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        FIELD + ".occurrence must be an exact integer",
                        malformed);
            }
            if (occurrence < 1) {
                throw new IllegalArgumentException(
                        FIELD + ".occurrence must be positive");
            }
            if (!taken.isJsonPrimitive()
                    || !taken.getAsJsonPrimitive().isBoolean()) {
                throw new IllegalArgumentException(
                        FIELD + ".outcome must be a boolean");
            }
            long vmEventId = 0L;
            if (clocked) {
                JsonElement clock = event.get("vmEventId");
                try {
                    if (!clock.isJsonPrimitive()
                            || !clock.getAsJsonPrimitive().isNumber()) {
                        throw new ArithmeticException("not a number");
                    }
                    vmEventId = new BigDecimal(
                            clock.getAsString()).longValueExact();
                } catch (RuntimeException malformed) {
                    throw new IllegalArgumentException(
                            FIELD + ".vmEventId must be an exact integer",
                            malformed);
                }
                if (vmEventId <= 0L) {
                    // A replay whose VM assigned no event states no field at
                    // all; a zero would order this anchor ahead of every
                    // decision the VM did number.
                    throw new IllegalArgumentException(
                            FIELD + ".vmEventId must be positive");
                }
            }
            return new TargetReachEvent(site.getAsString(), occurrence,
                    taken.getAsBoolean(), vmEventId);
        }

        public boolean matches(String site, int ordinal, boolean taken) {
            return siteId.equals(site) && occurrence == ordinal
                    && outcome == taken;
        }

    }

}
