package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * How a run departed from the model, and what is left of the model when it
 * did.
 */
public final class CoverageDivergence {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "REPLAY_DIVERGENCE";
    public static final String AUTHORITY = "REPLAY_DIVERGENCE_V1";

    public enum Kind {
        TARGET, FLOW, SHAPE, IMPORT
    }

    private CoverageDivergence() {
    }

    /** One classified divergence row. */
    public static JsonObject of(Kind kind, String reason, String subject,
                                String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", KIND);
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("divergenceClass", kind.name());
        row.addProperty("reason", nonNull(reason));
        row.addProperty("subject", nonNull(subject));
        row.addProperty("detail", nonNull(detail));
        return row;
    }

    /** Whether {@code row} is a divergence this vocabulary produced. */
    public static boolean isDivergence(JsonObject row) {
        return row != null
                && KIND.equals(optionalString(row, "kind"))
                && AUTHORITY.equals(optionalString(row, "authority"))
                && classOf(optionalString(row, "divergenceClass")) != null;
    }

    private static Kind classOf(String name) {
        for (Kind kind : Kind.values()) {
            if (kind.name().equals(name)) return kind;
        }
        return null;
    }

    /** Classifies one named gap from the existing coverage stream. */
    public static Kind classify(JsonObject gap) {
        if (gap == null) return null;
        String kind = optionalString(gap, "kind");
        String reason = optionalString(gap, "reason");
        if (isDivergence(gap)) return classOf(optionalString(gap, "divergenceClass"));
        if (RpcExpressionHandoff.GAP_KIND.equals(kind)) {
            return reason.endsWith("SHAPE_MISMATCH")
                    || reason.endsWith("SORT_MISMATCH")
                    ? Kind.SHAPE : Kind.IMPORT;
        }
        if (SharedStateEvidence.GAP_KIND.equals(kind)) return Kind.FLOW;
        // The loop gap that is actually raised.  BoundedLoopComposition
        // reaches coverage directly rather than through the importer's
        // alignment-gap stream, so its kind was never listed here and a
        // bound-exhausted loop - which README LOOP-1 requires be named and
        // forbids from an accepted witness - classified as nothing.  It was
        // counted in unclassifiedCount rather than lost, which is why this
        // was latent; it is a class of its own now.
        if (BoundedLoopComposition.GAP_KIND.equals(kind)) {
            return Kind.FLOW;
        }
        return null;
    }

}
