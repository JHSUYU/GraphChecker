package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * How a run departed from the model, and what is left of the model when it
 * did.
 */
public final class CoverageDivergence {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "REPLAY_DIVERGENCE";
    public static final String SUMMARY_KIND = "REPLAY_DIVERGENCE_SUMMARY";
    public static final String AUTHORITY = "REPLAY_DIVERGENCE_V1";

    /** Coverage states, shared with the relation merge and the worklist. */
    public static final String CLOSED = "CLOSED";
    public static final String PARTIAL = "PARTIAL";

    public enum Kind {
        TARGET, FLOW, SHAPE, IMPORT, GATE, SOURCE_EPOCH
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
                && KIND.equals(string(row, "kind"))
                && AUTHORITY.equals(string(row, "authority"))
                && classOf(string(row, "divergenceClass")) != null;
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
        String kind = string(gap, "kind");
        String reason = string(gap, "reason");
        if (isDivergence(gap)) return classOf(string(gap, "divergenceClass"));
        if (SparseReadCutGate.GAP_KIND.equals(kind)) return Kind.GATE;
        if (RpcExpressionHandoff.GAP_KIND.equals(kind)) {
            return reason.endsWith("SHAPE_MISMATCH")
                    || reason.endsWith("SORT_MISMATCH")
                    ? Kind.SHAPE : Kind.IMPORT;
        }
        if (SharedStateEvidence.GAP_KIND.equals(kind)) return Kind.FLOW;
        if (SessionTargetSlice.GAP_KIND.equals(kind)) {
            return SessionTargetSlice.NO_RECORDED_TARGET_REFERENCE.equals(
                    reason) ? Kind.TARGET : Kind.FLOW;
        }
        if ("OUTPUT_VERSION_ALIGNMENT_GAP".equals(kind)) {
            return Kind.SHAPE;
        }
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

    /**
     * Classifies a stream of named gaps and states what survives.
     *
     * @param rows                 coverage gaps and divergence rows
     * @param targetRelationUsable whether a usable target relation remains
     */
    public static JsonObject summary(Collection<JsonObject> rows,
                                     boolean targetRelationUsable) {
        Map<Kind, Integer> counts = new LinkedHashMap<>();
        for (Kind kind : Kind.values()) counts.put(kind, 0);
        List<JsonObject> classified = new ArrayList<>();
        int unclassified = 0;
        if (rows != null) {
            for (JsonObject row : rows) {
                Kind kind = classify(row);
                if (kind == null) {
                    unclassified++;
                    continue;
                }
                counts.put(kind, counts.get(kind) + 1);
                JsonObject entry = row.deepCopy();
                entry.addProperty("divergenceClass", kind.name());
                classified.add(entry);
            }
        }
        int total = 0;
        JsonObject classes = new JsonObject();
        for (Map.Entry<Kind, Integer> entry : counts.entrySet()) {
            classes.addProperty(entry.getKey().name(), entry.getValue());
            total += entry.getValue();
        }
        JsonObject summary = new JsonObject();
        summary.addProperty("schemaVersion", SCHEMA_VERSION);
        summary.addProperty("kind", SUMMARY_KIND);
        summary.addProperty("authority", AUTHORITY);
        summary.add("classes", classes);
        summary.addProperty("divergenceCount", total);
        summary.addProperty("unclassifiedCount", unclassified);
        summary.addProperty("targetRelationUsable", targetRelationUsable);
        int incompleteCount = total + unclassified;
        // A partial relation is retained whenever the target relation is
        // still usable.  Losing it because something else diverged would
        // discard evidence the run did produce.
        summary.addProperty("retainedPartialRelation",
                targetRelationUsable && incompleteCount > 0);
        summary.addProperty("coverageState", coverageState(incompleteCount,
                targetRelationUsable));
        JsonArray divergences = new JsonArray();
        for (JsonObject row : classified) divergences.add(row);
        summary.add("divergences", divergences);
        return summary;
    }

    /**
     * The honest coverage state of a model with {@code divergenceCount}
     * departures.
     */
    public static String coverageState(int divergenceCount,
                                       boolean targetRelationUsable) {
        if (!targetRelationUsable) return PARTIAL;
        return divergenceCount == 0 ? CLOSED : PARTIAL;
    }
}
