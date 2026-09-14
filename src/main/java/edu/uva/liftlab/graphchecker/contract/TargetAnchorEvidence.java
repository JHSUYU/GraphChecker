package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * What one replay publishes at the anchored fatal target.
 *
 * <p>The composer's whole input contract, in one object per replayed path:
 * the anchor that identifies the same site and occurrence across replays,
 * the fatal predicate {@code phi_p} as an expression in the polarity that
 * reaches the failure, the path condition {@code pi_p} that led there, the
 * case selectors the replay explored, and the roots the recording left
 * free.  {@code Fatal_T = OR_p (pi_p AND phi_p)} needs nothing else.</p>
 *
 * <p>Reaching the target means the fatal site <em>executed</em>, whatever it
 * decided.  A healthy activation publishes the same row with its own
 * {@code phi_p}, which that replay's values make false; it is a disjunct
 * that contributes nothing, not a row that is missing.</p>
 *
 * <p>This travels beside the older {@code targetReach} event rather than
 * replacing it, so that the two composers can be compared on one artifact
 * during the transition.</p>
 */
public final class TargetAnchorEvidence {
    /** The member one path row carries this under. */
    public static final String FIELD = "targetAnchor";
    public static final String KIND = "TARGET_ANCHOR_EVIDENCE";
    public static final int SCHEMA_VERSION = 1;
    public static final String AUTHORITY = "RUNTIME_PROPAGATED_FATAL_VALUE_V1";

    public static final String ANCHOR_KEY = "anchorKey";
    public static final String SITE_ID = SiteId.MEMBER;
    public static final String OCCURRENCE = "occurrence";
    public static final String SOURCE_KEY = "sourceKey";
    public static final String REGION_ID = "regionId";
    public static final String OCCURRENCE_ID = "occurrenceId";
    public static final String TOPOLOGY_EPOCH = "topologyEpoch";

    public static final String REACHED = "reached";
    public static final String OBSERVED_OUTCOME = "observedTakenOutcome";
    public static final String REQUIRED_OUTCOME = "requiredTakenOutcome";
    public static final String FATAL_PREDICATE = "fatalPredicate";
    public static final String PATH_CONDITION = "pathCondition";
    public static final String CASE_SELECTORS = "caseSelectors";
    public static final String ROOTS = "roots";
    public static final String CARRIERS = "carriers";

    /** Separates the members of {@link #key()}. */
    private static final String KEY_SEPARATOR = "\0";

    private final JsonObject raw;

    private TargetAnchorEvidence(JsonObject raw) {
        this.raw = raw;
    }

    /**
     * Builds one replay's anchor row.
     *
     * @param constraints the path's complete fatal-polarity conjunction, the
     *                    fatal branch predicate last.  The prefix is
     *                    {@code pi_p}; the last element is {@code phi_p}.
     */
    public static JsonObject build(String siteId, int occurrence,
                                   String sourceKey, String regionId,
                                   String occurrenceId, String topologyEpoch,
                                   boolean observedOutcome,
                                   boolean requiredOutcome,
                                   JsonArray constraints,
                                   JsonObject caseSelectors,
                                   Collection<JsonObject> roots,
                                   Collection<String> carriers) {
        if (siteId == null || siteId.trim().isEmpty()) {
            throw new IllegalArgumentException("anchor siteId is required");
        }
        if (occurrence < 1) {
            throw new IllegalArgumentException(
                    "anchor occurrence must be positive");
        }
        if (constraints == null || constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "an anchored path states at least its fatal predicate");
        }
        JsonObject anchor = new JsonObject();
        anchor.addProperty("kind", KIND);
        anchor.addProperty("schemaVersion", SCHEMA_VERSION);
        anchor.addProperty("authority", AUTHORITY);
        JsonObject key = new JsonObject();
        key.addProperty(SITE_ID, siteId);
        key.addProperty(OCCURRENCE, occurrence);
        key.addProperty(SOURCE_KEY, sourceKey == null ? "" : sourceKey);
        key.addProperty(REGION_ID, regionId == null ? "" : regionId);
        key.addProperty(OCCURRENCE_ID,
                occurrenceId == null ? "" : occurrenceId);
        key.addProperty(TOPOLOGY_EPOCH,
                topologyEpoch == null ? "" : topologyEpoch);
        anchor.add(ANCHOR_KEY, key);
        anchor.addProperty(REACHED, true);
        anchor.addProperty(OBSERVED_OUTCOME, observedOutcome);
        anchor.addProperty(REQUIRED_OUTCOME, requiredOutcome);
        JsonArray prefix = new JsonArray();
        for (int index = 0; index < constraints.size() - 1; index++) {
            prefix.add(constraints.get(index).deepCopy());
        }
        anchor.add(PATH_CONDITION, prefix);
        anchor.add(FATAL_PREDICATE,
                constraints.get(constraints.size() - 1).deepCopy());
        anchor.add(CASE_SELECTORS, caseSelectors == null
                ? new JsonObject() : caseSelectors.deepCopy());
        JsonArray rootRows = new JsonArray();
        if (roots != null) {
            for (JsonObject root : roots) {
                if (root != null) rootRows.add(root.deepCopy());
            }
        }
        anchor.add(ROOTS, rootRows);
        JsonArray carrierRows = new JsonArray();
        if (carriers != null) {
            for (String carrier : carriers) {
                if (carrier != null && !carrier.isEmpty()) {
                    carrierRows.add(carrier);
                }
            }
        }
        anchor.add(CARRIERS, carrierRows);
        return anchor;
    }

    /** The anchor row of one path, or null when it carries none. */
    public static TargetAnchorEvidence of(JsonObject path) {
        if (path == null) return null;
        JsonElement encoded = path.get(FIELD);
        if (encoded == null || !encoded.isJsonObject()) return null;
        JsonObject anchor = encoded.getAsJsonObject();
        if (!KIND.equals(optionalString(anchor, "kind"))) return null;
        return new TargetAnchorEvidence(anchor);
    }

    public JsonObject json() {
        return raw;
    }

    public String siteId() {
        return optionalString(object(raw, ANCHOR_KEY), SITE_ID);
    }

    public int occurrence() {
        return optionalInteger(object(raw, ANCHOR_KEY), OCCURRENCE, -1);
    }

    public String sourceKey() {
        return optionalString(object(raw, ANCHOR_KEY), SOURCE_KEY);
    }

    public String occurrenceId() {
        return optionalString(object(raw, ANCHOR_KEY), OCCURRENCE_ID);
    }

    public String topologyEpoch() {
        return optionalString(object(raw, ANCHOR_KEY), TOPOLOGY_EPOCH);
    }

    /**
     * Site, occurrence and the node/epoch that ran it: the one key that
     * makes two replays' rows rows about the same event.
     */
    public String key() {
        return siteId() + KEY_SEPARATOR + occurrence() + KEY_SEPARATOR
                + sourceKey() + KEY_SEPARATOR + topologyEpoch();
    }

    public boolean observedTakenOutcome() {
        return optionalBool(raw, OBSERVED_OUTCOME, false);
    }

    public boolean requiredTakenOutcome() {
        return optionalBool(raw, REQUIRED_OUTCOME, false);
    }

    /** {@code phi_p}: the fatal condition, in the polarity that fails. */
    public JsonElement fatalPredicate() {
        return raw.get(FATAL_PREDICATE);
    }

    /** {@code pi_p}: every branch decision that led to the target. */
    public JsonArray pathCondition() {
        return array(raw, PATH_CONDITION);
    }

    public JsonObject caseSelectors() {
        return object(raw, CASE_SELECTORS);
    }

    public List<JsonObject> roots() {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement encoded : array(raw, ROOTS)) {
            if (encoded.isJsonObject()) result.add(encoded.getAsJsonObject());
        }
        return result;
    }

    /** Session-local locations this replay declared as tracked carriers. */
    public List<String> carriers() {
        List<String> result = new ArrayList<>();
        for (JsonElement encoded : array(raw, CARRIERS)) {
            if (encoded.isJsonPrimitive()) result.add(encoded.getAsString());
        }
        return result;
    }
}
