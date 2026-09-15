package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.d3.plan.PathObservation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * Stable identity of one region-local control case.
 *
 * <p>This identity deliberately contains only local control facts.  A
 * complete summary names an execution observation; expression anchors name
 * propagated values; a family snapshot scopes a solver verdict.  None of
 * those three identities may become a local case identity.</p>
 */
public final class LocalCaseIdentity {
    public static final String FIELD = "localCaseId";
    public static final String PREFIX = "LOCAL_CASE.";
    /** Stable owner and selector carried by every case-local evidence row. */
    public static final String OWNER = "caseOwner";
    public static final String SELECTOR = "caseSelector";

    private LocalCaseIdentity() {
    }

    public static String owner(String regionId, String occurrenceId,
                               String caseId, int caseIndex) {
        return "region:" + text(regionId) + "/instance:"
                + text(occurrenceId) + "/case:"
                + first(caseId, String.valueOf(caseIndex));
    }

    public static String owner(JsonObject summary) {
        if (summary == null) {
            throw new IllegalArgumentException("summary is required");
        }
        return owner(optionalString(summary, "regionId"),
                optionalString(summary, "occurrenceId"), stated(summary), 0);
    }

    public static String selector(String owner) {
        return "case_selector__" + CanonicalJson.sha256(
                first(owner, "global"));
    }

    public static void stamp(JsonObject row, String owner) {
        if (row == null || owner == null || owner.isEmpty()) return;
        row.addProperty(OWNER, owner);
        row.addProperty(SELECTOR, selector(owner));
    }

    /** Computes the case id without reading an already-stated case id. */
    public static String compute(JsonObject summary) {
        return PREFIX + CanonicalJson.sha256(payload(summary));
    }

    /**
     * Reads the identity an admitted summary already carries.
     *
     * <p>The identity is minted exactly once, by the importer's admission
     * gate, and travels with the summary from there.  Recomputing it on the
     * way in re-parsed every branch mapping and re-hashed the whole control
     * payload at each decode; the stated value is the authority.</p>
     */
    public static String stated(JsonObject summary) {
        String stated = optionalString(summary, FIELD);
        if (stated.isEmpty()) {
            throw new IllegalArgumentException(
                    "relation summary has no localCaseId");
        }
        return stated;
    }

    /** Exposed for diagnostics and focused identity-contract tests. */
    public static JsonObject payload(JsonObject summary) {
        if (summary == null) {
            throw new IllegalArgumentException("summary is required");
        }
        String source = required(summary, "sourceKey");
        String region = required(summary, "regionId");
        String occurrence = required(summary, "occurrenceId");

        List<SummaryBranchMapping> mappings =
                SummaryBranchMapping.fromSummary(summary);
        JsonArray controls = new JsonArray();
        Set<Integer> ownedConditions = new LinkedHashSet<>();
        for (SummaryBranchMapping mapping : mappings) {
            JsonObject control = new JsonObject();
            control.addProperty("siteId", mapping.siteId());
            control.addProperty("occurrence", mapping.occurrence());
            control.addProperty("decisionOrdinal",
                    mapping.decisionOrdinal());
            control.addProperty("outcome", mapping.exactDecisionToken());
            if (mapping.isWitnessed()) {
                ownedConditions.add(mapping.summaryPcIndex());
            }
            controls.add(control);
        }

        JsonArray auxiliary = new JsonArray();
        JsonArray conditions = array(summary, "pathCondition");
        for (int index = 0; index < conditions.size(); index++) {
            if (ownedConditions.contains(index)) continue;
            JsonElement encoded = conditions.get(index);
            auxiliary.add(staticConditionToken(encoded));
        }

        List<JsonObject> loopRows = new ArrayList<>();
        for (JsonElement encoded : array(summary,
                LoopBoundPolicy.PATH_LOOP_COUNTS)) {
            if (!encoded.isJsonObject()) continue;
            JsonObject sourceRow = encoded.getAsJsonObject();
            JsonObject loop = new JsonObject();
            copyText(sourceRow, loop, LoopBoundPolicy.LOOP_SITE_ID);
            copyText(sourceRow, loop, LoopBoundPolicy.RUNTIME_LOOP_ID);
            copyText(sourceRow, loop,
                    LoopBoundPolicy.LOOP_CLASSIFICATION);
            copyInteger(sourceRow, loop, LoopBoundPolicy.LOOP_BODY_BOUND);
            copyInteger(sourceRow, loop, LoopBoundPolicy.LOOP_BODY_COUNT);
            loop.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED,
                    optionalBool(sourceRow, LoopBoundPolicy.PATH_LOOP_REACHED,
                            false));
            JsonArray cardinalities = new JsonArray();
            List<JsonObject> exact = new ArrayList<>();
            for (JsonElement value : array(sourceRow,
                    LoopBoundPolicy.LOOP_CARDINALITIES)) {
                if (!value.isJsonObject()) continue;
                JsonObject cardinality = new JsonObject();
                copyInteger(value.getAsJsonObject(), cardinality,
                        LoopBoundPolicy.DYNAMIC_OCCURRENCE);
                copyInteger(value.getAsJsonObject(), cardinality,
                        LoopBoundPolicy.LOOP_CARDINALITY);
                exact.add(cardinality);
            }
            Collections.sort(exact, Comparator.comparing(
                    CanonicalJson::render));
            for (JsonObject cardinality : exact) {
                cardinalities.add(cardinality);
            }
            if (cardinalities.size() > 0) {
                loop.add(LoopBoundPolicy.LOOP_CARDINALITIES,
                        cardinalities);
            }
            loopRows.add(loop);
        }
        Collections.sort(loopRows, Comparator.comparing(
                CanonicalJson::render));
        JsonArray loops = new JsonArray();
        for (JsonObject loop : loopRows) loops.add(loop);

        JsonObject terminal = new JsonObject();
        terminal.addProperty("normalExit", optionalBool(summary, "normalExit",
                false));
        terminal.addProperty("boundedExit", optionalBool(summary, "boundedExit",
                false));
        terminal.addProperty("exceptionType", optionalString(summary,
                "exceptionType"));
        if (summary.has(PathObservation.TARGET_REACHED)) {
            terminal.addProperty(PathObservation.TARGET_REACHED,
                    optionalBool(summary, PathObservation.TARGET_REACHED, false));
        }
        JsonElement target = summary.get(PathObservation.TargetReachEvent.FIELD);
        if (target != null && target.isJsonObject()) {
            PathObservation.TargetReachEvent event =
                    PathObservation.TargetReachEvent.decode(target);
            // Without the VM clock: see TargetReachEvent.toIdentityJson.
            terminal.add(PathObservation.TargetReachEvent.FIELD,
                    event.toIdentityJson());
        }

        JsonObject identity = new JsonObject();
        identity.addProperty("sourceKey", source);
        identity.addProperty("regionId", region);
        identity.addProperty("occurrenceId", occurrence);
        identity.add("orderedBranchControls", controls);
        identity.add("auxiliaryStaticTokens", auxiliary);
        identity.add("boundedLoopProfile", loops);
        identity.add("terminalOutcome", terminal);
        return identity;
    }

    /**
     * Value-independent identity of one non-branch path constraint.
     * Operands belong to propagated expression content; only the static
     * operation/site shape contributes to local control identity.
     */
    public static JsonObject staticConditionToken(JsonElement encoded) {
        JsonObject token = new JsonObject();
        if (encoded != null && encoded.isJsonObject()) {
            JsonObject condition = encoded.getAsJsonObject();
            copyText(condition, token, "_code_position");
            copyText(condition, token, "codePosition");
            copyText(condition, token, "_type");
            copyText(condition, token, "_java_type");
            copyText(condition, token, "_op");
        } else {
            token.addProperty("_type", encoded == null
                    ? "null" : encoded.isJsonPrimitive()
                    ? "primitive" : "array");
        }
        return token;
    }

    private static String required(JsonObject source, String field) {
        String value = optionalString(source, field);
        if (value.isEmpty()) {
            throw new IllegalArgumentException(
                    "local case requires " + field);
        }
        return value;
    }

    private static String first(String value, String fallback) {
        return value == null || value.trim().isEmpty() ? fallback : value;
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }

    private static void copyText(JsonObject source, JsonObject target,
                                 String field) {
        String value = optionalString(source, field);
        if (!value.isEmpty()) target.addProperty(field, value);
    }

    private static void copyInteger(JsonObject source, JsonObject target,
                                    String field) {
        if (source.has(field)) {
            target.addProperty(field, optionalInteger(source, field, -1));
        }
    }
}
