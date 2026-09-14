package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.LocationKind;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;
import edu.uva.liftlab.graphchecker.runtime.d3.D3Runtime;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

/**
 * Publishes one finished activation as Design 3 rows.
 *
 * <p>One translation, run once per activation, from what the replay has
 * assembled -- its decisions, its write log, its mints and its anchor -- to
 * the per-kind row set the contract defines.  It reads only what the
 * activation already published, so nothing here changes the execution and
 * no row exists that the single-row result does not also state.</p>
 */
final class D3RowPublication {
    private D3RowPublication() {
    }

    /** Every row this activation can state, in the contract's shapes. */
    static void publish(ActiveRegion active) {
        if (active == null || !D3Runtime.open()) return;
        OccurrenceAddress occurrence = active.d3Address;
        if (occurrence == null) return;
        try {
            decisions(active, occurrence);
            roots(active, occurrence);
            writes(active, occurrence);
            target(active, occurrence);
            D3Runtime.endActivation(active.token);
        } catch (RuntimeException failure) {
            // The rows describe a run; a translation that throws must not
            // end one.  It says so instead, which is the difference between
            // "this run published no writes" and "this run made none".
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    occurrence.render(),
                    "the Design 3 rows of this activation could not be"
                            + " published: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    /**
     * One row per decision, with the predicate the taken arm satisfied.
     *
     * <p>The term is the satisfied predicate as published -- no second
     * negation anywhere -- and the outcome states which arm that was.</p>
     */
    private static void decisions(ActiveRegion active,
                                  OccurrenceAddress occurrence) {
        for (JsonObject mapping : active.branchMappings) {
            JsonObject witness = object(mapping, "witness");
            JsonObject concrete = object(mapping, "concreteObservation");
            String siteId = optionalString(mapping, "siteId");
            int ordinal = optionalInteger(mapping, "occurrence", 1);
            long seq = optionalLongInteger(mapping, "vmEventId", 0L);
            if (witness.size() > 0) {
                D3Runtime.decision(occurrence, seq, siteId, ordinal,
                        optionalBool(witness, "sourceTakenOutcome", false),
                        predicate(witness));
            } else if (concrete.size() > 0) {
                // A decision the VM held no condition for still happened,
                // and the arm it took is a fact of this run.
                D3Runtime.decision(occurrence, seq, siteId, ordinal,
                        optionalBool(concrete, "observedOutcome",
                                optionalBool(concrete, "outcome", false)),
                        null);
            }
        }
    }

    private static JsonObject predicate(JsonObject witness) {
        JsonElement satisfied = witness.get("sourceSatisfiedPredicate");
        return satisfied != null && satisfied.isJsonObject()
                ? satisfied.getAsJsonObject() : null;
    }

    /** One row per root this activation minted. */
    private static void roots(ActiveRegion active,
                              OccurrenceAddress occurrence) {
        for (JsonObject row : active.symbolizedRows) {
            String symbol = optionalString(row, "rawSymbol");
            if (symbol.isEmpty()) symbol = optionalString(row, "symbol");
            if (symbol.isEmpty()) continue;
            String rootId = optionalString(row, "sourceId");
            if (rootId.isEmpty()) rootId = optionalString(row, "portId");
            D3Runtime.rootMint(occurrence, rootId, symbol,
                    kindOf(row), optionalString(row, "recordedValue"),
                    optionalString(row, "domainMin"),
                    optionalString(row, "domainMax"),
                    !optionalString(row, "sourceId").isEmpty());
        }
    }

    /**
     * What kind of root one mint row states.
     *
     * <p>A clock declares its callee, a marker mints a boolean, everything
     * else is integral.  The kind decides how the composer may move it --
     * a clock is unbounded with a floor, a marker has two values -- so it
     * is read from the declaration, never guessed from the value.</p>
     */
    private static RootKind kindOf(JsonObject row) {
        if (!optionalString(row, "declaredCallee").isEmpty()) {
            return RootKind.CLOCK;
        }
        String javaType = optionalString(row, "javaType");
        return "Z".equals(javaType) || "boolean".equals(javaType)
                ? RootKind.MARKER : RootKind.INTEGRAL;
    }

    /**
     * One row per write version, and one per read the expressions state.
     *
     * <p>The write log is by location and version; the reads are the
     * {@code ReadFromExpression} nodes inside the expressions this
     * activation published, each of which names the version it observed.
     * The VM's log states no bytecode site for a write, so the site the
     * endpoint carries is the location itself and the loss is named once
     * per activation rather than silently rendered as a site.</p>
     */
    private static void writes(ActiveRegion active,
                               OccurrenceAddress occurrence) {
        boolean namedSiteMissing = false;
        for (JsonObject record : active.sharedStateRecords.values()) {
            String locationKey = optionalString(record, "locationKey");
            LocationId location = location(locationKey);
            if (location == null) continue;
            JsonObject envelope = object(record, "envelope");
            for (JsonElement element : array(envelope, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject version = element.getAsJsonObject();
                long id = optionalLongInteger(version, "fieldVersionId", -1L);
                if (id < 0L) continue;
                namedSiteMissing = true;
                JsonElement expression = version.get("expression");
                JsonObject written =
                        expression != null && expression.isJsonObject()
                                ? expression.getAsJsonObject() : null;
                D3Runtime.write(occurrence, id,
                        Endpoint.stateSite(locationKey,
                                optionalString(version, "versionKind"), 0,
                                true),
                        location, id, written,
                        written == null ? "" : optionalString(written,
                                "_java_type"));
                reads(active, occurrence, expression);
            }
        }
        for (JsonObject mapping : active.branchMappings) {
            reads(active, occurrence, mapping.get("witness"));
        }
        if (namedSiteMissing) {
            D3Runtime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    occurrence.render(),
                    "the VM write log states no bytecode site for a version,"
                            + " so a write endpoint's site is its location");
        }
    }

    /** Every read one expression tree states, by the version it observed. */
    private static void reads(ActiveRegion active,
                              OccurrenceAddress occurrence,
                              JsonElement expression) {
        if (expression == null) return;
        Set<String> published = new LinkedHashSet<String>();
        Map<JsonElement, Boolean> seen =
                new IdentityHashMap<JsonElement, Boolean>();
        collect(expression, occurrence, published, seen, 0);
    }

    private static void collect(JsonElement node, OccurrenceAddress occurrence,
                                Set<String> published,
                                Map<JsonElement, Boolean> seen, int depth) {
        if (node == null || depth > 64) return;
        if (node.isJsonArray()) {
            for (JsonElement element : node.getAsJsonArray()) {
                collect(element, occurrence, published, seen, depth + 1);
            }
            return;
        }
        if (!node.isJsonObject()) return;
        if (seen.put(node, Boolean.TRUE) != null) return;
        JsonObject object = node.getAsJsonObject();
        String type = optionalString(object, "_type");
        if ("ReadFromExpression".equals(type)) {
            readFrom(object, occurrence, published);
        } else if ("FieldAccessExpression".equals(type)) {
            fieldAccess(object, occurrence, published);
        }
        for (Map.Entry<String, JsonElement> member : object.entrySet()) {
            collect(member.getValue(), occurrence, published, seen,
                    depth + 1);
        }
    }

    /** A read the write log covers: the location, and the version it saw. */
    private static void readFrom(JsonObject node,
                                 OccurrenceAddress occurrence,
                                 Set<String> published) {
        JsonObject where = object(node, "location");
        String locationKey = locationKey(where);
        LocationId location = location(locationKey);
        if (location == null) return;
        JsonElement stated = node.get("observedVersion");
        long observed = -1L;
        if (stated != null && stated.isJsonObject()) {
            observed = optionalLongInteger(stated.getAsJsonObject(),
                    "fieldVersionId", -1L);
        } else if (stated != null && stated.isJsonPrimitive()) {
            observed = stated.getAsLong();
        }
        String identity = locationKey + "#" + observed;
        if (!published.add(identity)) return;
        D3Runtime.read(occurrence, Math.max(0L, observed),
                Endpoint.stateSite(locationKey, "READ_FROM", 0, false),
                location, observed, optionalString(node, "_exp"),
                optionalString(node, "_java_type"), "");
    }

    /**
     * A read the log does not cover: the object read from and what its
     * field then held, which is the pair the VM states (REPORT15).
     */
    private static void fieldAccess(JsonObject node,
                                    OccurrenceAddress occurrence,
                                    Set<String> published) {
        JsonElement value = node.get("concreteValue");
        if (value == null || value.isJsonNull()) return;
        String ownerClass = optionalString(node, "ownerClass");
        int offset = optionalInteger(node, "fieldOffset", -1);
        String locationKey = "INSTANCE_FIELD/" + ownerClass + "#" + offset;
        String identity = locationKey + "#concrete";
        if (!published.add(identity)) return;
        LocationId location = LocationId.of(LocationKind.INSTANCE,
                ownerClass.isEmpty() ? "<unstated>" : ownerClass,
                String.valueOf(offset));
        D3Runtime.read(occurrence, 0L,
                Endpoint.stateSite(locationKey, "FIELD", offset, false),
                location, ReadRow.UNKNOWN_VERSION,
                optionalString(node, "_exp"),
                optionalString(node, "_java_type"),
                value.isJsonObject()
                        ? optionalString(value.getAsJsonObject(), "_exp")
                        : value.getAsString());
    }

    /** {@code KIND/owner#slot}, as the VM states one location. */
    private static String locationKey(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (kind.isEmpty() || owner == 0L || !location.has("slot")) {
            return "";
        }
        return kind + "/" + owner + "#"
                + optionalInteger(location, "slot", 0);
    }

    /** The contract location one VM location key names. */
    private static LocationId location(String locationKey) {
        String key = safe(locationKey);
        int separator = key.indexOf('/');
        int slot = key.lastIndexOf('#');
        if (separator <= 0 || slot <= separator) return null;
        String kind = key.substring(0, separator);
        return LocationId.of(kindOfLocation(kind),
                key.substring(separator + 1, slot), key.substring(slot + 1));
    }

    private static LocationKind kindOfLocation(String kind) {
        if (kind.startsWith("STATIC")) return LocationKind.STATIC;
        if (kind.startsWith("ARRAY")) return LocationKind.ARRAY;
        if (kind.startsWith("MAP")) return LocationKind.MAP;
        return LocationKind.INSTANCE;
    }

    /**
     * The anchor, with phi in the FATAL polarity whichever arm ran.
     *
     * <p>The recorded decision's predicate is the arm this run took; the
     * task declares which arm is fatal.  So the row states the fatal arm of
     * that predicate and, separately, whether this run took it -- and no
     * reader downstream re-derives a polarity (the second negation is
     * exactly the bug the phi-polarity fix removed).</p>
     */
    private static void target(ActiveRegion active,
                               OccurrenceAddress occurrence) {
        ConcolicTaskPlan.RuntimeTask task = active.activation;
        if (!task.declaresTargetBranch()) return;
        JsonObject reach = active.targetReach;
        boolean reached = reach != null;
        boolean observed = reached && optionalBool(reach, "outcome", false);
        boolean fatalArm = task.targetBranchRequiredOutcome;
        JsonObject condition = null;
        for (JsonObject mapping : active.branchMappings) {
            if (!task.targetBranchSite.equals(
                    optionalString(mapping, "siteId"))) {
                continue;
            }
            if (optionalInteger(mapping, "occurrence", -1)
                    != task.targetBranchOccurrence) {
                continue;
            }
            JsonObject witness = object(mapping, "witness");
            if (witness.size() > 0) condition = predicate(witness);
        }
        D3Runtime.target(occurrence,
                reach == null ? 0L : optionalLongInteger(reach, "vmEventId",
                        0L), task.targetBranchLabel(), condition,
                observed == fatalArm, reached && observed == fatalArm,
                reached);
    }
}
