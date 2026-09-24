package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * What ONE recording states at one site the static scope map named
 * {@code DECLARED_SITE}: that the call ran, what it returned, and the
 * receiver it ran on.
 *
 * <p>The dynamic half of a declared port, and the whole of it.  The static
 * half -- the cell, the callee, the implementation method, the dependency
 * cell and the type -- is the scope map's {@link StaticScopeMap.Declared},
 * and the two are joined by {@link
 * ConcolicScheduler.SymbolicInputSelection}, the one rule that decides
 * whether the case declared this site at all.  Nothing here decides
 * anything: a capture is published for every declared site the recording
 * entered, whether or not a declaration names it.</p>
 *
 * <p>{@link #ORDINAL} is the port's replay address -- the occurrence's own
 * returns at one site, counted 1, 2, 3 in recorded order.  It counts per
 * (occurrence, site, callee) and never per recorded {@code callId}: the
 * recorder's call id is a per-run event counter, so a port id spelled from
 * it would rename the same root on every run of the same obligation.</p>
 */
public final class DeclaredSiteCapture {
    /** Region-plan member carrying one occurrence's captures. */
    public static final String PLAN_FIELD = "declaredSiteCaptures";

    public static final String ORDINAL = "ordinal";
    public static final String DECLARED_CALLEE = "declaredCallee";
    public static final String PRIMITIVE_VALUE = "primitiveValue";
    public static final String EVENT_SEQ = "eventSeq";
    public static final String CALL_ID = "callId";
    public static final String INVOCATION_ID = "invocationId";
    public static final String ROOT_CALL_ID = "rootCallId";
    public static final String ROOT_SOURCE_KEY = "rootSourceKey";
    public static final String SOURCE_KEY = "sourceKey";
    public static final String REQUEST_KEY = "requestKey";
    public static final String REQUEST_API = "requestApi";
    public static final String RECEIVER_OBJECT_ID = "receiverObjectId";
    public static final String RECEIVER_RUNTIME_TYPE = "receiverRuntimeType";
    public static final String VALUE_OBJECT_ID = "valueObjectId";

    private final String siteId;
    private final String declaredCallee;
    private final int ordinal;
    private final String primitiveValue;
    private final long eventSeq;
    private final long callId;
    private final long invocationId;
    private final long rootCallId;
    private final String rootSourceKey;
    private final String sourceKey;
    private final String requestKey;
    private final String requestApi;
    private final int receiverObjectId;
    private final String receiverRuntimeType;
    private final int valueObjectId;

    private DeclaredSiteCapture(JsonObject row) {
        this.siteId = optionalString(row, SiteId.MEMBER);
        this.declaredCallee = optionalString(row, DECLARED_CALLEE);
        this.ordinal = optionalInteger(row, ORDINAL, -1);
        this.primitiveValue = optionalString(row, PRIMITIVE_VALUE);
        this.eventSeq = optionalLongInteger(row, EVENT_SEQ, -1L);
        this.callId = optionalLongInteger(row, CALL_ID, -1L);
        this.invocationId = optionalLongInteger(row, INVOCATION_ID, -1L);
        this.rootCallId = optionalLongInteger(row, ROOT_CALL_ID, -1L);
        this.rootSourceKey = optionalString(row, ROOT_SOURCE_KEY);
        this.sourceKey = optionalString(row, SOURCE_KEY);
        this.requestKey = optionalString(row, REQUEST_KEY);
        this.requestApi = optionalString(row, REQUEST_API);
        this.receiverObjectId = optionalInteger(row, RECEIVER_OBJECT_ID, 0);
        this.receiverRuntimeType = optionalString(row,
                RECEIVER_RUNTIME_TYPE);
        this.valueObjectId = optionalInteger(row, VALUE_OBJECT_ID, 0);
        if (siteId.isEmpty() || declaredCallee.isEmpty() || ordinal < 1) {
            throw new IllegalArgumentException(
                    "declared site capture names no site, callee or "
                            + "ordinal: " + row);
        }
    }

    /**
     * The row one recorded return publishes.  Written by the runtime
     * planner, which holds the recording, and read back here; the member
     * names are stated once, in this class, so the two cannot drift.
     */
    public static Map<String, Object> row(
            String siteId, String declaredCallee, int ordinal,
            String primitiveValue, long eventSeq, long callId,
            long invocationId, long rootCallId, String rootSourceKey,
            String sourceKey, String requestKey, String requestApi,
            int receiverObjectId, String receiverRuntimeType,
            int valueObjectId) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(SiteId.MEMBER, siteId);
        row.put(DECLARED_CALLEE, declaredCallee);
        row.put(ORDINAL, ordinal);
        row.put(PRIMITIVE_VALUE, primitiveValue);
        row.put(EVENT_SEQ, eventSeq);
        row.put(CALL_ID, callId);
        row.put(INVOCATION_ID, invocationId);
        row.put(ROOT_CALL_ID, rootCallId);
        putIfStated(row, ROOT_SOURCE_KEY, rootSourceKey);
        putIfStated(row, SOURCE_KEY, sourceKey);
        putIfStated(row, REQUEST_KEY, requestKey);
        putIfStated(row, REQUEST_API, requestApi);
        if (receiverObjectId != 0) {
            row.put(RECEIVER_OBJECT_ID, receiverObjectId);
            putIfStated(row, RECEIVER_RUNTIME_TYPE, receiverRuntimeType);
        }
        if (valueObjectId != 0) {
            row.put(VALUE_OBJECT_ID, valueObjectId);
        }
        return row;
    }

    private static void putIfStated(Map<String, Object> row, String key,
                                    String value) {
        if (value != null && !value.isEmpty()) row.put(key, value);
    }

    /** Every capture one occurrence's plan row states. */
    public static List<DeclaredSiteCapture> decode(JsonObject plan) {
        List<DeclaredSiteCapture> captures = new ArrayList<>();
        for (JsonElement element : array(plan, PLAN_FIELD)) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        PLAN_FIELD + " must contain objects");
            }
            captures.add(new DeclaredSiteCapture(element.getAsJsonObject()));
        }
        return Collections.unmodifiableList(captures);
    }

    public String siteId() { return siteId; }

    public String declaredCallee() { return declaredCallee; }

    /**
     * The port one declaration mints at this capture, before the binding
     * mode {@link ConcolicScheduler#materializationPlan} gives it.
     *
     * <p>Every static member is the scope map's and every dynamic one is the
     * recording's, so two stages holding the two artifacts spell the same
     * port.  The region is the PLAN's -- the occurrence this capture was
     * recorded in belongs to that region -- and not the scope map's
     * {@code regionId}, which names the innermost static region holding the
     * site and answers a different question.</p>
     */
    JsonObject port(RegionInstancePlan plan, StaticScopeMap.Site site) {
        StaticScopeMap.Declared declared = site.declared;
        boolean accessor = StaticScopeMap.ACCESSOR_RETURN.equals(
                declared.kind);
        String occurrenceId = plan.occurrenceId();
        // Published identity, spelled from content alone.  The accessor
        // family names the candidate edge the declaration was read from, as
        // its ports always have; the call-return family names the site.
        String key = accessor
                ? occurrenceId + "\n" + declared.edgeId + "\n" + siteId
                + "\n" + declaredCallee + "\n" + ordinal
                : occurrenceId + "\n" + siteId + "\n" + ordinal;
        JsonObject port = staticPort(plan, site, key);
        port.addProperty("observed", true);
        port.addProperty("replayOccurrence", ordinal);
        port.addProperty(PRIMITIVE_VALUE, primitiveValue);
        port.addProperty(EVENT_SEQ, eventSeq);
        port.addProperty(CALL_ID, callId);
        dependencyCells(port, site);
        if (accessor) {
            accessorPort(port, site, SiteId.methodOf(siteId),
                    plan.regionId());
        } else {
            callReturnPort(port, site);
            if (!sourceKey.isEmpty()) port.addProperty(SOURCE_KEY, sourceKey);
            if (!requestKey.isEmpty()) port.addProperty(REQUEST_KEY, requestKey);
            if (!requestApi.isEmpty()) port.addProperty(REQUEST_API, requestApi);
        }
        return port;
    }

    /**
     * The port a CALL_RETURN declaration mints at a site no recording
     * captured: the static half alone, for an occurrence a replay exposed
     * (DESIGN4 section 3.3b).  Its id carries no ordinal, so the one action
     * answers every firing of the site ({@code SymbolizeAction
     * #acceptsOccurrence}), and it states no observed value.  An accessor
     * return is ported from the recorded receiver, which such an occurrence
     * has none of, and is refused by name.
     */
    public static JsonObject declaredPort(RegionInstancePlan plan,
                                          StaticScopeMap.Site site) {
        if (StaticScopeMap.ACCESSOR_RETURN.equals(site.declared.kind)) {
            throw new IllegalArgumentException("an accessor return needs the"
                    + " recorded receiver, which an exposed occurrence has"
                    + " none of: " + site);
        }
        JsonObject port = staticPort(plan, site,
                plan.occurrenceId() + "\n" + site.siteId);
        port.addProperty("observed", false);
        dependencyCells(port, site);
        callReturnPort(port, site);
        return port;
    }

    /**
     * The same port at an occurrence a replay exposed, from the port a
     * recorded occurrence of the region holds -- {@link #declaredPort}'s
     * port, read off a plan row where the scope map is not at hand.
     *
     * <p>A port is one occurrence's input: its id is spelled from that
     * occurrence, so an exposed occurrence that answered with the recorded
     * one's id would mint the recorded occurrence's root, and a world that
     * planted the one would be stated for both.  So the static half is kept,
     * the id is spelled from the exposed occurrence with no ordinal, and
     * every member the recording stated -- the ordinal, the value, the
     * event, the call and the request it ran under -- is dropped.  Null for
     * an accessor return, which needs a recorded receiver.</p>
     */
    public static JsonObject exposedPort(JsonObject recorded, String regionId,
                                         String occurrenceId) {
        if (StaticScopeMap.ACCESSOR_RETURN.equals(
                optionalString(recorded, "sourceKind"))) {
            return null;
        }
        JsonObject port = recorded.deepCopy();
        for (String member : new String[] {"replayOccurrence",
                PRIMITIVE_VALUE, EVENT_SEQ, CALL_ID, SOURCE_KEY, REQUEST_KEY,
                REQUEST_API}) {
            port.remove(member);
        }
        String portId = portId(regionId, occurrenceId + "\n"
                + optionalString(recorded, SiteId.MEMBER));
        port.addProperty("portId", portId);
        port.addProperty("symbol", portId);
        port.addProperty("occurrenceId", occurrenceId);
        port.addProperty("observed", false);
        return port;
    }

    /** One port's id: its region and the key that names it there. */
    private static String portId(String regionId, String key) {
        return regionId + ".in." + UUID.nameUUIDFromBytes(
                (regionId + "\n" + key).getBytes(StandardCharsets.UTF_8));
    }

    /** The members every declared port takes from the scope map alone. */
    private static JsonObject staticPort(RegionInstancePlan plan,
                                         StaticScopeMap.Site site,
                                         String key) {
        String regionId = plan.regionId();
        String portId = portId(regionId, key);
        JsonObject port = new JsonObject();
        port.addProperty("portId", portId);
        port.addProperty("symbol", portId);
        port.addProperty("occurrenceId", plan.occurrenceId());
        port.addProperty("cell", site.cell);
        port.addProperty("javaType", site.declared.javaType);
        port.addProperty(DECLARED_CALLEE, site.declaredCallee);
        port.addProperty(SiteId.MEMBER, site.siteId);
        port.addProperty("staticAccessSiteId", site.siteId);
        port.addProperty("unitIndex", SiteId.unitIndexOf(site.siteId));
        port.addProperty("callerMethod", SiteId.methodOf(site.siteId));
        port.addProperty("dependencyRole", DependencyRole.VALUE_FRONTIER);
        port.addProperty("transportKind", "ACTIVATION_LOCAL");
        return port;
    }

    private static void dependencyCells(JsonObject port,
                                        StaticScopeMap.Site site) {
        JsonArray dependencyCells = new JsonArray();
        dependencyCells.add(site.declared.dependencyCell);
        port.add("dependencyCells", dependencyCells);
    }

    /**
     * A structural getter's return.  What the replay presents is the FIELD
     * the getter reads, at the receiver the call ran on, so the port carries
     * the field's own declaration and the recorded receiver identity.
     */
    private void accessorPort(JsonObject port, StaticScopeMap.Site site,
                              String caller, String regionId) {
        StaticScopeMap.Declared declared = site.declared;
        FieldPathSpec.DeclaredField field =
                FieldPathSpec.declaredField(site.cell);
        if (field == null) {
            throw new IllegalArgumentException("DECLARED_SITE "
                    + StaticScopeMap.ACCESSOR_RETURN
                    + " names no declared field: " + site.cell);
        }
        port.addProperty("sourceKind", StaticScopeMap.ACCESSOR_RETURN);
        port.addProperty("rootKind", "OBSERVED_FIELD_RECEIVER");
        port.addProperty("regionId", regionId);
        port.addProperty(SOURCE_KEY, rootSourceKey);
        port.addProperty("declaredFieldSignature", site.cell);
        port.addProperty("accessorImplementationMethod",
                declared.implementationMethod);
        port.addProperty("authority",
                "EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1");
        port.addProperty("accessorOccurrence", ordinal);
        // The occurrence's own returns at this site are what this port
        // addresses, so under that bound it is the first of them.
        port.addProperty("helperActivationBoundedOccurrence", 1);
        port.addProperty(ROOT_CALL_ID, rootCallId);
        port.addProperty(INVOCATION_ID, invocationId);
        port.addProperty("rootObjectId", receiverObjectId);
        port.addProperty(RECEIVER_OBJECT_ID, receiverObjectId);
        port.addProperty("fieldReceiverObjectId", receiverObjectId);
        port.addProperty("objectId", receiverObjectId);
        port.addProperty(RECEIVER_RUNTIME_TYPE, receiverRuntimeType);
        if (valueObjectId != 0) {
            port.addProperty(VALUE_OBJECT_ID, valueObjectId);
        }
        JsonArray path = new JsonArray();
        path.add(field.name());
        port.add("fieldPath", path);
        JsonArray declarations = new JsonArray();
        declarations.add(site.cell);
        port.add("fieldPathDeclarations", declarations);
        // The one path this port materializes, as every materialized port
        // states it: the task row drops it again where it is exactly the
        // single `fieldPath` (ExecutionTask#compactInputActions), but the
        // task's own port-set identity is taken over the port as planned.
        JsonArray paths = new JsonArray();
        JsonArray only = new JsonArray();
        only.add(field.name());
        paths.add(only);
        port.add("fieldPaths", paths);
        JsonArray accessSites = new JsonArray();
        accessSites.add(siteId);
        port.add("accessSites", accessSites);
        port.addProperty("accessFieldSignature", site.cell);
        port.addProperty("leafFieldSignature", site.cell);
        port.addProperty("accessorCallerMethod", caller);
        port.addProperty("accessorCallUnitIndex",
                SiteId.unitIndexOf(siteId));
        port.addProperty("accessorDeclaredCallee", declaredCallee);
        port.addProperty("location", "HEAP_OBJECT_FIELD");
    }

    /**
     * An external call's return: the local it lands in is the port.  The
     * one callee the workload declares in its own text, the fault marker
     * ({@code Debug.makeSymbolicBoolean}), is stamped as such: its
     * {@code boolean} local is the MARKER root the replay flips.
     */
    private static void callReturnPort(JsonObject port,
                                       StaticScopeMap.Site site) {
        String caller = SiteId.methodOf(site.siteId);
        port.addProperty("sourceKind",
                Debug.isBooleanMarkerSignature(site.declaredCallee)
                        ? RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                        : RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN);
        port.addProperty("rootKind", "CALL_RETURN");
        port.addProperty("method", caller);
        port.addProperty("rootMethod", caller);
        port.addProperty("definitionMethod", caller);
        port.addProperty("definitionUnitIndex",
                SiteId.unitIndexOf(site.siteId));
        port.addProperty("location", "CALL_RETURN");
    }
}
