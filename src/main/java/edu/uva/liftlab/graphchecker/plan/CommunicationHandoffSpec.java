package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** One typed value capture at one side of a message boundary. */
public final class CommunicationHandoffSpec {
    public static final String FIELD = "communicationHandoffs";
    public static final String SIDE = "side";
    public static final String CAPTURE_KIND = "captureKind";
    public static final String OUT = "OUT";
    public static final String IN = "IN";

    private final String portId;
    private final String leafPath;
    private final String side;
    private final String captureKind;
    private final String method;
    private final String frameMethod;
    private final String declaredCallee;
    private final int unitIndex;
    private final int argumentIndex;

    private CommunicationHandoffSpec(JsonObject row) {
        portId = optionalString(row, CommunicationCatalogContract.PORT_ID);
        leafPath = optionalString(row,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH);
        String javaType = optionalString(row,
                CommunicationCatalogContract.PORT_JAVA_TYPE);
        side = optionalString(row, SIDE);
        captureKind = optionalString(row, CAPTURE_KIND);
        method = optionalString(row,
                CommunicationCatalogContract.PORT_DEFINITION_METHOD);
        frameMethod = optionalString(row,
                CommunicationCatalogContract.PORT_FRAME_METHOD);
        declaredCallee = optionalString(row,
                CommunicationCatalogContract.DECLARED_CALLEE);
        unitIndex = optionalInteger(row,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, -1);
        argumentIndex = optionalInteger(row,
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX, -1);
        if (portId.isEmpty() || leafPath.isEmpty() || javaType.isEmpty()
                || method.isEmpty()
                || !(OUT.equals(side) || IN.equals(side))
                || !validCapture()) {
            throw new IllegalArgumentException(
                    "invalid communication handoff: " + portId);
        }
    }

    private boolean validCapture() {
        if (CommunicationCatalogContract.CAPTURE_METHOD_PARAMETER.equals(
                captureKind)) {
            return unitIndex < 0 && argumentIndex >= 0
                    && declaredCallee.isEmpty();
        }
        if (CommunicationCatalogContract.CAPTURE_METHOD_RETURN.equals(
                captureKind)) {
            return unitIndex < 0 && argumentIndex < 0
                    && declaredCallee.isEmpty();
        }
        if (CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT.equals(
                captureKind)) {
            return unitIndex >= 0 && argumentIndex >= 0
                    && !declaredCallee.isEmpty();
        }
        return CommunicationCatalogContract.CAPTURE_CALL_RETURN.equals(
                captureKind) && unitIndex >= 0 && argumentIndex < 0
                && !declaredCallee.isEmpty();
    }

    public static List<CommunicationHandoffSpec> decode(JsonObject task) {
        if (task == null || !task.has(FIELD)) return Collections.emptyList();
        JsonElement encoded = task.get(FIELD);
        if (!encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "communication handoffs must be an array");
        }
        List<CommunicationHandoffSpec> sites = new ArrayList<>();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "communication handoff must be an object");
            }
            sites.add(new CommunicationHandoffSpec(element.getAsJsonObject()));
        }
        return Collections.unmodifiableList(sites);
    }

    public String portId() { return portId; }
    public String side() { return side; }
    public String captureKind() { return captureKind; }
    public String method() { return method; }

    /** Method whose one call builds one value of this port; "" = framed by its
     *  RPC. */
    public String frameMethod() { return frameMethod; }
    public String declaredCallee() { return declaredCallee; }
    public int unitIndex() { return unitIndex; }
    public int argumentIndex() { return argumentIndex; }
    public boolean outgoing() { return OUT.equals(side); }

    public String siteId() {
        return unitIndex < 0 ? method
                : SiteId.of(method, unitIndex);
    }

    @Override
    public String toString() {
        return side + " " + portId + " " + captureKind + "@" + siteId();
    }
}
