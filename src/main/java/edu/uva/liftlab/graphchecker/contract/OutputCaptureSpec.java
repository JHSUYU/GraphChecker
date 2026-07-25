package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** One canonical output endpoint captured by a scheduled execution task. */
public final class OutputCaptureSpec {
    public enum Kind {
        CALL_ARGUMENT,
        REGION_EXIT_FIELD
    }

    private final JsonObject encoded;
    private final Kind kind;
    private final String captureBindingId;
    private final String outputPort;
    private final String outputCell;
    private final String callerMethod;
    private final int unitIndex;
    private final String siteId;
    private final String calleeMethod;
    private final int argumentIndex;
    private final int occurrence;
    private final String accessRootInputPort;
    private final List<String> fieldPath;
    private final String fieldSignature;
    private final String javaType;

    static OutputCaptureSpec decodeValidated(JsonObject encoded) {
        return new OutputCaptureSpec(encoded);
    }

    private OutputCaptureSpec(JsonObject encoded) {
        this.encoded = encoded.deepCopy();
        try {
            kind = Kind.valueOf(string(encoded, "captureKind"));
        } catch (RuntimeException invalid) {
            throw new IllegalArgumentException(
                    "captureKind must be CALL_ARGUMENT or "
                            + "REGION_EXIT_FIELD");
        }
        captureBindingId = string(encoded, "captureBindingId");
        outputPort = string(encoded, "outputPort");
        outputCell = string(encoded, "outputCell");
        callerMethod = string(encoded, "callerMethod");
        unitIndex = integer(encoded, "unitIndex", -1);
        siteId = string(encoded, "siteId");
        calleeMethod = string(encoded, "calleeMethod");
        argumentIndex = integer(encoded, "argumentIndex", -1);
        occurrence = integer(encoded, "occurrence", 0);
        accessRootInputPort = string(encoded, "accessRootInputPort");
        fieldPath = Collections.unmodifiableList(new ArrayList<>(
                FieldPathSpec.stringArray(encoded, "fieldPath")));
        fieldSignature = string(encoded, "fieldSignature");
        javaType = string(encoded, "javaType");
    }

    public Kind kind() {
        return kind;
    }

    public String captureBindingId() {
        return captureBindingId;
    }

    public String outputPort() {
        return outputPort;
    }

    public String outputCell() {
        return outputCell;
    }

    public String callerMethod() {
        return callerMethod;
    }

    public int unitIndex() {
        return unitIndex;
    }

    public String siteId() {
        return siteId;
    }

    public String calleeMethod() {
        return calleeMethod;
    }

    public int argumentIndex() {
        return argumentIndex;
    }

    public int occurrence() {
        return occurrence;
    }

    public String accessRootInputPort() {
        return accessRootInputPort;
    }

    public List<String> fieldPath() {
        return fieldPath;
    }

    public String fieldSignature() {
        return fieldSignature;
    }

    public String javaType() {
        return javaType;
    }

    public boolean matchesCallArgument(
            String caller, int unit, String site, String callee, int argument,
            String port, String cell, String binding,
            int requestedOccurrence) {
        return kind == Kind.CALL_ARGUMENT
                && callerMethod.equals(value(caller))
                && unitIndex == unit
                && siteId.equals(value(site))
                && calleeMethod.equals(value(callee))
                && argumentIndex == argument
                && outputPort.equals(value(port))
                && outputCell.equals(value(cell))
                && captureBindingId.equals(value(binding))
                && occurrence == requestedOccurrence;
    }

    public boolean matchesRegionExitField(
            String binding, String port, String cell, String field) {
        return kind == Kind.REGION_EXIT_FIELD
                && captureBindingId.equals(value(binding))
                && outputPort.equals(value(port))
                && outputCell.equals(value(cell))
                && fieldSignature.equals(value(field));
    }

    public JsonObject toJson() {
        return encoded.deepCopy();
    }

    private static String value(String value) {
        return value == null ? "" : value;
    }
}
