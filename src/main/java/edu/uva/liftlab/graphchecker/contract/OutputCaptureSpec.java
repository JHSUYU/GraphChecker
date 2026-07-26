package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** One canonical output endpoint captured by a scheduled execution task. */
public final class OutputCaptureSpec {
    private final String captureBindingId;
    private final String outputPort;
    private final String outputCell;
    private final String accessRootInputPort;
    private final List<String> fieldPath;
    private final String fieldSignature;
    private final String javaType;

    static OutputCaptureSpec decodeValidated(JsonObject encoded) {
        return new OutputCaptureSpec(encoded);
    }

    private OutputCaptureSpec(JsonObject encoded) {
        captureBindingId = string(encoded, "captureBindingId");
        outputPort = string(encoded, "outputPort");
        outputCell = string(encoded, "outputCell");
        accessRootInputPort = string(encoded, "accessRootInputPort");
        fieldPath = Collections.unmodifiableList(new ArrayList<>(
                FieldPathSpec.stringArray(encoded, "fieldPath")));
        fieldSignature = string(encoded, "fieldSignature");
        javaType = string(encoded, "javaType");
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

    public boolean matchesRegionExitField(
            String binding, String port, String cell, String field) {
        return captureBindingId.equals(value(binding))
                && outputPort.equals(value(port))
                && outputCell.equals(value(cell))
                && fieldSignature.equals(value(field));
    }

    private static String value(String value) {
        return value == null ? "" : value;
    }
}
