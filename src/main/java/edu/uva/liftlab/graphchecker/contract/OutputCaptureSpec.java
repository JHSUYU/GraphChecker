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
    private final String accessRootInputPort;
    private final List<String> fieldPath;
    private final String fieldSignature;

    static OutputCaptureSpec decodeValidated(JsonObject encoded) {
        return new OutputCaptureSpec(encoded);
    }

    private OutputCaptureSpec(JsonObject encoded) {
        captureBindingId = string(encoded, "captureBindingId");
        outputPort = string(encoded, "outputPort");
        accessRootInputPort = string(encoded, "accessRootInputPort");
        fieldPath = Collections.unmodifiableList(new ArrayList<>(
                FieldPathSpec.stringArray(encoded, "fieldPath")));
        fieldSignature = string(encoded, "fieldSignature");
    }

    public String captureBindingId() {
        return captureBindingId;
    }

    public String outputPort() {
        return outputPort;
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

}
