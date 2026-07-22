package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

/** Immutable selector for the initial, unforced capture of a target branch. */
public final class BranchCaptureSelector {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BINARY_BRANCH_CAPTURE_SELECTOR";

    private final String siteId;
    private final int occurrence;
    private final boolean desiredOutcome;

    private BranchCaptureSelector(String siteId, int occurrence,
                                  boolean desiredOutcome) {
        if (siteId == null || siteId.trim().isEmpty() || occurrence < 1) {
            throw new IllegalArgumentException(
                    "capture selector requires a site and occurrence");
        }
        this.siteId = siteId.trim();
        this.occurrence = occurrence;
        this.desiredOutcome = desiredOutcome;
    }

    public static BranchCaptureSelector of(String siteId, int occurrence,
                                           boolean desiredOutcome) {
        return new BranchCaptureSelector(siteId, occurrence, desiredOutcome);
    }

    public JsonObject toJson() {
        return coreJson();
    }

    public String siteId() {
        return siteId;
    }

    public int occurrence() {
        return occurrence;
    }

    public boolean desiredOutcome() {
        return desiredOutcome;
    }

    private JsonObject coreJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("siteId", siteId);
        result.addProperty("occurrence", occurrence);
        result.addProperty("desiredOutcome", desiredOutcome);
        return result;
    }

}
