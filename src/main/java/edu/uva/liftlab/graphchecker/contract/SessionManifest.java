package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * CONTRACT-SPEC 2: the role one session states it ran as ({@code
 * manifest.json}, written when the session opens) -- the only answer to
 * "which session is the recording".  Never inferred from activations: a
 * FOCUSED replay that activated nothing is still FOCUSED.
 */
public final class SessionManifest {
    /** What a session ran as: the recording, or one counterfactual of it. */
    public enum Role { SEED, FOCUSED }

    public static final String KIND = "SESSION_MANIFEST";

    private final String sessionId;
    private final Role role;
    private final List<String> obligationIds;

    private SessionManifest(String sessionId, Role role,
                            List<String> obligationIds) {
        this.sessionId = sessionId;
        this.role = role;
        this.obligationIds = Collections.unmodifiableList(obligationIds);
    }

    /** Obligation ids come from the worker's {@code focused_task.jsonl}. */
    public static SessionManifest of(String sessionId, Role role,
                                     List<String> obligationIds) {
        List<String> ids = new ArrayList<String>();
        if (obligationIds != null) {
            for (String id : obligationIds) {
                String stated = Fields.text(id, "obligationId");
                if (!ids.contains(stated)) ids.add(stated);
            }
        }
        return new SessionManifest(Fields.text(sessionId, "sessionId"),
                Fields.required(role, "role"), ids);
    }

    public String sessionId() {
        return sessionId;
    }

    public Role role() {
        return role;
    }

    /** Whether this session states it is the recording. */
    public boolean seed() {
        return role == Role.SEED;
    }

    /** The obligations this replay was handed, in the focus row's order. */
    public List<String> obligationIds() {
        return obligationIds;
    }

    public JsonObject toJson() {
        JsonObject json = new JsonObject();
        json.addProperty("schemaVersion", 1);
        json.addProperty("kind", KIND);
        json.addProperty("sessionId", sessionId);
        json.addProperty("role", role.name());
        JsonArray ids = new JsonArray();
        for (String id : obligationIds) {
            ids.add(id);
        }
        json.add("obligationIds", ids);
        return json;
    }

    /** Reads one manifest; an absent or unknown role is refused, never SEED. */
    public static SessionManifest fromJson(JsonObject json) {
        String role = JsonFields.optionalString(json, "role");
        Role parsed;
        try {
            parsed = Role.valueOf(role);
        } catch (IllegalArgumentException unstated) {
            throw new IllegalArgumentException(
                    "manifest states no role this contract has: \"" + role
                            + "\"");
        }
        return of(JsonFields.optionalString(json, "sessionId"), parsed,
                JsonFields.strings(json, "obligationIds"));
    }

    @Override
    public String toString() {
        return role + " " + sessionId
                + (obligationIds.isEmpty() ? "" : " " + obligationIds);
    }
}
