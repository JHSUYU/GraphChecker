package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * CONTRACT-SPEC 2: the role one session STATES it ran as.
 *
 * <p>{@code manifest.json}, written by the runtime at the moment the session
 * is opened, and the only answer to "which session is the recording".  It
 * used to be inferred -- the seed was the session whose activations focused
 * nothing -- and the inference is wrong for two runs that nobody focused for
 * different reasons.  On the 11741 campaign #2 corpus nine of eighty-one
 * sessions focused nothing: the seed, seven replays the kill cut before their
 * focused occurrence activated, and one legitimately NOT_ADMITTED focused
 * replay whose focused occurrence never ran.  COMPOSE then refused "more than
 * one session of this corpus focused nothing, so which one is the recording
 * has no answer" and the anchor degraded to {@code Lost:UNKNOWN}.</p>
 *
 * <p>So every session states its role.  A FOCUSED replay that activated
 * nothing is still a FOCUSED replay -- what it settled is its result row's to
 * say, not the seed rule's -- and a corpus with no SEED session, or with two,
 * is a named refusal instead of a coin toss.</p>
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

    /**
     * One session's statement.
     *
     * <p>The obligation ids are the FOCUSED replay's own: the worker reads
     * them out of its {@code focused_task.jsonl}, so the manifest and the
     * result row name the same obligations and no reader has to guess a
     * worker from a directory name.</p>
     */
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

    /**
     * Reads one manifest, refusing a document that states no role.
     *
     * <p>Fail-closed by name: a manifest whose {@code role} is absent or is
     * a word this contract does not have states nothing, and reading it as
     * SEED is how an exploration replay becomes the recording.</p>
     */
    public static SessionManifest fromJson(JsonObject json) {
        if (json == null) {
            throw new IllegalArgumentException("manifest states no role");
        }
        JsonElement stated = json.get("role");
        String role = stated == null || stated.isJsonNull() ? ""
                : stated.getAsString();
        Role parsed;
        try {
            parsed = Role.valueOf(role);
        } catch (IllegalArgumentException | NullPointerException unstated) {
            throw new IllegalArgumentException(
                    "manifest states no role this contract has: \"" + role
                            + "\"");
        }
        JsonElement id = json.get("sessionId");
        List<String> obligations = new ArrayList<String>();
        JsonElement ids = json.get("obligationIds");
        if (ids != null && ids.isJsonArray()) {
            for (JsonElement each : ids.getAsJsonArray()) {
                obligations.add(each.getAsString());
            }
        }
        return of(id == null || id.isJsonNull() ? "" : id.getAsString(),
                parsed, obligations);
    }

    @Override
    public String toString() {
        return role + " " + sessionId
                + (obligationIds.isEmpty() ? "" : " " + obligationIds);
    }
}
