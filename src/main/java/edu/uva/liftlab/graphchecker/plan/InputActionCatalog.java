package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.text;

public final class InputActionCatalog {
    public static final String FIELD = "inputActions";
    public static final String DECLARED_SYMBOLIC_ROOT =
            "declaredSymbolicRoot";
    public static final String DECLARED_WALL_CLOCK = "clock";
    public static final String DECLARED_CLOCK_SOURCE = "clockSource";
    public static final String DECLARED_CONFIG_SOURCE = "configSource";
    public static final String DECLARED_DOMAIN_MIN = "domainMin";
    public static final String DECLARED_DOMAIN_MAX = "domainMax";
    public static final String DECLARED_FAULT_MARKER = "marker";
    public static final String DIGEST = "actionDigest";

    public enum Mode {
        SYMBOLIC, CONCRETE, DECLARATION_ONLY
    }

    private final JsonArray all;
    private final JsonArray symbolic;

    private InputActionCatalog(JsonArray all, JsonArray symbolic) {
        this.all = all;
        this.symbolic = symbolic;
    }

    public static InputActionCatalog decode(JsonObject task) {
        JsonElement encoded = task == null ? null : task.get(FIELD);
        if (encoded == null || !encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "execution task requires inputActions array");
        }
        JsonArray all = new JsonArray();
        JsonArray symbolic = new JsonArray();
        int index = 0;
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException("inputActions[" + index
                        + "] must be an object");
            }
            JsonObject action = element.getAsJsonObject();
            Mode mode;
            try {
                mode = Mode.valueOf(text(action, "mode"));
            } catch (IllegalArgumentException malformed) {
                throw new IllegalArgumentException("inputActions[" + index
                        + "] has unsupported mode");
            }
            JsonObject copy = action.deepCopy();
            all.add(copy);
            if (mode == Mode.SYMBOLIC) {
                symbolic.add(copy);
            }
            index++;
        }
        return new InputActionCatalog(all, symbolic);
    }

    public static JsonObject stamp(JsonObject action) {
        action.remove(DIGEST);
        action.addProperty(DIGEST, CanonicalJson.sha256(
                JsonParser.parseString(action.toString())));
        return action;
    }

    public JsonArray all() { return all; }

    public JsonArray symbolic() { return symbolic; }
}
