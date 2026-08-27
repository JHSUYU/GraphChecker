package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.text;

/**
 * The one execution-task catalog for declared, symbolic and concrete inputs.
 */
public final class InputActionCatalog {
    public static final String FIELD = "inputActions";

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

    /** The catalog's own rows, not a copy: {@code decode} already isolated
     *  them from the task json and {@link #symbolic()} aliases the same
     *  objects, so a consumer reads them and never writes. */
    public JsonArray all() { return all; }

    /** The {@code SYMBOLIC} rows of {@link #all()}, aliased, never copied. */
    public JsonArray symbolic() { return symbolic; }
}
