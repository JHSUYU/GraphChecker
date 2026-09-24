package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.text;

/**
 * The one execution-task catalog for declared, symbolic and concrete inputs.
 */
public final class InputActionCatalog {
    public static final String FIELD = "inputActions";
    /**
     * Marks an input the experiment's {@code symbolic-inputs.jsonl} named by
     * hand, as opposed to one an automatic mechanism proposed.
     *
     * <p>The replay reads it: a declared primitive source mints its root even
     * when the value arrives wrapped in a carrier over a constant, which is
     * the only way an experiment can say "the search starts at this field"
     * about a field nothing symbolic has reached yet.</p>
     */
    public static final String DECLARED_SYMBOLIC_ROOT =
            "declaredSymbolicRoot";
    /**
     * Marks an input the case declared to be a wall-clock read.
     *
     * <p>A clock is the one root kind the composer moves differently -- it
     * rides an offset from what the recording read rather than a value of its
     * own -- so which reads are clocks has to be stated, not recognised.  The
     * case says so on the {@code symbolic-inputs.jsonl} row that declares the
     * cell; the planner copies the flag onto the action, the replay reads it
     * off the action, and the mint row states it for the composer.  Nothing
     * matches a callee name against a list.</p>
     */
    public static final String DECLARED_WALL_CLOCK = "clock";

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
