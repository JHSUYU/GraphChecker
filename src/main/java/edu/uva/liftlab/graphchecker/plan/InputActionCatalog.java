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
    /** Input a root category names ({@code StaticScopeMap}'s clocks and READ
     *  placeholders).  Such a primitive source mints its root even when
     *  wrapped in a carrier over a constant, so the search can start at a
     *  field nothing symbolic reached. */
    public static final String DECLARED_SYMBOLIC_ROOT =
            "declaredSymbolicRoot";
    /** Input that is a clock's reading, stating its tick in nanoseconds.
     *  The composer moves a clock by an offset from the recorded read, so
     *  the tick rides on the input row and no later stage recognises a
     *  clock, or its unit, again. */
    public static final String DECLARED_WALL_CLOCK = "clock";
    /** The JVM clock a clock input wraps ({@code contract.Clock#source}),
     *  beside its tick: the two are one clock's identity. */
    public static final String DECLARED_CLOCK_SOURCE = "clockSource";
    /** Input that is a configuration getter's return, stating the root it
     *  is ({@code CONFIG:<key>}): every read of one key is one symbol. */
    public static final String DECLARED_CONFIG_SOURCE = "configSource";
    /** A configuration input's static domain bounds, beside its source. */
    public static final String DECLARED_DOMAIN_MIN = "domainMin";
    public static final String DECLARED_DOMAIN_MAX = "domainMax";
    /** Input that is a fault marker's return, stating the marker's name
     *  ({@code FAULT:<TRANSPORT>:<DIRECTION>[:<Kind>]}): the replay that
     *  answers it {@code true} knows which door failed. */
    public static final String DECLARED_FAULT_MARKER = "marker";

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

    /** The catalog's own rows (read-only); {@link #symbolic()} aliases them. */
    public JsonArray all() { return all; }

    /** The {@code SYMBOLIC} rows of {@link #all()}, aliased, never copied. */
    public JsonArray symbolic() { return symbolic; }
}
