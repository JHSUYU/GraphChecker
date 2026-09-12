import java.util.ArrayList;
import java.util.List;

/**
 * Contract smoke for a String argument this session leaves unshadowed.
 *
 * <p>An interned String deliberately cannot carry a symbolic id in its
 * shared oop header, so no shadow is allocated for it.  What it does have is
 * the value this execution recorded, and naming that value costs nothing.
 * The untracked placeholder named neither the object nor its content: every
 * such argument serialized as one and the same {@code P_L'java/lang/String'_}
 * spelling, so distinct Strings were indistinguishable and each one reached
 * a formula as a root no symbolization event had declared.</p>
 */
public final class RegionUnshadowedStringArgumentSmoke {
    private static final class State {
        private final List<Object> rows = new ArrayList<Object>();
    }

    public static void main(String[] args) {
        State state = new State();

        require(System.startConcolicRegion(
                "REGION.unshadowed-string", "TASK.unshadowed-string") == 0L,
                "region start rejected");
        System.symbolizeField(state, "rows", "string_arg_rows");

        // Two distinct interned Strings, neither of which is shadowed.
        state.rows.add("supergroup");
        state.rows.add("ZhenyuLi");

        String relation = System.getSymbolicExpression(state.rows);
        System.endConcolic();

        // Each argument names its own content, so the two are distinct.
        require(relation.contains("ConStringSymbolExp"), relation);
        require(relation.contains("supergroup"), relation);
        require(relation.contains("ZhenyuLi"), relation);
        require(relation.indexOf("supergroup")
                != relation.indexOf("ZhenyuLi"),
                "two distinct Strings must not share one spelling");
        // And no argument is left as the anonymous placeholder.
        require(!relation.contains("P_L'java/lang/String'"),
                "an unshadowed String must not stay an untracked "
                        + "placeholder: " + relation);

        System.out.println(
                "CAUSYNTH_REGION_UNSHADOWED_STRING_ARGUMENT_SMOKE_OK");
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
