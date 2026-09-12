import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

/**
 * Contract smoke for an indexed container carried whole.
 *
 * <p>A List field versioned as a reference slot publishes one write for its
 * construction and nothing at all for any later add or remove, so the
 * contents a reader observes are unconstrained.  Selected as a whole-state
 * carrier it publishes one immutable state per mutation, spelled at the same
 * {@code MAP_STATE} whole-state slot a map uses, with the indexed algebra's
 * own operations.</p>
 */
public final class RegionIndexedCarrierApiSmoke {
    private static final class State {
        private final List<Object> rows = new ArrayList<Object>();
    }

    public static void main(String[] args) {
        State state = new State();
        state.rows.add(new Object());

        require(System.startConcolicRegion(
                "REGION.indexed-carrier", "TASK.indexed-carrier") == 0L,
                "region start rejected");
        System.symbolizeField(state, "rows", "indexed_input_rows");

        require(System.selectSharedMapCarrier(state.rows) > 0L,
                "indexed carrier selection rejected");
        require(System.selectSharedMapCarrier(state.rows) == 0L,
                "indexed carrier selection is not idempotent");

        // One version per mutation, in the indexed algebra's own vocabulary.
        state.rows.add(new Object());                 // APPEND
        state.rows.add(1, new Object());              // INSERT
        state.rows.set(0, new Object());              // WRITE
        state.rows.remove(2);                         // REMOVE
        require(state.rows.size() == 2,
                "concrete list diverged: " + state.rows.size());

        String evidence = System.getSharedMapVersions(state.rows);
        require(evidence.contains("\"selected\":true"), evidence);
        require(evidence.contains("\"writerSetComplete\":true"), evidence);
        // The whole-state spelling is one slot for every shape.
        require(evidence.contains("\"locationKind\":\"MAP_STATE\""),
                evidence);
        require(evidence.contains("\"slot\":-3"), evidence);
        // Selecting publishes the state the list started in, so the state a
        // read observes before any tracked mutation is an ordinary candidate.
        require(evidence.contains("\"versionKind\":\"INITIAL\""), evidence);
        require(evidence.contains("\"versionKind\":\"STATE_APPEND\""),
                evidence);
        require(evidence.contains("\"versionKind\":\"STATE_INSERT\""),
                evidence);
        require(evidence.contains("\"versionKind\":\"STATE_WRITE\""),
                evidence);
        require(evidence.contains("\"versionKind\":\"STATE_REMOVE\""),
                evidence);
        require(count(evidence, "\"fieldVersionId\"") == 5,
                "one version per mutation plus the initial: " + evidence);
        // Each version carries the relation that produced it, so the size of
        // the state it names is closed-form in the chain below it.
        require(evidence.contains("\"shape\":\"INDEXED\""), evidence);
        require(evidence.contains("\"operation\":\"INSERT\""), evidence);
        require(evidence.contains("\"operation\":\"REMOVE\""), evidence);

        // A truncating mutation is a state like any other.
        state.rows.clear();
        String cleared = System.getSharedMapVersions(state.rows);
        require(cleared.contains("\"versionKind\":\"STATE_CLEAR\""), cleared);
        require(count(cleared, "\"fieldVersionId\"") == 6, cleared);

        // A read of the selected list resolves over the retained writer
        // states rather than being pinned to the one value this run returned.
        int size = state.rows.size();
        require(size == 0, "concrete size diverged: " + size);
        String read = System.getSharedMapVersions(state.rows);
        require(read.contains("\"readEventId\""), read);

        System.endConcolic();

        // What is refused, and refused by name rather than selected and then
        // silently never versioned.
        require(System.startConcolicRegion(
                "REGION.indexed-refusal", "TASK.indexed-refusal") == 0L,
                "second region start rejected");
        Object[] array = new Object[2];
        require(System.selectSharedMapCarrier(array) == -4L,
                "an array must keep its own element locations");
        // A set has the associative whole-state algebra and a model that
        // publishes its ADD/REMOVE/CLEAR states, so the VM selects it.  What
        // declines to version a set whole is the Java classifier that decides
        // which fields are declared as carriers at all.
        require(System.selectSharedMapCarrier(new HashSet<Object>()) > 0L,
                "a modeled set has the whole-state algebra");
        require(System.selectSharedMapCarrier(new Object()) == -4L,
                "a non-container must not be selectable");
        System.endConcolic();

        System.out.println("CAUSYNTH_REGION_INDEXED_CARRIER_API_SMOKE_OK");
    }

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
