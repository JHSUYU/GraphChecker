import java.util.ArrayList;
import java.util.List;

/**
 * Contract smoke for an indexed container carried whole.
 *
 * <p>A List field versioned as a reference slot publishes one write for its
 * construction and nothing at all for any later add or remove, so the
 * contents a reader observes are unconstrained.  Versioned whole it publishes
 * one immutable state per mutation, spelled at the same {@code MAP_STATE}
 * whole-state slot a map uses, with the indexed algebra's own operations.
 * The log starts at the first symbolic touch of the container; nothing
 * declares it.</p>
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
        // The base the recorder walked before the first tracked mutation is
        // published as a version of its own, so the state a read observes
        // before any of them is an ordinary entry in the log.
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

        // A read of the list is logged against the location, so a later
        // question can say which states were live when it ran.
        int size = state.rows.size();
        require(size == 0, "concrete size diverged: " + size);
        String read = System.getSharedMapVersions(state.rows);
        require(read.contains("\"readEventId\""), read);

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
