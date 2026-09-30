import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Views and wrappers are their container.
 *
 * <p>A wrapper the program builds ({@code Collections.unmodifiableMap}) and a
 * key view ({@code keySet()}) stored into a tracked reference cell state
 * their backing map's container state ({@code referentState}), not one of
 * their own: one logical container, one location.  A query through a
 * wrapper reaches the model at the inner call and binds to the map's
 * location; a query through a ConcurrentHashMap's keySet() does too, and
 * keeps the read of the cell that held the view as its owner -- a read of a
 * reference cell is its own owner, whatever the object it returned.</p>
 */
public final class RegionWrapperViewSmoke {
    private static final class Holder {
        Map<String, Integer> published;
        Set<String> names;
    }

    private static final class Input {
        String name = "alpha";
    }

    private static final class Sink {
        Integer value;
        boolean present;
    }

    public static void main(String[] args) {
        Holder holder = new Holder();
        Map<String, Integer> backing = new HashMap<>();
        backing.put("alpha", 1);
        backing.put("beta", 2);
        ConcurrentHashMap<String, Integer> index = new ConcurrentHashMap<>();
        index.put("alpha", 3);

        require(System.startConcolicRegion("REGION.wrapper-view",
                "TASK.wrapper-view") == 0L, "region start rejected");
        require(System.observeField(holder, Holder.class.getName(),
                "published", "Ljava/util/Map;") == 0, "observation failed");
        require(System.observeField(holder, Holder.class.getName(), "names",
                "Ljava/util/Set;") == 0, "observation failed");
        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(), "name",
                "Ljava/lang/String;", "NAME");

        // Stored wrappers and views state their backing map.
        holder.published = Collections.unmodifiableMap(backing);
        holder.names = index.keySet();
        String published = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "published", "Ljava/util/Map;");
        String names = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "names", "Ljava/util/Set;");
        String backingLog = System.getSharedMapVersions(backing);
        String indexLog = System.getSharedMapVersions(index);

        // Queries through the wrapper and through the view.
        Sink sink = new Sink();
        sink.value = holder.published.get(input.name);
        String throughWrapper = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "value", "Ljava/lang/Integer;",
                sink.value);
        sink.present = holder.names.contains(input.name);
        String throughView = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "present", "Z",
                Boolean.valueOf(sink.present));
        System.endConcolic();

        System.out.println("PUBLISHED " + published);
        System.out.println("BACKING " + backingLog);
        System.out.println("WRAPPER " + throughWrapper);
        System.out.println("VIEW " + throughView);

        String backingOwner = member(backingLog, "\"ownerSymRid\":");
        String indexOwner = member(indexLog, "\"ownerSymRid\":");
        require(published.contains("\"referentState\":{\"ownerSymRid\":"
                        + backingOwner + ",")
                        && backingLog.contains("\"initialSnapshot\":{"
                                + "\"stated\":true,\"entries\":2,"),
                "the wrapper does not state its backing map: " + published
                        + " / " + backingLog);
        require(names.contains("\"referentState\":{\"ownerSymRid\":"
                        + indexOwner + ",")
                        && indexLog.contains("\"initialSnapshot\":{"
                                + "\"stated\":true,\"entries\":1,"),
                "the key view does not state its map: " + names + " / "
                        + indexLog);
        require(throughWrapper.contains("\"operation\":\"READ\"")
                        && throughWrapper.contains("\"ownerSymRid\":"
                                + backingOwner + ","),
                "the wrapper's query is not its map's: " + throughWrapper);
        require(throughView.contains("\"operation\":\"CONTAINS\"")
                        && throughView.contains("\"ownerSymRid\":"
                                + indexOwner + ",")
                        && throughView.contains("\"owner\":{"),
                "the view's query is not its map's, or lost the read of"
                        + " its cell: " + throughView);
        System.out.println("CAUSYNTH_REGION_WRAPPER_VIEW_SMOKE_OK");
    }

    private static String member(String json, String key) {
        int at = json.indexOf(key);
        if (at < 0) return "<none>";
        int start = at + key.length();
        int end = start;
        while (end < json.length() && json.charAt(end) != ','
                && json.charAt(end) != '}') {
            end++;
        }
        return json.substring(start, end);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
