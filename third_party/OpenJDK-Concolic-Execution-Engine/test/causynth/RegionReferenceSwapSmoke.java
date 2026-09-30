import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A reference field re-pointed at a fresh container: SOLR-18406's
 * {@code IndexDeletionPolicyWrapper.knownCommits}, a volatile Map every
 * commit replaces with a new ConcurrentHashMap.
 *
 * <p>The field is observed ({@code System.observeField}): its INITIAL is the
 * referent's identity, and its word the referent's session id, so a read of
 * it verifies itself like a scalar's.  The store that swaps in the new map
 * states the map's container state at the store ({@code referentState}):
 * the map had no log, so the store started one with a stated snapshot, and
 * names that INITIAL.  A read states the identity it returned.  A store no
 * hook saw -- here one made while recording is paused -- is found by the
 * next read's word, as an UNOBSERVED version of the loaded referent.  A
 * static reference field is observed on its class.  A query through the
 * field's read keeps the read as its {@code owner}.</p>
 */
public final class RegionReferenceSwapSmoke {
    private static final class Holder {
        volatile Map<Long, String> commits;
    }

    private static final class Registry {
        static Map<String, String> byName = new ConcurrentHashMap<>();
    }

    private static final class Measures {
        double ratio;
    }

    private static final class Input {
        long generation = 7L;
    }

    private static final class Sink {
        Map<Long, String> commits;
        Map<String, String> byName;
        String commit;
    }

    private static final String MAP = "Ljava/util/Map;";

    public static void main(String[] args) {
        Holder holder = new Holder();
        ConcurrentHashMap<Long, String> first = new ConcurrentHashMap<>();
        first.put(5L, "five");
        holder.commits = first;

        require(System.startConcolicRegion("REGION.reference-swap",
                "TASK.reference-swap") == 0L, "region start rejected");
        require(System.observeField(holder, Holder.class.getName(),
                "commits", MAP) == 0, "the reference observation failed");
        require(System.observeField(holder, Holder.class.getName(),
                "missing", MAP) == -3, "a missing field was observed");
        require(System.observeField(new Measures(), Measures.class.getName(),
                "ratio", "D") == -12, "a double was observed");
        require(System.observeField(Registry.class, Registry.class.getName(),
                "byName", MAP) == 0, "the static observation failed");

        // The writer builds a fresh map and swaps it in.
        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(),
                "generation", "J", "GENERATION");
        ConcurrentHashMap<Long, String> second = new ConcurrentHashMap<>();
        for (long generation = 5L; generation <= 8L; generation++) {
            second.put(generation, "g" + generation);
        }
        holder.commits = second;

        // The reader: the swap's version, exactly, and what it returned.
        Sink sink = new Sink();
        sink.commits = holder.commits;
        String read = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "commits", MAP, sink.commits);
        sink.byName = Registry.byName;
        String staticRead = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "byName", MAP, sink.byName);

        // A query through the read keeps the read as its owner.
        sink.commit = holder.commits.get(input.generation);
        String query = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "commit", "Ljava/lang/String;",
                sink.commit);

        // A store no hook sees, found by the next read's word.
        System.pauseConcolicPathCondition();
        holder.commits = new ConcurrentHashMap<>();
        System.resumeConcolicPathCondition();
        sink.commits = holder.commits;
        String unobserved = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "commits", MAP, sink.commits);

        String field = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "commits", MAP);
        String map = System.getSharedMapVersions(second);
        System.endConcolic();

        System.out.println("FIELD " + field);
        System.out.println("MAP " + map);
        System.out.println("READ " + read);
        System.out.println("QUERY " + query);

        // INITIAL: the first map's identity; WRITE: the second's, with the
        // second map's state at the store.
        require(field.contains("\"versionKind\":\"INITIAL\"")
                        && field.contains("\"versionKind\":\"WRITE\"")
                        && field.contains("_exp\":\"M_L'java/util/concurrent"
                                + "/ConcurrentHashMap'_"),
                "the field's versions are not the two identities: " + field);
        String state = member(field, "\"referentState\":");
        require(state != null
                        && state.contains("\"locationKind\":\"MAP_STATE\"")
                        && state.contains("\"slot\":-3"),
                "the swap states no referent state: " + field);
        String owner = member(state, "\"ownerSymRid\":");
        String version = member(state, "\"fieldVersionId\":");
        require(map.contains("\"ownerSymRid\":" + owner + ",")
                        && map.contains("\"fieldVersionId\":" + version + ",")
                        && map.contains("\"versionKind\":\"INITIAL\"")
                        && map.contains("\"initialSnapshot\":{\"stated\":true,"
                                + "\"entries\":4,"),
                "the referent state does not name the map's stated INITIAL: "
                        + state + " / " + map);

        require(read.contains("\"_type\":\"ReadFromExpression\"")
                        && read.contains("\"observedExact\":true")
                        && read.contains("\"concreteValue\":{\"_type\":"
                                + "\"VmExpressionReference\""),
                "the read is not exact or states no identity: " + read);
        require(staticRead.contains("\"locationKind\":\"STATIC_FIELD\"")
                        && staticRead.contains("\"observedExact\":true"),
                "the static field is not observed: " + staticRead);
        require(query.contains("\"operation\":\"READ\"")
                        && query.contains("\"owner\":{\"_type\":"
                                + "\"VmExpressionReference\""),
                "the query lost the read it went through: " + query);
        require(unobserved.contains("\"versionKind\":\"UNOBSERVED\"")
                        && unobserved.contains("\"unnamedWriter\":true")
                        && unobserved.contains("\"observedExact\":true"),
                "the unhooked store is not an UNOBSERVED referent: "
                        + unobserved);
        System.out.println("CAUSYNTH_REGION_REFERENCE_SWAP_SMOKE_OK");
    }

    // The value of `key` in `json` (to the next ',' or '}'), or the object it
    // opens.
    private static String member(String json, String key) {
        if (json == null) return null;
        int at = json.indexOf(key);
        if (at < 0) return null;
        int start = at + key.length();
        if (json.charAt(start) == '{') {
            int depth = 0;
            for (int end = start; end < json.length(); end++) {
                if (json.charAt(end) == '{') depth++;
                if (json.charAt(end) == '}' && --depth == 0) {
                    return json.substring(start, end + 1);
                }
            }
            return null;
        }
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
