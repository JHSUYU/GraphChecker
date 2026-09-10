import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * HDFS-11741 removal story, VM half: a removeExpiredKeys-shaped loop over a
 * symbolic map records each control-dependent {@code it.remove()} as a
 * {@code REMOVE_IF} op that carries the controlling branch predicate as a
 * {@code guard}, even when the branch is NOT taken on this run.
 *
 * The failure is a DataNode's {@code retrieveDataEncryptionKey(keyId)} finding
 * {@code allKeys.get(keyId) == null}.  There is no physical expiry on the
 * concrete run: {@code removeExpiredKeys} evaluates {@code if (expiry < now)},
 * the branch is false, and the key stays -- so {@code get} returns it and no
 * throw happens.  For a solver to reach the throw it must flip that branch.
 * The VM makes the branch flippable by recording, for the visited key, a
 * conditional removal
 *
 *   REMOVE_IF(receiver = prev map state, arguments = [keyId],
 *             guard = (expiry &lt; now))
 *
 * whose guard is oriented as the removal condition: concretely FALSE here (so
 * the key is present, matching the concrete map), and the exact predicate a
 * solver flips true to delete the key and drive {@code get} to null.  The
 * consuming half (ContainerSmtCodec, ContainerSmtCodecRemoveIfTest) is proven
 * SAT for the throw and unsat when the guard is forced false; this smoke pins
 * down the producing half.
 *
 * What it checks:
 *   1. the branch is NOT taken concretely -- the key remains in the map;
 *   2. a REMOVE_IF reuses the actual key object's semantic expression, while
 *      a key with no lineage uses a bounded concrete leaf rather than copying
 *      the iterator's whole map state;
 *   3. its guard is a real predicate naming the key's own symbolic expiry --
 *      the flippable branch -- and is the removal condition ("&lt;"), not the
 *      concrete branch's kept-arm;
 *   4. repeated entry-set passes grow the serialized expression linearly and
 *      retain every boxed primitive key symbol;
 *   5. an unconditional iterator remove (no marked controlling branch) still
 *      records the position-keyed REMOVE_AT, unchanged.
 */
public final class RegionConditionalRemovalApiSmoke {

    private static final int KEY_ID = 534995622;
    private static final int OTHER_KEY = 777;
    private static final long NOW = 50L;
    private static final String EXPIRY_SYMBOL = "rm_expiry_" + KEY_ID;

    private static final class Value {
        private long expiry;
        private Value(long expiry) { this.expiry = expiry; }
        private long getExpiryDate() { return expiry; }
    }

    private static final class KeySource {
        private int keyId;
        private KeySource(int keyId) { this.keyId = keyId; }
    }

    private static final class State {
        private final LinkedHashMap<Integer, Value> allKeys =
                new LinkedHashMap<Integer, Value>();
    }

    public static void main(String[] args) {
        conditionalRemovalIsRecordedOnTheNotTakenBranch(args);
        conditionalRemovalViaEntrySetIterator(args);
        symbolicEntryKeysStayLeafAndScaleLinearly();
        unconditionalRemoveStaysRemoveAt();
        System.out.println("CAUSYNTH_REGION_CONDITIONAL_REMOVAL_API_SMOKE_OK");
    }

    // (1)(2)(3) the removeExpiredKeys shape, branch not taken.
    private static void conditionalRemovalIsRecordedOnTheNotTakenBranch(
            String[] args) {
        State state = new State();
        // Target key is un-expired: 100 >= NOW, so `expiry < now` is false and
        // the key is NOT removed on this run.  A second, also-un-expired key
        // makes the target a non-final element so its disposition happens at
        // the following next() as well as at loop-exit hasNext().
        state.allKeys.put(KEY_ID, new Value(100L));
        state.allKeys.put(OTHER_KEY, new Value(200L));

        System.startConcolicRegion("REGION.remove-expired",
                "TASK.remove-expired");
        System.symbolizeField(state, "allKeys", "rm_map");
        for (Iterator<Integer> it = state.allKeys.keySet().iterator();
                it.hasNext();) {
            Integer keyId = it.next();
            Value value = state.allKeys.get(keyId);
            // Symbolize every occurrence: each element's expiry is its own
            // flippable symbol.
            System.symbolizeExactField(value, Value.class.getName(),
                    "expiry", "J", "rm_expiry_" + keyId);
            // The controlling branch, marked as a region control-flow site --
            // this is what turns the remove into a conditional one.
            System.markConcolicBranch("REMOVE.EXPIRED", keyId);
            if (value.expiry < NOW) {
                it.remove();
            }
        }
        String relation = System.getSymbolicExpression(state.allKeys);
        String summary = System.finishConcolicRegion();
        if (args.length > 0 && "--dump".equals(args[0])) {
            System.out.println(relation);
        }

        // (1) not taken concretely: the key is still present.
        require(state.allKeys.containsKey(KEY_ID),
                "the un-expired key must remain in the concrete map");
        require(relation.contains("\"operation\":\"REMOVE_IF\""),
                "no conditional removal was recorded: " + head(relation));

        // (2)(3) the REMOVE_IF for THIS key names it and guards on its expiry.
        String removeIf = removeIfGuardedBy(relation, EXPIRY_SYMBOL);
        require(removeIf != null,
                "no REMOVE_IF for key " + KEY_ID + ": " + head(relation));
        String arguments = valueOf(shallow(removeIf), "arguments");
        require(arguments != null
                        && reachableContains(relation, arguments,
                                "\"_exp\":\"Y_I_" + KEY_ID + "\"")
                        && !reachableContains(relation, arguments,
                                "\"operation\":\"NEXT\""),
                "the concrete fallback copied the iterator state: "
                        + head(String.valueOf(arguments)));
        String guard = valueOf(removeIf, "guard");
        require(guard != null,
                "the REMOVE_IF carries no guard: " + head(removeIf));
        require(reachableContains(relation, guard, EXPIRY_SYMBOL),
                "the guard does not name the key's expiry symbol "
                        + EXPIRY_SYMBOL + ": " + head(guard));
        // The guard is the removal condition (expiry < now).  Its top operator
        // is "<": recorded from the kept branch and negated back to the arm
        // under which the key would be gone.
        require(topOperatorIs(relation, guard, "<"),
                "the guard is not oriented as the removal condition (<): "
                        + head(guard));
    }

    // The exact Hadoop removeExpiredKeys shape: entrySet().iterator(), reading
    // e.getValue().getExpiryDate() and calling it.remove(), NEVER e.getKey().
    // The removed key is recovered from the entry node, so REMOVE_IF still
    // carries the map key as arguments[0].
    private static void conditionalRemovalViaEntrySetIterator(String[] args) {
        State state = new State();
        state.allKeys.put(KEY_ID, new Value(100L));   // un-expired: not removed
        state.allKeys.put(OTHER_KEY, new Value(200L));

        System.startConcolicRegion("REGION.remove-expired-entryset",
                "TASK.remove-expired-entryset");
        System.symbolizeField(state, "allKeys", "es_map");
        int occurrence = 0;
        for (Iterator<Map.Entry<Integer, Value>> it =
                state.allKeys.entrySet().iterator(); it.hasNext();) {
            Map.Entry<Integer, Value> e = it.next();
            // Only getValue() is touched -- getKey() is never called, exactly
            // as in BlockTokenSecretManager.removeExpiredKeys.
            System.symbolizeExactField(e.getValue(), Value.class.getName(),
                    "expiry", "J", "es_expiry_" + occurrence);
            System.markConcolicBranch("REMOVE.EXPIRED", ++occurrence);
            if (e.getValue().getExpiryDate() < NOW) {
                it.remove();
            }
        }
        String relation = System.getSymbolicExpression(state.allKeys);
        System.finishConcolicRegion();
        if (args.length > 0 && "--dump".equals(args[0])) {
            System.out.println(relation);
        }

        require(state.allKeys.containsKey(KEY_ID),
                "the un-expired entry-set key must remain in the map");
        // The target key was the first inserted, so it is visited first: its
        // guard is the occurrence-0 expiry symbol.
        String removeIf = removeIfGuardedBy(relation, "es_expiry_0");
        require(removeIf != null,
                "entrySet loop recorded no REMOVE_IF for key " + KEY_ID + ": "
                        + head(relation));
        String arguments = valueOf(shallow(removeIf), "arguments");
        require(arguments != null
                        && reachableContains(relation, arguments,
                                "\"_exp\":\"Y_I_" + KEY_ID + "\"")
                        && !reachableContains(relation, arguments,
                                "\"operation\":\"KEY\"")
                        && !reachableContains(relation, arguments,
                                "\"operation\":\"NEXT\""),
                "the entry-key fallback copied the iterator state: "
                        + head(String.valueOf(arguments)));
        String guard = valueOf(removeIf, "guard");
        require(guard != null
                        && reachableContains(relation, guard, "es_expiry_0"),
                "the entrySet REMOVE_IF guard does not name the entry's "
                        + "symbolic expiry: " + head(String.valueOf(guard)));
        require(topOperatorIs(relation, guard, "<"),
                "the entrySet guard is not the removal condition (<): "
                        + head(guard));
    }

    // A symbolic boxed key is the common map-index shape in HDFS.  Every pass
    // revisits the same entries, so embedding the current map state below KEY
    // makes the serialized tree multiply on each pass.  Reusing the key
    // object's own expression leaves exactly one REMOVE_IF node per visit.
    private static void symbolicEntryKeysStayLeafAndScaleLinearly() {
        String small = recordSymbolicKeyPasses(3, "growth_a");
        String large = recordSymbolicKeyPasses(6, "growth_b");

        require(count(small, "\"operation\":\"REMOVE_IF\"") == 6,
                "three two-entry passes did not produce six state updates: "
                        + small.length());
        require(count(large, "\"operation\":\"REMOVE_IF\"") == 12,
                "a prior map state was duplicated below a key expression: "
                        + large.length());
        require(large.length() <= small.length() * 5 / 2 + 2048,
                "doubling iterator passes grew faster than linearly: small="
                        + small.length() + " large=" + large.length());

        for (int key = 0; key < 2; key++) {
            String removeIf = removeIfGuardedBy(
                    large, "growth_b_expiry_" + key);
            require(removeIf != null,
                    "no conditional removal for symbolic key " + key);
            String arguments = valueOf(shallow(removeIf), "arguments");
            require(arguments != null
                            && reachableContains(large, arguments,
                                    "growth_b_key_" + key),
                    "REMOVE_IF lost boxed key lineage growth_b_key_" + key
                            + ": " + head(String.valueOf(arguments)));
            require(!reachableContains(large, arguments,
                                    "\"operation\":\"KEY\"")
                            && !reachableContains(large, arguments,
                                    "\"operation\":\"NEXT\""),
                    "symbolic key still embeds iterator state: "
                            + head(arguments));
        }
    }

    private static String recordSymbolicKeyPasses(
            int passes, String prefix) {
        State state = new State();
        Value[] values = {new Value(100L), new Value(200L)};

        System.startConcolicRegion("REGION." + prefix, "TASK." + prefix);
        System.symbolizeField(state, "allKeys", prefix + "_map");
        for (int key = 0; key < values.length; key++) {
            KeySource source = new KeySource(9000 + key);
            System.symbolizeExactField(source, KeySource.class.getName(),
                    "keyId", "I", prefix + "_key_" + key);
            // Match the production shape: a symbolic primitive is read from
            // an upstream object and boxed before it becomes a map key.  The
            // VM's Integer.valueOf model must attach that primitive
            // expression to the returned Integer object; iterator removal
            // then recovers the same expression from the entry's real key.
            Integer boxed = Integer.valueOf(source.keyId);
            System.symbolizeExactField(values[key], Value.class.getName(),
                    "expiry", "J", prefix + "_expiry_" + key);
            state.allKeys.put(boxed, values[key]);
        }

        int occurrence = 0;
        for (int pass = 0; pass < passes; pass++) {
            for (Iterator<Map.Entry<Integer, Value>> it =
                    state.allKeys.entrySet().iterator(); it.hasNext();) {
                Map.Entry<Integer, Value> entry = it.next();
                System.markConcolicBranch(
                        "REMOVE.GROWTH." + prefix, ++occurrence);
                if (entry.getValue().getExpiryDate() < NOW) {
                    it.remove();
                }
            }
        }
        String relation = System.getSymbolicExpression(state.allKeys);
        System.finishConcolicRegion();
        require(state.allKeys.size() == values.length,
                "growth baseline removed an unexpired key");
        return relation;
    }

    // (4) with no marked branch, an iterator remove is still REMOVE_AT.
    private static void unconditionalRemoveStaysRemoveAt() {
        State state = new State();
        state.allKeys.put(1, new Value(10L));
        state.allKeys.put(2, new Value(20L));

        System.startConcolicRegion("REGION.plain-remove",
                "TASK.plain-remove");
        System.symbolizeField(state, "allKeys", "plain_map");
        for (Iterator<Integer> it = state.allKeys.keySet().iterator();
                it.hasNext();) {
            Integer keyId = it.next();
            // No markConcolicBranch: this removal is not control-dependent on
            // a recorded symbolic branch.
            if (keyId.intValue() == 1) {
                it.remove();
            }
        }
        String relation = System.getSymbolicExpression(state.allKeys);
        System.finishConcolicRegion();

        require(relation.contains("\"operation\":\"REMOVE_AT\""),
                "an unmarked iterator remove must stay REMOVE_AT: "
                        + head(relation));
        require(!relation.contains("\"operation\":\"REMOVE_IF\""),
                "an unmarked iterator remove must not become REMOVE_IF: "
                        + head(relation));
    }

    // ---- a small JSON scan (depth/quote aware) -----------------------------

    /**
     * The balanced text of the {@code REMOVE_IF} carrying the named guard.
     */
    private static String removeIfGuardedBy(String json, String guardSymbol) {
        int at = 0;
        while (true) {
            int op = json.indexOf("\"operation\":\"REMOVE_IF\"", at);
            if (op < 0) return null;
            int objectStart = objectStartBefore(json, op);
            int objectEnd = balancedEnd(json, objectStart);
            String object = json.substring(objectStart, objectEnd);
            String guard = valueOf(shallow(object), "guard");
            if (guard != null
                    && reachableContains(json, guard, guardSymbol)) {
                return object;
            }
            at = op + 1;
        }
    }

    /** The object with nested ContainerRelation receivers blanked out, so a
     *  member lookup binds to this object's own members. */
    private static String shallow(String object) {
        int receiver = object.indexOf("\"receiver\":{");
        if (receiver < 0) return object;
        int valueStart = receiver + "\"receiver\":".length();
        int valueEnd = balancedEnd(object, valueStart);
        return object.substring(0, valueStart) + "{}"
                + object.substring(valueEnd);
    }

    private static int objectStartBefore(String json, int index) {
        int depth = 0;
        for (int at = index; at >= 0; at--) {
            char c = json.charAt(at);
            if (c == '}' || c == ']') depth++;
            else if (c == '{' || c == '[') {
                if (depth == 0) return at;
                depth--;
            }
        }
        return 0;
    }

    private static boolean topOperatorIs(String artifact, String binary,
                                         String op) {
        String definition = definitionOf(artifact, binary);
        String shallow = shallow2(definition == null ? binary : definition);
        return op.equals(valueOf(shallow, "_op"));
    }

    /** Whether an expression-reference DAG reachable from {@code value}
     *  contains a local definition fragment, without expanding the DAG. */
    private static boolean reachableContains(String artifact, String value,
                                             String needle) {
        return reachableContains(artifact, value, needle,
                new java.util.HashSet<String>());
    }

    private static boolean reachableContains(
            String artifact, String value, String needle,
            java.util.Set<String> visited) {
        if (value == null) return false;
        if (value.contains(needle)) return true;
        int at = 0;
        String marker = "\"_type\":\"VmExpressionReference\"";
        while ((at = value.indexOf(marker, at)) >= 0) {
            int start = objectStartBefore(value, at);
            int end = balancedEnd(value, start);
            String reference = value.substring(start, end);
            String identity = referenceIdentity(reference);
            if (visited.add(identity)) {
                String definition = definitionOf(artifact, reference);
                if (definition != null && reachableContains(
                        artifact, definition, needle, visited)) {
                    return true;
                }
            }
            at = end;
        }
        return false;
    }

    /** The local expression object named by one VM reference. */
    private static String definitionOf(String artifact, String reference) {
        if (reference == null || !reference.contains(
                "\"_type\":\"VmExpressionReference\"")) {
            return null;
        }
        String identity = referenceIdentity(reference);
        int slash = identity.indexOf('/');
        String session = identity.substring(0, slash);
        String expression = identity.substring(slash + 1);
        String prefix = "\"_type\":\"VmExpressionDefinition\","
                + "\"sessionId\":" + session + ","
                + "\"expressionId\":" + expression + ",";
        int at = artifact.indexOf(prefix);
        if (at < 0) return null;
        int start = objectStartBefore(artifact, at);
        String row = artifact.substring(start, balancedEnd(artifact, start));
        return valueOf(row, "expression");
    }

    private static String referenceIdentity(String reference) {
        String session = valueOf(reference, "sessionId");
        String expression = valueOf(reference, "expressionId");
        require(session != null && expression != null,
                "malformed VM expression reference: " + head(reference));
        return session + "/" + expression;
    }

    /** Blank out _left and _right so _op binds to the top node's operator. */
    private static String shallow2(String object) {
        String result = object;
        result = blankMember(result, "_left");
        result = blankMember(result, "_right");
        return result;
    }

    private static String blankMember(String object, String key) {
        int at = indexOfKey(object, key);
        if (at < 0) return object;
        int start = at;
        char open = object.charAt(start);
        int end = (open == '{' || open == '[')
                ? balancedEnd(object, start)
                : (open == '"' ? stringEnd(object, start) : start);
        if (open != '{' && open != '[' && open != '"') return object;
        return object.substring(0, start) + "{}" + object.substring(end);
    }

    private static String valueOf(String json, String key) {
        int at = indexOfKey(json, key);
        if (at < 0) return null;
        char open = json.charAt(at);
        if (open == '{' || open == '[') {
            return json.substring(at, balancedEnd(json, at));
        }
        if (open == '"') {
            String raw = json.substring(at, stringEnd(json, at));
            return raw.substring(1, raw.length() - 1);
        }
        int end = at;
        while (end < json.length() && ",}]".indexOf(json.charAt(end)) < 0) end++;
        return json.substring(at, end);
    }

    private static int indexOfKey(String json, String key) {
        String quoted = "\"" + key + "\":";
        int at = 0;
        while (at < json.length()) {
            char c = json.charAt(at);
            if (c == '"') {
                if (json.startsWith(quoted, at)) return at + quoted.length();
                at = stringEnd(json, at);
            } else {
                at++;
            }
        }
        return -1;
    }

    private static int balancedEnd(String json, int start) {
        int depth = 0;
        int at = start;
        while (at < json.length()) {
            char c = json.charAt(at);
            if (c == '"') { at = stringEnd(json, at); continue; }
            if (c == '{' || c == '[') depth++;
            else if (c == '}' || c == ']') {
                depth--;
                if (depth == 0) return at + 1;
            }
            at++;
        }
        throw new IllegalStateException("unbalanced from " + start);
    }

    private static int stringEnd(String json, int start) {
        int at = start + 1;
        while (at < json.length()) {
            char c = json.charAt(at);
            if (c == '\\') { at += 2; continue; }
            if (c == '"') return at + 1;
            at++;
        }
        throw new IllegalStateException("unterminated string at " + start);
    }

    private static int count(String value, String needle) {
        int result = 0;
        int at = 0;
        while ((at = value.indexOf(needle, at)) >= 0) {
            result++;
            at += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new IllegalStateException(message);
    }

    private static String head(String value) {
        if (value == null) return "null";
        return value.length() <= 400 ? value : value.substring(0, 400) + "...";
    }
}
