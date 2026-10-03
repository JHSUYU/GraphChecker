/**
 * A path condition too large to serialize is reported in full length, with
 * every index accounted for.
 *
 * The engine bounds how many bytes one `conditions` array may cost, because a
 * recorded condition is an expression DAG and a long-running thread can hold
 * hundreds of them.  The bound is necessary.  What was wrong is what it did
 * when it fired: the serializer wrote one `TruncatedExpression` and then
 * `break`-ed, so the array simply stopped -- while the envelope around it went
 * on declaring the full `conditionCount` and the full `pathConditionIndices`.
 * A reader was handed 240 declared conditions, 240 indices and 200 array
 * entries, which is not a truncated answer but a malformed one: the positional
 * correspondence between `conditions[i]` and `pathConditionIndices[i]` is
 * broken from the truncation point on, and there is no way to tell from the
 * document which 40 indices lost their expression.  HDFS-11741 run 24 hit
 * exactly this on a DataNode heartbeat loop iteration (240 conditions, 33.2 MB
 * against a 32 MB bound) and the import refused the row as a cardinality
 * fault.  The range form (`getConcolicPathConditionRange`) is the one reader
 * of that serializer left: a summary states no condition but a marked
 * branch's.  A condition with a NULL expression had the same effect for the same
 * reason -- it was `continue`-d past, emitting nothing at all for that index.
 *
 * What this pins down:
 *
 *   1. `conditions` holds exactly one entry per index, always.  Where the
 *      expression is not in the document its slot holds a named
 *      TruncatedExpression carrying its own `_index`, so the array stays
 *      positional and the reason is visible at the index it applies to.
 *   2. the envelope says so itself: `emittedConditionCount` sits next to
 *      `conditionCount`, and the two agree whether or not the bound fired.
 *      A reader checks cardinality against a number rather than inferring it.
 *   3. truncation is sticky and ordered -- every expression that made it into
 *      the document precedes every marker, so the prefix is a genuine prefix.
 *   4. a summary carries no auxiliary channel.
 *   5. at the shipped bound this workload does not truncate at all.  240
 *      conditions of ordinary branch shape are evidence, not a pathological
 *      size, and the default must carry them whole.
 *
 * The bound is read from `-Dcausynth.vm.pathcondition.bytes`, which is what
 * lets one smoke cover all three arms without ever producing the hundreds of
 * megabytes the shipped bound allows:
 *
 *   unset  -- the shipped 256 MB bound; expect no markers at all
 *   0      -- nothing fits; expect every index to be a marker
 *   <n>    -- some fit; expect a non-empty prefix of expressions followed by
 *             a non-empty suffix of markers
 */
public final class RegionPathConditionTruncationSmoke {

    /**
     * The count HDFS-11741 run 24 reported: one DataNode heartbeat loop
     * iteration.  Large enough that a mid-sized bound splits it, small enough
     * that the unbounded arm stays a smoke test.
     */
    private static final int BRANCHES = 240;

    private static final String MARKER = "\"_type\":\"TruncatedExpression\"";
    private static final String BYTE_LIMIT =
            "\"truncationKind\":\"PATH_CONDITION_RANGE_BYTE_LIMIT\"";

    private static final class Input { int v; }

    /** What the configured bound implies about the answer. */
    private static final int EXPECT_NONE_TRUNCATED = 0;
    private static final int EXPECT_ALL_TRUNCATED = 1;
    private static final int EXPECT_SOME_TRUNCATED = 2;

    public static void main(String[] args) throws Exception {
        int expectation = expectationFromBound();

        long status = System.startConcolicRegion(
                "REGION.pc-truncation", "TASK.pc-truncation");
        require(status == 0L, "region start rejected: " + status);

        Input in = new Input();
        in.v = 1;
        System.symbolizeExactField(
                in, Input.class.getName(), "v", "I", "TRUNCATION_SEED");

        // A branch records into the thread path condition, which is what the
        // range API reads; a symbolically indexed read beside it -- the shape
        // the HDFS workload's key lookups have -- records nothing there.
        int[] table = new int[8];
        int taken = 0;
        int sum = 0;
        for (int i = 0; i < BRANCHES; i++) {
            // One site, bounded dynamic occurrences, marker immediately before
            // the conditional it owns -- the shape the runtime ABI expects.
            System.markConcolicBranch("PC.TRUNCATION", i + 1);
            if (in.v + i > 0) {
                taken++;
            }
            sum += table[(in.v + i) & 7];
        }

        // Captured inside the region, checked outside it.  Every character
        // comparison a check makes is itself recorded while the region is
        // live, which would grow the path condition being measured in the
        // middle of measuring it.
        String summary = System.getConcolicRegionSummary();
        String range = System.getConcolicPathConditionRange(0, BRANCHES);

        System.endConcolic();

        require(taken == BRANCHES,
                "every branch should have been taken: " + taken);
        require(sum == 0, "the lookup table was never written: " + sum);

        require(valueOf(summary, "auxiliaryPathCondition") == null,
                "summary carries an auxiliary channel: " + head(summary));
        checkRange(range, expectation);

        System.out.println("RegionPathConditionTruncationSmoke OK ("
                + expectationName(expectation) + ")");
    }

    // ---- the range envelope ------------------------------------------------

    /** (1) (2) (3): the serializer, reached through the range API. */
    private static void checkRange(String range, int expectation) {
        int declared = intValueOf(range, "conditionCount");
        int emitted = intValueOf(range, "emittedConditionCount");
        String[] conditions = elementsOf(valueOf(range, "conditions"));

        require(declared == BRANCHES,
                "range conditionCount " + declared + " != requested "
                        + BRANCHES);
        require(emitted == declared,
                "range emittedConditionCount " + emitted
                        + " != conditionCount " + declared);
        require(conditions.length == declared,
                "range conditions holds " + conditions.length
                        + " entries, conditionCount is " + declared);

        checkPositional(conditions, 0, "range");
        checkTruncationShape(conditions, expectation, "range");
    }

    // ---- shared assertions -------------------------------------------------

    /**
     * (1): every marker names the index whose slot it occupies.
     *
     * This is what makes a truncated answer usable rather than merely
     * well-formed -- a reader can say which conditions it does not have,
     * without counting slots itself.
     */
    private static void checkPositional(String[] conditions, int start,
                                        String where) {
        // `_index` names the slot within the vector being serialized, so it
        // is `start + position`.
        for (int i = 0; i < conditions.length; i++) {
            String element = conditions[i];
            if (element.indexOf(MARKER) < 0) {
                continue;
            }
            int index = intValueOf(element, "_index");
            require(index == start + i,
                    where + " marker at position " + i + " names _index "
                            + index + ", expected " + (start + i));
            require(element.indexOf("\"expressionAuthority\":"
                            + "\"VM_SERIALIZATION_TRUNCATION_V1\"") >= 0,
                    where + " marker at position " + i
                            + " carries no truncation authority: " + element);
            require(element.indexOf("\"truncationKind\":") >= 0,
                    where + " marker at position " + i
                            + " does not say why: " + element);
        }
    }

    /**
     * (3) (5): how many markers there are, and that they form a suffix.
     *
     * Truncation is a byte bound on the document, so once it fires nothing
     * later can be afforded either.  The array must therefore be a genuine
     * prefix of expressions followed by markers -- never interleaved, which
     * would mean the bound was being applied per element and the answer is a
     * sample rather than a prefix.
     */
    private static void checkTruncationShape(String[] conditions,
                                             int expectation, String where) {
        int markers = 0;
        int firstMarker = -1;
        int lastExpression = -1;
        for (int i = 0; i < conditions.length; i++) {
            if (conditions[i].indexOf(MARKER) >= 0) {
                markers++;
                if (firstMarker < 0) {
                    firstMarker = i;
                }
                require(conditions[i].indexOf(BYTE_LIMIT) >= 0,
                        where + " marker at position " + i
                                + " is not a byte-limit truncation: "
                                + conditions[i]);
            } else {
                lastExpression = i;
            }
        }
        require(firstMarker < 0 || lastExpression < firstMarker,
                where + " markers are interleaved with expressions: first"
                        + " marker at " + firstMarker + ", an expression at "
                        + lastExpression);

        int total = conditions.length;
        if (expectation == EXPECT_NONE_TRUNCATED) {
            require(markers == 0,
                    where + " truncated " + markers + " of " + total
                            + " conditions at the shipped bound; " + total
                            + " ordinary branch conditions must fit");
        } else if (expectation == EXPECT_ALL_TRUNCATED) {
            require(markers == total,
                    where + " truncated only " + markers + " of " + total
                            + " conditions at a zero-byte bound");
        } else {
            require(markers > 0,
                    where + " truncated nothing at a reduced bound; raise "
                            + "BRANCHES or lower the bound");
            require(markers < total,
                    where + " truncated everything at a reduced bound; the "
                            + "bound is below one condition's size");
        }
    }

    // ---- the configured bound ----------------------------------------------

    private static int expectationFromBound() {
        String configured =
                System.getProperty("causynth.vm.pathcondition.bytes");
        if (configured == null || configured.length() == 0) {
            return EXPECT_NONE_TRUNCATED;
        }
        if (configured.equals("0")) {
            return EXPECT_ALL_TRUNCATED;
        }
        return EXPECT_SOME_TRUNCATED;
    }

    private static String expectationName(int expectation) {
        if (expectation == EXPECT_NONE_TRUNCATED) return "shipped bound";
        if (expectation == EXPECT_ALL_TRUNCATED) return "zero bound";
        return "reduced bound";
    }

    // ---- JSON scanning ------------------------------------------------------
    //
    // A depth- and quote-aware scan rather than a parser: the point is to
    // count top-level array elements exactly, and an expression payload is
    // full of braces and of strings containing braces.

    /** The balanced text of `"key": <value>`, or null if the key is absent. */
    private static String valueOf(String json, String key) {
        int at = indexOfKey(json, key);
        if (at < 0) {
            return null;
        }
        int start = at;
        while (start < json.length() && json.charAt(start) == ' ') {
            start++;
        }
        char open = json.charAt(start);
        if (open == '{' || open == '[') {
            return json.substring(start, balancedEnd(json, start));
        }
        if (open == '"') {
            return json.substring(start, stringEnd(json, start));
        }
        int end = start;
        while (end < json.length() && ",}]".indexOf(json.charAt(end)) < 0) {
            end++;
        }
        return json.substring(start, end);
    }

    private static int intValueOf(String json, String key) {
        String raw = valueOf(json, key);
        require(raw != null, "no " + key + " in " + head(json));
        return Integer.parseInt(raw.trim());
    }

    /** The offset just past `"key":`, skipping over any string contents. */
    private static int indexOfKey(String json, String key) {
        String quoted = "\"" + key + "\":";
        int at = 0;
        while (at < json.length()) {
            char c = json.charAt(at);
            if (c == '"') {
                if (json.startsWith(quoted, at)) {
                    return at + quoted.length();
                }
                at = stringEnd(json, at);
            } else {
                at++;
            }
        }
        return -1;
    }

    /** The top-level elements of a JSON array, as raw text. */
    private static String[] elementsOf(String array) {
        require(array != null && array.length() >= 2 && array.charAt(0) == '[',
                "not a JSON array: " + head(String.valueOf(array)));
        java.util.List<String> elements = new java.util.ArrayList<String>();
        int at = 1;
        int end = array.length() - 1;
        while (at < end) {
            char c = array.charAt(at);
            if (c == ',' || c == ' ') {
                at++;
                continue;
            }
            int stop;
            if (c == '{' || c == '[') {
                stop = balancedEnd(array, at);
            } else if (c == '"') {
                stop = stringEnd(array, at);
            } else {
                stop = at;
                while (stop < end && ",]".indexOf(array.charAt(stop)) < 0) {
                    stop++;
                }
            }
            elements.add(array.substring(at, stop));
            at = stop;
        }
        String[] result = new String[elements.size()];
        for (int i = 0; i < result.length; i++) {
            result[i] = elements.get(i);
        }
        return result;
    }

    /** The offset just past the bracket matching the one at `start`. */
    private static int balancedEnd(String json, int start) {
        int depth = 0;
        int at = start;
        while (at < json.length()) {
            char c = json.charAt(at);
            if (c == '"') {
                at = stringEnd(json, at);
                continue;
            }
            if (c == '{' || c == '[') {
                depth++;
            } else if (c == '}' || c == ']') {
                depth--;
                if (depth == 0) {
                    return at + 1;
                }
            }
            at++;
        }
        throw new IllegalStateException(
                "unbalanced JSON from offset " + start + ": "
                        + head(json.substring(start)));
    }

    /** The offset just past the closing quote of the string at `start`. */
    private static int stringEnd(String json, int start) {
        int at = start + 1;
        while (at < json.length()) {
            char c = json.charAt(at);
            if (c == '\\') {
                at += 2;
                continue;
            }
            if (c == '"') {
                return at + 1;
            }
            at++;
        }
        throw new IllegalStateException(
                "unterminated JSON string at " + start);
    }

    // ---- plumbing -----------------------------------------------------------

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new IllegalStateException(message);
        }
    }

    private static String head(String value) {
        if (value == null) {
            return "null";
        }
        return value.length() <= 400 ? value : value.substring(0, 400) + "...";
    }
}
