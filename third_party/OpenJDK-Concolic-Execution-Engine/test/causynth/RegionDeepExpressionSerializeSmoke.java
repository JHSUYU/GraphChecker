import java.util.concurrent.CountDownLatch;

/**
 * Serializing a deep expression is bounded by heap, not by the native stack.
 *
 * Every evidence API in the engine -- getSymbolicExpression,
 * getSymbolicFieldExpression, getSharedFieldVersions, getSharedElementVersions,
 * getConcolicRegionSummary and finishConcolicRegion funnel
 * into Expression::serialize.  That walk used to spend one native frame per
 * node (two, counting serialize_internal), so its depth was the depth of
 * whatever expression the workload had built.  Nothing bounds that: a
 * path-condition conjunction is one op_land node per branch the thread took,
 * and an arithmetic accumulation is one node per operation, so a region doing
 * ordinary string or container work builds left-deep chains thousands of nodes
 * long.  Past roughly three thousand the process died of SIGSEGV with no
 * hs_err file, which with stdout redirected is indistinguishable from evidence
 * that merely looks short.
 *
 * What this pins down:
 *
 *   1. a chain far deeper than that old limit serializes completely, through
 *      the field-expression funnel, and the payload really is the whole chain:
 *      one nesting per operation, the seed symbol at the bottom, balanced
 *      JSON at the top;
 *   2. the same holds for the shape that actually crashed -- a writer's path
 *      guard, which is the conjunction of every branch it took, reached
 *      through getSharedFieldVersions;
 *   3. a guarded read serializes its candidates without the output exploding.
 *      A ReadFromExpression names candidate values in both its evidence rows
 *      and selection term, so a shared subtree reached that way must be emitted
 *      per reference and not per path to it;
 *   4. none of this truncates.  The serializer may refuse a cycle or a
 *      pathological size, and says so with a named TruncatedExpression, but
 *      ordinary evidence of this depth must come back whole -- a silent
 *      partial answer would be worse than the crash it replaced.
 *   5. a small DAG whose expanded tree is exponential stays linear in the
 *      artifact: every node is defined once and both parent edges point to
 *      the same session-local expression id.
 */
public final class RegionDeepExpressionSerializeSmoke {

    /**
     * Both depths sit at roughly twice the measured limit of the recursive
     * walk, which died between 3,000 and 3,500 nodes on this configuration --
     * deep enough that a regression fails here reliably, shallow enough that
     * the test stays a smoke test.
     */
    private static final int CHAIN_DEPTH = 6000;
    /** Recorded branches, hence conjuncts in the writer's path guard. */
    private static final int GUARD_BRANCHES = 4500;
    private static final int SHARED_DAG_DEPTH = 40;
    private static final int MAX_DAG_ARTIFACT_BYTES = 128 * 1024;

    /**
     * What the serializer emits in place of a subtree it will not expand.  It
     * refuses only a cycle or a pathological size, and says so by name so that
     * the Java side can record a coverage gap; none of the evidence here
     * should contain it.
     */
    private static final String TRUNCATION = "TruncatedExpression";

    private static final class Input { int v; }
    private static final class Sink { int value; }
    private static final class Holder { int shared; }

    public static void main(String[] args) throws Exception {
        long status = System.startConcolicRegion(
                "REGION.deep-serialize", "TASK.deep-serialize");
        require(status == 0L, "region start rejected: " + status);

        String chain = deepOperatorChain();
        String guard = deepPathGuard();
        String read = guardedRead();
        String sharedDag = exponentiallySharedDag();

        System.endConcolic();

        // The checking happens outside the region on purpose.  Scanning a
        // payload this size is itself string work, and inside a traced region
        // every one of those character comparisons is recorded -- which would
        // cost far more than producing the evidence did, and would grow the
        // path condition being measured while measuring it.
        checkDeepOperatorChain(chain);
        checkDeepPathGuard(guard);
        checkGuardedRead(read);
        checkSharedDagTable(sharedDag);

        System.out.println("RegionDeepExpressionSerializeSmoke OK");
    }

    // ---- production, inside the region -------------------------------------

    private static String deepOperatorChain() {
        Input in = new Input();
        in.v = 1;
        System.symbolizeExactField(
                in, Input.class.getName(), "v", "I", "CHAIN_SEED");

        int acc = in.v;
        for (int i = 0; i < CHAIN_DEPTH; i++) {
            acc = acc + 1;
        }

        Sink sink = new Sink();
        sink.value = acc;
        return System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
    }

    /**
     * The writer's path guard, one conjunct per recorded branch.
     *
     * This is the shape the crash was found on.  Each conjunct is small and
     * independent -- a comparison against the seed, not against the running
     * accumulation -- so the guard is deep without the serialized form being
     * quadratic, which is how a real traced workload's branch history looks.
     */
    private static String deepPathGuard() throws Exception {
        final Holder holder = new Holder();

        final CountDownLatch done = new CountDownLatch(1);
        Thread writer = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(
                            "REGION.deep-guard", "TASK.deep-guard") != 0L) {
                        return;
                    }
                    Input in = new Input();
                    in.v = 1;
                    System.symbolizeExactField(
                            in, Input.class.getName(), "v", "I", "GUARD_SEED");
                    int taken = 0;
                    for (int i = 0; i < GUARD_BRANCHES; i++) {
                        // One site with bounded dynamic occurrences, matching
                        // the runtime ABI.  Keep the native marker immediately
                        // before the conditional it owns.
                        System.markConcolicBranch("DEEP.GUARD", i + 1);
                        if (in.v + i > 0) {
                            taken++;
                        }
                    }
                    if (taken == GUARD_BRANCHES) {
                        holder.shared = in.v + 1;
                    }
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, "deep-guard-writer");
        writer.start();
        done.await();
        writer.join();

        return System.getSharedFieldVersions(
                holder, Holder.class.getName(), "shared", "I");
    }

    /**
     * A read of a location two writers reached with the same value.
     *
     * The run still performed one read, and the node it produced names the
     * version that read observed and carries its value.  The other writer
     * stays in the location's log, where RegionSharedReadFromSmoke asserts
     * it; nothing about it is republished here.
     */
    private static String guardedRead() throws Exception {
        final Holder holder = new Holder();

        // Wait until both writes are retained. Read-from selection deliberately
        // does not use join or other schedule evidence to discard candidates.
        Thread first = writeFrom(holder, "REGION.rf1", 9, 1);
        Thread second = writeFrom(holder, "REGION.rf2", 5, 2);

        Sink sink = new Sink();
        sink.value = holder.shared;
        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        first.join();
        second.join();
        return read;
    }

    /** A linear-size DAG whose fully expanded JSON tree has 2^depth leaves. */
    private static String exponentiallySharedDag() {
        Input in = new Input();
        in.v = 1;
        System.symbolizeExactField(
                in, Input.class.getName(), "v", "I", "SHARED_DAG_SEED");
        int value = in.v;
        for (int i = 0; i < SHARED_DAG_DEPTH; i++) {
            value = value + value;
        }
        Sink sink = new Sink();
        sink.value = value;
        return System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
    }

    /**
     * Starts one writer and waits, on a latch rather than on the thread, for
     * it to finish writing.  Returns it unjoined; see the caller.
     */
    private static Thread writeFrom(final Holder holder, final String region,
                                    final int seed, final int op)
            throws Exception {
        final CountDownLatch done = new CountDownLatch(1);
        Thread thread = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(region, "TASK.rf") != 0L) {
                        return;
                    }
                    Input in = new Input();
                    in.v = seed;
                    System.symbolizeExactField(
                            in, Input.class.getName(), "v", "I", region + ".V");
                    if (in.v > 0) {
                        holder.shared = (op == 1) ? in.v + 1 : in.v * 2;
                    }
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, region);
        thread.start();
        done.await();
        return thread;
    }

    // ---- checking, outside the region --------------------------------------

    /** (1) (4): a CHAIN_DEPTH-deep operator chain, whole. */
    private static void checkDeepOperatorChain(String json) {
        require(json.contains("\"symbolic\":true"),
                "the accumulated value should still be symbolic: " + head(json));
        requireDagArtifact(json);
        // One binary node per addition, so one "_left" per addition.  This is
        // the assertion a partial answer cannot pass: a walk that stopped
        // early would leave fewer.
        int operands = count(json, "\"_left\"");
        require(operands == CHAIN_DEPTH,
                "expected " + CHAIN_DEPTH + " chained operands, got " + operands
                        + ": " + head(json));
        // The bottom of the chain is the seed, reached only by descending the
        // whole thing.
        require(count(json, "CHAIN_SEED") == 1,
                "the seed should appear exactly once: " + head(json));
        require(json.contains("\"_op\":\"+\""), head(json));
        requireWellFormed(json);
        requireNoTruncation(json);
    }

    /** (2) (4): the writer's guard, one conjunct per recorded branch. */
    private static void checkDeepPathGuard(String json) {
        require(json.contains("\"regionId\":\"REGION.deep-guard\""),
                "the write should be attributed to its writer: " + head(json));
        requireDagArtifact(json);
        require(json.contains("GUARD_SEED"), head(json));
        // The guard is a left-deep conjunction: one op_land per recorded
        // branch after the first.  Anything materially short of that is a walk
        // that gave up part way down.
        int conjuncts = count(json, "\"_op\":\"&&\"");
        require(conjuncts >= GUARD_BRANCHES - 1,
                "expected at least " + (GUARD_BRANCHES - 1)
                        + " guard conjuncts, got " + conjuncts + ": "
                        + head(json));
        requireWellFormed(json);
        requireNoTruncation(json);
    }

    /** (3) (4): a read of a multiply-written location, whole and unexploded. */
    private static void checkGuardedRead(String json) {
        requireDagArtifact(json);
        require(json.contains("\"_type\":\"ReadFromExpression\""), head(json));
        require(json.contains("\"writerSetComplete\":true"), head(json));
        // Two read nodes: the reader's read of the shared field, and, inside
        // the value it carries, the observed writer's own read of its seed.
        // Each names exactly one version -- one real read, one answer.
        int reads = count(json, "\"_type\":\"ReadFromExpression\"");
        int observed = count(json, "\"observedVersion\"");
        require(reads == 2, "expected two read nodes, got " + reads + ": "
                + head(json));
        require(observed == reads,
                "every read must name one observed version: " + reads
                        + " reads, " + observed + " versions named: "
                        + head(json));
        // The VM no longer duplicates candidate values in a nested ite tree.
        int arms = count(json, "\"_type\":\"IteExpression\"");
        require(arms == 0,
                "expected no serialized ite for recorded writers, got " + arms + ": "
                        + head(json));
        // The value it carries is that one writer's, seed and all -- and the
        // writer it did not read is not in the read.  Which of the two ran
        // last is the schedule's business, so this counts rather than names.
        int first = count(json, "REGION.rf1.V");
        int second = count(json, "REGION.rf2.V");
        require(first + second == 1,
                "the read should carry exactly one writer's seed, carried "
                        + first + " and " + second + ": " + head(json));
        requireWellFormed(json);
        requireNoTruncation(json);
    }

    /** (5): shared children remain shared in the artifact DAG. */
    private static void checkSharedDagTable(String json) {
        requireDagArtifact(json);
        require(json.length() <= MAX_DAG_ARTIFACT_BYTES,
                "linear shared DAG artifact is unexpectedly large: "
                        + json.length());
        // One definition per operator, plus three for the seed itself: its
        // symbol, the read node the seed's getfield produced, and that read's
        // boundary.  A tree rather than a DAG would be 2^SHARED_DAG_DEPTH.
        require(count(json, "\"_type\":\"VmExpressionDefinition\"")
                        == SHARED_DAG_DEPTH + 3,
                "expected one definition per operator plus the seed's read: "
                        + head(json));
        require(count(json, "\"_left\"") == SHARED_DAG_DEPTH,
                "shared DAG lost operator definitions: " + head(json));
        require(count(json, "SHARED_DAG_SEED") == 1,
                "the shared seed must be defined once: " + head(json));
        requireNoTruncation(json);
        requireWellFormed(json);
    }

    private static void requireDagArtifact(String json) {
        require(json.contains("\"_type\":\"VmExpressionReference\""),
                "expression root was not encoded as a reference: "
                        + head(json));
        require(json.contains("\"vmExpressionTable\":"),
                "missing expression table: " + head(json));
        require(json.contains("\"kind\":\"VM_EXPRESSION_TABLE\""),
                "wrong expression table schema: " + head(json));
        requireClosedDagArtifact(json);
    }

    /** Every emitted reference resolves in the envelope's one session. */
    private static void requireClosedDagArtifact(String json) {
        int table = json.indexOf("\"kind\":\"VM_EXPRESSION_TABLE\"");
        long tableSession = longMemberAfter(json, "sessionId", table);
        long declared = longMemberAfter(json, "definitionCount", table);
        java.util.Set<Long> definitions = new java.util.HashSet<Long>();
        String definitionMarker =
                "\"_type\":\"VmExpressionDefinition\"";
        int at = json.indexOf(definitionMarker, table);
        int definitionRows = 0;
        while (at >= 0) {
            long session = longMemberAfter(json, "sessionId", at);
            long expression = longMemberAfter(json, "expressionId", at);
            require(session == tableSession,
                    "definition crossed VM session: " + session
                            + " != " + tableSession);
            require(definitions.add(Long.valueOf(expression)),
                    "duplicate VM expression definition: " + expression);
            definitionRows++;
            at = json.indexOf(definitionMarker, at + definitionMarker.length());
        }
        require(declared == definitionRows,
                "definitionCount " + declared + " != rows " + definitionRows);

        String referenceMarker =
                "\"_type\":\"VmExpressionReference\"";
        at = json.indexOf(referenceMarker);
        int references = 0;
        while (at >= 0) {
            long session = longMemberAfter(json, "sessionId", at);
            long expression = longMemberAfter(json, "expressionId", at);
            require(session == tableSession,
                    "reference crossed VM session: " + session
                            + " != " + tableSession);
            require(definitions.contains(Long.valueOf(expression)),
                    "dangling VM expression reference: " + expression);
            references++;
            at = json.indexOf(referenceMarker, at + referenceMarker.length());
        }
        require(references > 0, "DAG artifact contains no references");
    }

    private static long longMemberAfter(String json, String key, int from) {
        String marker = "\"" + key + "\":";
        int start = json.indexOf(marker, from);
        require(start >= 0, "missing " + key + " after " + from);
        start += marker.length();
        int end = start;
        while (end < json.length()
                && Character.isDigit(json.charAt(end))) {
            end++;
        }
        require(end > start, "non-numeric " + key + " after " + from);
        return Long.parseLong(json.substring(start, end));
    }

    /**
     * The serializer reports a subtree it would not expand instead of dropping
     * it, so evidence is never quietly short.  Nothing at these depths should
     * reach that path.
     */
    private static void requireNoTruncation(String json) {
        require(!json.contains(TRUNCATION),
                "evidence was truncated: " + around(json, json.indexOf(TRUNCATION)));
    }

    /**
     * One pass over a payload: structural validity, plus how many times each
     * marker occurs.
     *
     * Structure means two things.  The braces have to balance, and -- the part
     * that is not decoration -- every string token has to be followed by a
     * separator.  A serializer that splices a child's text over the place a
     * placeholder occupied can be off by the separator the writer emitted just
     * before it, and the result, `"_left"{...}` with the colon eaten, still
     * balances its braces and still contains every substring an assertion
     * might look for.  Insisting that a closing quote be followed by `:` `,`
     * `}` or `]` is what catches it.
     *
     * Done in a single pass over a char[] because the suite runs -Xint and
     * these payloads are megabytes: a separate interpreted String scan per
     * marker costs several times what producing the evidence did.
     */
    private static void requireWellFormed(String json) {
        // Over a char[] rather than through charAt: the suite runs -Xint and
        // these payloads are megabytes, so one interpreted call per character
        // would cost more than producing the evidence did.
        char[] text = json.toCharArray();
        int length = text.length;
        int depth = 0;
        int deepest = 0;
        boolean inString = false;
        boolean escaped = false;
        for (int i = 0; i < length; i++) {
            char c = text[i];
            if (inString) {
                if (escaped) {
                    escaped = false;
                } else if (c == '\\') {
                    escaped = true;
                } else if (c == '"') {
                    inString = false;
                    char next = (i + 1 < length) ? text[i + 1] : ' ';
                    require(next == ':' || next == ',' || next == '}'
                                    || next == ']' || i + 1 == length,
                            "missing separator after string at " + i + ": "
                                    + around(json, i));
                }
                continue;
            }
            if (c == '"') {
                inString = true;
            } else if (c == '{' || c == '[') {
                depth++;
                if (depth > deepest) {
                    deepest = depth;
                }
            } else if (c == '}' || c == ']') {
                depth--;
                require(depth >= 0, "unbalanced JSON at " + i + ": " + head(json));
            }
        }
        require(!inString, "unterminated JSON string: " + head(json));
        require(depth == 0,
                "unbalanced JSON, depth " + depth + " at end: " + head(json));
        // A flat document would mean the nesting never happened.
        require(deepest > 3, "expected a nested document, got depth " + deepest);
    }

    private static int count(String haystack, String needle) {
        int total = 0;
        int at = haystack.indexOf(needle);
        while (at >= 0) {
            total++;
            at = haystack.indexOf(needle, at + needle.length());
        }
        return total;
    }

    private static String head(String json) {
        return json.length() <= 400 ? json : json.substring(0, 400) + "...";
    }

    private static String around(String json, int at) {
        if (at < 0) {
            return head(json);
        }
        int from = Math.max(0, at - 120);
        int to = Math.min(json.length(), at + 120);
        return json.substring(from, to);
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
