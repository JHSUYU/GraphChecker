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
 *      A ReadFromExpression names each candidate's value twice, once in
 *      `candidates` and once in the `ite` chain, so a shared subtree reached
 *      that way must be emitted per reference and not per path to it;
 *   4. none of this truncates.  The serializer may refuse a cycle or a
 *      pathological size, and says so with a named TruncatedExpression, but
 *      ordinary evidence of this depth must come back whole -- a silent
 *      partial answer would be worse than the crash it replaced.
 *   5. a small DAG whose expanded tree is exponential is stopped by the byte
 *      bound with valid, explicitly truncated JSON rather than native OOM.
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
    private static final int MAX_RENDER_BYTES = 8 * 1024 * 1024;

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
        checkBoundedSharedDag(sharedDag);

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
        require(System.selectSharedFieldCarrier(
                        holder, Holder.class.getName(), "shared", "I") > 0L,
                "carrier selection rejected");

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
     * A guarded read, whose candidate values are each named twice.
     *
     * Two equal-valued writers leave a read the run cannot attribute, so the
     * reader gets a ReadFromExpression.  It serializes every candidate once
     * under `candidates` and again in the `ite` chain; the point here is that
     * this stays proportional to the node count rather than to the number of
     * paths through it.
     */
    private static String guardedRead() throws Exception {
        final Holder holder = new Holder();
        require(System.selectSharedFieldCarrier(
                        holder, Holder.class.getName(), "shared", "I") > 0L,
                "carrier selection rejected");

        // Deliberately not joined before the read.  Joining is a synchronised
        // edge the engine records, which would make the later writer dominant
        // and the read exact -- and an exact read is precisely the case that
        // builds no ReadFromExpression at all.
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

    /** (3) (4): a guarded read, candidates named twice, output still linear. */
    private static void checkGuardedRead(String json) {
        require(json.contains("\"_type\":\"ReadFromExpression\""), head(json));
        require(json.contains("\"resolution\":\"GUARDED\""), head(json));
        // rf_unknown is always the last arm, and every recorded writer gets one
        // ite arm ahead of it.
        require(json.contains("rf_unknown"), head(json));
        int arms = count(json, "\"_type\":\"IteExpression\"");
        require(arms == 2,
                "expected one ite arm per recorded writer, got " + arms + ": "
                        + head(json));
        require(json.contains("REGION.rf1") && json.contains("REGION.rf2"),
                head(json));
        // Each candidate is named exactly twice -- once in `candidates`, once
        // in its ite arm -- and no more.  More would mean the walk re-expands
        // a shared subtree once per path that reaches it rather than once per
        // reference to it, which is how a modest DAG turns into an
        // exponentially large document.
        require(count(json, "\"selector\":\"rf1\"") == 2,
                "candidate rf1 should be named exactly twice, was "
                        + count(json, "\"selector\":\"rf1\""));
        require(count(json, "\"selector\":\"rf2\"") == 2,
                "candidate rf2 should be named exactly twice, was "
                        + count(json, "\"selector\":\"rf2\""));
        requireWellFormed(json);
        requireNoTruncation(json);
    }

    /** (5): expanded sharing is byte-bounded and remains valid evidence. */
    private static void checkBoundedSharedDag(String json) {
        require(json.length() <= MAX_RENDER_BYTES,
                "shared DAG exceeded byte cap: " + json.length());
        require(json.contains(TRUNCATION),
                "exponential shared DAG should be explicitly truncated");
        require(json.contains("EXPRESSION_BYTE_LIMIT"), head(json));
        requireWellFormed(json);
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
