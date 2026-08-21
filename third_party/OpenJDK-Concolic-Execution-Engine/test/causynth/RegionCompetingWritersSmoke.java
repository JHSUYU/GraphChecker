import java.util.concurrent.CountDownLatch;

/**
 * The read-from shapes that two writers cannot express.
 *
 * RegionSharedReadFromSmoke pins the two-candidate cases -- one writer, two
 * writers separated by value, two equal-valued writers, and an untracked one --
 * and RegionSharedSyncOrderSmoke pins the order sources that turn a
 * two-candidate choice into an exact one.  Three things are left over, and each
 * of them is a property of the *shape* of the candidate set rather than of any
 * single candidate:
 *
 *   1. three equal-valued competing writers.  Two candidates make a degenerate
 *      cut -- each candidate has exactly one competitor, so "before the
 *      selected write or after the read" cannot be told apart from "the other
 *      one".  With three, each candidate must name both of its competitors and
 *      neither itself, the exactly-one must range over all three plus the
 *      unknown arm, and the ite chain must be three deep and still bottom out
 *      in a free symbol.  The discriminating control is the same three writes
 *      sequenced by start/join: identical values, identical expressions,
 *      exactly one answer, because the order is there;
 *
 *   2. a writer whose own value is a guarded read.  Provenance has to compose:
 *      an exact read hands back the writer's expression, and when that
 *      expression is itself an unresolved choice the reader must receive that
 *      choice -- not a second wrapper around it, and not a collapsed arm of it.
 *      The reader's arithmetic then builds on the guarded node directly;
 *
 *   3. a selected carrier and an unselected neighbour of the same object under
 *      the same contention.  This is the cost boundary stated as a test.  The
 *      selected field refuses to name a writer; the unselected one hands back a
 *      plain expression with no provenance record at all, because nothing was
 *      versioned for it.  Both answers are the design's, and the difference
 *      between them is exactly what selection buys.
 */
public final class RegionCompetingWritersSmoke {

    private static final class Holder {
        int shared = 0;
        int neighbour = 0;
    }

    private static final class Input {
        int v;
        Input(int v) { this.v = v; }
    }

    private static final class Sink {
        int value = 0;
        int derived = 0;
    }

    public static void main(String[] args) throws Exception {
        require(System.startConcolicRegion(
                "REGION.competing", "TASK.competing") == 0L,
                "region start rejected");

        threeEqualValuedWritersAllSurvive();
        theSameThreeWritesSequencedResolveExactly();
        aWriterThatIsItselfAGuardedRead();
        anUnselectedNeighbourUnderTheSameContention();

        System.endConcolic();
        System.out.println("RegionCompetingWritersSmoke OK");
    }

    // ------------------------------------------------------------------
    // (1) Three candidates, and the cut each of them implies.
    // ------------------------------------------------------------------

    private static void threeEqualValuedWritersAllSurvive() throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        // Three different expressions, one shared concrete value.  Nothing in
        // the run separates them, and each takes a branch, so each candidate
        // carries a real path guard.
        Thread first = racingWriter(holder, "REGION.trio.1", 9, 1);
        Thread second = racingWriter(holder, "REGION.trio.2", 5, 2);
        Thread third = racingWriter(holder, "REGION.trio.3", 20, 3);

        Sink sink = new Sink();
        sink.value = holder.shared;
        require(sink.value == 10, "all three writers should have stored 10");

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(read.contains("\"_type\":\"ReadFromExpression\""), read);
        require(read.contains("\"reason\":\"AMBIGUOUS_WRITERS\""), read);
        require(read.contains(
                "\"exactlyOne\":[\"rf1\",\"rf2\",\"rf3\",\"rf_unknown\"]"),
                read);
        // Three real arms plus the unknown one, so three nested ites; the
        // innermost else is the free symbol, never a candidate by default.
        require(count(read, "\"_type\":\"IteExpression\"") == 3, read);
        require(read.contains("unknownWriter"), read);
        require(count(read, "\"pathGuard\":null") == 1,
                "only rf_unknown may be unguarded: " + read);

        // No candidate was dropped and none was preferred.
        require(read.contains("TRIO.1.A"), read);
        require(read.contains("TRIO.2.A"), read);
        require(read.contains("TRIO.3.A"), read);

        // The sparse read cut, which is what three candidates make checkable:
        // each of them precedes the read, and each names its *two* competitors.
        require(count(read, "\"kind\":\"WRITE_BEFORE_READ\"") == 3, read);
        require(count(read, "\"kind\":\"OTHER_WRITE_OUTSIDE_CUT\"") == 6,
                "each candidate must place both competitors: " + read);
        require(count(read, "\"kind\":\"UNKNOWN_WRITE_BEFORE_READ\"") == 1,
                read);

        String evidence = versions(holder);
        long[] versionIds = writeVersionIds(evidence);
        require(versionIds.length == 3,
                "expected three tracked writes, got " + versionIds.length);
        for (int index = 0; index < versionIds.length; index++) {
            long id = versionIds[index];
            // Present as a candidate and as its own cut anchor.
            require(read.contains("\"fieldVersionId\":" + id + ","), read);
            require(read.contains("\"kind\":\"WRITE_BEFORE_READ\",\"beforeEventId\":"
                            + id + ","), read);
            // And never listed as a competitor of itself: a write cannot be
            // required to fall outside a cut it is the centre of.
            require(count(read, "\"otherEventId\":" + id
                            + ",\"selectedEventId\":" + id + ",") == 0,
                    "candidate " + id + " competes with itself: " + read);
            // It does appear as somebody else's competitor, twice.
            require(count(read, "\"otherEventId\":" + id + ",") == 2,
                    "candidate " + id + " should be a competitor of the other"
                            + " two: " + read);
        }

        String last = lastRead(evidence);
        require(last.contains("\"resolution\":\"GUARDED\""), evidence);
        require(last.contains("\"candidateCount\":3"), evidence);
        require(last.contains("\"chosenFieldVersionId\":0"),
                "a guarded read must choose nothing: " + evidence);

        // A guarded read draws no read-from edge, whatever the candidate count.
        long readEvent = readLong(last,
                last.indexOf("\"readEventId\":") + "\"readEventId\":".length());
        String ledger = System.getEventLedger();
        require(!ledger.contains("\"afterEventId\":" + readEvent
                        + ",\"edgeKind\":\"FIELD_READ_FROM\""),
                "a three-way guarded read must contribute no edge: " + ledger);

        first.join();
        second.join();
        third.join();
    }

    /**
     * (1, control) The identical three writes, sequenced.
     *
     * Same values, same expressions, same three threads.  The only difference
     * is that each writer is joined before the next one starts, so the writes
     * are totally ordered by thread lifecycle and the last of them
     * happens-after both others.  If the three-way guard above came from the
     * shape of the test rather than from the absence of order, this would be
     * guarded too.
     */
    private static void theSameThreeWritesSequencedResolveExactly()
            throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        joinedWriter(holder, "REGION.seq.1", 9, 1);
        joinedWriter(holder, "REGION.seq.2", 5, 2);
        joinedWriter(holder, "REGION.seq.3", 20, 3);

        Sink sink = new Sink();
        sink.value = holder.shared;
        require(sink.value == 10, "all three writers should have stored 10");

        String evidence = versions(holder);
        String last = lastRead(evidence);
        require(last.contains("\"resolution\":\"EXACT\""),
                "sequenced writers must resolve: " + evidence);
        require(last.contains("\"reason\":\"SYNC_ORDERED\""), evidence);
        long[] versionIds = writeVersionIds(evidence);
        require(versionIds.length == 3, evidence);
        // The last releaser is the writer: coherence forbids reading a store
        // that a happens-before-later store to the same location overwrote.
        require(last.contains("\"chosenFieldVersionId\":"
                + versionIds[2]), evidence);

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(!read.contains("ReadFromExpression"),
                "an exact read must not be wrapped: " + read);
        require(read.contains("SEQ.3.A"), read);
        require(!read.contains("SEQ.1.A") && !read.contains("SEQ.2.A"), read);
    }

    // ------------------------------------------------------------------
    // (2) A writer whose value is itself an unresolved choice.
    // ------------------------------------------------------------------

    private static void aWriterThatIsItselfAGuardedRead() throws Exception {
        final Holder upstream = new Holder();
        require(select(upstream) > 0L, "upstream selection rejected");
        Thread first = racingWriter(upstream, "REGION.up.1", 9, 1);
        Thread second = racingWriter(upstream, "REGION.up.2", 5, 2);

        final Holder downstream = new Holder();
        require(select(downstream) > 0L, "downstream selection rejected");

        // One guarded read, immediately republished as this thread's own write
        // of another selected location.
        downstream.shared = upstream.shared;

        String upstreamEvidence = versions(upstream);
        String upstreamRead = lastRead(upstreamEvidence);
        require(upstreamRead.contains("\"resolution\":\"GUARDED\""),
                upstreamEvidence);
        long upstreamReadEvent = readLong(upstreamRead,
                upstreamRead.indexOf("\"readEventId\":")
                        + "\"readEventId\":".length());

        // The version this thread published carries the guarded node itself,
        // not a constant and not a collapsed arm of it.
        String downstreamEvidence = versions(downstream);
        require(downstreamEvidence.contains("\"_type\":\"ReadFromExpression\""),
                "the published version lost its guarded value: "
                        + summarise(downstreamEvidence));
        require(downstreamEvidence.contains("\"readEventId\":"
                        + upstreamReadEvent + ","),
                "the published version is not the node that was read: "
                        + summarise(downstreamEvidence));

        Sink sink = new Sink();
        sink.value = downstream.shared;

        String downstreamRead = lastRead(versions(downstream));
        require(downstreamRead.contains("\"resolution\":\"EXACT\""),
                downstreamRead);
        require(downstreamRead.contains("\"reason\":\"UNIQUE_VERSION\""),
                downstreamRead);

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        // Exactly one guarded node: the exact read handed back the writer's
        // own expression rather than wrapping an unresolved value a second
        // time, which would have made the choice depend on two selectors.
        require(count(read, "\"_type\":\"ReadFromExpression\"") == 1,
                "an exact read of a guarded value re-wrapped it: " + read);
        require(read.contains("\"readEventId\":" + upstreamReadEvent + ","),
                "the reader received a different node: " + read);
        require(read.contains("UP.1.A") && read.contains("UP.2.A"), read);
        require(read.contains("\"selector\":\"rf_unknown\""), read);

        // And the reader's own arithmetic composes onto the guarded node,
        // which is the whole reason an exact read hands the node over.
        sink.derived = downstream.shared + 100;
        String derived = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "derived", "I",
                Integer.valueOf(sink.derived));
        require(derived.contains("\"_op\":\"+\""), summarise(derived));
        require(derived.contains("\"_exp\":\"Y_I_100\""), summarise(derived));
        require(count(derived, "\"_type\":\"ReadFromExpression\"") == 1,
                summarise(derived));
        require(derived.contains("UP.1.A") && derived.contains("UP.2.A"),
                summarise(derived));

        first.join();
        second.join();
    }

    // ------------------------------------------------------------------
    // (3) Selection is what buys provenance.
    // ------------------------------------------------------------------

    private static void anUnselectedNeighbourUnderTheSameContention()
            throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");
        // `neighbour` is deliberately left unselected on the same object.

        final CountDownLatch done = new CountDownLatch(2);
        Runnable writer = new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(
                            "REGION.neighbour", "TASK.neighbour") != 0L) {
                        return;
                    }
                    Input operand = new Input(9);
                    System.symbolizeExactField(operand, Input.class.getName(),
                            "v", "I", "NEIGHBOUR.A");
                    holder.shared = operand.v + 1;
                    holder.neighbour = operand.v + 1;
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        };
        Thread first = new Thread(writer, "neighbour-writer-1");
        Thread second = new Thread(writer, "neighbour-writer-2");
        first.start();
        second.start();
        done.await();
        first.join();
        second.join();

        Sink selectedSink = new Sink();
        selectedSink.value = holder.shared;
        Sink neighbourSink = new Sink();
        neighbourSink.value = holder.neighbour;
        require(selectedSink.value == neighbourSink.value,
                "both fields should hold the same value");

        // The selected field: two competing writers, no answer.
        String selectedRead = System.getSymbolicFieldExpression(
                selectedSink, Sink.class.getName(), "value", "I",
                Integer.valueOf(selectedSink.value));
        require(selectedRead.contains("\"_type\":\"ReadFromExpression\""),
                selectedRead);
        require(selectedRead.contains("\"reason\":\"AMBIGUOUS_WRITERS\""),
                selectedRead);
        String selectedEvidence = versions(holder);
        require(lastRead(selectedEvidence).contains("\"candidateCount\":2"),
                selectedEvidence);
        // INITIAL plus exactly the two contended writes; the neighbour's
        // traffic did not leak into this location's version list.
        require(count(selectedEvidence, "\"fieldVersionId\":") == 3,
                selectedEvidence);

        // The unselected neighbour of the same object, written by the same two
        // threads in the same interval: no versions, no reads, no provenance.
        String neighbourEvidence = System.getSharedFieldVersions(
                holder, Holder.class.getName(), "neighbour", "I");
        require(neighbourEvidence.contains("\"selected\":false"),
                neighbourEvidence);
        require(neighbourEvidence.contains("\"versions\":[]"),
                neighbourEvidence);
        require(neighbourEvidence.contains("\"reads\":[]"),
                "an unselected location must record no read: "
                        + neighbourEvidence);

        String neighbourRead = System.getSymbolicFieldExpression(
                neighbourSink, Sink.class.getName(), "value", "I",
                Integer.valueOf(neighbourSink.value));
        // It answers with the surviving last-writer shadow.  That is a value,
        // not a claim: no guarded choice, no exactly-one, no read-from
        // authority, and nothing that a consumer could mistake for evidence
        // that this writer was proven.
        require(neighbourRead.contains("\"symbolic\":true"), neighbourRead);
        require(!neighbourRead.contains("ReadFromExpression"), neighbourRead);
        require(!neighbourRead.contains("exactlyOne"), neighbourRead);
        require(!neighbourRead.contains("VM_GUARDED_READ_FROM_V1"),
                neighbourRead);
        require(neighbourRead.contains("NEIGHBOUR.A"), neighbourRead);
    }

    // ---- helpers ----------------------------------------------------------

    /**
     * One competing writer, on its own thread and its own region, storing 10
     * through a symbolic input of its own and behind a branch.  The latch says
     * the store completed; it deliberately does not join, because a join is a
     * happens-before edge and these cases are about its absence.
     */
    private static Thread racingWriter(final Holder holder,
                                       final String region, final int seed,
                                       final int shape) throws Exception {
        final CountDownLatch done = new CountDownLatch(1);
        Thread thread = newWriter(holder, region, seed, shape, done);
        thread.start();
        done.await();
        return thread;
    }

    /** The same writer, joined before the next one starts. */
    private static void joinedWriter(final Holder holder, final String region,
                                     final int seed, final int shape)
            throws Exception {
        final CountDownLatch done = new CountDownLatch(1);
        Thread thread = newWriter(holder, region, seed, shape, done);
        thread.start();
        done.await();
        thread.join();
    }

    private static Thread newWriter(final Holder holder, final String region,
                                    final int seed, final int shape,
                                    final CountDownLatch done) {
        final String prefix = symbolOf(region);
        return new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(region, "TASK.writer")
                            != 0L) {
                        return;
                    }
                    Input operand = new Input(seed);
                    System.symbolizeExactField(operand, Input.class.getName(),
                            "v", "I", prefix);
                    long branch = System.markConcolicBranch(
                            "COMPETING.WRITER.GUARD", 1);
                    if (operand.v > 0) {
                        if (shape == 1) {
                            holder.shared = operand.v + 1;
                        } else if (shape == 2) {
                            holder.shared = operand.v * 2;
                        } else {
                            holder.shared = operand.v - 10;
                        }
                    }
                    require(branch > 0L,
                            "writer branch marker was refused");
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, region);
    }

    /** "REGION.trio.1" -> "TRIO.1.A"; the symbol names the writer. */
    private static String symbolOf(String region) {
        return region.substring("REGION.".length()).toUpperCase() + ".A";
    }

    private static long select(Holder holder) {
        return System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "shared", "I");
    }

    private static String versions(Holder holder) {
        return System.getSharedFieldVersions(
                holder, Holder.class.getName(), "shared", "I");
    }

    private static String lastRead(String json) {
        int at = json.lastIndexOf("\"readEventId\"");
        require(at >= 0, "no read was recorded: " + summarise(json));
        return json.substring(at);
    }

    /** The ids of every WRITE version, in publication order. */
    private static long[] writeVersionIds(String json) {
        int reads = json.indexOf("\"reads\":");
        String section = reads < 0 ? json : json.substring(0, reads);
        java.util.List<Long> ids = new java.util.ArrayList<Long>();
        int at = section.indexOf("\"fieldVersionId\":");
        while (at >= 0) {
            long id = readLong(section, at + "\"fieldVersionId\":".length());
            int kind = section.indexOf("\"versionKind\":\"", at);
            if (kind >= 0 && section.startsWith("\"versionKind\":\"WRITE\"",
                    kind)) {
                ids.add(Long.valueOf(id));
            }
            at = section.indexOf("\"fieldVersionId\":", at + 1);
        }
        long[] out = new long[ids.size()];
        for (int index = 0; index < out.length; index++) {
            out[index] = ids.get(index).longValue();
        }
        return out;
    }

    private static long readLong(String json, int start) {
        int end = start;
        while (end < json.length() && Character.isDigit(json.charAt(end))) {
            end++;
        }
        return Long.parseLong(json.substring(start, end));
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

    /** Keeps an assertion message readable when the payload is a whole DAG. */
    private static String summarise(String json) {
        return json.length() <= 1500 ? json
                : json.substring(0, 1500) + "...[" + json.length() + " bytes]";
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
