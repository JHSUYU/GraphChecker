import java.util.concurrent.CountDownLatch;

/**
 * Stage 2 of the shared-field work: a read of a selected location is either
 * exact or explicitly guarded, and never a guess.
 *
 * The cases here are the provenance rules, one test each:
 *
 *   1. one writer resolves exactly.  The reader receives that writer's own
 *      expression, so its own arithmetic composes straight onto it -- which is
 *      the entire point of proving provenance rather than wrapping it;
 *   2. two writers that stored *different* values are separated by the value
 *      the read actually returned.  That is an observation, not a guess: a
 *      writer that stored 11 is not the source of a read that returned 10;
 *   3. two writers that stored the *same* value are not separated at all.  The
 *      VM refuses to pick one and attaches exactlyOne(rf1, rf2, rf_unknown)
 *      with ite(rf1, E1, ite(rf2, E2, Unknown)), each candidate carrying its
 *      writer's path guard and the read cut that would have to hold for it;
 *   4. an untracked store -- one the hooks did not observe -- is detected by
 *      the value it leaves behind, permanently marks the location's writer set
 *      incomplete, and forces every later read of it to stay guarded.  This is
 *      what rf_unknown is for: with the writer set open, an UNSAT answer over
 *      this location describes the tracked writers, not the program.
 */
public final class RegionSharedReadFromSmoke {

    private static final class Holder {
        int shared = 0;
    }

    private static final class Input {
        int v;
        Input(int v) { this.v = v; }
    }

    private static final class Sink {
        int value = 0;
    }

    public static void main(String[] args) throws Exception {
        long status = System.startConcolicRegion(
                "REGION.read-from", "TASK.read-from");
        require(status == 0L, "region start rejected");

        oneWriterResolvesExactly();
        differentValuesResolveExactly();
        equalValuedWritersProduceGuardedChoice();
        untrackedWriterOpensTheWriterSet();
        arrayElementsResolveTheSameWay();

        System.endConcolic();
        System.out.println("RegionSharedReadFromSmoke OK");
    }

    /** (1) One writer, and the reader gets its expression, not a wrapper. */
    private static void oneWriterResolvesExactly() {
        Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        Input a = new Input(9);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "EXACT.A");
        holder.shared = a.v + 1;

        Sink sink = new Sink();
        // The read composes with the reader's own arithmetic.  If the reader
        // had received a wrapper instead of the writer's node, this would be
        // an addition over a read-from selection rather than over A + 1.
        sink.value = holder.shared + 100;

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(read.contains("\"kind\":\"SYMBOLIC_FIELD\""), read);
        require(read.contains("EXACT.A"), read);
        require(!read.contains("ReadFromExpression"),
                "an exact read must not be wrapped: " + read);

        String evidence = versions(holder);
        require(lastRead(evidence).contains("\"resolution\":\"EXACT\""),
                evidence);
        require(lastRead(evidence).contains("\"reason\":\"UNIQUE_VERSION\""),
                evidence);
        require(lastRead(evidence).contains("\"candidateCount\":1"), evidence);
    }

    /** (2) Unequal values: the observation itself separates the writers. */
    private static void differentValuesResolveExactly() throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        // One competing writer on another thread, storing a different value.
        Thread competitor = runWriter(holder, "REGION.diff", 4, false, false);

        // This thread's own write is the one the read returns.
        Input a = new Input(9);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "DIFF.A");
        holder.shared = a.v + 1;

        Sink sink = new Sink();
        sink.value = holder.shared;

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(read.contains("DIFF.A"), read);
        require(!read.contains("ReadFromExpression"), read);

        String evidence = versions(holder);
        String last = lastRead(evidence);
        require(last.contains("\"resolution\":\"EXACT\""), evidence);
        require(last.contains("\"reason\":\"VALUE_DISTINGUISHED\""), evidence);
        require(last.contains("\"candidateCount\":1"), evidence);
        // The competing writer really was recorded; it was excluded by the
        // value the read returned, not by never having been seen.
        require(count(evidence, "\"versionKind\":\"WRITE\"") == 2, evidence);
        competitor.join();
    }

    /** (3) Equal values: refuse to choose, and say so in the expression. */
    private static void equalValuedWritersProduceGuardedChoice()
            throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        // A + 1 == 10 on one thread, B * 2 == 10 on another.  Both take a
        // branch first, so both carry a real path guard.
        Thread first = runWriter(holder, "REGION.w1", 9, false, true);
        Thread second = runWriter(holder, "REGION.w2", 5, true, true);

        Sink sink = new Sink();
        sink.value = holder.shared;
        require(sink.value == 10, "both writers should have stored 10");

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(read.contains("\"_type\":\"ReadFromExpression\""), read);
        require(read.contains("\"resolution\":\"GUARDED\""), read);
        require(read.contains("\"reason\":\"AMBIGUOUS_WRITERS\""), read);

        // exactlyOne over both writers and the unknown one.
        require(read.contains("\"exactlyOne\":[\"rf1\",\"rf2\",\"rf_unknown\"]"),
                read);
        require(read.contains("\"selector\":\"rf_unknown\""), read);
        require(read.contains("unknownWriter"), read);
        // The ite chain, bottoming out in the unknown arm.
        require(count(read, "\"_type\":\"IteExpression\"") == 2, read);

        // Both writers' expressions survive in the node -- neither was picked
        // and neither was dropped.
        require(read.contains("REGION.w1.A"), read);
        require(read.contains("REGION.w2.A"), read);
        // Each candidate carries its writer's path guard.
        require(count(read, "\"pathGuard\":null") == 1,
                "only rf_unknown may be unguarded: " + read);
        // And the sparse read cut for each of them.
        require(count(read, "\"kind\":\"WRITE_BEFORE_READ\"") == 2, read);
        require(count(read, "\"kind\":\"OTHER_WRITE_OUTSIDE_CUT\"") == 2, read);
        require(read.contains("\"kind\":\"UNKNOWN_WRITE_BEFORE_READ\""), read);

        String evidence = versions(holder);
        String last = lastRead(evidence);
        require(last.contains("\"resolution\":\"GUARDED\""), evidence);
        require(last.contains("\"chosenFieldVersionId\":0"),
                "a guarded read must choose nothing: " + evidence);
        require(last.contains("\"candidateCount\":2"), evidence);
        first.join();
        second.join();
    }

    /** (4) A store the hooks never saw opens the writer set for good. */
    private static void untrackedWriterOpensTheWriterSet() {
        Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        Input a = new Input(9);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "GAP.A");
        holder.shared = a.v + 1;

        // A store the symbolic interpreter does not observe.  Pausing is the
        // reachable stand-in here for the JNI/reflective/compiled writers a
        // real workload has; either way the version store never sees it.
        System.pauseConcolicPathCondition();
        holder.shared = 4242;
        System.resumeConcolicPathCondition();

        Sink sink = new Sink();
        sink.value = holder.shared;

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(read.contains("\"_type\":\"ReadFromExpression\""), read);
        require(read.contains("\"reason\":\"UNTRACKED_WRITER\""), read);
        // Nothing tracked can have produced this value, so the unknown writer
        // is the only candidate -- and it is present, which is what keeps the
        // formula from asserting that the tracked writers were all of them.
        require(read.contains("\"exactlyOne\":[\"rf_unknown\"]"), read);
        require(read.contains("\"writerSetComplete\":false"), read);

        String evidence = versions(holder);
        require(evidence.contains("\"writerSetComplete\":false"), evidence);

        // The gap is permanent: a later read that *could* have been exact is
        // still guarded, because the location has already been shown to have
        // writers the run did not observe.
        holder.shared = a.v + 1;
        Sink later = new Sink();
        later.value = holder.shared;
        String afterGap = System.getSymbolicFieldExpression(
                later, Sink.class.getName(), "value", "I",
                Integer.valueOf(later.value));
        require(afterGap.contains("\"_type\":\"ReadFromExpression\""),
                afterGap);
        require(afterGap.contains("\"reason\":\"INCOMPLETE_WRITER_SET\""),
                afterGap);
        require(afterGap.contains("\"selector\":\"rf_unknown\""), afterGap);
    }

    /**
     * A fixed-shape array element is one slot like any other: its writes are
     * versioned per index and its reads resolve by the same rules.  The
     * neighbouring element is not selected, so it keeps the existing container
     * relation untouched -- selection bounds the cost here too.
     */
    private static void arrayElementsResolveTheSameWay() throws Exception {
        final int[] slots = new int[]{0, 0, 0};
        require(System.selectSharedElementCarrier(slots, 1) > 0L,
                "element selection rejected");

        Input a = new Input(9);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "ARRAY.A");
        slots[1] = a.v + 1;

        Sink exact = new Sink();
        exact.value = slots[1];
        String exactRead = System.getSymbolicFieldExpression(
                exact, Sink.class.getName(), "value", "I",
                Integer.valueOf(exact.value));
        require(exactRead.contains("ARRAY.A"), exactRead);
        require(!exactRead.contains("ReadFromExpression"), exactRead);

        // A competing writer on another thread stores the same value into the
        // same slot.  Nothing separates them, so the read stays guarded.
        final CountDownLatch done = new CountDownLatch(1);
        Thread thread = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(
                            "REGION.array-writer", "TASK.writer") != 0L) {
                        return;
                    }
                    Input operand = new Input(5);
                    System.symbolizeExactField(
                            operand, Input.class.getName(), "v", "I",
                            "ARRAY.B");
                    slots[1] = operand.v * 2;
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, "array-writer");
        thread.start();
        done.await();

        Sink guardedSink = new Sink();
        guardedSink.value = slots[1];
        String guarded = System.getSymbolicFieldExpression(
                guardedSink, Sink.class.getName(), "value", "I",
                Integer.valueOf(guardedSink.value));
        require(guarded.contains("\"_type\":\"ReadFromExpression\""), guarded);
        require(guarded.contains("\"locationKind\":\"ARRAY_ELEMENT\""),
                guarded);
        require(guarded.contains("\"slot\":1"), guarded);
        require(guarded.contains("ARRAY.A"), guarded);
        require(guarded.contains("ARRAY.B"), guarded);
        require(guarded.contains("\"selector\":\"rf_unknown\""), guarded);

        // The unselected neighbour keeps the ordinary container relation and
        // records no read at all.
        Sink neighbour = new Sink();
        neighbour.value = slots[2];
        String untouched = System.getSharedElementVersions(slots, 2);
        require(untouched.contains("\"selected\":false"), untouched);
        thread.join();
    }

    // ---- helpers ----------------------------------------------------------

    /**
     * Runs one competing writer on its own thread and its own region, storing
     * either {@code seed * 2} or {@code seed + 1} through a symbolic input of
     * its own.  With {@code guarded} the store is taken on a branch, so the
     * version it publishes carries a real path guard.
     */
    private static Thread runWriter(final Holder holder, final String region,
                                    final int seed, final boolean doubleIt,
                                    final boolean guarded) throws Exception {
        final CountDownLatch done = new CountDownLatch(1);
        Thread thread = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(region, "TASK.writer")
                            != 0L) {
                        return;
                    }
                    Input operand = new Input(seed);
                    System.symbolizeExactField(
                            operand, Input.class.getName(), "v", "I",
                            region + ".A");
                    if (!guarded) {
                        holder.shared = doubleIt
                                ? operand.v * 2 : operand.v + 1;
                    } else {
                        long branch = System.markConcolicBranch(
                                "SHARED.READ_FROM.WRITER", 1);
                        if (operand.v > 0) {
                            holder.shared = doubleIt
                                    ? operand.v * 2 : operand.v + 1;
                        }
                        require(branch > 0L,
                                "writer branch marker was refused");
                    }
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, region);
        thread.start();
        // The latch says the store completed; it deliberately does not join.
        // Joining would put a happens-before edge between this writer and the
        // reader below, and the cases here are about what the VM does when
        // there is no such edge -- that is, an ordinary data race.  Ordering
        // that *is* proven is the subject of RegionSharedSyncOrderSmoke.
        done.await();
        return thread;
    }

    private static long select(Holder holder) {
        return System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "shared", "I");
    }

    private static String versions(Holder holder) {
        return System.getSharedFieldVersions(
                holder, Holder.class.getName(), "shared", "I");
    }

    /** The most recently recorded read entry, as a substring. */
    private static String lastRead(String json) {
        int at = json.lastIndexOf("\"readEventId\"");
        require(at >= 0, "no read was recorded: " + json);
        return json.substring(at);
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

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
