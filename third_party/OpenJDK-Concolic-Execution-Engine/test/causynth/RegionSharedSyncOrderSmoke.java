import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Stage 3 of the shared-field work: the actions that create order now record
 * it, and a read that order can decide resolves exactly instead of guarded.
 *
 * A read of a location two threads wrote remains guarded until an explicitly
 * modeled lifecycle, volatile, or atomic relation decides it. The cases here
 * separate those authorities from an unordered control:
 *
 *   1. identical unordered writes stay guarded;
 *   2. a thread-join edge makes a joined writer's store visible, so the
 *      reader's own later write dominates it;
 *   3. an AtomicInteger/AtomicLong RMW publishes one linearized relation,
 *      `new = old + delta`, as a version other readers can select;
 *   4. compareAndSet publishes only the arm this run took: a successful CAS
 *      publishes `update` guarded by `old == expect`, and a failed one
 *      publishes no version at all, because no store happened.
 */
public final class RegionSharedSyncOrderSmoke {

    private static final class Holder {
        int shared = 0;
        volatile int flag = 0;
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
                "REGION.sync-order", "TASK.sync-order");
        require(status == 0L, "region start rejected");

        unsynchronizedControlStaysGuarded();
        volatileProvenanceMakesAPlainReadExact();
        joinOrderedReadIsExact();
        atomicRmwPublishesItsRelation();
        casPublishesOnlyTheObservedArm();
        ledgerRecordsTheOrderSources();

        System.endConcolic();
        System.out.println("RegionSharedSyncOrderSmoke OK");
    }

    /** (1) Identical writes without a modeled order stay guarded. */
    private static void unsynchronizedControlStaysGuarded() throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        Thread first = plainWriter(holder, "REGION.plain1", 9, false);
        Thread second = plainWriter(holder, "REGION.plain2", 5, true);

        Sink sink = new Sink();
        sink.value = holder.shared;
        require(sink.value == 10, "both writers should have stored 10");

        String evidence = versions(holder);
        String last = lastRead(evidence);
        require(last.contains("\"resolution\":\"GUARDED\""),
                "without order the writers must stay ambiguous: " + evidence);
        require(last.contains("\"reason\":\"AMBIGUOUS_WRITERS\""), evidence);

        first.join();
        second.join();
    }

    /**
     * Volatile provenance, with the read of the flag as the only variable.
     *
     * A volatile read happens-after the write it read and after no other, so
     * the clock it joins comes from the resolved version rather than from a
     * per-location release slot.  Joining "the location's latest release"
     * instead would let a reader claim to have seen a write that had not
     * executed when it read -- an invented happens-before, which is worse than
     * no edge.  The consequence is visible here: the plain read is guarded
     * until the flag has actually been read, and exact afterwards.
     */
    private static void volatileProvenanceMakesAPlainReadExact()
            throws Exception {
        final Holder holder = new Holder();
        holder.shared = 10;
        require(select(holder) > 0L, "carrier selection rejected");
        require(System.selectSharedFieldCarrier(
                holder, Holder.class.getName(), "flag", "I") > 0L,
                "volatile carrier selection rejected");

        // The writer stores the shared value first and then publishes the
        // flag, which is the ordinary release idiom.
        final CountDownLatch done = new CountDownLatch(1);
        Thread publisher = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(
                            "REGION.publisher", "TASK.writer") != 0L) {
                        return;
                    }
                    Input operand = new Input(9);
                    System.symbolizeExactField(
                            operand, Input.class.getName(), "v", "I",
                            "VOLATILE.A");
                    holder.shared = operand.v + 1;
                    holder.flag = 7;
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, "publisher");
        publisher.start();
        done.await();

        // Control, before the flag has been read: the writer's store and the
        // value the location started with are both 10 and nothing separates
        // them, so the read is guarded.
        Sink beforeAcquire = new Sink();
        beforeAcquire.value = holder.shared;
        String control = lastRead(versions(holder));
        require(control.contains("\"resolution\":\"GUARDED\""),
                "without the flag read there is no order: " + control);

        // Read the flag.  Its own value distinguishes it from the state the
        // location started in, so that read is exact, and it is what carries
        // the writer's clock across.
        Sink flagSink = new Sink();
        flagSink.value = holder.flag;
        require(flagSink.value == 7, "the publisher should have set the flag");
        String flagRead = lastRead(System.getSharedFieldVersions(
                holder, Holder.class.getName(), "flag", "I"));
        require(flagRead.contains("\"resolution\":\"EXACT\""), flagRead);

        // The same plain read, now ordered.
        Sink afterAcquire = new Sink();
        afterAcquire.value = holder.shared;
        String ordered = lastRead(versions(holder));
        require(ordered.contains("\"resolution\":\"EXACT\""),
                "the volatile acquire should have ordered it: " + ordered);
        require(ordered.contains("\"reason\":\"SYNC_ORDERED\""), ordered);

        String read = System.getSymbolicFieldExpression(
                afterAcquire, Sink.class.getName(), "value", "I",
                Integer.valueOf(afterAcquire.value));
        require(read.contains("VOLATILE.A"), read);

        String ledger = System.getEventLedger();
        require(ledger.contains("\"eventKind\":\"VOLATILE_WRITE\""), ledger);
        require(ledger.contains("\"eventKind\":\"VOLATILE_READ\""), ledger);
        require(ledger.contains("\"detail\":\"ACQUIRE\""), ledger);

        publisher.join();
    }

    /** (2) A joined writer's store is visible, so it can be dominated. */
    private static void joinOrderedReadIsExact() throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        Thread writer = plainWriter(holder, "REGION.joined", 9, false);
        writer.join();

        // This thread's own store happens-after the joined one, so it
        // dominates it even though both stored 10.
        Input a = new Input(5);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "JOIN.A");
        holder.shared = a.v * 2;

        Sink sink = new Sink();
        sink.value = holder.shared;

        String evidence = versions(holder);
        String last = lastRead(evidence);
        require(last.contains("\"resolution\":\"EXACT\""), evidence);
        require(last.contains("\"reason\":\"SYNC_ORDERED\""), evidence);

        String read = System.getSymbolicFieldExpression(
                sink, Sink.class.getName(), "value", "I",
                Integer.valueOf(sink.value));
        require(read.contains("JOIN.A"), read);
    }

    /** (3) One RMW, one linearized relation, published as a version. */
    private static void atomicRmwPublishesItsRelation() {
        AtomicInteger counter = new AtomicInteger(7);
        long initial = System.selectSharedFieldCarrier(
                counter, AtomicInteger.class.getName(), "value", "I");
        require(initial > 0L, "atomic carrier selection rejected: " + initial);

        Input a = new Input(4);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "RMW.DELTA");
        int returned = counter.addAndGet(a.v);
        require(returned == 11, "concrete RMW result should be 11");

        String evidence = System.getSharedFieldVersions(
                counter, AtomicInteger.class.getName(), "value", "I");
        require(evidence.contains("\"versionKind\":\"RMW\""), evidence);
        // new = old + delta, with the delta the symbolic operand.
        require(evidence.contains("RMW.DELTA"), evidence);
        require(evidence.contains("\"_op\":\"+\""), evidence);
        require(evidence.contains("\"fingerprint\":11"), evidence);
        // An RMW is a volatile access, so its version is marked as one.
        require(evidence.contains("\"volatileWrite\":true"), evidence);

        AtomicLong longCounter = new AtomicLong(3L);
        require(System.selectSharedFieldCarrier(
                longCounter, AtomicLong.class.getName(), "value", "J") > 0L,
                "long atomic carrier selection rejected");
        require(longCounter.getAndIncrement() == 3L, "getAndIncrement");
        String longEvidence = System.getSharedFieldVersions(
                longCounter, AtomicLong.class.getName(), "value", "J");
        require(longEvidence.contains("\"versionKind\":\"RMW\""), longEvidence);
        require(longEvidence.contains("\"fingerprint\":4"), longEvidence);
    }

    /** (4) CAS: the taken arm is published, the untaken one is not modeled. */
    private static void casPublishesOnlyTheObservedArm() {
        AtomicInteger cell = new AtomicInteger(5);
        require(System.selectSharedFieldCarrier(
                cell, AtomicInteger.class.getName(), "value", "I") > 0L,
                "cas carrier selection rejected");

        Input update = new Input(42);
        System.symbolizeExactField(update, Input.class.getName(), "v", "I",
                "CAS.UPDATE");

        require(cell.compareAndSet(5, update.v), "the CAS should succeed");
        String afterSuccess = System.getSharedFieldVersions(
                cell, AtomicInteger.class.getName(), "value", "I");
        require(count(afterSuccess, "\"versionKind\":\"RMW\"") == 1,
                afterSuccess);
        require(afterSuccess.contains("CAS.UPDATE"), afterSuccess);
        require(afterSuccess.contains("\"fingerprint\":42"), afterSuccess);
        // The published arm carries `old == expect` in its guard, so a solver
        // cannot select this writer while denying the comparison that let it
        // win.
        require(afterSuccess.contains("\"_op\":\"==\""), afterSuccess);

        int versionsBefore = count(afterSuccess, "\"fieldVersionId\"");
        require(!cell.compareAndSet(5, 99), "the second CAS should fail");
        String afterFailure = System.getSharedFieldVersions(
                cell, AtomicInteger.class.getName(), "value", "I");
        // No store happened, so no version exists.  Publishing one for the
        // arm that was not taken would put a value nothing wrote into every
        // later reader's choice.
        require(count(afterFailure, "\"fieldVersionId\"") == versionsBefore,
                "a failed CAS must publish no version: " + afterFailure);
        require(!afterFailure.contains("\"fingerprint\":99"), afterFailure);
        require(cell.get() == 42, "the failed CAS must not have stored");

        String ledger = System.getEventLedger();
        require(ledger.contains("OBSERVED_SUCCESS new = update"), ledger);
        require(ledger.contains("OBSERVED_FAILURE old != expect"), ledger);
    }

    /** The ledger is one event-id space over all of the above. */
    private static void ledgerRecordsTheOrderSources() {
        String ledger = System.getEventLedger();
        require(ledger.contains("\"kind\":\"SESSION_EVENT_LEDGER\""), ledger);
        require(ledger.contains("\"recording\":true"), ledger);
        require(ledger.contains("\"eventKind\":\"THREAD_START\""), ledger);
        require(ledger.contains("\"eventKind\":\"THREAD_JOIN\""), ledger);
        require(ledger.contains("\"eventKind\":\"ATOMIC_RMW\""), ledger);
        require(ledger.contains("\"eventKind\":\"ATOMIC_CAS\""), ledger);

        // One id space, strictly increasing: ids are allocation evidence, and
        // a smaller id is not a claim that its event happened first.
        long previous = 0;
        int at = ledger.indexOf("\"eventId\":");
        while (at >= 0) {
            long id = readLong(ledger, at + "\"eventId\":".length());
            require(id > previous, "event ids must be distinct and ordered");
            previous = id;
            at = ledger.indexOf("\"eventId\":", at + 1);
        }
        require(previous > 0, "the ledger should not be empty");
    }

    // ---- helpers ----------------------------------------------------------

    /** A writer with no modeled cross-thread synchronization. */
    private static Thread plainWriter(final Holder holder,
                                      final String region, final int seed,
                                      final boolean doubleIt)
            throws Exception {
        return writer(holder, region, seed, doubleIt);
    }

    private static Thread writer(final Holder holder, final String region,
                                 final int seed, final boolean doubleIt)
            throws Exception {
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
                    holder.shared = doubleIt
                            ? operand.v * 2 : operand.v + 1;
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
        require(at >= 0, "no read was recorded: " + json);
        return json.substring(at);
    }

    /** The id of the last version published before the reads section. */
    private static long lastWriteVersionId(String json) {
        int reads = json.indexOf("\"reads\":");
        String versionsPart = reads < 0 ? json : json.substring(0, reads);
        int at = versionsPart.lastIndexOf("\"fieldVersionId\":");
        require(at >= 0, json);
        return readLong(versionsPart, at + "\"fieldVersionId\":".length());
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

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
