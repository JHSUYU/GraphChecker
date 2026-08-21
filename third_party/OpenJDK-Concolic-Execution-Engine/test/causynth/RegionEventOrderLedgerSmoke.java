import java.util.concurrent.CountDownLatch;

/**
 * Stage 4 of the shared-field work: one event-id space, one order domain, and
 * a cycle check that refuses a candidate order no execution could have had.
 *
 * Before this the engine had two unrelated notions of "when" -- a per-thread
 * branch sequence and the index of a condition inside one thread's path
 * condition -- and neither could relate anything to another thread.  What this
 * pins down:
 *
 *   1. every channel draws from one id space and lands in one relation:
 *      program order, field write and read, synchronization, value handoff and
 *      region enter/exit are edges of the same graph, distinguished by kind
 *      rather than kept in separate graphs;
 *   2. an exact read-from is an edge; a *guarded* read is not.  An undecided
 *      choice has no causal edge, and drawing one would be exactly the
 *      read-from guess the design forbids;
 *   3. a candidate order that would close a cycle is refused, and refusing it
 *      leaves the relation unchanged;
 *   4. a candidate that keeps the relation acyclic is admitted, and admitting
 *      it orders nothing else.  The relation stays partial: no schedule is
 *      built, and none can be asked for.
 */
public final class RegionEventOrderLedgerSmoke {

    /** Mirrors EventLedger::OrderStatus. */
    private static final int ORDER_OK = 0;
    private static final int ORDER_UNKNOWN_EVENT = -2;
    private static final int ORDER_SELF_EDGE = -3;
    private static final int ORDER_CYCLIC = -4;

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

    /** The sender's side of one symbolic handoff. */
    private static final class Carrier {
        int seed = 41;
        int exported = 0;
    }

    /** The receiver's side: its value arrives concretely. */
    private static final class Landing {
        int value = 0;
    }

    public static void main(String[] args) throws Exception {
        long status = System.startConcolicRegion(
                "REGION.ledger", "TASK.ledger");
        require(status == 0L, "region start rejected");

        oneDomainOverEveryChannel();
        valueHandoffJoinsTheSameDomain();
        exactReadFromIsAnEdgeAndGuardedIsNot();
        cyclicCandidateIsRejected();
        acyclicCandidateIsAdmittedWithoutOrderingAnythingElse();

        System.endConcolic();
        System.out.println("RegionEventOrderLedgerSmoke OK");
    }

    /** (1) One id space; one relation; every channel present. */
    private static void oneDomainOverEveryChannel() throws Exception {
        final Holder holder = new Holder();
        require(select(holder) > 0L, "carrier selection rejected");

        final CountDownLatch done = new CountDownLatch(1);
        Thread writer = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(
                            "REGION.ledger-writer", "TASK.writer") != 0L) {
                        return;
                    }
                    Input operand = new Input(3);
                    System.symbolizeExactField(
                            operand, Input.class.getName(), "v", "I",
                            "LEDGER.A");
                    holder.shared = operand.v + 1;
                    System.endConcolic();
                } finally {
                    done.countDown();
                }
            }
        }, "ledger-writer");
        writer.start();
        done.await();
        writer.join();

        Sink sink = new Sink();
        sink.value = holder.shared;

        String ledger = System.getEventLedger();
        require(ledger.contains("\"eventKind\":\"REGION_ENTER\""), ledger);
        require(ledger.contains("\"eventKind\":\"FIELD_WRITE\""), ledger);
        require(ledger.contains("\"eventKind\":\"FIELD_READ\""), ledger);
        require(ledger.contains("\"eventKind\":\"THREAD_START\""), ledger);
        require(ledger.contains("\"eventKind\":\"THREAD_JOIN\""), ledger);
        require(ledger.contains("\"eventKind\":\"REGION_EXIT\""), ledger);

        require(ledger.contains("\"edgeKind\":\"PROGRAM_ORDER\""), ledger);
        require(ledger.contains("\"edgeKind\":\"SYNCHRONIZATION\""), ledger);
        require(ledger.contains("\"edgeKind\":\"FIELD_READ_FROM\""), ledger);
        require(ledger.contains("\"edgeKind\":\"REGION\""), ledger);

        // A partial order, reported as edges and never as a schedule.
        require(ledger.contains("\"partialOrder\":true"), ledger);
        require(ledger.contains("\"acyclic\":true"), ledger);
        require(ledger.contains("\"domainSaturated\":false"), ledger);
        require(!ledger.contains("schedule"), ledger);

        // Every event id is distinct and drawn from the same counter that the
        // field versions use, so a fieldVersionId is comparable to an eventId.
        String versions = versions(holder);
        long writeVersion = lastWriteVersionId(versions);
        require(ledger.contains("\"eventId\":" + writeVersion + ","),
                "a field version must be an event of the ledger: " + ledger);
    }

    /**
     * (1, continued) A symbolic value handoff is an edge of the same relation.
     *
     * The VM sees one mechanism here -- the session broker -- and RPC
     * send/receive and async executor handoff both go through it, so they
     * share one edge kind. Communication identity remains in the tracing
     * layer; inventing protocol-specific VM edges would duplicate it.
     */
    private static void valueHandoffJoinsTheSameDomain() {
        Carrier sender = new Carrier();
        System.symbolizeExactField(sender, Carrier.class.getName(), "seed",
                "I", "HANDOFF.SEED");
        sender.exported = sender.seed + 1;

        long handle = System.exportExpression(
                sender, Carrier.class.getName(), "exported", "I");
        require(handle > 0L, "export rejected with status " + handle);

        Landing receiver = new Landing();
        receiver.value = sender.exported;
        require(System.attachExpression(
                receiver, Landing.class.getName(), "value", "I", handle)
                > 0L, "attach rejected");

        String ledger = System.getEventLedger();
        require(ledger.contains("\"eventKind\":\"HANDOFF_EXPORT\""), ledger);
        require(ledger.contains("\"eventKind\":\"HANDOFF_ATTACH\""), ledger);
        require(ledger.contains("\"edgeKind\":\"VALUE_HANDOFF\""), ledger);
        long exported = firstEventOfKind(ledger, "HANDOFF_EXPORT");
        long attached = lastEventOfKind(ledger, "HANDOFF_ATTACH");
        require(ledger.contains("{\"beforeEventId\":" + exported
                        + ",\"afterEventId\":" + attached
                        + ",\"edgeKind\":\"VALUE_HANDOFF\"}"),
                ledger);
    }

    /** (2) Exact reads make edges; guarded reads deliberately do not. */
    private static void exactReadFromIsAnEdgeAndGuardedIsNot()
            throws Exception {
        final Holder exactHolder = new Holder();
        require(select(exactHolder) > 0L, "carrier selection rejected");
        Input a = new Input(9);
        System.symbolizeExactField(a, Input.class.getName(), "v", "I",
                "EDGE.A");
        exactHolder.shared = a.v + 1;
        Sink exactSink = new Sink();
        exactSink.value = exactHolder.shared;

        String exactEvidence = versions(exactHolder);
        String exactRead = lastRead(exactEvidence);
        require(exactRead.contains("\"resolution\":\"EXACT\""), exactEvidence);
        long chosen = readLong(exactRead,
                exactRead.indexOf("\"chosenFieldVersionId\":")
                        + "\"chosenFieldVersionId\":".length());
        long exactReadEvent = readLong(exactRead,
                exactRead.indexOf("\"readEventId\":")
                        + "\"readEventId\":".length());
        String ledger = System.getEventLedger();
        require(ledger.contains("{\"beforeEventId\":" + chosen
                        + ",\"afterEventId\":" + exactReadEvent
                        + ",\"edgeKind\":\"FIELD_READ_FROM\"}"),
                "an exact read-from must be an edge: " + ledger);

        // Now the guarded case, with two equal-valued racing writers.
        final Holder racedHolder = new Holder();
        require(select(racedHolder) > 0L, "carrier selection rejected");
        Thread first = racingWriter(racedHolder, "REGION.race1", 9, false);
        Thread second = racingWriter(racedHolder, "REGION.race2", 5, true);
        Sink racedSink = new Sink();
        racedSink.value = racedHolder.shared;

        String racedEvidence = versions(racedHolder);
        String racedRead = lastRead(racedEvidence);
        require(racedRead.contains("\"resolution\":\"GUARDED\""),
                racedEvidence);
        long racedReadEvent = readLong(racedRead,
                racedRead.indexOf("\"readEventId\":")
                        + "\"readEventId\":".length());
        String afterRace = System.getEventLedger();
        require(!afterRace.contains("\"afterEventId\":" + racedReadEvent
                        + ",\"edgeKind\":\"FIELD_READ_FROM\""),
                "a guarded read must contribute no read-from edge: "
                        + afterRace);

        first.join();
        second.join();
    }

    /** (3) A candidate that would close a cycle is refused. */
    private static void cyclicCandidateIsRejected() {
        String ledger = System.getEventLedger();
        long[] pair = firstProgramOrderEdge(ledger);
        long before = pair[0];
        long after = pair[1];

        int edgesBefore = count(ledger, "\"beforeEventId\":");

        // The reverse of an edge the run already exhibited.
        require(System.proposeEventOrder(after, before) == ORDER_CYCLIC,
                "reversing an observed edge must be refused as cyclic");
        // A self edge is not an order at all.
        require(System.proposeEventOrder(before, before) == ORDER_SELF_EDGE,
                "a self edge must be refused");
        // An event that does not exist cannot be ordered.
        require(System.proposeEventOrder(before, 999999999L)
                        == ORDER_UNKNOWN_EVENT,
                "an unknown event must be refused");

        String after1 = System.getEventLedger();
        require(count(after1, "\"beforeEventId\":") == edgesBefore,
                "a refused candidate must leave the relation unchanged");
        require(after1.contains("\"acyclic\":true"), after1);
        require(!after1.contains("\"edgeKind\":\"CANDIDATE\""), after1);
    }

    /** (4) An acyclic candidate is admitted and orders nothing else. */
    private static void acyclicCandidateIsAdmittedWithoutOrderingAnythingElse() {
        String ledger = System.getEventLedger();
        // Two distinct recorded events whose forward order is acyclic.
        long mine = firstEventOfKind(ledger, "REGION_ENTER");
        long other = lastEventOfKind(ledger, "FIELD_WRITE");
        require(mine != 0 && other != 0 && mine != other, ledger);

        int before = count(ledger, "\"edgeKind\":\"CANDIDATE\"");
        require(System.proposeEventOrder(mine, other) == ORDER_OK,
                "an acyclic candidate must be admitted");
        String admitted = System.getEventLedger();
        require(count(admitted, "\"edgeKind\":\"CANDIDATE\"") == before + 1,
                admitted);
        require(admitted.contains("\"acyclic\":true"), admitted);

        // Admitting it ordered only that pair: the reverse is now cyclic, but
        // nothing else became ordered, and no schedule was produced.
        require(System.proposeEventOrder(other, mine) == ORDER_CYCLIC,
                "the admitted edge should now forbid its reverse");
        require(admitted.contains("\"partialOrder\":true"), admitted);
    }

    // ---- helpers ----------------------------------------------------------

    private static Thread racingWriter(final Holder holder,
                                       final String region, final int seed,
                                       final boolean doubleIt)
            throws Exception {
        final CountDownLatch done = new CountDownLatch(1);
        Thread thread = new Thread(new Runnable() {
            public void run() {
                try {
                    if (System.startConcolicRegion(region, "TASK.race")
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
        // No join before the read: the point of this case is a read with no
        // proven order at all.
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

    private static long lastWriteVersionId(String json) {
        int reads = json.indexOf("\"reads\":");
        String versionsPart = reads < 0 ? json : json.substring(0, reads);
        int at = versionsPart.lastIndexOf("\"fieldVersionId\":");
        require(at >= 0, json);
        return readLong(versionsPart, at + "\"fieldVersionId\":".length());
    }

    private static long[] firstProgramOrderEdge(String ledger) {
        int at = ledger.indexOf("\"edgeKind\":\"PROGRAM_ORDER\"");
        require(at >= 0, "no program-order edge: " + ledger);
        int objectStart = ledger.lastIndexOf("{\"beforeEventId\":", at);
        require(objectStart >= 0, ledger);
        long before = readLong(ledger,
                objectStart + "{\"beforeEventId\":".length());
        int afterKey = ledger.indexOf("\"afterEventId\":", objectStart);
        long after = readLong(ledger,
                afterKey + "\"afterEventId\":".length());
        return new long[]{before, after};
    }

    private static long firstEventOfKind(String ledger, String kind) {
        int at = ledger.indexOf("\"eventKind\":\"" + kind + "\"");
        if (at < 0) return 0;
        int idKey = ledger.lastIndexOf("\"eventId\":", at);
        if (idKey < 0) return 0;
        return readLong(ledger, idKey + "\"eventId\":".length());
    }

    private static long lastEventOfKind(String ledger, String kind) {
        int at = ledger.lastIndexOf("\"eventKind\":\"" + kind + "\"");
        if (at < 0) return 0;
        int idKey = ledger.lastIndexOf("\"eventId\":", at);
        if (idKey < 0) return 0;
        return readLong(ledger, idKey + "\"eventId\":".length());
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
