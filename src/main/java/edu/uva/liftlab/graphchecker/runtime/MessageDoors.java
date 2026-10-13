package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

/**
 * THE message doors a system's transports call, whatever the system: a
 * request or a response leaves (outbound) carrying the sender's GraphChecker
 * context and the symbolic values it exports, and arrives (inbound) where the
 * receiver installs them for as long as it serves that message.  Its values
 * are the ports the thread staged: a declared row's, and the message fields
 * of the protobuf message the door is handed, which the door walks
 * ({@link MessageCodec}); a message parsed inside the exchange is walked
 * again ({@link #parsed}), binding each element to it.  Plus the workload's
 * side of attribution: nodes and their aliases, request scopes, the
 * recorded window, daemon ticks and scopes carried across a queue.
 *
 * <p>A transport keeps only what is its own: where its header travels (a
 * Hadoop RPC header field, an HTTP header), how it names an exchange (its
 * correlation id) and which half a message is.  The Hadoop shim ({@code
 * org.apache.hadoop.ipc.CausynthMessagePropagation}: IPC, the SASL exchange
 * and the DataTransfer ops) and the Solr trees (HTTP) call this class.</p>
 *
 * <p>One inbound exchange per thread: installing the next one ends the one
 * before it, and so does an outbound message, whose sender is no longer
 * serving what it received.</p>
 */
public final class MessageDoors {
    public static final String REQUEST = "REQUEST";
    public static final String RESPONSE = "RESPONSE";

    private static final ThreadLocal<Inbound> CURRENT = new ThreadLocal<>();

    /**
     * What each version of a shared store carried when it was written
     * ({@link #stored}), by transport and key.  The store is the nodes' own
     * (ZooKeeper, in a cluster that runs in one JVM): the table is its
     * metadata, not a channel of the engine's.
     */
    private static final Map<String, Outbound> STORED =
            new ConcurrentHashMap<String, Outbound>();
    /** Each node's view and version a decode re-pointed it to, once,
     *  inside the window or before it ({@link #decode}). */
    private static final Set<String> REPOINTED =
            ConcurrentHashMap.newKeySet();
    /**
     * The writes to a shared store in flight ({@link #storing}), by
     * transport and token.  Guarded by itself; every {@link #storeEnded}
     * notifies the reads waiting on it ({@link #filed}).
     */
    private static final Map<String, Map<Long, Write>> STORING =
            new HashMap<String, Map<Long, Write>>();
    private static final AtomicLong STORES = new AtomicLong();
    /**
     * How long a read waits for the writes in flight to file its version,
     * in ms, while none of them is filing: a write before its store's call
     * may be one the schedule holds behind the reader, which would
     * otherwise wait for the watchdog.
     */
    static final long FILED_WAIT_MS = 2000L;

    /**
     * How long a read waits, in ms, while a write in flight is filing
     * ({@link #stored} began: past its store's call, it takes no turn before
     * it files).  Filing exports the document's leaves under the VM, which
     * takes seconds (solr-18413 Z2V: the Overseer queue item MigrateCmd
     * wrote, read 2 s into its filing, paired with no write, and the chain
     * from the clock to the fatal broke there).
     */
    static final long FILING_WAIT_MS = 60000L;

    /** One write in flight: the thread making it and the location it
     *  writes. */
    private static final class Write {
        private final Thread thread;
        private final String location;
        /** Whether {@link #stored} registered it: past its store's call,
         *  filing ({@link #FILING_WAIT_MS}). */
        private final boolean filing;

        private Write(Thread thread, String location, boolean filing) {
            this.thread = thread;
            this.location = location;
            this.filing = filing;
        }

        /**
         * Whether a version read at {@code path} may be this write's: the
         * location itself, or a child named by its prefix -- a sequential
         * create's, whose name the store completes -- never a deeper one.
         */
        private boolean makes(String path) {
            return path.equals(location) || path.startsWith(location)
                    && path.indexOf('/', location.length()) < 0;
        }
    }

    /**
     * While the thread runs a store's notification ({@link #notified}): its
     * kind until a read names its cause, {@code null} after (and outside).
     */
    private static final ThreadLocal<String> NOTIFIED = new ThreadLocal<>();
    /**
     * How many store notifications this thread is delivering ({@link
     * #notified}), for the whole callback: a publication on it is a
     * notification's, which a pairing's hold may defer ({@link
     * #publishing}).  Unlike {@link #NOTIFIED}, which the callback's first
     * read of its cause clears, it stands until the callback returns.
     */
    private static final ThreadLocal<Integer> DELIVERING =
            ThreadLocal.withInitial(() -> 0);
    /**
     * How many notifications of one kind on one node have read each version
     * ({@link #fetched}).  Two watchers of one kind on one node both parse a
     * version (Solr registers a StateWatcher per refresh): the second parse
     * was the first's address, so the plan kept one, and SOLR-18413's leader
     * read the objects of the parse no replay recorded.
     */
    private static final Map<String, Integer> DELIVERIES =
            new ConcurrentHashMap<String, Integer>();

    private MessageDoors() {
    }

    /**
     * The request scope of the calling thread, as a value the work it is
     * creating can carry to whatever thread later sends it.
     */
    public static Object captureScope() {
        return guarded("captureScope", null, null,
                CausynthTraceRecorder::captureScope);
    }

    /**
     * One message leaves: its trace context and the symbolic values the
     * sender exported (the ports a {@code WIRE_FLOW} row declares), to
     * travel with it.
     *
     * @param scope the scope the work carries ({@link #captureScope}), or
     *              {@code null} for the calling thread's own
     */
    public static Outbound outbound(String transport, String correlationId,
                                    String attemptId, String half,
                                    Object localOwner, Object scope) {
        return send(transport, correlationId, attemptId, half, localOwner,
                scope, "", null);
    }

    /**
     * The same, the message leaving with the protobuf {@code message} it
     * carries: the door walks it, every message field's value carried
     * ({@link MessageCodec#send}).
     */
    public static Outbound outbound(String transport, String correlationId,
                                    String attemptId, String half,
                                    Object localOwner, Object scope,
                                    Object message) {
        return send(transport, correlationId, attemptId, half, localOwner,
                scope, "", message);
    }

    /**
     * One request leaves naming the operation it asks for ({@code verb}, a
     * constant its door reads off the request: a Hadoop RPC's protocol and
     * method), so its producer endpoint and its SEND are that operation's
     * (IDENTITY §4): a DataNode turn that sends a heartbeat before a block
     * report, where the recorded turn sent the report alone, no longer gives
     * the heartbeat the report's identity (hdfs-adhoc-15).
     */
    public static Outbound outboundRequest(String transport,
                                           String correlationId,
                                           String attemptId,
                                           Object localOwner, Object scope,
                                           String verb, Object message) {
        return send(transport, correlationId, attemptId, REQUEST,
                localOwner, scope, verb, message);
    }

    private static Outbound send(String transport, String correlationId,
                                 String attemptId, String half,
                                 Object localOwner, Object scope,
                                 String verb, Object message) {
        try {
            // Staged before the door files what the message carries.
            MessageCodec.send(message);
            String trace = CausynthTraceRecorder.outboundExchange(transport,
                    correlationId, attemptId, half, localOwner, scope,
                    trimmed(verb));
            String symbolic = SymbolicMessageEnvelope.takeOutbound();
            return trace.isEmpty() && symbolic.isEmpty() ? Outbound.EMPTY
                    : new Outbound(correlationId, attemptId, trace,
                    symbolic);
        } catch (RuntimeException fault) {
            doorFault("send " + transport + " " + correlationId, fault);
            return Outbound.EMPTY;
        }
    }

    /**
     * A request of {@code transport} starts on this thread, at its client's
     * invoke point, before the client's call.  A RESPONSE the thread
     * received is over: the request is the thread's own work, not that
     * response's (round SL1-3, hdfs-adhoc-52: every request the test made
     * stood on the previous response's anchor, chaining each NameNode
     * context onto every earlier exchange), as a node startup or a daemon's
     * turn ends what it served ({@link #beginTick}).  A REQUEST the thread
     * serves stands: a handler's nested call is its call's.  The request is
     * in hand, named by {@code verb}, attempt {@code attempt} of it (a retry
     * of one call), in a level of its own counted per verb ({@code
     * Identity#requestStarting}).
     *
     * @return what {@link #requestEnded} takes, in a finally
     */
    public static long requestStarting(String transport, String verb,
                                       int attempt) {
        try {
            callStarting();
            return Identity.requestStarting(Endpoint.messageSite(
                    trimmed(transport), REQUEST, trimmed(verb)), verb,
                    attempt);
        } catch (RuntimeException fault) {
            doorFault("requestStarting " + transport + " " + verb, fault);
            return 0L;
        }
    }

    /**
     * A client's call starts on this thread whose requests start below it
     * ({@link #requestStarting}): a cloud client's attempt at one call,
     * which it routes over its nodes' clients and may hand to its pool.  A
     * RESPONSE the thread received is over, as at a request's start, so
     * neither the routing nor the work it hands off stands on the last
     * response the thread read (round SG1, solr-adhoc-13: a cloud client's
     * parallel updates stood on the response to its previous attempt, and
     * the replay's timing had another response read last).
     */
    public static void callStarting() {
        Inbound served = CURRENT.get();
        if (served != null && RESPONSE.equals(served.half)) endInbound();
    }

    /** The request {@link #requestStarting} began is over, answered or
     *  failed ({@code Identity#requestEnded}). */
    public static void requestEnded(long request) {
        guarded("requestEnded", null, () -> Identity.requestEnded(request));
    }

    /**
     * A received message of {@code transport} ({@code correlationId}, {@code
     * half}) is handed to a worker queue: an IPC server's Reader queueing a
     * call for its handlers.  The hand-off is named by the message -- its
     * sender's endpoint, which the receipt's anchor names too -- not by how
     * many the thread handed off before ({@code Identity#handoffStarting}):
     * the receiving side's twin of a request counted per verb ({@link
     * #requestStarting}).  A message whose sender this run did not file
     * names nothing, and its hand-off is a plain start.
     *
     * @return what {@link #handedOff} takes, in a finally
     */
    public static Object handingOff(String transport, String correlationId,
                                    String half) {
        try {
            String sender = Interactions.sender(trimmed(transport),
                    trimmed(correlationId), trimmed(half));
            return Identity.handoffStarting(sender.isEmpty() ? ""
                    : trimmed(transport) + "." + sender);
        } catch (RuntimeException fault) {
            doorFault("handingOff " + transport + " " + correlationId,
                    fault);
            return null;
        }
    }

    /** The hand-off {@link #handingOff} began is over. */
    public static void handedOff(Object handoff) {
        guarded("handedOff", null, () -> Identity.handoffEnded(handoff));
    }

    /**
     * One message arrives: ends the exchange the thread was serving and
     * installs this one.
     *
     * @param keepSymbolic keep the values earlier messages of the same
     *                     multi-message exchange carried (a SASL handshake)
     */
    public static Inbound inbound(String trace, String symbolic,
                                  String transport, String correlationId,
                                  String attemptId, String half,
                                  Object localOwner, boolean keepSymbolic) {
        try {
            return install(trace, symbolic, transport, correlationId,
                    attemptId, half, localOwner, keepSymbolic);
        } catch (RuntimeException fault) {
            doorFault("inbound " + transport + " " + correlationId, fault);
            return Inbound.EMPTY;
        }
    }

    private static Inbound install(String trace, String symbolic,
                                   String transport, String correlationId,
                                   String attemptId, String half,
                                   Object localOwner, boolean keepSymbolic) {
        // Every receipt ends the request this thread had in hand, whether or
        // not it carries a context (Identity#requestInHand).
        Identity.requestInHand("");
        endInbound(!keepSymbolic);
        if (!keepSymbolic) {
            SymbolicMessageEnvelope.clearInbound();
        }
        String declared = trimmed(symbolic);
        boolean hasTrace = trace != null && !trace.isEmpty();
        if (!hasTrace && declared.isEmpty()) {
            return Inbound.EMPTY;
        }
        long token = hasTrace
                ? CausynthTraceRecorder.inboundExchange(trace, transport,
                correlationId, attemptId, half, localOwner)
                : 0L;
        if (!declared.isEmpty()) {
            SymbolicMessageEnvelope.installInbound(declared);
        }
        Inbound scope = new Inbound(token, correlationId, attemptId, half);
        CURRENT.set(scope);
        return scope;
    }

    /**
     * One request taken into the thread's own context, which it does not
     * anchor: a DataTransfer op a DataNode's turn received.  The turn keeps
     * its address, so a replay that sent the op from another IPC chain still
     * answers it; the op is a message for its values (the symbolic header's,
     * paired with the sender's exports), for the RECEIVE that binds the
     * receiver's captures to it, and for the RECV that names the message
     * that made the turn ({@link CausynthTraceRecorder#receivedExchange}),
     * which the control producers read.  Nothing answers it through a door,
     * so no response endpoint is minted.  Served until the next message or
     * {@link #endInbound}.
     */
    public static Inbound received(String symbolic, String transport,
                                   String correlationId, String attemptId,
                                   Object localOwner) {
        try {
            return take(symbolic, transport, correlationId, attemptId,
                    localOwner);
        } catch (RuntimeException fault) {
            doorFault("received " + transport + " " + correlationId, fault);
            return Inbound.EMPTY;
        }
    }

    private static Inbound take(String symbolic, String transport,
                                String correlationId, String attemptId,
                                Object localOwner) {
        endInbound(true);
        SymbolicMessageEnvelope.clearInbound();
        String declared = trimmed(symbolic);
        boolean correlated = !trimmed(correlationId).isEmpty();
        if (!correlated && declared.isEmpty()) {
            return Inbound.EMPTY;
        }
        if (correlated) {
            CausynthTraceRecorder.receivedExchange(transport, correlationId,
                    attemptId, REQUEST, localOwner);
        }
        if (!declared.isEmpty()) {
            SymbolicMessageEnvelope.installInbound(declared);
        }
        Inbound scope = new Inbound(0L, correlationId, attemptId, REQUEST);
        CURRENT.set(scope);
        return scope;
    }

    /**
     * A protobuf message parsed on this thread inside the exchange it
     * arrived in: each of its message fields' elements is bound to it
     * ({@link MessageCodec#receive}), for the getters that read it.
     */
    public static void parsed(Object message) {
        try {
            MessageCodec.receive(message);
        } catch (RuntimeException fault) {
            doorFault("parsed", fault);
        }
    }

    /** Ends {@code scope} if the thread still serves it. */
    public static void endInbound(Inbound scope) {
        if (scope == null || scope == Inbound.EMPTY || CURRENT.get() != scope) {
            // Already ended by the next message's install: not an error.
            return;
        }
        endInbound();
    }

    /** Ends whatever exchange the thread serves. */
    public static void endInbound() {
        endInbound(true);
    }

    private static void endInbound(boolean clearSymbolic) {
        Inbound scope = CURRENT.get();
        if (scope == null) {
            return;
        }
        CURRENT.remove();
        if (clearSymbolic) {
            SymbolicMessageEnvelope.clearInbound();
        }
        if (scope.token > 0L) {
            CausynthTraceRecorder.endInboundExchange(scope.token);
        }
    }

    /**
     * A write to a store the nodes share is about to be made at {@code
     * location}: a create of that path, or a write of its data.  It takes
     * its turn first ({@link ScheduleEvent.Kind#WRITE}, keyed by the location
     * as every run spells it, {@link RunNames}): writes to one location run
     * in the recorded order while the prefix holds them, and the store
     * decides each race they run -- whether a create finds its node made --
     * as the recording's did (SB19, solr-bugs-reindex-cleanup: a node
     * created the collection's terms node the recording had another replica
     * create, and the shard's leader election went the other way).  Past the
     * cut no slot holds, and writes at one location are ordered only behind
     * the prefix's ({@code ScheduleLog#conflictLocked}).  A location that
     * still spells a name only this run has, which no adapter stated
     * ({@link #spelledAs}), keys alike in no two runs: that write takes no
     * turn, and says so once per name.
     *
     * <p>The store applies a write, and notifies the version's watchers,
     * before the write's call returns, so another thread can read the
     * version before {@link #stored} files it (SOLR-18413 F2: node1's state
     * watchers read the routing rule's version before the Overseer's turn
     * filed it, and their work opened no occurrence).  Until {@link
     * #storeEnded}, a read of a version this write may have made that finds
     * it unfiled waits for it, at most {@link #FILED_WAIT_MS}, or {@link
     * #FILING_WAIT_MS} once it is filing ({@link #filed}).</p>
     *
     * @return the write's token, for {@link #storeEnded}
     */
    public static long storing(String transport, String location) {
        return guarded("storing", location, -1L, () -> {
            boolean paused = pause();
            try {
                turn(ScheduleEvent.Kind.WRITE, transport, location);
                return inFlight(transport, location, false);
            } finally {
                resume(paused);
            }
        });
    }

    /**
     * A write that takes or frees a number of its location's parent: a
     * sequential create ({@code location}: the prefix the store completes)
     * or a delete ({@code location}: the path deleted), each moving the
     * parent's child counter, which numbers the next sequential create
     * there.  Its turn is keyed by the parent, so every participant of one
     * leader election, or every writer of one queue, takes its number in
     * the recorded order, and no run-only name of the creating node (its
     * store session, spelled in an election's prefix) is part of the key.
     * In flight, as {@link #storing}, at {@code location}.
     *
     * @return the write's token, for {@link #storeEnded}
     */
    public static long storingChild(String transport, String location) {
        return guarded("storingChild", location, -1L, () -> {
            boolean paused = pause();
            try {
                String path = trimmed(location);
                int slash = path.lastIndexOf('/');
                turn(ScheduleEvent.Kind.WRITE, transport,
                        slash <= 0 ? "/" : path.substring(0, slash));
                return inFlight(transport, location, false);
            } finally {
                resume(paused);
            }
        });
    }

    /**
     * A read of {@code location} takes its turn before the store's call
     * ({@link ScheduleEvent.Kind#READ}), keyed as the write turn is ({@link
     * RunNames#key}): the read sees the version the recording's read saw --
     * an exists() check before a create, a compare-and-set's version, a
     * client's alias or cluster state (solr-adhoc-39, round MB23s: a cloud
     * client read the alias the Overseer had not yet written, and its updates
     * went to another node).
     */
    public static void reading(String transport, String location) {
        guarded("reading", location, () -> {
            boolean paused = pause();
            try {
                turn(ScheduleEvent.Kind.READ, transport, location);
            } finally {
                resume(paused);
            }
        });
    }

    /**
     * Engine work a system's code called runs with the VM's propagation
     * paused, as every hook the weave emits does: the engine's plumbing is
     * never program state (solr-bugs-snapshot-no-active Z2G: a store
     * write's door, keying a path spelled from a request's values, stated
     * 1,441 versions of the JDK's UTF-8 encoder arrays as the
     * CREATESNAPSHOT task's writes).  Only in a replay: elsewhere no VM
     * propagates.  Pair with {@link #resume} in a finally.
     */
    private static boolean pause() {
        if (!RowRuntime.open()) return false;
        ConcolicRegionRuntime.pauseObservation();
        return true;
    }

    /** Ends what {@link #pause} began. */
    private static void resume(boolean paused) {
        if (paused) ConcolicRegionRuntime.resumeObservation();
    }

    /**
     * A system's JSON codec serializes a document into bytes: the VM
     * propagates nothing until {@link #serialized}.  A store's content
     * crosses leaf by leaf, from the document the codec was handed ({@link
     * #jsonWritten}), never through its bytes, which are concrete; so is
     * any other use of the codec's output.  Unpaused, every character of a
     * symbolic leaf written into the codec's buffers was a version
     * (solr-bugs-snapshot-no-active Z2G: 2,100 array writes of noggit's
     * CharArr and ByteUtils.UTF16toUTF8 in the CREATESNAPSHOT task, whose
     * publication held every region close behind it).
     *
     * @return whether it paused, for {@link #serialized}
     */
    public static boolean serializing() {
        return pause();
    }

    /** The codec's serialization {@link #serializing} paused has ended. */
    public static void serialized(boolean paused) {
        resume(paused);
    }

    /** A write's or a read's turn at {@code location}, keyed as every run
     *  spells it: one key for both, and for the STORE location a version is
     *  filed under. */
    private static void turn(ScheduleEvent.Kind kind, String transport,
                             String location) {
        RunNames.Keyed keyed = RunNames.key(trimmed(location));
        if (keyed.unnamed.isEmpty()) {
            ScheduleLog.observe(kind,
                    ScheduleEvent.written(trimmed(transport), keyed.location));
        } else if (RunNames.firstUnstated(keyed.unnamed)) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    transport + " " + keyed.unnamed, "a store location"
                            + " spells " + keyed.unnamed + ", a name only"
                            + " this run has that no adapter stated as a"
                            + " node's (MessageDoors#spelledAs): its reads and"
                            + " writes take no turn before the store's call, so the"
                            + " store decides their races as this run's"
                            + " timing has it, held only by the SEND after"
                            + " each");
        }
    }

    /** A write in flight at {@code location} until {@link #storeEnded}. */
    private static long inFlight(String transport, String location,
                                 boolean filing) {
        long store = STORES.incrementAndGet();
        synchronized (STORING) {
            STORING.computeIfAbsent(transport,
                    none -> new HashMap<Long, Write>())
                    .put(store, new Write(Thread.currentThread(),
                            trimmed(location), filing));
        }
        return store;
    }

    /**
     * The write {@link #storing} began has filed its version
     * ({@link #stored}), or failed: called in a {@code finally}.
     */
    public static void storeEnded(String transport, long store) {
        synchronized (STORING) {
            Map<Long, Write> writes = STORING.get(transport);
            if (writes != null && writes.remove(store) != null
                    && writes.isEmpty()) {
                STORING.remove(transport);
            }
            STORING.notifyAll();
        }
    }

    /**
     * What the write of a stored version carried, once filed: at once if it
     * is, else once a write another thread had in flight at the version's
     * location when this one read files it -- the store applied that write
     * before the read saw its version, and its writer files the version
     * before its bracket ends.  {@code null} when none of those writes filed
     * it: the version was made outside the window or carried nothing, and
     * the read waits for nothing begun after it read; or the writes did not
     * file it within {@link #FILED_WAIT_MS} -- a writer the schedule holds
     * behind this reader, say -- or, while one of them is filing, within
     * {@link #FILING_WAIT_MS}, and a DIAGNOSTIC row names the version and
     * the writes still in flight.
     */
    static Outbound filed(String transport, String key) {
        String filed = transport + "\n" + key;
        Outbound message = STORED.get(filed);
        if (message != null) return message;
        String path = location(key);
        Thread reader = Thread.currentThread();
        long began = System.currentTimeMillis();
        Map<Long, Write> pending;
        boolean filing = false;
        synchronized (STORING) {
            pending = inFlight(transport, path, reader);
            while ((message = STORED.get(filed)) == null
                    && !pending.isEmpty()) {
                filing = filing(pending,
                        inFlight(transport, path, reader));
                long left = began + (filing ? FILING_WAIT_MS
                        : FILED_WAIT_MS) - System.currentTimeMillis();
                if (left <= 0L) break;
                try {
                    STORING.wait(left);
                } catch (InterruptedException interrupted) {
                    reader.interrupt();
                    return STORED.get(filed);
                }
                pending.keySet().retainAll(
                        inFlight(transport, path, reader).keySet());
            }
        }
        if (message == null && !pending.isEmpty()) {
            List<String> writers = new ArrayList<String>();
            for (Write write : pending.values()) {
                writers.add(write.location + " on " + write.thread.getName());
            }
            RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                    transport + " " + key, "this read found its version"
                            + " unfiled and the writes in flight that may"
                            + " have made it (" + String.join(", ", writers)
                            + ") did not file it within "
                            + (filing ? FILING_WAIT_MS : FILED_WAIT_MS)
                            + " ms: the read pairs with no write");
        }
        return message;
    }

    /**
     * This thread's write at {@code location} is filing ({@link #stored}):
     * past its store's call, it takes no turn and waits on nothing a reader
     * holds before it files -- a reader waiting for it ({@link #filed})
     * holds only {@link #STORING}, which its wait releases -- so a reader
     * may wait for it {@link #FILING_WAIT_MS}.  The token, for {@link
     * #storeEnded}.
     */
    static long filingBegins(String transport, String location) {
        return inFlight(transport, location, true);
    }

    /** Whether a thread making one of the {@code pending} writes is filing
     *  a write in flight {@code now} ({@link Write#filing}): one begun
     *  before its store's call goes on into {@link #stored}. */
    private static boolean filing(Map<Long, Write> pending,
                                  Map<Long, Write> now) {
        for (Write write : now.values()) {
            if (!write.filing) continue;
            for (Write waited : pending.values()) {
                if (waited.thread == write.thread) return true;
            }
        }
        return false;
    }

    /** A stored version's location: its key without the version. */
    static String location(String key) {
        int at = key.lastIndexOf('@');
        return at < 0 ? key : key.substring(0, at);
    }

    /** The writes of {@code transport} in flight at {@code path} on other
     *  threads than {@code reader}: a thread's own write in flight is
     *  behind its read. */
    private static Map<Long, Write> inFlight(String transport, String path,
                                             Thread reader) {
        Map<Long, Write> writes = new HashMap<Long, Write>();
        Map<Long, Write> storing = STORING.get(transport);
        if (storing == null) return writes;
        for (Map.Entry<Long, Write> write : storing.entrySet()) {
            if (write.getValue().thread != reader
                    && write.getValue().makes(path)) {
                writes.put(write.getKey(), write.getValue());
            }
        }
        return writes;
    }

    /**
     * A write to a store the nodes share: a message sent where it is written
     * (a schedule SEND) and received wherever a node later reads that
     * version, any number of times.  The write is in flight until its
     * version is filed ({@link #storing}), from wherever its adapter opened
     * the bracket: before the store's call, or here.
     *
     * <p>{@code data} is what the write wrote: when a system's codec
     * serialized it ({@link #jsonWritten}), each leaf of that document is
     * exported on this version ({@link StoreContent}).</p>
     *
     * @param key the location and the version this write made
     */
    public static void stored(String transport, String key, Object owner,
                              byte[] data) {
        boolean paused = false;
        long store = -1L;
        try {
            paused = pause();
            // In flight until filed, whatever bracket the adapter opened:
            // the SEND and the producer it mints take the concolic VM
            // milliseconds.
            store = filingBegins(transport, location(key));
            // Its place on the session's order before anything files it: a
            // reader released by the filing (#filed) stands after the write
            // (review re-check M8: positioned after the filing, a decode of
            // the version stood before its write, TOPOLOGY_DIVERGENCE).
            RowOrder.Position position = Identity.enginePosition();
            // The content first: a reader that finds the version filed
            // finds its leaves exported ({@link #filed}).
            StoreContent.stored(transport, key, data);
            Outbound message = outbound(transport, key, "1", REQUEST, owner,
                    null);
            if (message.active()) STORED.put(transport + "\n" + key, message);
            written(transport, key, owner, position);
        } catch (RuntimeException fault) {
            doorFault("stored " + key, fault);
        } finally {
            storeEnded(transport, store);
            resume(paused);
        }
    }

    /**
     * The version a write made is a version of its store location
     * (LocationKind.STORE): a write row at the writer's occurrence in a
     * replay, a STORE_WRITE trace row in the recording, which PLAN crosses
     * from a demanded read of it ({@code RecordedStore}).
     */
    private static void written(String transport, String key, Object owner,
                                RowOrder.Position position) {
        long version = version(key);
        if (version < 0L) return;
        String path = life(transport, location(key), version, true);
        String node = RuntimeTraceContext.ownedSource(owner).key();
        CausynthTraceRecorder.storeWritten(trimmed(transport), path, version,
                Identity.currentOccurrence(node));
        if (!RowRuntime.open()) return;
        OccurrenceAddress at = RowRuntime.doorOccurrence(node);
        LocationId location = storeLocation(transport, path);
        // After every VM event so far, as a concrete target stands: a closure
        // cuts a writer strictly before its write's seq, and the writer's
        // own last event (its door's fault marker) is before the write.
        RowRuntime.storeWrite(at, position,
                Endpoint.messageSite(trimmed(transport), "WRITE",
                        location.slot().replace('/', '.').replace('@', '.')),
                location, version);
    }

    /**
     * The objects a fetch of {@code key} was parsed into, the adapter's
     * product of the decode (Solr's {@code ClusterState.load}, {@code
     * Aliases.fromJSON}): each application object of it is registered as
     * holding that version ({@link Provenance}), so a guard that reads one
     * of its fields reads the version (a STORE read row at the guard, {@code
     * ConcolicRegionRuntime#observeProvenance}).  The recording states the
     * objects by identity (a STORE_DECODED trace row), which PLAN joins with
     * the objects each occurrence read a field on.
     */
    public static void decoded(String transport, String key, Object product) {
        boolean paused = false;
        try {
            paused = pause();
            decode(transport, key, product);
        } catch (RuntimeException fault) {
            doorFault("decoded " + key, fault);
        } finally {
            resume(paused);
        }
    }

    /**
     * An engine fault in a door the system's code calls -- one that
     * observes it (decodes, views, refreshes, stores, content) or brackets
     * its messages and requests: named, never thrown into the system's
     * code, which such a door leaves as it found it (a NullPointerException
     * of #decode killed every seed replay whose test builds its cluster in
     * @Before, solr-sg3 SP2-10).  The rows the door would have stated are
     * missing: ENGINE_FAULT, BLOCKING.  A fault door's planted fault is the
     * system's world, not an engine fault: it is thrown, never here; nor
     * is an Error (a replay's cut, LoopAccounting).
     */
    static void doorFault(String door, RuntimeException fault) {
        StackTraceElement[] frames = fault.getStackTrace();
        RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING, door,
                "the engine's door threw " + fault + (frames.length == 0
                        ? "" : " at " + frames[0]) + "; the system's call"
                        + " went on, and the rows the door states are"
                        + " missing");
    }

    /**
     * {@code call}, its engine fault named ({@link #doorFault}) and
     * {@code fallback} returned in place of a throw into the system: a
     * token no end door matches.  The door is named {@code at} what (null:
     * nothing) only when it faults, so a store door spells nothing per call.
     */
    private static <T> T guarded(String door, String at, T fallback,
                                 Supplier<T> call) {
        try {
            return call.get();
        } catch (RuntimeException fault) {
            doorFault(at == null ? door : door + " " + at, fault);
            return fallback;
        }
    }

    /** {@code call}, its engine fault named ({@link #doorFault}) as
     *  {@link #guarded(String, String, Object, Supplier)} names it. */
    private static void guarded(String door, String at, Runnable call) {
        try {
            call.run();
        } catch (RuntimeException fault) {
            doorFault(at == null ? door : door + " " + at, fault);
        }
    }

    private static void decode(String transport, String key, Object product) {
        long version = version(key);
        if (version < 0L || product == null) return;
        // A write in flight at the path may have made this version, its
        // hook not yet run (a create's version 0 opening a new life): the
        // decode waits for it to file, bounded and named (#filed), so it
        // names the life the version was made in.
        filed(trimmed(transport), trimmed(key));
        String path = life(transport, location(key), version, false);
        LocationId store = storeLocation(transport, path);
        // The decode re-points its node's view (LocationKind.VIEW): the
        // view's write is stated here, a pairing's hold deferring only the
        // system's publication of it (#publishing).  A version its node
        // decoded before -- a watcher's and a fetch's parse of one version,
        // or one decoded before the window opened -- re-points nothing: one
        // write of a view per version, the first.
        String node = nodeHere();
        OccurrenceAddress here = Identity.currentOccurrence(node);
        String decoder = decoderNode(here, node);
        LocationId view = viewOf(store, decoder);
        // A thread no registered node owns (a test building its cluster in
        // @Before) has no view to re-point: its parse is no node's decision.
        boolean repoints = view != null && REPOINTED.add(
                trimmed(transport) + "\n" + path + "\n" + decoder + "@"
                        + version);
        // A refresh's decode is what its reader reads at once where no
        // publication follows it (a lazy collection's live fetch): past a
        // pairing's hold of the view, it overrides it, named.
        if (view != null && REFRESHING.get() > 0) {
            Confirmation.overridden(view, version, here, "a decode inside"
                    + " a refresh the system asked for, what its reader"
                    + " reads at once");
        }
        List<Object> registered = Provenance.register(new Provenance.Version(
                store, path, version), product);
        // The decode runs on the fetching thread right after the read: the
        // occurrence running it is the fetch's.
        CausynthTraceRecorder.storeDecoded(trimmed(transport), path, version,
                registered, here);
        if (!repoints) return;
        if (!RowRuntime.open()) {
            // Before the window: what the node holds when it opens, the
            // view's INITIAL at its first row (RowRuntime#viewInitial).
            RowRuntime.viewBeforeWindow(view, version);
            return;
        }
        // The running occurrence, else the node's role occurrence: never
        // none on a registered node's thread.
        OccurrenceAddress at = RowRuntime.doorOccurrence(node);
        // After every VM event so far, as a store's write stands.
        RowRuntime.viewWrite(at, Identity.enginePosition(),
                Endpoint.messageSite(trimmed(transport), "VIEW",
                        view.slot().replace('/', '.').replace('@', '.')),
                viewOf(store, at), version);
    }

    /**
     * The blocking hold's door, which the Solr trees before the publication
     * hold call before a watch's refresh lock ({@code
     * ZkStateReader.StateWatcher#refreshAndWatch}): it holds nothing now --
     * a hold defers the node's publication instead ({@link #publishing}) --
     * and goes with its two calls once every tree carries the publication
     * hook (zk2-publication-hold.ZkStateReader.diff; external-callers.txt).
     */
    public static void refreshing(String transport, String path) {
    }

    /**
     * A node is about to PUBLISH version {@code version} of its view of
     * {@code path} -- make the decode the readers on the node see (Solr's
     * {@code ZkStateReader#updateWatchedCollection}, {@code
     * ZkStateReader.StateWatcher#refreshAndWatchChildren}, {@code
     * AliasesManager#setIfNewer}); -1 for a removal, -2 for an update of
     * the same version (per-replica states) -- and {@code
     * apply} publishes it, under the locks the system's own publication
     * takes.  On a thread delivering a store's notification ({@link
     * #notified}, the whole callback), outside a refresh the system asked
     * for ({@link #refreshStarting}), a pairing's hold of the view may defer
     * it, and a deferred one holds every later one of the view behind it
     * ({@code Confirmation#publishing}): the thread goes on, the node's
     * readers keep the version they had, and the publications apply later
     * in the order they came.  A notification's publication with a PUBLISH
     * turn that nothing defers is put in force here, on this thread, its
     * turn settled once {@code apply} returns ({@code Confirmation#inForce}).
     * A synchronous publication -- a forced refresh, a fetch on the reader's
     * own thread, the node's own write -- is never deferred, the caller
     * publishes it, and it supersedes the deferred removals and what came
     * before them ({@code Confirmation#published}).
     *
     * @return whether the door put it in force (now, or later on the node's
     *         publisher): the caller then publishes nothing
     */
    public static boolean publishing(String transport, String path,
                                     long version, Runnable apply) {
        boolean delivering = DELIVERING.get() > 0 && REFRESHING.get() == 0;
        String why = REFRESHING.get() > 0
                ? "inside a refresh the system asked for"
                : "on a thread delivering no store notification";
        Runnable inForce = guarded("publishing", path, null, () -> {
            // A notification's publication takes a PUBLISH turn, recorded
            // and held whether or not a pairing holds the view; one at once
            // settles what a hold deferred, and the node's older turns of
            // the view where an order holds them (Confirmation#published).
            if (!delivering && !Confirmation.holdsViews()
                    && !ScheduleLog.enforcing()) {
                return null;
            }
            boolean paused = pause();
            try {
                String node = nodeHere();
                OccurrenceAddress at = Identity.currentOccurrence(node);
                String life = life(transport, trimmed(path),
                        Math.max(0L, version), false);
                String decoder = decoderNode(at, node);
                LocationId view = viewOf(storeLocation(transport, life),
                        decoder);
                if (!delivering) {
                    Confirmation.published(view, version, at, why, decoder,
                            version < 0L ? null
                                    : publishedSite(transport, life, version));
                    return null;
                }
                return Confirmation.publishing(view, version, at, decoder,
                        CausynthTraceRecorder.captureScope(), apply,
                        publishTurn(transport, life, version, decoder));
            } finally {
                resume(paused);
            }
        });
        if (inForce == null) return false;
        // Outside the pause and the guard: the system's own apply, traced as
        // its code, its throw the caller's.  Solr's (ZkStateReader
        // #updateWatchedCollection's) publishes and reconstructs, so the
        // caller's constructState after it (StateWatcher#refreshAndWatch)
        // runs twice -- an idempotent rebuild and a same-state watcher
        // notification, as Solr itself issues one for an added watcher, and
        // as a deferred publication's caller already did.  It takes the
        // collection's refresh lock, which the callback holds here, then the
        // update lock: the order stock refreshAndWatchChildren takes them
        // (one nested in the other); no thread takes the refresh lock under
        // the update lock, since a synchronous publication, whose caller may
        // hold the update lock (forceUpdateCollection), is published by its
        // caller.
        inForce.run();
        return true;
    }

    /** A view's PUBLISH site at {@code version}: the store location of
     *  {@code path} in its store life, as every run spells it ({@link
     *  #storeLocation}). */
    private static String publishedSite(String transport, String path,
                                        long version) {
        return ScheduleEvent.published(trimmed(transport),
                storeLocation(transport, path).slot(), version);
    }

    /** The (node, path, version) publications that took their turn. */
    private static final Set<String> PUBLISH_TURNS =
            java.util.concurrent.ConcurrentHashMap.newKeySet();

    /**
     * The PUBLISH turn of a notification's publication of {@code version}
     * of {@code path} on {@code node}: its site, the first per version --
     * a second callback's publication of a version re-points nothing, as a
     * second decode of it ({@link #decode}) --, or null (another's, a
     * removal or a same-version update, or a node no registered work owns).
     */
    private static String publishTurn(String transport, String path,
                                      long version, String node) {
        if (version < 0L || node == null || node.isEmpty()) return null;
        String site = publishedSite(transport, path, version);
        return PUBLISH_TURNS.add(node + "\n" + site) ? site : null;
    }

    /**
     * The node whose view a decode or a refresh on this thread re-points:
     * the running occurrence's, else the thread's scope's (a decode before
     * the window, or on a thread no occurrence runs on).
     */
    private static String decoderNode(OccurrenceAddress here, String node) {
        return here != null ? here.node().render() : node;
    }

    /**
     * The system's own refresh of a view begins (Solr's {@code
     * ZkStateReader#forceUpdateCollection}, {@code
     * #forciblyRefreshAllClusterStateSlow}, a lazy collection's {@code
     * LazyCollectionRef#get}): it reads the store as it stands, as its
     * caller asked, so no pairing's hold defers what it publishes ({@link
     * #publishing}), even on a notification's thread -- a refresh on the
     * program's way (the Overseer applying a RefreshCollectionMessage, a
     * leader's prep-recovery) is no slow event thread; one that publishes a
     * version past the paired one leaves the pairing untaken.  Ends at
     * {@link #refreshEnded}.
     *
     * @return the token {@link #refreshEnded} takes
     */
    public static long refreshStarting() {
        int depth = REFRESHING.get();
        REFRESHING.set(depth + 1);
        return depth;
    }

    /** Ends the refresh {@link #refreshStarting} began. */
    public static void refreshEnded(long token) {
        if (token <= 0L) {
            REFRESHING.remove();
        } else {
            REFRESHING.set((int) token);
        }
    }

    /** How many system refreshes run on this thread ({@link
     *  #refreshStarting}). */
    private static final ThreadLocal<Integer> REFRESHING =
            ThreadLocal.withInitial(() -> 0);

    /** The node the running thread's work is attributed to, or "". */
    private static String nodeHere() {
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        return view.source == null ? "" : view.source.key();
    }

    /**
     * The adapter's accessor of one node's view of {@code path} handed out
     * {@code product}, the object its decodes re-point (Solr's {@code
     * AliasesManager#getAliases}): a read of the version a decode made it
     * from ({@link Provenance}), stated as a STORE read and a VIEW read of
     * the running occurrence -- the admitted activation's, else the
     * thread's role occurrence -- at the accessor's site ({@link
     * ContentPort#viewed}), as a PROVENANCE site states one (SYMBOL-SCOPE
     * §6.4).
     * An object no decode made states nothing.
     */
    public static void viewed(String transport, String path, Object product) {
        if (product == null || !RowRuntime.open()) return;
        boolean paused = false;
        try {
            paused = pause();
            view(transport, path, product);
        } catch (RuntimeException fault) {
            doorFault("viewed " + path, fault);
        } finally {
            resume(paused);
        }
    }

    private static void view(String transport, String path, Object product) {
        Provenance.Version version = Provenance.observe(product, null,
                new boolean[1]);
        if (version == null) return;
        String node = nodeHere();
        OccurrenceAddress at = RowRuntime.doorOccurrence(node);
        if (at == null) return;
        // On the scale the engine's writes of a store and a view stand on,
        // after every VM event so far and every engine row stated before it
        // (contract.RowOrder): never ordered before the write it saw.
        String site = ContentPort.viewed(trimmed(transport), path);
        RowRuntime.storeRead(at, Identity.enginePosition(), site,
                version.location, version.version);
        LocationId view = viewOf(version.location, at);
        if (view != null) {
            RowRuntime.viewRead(at, Identity.enginePosition(), site + "#VIEW",
                    view, version.version);
        }
    }

    /**
     * Whether a system's JSON codec hands this thread's documents over
     * ({@link #jsonWritten}, {@link #jsonRead}): in a replay.  The codec
     * builds the writer's document only then.
     */
    public static boolean capturingContent() {
        return StoreContent.capturing();
    }

    /**
     * A system's JSON codec serialized {@code document} -- a tree of maps,
     * lists and leaves as its serializer walked the object it was handed,
     * each leaf the object the writer holds -- into {@code bytes}: a store
     * write of these bytes ({@link #stored}) exports its leaves.  Kept
     * weakly by the array, so bytes no store takes drop it.
     */
    public static void jsonWritten(byte[] bytes, Object document) {
        try {
            StoreContent.written(bytes, document);
        } catch (RuntimeException fault) {
            doorFault("jsonWritten", fault);
        }
    }

    /**
     * A system's JSON codec parsed {@code bytes} into {@code tree}: when a
     * store fetch returned these bytes ({@link #fetched}), each leaf of the
     * tree is minted on its entry, paired with that version's export of it
     * ({@link StoreContent}).
     */
    public static void jsonRead(byte[] bytes, Object tree) {
        try {
            StoreContent.parsed(bytes, tree);
        } catch (RuntimeException fault) {
            doorFault("jsonRead", fault);
        }
    }

    /**
     * One node's view of a store location (LocationKind.VIEW): the
     * transport at the node of {@code at}, the location as every run spells
     * it; null for no registered node, whose view is no node's.
     */
    static LocationId viewOf(LocationId store, OccurrenceAddress at) {
        return viewOf(store, at == null ? "" : at.node().render());
    }

    /** The same, of the node {@code node} names. */
    private static LocationId viewOf(LocationId store, String node) {
        if (store == null || node.isEmpty() || node.startsWith(
                OccurrenceBinding.UNREGISTERED_SOURCE_KEY)) {
            return null;
        }
        return LocationId.of(LocationKind.VIEW, store.owner() + "@" + node,
                store.slot());
    }

    /** A store location as every run spells it: the path as {@link
     *  RunNames} keys it, then its life ({@link #life}) past the first. */
    static LocationId storeLocation(String transport, String path) {
        String named = trimmed(path);
        int life = named.lastIndexOf(LIFE);
        String suffix = life < 0 ? "" : named.substring(life);
        String bare = life < 0 ? named : named.substring(0, life);
        return LocationId.of(LocationKind.STORE, trimmed(transport),
                RunNames.key(bare).location + suffix);
    }

    /**
     * {@code path} named with its life in this run (design Z §1): {@code
     * <path>#<n>} from its second life on.  A store restarts a path's
     * versions at 0 when the path is created again after its delete, so a
     * version 0 written once the path stood at a version is a new life --
     * without it, writeOf(location, v) could pick the other life's v.  A
     * decode names the life it read and starts none: it first waits for a
     * write in flight at the path to file ({@link #decoded}).
     */
    private static String life(String transport, String path,
                               long version, boolean write) {
        String key = trimmed(transport) + "\n" + trimmed(path);
        synchronized (LIVES) {
            int[] held = LIVES.get(key);
            if (held == null) {
                held = new int[] {1, 0};
                LIVES.put(key, held);
            }
            if (write && version == 0L && held[1] != 0) held[0]++;
            if (write || version > 0L) held[1] = 1;
            return held[0] == 1 ? trimmed(path)
                    : trimmed(path) + LIFE + held[0];
        }
    }

    /** transport + path -> {its life, whether it stood at a version}. */
    private static final Map<String, int[]> LIVES = new HashMap<>();

    /** What separates a path from its life in a store location's name. */
    private static final String LIFE = "#";

    /** A stored version's version: its key after the last {@code @}, or -1. */
    private static long version(String key) {
        String held = trimmed(key);
        int at = held.lastIndexOf('@');
        if (at < 0) return -1L;
        try {
            return Long.parseLong(held.substring(at + 1));
        } catch (NumberFormatException unversioned) {
            return -1L;
        }
    }

    /**
     * A store's notification (a ZooKeeper watch event) run by its callback:
     * the first version the callback reads that a write of the window
     * stored ({@link #fetched}) is the message that caused it, and the
     * callback's end ends it.  Whatever lineage the callback's pooled thread
     * inherited is the pool's, not the notification's cause.
     *
     * @param kind what is notified (the watcher's class): one change the
     *             store reports to two watchers is read by two callbacks,
     *             each an occurrence of its own
     */
    public static void notified(String kind, Runnable callback) {
        NOTIFIED.set(trimmed(kind));
        DELIVERING.set(DELIVERING.get() + 1);
        try {
            callback.run();
        } finally {
            DELIVERING.set(DELIVERING.get() - 1);
            // The callback's own exception is the system's and goes on; an
            // engine fault here would replace it, so it is named instead.
            try {
                NOTIFIED.remove();
                endInbound();
            } catch (RuntimeException fault) {
                doorFault("notified " + kind, fault);
            }
        }
    }

    /**
     * A read of a version a {@link #stored} write made.  The first such read
     * of a notification installs the writer's context, on the reading node:
     * each version read is an occurrence of its own, named by the write.
     * The schedule never waits for it: ZooKeeper folds the changes that
     * arrive before a watch is set again into one event, so how many
     * notifications a run takes is the store's timing.  Any other read is
     * data, not a cause: a loop that polls the store reads as often as its
     * timing lets it.  A read that takes what its write carried -- the
     * writer's context in a notification -- first waits for the version to
     * be filed, if a write in flight may file it ({@link #filed}).
     * {@code data} is what the fetch returned: a parse of it by a system's
     * codec ({@link #jsonRead}) takes in this version's content.
     */
    public static void fetched(String transport, String key, Object owner,
                               byte[] data) {
        boolean paused = false;
        try {
            paused = pause();
            fetch(transport, key, owner, data);
        } catch (RuntimeException fault) {
            doorFault("fetched " + key, fault);
        } finally {
            resume(paused);
        }
    }

    private static void fetch(String transport, String key, Object owner,
                              byte[] data) {
        StoreContent.fetched(transport, key, data);
        String kind = NOTIFIED.get();
        if (kind == null) return;
        Outbound message = filed(transport, key);
        if (message == null) return;
        NOTIFIED.remove();
        endInbound(true);
        SymbolicMessageEnvelope.clearInbound();
        // The notified kind is part of the context the callback's work is
        // addressed by, never of the pairing with the write; so is which of
        // the node's deliveries of this version it is, from the second on --
        // the store's timing, which CONFIRM compares through
        // (CausalContext.Anchor#anyDelivery).
        int delivery = DELIVERIES.merge(RuntimeTraceContext.ownedSource(owner)
                .key() + "\n" + transport + "\n" + key + "\n" + kind, 1,
                Integer::sum);
        String via = delivery == 1 ? kind : kind + "." + delivery;
        long token = message.trace.isEmpty() ? 0L
                : CausynthTraceRecorder.inboundExchange(message.trace,
                transport, key, "1", REQUEST, owner, false, via);
        if (!message.symbolic.isEmpty()) {
            SymbolicMessageEnvelope.installInbound(message.symbolic);
        }
        CURRENT.set(new Inbound(token, key, "1", REQUEST));
    }

    /**
     * An item of a store's queue (ZooKeeper's sequential nodes: the Solr
     * Overseer's state-update queue) taken by the one consumer that
     * processes it, as {@link #received} takes a request: it ends what the
     * thread served, and is the message the thread serves until the next
     * one -- named by its key, as its write sent it ({@link #stored}), so an
     * attach of an element it carried pairs with that write's export by the
     * item and its port ({@code Interactions#pairing}, CORRELATION_PORT) --
     * with the values its writer staged on it.  The consumer's context stays
     * its own: which turn takes an item is the queue's batching, and each
     * turn is ordered as a tick of its own, and a consumer takes an item
     * inside its turn ({@link #beginTick}), which ended whatever the thread
     * served before: what an item ends is the item before it.  An item its
     * writer has not yet filed is waited for ({@link #filed}); one no write
     * of the window filed names nothing.
     */
    public static void consumed(String transport, String key) {
        boolean paused = false;
        try {
            paused = pause();
            consume(transport, key);
        } catch (RuntimeException fault) {
            doorFault("consumed " + key, fault);
        } finally {
            resume(paused);
        }
    }

    private static void consume(String transport, String key) {
        endInbound(true);
        SymbolicMessageEnvelope.clearInbound();
        Outbound message = filed(transport, key);
        if (message == null) return;
        // Its RECV names the item the turn took in, as a received request's
        // does: the doors of the message that started the consumer
        // (Corpus#startedBy, RecordedMessages#doorsOf).
        CausynthTraceRecorder.receivedExchange(transport, key, "1", REQUEST,
                null);
        if (!message.symbolic.isEmpty()) {
            SymbolicMessageEnvelope.installInbound(message.symbolic);
        }
        CURRENT.set(new Inbound(0L, key, "1", REQUEST));
    }

    /** The exchange the thread serves, or {@code null}. */
    public static Inbound current() {
        return CURRENT.get();
    }

    /**
     * Sets the served exchange aside, unended, while the thread runs an
     * exchange of its own as a client; {@link #restore} gives it back.
     */
    public static Inbound setAside() {
        Inbound serving = CURRENT.get();
        if (serving != null) {
            CURRENT.remove();
        }
        return serving;
    }

    /** Gives back what {@link #setAside} took. */
    public static void restore(Inbound serving) {
        if (serving != null) {
            CURRENT.set(serving);
        }
    }

    /**
     * Enters the scope a queued unit of work carried from where it was made:
     * the dequeue half of a queue handoff.
     */
    public static long enterCarriedScope(Object scope, String role,
                                         String api) {
        return guarded("enterCarriedScope", role, 0L, () ->
                CausynthTraceRecorder.enterCarriedScope(scope, role, api));
    }

    /** Leaves the scope {@link #enterCarriedScope} entered. */
    public static void exitCarriedScope(long token) {
        guarded("exitCarriedScope", null, () ->
                CausynthTraceRecorder.exitCarriedScope(token));
    }

    /**
     * Opens one daemon tick as a root of its own: a service-loop turn.  The
     * exchange the thread served ends first, as for a node startup: the turn
     * serves no message it did not take in itself.  Left standing below the
     * turn, the next message's end of it closed the turn as well (a
     * DataNode actor built inside the window stands in its registration's
     * response when its first turn begins; the IPC client ends that exchange
     * before its heartbeat, so the heartbeat went out in the test's request
     * and the turn stated no END: hdfs-adhoc-21/22/23/25, round HG5A).
     */
    public static long beginTick(Object owner, String role) {
        return guarded("beginTick", role, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginDaemonTick(owner, role);
        });
    }

    /**
     * Whether the turn {@link #beginTick} opened is vacant: one the recording
     * never made, which a replay held and let go only because the run could
     * go no further (a pool's shutdown awaiting the timer task it runs in).
     * A tick site whose turn may be skipped -- a poll, not a queue's consumer
     * -- skips it; the recording, which holds nothing, has no vacant turn.
     */
    public static boolean vacant(long tick) {
        return CausynthTraceRecorder.vacantDaemonTick(tick);
    }

    /**
     * {@code who} is about to take startup {@code step}, a step that builds
     * state a replay reads and that no slot of the schedule orders, before
     * the window or inside it: a replay holds it until those its recording
     * saw complete the step first have completed it ({@link StartupOrder}).
     * {@code who} names the taker the same in both passes (a DataNode's
     * UUID, which its keyed draw makes).
     *
     * @return what {@link #startupDone} takes
     */
    public static Object startupStep(String step, String who) {
        return CausynthTraceRecorder.startupStep(step, who);
    }

    /** The step {@link #startupStep} began completed. */
    public static void startupDone(Object pass) {
        CausynthTraceRecorder.startupDone(pass);
    }

    /**
     * Closes the tick {@link #beginTick} opened, and the exchange its thread
     * served in it: the turn serves nothing past its end (the Solr
     * Overseer's batch write after its last item's turn served that item).
     */
    public static void endTick(long token) {
        guarded("endTick", null, () -> {
            endInbound();
            CausynthTraceRecorder.endDaemonTick(token);
        });
    }

    /** Opens the recorded window: the workload's recording boundary. */
    public static void startRecording() {
        CausynthTraceRecorder.startRecording();
    }

    /**
     * Whether the case declares its window open before its cluster starts
     * (case key {@code recording_window=startup}), where a system's cluster
     * adapter then opens it; otherwise it opens once the cluster is up.
     */
    public static boolean startupWindow() {
        return RecordingWindow.atStartup();
    }

    /**
     * Opens the construction of one node, under the name the system's
     * adapter registers it by once it is built ({@link #registerNode}, the
     * same kind, role and id): what it starts or creates until {@link
     * #endNodeStartup} belongs to that node, though the test's request
     * stands where it runs (IDENTITY.md §5), the calling thread's own work
     * inside it included.  Attribution only: no event, no lineage hop.  A
     * system's cluster adapter brackets each node it constructs this way,
     * and a registered node's start, a restart's included, by {@link
     * #beginNodeStartup(Object)}.
     *
     * <p>A construction is the test's own work, not the serving of the last
     * message its thread received: the exchange the thread served ends
     * first, so the node and the threads it starts stand in the test's
     * request, not under that message's anchor (round HG4, hdfs-adhoc-22: one
     * response that differed after a divergence re-anchored every later
     * cluster's build, and 10560 slots were given up at once).</p>
     *
     * @return the token {@link #endNodeStartup} takes
     */
    public static long beginNodeStartup(String kind, String role,
                                        String sourceId) {
        return guarded("beginNodeStartup", role, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginNodeStartup(kind, role,
                    sourceId);
        });
    }

    /**
     * Opens one startup of a node already registered -- its threads' start
     * -- or of none when it is not: what it starts belongs to the node.  The
     * exchange the thread served ends first, as for a construction.
     */
    public static long beginNodeStartup(Object node) {
        return guarded("beginNodeStartup", null, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginNodeStartup(node);
        });
    }

    /** Ends the startup {@code token} opened. */
    public static void endNodeStartup(long token) {
        guarded("endNodeStartup", null, () ->
                CausynthTraceRecorder.endNodeStartup(token));
    }

    /** Closes it: the workload's test is over, its teardown unrecorded. */
    public static void stopRecording() {
        CausynthTraceRecorder.stopRecording();
    }

    /**
     * Whether this run is a concolic replay: a world the engine chose, where a
     * workload's check of the RECORDING's world is not the workload's to make.
     */
    public static boolean replaying() {
        return CausynthTraceRecorder.replaying();
    }

    public static void registerSource(Object anchor, String kind, String role,
                                      String sourceId, long epoch) {
        CausynthTraceRecorder.registerSource(anchor, kind, role, sourceId,
                epoch);
    }

    /**
     * The names node {@code sourceId} has only in this run -- the id of its
     * store session, its host and port -- each stated so: a store location
     * that spells one keys its write by the node's name instead ({@link
     * #storing}), alike in the recording and every replay (a ZooKeeper
     * leader election's {@code <session>-<core>-n_} prefix).
     */
    public static void spelledAs(String sourceId, String... spellings) {
        if (spellings == null) return;
        for (String spelling : spellings) {
            RunNames.spelled(trimmed(sourceId), trimmed(spelling));
        }
    }

    public static void registerSourceAlias(Object alias, Object anchor) {
        CausynthTraceRecorder.registerSourceAlias(alias, anchor);
    }

    /**
     * Registers one node: its anchor as the source, and every object the node
     * runs its work through as the same node -- what the attribution rule
     * finds on a thread's frames.  A null or repeated alias is skipped.
     */
    public static void registerNode(Object anchor, String kind, String role,
                                    String sourceId, Object... aliases) {
        registerSource(anchor, kind, role, sourceId, 0L);
        if (aliases == null) {
            return;
        }
        for (Object alias : aliases) {
            if (alias == null || alias == anchor) {
                continue;
            }
            registerSourceAlias(alias, anchor);
        }
    }

    public static void restartSource(Object anchor, String kind, String role,
                                     String sourceId, long epoch) {
        CausynthTraceRecorder.restartSource(anchor, kind, role, sourceId,
                epoch);
    }

    public static long beginRequest(Object source, String api) {
        return guarded("beginRequest", api, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginSourceRequest(source, api);
        });
    }

    public static void endRequest(long request, String api) {
        guarded("endRequest", api, () -> {
            endInbound();
            CausynthTraceRecorder.endSourceRequest(request, api);
        });
    }

    /**
     * One client operation the workload itself makes, a request root of its
     * own ({@link CausynthTraceRecorder#beginWorkloadCall}); 0, and nothing
     * begun, on a node's own thread.
     */
    public static long beginWorkloadCall(String api) {
        return CausynthTraceRecorder.beginWorkloadCall(api);
    }

    public static void endWorkloadCall(long call, String api) {
        if (call != 0L) endRequest(call, api);
    }

    /** The outbound of a message that carries nothing. */
    public static Outbound outboundNone() {
        return Outbound.EMPTY;
    }

    /** What one outbound message carries. */
    public static final class Outbound {
        static final Outbound EMPTY = new Outbound("", "", "", "");
        public final String correlationId;
        public final String attemptId;
        public final String trace;
        public final String symbolic;

        private Outbound(String correlationId, String attemptId, String trace,
                         String symbolic) {
            this.correlationId = correlationId;
            this.attemptId = attemptId;
            this.trace = trace;
            this.symbolic = symbolic == null ? "" : symbolic;
        }

        public boolean active() {
            return !trace.isEmpty() || !symbolic.isEmpty();
        }
    }

    /** One installed inbound exchange. */
    public static final class Inbound {
        static final Inbound EMPTY = new Inbound(0L, "", "", "");
        private final long token;
        public final String correlationId;
        public final String attemptId;
        public final String half;

        private Inbound(long token, String correlationId, String attemptId,
                        String half) {
            this.token = token;
            this.correlationId = correlationId;
            this.attemptId = attemptId;
            this.half = half;
        }
    }
}
