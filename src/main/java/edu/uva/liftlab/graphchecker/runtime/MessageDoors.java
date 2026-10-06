package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * THE message doors a system's transports call, whatever the system: a
 * request or a response leaves (outbound) carrying the sender's GraphChecker
 * context and the symbolic values it exports, and arrives (inbound) where the
 * receiver installs them for as long as it serves that message.  Its values
 * are the {@code WIRE_FLOW} ports the thread staged.  Plus the workload's
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
     * in ms: they file within milliseconds (SOLR-18413 F2's measured
     * 0.1-6.5 ms), and a write the schedule holds behind the reader would
     * otherwise wait for the watchdog.
     */
    static final long FILED_WAIT_MS = 2000L;

    /** One write in flight: the thread making it and the location it
     *  writes. */
    private static final class Write {
        private final Thread thread;
        private final String location;

        private Write(Thread thread, String location) {
            this.thread = thread;
            this.location = location;
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
        return CausynthTraceRecorder.captureScope();
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
        return outbound(transport, correlationId, attemptId, half,
                localOwner, scope, "");
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
                                           String verb) {
        return outbound(transport, correlationId, attemptId, REQUEST,
                localOwner, scope, verb);
    }

    private static Outbound outbound(String transport, String correlationId,
                                     String attemptId, String half,
                                     Object localOwner, Object scope,
                                     String verb) {
        String trace = CausynthTraceRecorder.outboundExchange(transport,
                correlationId, attemptId, half, localOwner, scope,
                Text.safe(verb));
        String symbolic = SymbolicMessageEnvelope.takeOutbound();
        return trace.isEmpty() && symbolic.isEmpty() ? Outbound.EMPTY
                : new Outbound(correlationId, attemptId, trace, symbolic);
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
        Inbound served = CURRENT.get();
        if (served != null && RESPONSE.equals(served.half)) endInbound();
        return Identity.requestStarting(Endpoint.messageSite(
                Text.safe(transport), REQUEST, Text.safe(verb)), verb,
                attempt);
    }

    /** The request {@link #requestStarting} began is over, answered or
     *  failed ({@code Identity#requestEnded}). */
    public static void requestEnded(long request) {
        Identity.requestEnded(request);
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
        String sender = Interactions.sender(Text.safe(transport),
                Text.safe(correlationId), Text.safe(half));
        return Identity.handoffStarting(sender.isEmpty() ? ""
                : Text.safe(transport) + "." + sender);
    }

    /** The hand-off {@link #handingOff} began is over. */
    public static void handedOff(Object handoff) {
        Identity.handoffEnded(handoff);
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
        // Every receipt ends the request this thread had in hand, whether or
        // not it carries a context (Identity#requestInHand).
        Identity.requestInHand("");
        endInbound(!keepSymbolic);
        if (!keepSymbolic) {
            SymbolicMessageEnvelope.clearInbound();
        }
        String declared = Text.safe(symbolic);
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
        endInbound(true);
        SymbolicMessageEnvelope.clearInbound();
        String declared = Text.safe(symbolic);
        boolean correlated = !Text.safe(correlationId).isEmpty();
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
     * location} (a sequential create's: the prefix the store completes).
     * The store applies a write, and notifies the version's watchers, before
     * the write's call returns, so another thread can read the version
     * before {@link #stored} files it (SOLR-18413 F2: node1's state watchers
     * read the routing rule's version before the Overseer's turn filed it,
     * and their work opened no occurrence).  Until {@link #storeEnded}, a
     * read of a version this write may have made that finds it unfiled
     * waits for it, at most {@link #FILED_WAIT_MS} ({@link #filed}).
     *
     * @return the write's token, for {@link #storeEnded}
     */
    public static long storing(String transport, String location) {
        long store = STORES.incrementAndGet();
        synchronized (STORING) {
            STORING.computeIfAbsent(transport,
                    none -> new HashMap<Long, Write>())
                    .put(store, new Write(Thread.currentThread(),
                            Text.safe(location)));
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
     * behind this reader, say -- and a DIAGNOSTIC row names the version and
     * the writes still in flight.
     */
    private static Outbound filed(String transport, String key) {
        String filed = transport + "\n" + key;
        Outbound message = STORED.get(filed);
        if (message != null) return message;
        String path = location(key);
        Thread reader = Thread.currentThread();
        long deadline = System.currentTimeMillis() + FILED_WAIT_MS;
        Map<Long, Write> pending;
        synchronized (STORING) {
            pending = inFlight(transport, path, reader);
            while ((message = STORED.get(filed)) == null
                    && !pending.isEmpty()) {
                long left = deadline - System.currentTimeMillis();
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
                            + ") did not file it within " + FILED_WAIT_MS
                            + " ms: the read pairs with no write");
        }
        return message;
    }

    /** A stored version's location: its key without the version. */
    private static String location(String key) {
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
     * @param key the location and the version this write made
     */
    public static void stored(String transport, String key, Object owner) {
        // In flight until filed, whatever bracket the adapter opened: the
        // SEND and the producer it mints take the concolic VM milliseconds.
        long store = storing(transport, location(key));
        try {
            Outbound message = outbound(transport, key, "1", REQUEST, owner,
                    null);
            if (message.active()) STORED.put(transport + "\n" + key, message);
        } finally {
            storeEnded(transport, store);
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
        NOTIFIED.set(Text.safe(kind));
        try {
            callback.run();
        } finally {
            NOTIFIED.remove();
            endInbound();
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
     */
    public static void fetched(String transport, String key, Object owner) {
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
     * processes it: what its writer staged on it -- the values a {@code
     * WIRE_FLOW} carries -- arrives with it and stays until the next item.
     * The consumer's context stays its own: which turn takes an item is the
     * queue's batching, and each turn is ordered as a tick of its own.  An
     * item its writer has not yet filed is waited for ({@link #filed}).
     */
    public static void consumed(String transport, String key) {
        SymbolicMessageEnvelope.clearInbound();
        Outbound message = filed(transport, key);
        if (message != null && !message.symbolic.isEmpty()) {
            SymbolicMessageEnvelope.installInbound(message.symbolic);
        }
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
        return CausynthTraceRecorder.enterCarriedScope(scope, role, api);
    }

    /** Leaves the scope {@link #enterCarriedScope} entered. */
    public static void exitCarriedScope(long token) {
        CausynthTraceRecorder.exitCarriedScope(token);
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
        endInbound();
        return CausynthTraceRecorder.beginDaemonTick(owner, role);
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

    /** Closes the tick {@link #beginTick} opened. */
    public static void endTick(long token) {
        CausynthTraceRecorder.endDaemonTick(token);
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
        endInbound();
        return CausynthTraceRecorder.beginNodeStartup(kind, role, sourceId);
    }

    /**
     * Opens one startup of a node already registered -- its threads' start
     * -- or of none when it is not: what it starts belongs to the node.  The
     * exchange the thread served ends first, as for a construction.
     */
    public static long beginNodeStartup(Object node) {
        endInbound();
        return CausynthTraceRecorder.beginNodeStartup(node);
    }

    /** Ends the startup {@code token} opened. */
    public static void endNodeStartup(long token) {
        CausynthTraceRecorder.endNodeStartup(token);
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
        endInbound();
        return CausynthTraceRecorder.beginSourceRequest(source, api);
    }

    public static void endRequest(long request, String api) {
        endInbound();
        CausynthTraceRecorder.endSourceRequest(request, api);
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
