package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.ZkChain;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class MessageDoors {
    public static final String REQUEST = "REQUEST";
    public static final String RESPONSE = "RESPONSE";
    public static final long TOMBSTONE = Integer.MAX_VALUE - 1L;

    private static final ThreadLocal<Inbound> CURRENT = new ThreadLocal<>();

    private static final Map<String, Outbound> STORED =
            new ConcurrentHashMap<String, Outbound>();
    private static final Set<String> REPOINTED =
            ConcurrentHashMap.newKeySet();
    private static final Map<String, Map<Long, Write>> STORING =
            new HashMap<String, Map<Long, Write>>();
    private static final AtomicLong STORES = new AtomicLong();
    static final long FILED_WAIT_MS = 2000L;

    static final long FILING_WAIT_MS = 60000L;

    private static final class Write {
        private final Thread thread;
        private final String location;
        private final boolean filing;

        private Write(Thread thread, String location, boolean filing) {
            this.thread = thread;
            this.location = location;
            this.filing = filing;
        }

        private boolean makes(String path) {
            return path.equals(location) || path.startsWith(location)
                    && path.indexOf('/', location.length()) < 0;
        }
    }

    private static final ThreadLocal<String> NOTIFIED = new ThreadLocal<>();
    private static final ThreadLocal<Integer> DELIVERING =
            ThreadLocal.withInitial(() -> 0);
    private static final Map<String, Integer> DELIVERIES =
            new ConcurrentHashMap<String, Integer>();

    private MessageDoors() {
    }

    public static Object captureScope() {
        return guarded("captureScope", null, null,
                CausynthTraceRecorder::captureScope);
    }

    public static Outbound outbound(String transport, String correlationId,
                                    String attemptId, String half,
                                    Object localOwner, Object scope) {
        return send(transport, correlationId, attemptId, half, localOwner,
                scope, "", null);
    }

    public static Outbound outbound(String transport, String correlationId,
                                    String attemptId, String half,
                                    Object localOwner, Object scope,
                                    Object message) {
        return send(transport, correlationId, attemptId, half, localOwner,
                scope, "", message);
    }

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

    public static void callStarting() {
        Inbound served = CURRENT.get();
        if (served != null && RESPONSE.equals(served.half)) endInbound();
    }

    public static void requestEnded(long request) {
        guarded("requestEnded", null, () -> Identity.requestEnded(request));
    }

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

    public static void handedOff(Object handoff) {
        guarded("handedOff", null, () -> Identity.handoffEnded(handoff));
    }

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

    public static void parsed(Object message) {
        try {
            MessageCodec.receive(message);
        } catch (RuntimeException fault) {
            doorFault("parsed", fault);
        }
    }

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

    public static void endInbound(Inbound scope) {
        if (scope == null || scope == Inbound.EMPTY || CURRENT.get() != scope) {
            return;
        }
        endInbound();
    }

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

    public static void reading(String transport, String location) {
        guarded("reading", location, () -> {
            boolean paused = pause();
            try {
                ActiveRegion active = ConcolicRegionRuntime.activeRegion();
                if (active != null && active.d3Address != null) {
                    Confirmation.storeReading(active.d3Address, storeLocation(
                            transport, life(transport, trimmed(location), -1L,
                                    false)));
                }
                turn(ScheduleEvent.Kind.READ, transport, location);
            } finally {
                resume(paused);
            }
        });
    }

    private static boolean pause() {
        if (!RowRuntime.open()) return false;
        ConcolicRegionRuntime.pauseObservation();
        return true;
    }

    private static void resume(boolean paused) {
        if (paused) ConcolicRegionRuntime.resumeObservation();
    }

    public static boolean serializing() {
        return pause();
    }

    public static void serialized(boolean paused) {
        resume(paused);
    }

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

    static long filingBegins(String transport, String location) {
        return inFlight(transport, location, true);
    }

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

    static String location(String key) {
        int at = key.lastIndexOf('@');
        return at < 0 ? key : key.substring(0, at);
    }

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

    public static void stored(String transport, String key, Object owner,
                              byte[] data) {
        boolean paused = false;
        long store = -1L;
        try {
            paused = pause();
            store = filingBegins(transport, location(key));
            RowOrder.Position position = Identity.enginePosition();
            Object document = StoreContent.stored(transport, key, data);
            Outbound message = outbound(transport, key, "1", REQUEST, owner,
                    null);
            if (message.active()) {
                STORED.put(transport + "\n" + key, message);
                FILINGS.put(transport + "\n" + key, FILED.incrementAndGet());
            }
            written(transport, key, owner, position, document);
        } catch (RuntimeException fault) {
            doorFault("stored " + key, fault);
        } finally {
            storeEnded(transport, store);
            resume(paused);
        }
    }

    private static final Map<String, Long> FILINGS =
            new ConcurrentHashMap<String, Long>();
    private static final AtomicLong FILED = new AtomicLong();

    public static void deleted(String transport, String path, Object owner) {
        boolean paused = false;
        try {
            paused = pause();
            written(transport, trimmed(path) + "@" + TOMBSTONE, owner,
                    Identity.enginePosition(), null);
        } catch (RuntimeException fault) {
            doorFault("deleted " + path, fault);
        } finally {
            resume(paused);
        }
    }

    public static boolean absent(String transport, String path, String op,
                                 Object owner) {
        boolean paused = false;
        try {
            paused = pause();
            String bare = trimmed(path);
            if (absentVersion(transport, bare) != TOMBSTONE) return false;
            read(transport, bare + "@" + TOMBSTONE, op, owner);
            return true;
        } catch (RuntimeException fault) {
            doorFault("absent " + path, fault);
            return false;
        } finally {
            resume(paused);
        }
    }

    static long absentVersion(String transport, String path) {
        Thread reader = Thread.currentThread();
        long began = System.currentTimeMillis();
        synchronized (STORING) {
            while (!tombstoned(transport, path)
                    && !inFlight(transport, path, reader).isEmpty()) {
                long left = began + FILED_WAIT_MS
                        - System.currentTimeMillis();
                if (left <= 0L) break;
                try {
                    STORING.wait(left);
                } catch (InterruptedException interrupted) {
                    reader.interrupt();
                    break;
                }
            }
        }
        return tombstoned(transport, path) ? TOMBSTONE : -1L;
    }

    private static boolean tombstoned(String transport, String path) {
        synchronized (LIVES) {
            int[] held = LIVES.get(trimmed(transport) + "\n" + trimmed(path));
            return held != null && held[2] != 0;
        }
    }

    public static void childrenFetched(String transport, String parent,
                                       List<String> children, Object owner) {
        if (children == null || children.isEmpty()
                || NOTIFIED.get() == null) {
            return;
        }
        boolean paused = false;
        try {
            paused = pause();
            String kind = NOTIFIED.get();
            String node = RuntimeTraceContext.ownedSource(owner).key();
            String folder = trimmed(parent).endsWith("/") ? trimmed(parent)
                    : trimmed(parent) + "/";
            List<String> keys = new ArrayList<String>();
            Set<String> delivered = new java.util.HashSet<String>();
            for (String child : children) {
                String key = folder + trimmed(child) + "@0";
                if (DELIVERIES.containsKey(delivery(node, transport, key,
                        kind))) {
                    delivered.add(key);
                } else if (filed(transport, key) != null) {
                    keys.add(key);
                }
            }
            String newest = newestFiled(transport, keys, delivered);
            Outbound message = newest == null ? null
                    : STORED.get(transport + "\n" + newest);
            if (message != null) {
                receive(transport, newest, owner, message, kind);
            }
        } catch (RuntimeException fault) {
            doorFault("childrenFetched " + parent, fault);
        } finally {
            resume(paused);
        }
    }

    static String newestFiled(String transport, List<String> keys,
                              Set<String> delivered) {
        String newest = null;
        long at = -1L;
        for (String key : keys) {
            Long order = FILINGS.get(transport + "\n" + key);
            if (order == null || delivered.contains(key)) continue;
            if (order > at) {
                at = order;
                newest = key;
            }
        }
        return newest;
    }

    private static String delivery(String node, String transport, String key,
                                   String kind) {
        return node + "\n" + transport + "\n" + key + "\n" + kind;
    }

    private static void written(String transport, String key, Object owner,
                                RowOrder.Position position,
                                Object document) {
        long version = version(key);
        if (version < 0L) return;
        String path = life(transport, location(key), version, true);
        String node = RuntimeTraceContext.ownedSource(owner).key();
        if (CausynthTraceRecorder.tracing()) {
            OccurrenceAddress writer = Identity.currentOccurrence(node);
            CausynthTraceRecorder.storeWritten(trimmed(transport), path,
                    version, writer);
            if (document != null) {
                CausynthTraceRecorder.storeLeaves(true, trimmed(transport),
                        path, version, writer, StoreContent.leafRows(
                                transport, path, document));
            }
        }
        if (!RowRuntime.open()) return;
        OccurrenceAddress at = RowRuntime.doorOccurrence(node);
        LocationId location = storeLocation(transport, path);
        RowRuntime.storeWrite(at, position,
                Endpoint.messageSite(trimmed(transport), "WRITE",
                        location.slot().replace('/', '.').replace('@', '.')),
                location, version);
    }

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

    static void doorFault(String door, RuntimeException fault) {
        StackTraceElement[] frames = fault.getStackTrace();
        RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING, door,
                "the engine's door threw " + fault + (frames.length == 0
                        ? "" : " at " + frames[0]) + "; the system's call"
                        + " went on, and the rows the door states are"
                        + " missing");
    }

    private static <T> T guarded(String door, String at, T fallback,
                                 Supplier<T> call) {
        try {
            return call.get();
        } catch (RuntimeException fault) {
            doorFault(at == null ? door : door + " " + at, fault);
            return fallback;
        }
    }

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
        filed(trimmed(transport), trimmed(key));
        String path = life(transport, location(key), version, false);
        LocationId store = storeLocation(transport, path);
        String node = nodeHere();
        OccurrenceAddress here = Identity.currentOccurrence(node);
        String decoder = decoderNode(here, node);
        LocationId view = viewOf(store, decoder);
        boolean repoints = view != null && REPOINTED.add(
                trimmed(transport) + "\n" + path + "\n" + decoder + "@"
                        + version);
        if (view != null && REFRESHING.get() > 0) {
            Confirmation.overridden(view, version, here, "a decode inside"
                    + " a refresh the system asked for, what its reader"
                    + " reads at once");
        }
        List<Object> registered = Provenance.register(new Provenance.Version(
                store, path, version), product);
        CausynthTraceRecorder.storeDecoded(trimmed(transport), path, version,
                registered, here);
        if (!repoints) return;
        if (!RowRuntime.open()) {
            RowRuntime.viewBeforeWindow(view, version);
            return;
        }
        OccurrenceAddress at = RowRuntime.doorOccurrence(node);
        RowRuntime.viewWrite(at, Identity.enginePosition(),
                Endpoint.messageSite(trimmed(transport), "VIEW",
                        view.slot().replace('/', '.').replace('@', '.')),
                viewOf(store, at), version);
    }

    public static boolean publishing(String transport, String path,
                                     long version, Runnable apply) {
        boolean delivering = DELIVERING.get() > 0 && REFRESHING.get() == 0;
        String why = REFRESHING.get() > 0
                ? "inside a refresh the system asked for"
                : "on a thread delivering no store notification";
        return guarded("publishing", path, Boolean.FALSE, () -> {
            if (!delivering && !Confirmation.holdsViews()
                    && !ScheduleLog.enforcing()) {
                return false;
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
                    return false;
                }
                return Confirmation.publishing(view, version, at, decoder,
                        CausynthTraceRecorder.captureScope(), apply,
                        publishTurn(transport, life, version, decoder));
            } finally {
                resume(paused);
            }
        });
    }

    private static String publishedSite(String transport, String path,
                                        long version) {
        return ScheduleEvent.published(trimmed(transport),
                storeLocation(transport, path).slot(), version);
    }

    private static final Set<String> PUBLISH_TURNS =
            java.util.concurrent.ConcurrentHashMap.newKeySet();

    private static String publishTurn(String transport, String path,
                                      long version, String node) {
        if (version < 0L || node == null || node.isEmpty()) return null;
        String site = publishedSite(transport, path, version);
        return PUBLISH_TURNS.add(node + "\n" + site) ? site : null;
    }

    private static String decoderNode(OccurrenceAddress here, String node) {
        return here != null ? here.node().render() : node;
    }

    public static long refreshStarting() {
        int depth = REFRESHING.get();
        REFRESHING.set(depth + 1);
        return depth;
    }

    public static void refreshEnded(long token) {
        if (token <= 0L) {
            REFRESHING.remove();
        } else {
            REFRESHING.set((int) token);
        }
    }

    private static final ThreadLocal<Integer> REFRESHING =
            ThreadLocal.withInitial(() -> 0);

    private static String nodeHere() {
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        return view.source == null ? "" : view.source.key();
    }

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
        String site = ContentPort.viewed(trimmed(transport), path);
        RowRuntime.storeRead(at, Identity.enginePosition(), site,
                version.location, version.version);
        LocationId view = viewOf(version.location, at);
        if (view != null) {
            RowRuntime.viewRead(at, Identity.enginePosition(), site + "#VIEW",
                    view, version.version);
        }
    }

    public static boolean capturingContent() {
        return StoreContent.capturing() || CausynthTraceRecorder.tracing();
    }

    public static void jsonWritten(byte[] bytes, Object document) {
        try {
            StoreContent.written(bytes, document);
        } catch (RuntimeException fault) {
            doorFault("jsonWritten", fault);
        }
    }

    public static void jsonRead(byte[] bytes, Object tree) {
        try {
            String version = StoreContent.parsed(bytes, tree);
            if (version == null || !CausynthTraceRecorder.tracing()) return;
            int cut = version.indexOf('\n');
            String transport = version.substring(0, cut);
            String key = version.substring(cut + 1);
            String path = life(transport, location(key), version(key), false);
            CausynthTraceRecorder.storeLeaves(false, transport, path,
                    version(key), Identity.currentOccurrence(nodeHere()),
                    StoreContent.leafRows(transport, path, tree));
        } catch (RuntimeException fault) {
            doorFault("jsonRead", fault);
        }
    }

    static LocationId viewOf(LocationId store, OccurrenceAddress at) {
        return viewOf(store, at == null ? "" : at.node().render());
    }

    private static LocationId viewOf(LocationId store, String node) {
        if (store == null || node.isEmpty() || node.startsWith(
                OccurrenceBinding.UNREGISTERED_SOURCE_KEY)) {
            return null;
        }
        return LocationId.of(LocationKind.VIEW, store.owner() + "@" + node,
                store.slot());
    }

    static LocationId storeLocation(String transport, String path) {
        String named = trimmed(path);
        int life = named.lastIndexOf(LIFE);
        String suffix = life < 0 ? "" : named.substring(life);
        String bare = life < 0 ? named : named.substring(0, life);
        return LocationId.of(LocationKind.STORE, trimmed(transport),
                RunNames.key(bare).location + suffix);
    }

    private static String life(String transport, String path,
                               long version, boolean write) {
        String key = trimmed(transport) + "\n" + trimmed(path);
        synchronized (LIVES) {
            int[] held = LIVES.get(key);
            if (held == null) {
                held = new int[] {1, 0, 0};
                LIVES.put(key, held);
            }
            if (write && version == 0L && held[1] != 0) {
                held[0]++;
                held[2] = 0;
            }
            if (write || version > 0L) held[1] = 1;
            if (write && version == TOMBSTONE) held[2] = 1;
            return held[0] == 1 ? trimmed(path)
                    : trimmed(path) + LIFE + held[0];
        }
    }

    private static final Map<String, int[]> LIVES = new HashMap<>();

    private static final String LIFE = "#";

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

    public static void notified(String kind, String transport, String path,
                                String type, Runnable callback) {
        NOTIFIED.set(trimmed(kind));
        DELIVERING.set(DELIVERING.get() + 1);
        FIRED.set(path == null || !CausynthTraceRecorder.tracing() ? null
                : new String[] {trimmed(transport), trimmed(path),
                        trimmed(type)});
        int owed = Confirmation.notificationBegins();
        try {
            callback.run();
        } finally {
            DELIVERING.set(DELIVERING.get() - 1);
            try {
                if (FIRED.get() != null) {
                    fired(Identity.currentOccurrence(nodeHere()));
                }
                Confirmation.notificationEnded(owed);
                NOTIFIED.remove();
                endInbound();
            } catch (RuntimeException fault) {
                doorFault("notified " + kind, fault);
            }
        }
    }

    private static final ThreadLocal<String[]> FIRED = new ThreadLocal<>();

    static void regionOpened(OccurrenceAddress occurrence) {
        if (FIRED.get() != null) fired(occurrence);
    }

    private static void fired(OccurrenceAddress occurrence) {
        String[] fired = FIRED.get();
        if (fired == null) return;
        FIRED.remove();
        CausynthTraceRecorder.watchFired(fired[0], life(fired[0], fired[1],
                -1L, false), fired[2], -1L, occurrence);
    }

    public static void storeRead(String transport, String key, String op,
                                 Object owner) {
        boolean paused = false;
        try {
            paused = pause();
            read(transport, key, op, owner);
        } catch (RuntimeException fault) {
            doorFault("storeRead " + key, fault);
        } finally {
            resume(paused);
        }
    }

    private static void read(String transport, String key, String op,
                             Object owner) {
        long version = version(key);
        String path = life(transport, location(key), version, false);
        if (CausynthTraceRecorder.tracing()) {
            CausynthTraceRecorder.storeRead(trimmed(transport), path, version,
                    op, Identity.currentOccurrence(
                            RuntimeTraceContext.ownedSource(owner).key()));
        }
        if (version < 0L || "getChildren".equals(op) || !RowRuntime.open()) {
            return;
        }
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || active.d3Address == null
                || active.activation.doorsOnly) {
            return;
        }
        LocationId location = storeLocation(transport, path);
        if (!chain().holdsPath(trimmed(transport), location.slot())
                && !active.onZkChain()) {
            return;
        }
        RowRuntime.storeRead(active.d3Address, Identity.enginePosition(),
                Endpoint.messageSite(trimmed(transport), "READ",
                        location.slot().replace('/', '.')
                                .replace('@', '.')),
                location, version);
    }

    private static volatile ZkChain chain;

    static ZkChain chain() {
        ZkChain held = chain;
        if (held != null) return held;
        synchronized (CHAIN_LOCK) {
            if (chain == null) chain = readChain();
            return chain;
        }
    }

    private static final Object CHAIN_LOCK = new Object();

    private static ZkChain readChain() {
        String named = trimmed(System.getenv(ZkChain.ENVIRONMENT));
        try {
            return ZkChain.held(named.isEmpty() ? null : Paths.get(named));
        } catch (IOException | RuntimeException unread) {
            RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING, named,
                    "the ZooKeeper chain " + named + " could not be read ("
                            + unread + "), so this replay states no store"
                            + " read of its store calls");
            return ZkChain.of(new ArrayList<JsonObject>());
        }
    }

    static String livePath(String transport, String key) {
        return life(transport, location(key), version(key), false);
    }

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
        read(transport, key, "getData", owner);
        StoreContent.fetched(transport, key, data);
        String kind = NOTIFIED.get();
        if (kind == null) return;
        Outbound message = filed(transport, key);
        if (message == null) return;
        receive(transport, key, owner, message, kind);
    }

    private static void receive(String transport, String key, Object owner,
                                Outbound message, String kind) {
        NOTIFIED.remove();
        endInbound(true);
        SymbolicMessageEnvelope.clearInbound();
        int delivery = DELIVERIES.merge(delivery(RuntimeTraceContext
                .ownedSource(owner).key(), transport, key, kind), 1,
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
        CausynthTraceRecorder.receivedExchange(transport, key, "1", REQUEST,
                null);
        if (!message.symbolic.isEmpty()) {
            SymbolicMessageEnvelope.installInbound(message.symbolic);
        }
        CURRENT.set(new Inbound(0L, key, "1", REQUEST));
    }

    public static Inbound current() {
        return CURRENT.get();
    }

    public static Inbound setAside() {
        Inbound held = CURRENT.get();
        CURRENT.remove();
        return held;
    }

    public static void putBack(Inbound held) {
        if (held == null) CURRENT.remove();
        else CURRENT.set(held);
    }

    public static long enterCarriedScope(Object scope, String role,
                                         String api) {
        return guarded("enterCarriedScope", role, 0L, () ->
                CausynthTraceRecorder.enterCarriedScope(scope, role, api));
    }

    public static void exitCarriedScope(long token) {
        guarded("exitCarriedScope", null, () ->
                CausynthTraceRecorder.exitCarriedScope(token));
    }

    public static long beginTick(Object owner, String role) {
        return guarded("beginTick", role, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginDaemonTick(owner, role);
        });
    }

    public static boolean vacant(long tick) {
        return CausynthTraceRecorder.vacantDaemonTick(tick);
    }

    public static Object startupStep(String step, String who) {
        return CausynthTraceRecorder.startupStep(step, who);
    }

    public static void startupDone(Object pass) {
        CausynthTraceRecorder.startupDone(pass);
    }

    public static void endTick(long token) {
        guarded("endTick", null, () -> {
            endInbound();
            CausynthTraceRecorder.endDaemonTick(token);
        });
    }

    public static void startRecording() {
        CausynthTraceRecorder.startRecording();
    }

    public static boolean startupWindow() {
        return RecordingWindow.atStartup();
    }

    public static long beginNodeStartup(String kind, String role,
                                        String sourceId) {
        return guarded("beginNodeStartup", role, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginNodeStartup(kind, role,
                    sourceId);
        });
    }

    public static long beginNodeStartup(Object node) {
        return guarded("beginNodeStartup", null, 0L, () -> {
            endInbound();
            return CausynthTraceRecorder.beginNodeStartup(node);
        });
    }

    public static void endNodeStartup(long token) {
        guarded("endNodeStartup", null, () ->
                CausynthTraceRecorder.endNodeStartup(token));
    }

    public static void stopRecording() {
        CausynthTraceRecorder.stopRecording();
    }

    public static boolean replaying() {
        return CausynthTraceRecorder.replaying();
    }

    public static void registerSource(Object anchor, String kind, String role,
                                      String sourceId, long epoch) {
        CausynthTraceRecorder.registerSource(anchor, kind, role, sourceId,
                epoch);
    }

    public static void spelledAs(String sourceId, String... spellings) {
        if (spellings == null) return;
        for (String spelling : spellings) {
            RunNames.spelled(trimmed(sourceId), trimmed(spelling));
        }
    }

    public static void registerSourceAlias(Object alias, Object anchor) {
        CausynthTraceRecorder.registerSourceAlias(alias, anchor);
    }

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

    public static long beginWorkloadCall(String api) {
        return CausynthTraceRecorder.beginWorkloadCall(api);
    }

    public static void endWorkloadCall(long call, String api) {
        if (call != 0L) endRequest(call, api);
    }

    public static Outbound outboundNone() {
        return Outbound.EMPTY;
    }

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
