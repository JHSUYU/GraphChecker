package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Digests;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.ExpressionRefs;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.Validity;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class RowRuntime {
    public static final String SESSIONS_ENV = "CAUSYNTH_CONCOLIC_SESSIONS";

    private static final Object LOCK = new Object();
    private static final Map<String, ClockCell> CLOCK_CELLS =
            new ConcurrentHashMap<String, ClockCell>();

    private static final class ClockCell {
        private final String rootId;
        private final long reading;

        private ClockCell(String rootId, long reading) {
            this.rootId = rootId;
            this.reading = reading;
        }
    }
    private static volatile SessionPublisher publisher;
    private static volatile String sessionId = "";

    private RowRuntime() {
    }

    public static void configure(Path resultFile) {
        if (resultFile == null) return;
        synchronized (LOCK) {
            if (publisher != null) return;
            sessionId = sessionId(resultFile);
            Path sessions = declaredSessionsRoot();
            publisher = sessions == null
                    ? SessionPublisher.of(iterationOf(resultFile), sessionId)
                    : SessionPublisher.at(SessionDir.of(sessions.getParent()
                            == null ? sessions : sessions.getParent(),
                            sessionId));
        }
        final SessionPublisher opened = publisher;
        ScheduleLog.install(new ScheduleLog.Sink() {
            @Override
            public void write(JsonObject row) {
                opened.schedule(row);
            }
        });
    }

    public static boolean open() {
        return publisher != null;
    }

    public static String sessionId() {
        return sessionId;
    }

    private static Path declaredSessionsRoot() {
        String declared = trimmed(System.getenv(SESSIONS_ENV));
        return declared.isEmpty() ? null
                : Paths.get(declared).toAbsolutePath();
    }

    private static Path iterationOf(Path inside) {
        if (inside == null) return null;
        Path cursor = inside.toAbsolutePath();
        while (cursor != null) {
            Path name = cursor.getFileName();
            if (name != null && name.toString().startsWith("iteration-")) {
                return cursor;
            }
            cursor = cursor.getParent();
        }
        Path parent = inside.toAbsolutePath().getParent();
        return parent == null ? inside.toAbsolutePath() : parent;
    }

    private static String sessionId(Path resultFile) {
        Path parent = resultFile.toAbsolutePath().getParent();
        String where = parent == null || parent.getFileName() == null
                ? "session" : parent.getFileName().toString();
        return where + "-" + ArtifactIO.digest(trimmed(
                resultFile.toAbsolutePath() + "\n"
                + ManagementFactory.getRuntimeMXBean().getName() + "\n"
                + System.nanoTime()), 8);
    }


    public static OccurrenceAddress beginActivation(long token,
                                                    String nodeKey,
                                                    String regionId,
                                                    String taskId) {
        OccurrenceAddress address = Identity.currentOccurrence(nodeKey);
        SessionPublisher session = publisher;
        if (address == null) {
            if (session != null) {
                gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                        firstNonBlank(trimmed(regionId), trimmed(taskId),
                                Long.toString(token)),
                        "an activation of this region ran on a node this run"
                                + " could not name, so it has no address");
            }
            return null;
        }
        FocusedReplay.entered(address);
        if (session != null) {
            session.activation(ActivationRow.of(sessionId(), address,
                    trimmed(taskId), FocusedReplay.focused(taskId,
                            address), true, threadKey(),
                    Identity.claimKind(), anchorProducer(address)));
            if (address.lineageLost()) {
                session.gap(GapRow.of(sessionId(), GapKind.LINEAGE_LOST,
                        GapClass.DIAGNOSTIC, address.render(),
                        "the activation ran under a scope this run could not"
                                + " attribute; the address states the role it"
                                + " ran as and a window-local k"));
            }
        }
        return address;
    }

    static void answered(OccurrenceAddress ran, OccurrenceAddress planned) {
        if (ran == null) return;
        gap(GapKind.ADDRESS_UNSTABLE, GapClass.DIAGNOSTIC, planned.render(),
                "the planned occurrence ran at " + ran.render() + ", under"
                        + " a chain of its shape whose counts differ from"
                        + " the recording's, and answers it: its rows state"
                        + " the planned address");
    }

    public static void ambientActivation(OccurrenceAddress address) {
        SessionPublisher session = publisher;
        if (session == null || address == null) return;
        if (AMBIENT.putIfAbsent(address.id(), Boolean.TRUE) != null) return;
        session.activation(ActivationRow.of(sessionId(), address, "", false,
                false, threadKey(), Identity.claimKind(),
                anchorProducer(address)));
    }

    private static Endpoint anchorProducer(OccurrenceAddress address) {
        return address.context().form() == CausalContext.Form.ANCHOR
                ? Interactions.producer(((CausalContext.Anchor)
                        address.context()).producerEndpointId())
                : null;
    }

    private static final Map<String, Boolean> AMBIENT =
            new ConcurrentHashMap<String, Boolean>();

    private static String threadKey() {
        String claimed = Identity.claimedStart();
        if (claimed != null) return ActivationRow.CLAIMED + claimed;
        Thread thread = Thread.currentThread();
        return thread.getName() + "#" + thread.getId();
    }


    public static void decision(OccurrenceAddress occurrence, long seq,
                                String siteId, int ordinal, boolean outcome,
                                JsonObject condition) {
        decision(occurrence, seq, siteId, ordinal, outcome, condition, null,
                "");
    }

    static void decision(OccurrenceAddress occurrence, long seq,
                         String siteId, int ordinal, boolean outcome,
                         JsonObject condition, Boolean concreteOutcome,
                         String via) {
        if (occurrence == null) return;
        SessionPublisher session = publisher;
        if (session != null) {
            String ref = expressionRef(condition);
            DecisionRow row = DecisionRow.of(sessionId(), sequence(seq),
                    occurrence, trimmed(siteId), ordinal, outcome, ref,
                    clockReadings(condition)).via(via);
            session.decision(concreteOutcome == null ? row
                    : row.forced(concreteOutcome.booleanValue()));
        }
        if (FocusedReplay.observeDecision(occurrence, siteId, ordinal,
                outcome)) {
            ConcolicResultPublisher.concludeAtRefusal();
        }
    }

    public static Endpoint exported(OccurrenceAddress producer, long seq,
                                    String portId, long handle, int attempt,
                                    JsonObject expression, String javaType,
                                    String recordedValue) {
        if (producer == null) return null;
        Endpoint endpoint = endpoint(producer, portId, attempt);
        String ref = expressionRef(expression);
        Interactions.exported(handle, endpoint);
        SessionPublisher session = publisher;
        if (session != null) {
            String type = statedJavaType("export", endpoint.id(), javaType,
                    expression);
            if (!type.isEmpty()) {
                session.export(ExportRow.of(sessionId(), sequence(seq),
                        endpoint, ref, type, handle,
                        trimmed(recordedValue)));
            }
        }
        return endpoint;
    }

    public static Endpoint nextEndpoint(OccurrenceAddress occurrence,
                                        String site, int attempt) {
        return occurrence == null ? null : endpoint(occurrence, site,
                attempt);
    }


    public static Endpoint attachedAt(Endpoint endpoint, long seq,
                                      String portId, long handle,
                                      String correlationId, String half,
                                      String symbol, String javaType,
                                      String arrival, boolean answered,
                                      String answeredValue) {
        if (endpoint == null) return null;
        Interactions.Pairing pairing = Interactions.pairing(portId, handle,
                correlationId, half);
        Endpoint producer = pairing.producer();
        if (producer != null && handle > 0L
                && !"HANDLE".equals(pairing.key())) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, endpoint.id(),
                    "this delivery states VM handle " + handle
                            + " and was paired by " + pairing.key()
                            + ", so the producer is the message's and not"
                            + " the staged expression's");
        }
        confirm(endpoint, producer, arrival);
        SessionPublisher session = publisher;
        if (session != null) {
            String type = statedJavaType("attach", endpoint.id(), javaType,
                    null);
            if (!type.isEmpty()) {
                session.attach(AttachRow.of(sessionId(), sequence(seq),
                        endpoint, trimmed(symbol), type,
                        trimmed(arrival), answered,
                        answered ? trimmed(answeredValue) : null, producer,
                        trimmed(correlationId), pairing.key()));
            }
            if (producer == null) {
                session.gap(GapRow.of(sessionId(), GapKind.LINEAGE_LOST,
                        GapClass.DIAGNOSTIC, endpoint.id(),
                        handle == SymbolicMessageEnvelope.ABSENT
                                ? "the message carried no element for "
                                + trimmed(portId) + ", so the delivery"
                                + " pairs with no export"
                                : "the delivery at " + trimmed(portId)
                                + " was paired with no export of this run"));
            }
        }
        return endpoint;
    }


    private static void confirm(Endpoint consumer, Endpoint producer,
                                String arrival) {
        Confirmation.Compared compared = Confirmation.attached(consumer,
                producer, arrival);
        if (!compared.mismatch.isEmpty()) {
            gap(GapKind.CONFIRM_MISMATCH, GapClass.DIAGNOSTIC, consumer.id(),
                    compared.mismatch);
            Confirmation.mismatched();
        }
        if (!compared.substitution.isEmpty()) {
            gap(GapKind.ADDRESS_UNSTABLE, GapClass.DIAGNOSTIC, consumer.id(),
                    compared.substitution);
        }
    }

    public static OccurrenceAddress occurrenceHere(String nodeKey,
                                                   String site) {
        String node = trimmed(nodeKey);
        if (node.isEmpty() || OccurrenceBinding.UNREGISTERED_SOURCE_KEY
                .equals(node)) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, trimmed(site),
                    "an event at this site ran on a thread the attribution"
                            + " rule names no node for -- no explicit scope,"
                            + " no registered receiver on its frames, no"
                            + " registered starter -- so its address is the"
                            + " unregistered one");
            node = OccurrenceBinding.UNREGISTERED_SOURCE_KEY;
        }
        return Identity.currentOccurrence(node);
    }

    private static boolean ownCode(String site) {
        if (site == null) return false;
        int method = site.indexOf('#');
        return EnginePlumbing.site(method < 0 ? site
                : site.substring(0, method));
    }

    public static void write(OccurrenceAddress occurrence, long seq,
                             String site, LocationId location, long version,
                             JsonObject expression, String javaType,
                             String siteIndex, WriteRow.Referent referent,
                             String referentRefused, boolean initial) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null
                || ownCode(site)) {
            return;
        }
        Endpoint at = endpoint(occurrence, site, 0, siteIndex);
        String type = statedJavaType("version", location + "#" + version,
                javaType, expression);
        if (type.isEmpty()) return;
        WRITTEN.add(Confirmation.key(location, version));
        distinct(at, "write#" + location + "#" + version);
        long sequenced = sequence(seq);
        String ref = expressionRef(expression);
        session.write(initial
                ? WriteRow.initial(sessionId(), sequenced, at, location,
                version, ref, type)
                : WriteRow.of(sessionId(), sequenced, at, location, version,
                ref, type, referent, referentRefused));
        Confirmation.wrote(location, version, at, initial);
    }

    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue,
                            String siteIndex, long mintVersion) {
        read(occurrence, seq, site, location, observedVersion, symbol,
                javaType, concreteValue, siteIndex, mintVersion, false);
    }

    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue,
                            String siteIndex, long mintVersion,
                            boolean unnamedWriter) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null
                || ownCode(site)) {
            return;
        }
        Endpoint at = endpoint(occurrence, site, 0, siteIndex);
        String type = statedJavaType("read", location + "#" + seq, javaType,
                null);
        if (type.isEmpty()) return;
        if (mintVersion == ReadRow.UNKNOWN_VERSION && observedVersion >= 0L) {
            READERS.computeIfAbsent(Confirmation.key(location,
                    observedVersion), key -> new Readers(at, location,
                    observedVersion)).count.incrementAndGet();
        }
        distinct(at, "read#" + location + "#" + seq);
        session.read(ReadRow.of(sessionId(), sequence(seq), at, location,
                observedVersion, trimmed(symbol), type,
                trimmed(concreteValue).isEmpty() ? null
                        : trimmed(concreteValue), mintVersion,
                unnamedWriter));
        Confirmation.read(at, location, observedVersion, mintVersion);
    }

    static OccurrenceAddress doorOccurrence(String nodeKey) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null && active.d3Address != null) {
            return active.d3Address;
        }
        OccurrenceAddress here = Identity.currentOccurrence(nodeKey);
        ambientActivation(here);
        return here;
    }

    static final String STORE_TYPE = "[B";

    public static void storeWrite(OccurrenceAddress occurrence,
                                  RowOrder.Position at,
                                  String site, LocationId location,
                                  long version) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) {
            return;
        }
        Endpoint writer = Identity.endpointAt(occurrence, site, 0);
        if (writer == null) return;
        WRITTEN.add(Confirmation.key(location, version));
        session.write(WriteRow.of(sessionId(), sequence(at.seq), writer,
                location, version, "", STORE_TYPE).withTie(at.tie));
        Confirmation.wrote(location, version, writer, false);
    }

    public static void storeRead(OccurrenceAddress occurrence,
                                 RowOrder.Position position,
                                 String site, LocationId location,
                                 long version) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) {
            return;
        }
        if (!STORE_READS.add(occurrence.id() + "|" + position.seq + "|"
                + location + "|" + version)) {
            return;
        }
        Endpoint at = Identity.endpointAt(occurrence, site, 0);
        if (at == null) return;
        if (version >= 0L) {
            READERS.computeIfAbsent(Confirmation.key(location, version),
                    key -> new Readers(at, location, version))
                    .count.incrementAndGet();
        }
        session.read(ReadRow.of(sessionId(), sequence(position.seq), at,
                location, version, storeSymbol(location, version), STORE_TYPE,
                null).withTie(position.tie));
        Confirmation.read(at, location, version, ReadRow.UNKNOWN_VERSION);
        FocusedReplay.pairedRead(at, version);
    }

    public static void viewWrite(OccurrenceAddress occurrence,
                                 RowOrder.Position position,
                                 String site, LocationId view,
                                 long version) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || view == null) return;
        viewInitial(occurrence, view);
        if (READERS.containsKey(Confirmation.key(view, version))) return;
        Endpoint at = Identity.endpointAt(occurrence, site, 0);
        if (at == null) return;
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_exp", "Y_J_" + version);
        value.addProperty("_java_type", "J");
        WRITTEN.add(Confirmation.key(view, version));
        session.write(WriteRow.of(sessionId(), sequence(position.seq), at,
                view, version, expressionRef(value), "J")
                .withTie(position.tie));
        Confirmation.wrote(view, version, at, false);
    }

    static void viewBeforeWindow(LocationId view, long version) {
        if (view == null || version < 0L) return;
        PRE_WINDOW.put(Confirmation.viewKey(view), version);
    }

    private static void viewInitial(OccurrenceAddress occurrence,
                                    LocationId view) {
        Long version = PRE_WINDOW.remove(Confirmation.viewKey(view));
        if (version == null
                || WRITTEN.contains(Confirmation.key(view, version))) {
            return;
        }
        String owner = view.owner();
        int node = owner.indexOf('@');
        String site = Endpoint.initialSite(Endpoint.messageSite(
                node < 0 ? owner : owner.substring(0, node), "VIEW",
                view.slot().replace('/', '.').replace('@', '.')));
        Endpoint at = Identity.endpointAt(occurrence, site, 0);
        if (at == null) return;
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_exp", "Y_J_" + version);
        value.addProperty("_java_type", "J");
        WRITTEN.add(Confirmation.key(view, version));
        publisher.write(WriteRow.initial(sessionId(), 0L, at, view, version,
                expressionRef(value), "J"));
        Confirmation.wrote(view, version, at, true);
    }

    private static final Map<String, Long> PRE_WINDOW =
            new ConcurrentHashMap<String, Long>();

    public static void viewRead(OccurrenceAddress occurrence,
                                RowOrder.Position position,
                                String site, LocationId view, long version) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || view == null) return;
        viewInitial(occurrence, view);
        if (!STORE_READS.add(occurrence.id() + "|" + position.seq + "|"
                + view + "|" + version)) {
            return;
        }
        Endpoint at = Identity.endpointAt(occurrence, site, 0);
        if (at == null) return;
        READERS.computeIfAbsent(Confirmation.key(view, version),
                key -> new Readers(at, view, version)).count.incrementAndGet();
        session.read(ReadRow.of(sessionId(), sequence(position.seq), at, view,
                version, "V_" + Digests.digest(at.id(), 16), "J",
                Long.toString(version)).withTie(position.tie));
        Confirmation.read(at, view, version, ReadRow.UNKNOWN_VERSION);
        FocusedReplay.pairedRead(at, version);
    }

    private static final Set<String> STORE_READS =
            ConcurrentHashMap.newKeySet();


    static String storeSymbol(LocationId location, long version) {
        return "S_" + Digests.digest(location.owner() + "#"
                + location.slot() + "#" + version, 16);
    }

    private static void distinct(Endpoint at, String event) {
        if (at == null) return;
        String first = ENDPOINTS.putIfAbsent(at.id(), trimmed(event));
        if (first == null || first.equals(trimmed(event))) return;
        gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, at.render(),
                "two events of this site inside one occurrence stand on the"
                        + " same frames, so the site index cannot"
                        + " distinguish them: " + first + " and " + event);
    }

    private static final Set<String> WRITTEN = ConcurrentHashMap.newKeySet();
    private static final Map<String, Readers> READERS =
            new ConcurrentHashMap<String, Readers>();
    private static final Map<String, String> OUTSIDE =
            new ConcurrentHashMap<String, String>();

    private static final class Readers {
        final Endpoint first;
        final LocationId location;
        final long version;
        final AtomicInteger count = new AtomicInteger();

        Readers(Endpoint first, LocationId location, long version) {
            this.first = first;
            this.location = location;
            this.version = version;
        }
    }

    static void storedOutside(LocationId location, long version,
                              String site) {
        if (location == null) return;
        OUTSIDE.putIfAbsent(Confirmation.key(location, version),
                trimmed(site));
    }

    static String outsideSite(String key) {
        return OUTSIDE.get(trimmed(key));
    }

    private static void unattributedStores() {
        for (Map.Entry<String, Readers> read : READERS.entrySet()) {
            if (WRITTEN.contains(read.getKey())) continue;
            Readers readers = read.getValue();
            String site = OUTSIDE.get(read.getKey());
            gap(GapKind.UNATTRIBUTED_STORE, GapClass.DIAGNOSTIC,
                    read.getKey(), readers.count.get() + " read(s) of this"
                            + " session observed version " + readers.version
                            + " of " + readers.location + ", the first at "
                            + readers.first.render() + ", and no write row"
                            + " of the session states it: "
                            + (site == null ? "no read-out of this run"
                            + " states its store"
                            : "its store ran outside every activation"
                            + (site.isEmpty() ? "" : ", at " + site)));
        }
    }

    private static final Map<String, String> ENDPOINTS =
            new ConcurrentHashMap<String, String>();

    public static void rootMint(OccurrenceAddress occurrence, long seq,
                                String rootId, String symbol, RootKind kind,
                                RootCategory category,
                                String recordedValue, String domainMin,
                                String domainMax, Validity valid,
                                boolean declared, Clock clock,
                                long clockSkew) {
        if (kind == RootKind.CLOCK) {
            clockCell(symbol, rootId, recordedValue);
        }
        SessionPublisher session = publisher;
        if (session == null || occurrence == null) return;
        session.rootMint(RootMintRow.of(sessionId(), sequence(seq),
                occurrence,
                trimmed(rootId), trimmed(symbol),
                kind == null ? RootKind.INTEGRAL : kind, category,
                trimmed(recordedValue),
                trimmed(domainMin).isEmpty() ? null : trimmed(domainMin),
                trimmed(domainMax).isEmpty() ? null : trimmed(domainMax),
                declared, clock, clockSkew).validated(valid));
        FocusedReplay.mintPublished(rootId);
    }

    public static void target(OccurrenceAddress occurrence, long seq,
                              String anchorSiteId, JsonObject condition,
                              boolean fatalArm, boolean observedFatal,
                              boolean reachedAnchor) {
        target(occurrence, seq, anchorSiteId, reachedAnchor
                        ? fatalTerm(condition, fatalArm) : "",
                observedFatal, reachedAnchor, null, false);
    }

    static void target(OccurrenceAddress occurrence, long seq,
                       String anchorSiteId, String phiTerm,
                       boolean observedFatal, boolean reachedAnchor,
                       TargetRow.OpenArm openArm, boolean forced) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null) return;
        TargetRow row = TargetRow.of(sessionId(), sequence(seq), occurrence,
                trimmed(anchorSiteId), trimmed(phiTerm), observedFatal,
                reachedAnchor, openArm);
        session.target(forced ? row.forced() : row);
        if (!reachedAnchor || !FocusedReplay.declaredTarget(occurrence)) {
            return;
        }
        if (forced) {
            ConcolicResultPublisher.concludeAtForcedTarget();
        } else if (observedFatal) {
            ConcolicResultPublisher.concludeAtWitness();
        }
    }

    static String fatalTerm(JsonObject condition, boolean fatalArm) {
        String ref = trimmed(expressionRef(condition));
        return ref.isEmpty() ? String.valueOf(fatalArm)
                : Arms.conjunct(ref, fatalArm);
    }

    public static void messageContextRefused(String subject, String detail) {
        gap(GapKind.MESSAGE_CONTEXT_REFUSED, GapClass.DIAGNOSTIC, subject,
                detail);
    }

    public static void gap(GapKind kind, GapClass cls, String subject,
                           String detail) {
        SessionPublisher session = publisher;
        String named = trimmed(subject).trim();
        String says = trimmed(detail);
        if (named.isEmpty() && session != null) {
            named = sessionId();
            says = "this " + kind + " names no subject, so the run cannot"
                    + " say what it refused on: " + says;
        }
        if (!claimEvent("gap", kind + "#" + cls + "#" + named + "#" + says)) {
            return;
        }
        if (session == null) {
            CausynthTraceRecorder.recordingGap(kind, cls, named, says);
            return;
        }
        session.gap(GapRow.of(sessionId(), kind, cls, named, says));
    }

    private static final Map<String, AtomicInteger> UNNAMED =
            new ConcurrentHashMap<String, AtomicInteger>();

    static void regionNamed(int region, OccurrenceAddress address,
                            Object receiver, long hop) {
        CausynthTraceRecorder.regionNamed(region, address);
        ConcolicRegionRuntime.regionNamed(address, receiver, hop);
    }

    static void regionUnnamed(int region, long hop, Throwable thrown) {
        ConcolicRegionRuntime.regionUnnamed(hop, thrown);
        CausynthTraceRecorder.regionUnnamed(region);
    }

    static void unnamedEntry(String nodeKey, String regionId) {
        if (!RecordingWindow.opened()) return;
        String subject = trimmed(nodeKey) + "/region/"
                + trimmed(regionId);
        if (UNNAMED.computeIfAbsent(subject, key -> new AtomicInteger())
                .getAndIncrement() > 0) {
            return;
        }
        gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, subject,
                "work started where no hop named its starter (a connection"
                        + " acceptor's, a daemon's started under no root)"
                        + " entered this region before a hop named it, so"
                        + " the entry opened no occurrence (IDENTITY §1,"
                        + " unnamed work): no decision, root or write of it"
                        + " is recorded, its events are its role's, and a"
                        + " closure reaching them stops there; the session"
                        + " manifest counts every such entry"
                        + " (unnamedEntries)");
    }

    private static final Map<String, Map<String, String>> CONCRETE =
            new ConcurrentHashMap<String, Map<String, String>>();
    private static final Set<String> DERIVED =
            ConcurrentHashMap.<String>newKeySet();
    private static final Set<String> DOORS_ONLY =
            ConcurrentHashMap.<String>newKeySet();

    static void ranDoorsOnly(OccurrenceAddress occurrence) {
        if (occurrence != null) DOORS_ONLY.add(occurrence.render());
    }

    static void concreteReading(String rootId, String occurrence,
                                String value) {
        if (trimmed(occurrence).isEmpty() || trimmed(value).isEmpty()) {
            return;
        }
        CONCRETE.computeIfAbsent(trimmed(rootId),
                key -> new ConcurrentHashMap<String, String>())
                .putIfAbsent(occurrence, value);
    }

    static void derivedRoot(String rootId) {
        if (!trimmed(rootId).isEmpty()) DERIVED.add(trimmed(rootId));
    }

    private static final Set<String> MINT_LABELS =
            ConcurrentHashMap.<String>newKeySet();

    public static void declaredMintLabel(String label) {
        String named = trimmed(label);
        if (!named.isEmpty()) MINT_LABELS.add(named);
    }

    public static boolean isDeclaredMint(String symbol) {
        String name = trimmed(symbol);
        if (name.length() <= FIELD_SYMBOL_HEAD || name.charAt(0) != 'M'
                || name.charAt(1) != '_'
                || !name.startsWith("_field_", 3)) {
            return false;
        }
        String rest = name.substring(FIELD_SYMBOL_HEAD);
        if (MINT_LABELS.contains(rest)) return true;
        for (int split = rest.indexOf('_'); split > 0;
             split = rest.indexOf('_', split + 1)) {
            if (MINT_LABELS.contains(rest.substring(0, split))) return true;
        }
        return false;
    }

    private static final int FIELD_SYMBOL_HEAD = "M_J_field_".length();

    public static void startWork(String startSiteId, Object carrier,
                                 Object submittedTo) {
        String site = trimmed(startSiteId);
        try {
            Identity.startWork(site, carrier, submittedTo);
        } catch (Throwable unnamed) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                    firstNonBlank(site, carrier == null ? ""
                            : carrier.getClass().getName()),
                    "the frame of this work start could not be filed, "
                            + "so the work it started carries no start-site "
                            + "frame in its execution index: " + unnamed);
        }
    }

    public static long claimStart(Object carrier) {
        return claim(carrier, false);
    }

    static long claimContinuation(Object carrier) {
        return claim(carrier, true);
    }

    private static long claim(Object carrier, boolean continuation) {
        if (carrier == null) return 0L;
        try {
            return Identity.claimStart(carrier, continuation);
        } catch (Throwable unnamed) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                    carrier.getClass().getName(),
                    "the start frame filed for this work could not be "
                            + "claimed, so the occurrences it publishes carry "
                            + "no start-site frame in their execution index: "
                            + unnamed);
            return 0L;
        }
    }

    public static void endClaim(long claim) {
        try {
            Identity.endClaim(claim);
        } catch (Throwable unclosed) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, "work entry",
                    "the claim of a returning work entry could not be ended, "
                            + "so the thread's next work stands on its start "
                            + "frames: " + unclosed);
        }
    }

    public static void claimItem(Object item) {
        if (item == null) return;
        try {
            Identity.claimItem(item);
        } catch (Throwable unnamed) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                    item.getClass().getName(),
                    "the start filed for this queue item could not be "
                            + "claimed, so the work it publishes carries "
                            + "no start-site frame in its execution index: "
                            + unnamed);
        }
    }

    public static String expressionRef(JsonElement expression) {
        if (expression == null || expression.isJsonNull()
                || !expression.isJsonObject()) {
            return "";
        }
        JsonObject object = expression.getAsJsonObject();
        String ref = refOf(object);
        SessionPublisher session = publisher;
        if (session != null) session.expression(ref, object);
        return ref;
    }

    static String refOf(JsonObject expression) {
        return expressions.ref(expression);
    }

    static Map<String, Long> clockReadings(JsonObject term) {
        Map<String, Long> named = new LinkedHashMap<String, Long>();
        if (term == null || CLOCK_CELLS.isEmpty()) return named;
        Deque<JsonElement> pending =
                new ArrayDeque<JsonElement>();
        Map<JsonElement, Boolean> seen =
                new IdentityHashMap<JsonElement, Boolean>();
        pending.push(term);
        while (!pending.isEmpty()) {
            JsonElement node = pending.pop();
            if (node == null || node.isJsonNull()
                    || node.isJsonPrimitive()) {
                continue;
            }
            if (seen.put(node, Boolean.TRUE) != null) continue;
            if (node.isJsonArray()) {
                for (JsonElement element : node.getAsJsonArray()) {
                    pending.push(element);
                }
                continue;
            }
            JsonObject object = node.getAsJsonObject();
            JsonElement spelling = object.get("_exp");
            if (spelling != null && spelling.isJsonPrimitive()) {
                ClockCell cell = CLOCK_CELLS.get(spelling.getAsString());
                if (cell != null) {
                    named.put(cell.rootId, Long.valueOf(cell.reading));
                }
            }
            for (Map.Entry<String, JsonElement> member : object.entrySet()) {
                pending.push(member.getValue());
            }
        }
        return named;
    }

    static void clockCell(String symbol, String rootId,
                          String recordedValue) {
        String named = trimmed(symbol);
        String root = trimmed(rootId);
        Long reading = longOrNull(recordedValue);
        if (named.isEmpty() || root.isEmpty() || reading == null) return;
        CLOCK_CELLS.put(named, new ClockCell(root, reading.longValue()));
    }

    private static long sequence(long vmEventId) {
        return vmEventId > 0L ? vmEventId : 0L;
    }

    private static String javaType(String declared, JsonObject expression) {
        String type = trimmed(declared);
        if (!type.isEmpty()) return type;
        return isNull(expression) ? NULL_REFERENCE_TYPE
                : statedType(expression);
    }

    private static final String NULL_REFERENCE_TYPE = "L";

    private static boolean isNull(JsonObject expression) {
        if (expression == null) return false;
        JsonElement symbol = expression.get("_exp");
        return symbol != null && symbol.isJsonPrimitive()
                && VmExpressionIr.SYMBOLIC_NULL.equals(symbol.getAsString());
    }

    private static String statedJavaType(String kind, String subject,
                                         String declared,
                                         JsonObject expression) {
        String type = javaType(declared, expression);
        if (!type.isEmpty()) return type;
        gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, subject,
                "this " + kind + " states no java type and its expression"
                        + " states none either, so the run cannot say what"
                        + " sort it wrote and publishes no row for it");
        return "";
    }

    private static String statedType(JsonObject expression) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression);
             walk.hasNext(); ) {
            JsonObject object = walk.next();
            JsonElement own = object.get("_java_type");
            if (own != null && own.isJsonPrimitive()) {
                String stated = trimmed(own.getAsString());
                if (!stated.isEmpty()) return stated;
            }
            if (VmExpressionIr.STRING_OPERATION_TYPE.equals(
                    VmExpressionIr.typeOf(object))) {
                JsonElement name = object.get("_name");
                return VmExpressionIr.stringOperationType(
                        name == null || !name.isJsonPrimitive() ? ""
                                : name.getAsString());
            }
        }
        return "";
    }

    private static Long longOrNull(String value) {
        try {
            return Long.valueOf(trimmed(value));
        } catch (NumberFormatException notALong) {
            return null;
        }
    }

    private static volatile ExpressionRefs expressions = new ExpressionRefs();

    private static final Map<String, Boolean> CLAIMED_EVENTS =
            new ConcurrentHashMap<String, Boolean>();

    public static boolean claimEvent(String kind, String identity) {
        return CLAIMED_EVENTS.put(trimmed(kind) + "\n"
                + trimmed(identity), Boolean.TRUE) == null;
    }

    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt) {
        return Identity.endpointAt(occurrence, site, attempt);
    }

    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt,
                                     String siteIndex) {
        return Endpoint.of(occurrence, trimmed(site),
                ExecutionIndex.parse(trimmed(siteIndex)), attempt);
    }

    public static void journalRegion(long vmRegionEnterEventId,
                                     OccurrenceAddress occurrence) {
        Identity.regionKey(vmRegionEnterEventId);
        if (vmRegionEnterEventId > 0L && occurrence != null) {
            PERFORMERS.put(Long.valueOf(vmRegionEnterEventId), occurrence);
        }
    }

    public static OccurrenceAddress occurrenceAt(long vmRegionEnterEventId) {
        return vmRegionEnterEventId <= 0L ? null
                : PERFORMERS.get(Long.valueOf(vmRegionEnterEventId));
    }

    private static final Map<Long, OccurrenceAddress> PERFORMERS =
            new ConcurrentHashMap<Long, OccurrenceAddress>();

    public static void closeSession() {
        SessionPublisher session = publisher;
        if (session == null) return;
        if (Provenance.walked()) {
            EngineConsole.println("Causynth decoded walks: "
                    + Provenance.summary());
        }
        if (SharedStateCapture.readOutsTaken()) {
            EngineConsole.println("Causynth read-outs: "
                    + SharedStateCapture.readOutSummary());
        }
        Map<String, Integer> unnamed = new LinkedHashMap<String, Integer>();
        for (Map.Entry<String, AtomicInteger> entry : UNNAMED.entrySet()) {
            unnamed.put(entry.getKey(), entry.getValue().get());
        }
        Set<String> serving = new TreeSet<String>();
        for (String start : Identity.servingTasks()) {
            serving.add(ActivationRow.CLAIMED + start);
        }
        session.atClose(unnamed, CONCRETE, DERIVED, RunNames.stated(),
                DOORS_ONLY, serving, RuntimeTraceContext.clientNodes());
        unattributedStores();
        for (Map.Entry<String, String> unplanted
                : FocusedReplay.unplantedAssignments().entrySet()) {
            gap(GapKind.ASSIGNMENT_UNPLANTED, GapClass.BLOCKING,
                    firstNonBlank(unplanted.getKey(), sessionId()),
                    "the obligation assigns this root \"" + unplanted
                            .getValue() + "\" and no mint of this replay"
                            + " planted it");
        }
        for (String shortfall : FocusedReplay.shortfalls()) {
            gap(GapKind.SESSION_INCOMPLETE, GapClass.BLOCKING,
                    sessionId(), shortfall);
        }
        for (String mismatch : Confirmation.close()) {
            gap(GapKind.CONFIRM_MISMATCH, GapClass.DIAGNOSTIC,
                    mismatch.substring(0, mismatch.indexOf(':')), mismatch);
        }
        for (String observed : Confirmation.observed()) {
            gap(GapKind.ORDER_OBSERVED, GapClass.DIAGNOSTIC,
                    observed.substring(0, observed.indexOf(':')), observed);
        }
        String unreached = FocusedReplay.forcing() ? ForcedArms.unreached()
                : "";
        if (!unreached.isEmpty()) FocusedReplay.decideForced(unreached);
        List<ObligationResult> results =
                FocusedReplay.results(sessionId());
        for (ObligationResult result : results) {
            session.obligationResult(result);
        }
        String worker = FocusedReplay.workerDir();
        if (FocusedReplay.unsettled() && !worker.isEmpty()) {
            try {
                Files.deleteIfExists(Paths.get(worker,
                        ObligationDir.QUESTION_ASKED));
            } catch (IOException undeleted) {
                EngineConsole.println("Causynth could not withdraw the question"
                        + " this unsettled replay asked: " + undeleted);
            }
        }
        if (FocusedReplay.refusedAt().isEmpty() || worker.isEmpty()) {
            session.close();
            writeWorkerVerdicts(worker, results);
            return;
        }
        String unmoved = session.withdrawTo(
                Paths.get(worker, REFUSED_SESSIONS));
        if (!unmoved.isEmpty()) {
            EngineConsole.println("Causynth could not withdraw the session of"
                    + " this decided replay to " + worker + "/"
                    + REFUSED_SESSIONS + " (" + unmoved + "); its worker"
                    + " withdraws what is still listed");
        }
        writeWorkerVerdicts(worker, FocusedReplay.results(""));
    }

    static final String REFUSED_SESSIONS = "refused-sessions";

    private static void writeWorkerVerdicts(String worker,
                                            List<ObligationResult> results) {
        if (results.isEmpty() || worker.isEmpty()) return;
        StringBuilder rows = new StringBuilder();
        for (ObligationResult result : results) {
            rows.append(RowCodec.toLine(
                    RowCodec.writeObligationResult(result))).append('\n');
        }
        ConcolicVmBroker.asEngineWork(() -> {
            Path statement = Paths.get(worker, ObligationDir.REPLAY_VERDICT);
            Path part = Paths.get(worker,
                    ObligationDir.REPLAY_VERDICT + ".part");
            try {
                Files.write(part, rows.toString().getBytes(
                        StandardCharsets.UTF_8));
                Files.move(part, statement,
                        StandardCopyOption.ATOMIC_MOVE);
            } catch (IOException unwritable) {
                EngineConsole.println("Causynth could not write the replay's"
                        + " obligation verdict: " + unwritable);
            }
        });
    }
}
