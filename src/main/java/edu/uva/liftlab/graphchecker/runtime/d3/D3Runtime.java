package edu.uva.liftlab.graphchecker.runtime.d3;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.LocationId;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.SessionDir;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;
import java.lang.management.ManagementFactory;
import java.nio.file.Path;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * The one door between the replay and the Design 3 row set.
 *
 * <p>Every call is total and silent about its own bookkeeping: the rows
 * describe a workload run, and a publisher that threw into the workload
 * would change the execution it is describing.  What it never does is stay
 * silent about the RUN -- a site that ran and could not be addressed files a
 * gap, which is why {@link #gap} sits beside every other method here.</p>
 */
public final class D3Runtime {
    /** Where the wave names this replay's session, when it does. */
    public static final String SESSION_PROPERTY = "causynth.d3.session";
    /** Where the campaign's REPLAY stage puts every worker's session. */
    public static final String SESSIONS_PROPERTY = "causynth.d3.sessions";

    private static final Object LOCK = new Object();
    private static final Map<Long, OccurrenceAddress> ACTIVATIONS =
            new ConcurrentHashMap<Long, OccurrenceAddress>();
    private static final Map<String, AtomicInteger> ORDINALS =
            new ConcurrentHashMap<String, AtomicInteger>();
    /** This replay's clock readings so far, by root id. */
    private static final Map<String, Long> CLOCKS =
            new ConcurrentHashMap<String, Long>();
    /**
     * The highest VM event id this session has published.
     *
     * <p>{@code seq} is ONE counter for every row kind -- the VM's own
     * session-global event id, which the decisions' {@code vmEventId} and
     * the write log's {@code fieldVersionId} are both drawn from -- because
     * the composer compares a decision's seq against an export's directly.
     * Never a per-kind ordinal.</p>
     */
    private static final java.util.concurrent.atomic.AtomicLong LAST_SEQ =
            new java.util.concurrent.atomic.AtomicLong();
    private static volatile SessionPublisher publisher;
    private static volatile String sessionId = "";

    private D3Runtime() {
    }

    /**
     * Opens this JVM's session beside the result file the campaign named.
     *
     * <p>The session directory is the contract's {@code
     * <iteration>/sessions/<sessionId>/}; the id is the wave's when the wave
     * stated one, and otherwise this run's own, so two replays of one
     * iteration never write into each other's rows.</p>
     */
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
    }

    /** Whether a session is open to publish into. */
    public static boolean open() {
        return publisher != null;
    }

    public static String sessionId() {
        return sessionId;
    }

    public static SessionPublisher publisher() {
        return publisher;
    }

    /**
     * The sessions directory the campaign named, or null.
     *
     * <p>{@code CAUSYNTH_CONCOLIC_SESSIONS} is what REPLAY passes every
     * worker; deriving it from the result file is the fallback for a run
     * nothing told.</p>
     */
    private static Path declaredSessionsRoot() {
        String declared = Text.safe(System.getProperty(SESSIONS_PROPERTY));
        if (declared.isEmpty()) {
            declared = Text.safe(System.getenv("CAUSYNTH_CONCOLIC_SESSIONS"));
        }
        return declared.isEmpty() ? null
                : java.nio.file.Paths.get(declared).toAbsolutePath();
    }

    /** The iteration directory a campaign path belongs to. */
    public static Path iterationOf(Path inside) {
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
        String declared = Text.safe(System.getProperty(SESSION_PROPERTY));
        if (!declared.isEmpty()) return declared;
        Path parent = resultFile.toAbsolutePath().getParent();
        String where = parent == null || parent.getFileName() == null
                ? "session" : parent.getFileName().toString();
        return where + "-" + Text.sha16(resultFile.toAbsolutePath() + "\n"
                + ManagementFactory.getRuntimeMXBean().getName() + "\n"
                + System.nanoTime()).substring(0, 8);
    }

    // ------------------------------------------------------------------
    // Activations
    // ------------------------------------------------------------------

    /**
     * Mints and publishes the v2 address of one activation.
     *
     * @return the address, or {@code null} when this run can name no node
     */
    public static OccurrenceAddress beginActivation(long token,
                                                    String nodeKey,
                                                    String regionId,
                                                    String taskId) {
        OccurrenceAddress address =
                OccurrenceMinterV2.mint(nodeKey, regionId);
        SessionPublisher session = publisher;
        if (address == null) {
            if (session != null) {
                session.gap(GapRow.of(sessionId(), GapKind.LINEAGE_LOST,
                        GapClass.DIAGNOSTIC, Text.safe(regionId),
                        "an activation of this region ran on a node this run"
                                + " could not name, so it has no address"));
            }
            return null;
        }
        if (token > 0L) ACTIVATIONS.put(token, address);
        if (session != null) {
            session.activation(ActivationRow.of(sessionId(), address,
                    Text.safe(taskId), FocusedReplay.focused(address)));
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

    /** The address minted for this activation, or {@code null}. */
    public static OccurrenceAddress addressOf(long token) {
        return ACTIVATIONS.get(token);
    }

    public static void endActivation(long token) {
        ACTIVATIONS.remove(token);
    }

    // ------------------------------------------------------------------
    // Rows
    // ------------------------------------------------------------------

    /** One decision, its term in the polarity it was taken. */
    public static void decision(OccurrenceAddress occurrence, long seq,
                                String siteId, int ordinal, boolean outcome,
                                JsonObject condition) {
        if (occurrence == null) return;
        SessionPublisher session = publisher;
        if (session != null) {
            String ref = expressionRef(condition);
            session.decision(DecisionRow.of(sessionId(), sequence(seq),
                    occurrence, Text.safe(siteId), ordinal, outcome,
                    term(ref, outcome), clockReadings()));
        }
        FocusedReplay.observeDecision(occurrence, siteId, ordinal, outcome);
    }

    /**
     * The term a row states for one arm of one condition.
     *
     * <p>The runtime does not lower to SMT -- one lowering exists and it is
     * the composer's -- so the term names the expression the condition is,
     * in the polarity the arm took.  {@code (not ref)} and {@code ref} are
     * the two arms of the same condition and nothing downstream has to
     * re-derive which is which.</p>
     */
    static String term(String expressionRef, boolean arm) {
        String ref = Text.safe(expressionRef);
        if (ref.isEmpty()) return "";
        return arm ? ref : "(not " + ref + ")";
    }

    /** One export, and the producer endpoint a delivery can be paired to. */
    public static Endpoint exported(OccurrenceAddress producer, long seq,
                                    String portId, long handle,
                                    String correlationId, int attempt,
                                    JsonObject expression, String javaType,
                                    String recordedValue) {
        if (producer == null) return null;
        Endpoint endpoint = endpoint(producer, portId, attempt);
        String ref = expressionRef(expression);
        Interactions.exported(portId, handle, correlationId, endpoint, ref);
        SessionPublisher session = publisher;
        if (session != null) {
            session.export(ExportRow.of(sessionId(), sequence(seq), endpoint,
                    ref, javaType(javaType, expression), handle,
                    Text.safe(recordedValue)));
        }
        FocusedReplay.observeInteraction(endpoint.id());
        return endpoint;
    }

    /**
     * The endpoint of the next event of one site in one occurrence.
     *
     * <p>Allocated before the mint where the mint needs its id -- an
     * obligation answers an attach BY endpoint, so the endpoint has to
     * exist before the value is written.</p>
     */
    public static Endpoint nextEndpoint(OccurrenceAddress occurrence,
                                        String site, int attempt) {
        return occurrence == null ? null : endpoint(occurrence, site,
                attempt);
    }

    /** One v_H minted at an endpoint already allocated. */
    public static Endpoint attachedAt(Endpoint endpoint, long seq,
                                      String portId, long handle,
                                      String correlationId, String symbol,
                                      String javaType, String arrival,
                                      boolean answered,
                                      String answeredValue) {
        if (endpoint == null) return null;
        Endpoint producer = Interactions.producer(portId, handle,
                correlationId);
        SessionPublisher session = publisher;
        if (session != null) {
            session.attach(AttachRow.of(sessionId(), sequence(seq), endpoint,
                    Text.safe(symbol), javaType(javaType, null),
                    Text.safe(arrival), answered,
                    answered ? Text.safe(answeredValue) : null, producer,
                    Text.safe(correlationId)));
            if (producer == null) {
                session.gap(GapRow.of(sessionId(), GapKind.LINEAGE_LOST,
                        GapClass.DIAGNOSTIC, endpoint.id(),
                        "the delivery at " + Text.safe(portId)
                                + " was paired with no export of this run"));
            }
        }
        FocusedReplay.observeInteraction(endpoint.id());
        return endpoint;
    }

    /** One v_H minted at a declared port, paired to its producer. */
    public static Endpoint attached(OccurrenceAddress consumer, long seq,
                                    String portId, long handle,
                                    String correlationId, int attempt,
                                    String symbol, String javaType,
                                    String arrival, boolean answered,
                                    String answeredValue) {
        if (consumer == null) return null;
        return attachedAt(endpoint(consumer, portId, attempt), seq, portId,
                handle, correlationId, symbol, javaType, arrival, answered,
                answeredValue);
    }

    /**
     * The address of an activation that ran under no live occurrence: its
     * role, on its node, at a window-local k.
     *
     * <p>REPORT-ENTRY: the OUT side already exported unconditionally and
     * said {@code UNPLANNED} of itself.  It now says which role, on which
     * node, at which k -- a degraded endpoint, which is still an endpoint an
     * arm can be keyed by (INTERACTION-ID R-I1).</p>
     */
    public static OccurrenceAddress degraded(String nodeKey, String site) {
        Role role = Lineage.named() ? Lineage.role() : Role.UNKNOWN;
        return OccurrenceMinterV2.degraded(nodeKey, role, site);
    }

    public static void write(OccurrenceAddress occurrence, long seq,
                             String site, LocationId location, long version,
                             JsonObject expression, String javaType) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) return;
        session.write(WriteRow.of(sessionId(), sequence(seq),
                endpoint(occurrence, site, 0), location, version,
                expressionRef(expression), javaType(javaType, expression)));
    }

    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) return;
        session.read(ReadRow.of(sessionId(), sequence(seq),
                endpoint(occurrence, site, 0), location, observedVersion,
                Text.safe(symbol), javaType(javaType, null),
                Text.safe(concreteValue).isEmpty() ? null
                        : Text.safe(concreteValue)));
    }

    /** One root minted, with its kind and the domain it resolved to. */
    public static void rootMint(OccurrenceAddress occurrence, long seq,
                                String rootId, String symbol, RootKind kind,
                                String recordedValue, String domainMin,
                                String domainMax, boolean declared) {
        if (kind == RootKind.CLOCK) {
            Long reading = longOrNull(recordedValue);
            if (reading != null) CLOCKS.put(Text.safe(rootId), reading);
        }
        SessionPublisher session = publisher;
        if (session == null || occurrence == null) return;
        session.rootMint(RootMintRow.of(sessionId(), sequence(seq),
                occurrence,
                Text.safe(rootId), Text.safe(symbol),
                kind == null ? RootKind.INTEGRAL : kind,
                Text.safe(recordedValue),
                Text.safe(domainMin).isEmpty() ? null : Text.safe(domainMin),
                Text.safe(domainMax).isEmpty() ? null : Text.safe(domainMax),
                declared));
    }

    /** The anchor, with phi stated in the FATAL polarity as published. */
    public static void target(OccurrenceAddress occurrence, long seq,
                              String anchorSiteId, JsonObject condition,
                              boolean fatalArm, boolean observedFatal,
                              boolean reachedAnchor) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null) return;
        session.target(TargetRow.of(sessionId(), sequence(seq), occurrence,
                Text.safe(anchorSiteId),
                term(expressionRef(condition), fatalArm), observedFatal,
                reachedAnchor));
    }

    public static void gap(GapKind kind, GapClass cls, String subject,
                           String detail) {
        SessionPublisher session = publisher;
        if (session == null) return;
        session.gap(GapRow.of(sessionId(), kind, cls, Text.safe(subject),
                Text.safe(detail)));
    }

    /** Files one expression and returns the ref rows name it by. */
    public static String expressionRef(JsonElement expression) {
        if (expression == null || expression.isJsonNull()
                || !expression.isJsonObject()) {
            return "";
        }
        JsonObject object = expression.getAsJsonObject();
        String ref = "EXPR." + Text.sha16(RowCodec.toLine(object));
        SessionPublisher session = publisher;
        if (session != null) session.expression(ref, object);
        return ref;
    }

    /** What every clock this replay minted read, for the decisions' rows. */
    public static Map<String, Long> clockReadings() {
        return new java.util.LinkedHashMap<String, Long>(CLOCKS);
    }

    /**
     * Where one row sits in the run: the VM's own event id.
     *
     * <p>One counter for every kind, so a producer's prefix can be cut at
     * its export and a read ordered against the write it saw.  The VM's
     * ledger is that counter -- decisions carry its event id, versions are
     * drawn from it -- so a row states the id it was produced at rather
     * than a second numbering of the same events.  A row the VM gave no id
     * states 0, which says "this row carries no VM clock" and never
     * pretends to an order it does not have.</p>
     */
    private static long sequence(long vmEventId) {
        if (vmEventId > 0L) {
            long seen = LAST_SEQ.get();
            while (vmEventId > seen
                    && !LAST_SEQ.compareAndSet(seen, vmEventId)) {
                seen = LAST_SEQ.get();
            }
            return vmEventId;
        }
        // The VM gave this row no id of its own -- an ambient mint, an
        // export the ledger did not number.  It is not earlier than
        // anything already seen, and saying 0 would place it before the
        // whole run.  A comparison against it is then "no earlier than",
        // which is the strongest true statement available.
        return LAST_SEQ.get();
    }

    /**
     * The JVM descriptor a row states, from the declaration where there is
     * one and from the expression the VM published otherwise.
     */
    private static String javaType(String declared, JsonObject expression) {
        String type = Text.safe(declared);
        if (!type.isEmpty()) return type;
        if (expression != null && expression.has("_java_type")) {
            String published =
                    Text.safe(expression.get("_java_type").getAsString());
            if (!published.isEmpty()) return published;
        }
        // Never blank: the contract refuses one, and "the type was not
        // stated" is a fact about the row, not an absence of a member.
        return "Ljava/lang/Object;";
    }

    private static Long longOrNull(String value) {
        try {
            return Long.valueOf(Text.safe(value));
        } catch (NumberFormatException notALong) {
            return null;
        }
    }

    /** The k-th event of one site inside one occurrence. */
    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt) {
        String scope = occurrence.render() + "\n" + Text.safe(site);
        AtomicInteger counter = ORDINALS.get(scope);
        if (counter == null) {
            AtomicInteger fresh = new AtomicInteger();
            AtomicInteger raced = ORDINALS.putIfAbsent(scope, fresh);
            counter = raced == null ? fresh : raced;
        }
        return Endpoint.of(occurrence, Text.safe(site),
                counter.incrementAndGet(), attempt);
    }

    /** Publishes what only the end of a replay can state, and closes. */
    public static void closeSession() {
        SessionPublisher session = publisher;
        if (session == null) return;
        for (ObligationResult result : FocusedReplay.results(sessionId())) {
            session.obligationResult(result);
        }
        session.close();
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            ACTIVATIONS.clear();
            ORDINALS.clear();
            CLOCKS.clear();
            LAST_SEQ.set(0L);
            publisher = null;
            sessionId = "";
            OccurrenceMinterV2.resetForTests();
            Interactions.resetForTests();
            Lineage.resetForTests();
            FocusedReplay.resetForTests();
            SessionPublisher.resetForTests();
        }
    }
}
