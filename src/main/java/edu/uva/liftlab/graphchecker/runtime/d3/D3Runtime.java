package edu.uva.liftlab.graphchecker.runtime.d3;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
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
import java.util.List;
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
    /** The causal context and execution index of each live activation. */
    private static final Map<Long, CausalContext> CONTEXTS =
            new ConcurrentHashMap<Long, CausalContext>();
    private static final Map<Long, ExecutionIndex> INDEXES =
            new ConcurrentHashMap<Long, ExecutionIndex>();
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
        CausalContext context = Identity.context(Lineage.anchor(),
                Lineage.rpcSite(), Lineage.rootRole(),
                Lineage.rootWindowIndex());
        ExecutionIndex index = Identity.regionEnter();
        OccurrenceAddress address = OccurrenceMinterV2.mint(nodeKey,
                regionId, context, index);
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
        if (token > 0L) {
            CONTEXTS.put(token, context);
            INDEXES.put(token, index);
        }
        if (session != null) {
            session.activation(ActivationRow.of(sessionId(), address,
                    Text.safe(taskId), FocusedReplay.focused(taskId,
                            address), true, threadKey(), null));
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

    /**
     * States one activation that no plan selected.
     *
     * <p>Every activation of every region publishes a row, focused or not:
     * the explorer reads "this occurrence ran, and these are its decisions"
     * from the rows, so an activation with no row silently downgrades an
     * arm that rests on it.  Once per occurrence per session -- an ambient
     * occurrence publishes at its first delivery, not at every leaf.</p>
     */
    public static void ambientActivation(OccurrenceAddress address) {
        SessionPublisher session = publisher;
        if (session == null || address == null) return;
        if (AMBIENT.putIfAbsent(address.id(), Boolean.TRUE) != null) return;
        // A lightweight entry hook published this one: the region is not in
        // the instrumented set, so it has no decisions to find.
        session.activation(ActivationRow.of(sessionId(), address, "", false,
                false, threadKey(), null));
    }

    private static final Map<String, Boolean> AMBIENT =
            new ConcurrentHashMap<String, Boolean>();

    /**
     * The session's key for the thread this activation runs on.
     *
     * <p>Name plus JVM thread id: the name alone repeats across a pool, and
     * the id alone says nothing to a reader.  Stable for the life of the
     * session, which is all program order needs.</p>
     */
    private static String threadKey() {
        Thread thread = Thread.currentThread();
        return thread.getName() + "#" + thread.getId();
    }

    /** The address minted for this activation, or {@code null}. */
    public static OccurrenceAddress addressOf(long token) {
        return ACTIVATIONS.get(token);
    }

    public static void endActivation(long token) {
        ACTIVATIONS.remove(token);
        CONTEXTS.remove(token);
        INDEXES.remove(token);
    }

    /** The causal context this activation entered under, or null. */
    public static CausalContext contextOf(long token) {
        return CONTEXTS.get(token);
    }

    /** The execution index of this activation's entry, or null. */
    public static ExecutionIndex indexOf(long token) {
        return INDEXES.get(token);
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
            // Polarity-free: the row states the predicate and the arm,
            // and the composer conjoins (outcome ? term : (not term)).
            session.decision(DecisionRow.of(sessionId(), sequence(seq),
                    occurrence, Text.safe(siteId), ordinal, outcome, ref,
                    clockReadings()));
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

    /**
     * The endpoint of one work submission.
     *
     * <p>A batch submits several tasks from one point of one activation --
     * {@code invokeAll} with three subtasks -- and the started work is
     * addressed by the endpoint that started it, so those submissions may
     * not share an endpoint.  The k-th submission made at one point is the
     * k-th, in the order the run makes them, which a replay of the same
     * prefix makes in the same order.</p>
     */
    public static Endpoint submission(OccurrenceAddress from) {
        if (from == null) return null;
        Endpoint at = endpoint(from, "SUBMIT", 0);
        if (at == null) return null;
        AtomicInteger made = SUBMISSIONS.get(at.id());
        if (made == null) {
            AtomicInteger fresh = new AtomicInteger();
            made = SUBMISSIONS.putIfAbsent(at.id(), fresh);
            if (made == null) made = fresh;
        }
        return endpoint(from, "SUBMIT#" + made.getAndIncrement(), 0);
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
     * Files the endpoint of one message, for the anchor its receiver states.
     *
     * <p>The site is the transport leg itself, so a message that carries no
     * declared port still names its producer -- which is what a causal
     * context needs (IDENTITY-V3 §1).</p>
     */
    public static void sending(OccurrenceAddress sender, String transport,
                               String correlationId, String half) {
        if (sender == null) return;
        Endpoint endpoint = endpoint(sender, transport + "#" + half, 0);
        Interactions.sent(transport, correlationId, half, endpoint.id());
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

    /**
     * One write, at the site index the event itself stood on.
     *
     * <p>{@code siteIndex} is the rendered execution index of the frames the
     * writing thread stood on WHEN the write ran, not where the row is
     * published: the write log is read out at the end of the activation, by
     * which point the thread has returned to the region entry.  The frames
     * come from that activation's {@link FrameJournal}, aligned to the
     * version's own event id.  An empty index is an event the run could not
     * place, and the caller names that gap -- nothing here fabricates one.</p>
     */
    public static void write(OccurrenceAddress occurrence, long seq,
                             String site, LocationId location, long version,
                             JsonObject expression, String javaType,
                             String siteIndex) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) return;
        Endpoint at = endpoint(occurrence, site, 0, siteIndex);
        distinct(at, "write#" + location + "#" + version);
        session.write(WriteRow.of(sessionId(), sequence(seq), at, location,
                version, expressionRef(expression),
                javaType(javaType, expression)));
    }

    /** One read, at the site index the event itself stood on. */
    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue,
                            String siteIndex) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) return;
        Endpoint at = endpoint(occurrence, site, 0, siteIndex);
        distinct(at, "read#" + location + "#" + seq);
        session.read(ReadRow.of(sessionId(), sequence(seq), at, location,
                observedVersion, Text.safe(symbol), javaType(javaType, null),
                Text.safe(concreteValue).isEmpty() ? null
                        : Text.safe(concreteValue)));
    }

    /**
     * Names two events of one site that one occurrence cannot tell apart.
     *
     * <p>An endpoint is {@code (occurrence, site, siteIndex, attempt)}.  Two
     * events of one site whose frames are identical are two events of the
     * same site in the same call path at the same loop iteration -- a genuine
     * repeat inside one iteration, e.g. a field read twice in one basic
     * block.  The identity states so rather than separating them by a
     * counter: an ordinal moves when an unrelated earlier event is inserted,
     * which is exactly what a branch flip does, and two replays would then
     * disagree about which event is which (IDENTITY-V3 sec 1).</p>
     */
    private static void distinct(Endpoint at, String event) {
        if (at == null) return;
        String first = ENDPOINTS.putIfAbsent(at.id(), Text.safe(event));
        if (first == null || first.equals(Text.safe(event))) return;
        gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, at.render(),
                "two events of this site inside one occurrence stand on the"
                        + " same frames, so the site index cannot"
                        + " distinguish them: " + first + " and " + event);
    }

    /** The first event each read/write endpoint id was minted for. */
    private static final Map<String, String> ENDPOINTS =
            new ConcurrentHashMap<String, String>();

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
        // One statement, stated once: the same refusal is reached from every
        // activation that met it, and a reader counts named gaps.
        if (!claimEvent("gap", kind + "#" + cls + "#" + Text.safe(subject)
                + "#" + Text.safe(detail))) {
            return;
        }
        session.gap(GapRow.of(sessionId(), kind, cls, Text.safe(subject),
                Text.safe(detail)));
    }

    /** The symbols this session minted at declared region inputs. */
    private static final Map<String, Boolean> PLACEHOLDERS =
            new ConcurrentHashMap<String, Boolean>();

    /**
     * Records that one symbol is a read placeholder, session-wide.
     *
     * <p>The mint happens in the innermost activation, and every activation
     * it runs inside sees the same field shadow afterwards.  The write log
     * of an OUTER activation therefore offers the mint's version as a write
     * of that location, and only a session-wide answer suppresses it: the
     * per-activation one let hdfs-17960's version 173 through on
     * {@code REGION.f167c8f6}.</p>
     */
    public static void placeholderSymbol(String symbol) {
        PLACEHOLDERS.put(Text.safe(symbol), Boolean.TRUE);
    }

    /** Whether one symbol is a read placeholder this session minted. */
    public static boolean isPlaceholderSymbol(String symbol) {
        return PLACEHOLDERS.containsKey(Text.safe(symbol));
    }

    /** Enters one frame of the execution index: a woven control site. */
    public static void enterFrame(String callSiteId) {
        Identity.enterCall(callSiteId);
    }

    /** Leaves the innermost frame. */
    public static void exitFrame() {
        Identity.exitCall();
    }

    /**
     * This thread, as a key stable inside one session.
     *
     * <p>Same-thread program order is a happens-before input (R-I7.1), and
     * two rows are on one thread iff they carry one key.  The name alone is
     * not stable -- Hadoop renames DataXceiver threads per op -- so the JVM
     * thread id is the key and the name travels with it for a reader.</p>
     */

    /** The submission endpoint this thread inherited its frame from. */
    private static Endpoint startedBy() {
        String id = Lineage.startedBy();
        if (id.isEmpty()) return null;
        Endpoint known = STARTERS.get(id);
        return known;
    }

    /** Endpoints that started work elsewhere, by id, for startedBy. */
    private static final Map<String, Endpoint> STARTERS =
            new ConcurrentHashMap<String, Endpoint>();

    /** Remembers one submission endpoint so a child row can name it. */
    public static void starting(Endpoint submission) {
        if (submission != null) STARTERS.put(submission.id(), submission);
    }

    /** Charges one loop iteration to the running execution index. */
    public static void loopIteration(String loopId) {
        Identity.loopIteration(loopId);
    }

    /** Files one expression and returns the ref rows name it by. */
    public static String expressionRef(JsonElement expression) {
        if (expression == null || expression.isJsonNull()
                || !expression.isJsonObject()) {
            return "";
        }
        JsonObject object = expression.getAsJsonObject();
        // One serialization per expression, not per row that names it.  A
        // container's expression on hdfs-17960 is hundreds of nodes deep
        // and every write of that location publishes the same tree; the
        // replay spent longer serializing them again than running the
        // workload.
        String ref = REFS.get(object);
        if (ref == null) {
            ref = "EXPR." + Text.sha16(RowCodec.toLine(object));
            REFS.put(object, ref);
        }
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
     * The JVM descriptor a row states: the declaration where there is one,
     * and otherwise the type the expression the VM published states.
     *
     * <p>An operator node states no type of its own -- the VM's
     * {@code BinaryExpression} carries only its operands -- so the type of
     * {@code Y_I_0 + Y_I_1} is read off the operands, which say {@code I}.
     * The alternative was the unstated fallback, and the snapshot counter's
     * RMW versions went out as {@code Ljava/lang/Object;} while the run knew
     * they were ints (REPORT-P2CD follow-up).  Depth-first in the tree's own
     * member order, so one tree always answers the same type.</p>
     */
    private static String javaType(String declared, JsonObject expression) {
        String type = Text.safe(declared);
        if (!type.isEmpty()) return type;
        String stated = statedType(expression, 0);
        if (!stated.isEmpty()) return stated;
        // Never blank: the contract refuses one, and "the type was not
        // stated" is a fact about the row, not an absence of a member.
        return "Ljava/lang/Object;";
    }

    private static String statedType(JsonElement node, int depth) {
        if (node == null || depth > 64 || !node.isJsonObject()) return "";
        JsonObject object = node.getAsJsonObject();
        JsonElement own = object.get("_java_type");
        if (own != null && own.isJsonPrimitive()) {
            String stated = Text.safe(own.getAsString());
            if (!stated.isEmpty()) return stated;
        }
        for (java.util.Map.Entry<String, JsonElement> member
                : object.entrySet()) {
            String found = statedType(member.getValue(), depth + 1);
            if (!found.isEmpty()) return found;
        }
        return "";
    }

    private static Long longOrNull(String value) {
        try {
            return Long.valueOf(Text.safe(value));
        } catch (NumberFormatException notALong) {
            return null;
        }
    }

    /** Expression refs already computed, by the tree they name. */
    private static final Map<JsonObject, String> REFS =
            java.util.Collections.synchronizedMap(
                    new java.util.IdentityHashMap<JsonObject, String>());

    /** Read events already stated, so one read is one occurrence's. */
    private static final Map<String, Boolean> CLAIMED_READS =
            new ConcurrentHashMap<String, Boolean>();

    /**
     * Claims one read event for the activation publishing it now.
     *
     * <p>A value read once is carried by the expression of everything
     * built from it, so the same read node is reachable from several
     * activations' trees.  It happened in one of them: the first to
     * publish it, which is the innermost, since an activation finishes
     * before the one it runs inside.</p>
     */
    public static boolean claimRead(String identity) {
        return claimEvent("read", identity);
    }

    /**
     * The same rule for every row kind: one event, one occurrence.
     *
     * <p>The VM's branch, write and read logs are read out per activation
     * over overlapping event ranges, so one event is reachable from every
     * activation it ran inside -- on hdfs-17960 each of the 53 write events
     * was published by up to 42 occurrences.  A row per reachable
     * activation states one event many times and, worse, attributes it to
     * occurrences that did not perform it, which is exactly the identity a
     * STATE family is keyed on (INTERACTION-ID R-I7.1).  The first
     * publisher wins and that is the innermost, since an activation
     * finishes before the one it runs inside.</p>
     */
    public static boolean claimEvent(String kind, String identity) {
        return CLAIMED_READS.put(Text.safe(kind) + "\n"
                + Text.safe(identity), Boolean.TRUE) == null;
    }

    /** Submissions already made at one point, by base endpoint id. */
    private static final ConcurrentHashMap<String, AtomicInteger> SUBMISSIONS =
            new ConcurrentHashMap<String, AtomicInteger>();

    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt) {
        return Endpoint.of(occurrence, Text.safe(site), Identity.siteIndex(),
                attempt);
    }

    /**
     * The endpoint of an event whose site index was captured earlier.
     *
     * <p>Every endpoint the runtime mints AT its site takes the live index;
     * an event the VM logged and the runtime publishes afterwards takes the
     * index the journal states for it.  An index that was not stated is
     * empty, never the live one: the publishing thread's frames are not the
     * frames of an event some other activation performed.</p>
     */
    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt,
                                     String siteIndex) {
        return Endpoint.of(occurrence, Text.safe(site),
                ExecutionIndex.parse(Text.safe(siteIndex)), attempt);
    }

    /** The frames from the region entry to the site running right now. */
    public static String siteIndexHere() {
        return Identity.siteIndex().render();
    }

    /**
     * Files this activation's frame journal under the VM's own key.
     *
     * <p>Called once the engine has stated the region-enter event id, which
     * is what every version and read it logs from inside this activation
     * carries.  Until then the activation journals nothing: an entry with no
     * key could not be found again.</p>
     */
    public static void journalRegion(long vmRegionEnterEventId) {
        Identity.regionKey(vmRegionEnterEventId);
    }

    /** Leaves the innermost region of the execution index. */
    public static void exitRegionIndex() {
        Identity.regionExit();
    }

    /** Installs the VM's event clock the frame journal samples. */
    public static void clock(FrameJournal.Clock source) {
        Identity.clock(source);
    }

    /**
     * The rendered site index of one event the VM logged, or null.
     *
     * <p>{@code activationKey} is the {@code regionEnterEventId} the logged
     * event states and {@code eventId} its version id or read event id; both
     * are the VM's own statements, and the frames are the journal's
     * (FrameJournal).</p>
     *
     * <p>Null is an event this run cannot place; {@code ""} is an event the
     * journal DID place on no frames at all, which is where most stores are
     * -- the region's own method, with no woven call between its entry and
     * the store.  The two are different answers and the row would read the
     * same for both, so the caller gets to tell them apart: an index that is
     * empty because the event stood at the region entry is stated, and only
     * an unplaced event is a gap.</p>
     */
    public static String framesOf(long activationKey, long eventId) {
        ExecutionIndex index = FrameJournal.framesAt(activationKey, eventId);
        return index == null ? null : index.render();
    }

    /**
     * Publishes what only the end of a replay can state, and closes.
     *
     * <p>The verdict goes twice: into the session, which is the evidence,
     * and into the worker's own {@code obligation_result.jsonl}, which is
     * what the wave reads.  The replay owns the verdict -- whether the
     * focused prefix reproduced and the flipped decision was taken is a
     * fact of the run, not of the solve that proposed it.</p>
     */
    public static void closeSession() {
        SessionPublisher session = publisher;
        if (session == null) return;
        List<ObligationResult> results =
                FocusedReplay.results(sessionId());
        for (ObligationResult result : results) {
            session.obligationResult(result);
        }
        writeWorkerVerdicts(results);
        session.close();
    }

    /** The wave's own file: one row per obligation this replay ran. */
    private static void writeWorkerVerdicts(List<ObligationResult> results) {
        if (results.isEmpty()) return;
        String worker = Text.safe(System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
        if (worker.isEmpty()) return;
        StringBuilder rows = new StringBuilder();
        for (ObligationResult result : results) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", "OBLIGATION_RESULT");
            row.addProperty("obligationId", result.obligationId());
            row.addProperty("verdict", result.verdict().name());
            row.addProperty("sessionId", result.sessionId());
            row.addProperty("detail", result.detail());
            rows.append(RowCodec.toLine(row)).append('\n');
        }
        try {
            java.nio.file.Files.write(
                    java.nio.file.Paths.get(worker,
                            "obligation_result.jsonl"),
                    rows.toString().getBytes(
                            java.nio.charset.StandardCharsets.UTF_8));
        } catch (java.io.IOException unwritable) {
            System.err.println("Causynth could not write the replay's"
                    + " obligation verdict: " + unwritable);
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            ACTIVATIONS.clear();
            AMBIENT.clear();
            STARTERS.clear();
            CONTEXTS.clear();
            INDEXES.clear();
            ORDINALS.clear();
            CLAIMED_READS.clear();
            PLACEHOLDERS.clear();
            REFS.clear();
            SUBMISSIONS.clear();
            Identity.resetForTests();
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
