package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.smt.Arms;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import java.lang.management.ManagementFactory;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The one door between the replay and the row set.
 *
 * <p>Every call is total and silent about its own bookkeeping: the rows
 * describe a workload run, and a publisher that threw into the workload
 * would change the execution it is describing.  What it never does is stay
 * silent about the RUN -- a site that ran and could not be addressed files a
 * gap, which is why {@link #gap} sits beside every other method here.</p>
 */
public final class RowRuntime {
    /** Where the campaign's REPLAY stage puts every worker's session. */
    public static final String SESSIONS_ENV = "CAUSYNTH_CONCOLIC_SESSIONS";

    private static final Object LOCK = new Object();
    /**
     * The clock cells this session has minted, by the VM symbol that names
     * one: its root id and what the mint read.
     *
     * <p>I4 -- A DECISION ROW CARRIES EXACTLY THE CLOCK CELLS ITS TERM
     * NAMES, so this is a lookup from a symbol a term mentions to the cell
     * it is, and never the set of readings a row states.  Keyed by the
     * SYMBOL because that is what an expression tree spells; filed at the
     * MINT, because an activation nested inside the one that minted the
     * clock publishes its own decisions first -- 11741's {@code
     * removeExpiredKeys} closes before the {@code updateKeys} rotation that
     * minted the clock it read.</p>
     */
    private static final Map<String, ClockCell> CLOCK_CELLS =
            new ConcurrentHashMap<String, ClockCell>();

    /** One clock cell: the root a symbol is, and the instant it read. */
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
        // The session's schedule goes where its rows go: the events this
        // run made before the session opened are kept and written first.
        final SessionPublisher opened = publisher;
        ScheduleLog.install(new ScheduleLog.Sink() {
            @Override
            public void write(com.google.gson.JsonObject row) {
                opened.schedule(row);
            }
        });
    }

    /** Whether a session is open to publish into. */
    public static boolean open() {
        return publisher != null;
    }

    public static String sessionId() {
        return sessionId;
    }

    /**
     * The sessions directory the campaign named, or null.
     *
     * <p>{@link #SESSIONS_ENV} is what REPLAY passes every worker, and it is
     * the one spelling; deriving the directory from the result file is what
     * a run nothing told does instead.</p>
     */
    private static Path declaredSessionsRoot() {
        String declared = Text.safe(System.getenv(SESSIONS_ENV));
        return declared.isEmpty() ? null
                : java.nio.file.Paths.get(declared).toAbsolutePath();
    }

    /** The iteration directory a campaign path belongs to. */
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

    /**
     * This session's id: where the campaign put it, and what ran it.
     *
     * <p>Derived and never declared -- a replay that was handed an id it
     * shares with another worker of the same iteration writes into that
     * worker's rows.</p>
     */
    private static String sessionId(Path resultFile) {
        Path parent = resultFile.toAbsolutePath().getParent();
        String where = parent == null || parent.getFileName() == null
                ? "session" : parent.getFileName().toString();
        return where + "-" + ArtifactIO.digest(Text.safe(
                resultFile.toAbsolutePath() + "\n"
                + ManagementFactory.getRuntimeMXBean().getName() + "\n"
                + System.nanoTime()), 8);
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
        // The occurrence this ENTRY already opened
        // (ConcolicRegionRuntime.enterRegionEntry, the one hook every
        // skeleton root carries), not a second opening of the same
        // activation: one entry, one region, one address -- the same one
        // the recorder computed on the stock JDK.
        OccurrenceAddress address = Identity.currentOccurrence(nodeKey);
        SessionPublisher session = publisher;
        if (address == null) {
            if (session != null) {
                gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                        firstNonBlank(Text.safe(regionId), Text.safe(taskId),
                                Long.toString(token)),
                        "an activation of this region ran on a node this run"
                                + " could not name, so it has no address");
            }
            return null;
        }
        if (session != null) {
            // The contract's last member is the deleted intra-node
            // thread-start edge: no producer of it is left in the runtime,
            // and the argument goes with the member (contract owner).
            session.activation(ActivationRow.of(sessionId(), address,
                    Text.safe(taskId), FocusedReplay.focused(taskId,
                            address), true, threadKey()));
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
                false, threadKey()));
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
                    clockReadings(condition)));
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
        return Arms.conjunct(ref, arm);
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
        Interactions.exported(portId, handle, correlationId, endpoint);
        SessionPublisher session = publisher;
        if (session != null) {
            String type = statedJavaType("export", endpoint.id(), javaType,
                    expression);
            if (!type.isEmpty()) {
                session.export(ExportRow.of(sessionId(), sequence(seq),
                        endpoint, ref, type, handle,
                        Text.safe(recordedValue)));
            }
        }
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
        Interactions.Pairing pairing = Interactions.pairing(portId, handle,
                correlationId);
        Endpoint producer = pairing.producer();
        if (producer != null && handle > 0L
                && !"HANDLE".equals(pairing.key())) {
            // The strongest evidence this delivery carried did not answer,
            // and the pairing rests on the message it travelled in.  The
            // class is every attach that states a handle and is paired by
            // correlation+port: the producer named here is the one that sent
            // the MESSAGE, not the one that staged this value.
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, endpoint.id(),
                    "this delivery states VM handle " + handle
                            + " and was paired by " + pairing.key()
                            + ", so the producer is the message's and not"
                            + " the staged expression's");
        }
        SessionPublisher session = publisher;
        if (session != null) {
            String type = statedJavaType("attach", endpoint.id(), javaType,
                    null);
            if (!type.isEmpty()) {
                // The row states WHICH key answered, so a reader does not
                // have to re-derive it from the handle and the correlation
                // and get "both were available" for an answer.  Blank when
                // neither paired, which Fields.optional reads as unstated:
                // the unpaired case is already stated by a null producer and
                // the LINEAGE_LOST row below.
                session.attach(AttachRow.of(sessionId(), sequence(seq),
                        endpoint, Text.safe(symbol), type,
                        Text.safe(arrival), answered,
                        answered ? Text.safe(answeredValue) : null, producer,
                        Text.safe(correlationId), pairing.key()));
            }
            if (producer == null) {
                session.gap(GapRow.of(sessionId(), GapKind.LINEAGE_LOST,
                        GapClass.DIAGNOSTIC, endpoint.id(),
                        "the delivery at " + Text.safe(portId)
                                + " was paired with no export of this run"));
            }
        }
        return endpoint;
    }


    /**
     * The occurrence an event on this thread belongs to, by the one door
     * both passes mint producer and consumer addresses through
     * ({@link Identity#currentOccurrence}): the region occurrence running
     * here, else the ambient one of the thread's role on its node.
     *
     * <p>{@code nodeKey} is THE attribution rule's answer; when that rule
     * names no node the address is the unregistered one, and saying so is a
     * LINEAGE_LOST diagnostic at the site -- never a node guessed for it.</p>
     */
    public static OccurrenceAddress occurrenceHere(String nodeKey,
                                                   String site) {
        String node = Text.safe(nodeKey);
        if (node.isEmpty() || OccurrenceBinding.UNREGISTERED_SOURCE_KEY
                .equals(node)) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC, Text.safe(site),
                    "an event at this site ran on a thread the attribution"
                            + " rule names no node for -- no explicit scope,"
                            + " no registered receiver on its frames, no"
                            + " registered starter -- so its address is the"
                            + " unregistered one");
            node = OccurrenceBinding.UNREGISTERED_SOURCE_KEY;
        }
        return Identity.currentOccurrence(node);
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
        String type = statedJavaType("version", location + "#" + version,
                javaType, expression);
        if (type.isEmpty()) return;
        distinct(at, "write#" + location + "#" + version);
        session.write(WriteRow.of(sessionId(), sequence(seq), at, location,
                version, expressionRef(expression), type));
    }

    /** One read, at the site index the event itself stood on. */
    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue,
                            String siteIndex) {
        read(occurrence, seq, site, location, observedVersion, symbol,
                javaType, concreteValue, siteIndex,
                ReadRow.UNKNOWN_VERSION);
    }

    /**
     * One read, also stating the version its mint's store published.
     *
     * <p>Only a placeholder has one: the term that consumes the read names
     * the mint's version, and this is what a reader follows from that
     * version back to this row (CONTRACT v2.4).</p>
     */
    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue,
                            String siteIndex, long mintVersion) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null || location == null) return;
        Endpoint at = endpoint(occurrence, site, 0, siteIndex);
        String type = statedJavaType("read", location + "#" + seq, javaType,
                null);
        if (type.isEmpty()) return;
        distinct(at, "read#" + location + "#" + seq);
        session.read(ReadRow.of(sessionId(), sequence(seq), at, location,
                observedVersion, Text.safe(symbol), type,
                Text.safe(concreteValue).isEmpty() ? null
                        : Text.safe(concreteValue), mintVersion));
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
            // The same cell the mint filed (ActiveRegion
            // #recordManualSymbolization), stated again where the root row
            // is: a session that published a CLOCK row nothing filed at the
            // mint can still resolve the symbol its decisions name.
            clockCell(symbol, rootId, recordedValue);
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
        // The verdict is the session's own row (X17 R4b), so the one
        // account of this replay is told that the mint is IN the session --
        // a different fact from the plant, which happens earlier and
        // survives an occurrence whose rows are then discarded.
        FocusedReplay.mintPublished(rootId);
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

    /**
     * One refusal on message-carried context: named, and the message goes
     * on without it.
     *
     * <p>The rule for every door the workload's own transport calls into:
     * a header or an envelope this side will not install is a row, never a
     * throw.  Fail-closed on the claim -- the values are not attributed and
     * the rows that needed them say so -- and never on the process.</p>
     *
     * <p>{@code subject} is the flow, not the message: one correlation id
     * is a fresh UUID per call, so keying the row by it published one row
     * per RPC (62 of them in the first minute of hdfs-11741) and no two
     * replays could be compared on them.  Stated once per transport, half
     * and reason, as every other refusal here is.</p>
     */
    public static void messageContextRefused(String subject, String detail) {
        gap(GapKind.MESSAGE_CONTEXT_REFUSED, GapClass.DIAGNOSTIC, subject,
                detail);
    }

    /**
     * One refusal or diagnostic, naming its subject.
     *
     * <p>A GAP ROW NAMES WHAT IT IS ABOUT: {@code GapRow.of} puts {@code
     * subject} through {@code Fields.text}, which REFUSES a blank one --
     * correctly, a refusal that reports a category is not evidence.  That
     * refusal is an {@code IllegalArgumentException} thrown out of a woven
     * hook, and this class never throws into the workload (see the class
     * javadoc): a publisher that did would change the execution it is
     * describing.  So an unnamed subject is answered HERE, by the session
     * that met it, with the kind and class the caller stated and a detail
     * that says the caller named nothing.  Every caller in {@code runtime/}
     * hands a subject that cannot be blank; this is the door holding the
     * next one to it.</p>
     */
    public static void gap(GapKind kind, GapClass cls, String subject,
                           String detail) {
        SessionPublisher session = publisher;
        if (session == null) return;
        String named = Text.safe(subject).trim();
        String says = Text.safe(detail);
        if (named.isEmpty()) {
            // A session is open, so sessionId() is not blank: configure()
            // sets both under one lock.
            named = sessionId();
            says = "this " + kind + " names no subject, so the run cannot"
                    + " say what it refused on: " + says;
        }
        // One statement, stated once: the same refusal is reached from every
        // activation that met it, and a reader counts named gaps.
        if (!claimEvent("gap", kind + "#" + cls + "#" + named + "#" + says)) {
            return;
        }
        session.gap(GapRow.of(sessionId(), kind, cls, named, says));
    }

    /** The symbols this session minted at declared region inputs. */
    private static final Map<String, Boolean> DECLARED_MINTS =
            new ConcurrentHashMap<String, Boolean>();

    /**
     * Records that one symbol was minted at a declared region input.
     *
     * <p>SESSION-WIDE, AND FILED AT THE MINT.  A mint installs its symbol
     * into a field the VM versions, and that version is no write -- nobody
     * stored it, the mint made it ({@link RowPublication} suppresses it and
     * the placeholder read states it instead).  The mint happens in the
     * innermost activation, and every activation it runs inside sees the
     * same field shadow afterwards, so the write log of an OUTER activation
     * offers that version as a write of the location: only a session-wide
     * answer suppresses it, and the per-activation one let hdfs-17960's
     * version 173 through on {@code REGION.f167c8f6}.</p>
     *
     * <p>WHEN it is filed is the other half, and it is what makes the
     * suppression independent of which activation publishes first.  This is
     * called from {@code ActiveRegion#recordManualSymbolization} and
     * {@code ActiveRegion#recordConfiguredSourceMint} -- where the mint RUNS
     * -- and every publication happens when an activation closes, which is
     * strictly later than the mint of any store that activation's write log
     * can hold.  Filed at publication instead, the answer depended on the
     * order two activations happened to close in: on hdfs-11741 campaign #5b
     * a second activation published 284 of the clock mints' stores as
     * WriteRows at {@code sun.reflect.NativeMethodAccessorImpl#invoke}
     * before the minting activation had said anything at all.  The
     * publication-time call is kept as well, for a mint row that reached
     * publication by some other road than the two recorders.</p>
     */
    public static void declaredMintSymbol(String symbol) {
        DECLARED_MINTS.put(Text.safe(symbol), Boolean.TRUE);
    }

    /** Whether one symbol was minted at a declared region input. */
    public static boolean isDeclaredMintSymbol(String symbol) {
        return DECLARED_MINTS.containsKey(Text.safe(symbol));
    }

    /**
     * Enters one level of the execution index: an application method's entry.
     *
     * <p>The frame's iteration is the k-th entry of this site in the level
     * that encloses it, under the root hop that level is running in
     * ({@code Identity.State#nextSiteEvent}).  No node is named: a level's
     * counts are keyed by (level, root hop, site) and by nothing else.</p>
     *
     * @return the token that closes exactly this level
     */
    public static long enterFrame(String callSiteId, Object receiver) {
        return Identity.enterFrame(callSiteId, receiver);
    }

    /** Leaves the level {@code token} opened. */
    public static void exitFrame(long token) {
        Identity.exitFrame(token);
    }

    /**
     * The ordinal of one decision at {@code siteId} in the occurrence that
     * is performing it, or {@code 0} when this thread runs none.
     *
     * <p>I3: a decision row is addressed by the occurrence that performed
     * the branch and its ordinal is counted on that occurrence, which is
     * what an obligation's {@code (siteId, ordinal)} flip is addressed
     * by.</p>
     */
    public static int nextBranchOrdinal(String siteId) {
        return Identity.nextBranchOrdinal(siteId);
    }

    /**
     * Files the frame of one work start, for the work it started.
     *
     * <p>The starter's own frames are unchanged: a start is an event, not a
     * call, and what it leaves behind is the frame the STARTED work is
     * indexed from (IDENTITY-V3 SS1, scope transfer).</p>
     */
    public static void startWork(String startSiteId, Object carrier) {
        Identity.startWork(startSiteId, carrier);
    }

    /** Takes the start frame filed for the work this object carries. */
    public static void claimStart(Object carrier) {
        Identity.claimStart(carrier);
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
            ref = "EXPR." + ArtifactIO.digest(
                    Text.safe(RowCodec.toLine(object)), 16);
            REFS.put(object, ref);
        }
        SessionPublisher session = publisher;
        if (session != null) session.expression(ref, object);
        return ref;
    }

    /**
     * The clock cells one decision's term NAMES, with what each one read.
     *
     * <p>I4, and the whole of it: the row states the cells the decision's
     * own expression tree mentions, resolved to their root ids through this
     * session's mints ({@link #clockCell}), each at the instant its mint
     * recorded.  A decision that reads no clock states none, and a
     * concrete decision -- no term at all -- states none either.</p>
     *
     * <p>It used to answer a JVM-WIDE map of every clock the process had
     * ever minted, so a row listed cells its term never read and could miss
     * the one it did: on the hdfs-11741 corpus 14 of 17 {@code
     * removeExpiredKeys#u15} rows lack the cell their own term reads, and 15
     * of 17 list other NODES' cells -- one MiniDFSCluster is one JVM.
     * Downstream that membership IS the claim: {@code explore.Corpus#index}
     * files a cell under every session whose decision "read" it, and {@code
     * compose.ClaimPolicy#movedRoots}/{@code #clockNecessary} read it as
     * "this session's decision read this cell".</p>
     */
    static Map<String, Long> clockReadings(JsonObject term) {
        Map<String, Long> named = new java.util.LinkedHashMap<String, Long>();
        if (term == null || CLOCK_CELLS.isEmpty()) return named;
        java.util.Deque<JsonElement> pending =
                new java.util.ArrayDeque<JsonElement>();
        // Iteratively, over an explicit stack and a seen set: a container's
        // expression nests one relation per recorded operation, and a walk
        // that recursed would stack-overflow into the workload or be cut
        // before the leaves -- and a cell dropped by a cut reads downstream
        // exactly like a cell the term never named.
        java.util.Map<JsonElement, Boolean> seen =
                new java.util.IdentityHashMap<JsonElement, Boolean>();
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
                // Only a symbol this session MINTED as a clock resolves, so
                // matching on the VM's spelling wherever it stands cannot
                // name a cell that is not one.
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

    /**
     * Files one clock cell this session minted: the symbol that names it,
     * the root it is, and the instant the mint read.
     *
     * <p>Called at the MINT ({@code ActiveRegion#recordManualSymbolization})
     * and again when the root row is published, which are the same fact
     * stated twice; the mint is the one that has to be first, because an
     * activation nested inside the minting one publishes its decisions
     * before the mint's own row exists.</p>
     */
    static void clockCell(String symbol, String rootId,
                          String recordedValue) {
        String named = Text.safe(symbol);
        String root = Text.safe(rootId);
        Long reading = longOrNull(recordedValue);
        if (named.isEmpty() || root.isEmpty() || reading == null) return;
        CLOCK_CELLS.put(named, new ClockCell(root, reading.longValue()));
    }

    /**
     * Where one row sits in the run: the VM's own event id, or 0.
     *
     * <p>One counter for every kind, so a producer's prefix can be cut at
     * its export and a read ordered against the write it saw.  The VM's
     * ledger is that counter -- decisions carry its event id, versions are
     * drawn from it -- so a row states the id it was produced at rather
     * than a second numbering of the same events.</p>
     *
     * <p><b>{@code seq == 0} means THIS ROW CARRIES NO VM CLOCK.</b>  An
     * ambient mint, a decision taken before path recording opened, an
     * export the ledger did not number: the run cannot place it in the VM's
     * event order and the row says so.  It is not a position at the start
     * of the run and no reader may treat it as one.</p>
     *
     * <p>It used to answer the session's HIGH-WATER MARK instead, on the
     * ground that such a row is "no earlier than anything already seen".
     * That made two different statements one integer: "no VM clock" and
     * "the latest VM event this session published" both came out as 345.
     * On the 17960 corpus 46, 46 and 52 decision rows per session share a
     * seq with another row, and in each group exactly ONE owns that VM
     * event id and carries a term -- {@code
     * FSImageFormatPBSnapshot$Saver.serializeSnapshotSection#u61#1} at 220,
     * {@code FSImageFormatProtobuf$Saver.saveSnapshots#u13#1} at 345 -- the
     * rest borrowed it and state no term at all.  A borrowed mark reads
     * downstream as a real ordering: {@code Arms#pathCondition} keeps every
     * decision {@code seq < before}, so a clockless decision was dropped
     * from or kept in a prefix by the accident of where the mark stood when
     * it was published.  Answering 0 states the one thing that is true.</p>
     */
    private static long sequence(long vmEventId) {
        return vmEventId > 0L ? vmEventId : 0L;
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
    private static String javaType(String declared, JsonObject expression,
                                   String walk) {
        String type = Text.safe(declared);
        return type.isEmpty() ? statedType(expression, 0, walk) : type;
    }

    /**
     * Names a row whose java type neither the caller nor the VM stated, and
     * publishes no row for it.
     *
     * <p>It used to publish {@code Ljava/lang/Object;}, which is a type the
     * run did not observe: on the 17960 clean corpus 2 of 100 write rows and
     * on the 11741 corpus 419 of 25,206 went out that way, declaring a
     * reference where the run knew nothing -- and the composer lowers a
     * reference-sorted write against an integral read as two sorts for one
     * location.  The class this covers is every row of every kind whose
     * declared type is empty AND whose expression states no {@code
     * _java_type} anywhere: the row is refused, and each read of that
     * version then reaches the formula with no read-from arm, which is what
     * {@code UNSTATED_VALUE} names.</p>
     *
     * @return the descriptor when the run stated one, else {@code ""}
     */
    private static String statedJavaType(String kind, String subject,
                                         String declared,
                                         JsonObject expression) {
        String type = javaType(declared, expression,
                kind + " type of " + subject);
        if (!type.isEmpty()) return type;
        gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, subject,
                "this " + kind + " states no java type and its expression"
                        + " states none either, so the run cannot say what"
                        + " sort it wrote and publishes no row for it");
        return "";
    }

    /**
     * The walk under {@link #javaType}, with its bound NAMED when it cuts.
     *
     * <p>The same silent-cut shape M-R2 closed for the four
     * {@code RowPlaceholderMint} walks ({@code RowPublication#cut}): a walk
     * that found no {@code _java_type} and a walk that was cut before it
     * could look both answered {@code ""}, so a row refused
     * UNSTATED_VALUE because its expression states no sort read exactly
     * like one refused because this walk ran out of depth.  The bound stays
     * -- a container's expression on hdfs-17960 nests one relation per
     * recorded operation -- and the cut says so, once per walk and
     * subject.</p>
     */
    private static final int TYPE_WALK_DEPTH = 64;

    private static String statedType(JsonElement node, int depth,
                                     String walk) {
        if (depth > TYPE_WALK_DEPTH) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    firstNonBlank(walk, sessionId()),
                    "this expression walk stopped at depth "
                            + TYPE_WALK_DEPTH + ", so \"no java type\" here"
                            + " is the walk's bound and not the"
                            + " expression's silence");
            return "";
        }
        if (node == null || !node.isJsonObject()) return "";
        JsonObject object = node.getAsJsonObject();
        JsonElement own = object.get("_java_type");
        if (own != null && own.isJsonPrimitive()) {
            String stated = Text.safe(own.getAsString());
            if (!stated.isEmpty()) return stated;
        }
        for (java.util.Map.Entry<String, JsonElement> member
                : object.entrySet()) {
            String found = statedType(member.getValue(), depth + 1, walk);
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

    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt) {
        // Identity's, so a row's endpoint and the endpoint a message files
        // as its producer are one computation.
        return Identity.endpointAt(occurrence, site, attempt);
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
    public static void journalRegion(long vmRegionEnterEventId,
                                     OccurrenceAddress occurrence) {
        Identity.regionKey(vmRegionEnterEventId);
        if (vmRegionEnterEventId > 0L && occurrence != null) {
            PERFORMERS.put(Long.valueOf(vmRegionEnterEventId), occurrence);
        }
    }

    /**
     * The occurrence whose activation the VM named, or null.
     *
     * <p>A logged read or write is an event of the activation that PERFORMED
     * it, and the VM states which one on every record it keeps
     * ({@code regionEnterEventId}).  The row used to name the innermost
     * activation that happened to publish the location's log instead, which
     * on hdfs-17960 put a read the deletion region made into the anchor's
     * rows -- so the anchor's path carried a read it never performed, and
     * "each path carries its own reads" was false of it.  One key, filed
     * here and in {@link FrameJournal}, so the occurrence a row names and
     * the frames it carries are the same activation's.</p>
     */
    public static OccurrenceAddress occurrenceAt(long vmRegionEnterEventId) {
        return vmRegionEnterEventId <= 0L ? null
                : PERFORMERS.get(Long.valueOf(vmRegionEnterEventId));
    }

    /** The occurrence of every activation this session has entered. */
    private static final Map<Long, OccurrenceAddress> PERFORMERS =
            new ConcurrentHashMap<Long, OccurrenceAddress>();

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
        // What the replay RAN the obligation's roots at, stated by the
        // replay.  A root the obligation assigns that no mint planted means
        // this run read the recording's value where the wave asked for
        // another one, so it did not run what was asked -- and the composer
        // meeting that as "the mint states X and the obligation assigns Y"
        // is the second statement of it, not the first.
        for (Map.Entry<String, String> unplanted
                : FocusedReplay.unplantedAssignments().entrySet()) {
            gap(GapKind.ASSIGNMENT_UNPLANTED, GapClass.BLOCKING,
                    // The focus row's own key for the root; JSON admits an
                    // empty one, and this session is what is left to name.
                    firstNonBlank(unplanted.getKey(), sessionId()),
                    "the obligation assigns this root \"" + unplanted
                            .getValue() + "\" and no mint of this replay"
                            + " planted it");
        }
        // What this replay was handed and could not read.  A focus row the
        // session could not read whole leaves it reporting role FOCUSED
        // with however many obligations it parsed, so the shortfall is the
        // session's own row rather than a line on stderr.
        for (String shortfall : FocusedReplay.shortfalls()) {
            gap(GapKind.SESSION_INCOMPLETE, GapClass.BLOCKING,
                    sessionId(), shortfall);
        }
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
            rows.append(RowCodec.toLine(
                    RowCodec.writeObligationResult(result))).append('\n');
        }
        try {
            java.nio.file.Files.write(
                    java.nio.file.Paths.get(worker,
                            edu.uva.liftlab.graphchecker.contract
                                    .ObligationDir.RESULT),
                    rows.toString().getBytes(
                            java.nio.charset.StandardCharsets.UTF_8));
        } catch (java.io.IOException unwritable) {
            System.err.println("Causynth could not write the replay's"
                    + " obligation verdict: " + unwritable);
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            AMBIENT.clear();
            CLAIMED_READS.clear();
            DECLARED_MINTS.clear();
            REFS.clear();
            Identity.resetForTests();
            CLOCK_CELLS.clear();
            publisher = null;
            sessionId = "";
            Interactions.resetForTests();
            Lineage.resetForTests();
            FocusedReplay.resetForTests();
            SessionPublisher.resetForTests();
            HandoffMint.resetForTests();
        }
    }
}
