package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
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
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
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
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

/**
 * The one door between the replay and the row set.
 *
 * <p>Never throws into the workload (that would change the run it
 * describes), but never silent about the run: a site that ran and could not
 * be addressed files a {@link #gap}.</p>
 */
public final class RowRuntime {
    /** Where the campaign's REPLAY stage puts every worker's session. */
    public static final String SESSIONS_ENV = "CAUSYNTH_CONCOLIC_SESSIONS";

    private static final Object LOCK = new Object();
    /**
     * The clock cells this session minted, by the VM symbol that names one.
     *
     * <p>I4: a decision row carries exactly the clock cells its term names,
     * so this is a symbol-to-cell lookup, never the set a row states.  Filed
     * at the MINT, because an activation nested inside the minting one
     * publishes its decisions first.</p>
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

    /** Opens {@code <iteration>/sessions/<sessionId>/} for this JVM. */
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
        // The schedule goes with the rows; events from before the open are
        // kept and written first.
        final SessionPublisher opened = publisher;
        ScheduleLog.install(new ScheduleLog.Sink() {
            @Override
            public void write(JsonObject row) {
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

    /** The sessions directory {@link #SESSIONS_ENV} names, or null. */
    private static Path declaredSessionsRoot() {
        String declared = Text.safe(System.getenv(SESSIONS_ENV));
        return declared.isEmpty() ? null
                : Paths.get(declared).toAbsolutePath();
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

    /** Derived, never declared: two workers must never share an id. */
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
     * Publishes the address of one activation.
     *
     * @return the address, or {@code null} when this run can name no node
     */
    public static OccurrenceAddress beginActivation(long token,
                                                    String nodeKey,
                                                    String regionId,
                                                    String taskId) {
        // The occurrence the region ENTRY already opened, not a second one:
        // one entry, one address, the same the recorder computed.
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
            session.activation(ActivationRow.of(sessionId(), address,
                    Text.safe(taskId), FocusedReplay.focused(taskId,
                            address), true, threadKey(),
                    anchorProducer(address)));
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
     * States that the occurrence this run ran at {@code ran} answers the
     * planned occurrence {@code planned} by its shape (IDENTITY §9) and
     * states its rows at {@code planned}: never silent, since the address
     * the run computed is gone from every row.
     */
    static void answered(OccurrenceAddress ran, OccurrenceAddress planned) {
        if (ran == null) return;
        gap(GapKind.ADDRESS_UNSTABLE, GapClass.DIAGNOSTIC, planned.render(),
                "the planned occurrence ran at " + ran.render() + ", under"
                        + " a chain of its shape whose counts differ from"
                        + " the recording's, and answers it: its rows state"
                        + " the planned address");
    }

    /**
     * States one unselected activation, once: an activation with no row
     * silently downgrades an arm that rests on it.
     */
    public static void ambientActivation(OccurrenceAddress address) {
        SessionPublisher session = publisher;
        if (session == null || address == null) return;
        if (AMBIENT.putIfAbsent(address.id(), Boolean.TRUE) != null) return;
        // Not an instrumented region, so it has no decisions to find.
        session.activation(ActivationRow.of(sessionId(), address, "", false,
                false, threadKey(), anchorProducer(address)));
    }

    /** The endpoint that sent the message this address's anchor names,
     *  when this run filed it: the link a causal chain is followed by. */
    private static Endpoint anchorProducer(OccurrenceAddress address) {
        return address.context().form() == CausalContext.Form.ANCHOR
                ? Interactions.producer(((CausalContext.Anchor)
                        address.context()).producerEndpointId())
                : null;
    }

    private static final Map<String, Boolean> AMBIENT =
            new ConcurrentHashMap<String, Boolean>();

    /**
     * What an activation is program-ordered by (CONTRACT-SPEC §2.2): the
     * start of the work it runs in, claimed on this thread (a queue item, a
     * task: {@link Identity#claimedStart}), else its thread, by name plus id
     * (the name repeats across a pool).  Two items one consumer thread
     * claims run in their queue's order, which their starters decide: a
     * server's pipeline applies two clients' requests on one thread.
     */
    private static String threadKey() {
        String claimed = Identity.claimedStart();
        if (claimed != null) return ActivationRow.CLAIMED + claimed;
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
            // Polarity-free: the composer conjoins (outcome ? term : not term).
            session.decision(DecisionRow.of(sessionId(), sequence(seq),
                    occurrence, Text.safe(siteId), ordinal, outcome, ref,
                    clockReadings(condition)));
        }
        if (FocusedReplay.observeDecision(occurrence, siteId, ordinal,
                outcome)) {
            ConcolicResultPublisher.concludeAtRefusal();
        }
    }

    /** One export, and the producer endpoint a delivery can be paired to. */
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
                        Text.safe(recordedValue)));
            }
        }
        return endpoint;
    }

    /** Allocated before the mint: attaches are answered BY endpoint. */
    public static Endpoint nextEndpoint(OccurrenceAddress occurrence,
                                        String site, int attempt) {
        return occurrence == null ? null : endpoint(occurrence, site,
                attempt);
    }


    /**
     * One v_H minted at an endpoint already allocated, paired with the
     * export of the message this thread received ({@link
     * MessageDoors#current}): by the element's handle, else by that
     * message and the port when the message carried an element for it.
     */
    public static Endpoint attachedAt(Endpoint endpoint, long seq,
                                      String portId, long handle,
                                      String correlationId, String symbol,
                                      String javaType, String arrival,
                                      boolean answered,
                                      String answeredValue) {
        if (endpoint == null) return null;
        MessageDoors.Inbound received = MessageDoors.current();
        Interactions.Pairing pairing = Interactions.pairing(portId, handle,
                received == null ? "" : received.correlationId,
                received == null ? "" : received.half);
        Endpoint producer = pairing.producer();
        if (producer != null && handle > 0L
                && !"HANDLE".equals(pairing.key())) {
            // Paired by the message, not the handle: the producer is the
            // message's sender, not the one that staged this value.
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
                // The row states WHICH key paired; blank when none did.
                session.attach(AttachRow.of(sessionId(), sequence(seq),
                        endpoint, Text.safe(symbol), type,
                        Text.safe(arrival), answered,
                        answered ? Text.safe(answeredValue) : null, producer,
                        Text.safe(correlationId), pairing.key()));
            }
            if (producer == null) {
                session.gap(GapRow.of(sessionId(), GapKind.LINEAGE_LOST,
                        GapClass.DIAGNOSTIC, endpoint.id(),
                        handle == SymbolicMessageEnvelope.ABSENT
                                ? "the message carried no element for "
                                + Text.safe(portId) + ": its sender forwarded"
                                + " the value without exporting it, so the"
                                + " delivery pairs with no export"
                                : "the delivery at " + Text.safe(portId)
                                + " was paired with no export of this run"));
            }
        }
        return endpoint;
    }


    /**
     * CONFIRM (b): one delivery compared with the edge the model chose --
     * its producer and value -- never enforced.  A difference is a
     * {@code CONFIRM_MISMATCH}; a producer taken because it answers the
     * model's producer's question is never silent either.
     */
    private static void confirm(Endpoint consumer, Endpoint producer,
                                String arrival) {
        Confirmation.Compared compared = Confirmation.attached(consumer,
                producer, arrival);
        if (!compared.mismatch.isEmpty()) {
            gap(GapKind.CONFIRM_MISMATCH, GapClass.DIAGNOSTIC, consumer.id(),
                    compared.mismatch);
        }
        if (!compared.substitution.isEmpty()) {
            gap(GapKind.ADDRESS_UNSTABLE, GapClass.DIAGNOSTIC, consumer.id(),
                    compared.substitution);
        }
    }

    /**
     * The occurrence an event on this thread belongs to, through
     * {@link Identity#currentOccurrence}.
     *
     * <p>When the attribution rule names no node, the address is the
     * unregistered one plus a LINEAGE_LOST gap -- never a guessed node.</p>
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
     * The tool's own code.  Its wait sets and frame levels are never program
     * state, though the VM versions them once an application reference keys
     * them (adhoc pipeline-reply.flush: TimedWaits' send counter, read and
     * written in one call, stood as a BLOCKING TOPOLOGY_DIVERGENCE).
     */
    private static boolean ownCode(String site) {
        return site != null && site.startsWith(OWN_CODE);
    }

    private static final String OWN_CODE = "edu.uva.liftlab.graphchecker.";

    /**
     * One write, at the site index the event stood on WHEN it ran.
     *
     * <p>The write log is read out at the activation's end, so the index
     * comes from its {@link FrameJournal}, not the live frames.  An empty
     * index is the caller's gap to name; nothing here fabricates one.</p>
     */
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

    /**
     * One read, at the site index the event itself stood on, plus its
     * placeholder mint's version ({@link ReadRow#UNKNOWN_VERSION} for none,
     * CONTRACT-SPEC §2.2).
     */
    public static void read(OccurrenceAddress occurrence, long seq,
                            String site, LocationId location,
                            long observedVersion, String symbol,
                            String javaType, String concreteValue,
                            String siteIndex, long mintVersion) {
        read(occurrence, seq, site, location, observedVersion, symbol,
                javaType, concreteValue, siteIndex, mintVersion, false);
    }

    /**
     * The same, stating whether a writer the log never named had reached
     * the location when it read ({@link ReadRow#unnamedWriter}).
     */
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
        distinct(at, "read#" + location + "#" + seq);
        session.read(ReadRow.of(sessionId(), sequence(seq), at, location,
                observedVersion, Text.safe(symbol), type,
                Text.safe(concreteValue).isEmpty() ? null
                        : Text.safe(concreteValue), mintVersion,
                unnamedWriter));
        Confirmation.read(at, location, observedVersion, mintVersion);
    }

    /**
     * Names two events of one site that stand on identical frames in one
     * occurrence.
     *
     * <p>They are stated, not separated by a counter: an ordinal moves when
     * a branch flip inserts an earlier event, and two replays would then
     * disagree which event is which (IDENTITY §3).</p>
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

    /** One root minted, with its kind, its category and the domain it
     *  resolved to. */
    public static void rootMint(OccurrenceAddress occurrence, long seq,
                                String rootId, String symbol, RootKind kind,
                                RootCategory category,
                                String recordedValue, String domainMin,
                                String domainMax, boolean declared,
                                Clock clock, long clockSkew) {
        if (kind == RootKind.CLOCK) {
            // The cell the mint already filed, restated so a CLOCK row
            // nothing filed at the mint still resolves.
            clockCell(symbol, rootId, recordedValue);
        }
        SessionPublisher session = publisher;
        if (session == null || occurrence == null) return;
        session.rootMint(RootMintRow.of(sessionId(), sequence(seq),
                occurrence,
                Text.safe(rootId), Text.safe(symbol),
                kind == null ? RootKind.INTEGRAL : kind, category,
                Text.safe(recordedValue),
                Text.safe(domainMin).isEmpty() ? null : Text.safe(domainMin),
                Text.safe(domainMax).isEmpty() ? null : Text.safe(domainMax),
                declared, clock, clockSkew));
        // The mint is IN the session -- a different fact from the plant,
        // which survives an occurrence whose rows are discarded.
        FocusedReplay.mintPublished(rootId);
    }

    /** The anchor, with phi stated in the FATAL polarity as published;
     *  an anchor the run did not reach states none. */
    public static void target(OccurrenceAddress occurrence, long seq,
                              String anchorSiteId, JsonObject condition,
                              boolean fatalArm, boolean observedFatal,
                              boolean reachedAnchor) {
        target(occurrence, seq, anchorSiteId, reachedAnchor
                        ? fatalTerm(condition, fatalArm) : "",
                observedFatal, reachedAnchor, null);
    }

    /** The anchor with phi already stated (a disjunction of fatal arms, a
     *  helper decision's condition), and the open decider arm it left out,
     *  if any (TargetRow.OpenArm). */
    static void target(OccurrenceAddress occurrence, long seq,
                       String anchorSiteId, String phiTerm,
                       boolean observedFatal, boolean reachedAnchor,
                       TargetRow.OpenArm openArm) {
        SessionPublisher session = publisher;
        if (session == null || occurrence == null) return;
        session.target(TargetRow.of(sessionId(), sequence(seq), occurrence,
                Text.safe(anchorSiteId), Text.safe(phiTerm), observedFatal,
                reachedAnchor, openArm));
        if (observedFatal && reachedAnchor
                && FocusedReplay.declaredTarget(occurrence)) {
            ConcolicResultPublisher.concludeAtWitness();
        }
    }

    /**
     * One decision's predicate in the polarity of its fatal arm: the ref
     * as the arm it states, or {@code (not ref)}.  A decision that states no
     * predicate decided concretely, and its predicate is the constant of the
     * arm it took: {@code true} where that arm is the fatal one, else
     * {@code false} (CONTRACT-SPEC §2.2), never empty.
     */
    static String fatalTerm(JsonObject condition, boolean fatalArm) {
        String ref = Text.safe(expressionRef(condition));
        return ref.isEmpty() ? String.valueOf(fatalArm)
                : Arms.conjunct(ref, fatalArm);
    }

    /**
     * One refusal on message-carried context: a row, never a throw, and the
     * message goes on without it.
     *
     * <p>{@code subject} is the flow, not the message: a correlation id is a
     * fresh UUID per call, so keying by it gives one row per RPC.</p>
     */
    public static void messageContextRefused(String subject, String detail) {
        gap(GapKind.MESSAGE_CONTEXT_REFUSED, GapClass.DIAGNOSTIC, subject,
                detail);
    }

    /**
     * One refusal or diagnostic, naming its subject, stated once.
     *
     * <p>{@code GapRow.of} throws on a blank subject, and this class never
     * throws into the workload, so a blank subject is answered here with the
     * session id and a detail saying the caller named nothing.</p>
     */
    public static void gap(GapKind kind, GapClass cls, String subject,
                           String detail) {
        SessionPublisher session = publisher;
        String named = Text.safe(subject).trim();
        String says = Text.safe(detail);
        if (named.isEmpty() && session != null) {
            // configure() sets publisher and sessionId under one lock.
            named = sessionId();
            says = "this " + kind + " names no subject, so the run cannot"
                    + " say what it refused on: " + says;
        }
        // Once: every activation that met the refusal reaches here.
        if (!claimEvent("gap", kind + "#" + cls + "#" + named + "#" + says)) {
            return;
        }
        if (session == null) {
            // No session: the recording states it through its trace.
            CausynthTraceRecorder.recordingGap(kind, cls, named, says);
            return;
        }
        session.gap(GapRow.of(sessionId(), kind, cls, named, says));
    }

    /**
     * Unnamed work's region entries, by {@code <node>/region/<regionId>}
     * ({@link Identity#occurrence}): none opened an occurrence.
     */
    private static final Map<String, AtomicInteger> UNNAMED =
            new ConcurrentHashMap<String, AtomicInteger>();

    /**
     * A hop named the standing region at position {@code region} of this
     * thread's region stack ({@link Identity#hopOpened}): the recording
     * states the occurrence as an activation of its own, a replay admits the
     * task planned there.  Each half is a no-op in the other pass.
     */
    static void regionNamed(int region, OccurrenceAddress address,
                            Object receiver, long hop) {
        CausynthTraceRecorder.regionNamed(region, address);
        ConcolicRegionRuntime.regionNamed(address, receiver, hop);
    }

    /**
     * The occurrence the hop {@code hop} named ends: the hop ended, or the
     * region's entry exited ({@code thrown} when by a throw).
     */
    static void regionUnnamed(int region, long hop, Throwable thrown) {
        ConcolicRegionRuntime.regionUnnamed(hop, thrown);
        CausynthTraceRecorder.regionUnnamed(region);
    }

    /**
     * One region entry unnamed work made, which opened no occurrence.
     * Never silent: each region and node is named once, in either pass, by
     * a LINEAGE_LOST row, and the session's manifest counts every entry at
     * the run's end ({@link #closeSession}).
     */
    static void unnamedEntry(String nodeKey, String regionId) {
        // Neither the trace nor the schedule states what ran before the
        // window opened.
        if (!RecordingWindow.opened()) return;
        String subject = Text.safe(nodeKey) + "/region/"
                + Text.safe(regionId);
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

    /**
     * Root id -> rendered occurrence -> what a declared root held when this
     * replay first read it there and minted none.
     */
    private static final Map<String, Map<String, String>> CONCRETE =
            new ConcurrentHashMap<String, Map<String, String>>();
    /** The declared roots found carrying another input's expression. */
    private static final Set<String> DERIVED =
            ConcurrentHashMap.<String>newKeySet();

    /**
     * One read of a declared root that minted none ({@code RootMint}: an
     * occurrence run concretely, a mint refused or failed): the occurrence's
     * rows hold literals computed from this value, and the session's
     * manifest states it at the run's end ({@link #closeSession}) -- an arm
     * or path of the session whose closure reaches the occurrence exists
     * only at it (CONTRACT-SPEC §4).  The first read at an occurrence is the
     * one a mint there would have stated.
     */
    static void concreteReading(String rootId, String occurrence,
                                String value) {
        if (Text.safe(occurrence).isEmpty() || Text.safe(value).isEmpty()) {
            return;
        }
        CONCRETE.computeIfAbsent(Text.safe(rootId),
                key -> new ConcurrentHashMap<String, String>())
                .putIfAbsent(occurrence, value);
    }

    /**
     * A declared root whose value already carried an expression where it
     * was read, so no root was minted: its value is another input's (a
     * clock's, say), and no reading of it is the root's own.
     */
    static void derivedRoot(String rootId) {
        if (!Text.safe(rootId).isEmpty()) DERIVED.add(Text.safe(rootId));
    }

    /** The labels this session's declared mints asked the VM for. */
    private static final Set<String> MINT_LABELS =
            ConcurrentHashMap.<String>newKeySet();

    /**
     * Files one declared mint's label, BEFORE the VM makes its store.
     *
     * <p>SESSION-WIDE: the version a mint installs is no write
     * ({@link RowPublication} suppresses it), and every activation that
     * later reads the VM record sees it.  BEFORE THE STORE: once the VM
     * returns, an activation closing on another thread can publish it, so any
     * later filing point races.  Read by {@link #isDeclaredMint}.</p>
     */
    public static void declaredMintLabel(String label) {
        String named = Text.safe(label);
        if (!named.isEmpty()) MINT_LABELS.add(named);
    }

    /**
     * Whether one VM symbol names a declared mint's store.
     *
     * <p>The VM spells a minted field {@code M_<sort>_field_<label>_<owner>}
     * or {@code M_<sort>_field_<label>_<path>}, so the rest after
     * {@code M_<sort>_field_} is a filed label or starts with one plus
     * {@code _}.  A copy of a minted symbol carries the same name: which
     * VERSION is the mint's own store is {@code RowPlaceholderMint#mintStores}'
     * question.</p>
     */
    public static boolean isDeclaredMint(String symbol) {
        String name = Text.safe(symbol);
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

    /** The length of {@code M_<sort>_field_}. */
    private static final int FIELD_SYMBOL_HEAD = "M_J_field_".length();

    /**
     * Files the frame of one work start (thread start, executor submit,
     * fork) for the started work to claim (IDENTITY §3).  The start
     * happens either way; a frame that cannot be filed is a stated gap.
     */
    public static void startWork(String startSiteId, Object carrier) {
        String site = Text.safe(startSiteId);
        try {
            Identity.startWork(site, carrier);
        } catch (Throwable unnamed) {
            gap(GapKind.LINEAGE_LOST, GapClass.DIAGNOSTIC,
                    firstNonBlank(site, carrier == null ? ""
                            : carrier.getClass().getName()),
                    "the frame of this work start could not be filed, "
                            + "so the work it started carries no start-site "
                            + "frame in its execution index: " + unnamed);
        }
    }

    /**
     * Takes the start frame filed for the work {@code carrier} carries, at
     * its entry ({@link Identity#claimStart}).  The work runs either way;
     * an unclaimable frame is a stated gap.
     *
     * @return what ends the claim ({@link #endClaim}), 0 when none opened
     */
    public static long claimStart(Object carrier) {
        // No carrier, no frame, and no subject to name a gap by.
        if (carrier == null) return 0L;
        try {
            return Identity.claimStart(carrier);
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

    /** Ends one work entry's claim ({@link Identity#endClaim}). */
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

    /**
     * Takes the start filed for an item taken off a queue ({@link
     * Identity#claimItem}).  The work runs either way; an unclaimable start
     * is a stated gap.
     */
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

    /** Files one expression and returns the ref rows name it by. */
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

    /**
     * One expression's ref, filing nothing: THE structural identity of a VM
     * expression (equal refs, equal expressions), each node hashed once.
     */
    static String refOf(JsonObject expression) {
        return expressions.ref(expression);
    }

    /**
     * I4: the clock cells one decision's term NAMES, each at the instant its
     * mint recorded ({@link #clockCell}); none for a concrete decision.
     *
     * <p>Trap: never a JVM-wide set of clocks -- one MiniDFSCluster is one
     * JVM, and downstream ({@code explore.Corpus#index},
     * {@code compose.ClaimPolicy#movedRoots}) reads membership as "this
     * decision read this cell".</p>
     */
    static Map<String, Long> clockReadings(JsonObject term) {
        Map<String, Long> named = new LinkedHashMap<String, Long>();
        if (term == null || CLOCK_CELLS.isEmpty()) return named;
        Deque<JsonElement> pending =
                new ArrayDeque<JsonElement>();
        // Iterative and uncut: deep trees would overflow a recursion, and a
        // cell dropped by a cut reads as one the term never named.
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
                // Only a symbol this session minted as a clock resolves.
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

    /** Filed at the mint first, then again at the root row. */
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
     * <p>One counter for every kind, the VM's ledger, so rows order against
     * each other.  <b>{@code seq == 0} means THIS ROW CARRIES NO VM
     * CLOCK</b>, not "start of run".  Trap: never substitute a high-water
     * mark -- {@code Arms#pathCondition} keeps {@code seq < before}, so a
     * borrowed mark silently moves clockless decisions in or out of a
     * prefix.</p>
     */
    private static long sequence(long vmEventId) {
        return vmEventId > 0L ? vmEventId : 0L;
    }

    /**
     * The JVM descriptor a row states: the declaration, else the first
     * {@code _java_type} in the expression tree, depth-first in member order
     * (an operator node states none; its operands do).
     */
    private static String javaType(String declared, JsonObject expression) {
        String type = Text.safe(declared);
        if (!type.isEmpty()) return type;
        // Java null is a reference, whichever field it was stored into (the
        // VM's null symbol states no class): a null store into a tracked
        // reference field is a write a later read joins.
        return isNull(expression) ? NULL_REFERENCE_TYPE
                : statedType(expression);
    }

    /** The java type of a written {@code null}: a reference (Ref sort). */
    private static final String NULL_REFERENCE_TYPE = "L";

    private static boolean isNull(JsonObject expression) {
        if (expression == null) return false;
        JsonElement symbol = expression.get("_exp");
        return symbol != null && symbol.isJsonPrimitive()
                && VmExpressionIr.SYMBOLIC_NULL.equals(symbol.getAsString());
    }

    /**
     * Names a row whose java type neither the caller nor the VM stated, and
     * publishes no row for it (UNSTATED_VALUE).
     *
     * <p>Trap: never default to {@code Ljava/lang/Object;} -- the composer
     * would lower a reference-sorted write against an integral read.</p>
     *
     * @return the descriptor when the run stated one, else {@code ""}
     */
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

    /**
     * The first type the expression states, each node once
     * ({@link ExpressionWalk}): cut at depth 64, a deeper one was a gap and
     * no row.
     */
    private static String statedType(JsonObject expression) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression);
             walk.hasNext(); ) {
            JsonObject object = walk.next();
            JsonElement own = object.get("_java_type");
            if (own != null && own.isJsonPrimitive()) {
                String stated = Text.safe(own.getAsString());
                if (!stated.isEmpty()) return stated;
            }
            // A String method's result is typed by the method, not its
            // operands.
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
            return Long.valueOf(Text.safe(value));
        } catch (NumberFormatException notALong) {
            return null;
        }
    }

    /** The refs of every expression filed, by the node they name. */
    private static volatile ExpressionRefs expressions = new ExpressionRefs();

    /** Events already stated (every kind), so one event is one occurrence's. */
    private static final Map<String, Boolean> CLAIMED_EVENTS =
            new ConcurrentHashMap<String, Boolean>();

    /**
     * One event, one occurrence: the first publisher wins.
     *
     * <p>VM logs are read out per activation over overlapping ranges, so one
     * event is reachable from every enclosing activation.  The first read-out
     * publishes it, addressed to the occurrence that performed it (IDENTITY
     * §4); a later one publishes nothing.</p>
     */
    public static boolean claimEvent(String kind, String identity) {
        return CLAIMED_EVENTS.put(Text.safe(kind) + "\n"
                + Text.safe(identity), Boolean.TRUE) == null;
    }

    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt) {
        // Identity's, so a row's endpoint and a message's producer are one
        // computation.
        return Identity.endpointAt(occurrence, site, attempt);
    }

    /** An unstated index stays empty, never the publisher's live one. */
    private static Endpoint endpoint(OccurrenceAddress occurrence,
                                     String site, int attempt,
                                     String siteIndex) {
        return Endpoint.of(occurrence, Text.safe(site),
                ExecutionIndex.parse(Text.safe(siteIndex)), attempt);
    }

    /** Keys this activation's frame journal by the VM's enter id. */
    public static void journalRegion(long vmRegionEnterEventId,
                                     OccurrenceAddress occurrence) {
        Identity.regionKey(vmRegionEnterEventId);
        if (vmRegionEnterEventId > 0L && occurrence != null) {
            PERFORMERS.put(Long.valueOf(vmRegionEnterEventId), occurrence);
        }
    }

    /**
     * The occurrence that PERFORMED a logged event, by the VM's
     * {@code regionEnterEventId}, or null.
     *
     * <p>Trap: not the innermost activation that published the log -- that
     * puts other regions' reads on a path.  Same key as {@link FrameJournal},
     * so a row's occurrence and frames are one activation's.</p>
     */
    public static OccurrenceAddress occurrenceAt(long vmRegionEnterEventId) {
        return vmRegionEnterEventId <= 0L ? null
                : PERFORMERS.get(Long.valueOf(vmRegionEnterEventId));
    }

    /** The occurrence of every activation this session has entered. */
    private static final Map<Long, OccurrenceAddress> PERFORMERS =
            new ConcurrentHashMap<Long, OccurrenceAddress>();

    /**
     * Publishes what only the end of a replay can state, and closes.
     *
     * <p>The replay owns the verdict and states it twice: into the session
     * (evidence) and the worker's {@code replay_verdict.jsonl}, which the
     * worker, the one writer of the obligation's answer, makes that answer
     * once the replay's process group is gone ({@code run_engine.sh}
     * {@code campaign_obligation_replay}).  A replay a refusal decided
     * withdraws its own session first, to {@code <worker>/refused-sessions/},
     * so no stage can read the prefix of a run it wrote.</p>
     */
    public static void closeSession() {
        SessionPublisher session = publisher;
        if (session == null) return;
        Map<String, Integer> unnamed = new LinkedHashMap<String, Integer>();
        for (Map.Entry<String, AtomicInteger> entry : UNNAMED.entrySet()) {
            unnamed.put(entry.getKey(), entry.getValue().get());
        }
        session.atClose(unnamed, CONCRETE, DERIVED);
        // A root the obligation assigns that no mint planted: this run did
        // not run what was asked.
        for (Map.Entry<String, String> unplanted
                : FocusedReplay.unplantedAssignments().entrySet()) {
            gap(GapKind.ASSIGNMENT_UNPLANTED, GapClass.BLOCKING,
                    // JSON admits an empty key; the session names it then.
                    firstNonBlank(unplanted.getKey(), sessionId()),
                    "the obligation assigns this root \"" + unplanted
                            .getValue() + "\" and no mint of this replay"
                            + " planted it");
        }
        // What the focus row left unread, as the session's own rows.
        for (String shortfall : FocusedReplay.shortfalls()) {
            gap(GapKind.SESSION_INCOMPLETE, GapClass.BLOCKING,
                    sessionId(), shortfall);
        }
        // CONFIRM (b) edges only the whole run can answer for, and the
        // pairings an obligation's world plants (FocusedReplay#results).
        for (String mismatch : Confirmation.close()) {
            gap(GapKind.CONFIRM_MISMATCH, GapClass.DIAGNOSTIC,
                    mismatch.substring(0, mismatch.indexOf(':')), mismatch);
        }
        List<ObligationResult> results =
                FocusedReplay.results(sessionId());
        for (ObligationResult result : results) {
            session.obligationResult(result);
        }
        String worker = FocusedReplay.workerDir();
        if (FocusedReplay.unsettled() && !worker.isEmpty()) {
            // A session missing a publication's rows settles no question:
            // the next ask of it replays again.
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
        // A replay a refusal decided publishes no session
        // (FocusedReplay#refusedAt): it withdraws the directory it opened,
        // and its verdict rows name none.
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

    /** Where a decided replay's session goes, under its worker. */
    static final String REFUSED_SESSIONS = "refused-sessions";

    /** The replay's statement to its worker: one row per obligation. */
    private static void writeWorkerVerdicts(String worker,
                                            List<ObligationResult> results) {
        if (results.isEmpty() || worker.isEmpty()) return;
        StringBuilder rows = new StringBuilder();
        for (ObligationResult result : results) {
            rows.append(RowCodec.toLine(
                    RowCodec.writeObligationResult(result))).append('\n');
        }
        try {
            Files.write(
                    Paths.get(worker,
                            ObligationDir.REPLAY_VERDICT),
                    rows.toString().getBytes(
                            StandardCharsets.UTF_8));
        } catch (IOException unwritable) {
            EngineConsole.println("Causynth could not write the replay's"
                    + " obligation verdict: " + unwritable);
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            AMBIENT.clear();
            CLAIMED_EVENTS.clear();
            ENDPOINTS.clear();
            MINT_LABELS.clear();
            UNNAMED.clear();
            CONCRETE.clear();
            DERIVED.clear();
            expressions = new ExpressionRefs();
            Identity.resetForTests();
            CLOCK_CELLS.clear();
            publisher = null;
            sessionId = "";
            Interactions.resetForTests();
            Lineage.resetForTests();
            FocusedReplay.resetForTests();
            RootMint.resetForTests();
            Confirmation.resetForTests();
            SessionPublisher.resetForTests();
            HandoffMint.resetForTests();
        }
    }
}
