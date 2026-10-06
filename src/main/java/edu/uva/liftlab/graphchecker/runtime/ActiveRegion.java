package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.BranchObservation.BranchDecision;
import edu.uva.liftlab.graphchecker.runtime.BranchObservation.PreparedBranch;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.LoopBackedgeBudget;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.ReplayLoopResourceCut;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** One live activation of a declared region, and what it records. */
final class ActiveRegion {
    final long token;
    /** The one task whose region-local path this activation records. */
    final RuntimeTask activation;
    /** The address every row of this activation is keyed by, or null. */
    OccurrenceAddress d3Address;
    /** Whether this activation counts against its address's set. */
    private boolean activationClaimed;
    /** Exact event-ledger entry of this native region frame. */
    long vmRegionEnterEventId;
    final Object receiver;
    final Thread thread;
    final AtomicBoolean finished = new AtomicBoolean();
    /** The declared target branch event this occurrence decided, or null. */
    JsonObject targetReach;
    /** Terminal outcome, frozen when the occurrence stops running. */
    boolean abandoned;
    /** A selected non-loop occurrence ended in a durable named gap. */
    boolean terminalGap;
    private boolean closed;
    /** Loop bodies this activation has charged. */
    volatile long chargedLoopBodies;
    /** Logical sources and request scopes observed while this ran. */
    final Set<String> observedSourceKeys = new LinkedHashSet<>();
    /** Every source the observed context or the receiver's registration
     *  attributes this to. */
    Set<String> attributedSourceKeys() {
        Set<String> keys = new LinkedHashSet<>(observedSourceKeys);
        SourceRef registered = RuntimeTraceContext.sourceFor(receiver);
        if (registered != null) keys.add(registered.key());
        return keys;
    }

    synchronized boolean beginClose() {
        if (closed) return false;
        closed = true;
        return true;
    }

    /** Exact configured-source and planned-action observations. */
    final List<JsonObject> symbolizedRows = new ArrayList<>();
    final List<JsonObject> branchMappings = new ArrayList<>();
    /** The write log this activation read out, and its gaps. */
    final Map<String, JsonObject> sharedStateRecords =
            new LinkedHashMap<>();
    /** The locations its read-out refused, with why. */
    final Map<String, String> sharedStateRefusals = new LinkedHashMap<>();
    /** Symbols this activation already minted at a one-shot hook. */
    final Set<String> materialized = new LinkedHashSet<>();
    /** The box each configuration key's first getter read here minted. */
    private final Map<String, Object> configurationReads =
            new LinkedHashMap<>();
    /** The declared inputs that took such a box: symbolic, and stated by
     *  the first read's row. */
    private final Set<String> configurationReuses = new LinkedHashSet<>();
    final ConcolicRegionRuntime.OccurrenceCounter
            materializationOccurrences =
            new ConcolicRegionRuntime.OccurrenceCounter();
    final Map<String, Integer> accessorCallOccurrences =
            new LinkedHashMap<>();
    private final LoopBackedgeBudget loopBackedges;
    private final Map<Long, PreparedBranch> preparedBranches =
            new LinkedHashMap<>();
    /** One shared expression DAG for all read-outs in this VM session. */
    final VmExpressionTable.Store expressionStore;
    private long preparedBranchSequence;
    int lastPathConditionSize;
    /**
     * The Java-side branch-observation gate, opened once the first selected
     * input is symbolic (or inherited from a symbolic caller).
     */
    boolean pathRecordingStarted;

    ActiveRegion(long token, RuntimeTask activation,
                 Object receiver, Thread thread) {
        this.token = token;
        this.activation = activation;
        this.receiver = receiver;
        this.thread = thread;
        this.expressionStore = ConcolicRegionRuntime.workloadExpressionStore;
        this.loopBackedges = new LoopBackedgeBudget(activation.loopBound);
    }

    /** Counts this activation against its address's set (bounds loop-body
     *  occurrences). */
    void claimActivation() {
        if (activationClaimed) return;
        activationClaimed = true;
        activation.claimActivation();
    }

    /** Gives the slot back; this activation published nothing. */
    void releaseActivation() {
        if (!activationClaimed) return;
        activationClaimed = false;
        activation.releaseActivation();
    }

    /** This activation's address as a row names it, or "" when unnamed. */
    String address() {
        return d3Address == null ? "" : d3Address.render();
    }

    /**
     * Charges one body of this loop to the replay resource cap, returning
     * the cut that ends the activation once the cap is spent.
     */
    synchronized ReplayLoopResourceCut chargeLoopBody(String loopId) {
        // Body entries a loop may run before the replay is cut.
        int maxBodies = LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES;
        chargedLoopBodies++;
        long entered = loopBackedges.recordBody(inThisCall(loopId));
        if (entered <= maxBodies) return null;
        return new ReplayLoopResourceCut(loopId, maxBodies, entered,
                ReplayLoopResourceCut.REASON);
    }

    /** Counts one traversal of this loop's backedge; returns the attempt. */
    synchronized long traverseBackedge(String loopId) {
        return loopBackedges.recordTraversal(inThisCall(loopId));
    }

    /**
     * A loop's budget key: the loop in the method activation running it.
     * Keyed by the loop alone, every call of a helper in one long activation
     * shared one budget (WritableUtils.readVLong, cut at its 9th body across
     * the token fields a DataXceiver reads: a9b token-expired.mirror).
     */
    private static String inThisCall(String loopId) {
        return LoopBackedgeBudget.scoped(loopId, Identity.frameToken());
    }

    /**
     * Records a decision while the symbolic gate is closed, and answers
     * with the occurrence of the site it charged, or {@code 0} where
     * nothing was recorded.
     */
    int recordConcreteDecision(
            String method, int unitIndex, BranchDecision decision) {
        try {
            // The only caller has filtered out undeclared sites.
            String site = SiteId.render(method, unitIndex);
            int occurrence = Identity.nextBranchOrdinal(site);
            // No path condition was added: the row owns an empty range.
            branchMappings.add(BranchObservation.decisionRow(method,
                    unitIndex, occurrence, 0L, decision.outcome(), 0, 0));
            if (activation.targetTest(site)
                    && activation.targetBranchOccurrence == occurrence) {
                // Concrete: it stands after every event so far, so the path
                // condition before it is every decision the VM recorded.
                recordTargetReach(site, occurrence, decision.outcome(),
                        Identity.afterLastEvent());
            }
            return occurrence;
        } catch (Throwable ignored) {
            // Observation must never alter the workload's own outcome.
            return 0;
        }
    }

    /**
     * States one decision to {@code FocusedReplay}, the only account of
     * whether a replay follows its obligation; keep no second account here.
     */
    void observeReplayDecision(
            String siteId, int occurrence, BranchDecision decision) {
        if (d3Address == null) return;
        if (FocusedReplay.observeDecision(d3Address, siteId, occurrence,
                decision.outcome)) {
            ConcolicResultPublisher.concludeAtRefusal();
        }
    }

    /** Whether this activation has walked a branch its obligation forbids. */
    boolean replayPrefixContradicted() {
        return d3Address != null && FocusedReplay.contradicted(d3Address);
    }

    PreparedBranch prepareBranch(
            String method, int unitIndex, String expression)
            throws Exception {
        String site = SiteId.render(method, unitIndex);
        int occurrence = Identity.nextBranchOrdinal(site);
        long sequence = ++preparedBranchSequence;
        if (sequence > Integer.MAX_VALUE) {
            return null;
        }
        long handle = (sequence << 32)
                | (occurrence & 0xffffffffL);
        PreparedBranch prepared = new PreparedBranch(handle, method,
                unitIndex, expression, occurrence);
        preparedBranches.put(handle, prepared);
        return prepared;
    }

    PreparedBranch takePreparedBranch(long handle) {
        return handle <= 0L ? null : preparedBranches.remove(handle);
    }

    /**
     * Records the declared target branch event this occurrence decided.
     */
    void recordTargetReach(String siteId, int occurrence,
                                   boolean outcome, long vmEventId) {
        if (targetReach != null) return;
        JsonObject reach = new JsonObject();
        reach.addProperty("kind", "TARGET_REACH_EVENT");
        reach.addProperty("siteId", safe(siteId));
        reach.addProperty("occurrence", occurrence);
        reach.addProperty("outcome", outcome);
        // Same clock as the decisions, so they can be ordered against it.
        if (vmEventId > 0L) reach.addProperty("vmEventId", vmEventId);
        targetReach = reach;
    }

    /**
     * Whether a configured-source hook may mint where it just fired.
     *
     * <p>A concretely run region contributes literals, never freedom:
     * minting under a concrete occurrence adds a free root that
     * is decoupled from what computed the value (e.g. an expiry from its
     * clock).  The owning occurrence is the thread's active one (occurrences
     * do not nest), and the question is {@code FocusedReplay}'s: does it run
     * symbolic here?  Otherwise nothing is minted and a DIAGNOSTIC gap says
     * why; an unaddressed activation is never focused.</p>
     */
    static boolean mintsUnderSymbolicOccurrence(
            ActiveRegion active, String sourceId, String fieldSignature) {
        if (active != null && active.symbolicallyActive()) return true;
        RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                firstNonBlank(safe(sourceId), safe(fieldSignature)),
                "this configured-source hook fired under "
                        + (active == null ? "none" : active.mintAddress())
                        + ", which is not an occurrence this replay runs"
                        + " symbolically, so the field it stands on holds"
                        + " the literal this execution produced and no root"
                        + " is minted for " + safe(sourceId) + " here"
                        + " (field " + safe(fieldSignature) + ")");
        return false;
    }

    /**
     * Whether this occurrence runs symbolic, per {@code FocusedReplay}; with
     * no focus row (the recording) every planned occurrence does.
     */
    boolean symbolicallyActive() {
        if (!FocusedReplay.focusedSession()) return true;
        return FocusedReplay.focused(activation.taskId, d3Address);
    }

    /** This activation, as a row about its mint names it. */
    private String mintAddress() {
        return firstNonBlank(address(), Long.toString(token))
                + " of region " + safe(activation.regionId);
    }

    /**
     * The declared mint site one hook execution stands at, or null.  The
     * catalog lists SITES, not a budget: any read at a known site binds to
     * its symbol.  A configuration read at a site this occurrence's catalog
     * lacks (its recording never read the key there; a flipped path reaches
     * new reads) holds the world's value, which {@code RootMint#configuration}
     * wrote before the mint, and mints nothing: named, and stated as a
     * concrete reading by the caller.  A tree hook's plant is per site, so
     * its unnamed site is a plan/instrumentation disagreement, BLOCKING.
     */
    synchronized RootMint.SourceSiteEntry observeConfiguredSourceEntry(
            String sourceId, String runtimeFieldSignature) {
        CausynthTraceRecorder.ActiveCallSiteContext context =
                CausynthTraceRecorder.currentCallSiteContext();
        List<ConfiguredSourcePhaseContract.Occurrence> declaration =
                new ArrayList<>();
        String site = context == null ? "" : context.siteId();
        for (ConfiguredSourcePhaseContract.Occurrence candidate
                : activation.configuredSourcePhases) {
            if (candidate.sourceId().equals(safe(sourceId))
                    && (site.isEmpty()
                    || candidate.siteId().equals(site))) {
                declaration.add(candidate);
            }
        }
        ConfiguredSourcePhaseContract.Occurrence planned =
                declaration.isEmpty() ? ConcolicTaskPlan.configuration()
                        .declaredPhase(safe(sourceId)) : null;
        if (declaration.isEmpty() && planned == null) {
            // A tree hook every NameNode runs (a block key's serial, a
            // configuration a scaffold hooks) in a case whose plan declares
            // its source nowhere: no root of this case, so nothing to mint
            // and nothing a verdict waits for -- named, not blocking, and
            // counted by a closed negative.
            RowRuntime.gap(GapKind.HOOK_UNDECLARED, GapClass.DIAGNOSTIC,
                    mintAddress(), "the hook for " + safe(sourceId)
                            + " ran, but no task of this case's plan"
                            + " declares a phase of that source: it is no"
                            + " root of this case, and nothing is minted");
            return null;
        }
        if (context == null) {
            refuseMint(GapKind.DECLARATION_MISSING,
                    declaration.isEmpty() ? null : declaration.get(0),
                    "the PUBLISH hook for " + safe(sourceId)
                            + " ran under no active call site, so the"
                            + " mint is at no declared phase");
            return null;
        }
        if (declaration.isEmpty()
                && planned.category() == RootCategory.CONFIG) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    mintAddress(), "the configuration read of "
                            + safe(sourceId) + " at " + site + " is outside"
                            + " this occurrence's frozen phase catalog (its"
                            + " recording never read the key there): the"
                            + " field holds the world's value, written at"
                            + " every read, but no symbol is minted, so this"
                            + " occurrence's decisions on it are concrete;"
                            + " the read is stated as a concrete reading");
            return null;
        }
        if (declaration.isEmpty()) {
            refuseMint(GapKind.DECLARATION_MISSING, null,
                    "PUBLISH " + site + " is outside the frozen phase"
                            + " catalog, so nothing declares this mint");
            return null;
        }
        // All rows are executions of one site and agree on phase id,
        // field and callee, so the first stands for them.
        ConfiguredSourcePhaseContract.Occurrence matched =
                declaration.get(0);
        if (!matched.fieldSignature().equals(
                safe(runtimeFieldSignature))
                || !matched.runtimeDeclaredCallee().equals(
                context.declaredCallee())) {
            refuseMint(GapKind.DECLARATION_MISSING, matched,
                    "the runtime field and callee differ from the ones"
                            + " the catalog site declares");
            return null;
        }
        return new RootMint.SourceSiteEntry(matched, site);
    }

    /** The box a getter read of this configuration minted here, or null
     *  ({@code RootMint#materializePrimitiveValue}); a non-null answer is
     *  the box the asking input {@code symbol} takes. */
    synchronized Object configurationRead(String sourceId, String symbol) {
        Object box = configurationReads.get(sourceId);
        if (box != null) configurationReuses.add(symbol);
        return box;
    }

    /** Whether this declared input took the box of its key's first read
     *  here: no input left unsymbolized. */
    synchronized boolean configurationReused(String symbol) {
        return configurationReuses.contains(symbol);
    }

    synchronized void configurationMinted(String sourceId, Object box) {
        configurationReads.putIfAbsent(sourceId, box);
    }

    /** Publishes one mint row for one entry of a declared site. */
    synchronized void recordConfiguredSourceMint(
            RootMint.SourceSiteEntry entry, String sourceId,
            String fieldSignature, String symbol,
            JsonElement expression, boolean reused,
            String recordedValue) {
        JsonObject row = new JsonObject();
        // The live read, taken before any focused plant
        // (RootMint#configuredSource); a configuration's world plant comes
        // first (RootMint#configuration), so it states the world it read.
        // Without it a relative domain has no centre;
        // RowPlaceholderMint#roots names that case.
        if (recordedValue != null && !recordedValue.isEmpty()) {
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        row.addProperty("sourceId", safe(sourceId));
        row.addProperty("sourcePhaseId", entry.phaseId());
        row.addProperty("siteId", entry.siteId);
        row.addProperty("fieldSignature", safe(fieldSignature));
        row.addProperty("symbol", safe(symbol));
        row.add("expression", expression == null
                ? JsonNull.INSTANCE : expression);
        row.addProperty("reused", reused);
        row.addProperty("category", entry.category().name());
        configDomain(row, entry.domainMin(), entry.domainMax(),
                recordedValue);
        row.addProperty("mintOccurrence",
                mintOccurrence(safe(sourceId)));
        symbolizedRows.add(row);
    }

    /**
     * A configuration root's domain (SYMBOL-SCOPE §4.3): the hull of its
     * static anchors ({@code causynth.ConfigRoots}) and the value this mint
     * read.  None stated: a boolean, or no anchor, and the root is pinned.
     * A declaration stating half a domain, or a bound that is no integer,
     * states none either, named.
     */
    static void configDomain(JsonObject row, String staticMin,
                             String staticMax, String recordedValue) {
        String min = safe(staticMin).trim();
        String max = safe(staticMax).trim();
        String value = safe(recordedValue).trim();
        if (min.isEmpty() && max.isEmpty()) return;
        if (!INTEGER.matcher(min).matches()
                || !INTEGER.matcher(max).matches()
                || !INTEGER.matcher(value).matches()) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    optionalString(row, "sourceId"), "this configuration's"
                            + " declared domain [" + min + ", " + max
                            + "] or the value its mint read (" + value
                            + ") is no integer, so the root states no domain"
                            + " and is pinned");
            return;
        }
        BigInteger read = new BigInteger(value);
        row.addProperty("domainMin",
                read.min(new BigInteger(min)).toString());
        row.addProperty("domainMax",
                read.max(new BigInteger(max)).toString());
    }

    private static final java.util.regex.Pattern INTEGER =
            java.util.regex.Pattern.compile("-?[0-9]+");

    /**
     * The occurrence a mint of this root is addressed at: the region whose
     * plan owns it ({@code declaringRegion}, runtime counterpart of
     * {@code StaticScopeMap.holders}), not the innermost one, so seed and
     * replay agree.  Captured now, while the region stack is live.
     */
    private String mintOccurrence(String rootId) {
        return rootOwner(rootId).address();
    }

    /**
     * The live activation whose plan owns root {@code rootId}, else this
     * one: every mint asks it ({@code RootMint#mintOwner},
     * {@code RootMint#focusedRootValue}).
     */
    ActiveRegion rootOwner(String rootId) {
        ActiveRegion owner = ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Root(safe(rootId)));
        return owner == null ? this : owner;
    }

    /**
     * Records what one frozen {@code SYMBOLIC} action observed after its hook
     * minted or retained a value, with the concrete value the mint read (""
     * when none) -- the same shape as a configured-source mint.  The VM
     * label is descriptive only; authority comes from the exact expression.
     *
     * <p>Stated even when the replay planted here.  Trap: suppressing it
     * leaves the moved root with no {@code recordedValue}, which IMPORT
     * refuses (invariant 8).  A declared clock also states {@code
     * clockSkew}, how far its node's clock ran off the host's reading there
     * ({@code NodeClocks}; 0 is not written).</p>
     */
    synchronized void recordManualSymbolization(
            SymbolizeAction action, String requestedSymbol,
            List<String> fieldPath, String fieldSignature,
            JsonElement expression, boolean minted, boolean reused,
            String recordedValue, long clockSkew) {
        if (action == null || minted == reused) {
            throw new IllegalArgumentException(
                    "manual symbolization must be exactly minted or reused");
        }
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "MANUAL_SYMBOLIC_INPUT_OBSERVATION");
        row.addProperty("authority", "EXACT_PLANNED_SYMBOLIZATION_ACTION_V1");
        row.addProperty("portId", action.symbol);
        row.addProperty("actionDigest", action.actionDigest);
        row.addProperty("plannedOccurrenceId",
                activation.occurrenceId);
        // Captured now: frames are gone at publish.  One row per mint
        // (RowPlaceholderMint), so the frames alone place it.
        row.addProperty("siteIndex", Identity.siteIndex().render());
        row.addProperty("symbol", safe(requestedSymbol));
        JsonArray encodedPath = new JsonArray();
        for (String segment : fieldPath == null
                ? Collections.<String>emptyList() : fieldPath) {
            encodedPath.add(safe(segment));
        }
        row.add("fieldPath", encodedPath);
        row.addProperty("fieldSignature", safe(fieldSignature));
        row.add("expression", expression == null
                ? JsonNull.INSTANCE : expression);
        JsonObject exact = VmExpressionIr.exactSymbolRoot(expression);
        row.addProperty("rawSymbol", exact == null ? ""
                : optionalString(exact, "_exp"));
        row.addProperty("javaType", exact == null ? action.javaType
                : optionalString(exact, "_java_type"));
        row.addProperty("minted", minted);
        row.addProperty("reused", reused);
        if (recordedValue != null && !recordedValue.isEmpty()) {
            // What THIS execution ran the root at, clocks included (the
            // seed replay's readings are the composer's timeline).
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        row.addProperty("category", action.category().name());
        if (!action.configSource.isEmpty()) {
            // A configuration getter's return is the root of its key.
            row.addProperty("sourceId", action.configSource);
            configDomain(row, action.configDomainMin,
                    action.configDomainMax, recordedValue);
        }
        // A declared wall-clock read says so, so no reader guesses a clock
        // from a name.  Trap: never publish the PLAN's instant as its value.
        if (action.declaresWallClockRead()) {
            row.addProperty(InputActionCatalog.DECLARED_WALL_CLOCK,
                    action.clock.nanos());
            if (!action.clock.source().isEmpty()) {
                row.addProperty(InputActionCatalog.DECLARED_CLOCK_SOURCE,
                        action.clock.source());
            }
            row.addProperty("eventSeq", action.eventSeq);
            if (clockSkew != 0L) {
                row.addProperty(RootMintRow.CLOCK_SKEW, clockSkew);
            }
        }
        row.addProperty("mintOccurrence",
                mintOccurrence(safe(action.symbol)));
        symbolizedRows.add(row);
        // I4: file the clock cell at mint time, keyed by the installed VM
        // symbol: nested activations publish their decisions before this
        // row exists.  Only a fresh mint of a declared clock; the port id
        // is a manual mint's root id.
        if (minted && action.declaresWallClockRead()) {
            String installed = optionalString(row, "rawSymbol");
            RowRuntime.clockCell(installed.isEmpty()
                            ? safe(requestedSymbol) : installed,
                    safe(action.symbol),
                    RowPublication.literal(safe(recordedValue)));
        }
    }

    /**
     * Names one refusal at a configured source's mint as a BLOCKING gap: the
     * wave's value was not written at the mint the obligation is about.
     */
    private void refuseMint(
            GapKind kind,
            ConfiguredSourcePhaseContract.Occurrence phase,
            String detail) {
        RowRuntime.gap(kind, GapClass.BLOCKING,
                // Never blank: a blank subject throws inside Fields.text,
                // out of the mint hook into the workload.
                firstNonBlank(
                        phase == null ? "" : phase.phaseId(),
                        address(), Long.toString(token)),
                safe(detail));
    }

    /**
     * Whether this run can place this mint at the node and epoch the plan
     * addresses, filing the gap that says why not.  The site is reached once
     * per node lifecycle, so the epoch tells two mints of one site apart.
     */
    synchronized boolean mintIsPlaceable(Object mintOwner) {
        String unattributed = mintIsNotThePlannedNode(mintOwner);
        if (unattributed.isEmpty()) return true;
        refuseMint(mintAttribution(mintOwner).isEmpty()
                        ? GapKind.MINT_UNATTRIBUTED
                        : GapKind.EPOCH_UNMATCHED, null, unattributed);
        return false;
    }

    /**
     * Every node this mint is attributed to: the minted object's owner, this
     * occurrence's sources, and the thread's current source.
     */
    private Set<String> mintAttribution(Object mintOwner) {
        Set<String> attributed = new LinkedHashSet<>(
                attributedSourceKeys());
        SourceRef owner = RuntimeTraceContext.sourceFor(mintOwner);
        if (owner != null) attributed.add(owner.key());
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        if (context != null && context.source != null) {
            attributed.add(context.source.key());
        }
        return attributed;
    }

    /**
     * Why this mint cannot be shown to be the planned node and epoch, or
     * {@code ""}.
     *
     * <p>Deliberately stricter than root admission: admission tolerates an
     * unattributed activation, but a model rewrites the recorded execution,
     * so a mint must be attributed positively or the recorded value
     * stands.</p>
     */
    private String mintIsNotThePlannedNode(Object mintOwner) {
        String planned = safe(activation.sourceKey);
        if (!RuntimeTraceContext.declaresEpoch(planned)) return "";
        Set<String> attributed = mintAttribution(mintOwner);
        if (attributed.contains(planned)) return "";
        if (attributed.isEmpty()) {
            return "the registry attributes this mint to no node, so it "
                    + "cannot be shown to be " + planned + "; the "
                    + "recorded value stands";
        }
        // Another epoch of the planned node is named as such: the source
        // identity strips #epoch<n>, so it reads as the planned node.
        for (String observed : attributed) {
            if (!observed.equals(planned)
                    && RuntimeTraceContext.sameSourceIdentity(planned,
                    observed)) {
                return "the mint ran at " + observed + ", not at " + planned;
            }
        }
        return "the registry attributes this mint to " + attributed
                + ", which does not include " + planned;
    }
}
