package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.plan.VmExpressionTable;

import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;

import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;

import edu.uva.liftlab.graphchecker.runtime.RowRuntime;

import edu.uva.liftlab.graphchecker.runtime.BranchObservation.BranchDecision;
import edu.uva.liftlab.graphchecker.runtime.BranchObservation.PreparedBranch;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.LoopBackedgeBudget;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.LoopBoundCut;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.ReplayLoopResourceCut;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;

import java.util.ArrayList;

import java.util.Collections;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

import java.util.Map;
import java.util.Set;

import java.util.concurrent.atomic.AtomicBoolean;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** One live activation of a declared region, and what it records. */
final class ActiveRegion {
    final long token;
    /** The one task whose region-local path this activation records. */
    final RuntimeTask activation;
    /** The address every row of this activation is keyed by (IDENTITY-V3), or null. */
    edu.uva.liftlab.graphchecker.contract.OccurrenceAddress d3Address;
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
    /** Every source the observed context or the receiver's registration attributes this to. */
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
    /** Symbols this activation already minted at a one-shot hook. */
    final Set<String> materialized = new LinkedHashSet<>();
    final ConcolicRegionRuntime.OccurrenceCounter
            materializationOccurrences =
            new ConcolicRegionRuntime.OccurrenceCounter();
    final Map<String, Integer> accessorCallOccurrences =
            new LinkedHashMap<>();
    final LoopBackedgeBudget loopBackedges;
    /**
     * The ordinal of the open invocation of each fixed-count loop; read only
     * by {@link #chargeLoopBody} to scope the body budget per invocation.
     */
    private final Map<String, Integer> activeLoopInvocations =
            new LinkedHashMap<>();
    /** Next invocation ordinal by runtime natural-loop id. */
    private final Map<String, Integer> loopInvocationOrdinals =
            new LinkedHashMap<>();
    private final Map<Long, PreparedBranch> preparedBranches =
            new LinkedHashMap<>();
    /** One shared expression DAG for all read-outs in this VM session. */
    final VmExpressionTable.Store expressionStore;
    private long preparedBranchSequence;
    int lastPathConditionSize;
    /** Whether this activation's bounded local path has been cut. */
    boolean loopBoundCut;
    boolean pathRecordingStarted;

    ActiveRegion(long token, RuntimeTask activation,
                         Object receiver, Thread thread) {
        this.token = token;
        this.activation = activation;
        this.receiver = receiver;
        this.thread = thread;
        this.expressionStore = ConcolicRegionRuntime.workloadExpressionStore;
        this.loopBackedges = new LoopBackedgeBudget(
                activation.loopBound);
    }


    /** Counts this activation against its address's set (bounds loop-body occurrences). */
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
    synchronized ReplayLoopResourceCut chargeLoopBody(
            String loopId) {
        // Body entries a loop may run before the replay is cut.
        int maxBodies = LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES;
        chargedLoopBodies++;
        // The ceiling is per dynamic invocation: keyed by the static loop
        // id alone, repeated walks of one loop would share one budget.
        Integer invocation = activeLoopInvocations.get(loopId);
        String budgetKey = invocation == null ? loopId
                : LoopBackedgeBudget.scoped(loopId,
                        invocation.intValue());
        long entered = loopBackedges.recordBody(budgetKey);
        if (entered <= maxBodies) return null;
        return replayBodyCut(loopId, maxBodies, entered,
                ReplayLoopResourceCut.REASON);
    }

    /**
     * Records the terminal of this activation's spent body budget.  Like
     * {@link #loopBoundCut}: marks the activation cut and carries the reason,
     * so a hook failure is told apart from the bound.
     */
    ReplayLoopResourceCut replayBodyCut(String loopId, int maxBodies,
                                        long attemptedBody, String reason) {
        loopBoundCut = true;
        return new ReplayLoopResourceCut(loopId, maxBodies, attemptedBody,
                reason);
    }

    /** Opens one dynamic invocation of a fixed-count loop (scopes its budget). */
    synchronized void openLoopInvocation(String loopId) {
        if (loopId.isEmpty()
                || activeLoopInvocations.containsKey(loopId)) {
            return;
        }
        activeLoopInvocations.put(loopId,
                loopInvocationOrdinals.merge(loopId, 1, Integer::sum));
    }

    synchronized void closeLoopInvocation(String loopId) {
        if (!loopId.isEmpty()) activeLoopInvocations.remove(loopId);
    }

    /** Records the terminal of this activation's bounded local path. */
    LoopBoundCut loopBoundCut(
            String backedgeId, int maxTraversals, String reason) {
        loopBoundCut = true;
        return new LoopBoundCut(backedgeId, maxTraversals, reason);
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
            int occurrence = RowRuntime.nextBranchOrdinal(site);
            recordDecisionRow(method, unitIndex, occurrence,
                    decision.outcome());
            if (activation.targetBranchSite.equals(site)
                    && activation.targetBranchOccurrence == occurrence) {
                recordTargetReach(site, occurrence, decision.outcome(),
                        0L);
            }
            return occurrence;
        } catch (Throwable ignored) {
            // Observation must never alter the workload's own outcome.
            return 0;
        }
    }

    /** The branch row one decision that added no path condition is. */
    private void recordDecisionRow(
            String method, int unitIndex, int occurrence,
            boolean outcome) {
        JsonObject mapping = BranchObservation.branchMapping(
                method, unitIndex, occurrence, 0L);
        mapping.addProperty("outcome", outcome);
        mapping.addProperty("rawPathConditionSize", 0);
        mapping.addProperty("rawPathConditionBaseline", 0);
        branchMappings.add(mapping);
    }

    /**
     * States one decision to {@code FocusedReplay}, the only account of
     * whether a replay follows its obligation; keep no second account here.
     */
    boolean observeReplayDecision(
            String siteId, int occurrence, BranchDecision decision) {
        if (d3Address == null) return true;
        edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                .observeDecision(d3Address, siteId, occurrence,
                        decision.outcome);
        return !edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                .contradicted(d3Address);
    }

    /** Whether this activation has walked a branch its obligation forbids. */
    boolean replayPrefixContradicted() {
        return d3Address != null
                && edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                        .contradicted(d3Address);
    }

    PreparedBranch prepareBranch(
            String method, int unitIndex, String expression)
            throws Exception {
        String site = SiteId.render(method, unitIndex);
        int occurrence = RowRuntime.nextBranchOrdinal(site);
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
     * <p>A concretely run region contributes literals, never freedom (README
     * SS9 rule 1): minting under a concrete occurrence adds a free root that
     * is decoupled from what computed the value (e.g. an expiry from its
     * clock).  The owning occurrence is the thread's active one (occurrences
     * do not nest), and the question is {@code FocusedReplay}'s: does it run
     * symbolic here?  Otherwise nothing is minted and a DIAGNOSTIC gap says
     * why; an unaddressed activation is never focused.</p>
     */
    static boolean mintsUnderSymbolicOccurrence(
            ActiveRegion active, String sourceId, String fieldSignature) {
        if (active != null && active.symbolicallyActive()) return true;
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                        .DECLARATION_MISSING,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank(
                        safe(sourceId), safe(fieldSignature)),
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
        return edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank(
                address(),
                Long.toString(token)) + " of region "
                + safe(activation.regionId);
    }

    /**
     * The declared mint site one hook execution stands at, or null.  The
     * catalog lists SITES, not a budget: any read at a known site binds to
     * its symbol.  An unnamed site is a plan/instrumentation disagreement
     * and a gap.
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
            if (candidate.phase()
                    == ConfiguredSourcePhaseContract.Phase.PUBLISH
                    && candidate.sourceId().equals(safe(sourceId))
                    && (site.isEmpty()
                    || candidate.siteId().equals(site))) {
                declaration.add(candidate);
            }
        }
        if (context == null) {
            refuseMint(edu.uva.liftlab.graphchecker.contract.GapKind
                            .DECLARATION_MISSING,
                    declaration.isEmpty() ? null : declaration.get(0),
                    "the PUBLISH hook for " + safe(sourceId)
                            + " ran under no active call site, so the"
                            + " mint is at no declared phase");
            return null;
        }
        if (declaration.isEmpty()) {
            refuseMint(edu.uva.liftlab.graphchecker.contract.GapKind
                            .DECLARATION_MISSING, null,
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
            refuseMint(edu.uva.liftlab.graphchecker.contract.GapKind
                            .DECLARATION_MISSING, matched,
                    "the runtime field and callee differ from the ones"
                            + " the catalog site declares");
            return null;
        }
        return new RootMint.SourceSiteEntry(matched, site);
    }

    /** Publishes one mint row for one entry of a declared site. */
    synchronized void recordConfiguredSourceMint(
            RootMint.SourceSiteEntry entry, String sourceId,
            String fieldSignature, String symbol,
            JsonElement expression, boolean reused,
            String recordedValue) {
        JsonObject row = new JsonObject();
        // The live read, taken before any plant (RootMint#configuredSource),
        // so never the wave's value.  Without it a relative domain has no
        // centre; RowPlaceholderMint#roots names that case.
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
        row.addProperty("mintOccurrence",
                mintOccurrence(safe(sourceId)));
        symbolizedRows.add(row);
    }

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
     * <p>Stated even when the replay planted here: the value is read before
     * the plant, so it is the recording's; the plant is the focus row's
     * statement.  Trap: suppressing it leaves the moved root with no
     * {@code recordedValue}, which IMPORT refuses (invariant 8).</p>
     */
    synchronized void recordManualSymbolization(
            SymbolizeAction action, String requestedSymbol,
            List<String> fieldPath, String fieldSignature,
            JsonElement expression, boolean minted, boolean reused,
            String recordedValue) {
        if (action == null || minted == reused) {
            throw new IllegalArgumentException(
                    "manual symbolization must be exactly minted or reused");
        }
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind",
                ConcolicRegionRuntime.MANUAL_INPUT_OBSERVATION_KIND);
        row.addProperty("authority",
                ConcolicRegionRuntime.MANUAL_INPUT_OBSERVATION_AUTHORITY);
        row.addProperty("portId", action.symbol);
        row.addProperty("actionDigest", action.actionDigest);
        row.addProperty("plannedOccurrenceId",
                activation.occurrenceId);
        // Captured now: frames are gone at publish.  One row per mint
        // (RowPlaceholderMint), so the frames alone place it.
        row.addProperty("siteIndex", RowRuntime.siteIndexHere());
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
            // What THIS execution read, clocks included: the seed replay is
            // the reference the composer's deltas are relative to.
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        // A declared wall-clock read says so, so no reader guesses a clock
        // from a name.  Trap: never publish the PLAN's instant as its value.
        if (action.declaresWallClockRead()) {
            row.addProperty(InputActionCatalog.DECLARED_WALL_CLOCK, true);
            row.addProperty("eventSeq", action.eventSeq);
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
            edu.uva.liftlab.graphchecker.contract.GapKind kind,
            ConfiguredSourcePhaseContract.Occurrence phase,
            String detail) {
        RowRuntime.gap(kind, edu.uva.liftlab.graphchecker.contract
                        .GapClass.BLOCKING,
                // Never blank: a blank subject throws inside Fields.text,
                // out of the mint hook into the workload.
                edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank(
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
                        ? edu.uva.liftlab.graphchecker.contract.GapKind
                                .MINT_UNATTRIBUTED
                        : edu.uva.liftlab.graphchecker.contract.GapKind
                                .EPOCH_UNMATCHED, null, unattributed);
        return false;
    }

    /**
     * Every node this mint is attributed to: the minted object's owner, this
     * occurrence's sources, and the thread's current source -- the registry
     * {@link ConcolicTaskPlan#lifecycleMismatch} reads.
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
        String elsewhere = ConcolicTaskPlan.lifecycleMismatch(planned,
                attributed);
        return elsewhere.isEmpty()
                ? "the registry attributes this mint to " + attributed
                + ", which does not include " + planned
                : elsewhere;
    }
}
