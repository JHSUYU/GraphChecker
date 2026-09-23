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

final class ActiveRegion {
    /** The thread this activation ran on, as the recording names it. */
    final String threadName = Thread.currentThread().getName();
    final long token;
    /** The one task whose region-local path this activation records. */
    final RuntimeTask activation;
    /**
     * This activation's identity v2 address, or null when this run can
     * name no node to put it on.
     *
     * <p>{@code node#epoch / lineage hops / region#k} (IDENTITY-V2): the
     * address every contract row of this activation is keyed by.  The v1
     * {@link #occurrenceId()} is unchanged beside it -- the two are
     * minted from the same activation and nothing reads one for the
     * other.</p>
     */
    edu.uva.liftlab.graphchecker.contract.OccurrenceAddress d3Address;
    /** Whether this activation counts against its address's set. */
    private boolean activationClaimed;
    /** VM context whose writes belong to this materialized activation. */
    long vmContextId;
    /** Exact event-ledger entry of this native region frame. */
    long vmRegionEnterEventId;
    final Object receiver;
    final Thread thread;
    /** Entry lacked local producer-source evidence; OUT must confirm it. */
    /** Exact outgoing message leaves this provisional activation reached. */
    final AtomicBoolean finished = new AtomicBoolean();
    boolean prepared;
    /**
     * The declared target branch event this occurrence decided, or {@code
     * null} while it has not decided one.
     */
    JsonObject targetReach;
    /** Terminal outcome, frozen when the occurrence stops running. */
    boolean abandoned;
    /** A selected non-loop occurrence ended in a durable named gap. */
    boolean terminalGap;
    private boolean closed;
    /** Loop bodies this activation has charged. */
    volatile long chargedLoopBodies;
    /**
     * The stable causal context this candidate observed while it was live:
     * the logical sources it ran on and the external request scopes it ran
     * inside.
     */
    final Set<String> observedSourceKeys = new LinkedHashSet<>();
    /**
     * Every stable source this occurrence can be attributed to by the
     * application's own registration.
     *
     * <p>Two kinds of evidence, both produced by the replay itself.</p>
     */
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
    /**
     * Case-local references into the VM's own handoff ledger: the
     * declared port an attach landed on and the export event the
     * {@code VALUE_HANDOFF} edge relates it to.
     */
    /**
     * VM export event most recently published at each declared port.
     *
     * <p>README {@code RPC-1}: written down from the VM's own export
     * answer so the producer's interaction row can name it.</p>
     */

    /** The write log this activation read out, and its gaps. */
    final Map<String, JsonObject> sharedStateRecords =
            new LinkedHashMap<>();
    /** Read-out batch every record of this activation is stamped with. */
    final Set<String> materialized = new LinkedHashSet<>();
    private final Map<String, Integer> branchOccurrences =
            new LinkedHashMap<>();
    final ConcolicRegionRuntime.OccurrenceCounter
            materializationOccurrences =
            new ConcolicRegionRuntime.OccurrenceCounter();
    final Map<String, Integer> accessorCallOccurrences =
            new LinkedHashMap<>();
    final LoopBackedgeBudget loopBackedges;
    /**
     * The ordinal of the OPEN dynamic invocation of each fixed-count
     * loop, by runtime natural-loop id.
     *
     * <p>Its only reader is {@link #chargeLoopBody}, which scopes the
     * replay body budget to one dynamic invocation.  It used to also
     * publish a {@code loopCardinalities} row per invocation carrying
     * the exact array length, its ordinal and a cardinality authority;
     * nothing read those rows once R1 deleted the result envelope they
     * were written onto.</p>
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


    /**
     * Counts this activation against the published set of its address,
     * which is what bounds a loop-body region's occurrences.
     */
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

    /**
     * This activation's own occurrence identity.
     *
     * <p>The address, and nothing appended to it. Identity v1 numbered
     * the activations of one planned address and wrote {@code #a<n>}
     * beside it, because two runs of one address were two occurrences it
     * could not otherwise tell apart. Identity v3 distinguishes them by
     * the execution index they entered under, so an address IS the
     * occurrence and a suffix would be a second identity beside it.</p>
     */
    String occurrenceId() {
        return safe(activation.occurrenceId);
    }

    /**
     * Charges one body of this loop to the replay resource cap, returning
     * the cut that ends the activation once the cap is spent.
     */
    synchronized ReplayLoopResourceCut chargeLoopBody(
            String loopId) {
        int maxBodies = activation.maxLoopBodies(loopId);
        chargedLoopBodies++;
        // A fixed-count loop may be invoked repeatedly inside one region
        // activation.  Its resource ceiling applies to each dynamic
        // invocation; accumulating all invocations under the static loop
        // id cuts ordinary code after (for example) two 16-element array
        // walks.  openLoopInvocation opens the exact invocation before
        // the first body hook and closeLoopInvocation closes it.
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
     * Records the terminal of this activation's spent body budget.
     *
     * <p>The sibling of {@link #loopBoundCut}, and now the same two
     * statements: the activation IS cut ({@code loopBoundCut = true}), and
     * the cut carries the REASON it was taken.  The body cut used to be
     * built at its hook with neither -- so an activation cut for spending
     * its budget did not read as cut, and a cut taken because the hook
     * itself failed was indistinguishable from one taken at the bound.</p>
     */
    ReplayLoopResourceCut replayBodyCut(String loopId, int maxBodies,
                                        long attemptedBody, String reason) {
        loopBoundCut = true;
        return new ReplayLoopResourceCut(loopId, maxBodies, attemptedBody,
                reason);
    }

    /**
     * Opens one dynamic invocation of a fixed-count loop.
     *
     * <p>The resource ceiling applies per invocation, so the backedge
     * budget is scoped by which invocation this is; that an invocation
     * is open at all is the whole of what the hook states now.</p>
     */
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
     * The ordinal of the next decision this activation takes at one site.
     *
     * <p>I3 -- ROWS AND ORDINALS BELONG TO THE PERFORMER: the performer is
     * the occurrence running on this thread, and the count is kept there
     * ({@code Identity#nextBranchOrdinal}), beside the address the row
     * carries.  Counted per ACTIVATION, two activations that fold into one
     * occurrence (I1) each start at 1 and two of their rows collide at
     * (occurrence, site, ordinal) -- which is the pair an obligation's flip
     * is addressed by, and the pair {@code RowPublication#decisions} claims
     * each decision event under.</p>
     *
     * <p>The activation-local count remains for an activation running
     * outside every open region: a test that drives this class directly,
     * and any entry whose occurrence this run could name no node for.  It is
     * a count of this activation's own decisions, which is what it always
     * was.</p>
     */
    private int nextBranchOccurrence(String siteId) {
        int onPerformer = RowRuntime.nextBranchOrdinal(siteId);
        if (onPerformer > 0) return onPerformer;
        Integer previous = branchOccurrences.get(siteId);
        int occurrence = previous == null ? 1 : previous + 1;
        branchOccurrences.put(siteId, occurrence);
        return occurrence;
    }

    /**
     * Records a decision while the symbolic gate is closed, and answers
     * with the occurrence of the site it charged, or {@code 0} where
     * nothing was recorded.
     */
    int recordConcreteDecision(
            String method, int unitIndex, BranchDecision decision) {
        try {
            // observeDecision is the only caller and it has already
            // returned for every undeclared site, so the site here is
            // always one the plan named.
            String site = SiteId.render(method, unitIndex);
            int occurrence = nextBranchOccurrence(site);
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
     * States one decision to the one prefix matcher.
     *
     * <p>{@code runtime/FocusedReplay} is the only account of
     * whether a replay is following its obligation: it reads the
     * obligation and the published decisions, and a second account of
     * the same decisions is how two answers to one question appear.</p>
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

    /**
     * Whether this activation has already walked a branch its
     * obligation forbids.
     */
    boolean replayPrefixContradicted() {
        return d3Address != null
                && edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                        .contradicted(d3Address);
    }

    int nextLocalMaterializationOccurrence(
            String method, int unitIndex, String local) {
        return materializationOccurrences.local(method, unitIndex,
                local);
    }

    PreparedBranch prepareBranch(
            String method, int unitIndex, String expression)
            throws Exception {
        String site = SiteId.render(method, unitIndex);
        int occurrence = nextBranchOccurrence(site);
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
        // The anchor is read on the same clock as the decisions, so a
        // composer can say which of them were taken before it.
        if (vmEventId > 0L) reach.addProperty("vmEventId", vmEventId);
        targetReach = reach;
    }

    /**
     * Whether a configured-source hook may mint where it just fired.
     *
     * <p>A CONCRETELY RUN REGION CONTRIBUTES LITERALS, NEVER FREEDOM
     * (README SS9 rule 1).  The hook fires wherever its site runs, and it
     * used to mint on whatever activation was on the thread -- so an
     * occurrence whose every read is a literal handed the export a FREE
     * root the recording never had.  On hdfs-11741 that is {@code
     * HDFS.BLOCK_KEY.EXPIRY_DATE{,.CURRENT,.RETIRED}}: in the seed the
     * field arrives as {@code clock + k*keyUpdateInterval + tokenLifetime}
     * and the mint is a no-op publishing {@code reused}; where {@code
     * updateKeys} ran concrete the field was a literal and three fresh
     * INTEGRAL roots were minted beside it, which decouples the expiry
     * from the clock it is computed from -- twelve wave-1 obligations
     * refused {@code ASSIGNMENT_UNMINTABLE} on roots no replay could
     * plant, and a composer that cannot relate expiry to the clock.</p>
     *
     * <p>THE OCCURRENCE THAT OWNS THE SITE IS THE THREAD'S ACTIVE ONE.
     * Occurrences do not nest: entering a declared region below an active
     * occurrence opens none, so every site executed synchronously beneath
     * it -- {@code updateKeys}, {@code removeExpiredKeys} -- belongs to
     * that occurrence.  So the mint asks one question of it, the same one
     * {@code FocusedReplay} answers everywhere else: is this occurrence
     * one of the ones that run SYMBOLIC in this replay?  A replay handed
     * no focus row is the seed, where every planned occurrence does; a
     * focused replay runs its focused set and nothing else.</p>
     *
     * <p>A hook under no active occurrence at all, or under one that runs
     * concretely, mints nothing, plants nothing and says so once: the row
     * names the source and the occurrence that was active, or {@code
     * none}.  DIAGNOSTIC, because nothing was rewritten -- the region
     * reads the literal its own execution produced, which is what it read
     * in the recording; what the row answers is why no root row stands
     * here.  An activation this run could give no address is not focused
     * either, so it refuses by the same rule: a mint is addressed at an
     * occurrence, and one that cannot be named cannot be the focused
     * one.</p>
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
     * Whether THIS occurrence is one of the ones that run symbolic.
     *
     * <p>One implementation of the notion, and it is {@code
     * FocusedReplay}'s: the focused occurrence, a member of its
     * state-connected factor, or the mint of a root the obligation
     * assigns.  A replay handed no focus row is the recording, and every
     * planned occurrence of it runs symbolic.</p>
     */
    boolean symbolicallyActive() {
        if (!FocusedReplay.focusedSession()) return true;
        return FocusedReplay.focused(activation.taskId, d3Address);
    }

    /** This activation, as a row about its mint names it. */
    private String mintAddress() {
        return edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank(
                d3Address == null ? "" : d3Address.render(), occurrenceId(),
                Long.toString(token)) + " of region "
                + safe(activation.regionId);
    }

    /**
     * The declared mint site one hook execution stands at, or null.
     *
     * <p>The catalog is a list of mint SITES, not a selection and not a
     * budget: any read at a known site binds to that site's symbol,
     * however many reads there are and whichever occurrence makes them.
     * A hook that fires at a site the catalog does not name is still a
     * gap - that is a plan/instrumentation disagreement, not a free
     * occurrence.</p>
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
        // Every row of this list is one execution of ONE site, so they
        // agree on everything the mint reads off a declaration - the
        // phase id the symbol is derived from, the field and the callee.
        // Which execution the recording made is evidence on the row, not
        // a limit on the reads a replay may make.
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
        // What the run read at the mint, whether or not a plant followed
        // it: the mint hands the LIVE read here (RootMint#configuredSource
        // asks for it before the assignment is written), so this is never
        // the wave's own value.  A root whose row states no value has no
        // centre for a relative domain to resolve against -- [+0,+3]
        // around nothing -- so the composer cannot move it at all, and
        // RowPlaceholderMint#roots names an unstatable one rather than
        // letting the empty field pass.
        if (recordedValue != null && !recordedValue.isEmpty()) {
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        row.addProperty("sourceId", safe(sourceId));
        row.addProperty("sourcePhaseId", entry.phaseId());
        row.addProperty("occurrenceId", occurrenceId());
        row.addProperty("siteId", entry.siteId);
        row.addProperty("fieldSignature", safe(fieldSignature));
        row.addProperty("symbol", safe(symbol));
        row.add("expression", expression == null
                ? JsonNull.INSTANCE : expression);
        row.addProperty("reused", reused);
        row.addProperty("mintOccurrence",
                mintOccurrence(safe(sourceId)));
        symbolizedRows.add(row);
        // AT THE MINT, not at the publication: the store this mint just made
        // is no write, in this activation or in any other, and only a
        // register the session already holds when the OTHER activation reads
        // its write log out can say so (RowRuntime#declaredMintSymbol).  The
        // name is the VM's own, read exactly as the row's reader reads it.
        if (!reused) {
            RowRuntime.declaredMintSymbol(RowPlaceholderMint.vmSymbol(row));
        }
    }

    /**
     * The occurrence a mint of this root is ADDRESSED at, rendered.
     *
     * <p>The activation of the region whose plan owns the mint
     * ({@link #declaringRegion}), which is the runtime counterpart of
     * {@code StaticScopeMap.holders}.  Captured here because here is
     * where the region stack is live: the row is published when the
     * activation closes, and by then the nesting is gone.  It is what
     * makes a mint address the same in the seed and in a replay -- the
     * row used to carry whichever activation happened to be innermost,
     * and hdfs-11741 campaign #3 has one session (e635d55d...) whose
     * SERIAL_NO row landed on REGION.08ab84c9 at index depth 1 where
     * every other session and the seed put it on REGION.aaa1cfd7 at
     * depth 2, so the focus row's rootMints address matched nothing.</p>
     */
    private String mintOccurrence(String rootId) {
        ActiveRegion owner = ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Root(rootId));
        if (owner == null) owner = this;
        return owner.d3Address == null ? ""
                : owner.d3Address.render();
    }

    /**
     * Records what one exact frozen {@code SYMBOLIC} action observed after
     * its runtime hook either minted a value or retained a propagated one.
     * The requested VM label is descriptive only; downstream authority is
     * derived from the exact expression, never from this label.
     */
    synchronized void recordManualSymbolization(
            SymbolizeAction action, String requestedSymbol,
            List<String> fieldPath, String fieldSignature,
            JsonElement expression, boolean minted, boolean reused) {
        recordManualSymbolization(action, requestedSymbol, fieldPath,
                fieldSignature, expression, minted, reused, "");
    }

    /**
     * The same row, with the concrete value the mint read.
     *
     * <p>One mint publication shape: a configured-source mint states
     * what the field held
     * and a manual one stated nothing, so a root the composer met
     * through a manual input had no recorded value to lower -- on lane
     * VM12 that is DelegationKey.expiryDate, minted as
     * {@code M_J_field_REGION.aaa1cfd7...}, and
     * RECORDED_ROOT_VALUE_UNSTATED was the anchor's last refusal.</p>
     *
     * <p>And it states it whether or not the replay planted at this mint.
     * There WAS a suppression rule -- a replay that wrote a model read the
     * model back, so calling that "recorded" makes a counterfactual the
     * recording -- and the mistake in it is that the value a mint hands
     * here is the one it read BEFORE the plant, which is the recording's.
     * What the session planted is stated by the focus row and by nothing
     * on this row.  Suppressing it left the one root each obligation
     * moves with an empty {@code recordedValue} in every focused session
     * of both kept corpora (hdfs-17960 {@code seq=121}, hdfs-11741's six
     * CLOCK rows), which IMPORT refuses under invariant 8.</p>
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
        row.addProperty("occurrenceId", occurrenceId());
        // WHERE in the region this read stood, captured here because
        // here is where it runs: the row is published at the end of the
        // activation, and the frames are gone by then.  Two reads of one
        // accessor site inside one occurrence differ by the site index's
        // own innermost frame (Identity.eventSiteIndex), not by an
        // ordinal and not by a frame only a replay stands on.
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
            // What THIS execution read at the mint, under both names.
            // A clock is no exception: the seed replay IS the reference
            // execution, so the instant it read is the one the composer's
            // deltas are relative to, and a row that carried the PLAN's
            // instant instead described an execution nobody ran.  A
            // replay that planted `now + skew` still states the instant
            // it READ -- the mint asks for it before the plant -- and the
            // skew itself is the focus row's statement.
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        // The case declared this read a wall clock, so the mint row
        // states it and no reader downstream has to guess a clock from a
        // callee or a site name.  It states WHERE the plan observed the
        // read and nothing about its value: the value is the one above,
        // which is what THIS execution read.
        //
        // The plan's own instant used to be published here as
        // recordedValue.  The seed replay is THE reference execution --
        // the composer's clock deltas are relative to the recordedValue
        // its rows state -- so a row that names the PLAN's instant makes
        // every delta relative to an execution that is not the one the
        // session describes.  A replay that planted `now + skew` states
        // the instant its own mint READ, by the rule above, and the skew
        // is stated by the focus row.
        if (action.declaresWallClockRead()) {
            row.addProperty(InputActionCatalog.DECLARED_WALL_CLOCK, true);
            row.addProperty("eventSeq", action.eventSeq);
        }
        row.addProperty("mintOccurrence",
                mintOccurrence(safe(action.symbol)));
        symbolizedRows.add(row);
        // I4: a decision row carries the clock cells its own term names, and
        // a term names one by the VM SYMBOL this mint installed -- so the
        // cell is filed HERE, where the mint runs, rather than where the
        // root row is published: activations publish innermost first, and a
        // decision of an activation nested inside this one is published
        // before this row exists (11741's removeExpiredKeys closes before
        // the updateKeys rotation whose clock its decisions read).
        //
        // The three statements the root row will carry, off this same row:
        // only a MINT (a reused symbol is another mint's root), only a
        // declared CLOCK, and the port id -- which is the root id of a
        // manual mint, because it states no sourceId of its own.
        if (minted && action.declaresWallClockRead()) {
            String installed = optionalString(row, "rawSymbol");
            RowRuntime.clockCell(installed.isEmpty()
                            ? safe(requestedSymbol) : installed,
                    safe(action.symbol),
                    RowPublication.literal(safe(recordedValue)));
        }
        // And the same rule for the shadow store this mint just made, filed
        // where the mint RUNS for the same reason the clock cell is: an
        // activation nested inside this one publishes before this row
        // exists, and its write log already holds the version the mint
        // installed.  A REUSED symbol is another mint's and is filed by that
        // mint; this row made no store to suppress.
        if (minted) {
            RowRuntime.declaredMintSymbol(RowPlaceholderMint.vmSymbol(row));
        }
    }

    /**
     * Names one refusal at a configured source's mint, as a row.
     *
     * <p>One gap vocabulary: this used to build a second row shape into
     * a list nothing downstream read, so a mint the replay refused was
     * invisible to the claim.  Every one of these means the wave's value
     * was NOT written at the mint the obligation is about, so they are
     * BLOCKING for the session that met them and the subject is the
     * phase the declaration names.</p>
     */
    private void refuseMint(
            edu.uva.liftlab.graphchecker.contract.GapKind kind,
            ConfiguredSourcePhaseContract.Occurrence phase,
            String detail) {
        RowRuntime.gap(kind, edu.uva.liftlab.graphchecker.contract
                        .GapClass.BLOCKING,
                // The declared phase, else this occurrence, else the
                // activation's own token: phaseId and occurrenceId are both
                // read out of the plan with optionalString, so either can
                // be blank, and a blank subject refuses inside Fields.text
                // -- out of the mint hook, into the workload.
                edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank(
                        phase == null ? "" : phase.phaseId(),
                        occurrenceId(), Long.toString(token)),
                safe(detail));
    }

    /**
     * Whether this run can place this mint at the node and epoch the
     * plan addresses, filing the gap that says why not.
     *
     * <p>A configured source names one mint SITE, and the site is
     * reached once per node lifecycle.  The site is not the address: the
     * address is (node, epoch, region, k-th activation), and the epoch
     * is the half nothing was checking.  On hdfs-17960 the flip replay
     * threw inside the workload before it restarted the NameNode, so
     * the only activation it offered was epoch 0 -- and root=false was
     * written there, at the mint the recording made before the restart,
     * instead of at the epoch-1 mint the plan addresses.  The recorded
     * execution was rewritten at a point the wave said nothing
     * about.</p>
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
     * Every node this run can attribute this mint to, at mint time.
     *
     * <p>Three registrations, all the workload's own: the object whose
     * field is being minted, the source this occurrence was entered
     * under, and whatever the thread is carrying now.  The registry is
     * the same one {@link ConcolicTaskPlan#lifecycleMismatch} reads, so
     * the epoch here is the epoch admission compared.</p>
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
     * Why this mint cannot be shown to be the planned node and epoch,
     * or {@code ""}.
     *
     * <p>Deliberately stricter than root admission, and the asymmetry is
     * the point.  Admission admits an activation nothing attributed --
     * absence of evidence is not evidence of another occurrence, and a
     * replay routinely reconstructs a receiver without repeating its
     * alias registration.  A model is different in kind: it <em>rewrites
     * the recorded execution</em>, and doing that at a mint the run
     * cannot place is asserting an occurrence nobody established.  So a
     * mint must be attributed positively, and an unattributed one
     * refuses the model and keeps the value the recording made.</p>
     *
     * <p>This is the hdfs-17960 flip in its general form.  The address is
     * (node, epoch, region, k-th activation); the mint site is reached
     * once per node lifecycle, so the epoch is what tells two mints of
     * one site apart, and root=false landing on the epoch-0 mint
     * rewrote a value the solver had said nothing about.  Refusing on a
     * different epoch closed that where the run attributes the mint;
     * requiring attribution closes it where the run does not.</p>
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
