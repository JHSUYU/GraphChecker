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
import edu.uva.liftlab.graphchecker.contract.Validity;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

final class ActiveRegion {
    final long token;
    final RuntimeTask activation;
    OccurrenceAddress d3Address;
    private boolean activationClaimed;
    long vmRegionEnterEventId;
    final Object receiver;
    final Thread thread;
    final AtomicBoolean finished = new AtomicBoolean();
    JsonObject targetReach;
    boolean abandoned;
    boolean terminalGap;
    private boolean closed;
    volatile long chargedLoopBodies;
    int termedDecisions;
    volatile String cut;
    final Set<String> observedSourceKeys = new LinkedHashSet<>();
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

    final List<JsonObject> symbolizedRows = new ArrayList<>();
    final List<JsonObject> branchMappings = new ArrayList<>();
    final Map<String, SharedStateCapture.Filed> sharedStateRecords =
            new LinkedHashMap<>();
    final Map<String, String> sharedStateRefusals = new LinkedHashMap<>();
    final Set<String> materialized = new LinkedHashSet<>();
    private final Map<String, Object> configurationReads =
            new LinkedHashMap<>();
    private final Set<String> configurationReuses = new LinkedHashSet<>();
    final ConcolicRegionRuntime.OccurrenceCounter
            materializationOccurrences =
            new ConcolicRegionRuntime.OccurrenceCounter();
    final Map<String, Integer> accessorCallOccurrences =
            new LinkedHashMap<>();
    private final LoopBackedgeBudget loopBackedges;
    private final Map<Long, PreparedBranch> preparedBranches =
            new LinkedHashMap<>();
    final VmExpressionTable.Store expressionStore;
    private long preparedBranchSequence;
    int lastPathConditionSize;
    boolean pathRecordingStarted;
    boolean basePaused;

    ActiveRegion(long token, RuntimeTask activation,
                 Object receiver, Thread thread) {
        this.token = token;
        this.activation = activation;
        this.receiver = receiver;
        this.thread = thread;
        this.expressionStore = ConcolicRegionRuntime.workloadExpressionStore;
        this.loopBackedges = new LoopBackedgeBudget();
    }

    void claimActivation() {
        if (activationClaimed) return;
        activationClaimed = true;
        activation.claimActivation();
    }

    void releaseActivation() {
        if (!activationClaimed) return;
        activationClaimed = false;
        activation.releaseActivation();
    }

    String address() {
        return d3Address == null ? "" : d3Address.render();
    }

    private Boolean onZkChain;

    boolean onZkChain() {
        if (onZkChain == null) {
            onZkChain = d3Address != null
                    && MessageDoors.chain().holds(d3Address.render());
        }
        return onZkChain;
    }

    synchronized ReplayLoopResourceCut chargeLoopBody(String loopId,
                                                      int bound) {
        chargedLoopBodies++;
        return loopBackedges.body(loopId, inThisCall(loopId), bound);
    }

    synchronized Error traverseBackedge(String loopId, int bound) {
        chargedLoopBodies++;
        return loopBackedges.traverse(loopId, inThisCall(loopId),
                termedDecisions, bound, ForcedArms.armedOn(this));
    }

    private static String inThisCall(String loopId) {
        return LoopBackedgeBudget.scoped(loopId, Identity.frameToken());
    }

    int recordConcreteDecision(
            String method, int unitIndex, BranchDecision decision) {
        try {
            String site = SiteId.render(method, unitIndex);
            int occurrence = Identity.nextBranchOrdinal(site);
            JsonObject row = BranchObservation.decisionRow(method,
                    unitIndex, occurrence, 0L, decision.outcome(), 0, 0);
            ForcedArms.statesCaller(this, row);
            branchMappings.add(row);
            if (activation.targetTest(site)
                    && activation.targetBranchOccurrence == occurrence) {
                recordTargetReach(site, occurrence, decision.outcome(),
                        Identity.afterLastEvent());
            }
            return occurrence;
        } catch (Throwable ignored) {
            return 0;
        }
    }

    void observeReplayDecision(
            String siteId, int occurrence, BranchDecision decision) {
        if (d3Address == null) return;
        if (FocusedReplay.observeDecision(d3Address, siteId, occurrence,
                decision.outcome)) {
            ConcolicResultPublisher.concludeAtRefusal();
        }
    }

    boolean replayPrefixContradicted() {
        return d3Address != null && FocusedReplay.contradicted(d3Address);
    }

    PreparedBranch prepareBranch(
            String method, int unitIndex, String expression,
            boolean recording) throws Exception {
        String site = SiteId.render(method, unitIndex);
        int occurrence = Identity.nextBranchOrdinal(site);
        long sequence = ++preparedBranchSequence;
        if (sequence > Integer.MAX_VALUE) {
            return null;
        }
        long handle = (sequence << 32)
                | (occurrence & 0xffffffffL);
        PreparedBranch prepared = new PreparedBranch(handle, method,
                unitIndex, expression, occurrence, recording);
        preparedBranches.put(handle, prepared);
        return prepared;
    }

    PreparedBranch takePreparedBranch(long handle) {
        return handle <= 0L ? null : preparedBranches.remove(handle);
    }

    void recordTargetReach(String siteId, int occurrence,
                                   boolean outcome, long vmEventId) {
        if (targetReach != null) return;
        JsonObject reach = new JsonObject();
        reach.addProperty("kind", "TARGET_REACH_EVENT");
        reach.addProperty("siteId", nonNull(siteId));
        reach.addProperty("occurrence", occurrence);
        reach.addProperty("outcome", outcome);
        if (vmEventId > 0L) reach.addProperty("vmEventId", vmEventId);
        targetReach = reach;
    }

    static boolean mintsUnderSymbolicOccurrence(
            ActiveRegion active, String sourceId, String fieldSignature) {
        if (active != null && active.symbolicallyActive()) return true;
        RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                firstNonBlank(nonNull(sourceId), nonNull(fieldSignature)),
                "this configured-source hook fired under "
                        + (active == null ? "none" : active.mintAddress())
                        + ", which is not an occurrence this replay runs"
                        + " symbolically, so the field it stands on holds"
                        + " the literal this execution produced and no root"
                        + " is minted for " + nonNull(sourceId) + " here"
                        + " (field " + nonNull(fieldSignature) + ")");
        return false;
    }

    boolean symbolicallyActive() {
        if (!FocusedReplay.focusedSession()) return true;
        return FocusedReplay.focused(activation.taskId, d3Address);
    }

    private String mintAddress() {
        return firstNonBlank(address(), Long.toString(token))
                + " of region " + nonNull(activation.regionId);
    }

    synchronized RootMint.SourceSiteEntry observeConfiguredSourceEntry(
            String sourceId, String runtimeFieldSignature) {
        CausynthTraceRecorder.ActiveCallSiteContext context =
                CausynthTraceRecorder.currentCallSiteContext();
        List<ConfiguredSourcePhaseContract.Occurrence> declaration =
                new ArrayList<>();
        String site = context == null ? "" : context.siteId();
        for (ConfiguredSourcePhaseContract.Occurrence candidate
                : activation.configuredSourcePhases) {
            if (candidate.sourceId().equals(nonNull(sourceId))
                    && (site.isEmpty()
                    || candidate.siteId().equals(site))) {
                declaration.add(candidate);
            }
        }
        ConfiguredSourcePhaseContract.Occurrence planned =
                declaration.isEmpty() ? ConcolicTaskPlan.configuration()
                        .declaredPhase(nonNull(sourceId)) : null;
        if (declaration.isEmpty() && planned == null) {
            RowRuntime.gap(GapKind.HOOK_UNDECLARED, GapClass.DIAGNOSTIC,
                    mintAddress(), "the hook for " + nonNull(sourceId)
                            + " ran, but no task of this case's plan"
                            + " declares a phase of that source: it is no"
                            + " root of this case, and nothing is minted");
            return null;
        }
        if (context == null) {
            refuseMint(GapKind.DECLARATION_MISSING,
                    declaration.isEmpty() ? null : declaration.get(0),
                    "the PUBLISH hook for " + nonNull(sourceId)
                            + " ran under no active call site, so the"
                            + " mint is at no declared phase");
            return null;
        }
        if (declaration.isEmpty()
                && planned.category() == RootCategory.CONFIG) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    mintAddress(), "the configuration read of "
                            + nonNull(sourceId) + " at " + site + " is outside"
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
        ConfiguredSourcePhaseContract.Occurrence matched =
                declaration.get(0);
        if (!matched.fieldSignature().equals(
                nonNull(runtimeFieldSignature))
                || !matched.runtimeDeclaredCallee().equals(
                context.declaredCallee())) {
            refuseMint(GapKind.DECLARATION_MISSING, matched,
                    "the runtime field and callee differ from the ones"
                            + " the catalog site declares");
            return null;
        }
        return new RootMint.SourceSiteEntry(matched, site);
    }

    synchronized Object configurationRead(String sourceId, String symbol) {
        Object box = configurationReads.get(sourceId);
        if (box != null) configurationReuses.add(symbol);
        return box;
    }

    synchronized boolean configurationReused(String symbol) {
        return configurationReuses.contains(symbol);
    }

    synchronized void configurationMinted(String sourceId, Object box) {
        configurationReads.putIfAbsent(sourceId, box);
    }

    synchronized void recordConfiguredSourceMint(
            RootMint.SourceSiteEntry entry, String sourceId,
            String fieldSignature, String symbol,
            JsonElement expression, boolean reused,
            String recordedValue) {
        JsonObject row = new JsonObject();
        if (recordedValue != null && !recordedValue.isEmpty()) {
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        row.addProperty("sourceId", nonNull(sourceId));
        row.addProperty("sourcePhaseId", entry.phaseId());
        row.addProperty("siteId", entry.siteId);
        row.addProperty("fieldSignature", nonNull(fieldSignature));
        row.addProperty("symbol", nonNull(symbol));
        row.add("expression", expression == null
                ? JsonNull.INSTANCE : expression);
        row.addProperty("reused", reused);
        row.addProperty("category", entry.category().name());
        configDomain(row, entry.domainMin(), entry.domainMax(),
                entry.valid(), recordedValue);
        row.addProperty("mintOccurrence",
                mintOccurrence(nonNull(sourceId)));
        symbolizedRows.add(row);
    }

    static void configDomain(JsonObject row, String staticMin,
                             String staticMax, Validity valid,
                             String recordedValue) {
        String min = nonNull(staticMin).trim();
        String max = nonNull(staticMax).trim();
        String value = nonNull(recordedValue).trim();
        Validity kept = Validity.ANY;
        if (valid != null && valid != Validity.ANY
                && INTEGER.matcher(value).matches()
                && !valid.admits(new BigInteger(value))) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    optionalString(row, "sourceId"), "the value this"
                            + " configuration's mint read (" + value + ")"
                            + " lies outside what its validation admits ["
                            + (valid.min() == null ? "" : valid.min()) + ", "
                            + (valid.max() == null ? "" : valid.max())
                            + "] by " + valid.by() + ", so that validation"
                            + " bounds nothing");
        } else if (valid != null) {
            valid.write(row);
            kept = valid;
        }
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
                kept.clip(read.min(new BigInteger(min))).toString());
        row.addProperty("domainMax",
                kept.clip(read.max(new BigInteger(max))).toString());
    }

    private static final java.util.regex.Pattern INTEGER =
            java.util.regex.Pattern.compile("-?[0-9]+");

    private String mintOccurrence(String rootId) {
        return rootOwner(rootId).address();
    }

    ActiveRegion rootOwner(String rootId) {
        ActiveRegion owner = ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Root(nonNull(rootId)));
        return owner == null ? this : owner;
    }

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
        row.addProperty("siteIndex", Identity.siteIndex().render());
        row.addProperty("symbol", nonNull(requestedSymbol));
        JsonArray encodedPath = new JsonArray();
        for (String segment : fieldPath == null
                ? Collections.<String>emptyList() : fieldPath) {
            encodedPath.add(nonNull(segment));
        }
        row.add("fieldPath", encodedPath);
        row.addProperty("fieldSignature", nonNull(fieldSignature));
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
            row.addProperty("observedValue", recordedValue);
            row.addProperty("recordedValue", recordedValue);
        }
        row.addProperty("category", action.category().name());
        if (!action.configSource.isEmpty()) {
            row.addProperty("sourceId", action.configSource);
            configDomain(row, action.configDomainMin,
                    action.configDomainMax, action.configValid,
                    recordedValue);
        }
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
                mintOccurrence(nonNull(action.symbol)));
        symbolizedRows.add(row);
        if (minted && action.declaresWallClockRead()) {
            String installed = optionalString(row, "rawSymbol");
            RowRuntime.clockCell(installed.isEmpty()
                            ? nonNull(requestedSymbol) : installed,
                    nonNull(action.symbol),
                    RowPublication.literal(nonNull(recordedValue)));
        }
    }

    private void refuseMint(
            GapKind kind,
            ConfiguredSourcePhaseContract.Occurrence phase,
            String detail) {
        RowRuntime.gap(kind, GapClass.BLOCKING,
                firstNonBlank(
                        phase == null ? "" : phase.phaseId(),
                        address(), Long.toString(token)),
                nonNull(detail));
    }

    synchronized boolean mintIsPlaceable(Object mintOwner) {
        String unattributed = mintIsNotThePlannedNode(mintOwner);
        if (unattributed.isEmpty()) return true;
        refuseMint(mintAttribution(mintOwner).isEmpty()
                        ? GapKind.MINT_UNATTRIBUTED
                        : GapKind.EPOCH_UNMATCHED, null, unattributed);
        return false;
    }

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

    private String mintIsNotThePlannedNode(Object mintOwner) {
        String planned = nonNull(activation.sourceKey);
        if (!RuntimeTraceContext.declaresEpoch(planned)) return "";
        Set<String> attributed = mintAttribution(mintOwner);
        if (attributed.contains(planned)) return "";
        if (attributed.isEmpty()) {
            return "the registry attributes this mint to no node, so it "
                    + "cannot be shown to be " + planned + "; the "
                    + "recorded value stands";
        }
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
