package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.ClockRootPhysics;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.concolic.RpcExpressionHandoff;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SymbolicPropagationClosure;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionIr;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionTable;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.concolic.SmtModelValueCodec;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;

import edu.uva.liftlab.graphchecker.contract.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.RawSharedStateReadOut;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.SharedStateResult;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.math.BigInteger;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.integralRange;
import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.beginLiveSelectedRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.beginSelectedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.addResultIdentity;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.buildCompletedResult;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.haltWhenCampaignSettled;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.endSelectedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.jsonObjectEnvelope;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.endLiveSelectedRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.submitCompletedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.writeSkipped;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.captureRecordedSharedStateRaw;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.evidenceIdentity;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.contiguousConditionIndices;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.vmEventConditionIndices;

/**
 * Runtime bridge injected at symbolic-region roots for the second (concolic)
 * unit-test execution.
 *
 * <p>The class uses reflection for the custom {@code java.lang.System} APIs so
 * GraphChecker itself remains buildable and testable on an ordinary JDK.</p>
 */
public final class ConcolicRegionRuntime {
    private static final String MANUAL_INPUT_OBSERVATION_KIND =
            "MANUAL_SYMBOLIC_INPUT_OBSERVATION";
    private static final String MANUAL_INPUT_OBSERVATION_AUTHORITY =
            "EXACT_PLANNED_SYMBOLIZATION_ACTION_V1";
    static final String CONFIGURED_SOURCE_PHASE_OBSERVATIONS =
            "configuredSourcePhaseObservations";
    static final String CONFIGURED_SOURCE_PHASE_GAPS =
            "configuredSourcePhaseGaps";
    static final Pattern DEFAULT_EXECUTOR_THREAD_NAME =
            Pattern.compile("^pool-[0-9]+-thread-([0-9]+)$");
    static final Pattern DEFAULT_OBJECT_IDENTITY_THREAD_NAME =
            Pattern.compile("^([A-Za-z_$][A-Za-z0-9_$.]*?)@"
                    + "[0-9a-fA-F]+$");
    static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    private static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    /** Monotonic ordinal of one recorded-evidence read-out batch. */
    private static final AtomicLong EVIDENCE_SNAPSHOTS = new AtomicLong();
    static final String HALT_AFTER_SELECTED_RESULT_PROPERTY =
            "causynth.concolic.halt.after.selected.result";
    /** Why an activation never published a region result. */
    static final String SKIP_NOT_STARTED = "NOT_STARTED";
    static final String SKIP_REPLAY_PREFIX_UNMATCHED =
            "REPLAY_PREFIX_UNMATCHED";
    static final String SKIP_UNAPPLIED_MODEL_ASSIGNMENT =
            "UNAPPLIED_MODEL_ASSIGNMENT";
    static final String SKIP_RESULT_PUBLICATION_FAILED =
            "RESULT_PUBLICATION_FAILED";
    /**
     * A candidate ran to its terminal and was not the occurrence its plan row
     * addressed: it ran on another source, or inside another request scope.
     */
    static final String SKIP_OCCURRENCE_ANCHOR_UNMATCHED =
            "OCCURRENCE_ANCHOR_UNMATCHED";
    /** The source this occurrence is anchored on never existed in this run. */
    static final String SKIP_ANCHOR_SOURCE_NEVER_EXISTED =
            "ANCHOR_EPOCH_NOT_REACHED";
    /**
     * A bounded loop address ran, but the response exchange selected as its
     * causal identity never occurred before the workload ended.
     */
    /**
     * The planned root never executed in this replay.
     *
     * <p>Not the same as an address several activations failed to answer:
     * there was no activation at all, compatible or otherwise.  Saying so is
     * what keeps a planned task that simply did not run from reaching the
     * importer as silence.</p>
     */
    static final String SKIP_ROOT_NEVER_EXECUTED =
            "ROOT_NEVER_EXECUTED";
    /**
     * The region root was still running when the workload ended, so this
     * occurrence never reached {@code NORMAL}, {@code THROW} or a bounded
     * {@code CUT}.
     */
    /**
     * A loop-body region reached its bounded occurrence set (K_L rows) and
     * this and later iterations run concretely without capture.  Not a
     * failure: the occurrence set is bounded, not silently truncated, and the
     * composer reads this marker to know so.
     */
    static final String SKIP_LOOP_OCCURRENCE_BEYOND_BOUND =
            "LOOP_OCCURRENCE_BEYOND_BOUND";
    static final String SKIP_LOOP_OCCURRENCES_BOUNDED =
            "LOOP_OCCURRENCES_BOUNDED";
    static final String SKIP_TERMINAL_NEVER_REACHED =
            "TERMINAL_NEVER_REACHED";
    /** Emits one line per replay milestone to stderr. */
    static final String DIAGNOSTICS_PROPERTY =
            "causynth.concolic.diagnostics";
    private static volatile Boolean diagnostics;
    static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    /**
     * Selected activations on this Java thread, innermost first.
     *
     * <p>The custom VM already keeps the matching native region stack.  The
     * Java runtime must preserve that nesting as well: a selected helper can
     * execute inside a selected caller while both share the same propagated
     * expression universe and thread-local path condition.</p>
     */
    private static final ThreadLocal<Deque<Long>> CURRENT_TOKENS =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<>();
                }
            };
    private static final ThreadLocal<Integer> OBSERVATION_PAUSE_DEPTH =
            ThreadLocal.withInitial(() -> 0);
    /**
     * Dynamic root-invocation ownership used only by injected entry/exit
     * hooks.
     */
    private static final ThreadLocal<Deque<RootInvocationFrame>>
            ROOT_INVOCATION_FRAMES = new ThreadLocal<Deque<RootInvocationFrame>>() {
        @Override
        protected Deque<RootInvocationFrame> initialValue() {
            return new ArrayDeque<>();
                }
            };
    /** Enclosing method calls that own LOOP_BODY_ROOT iteration frames. */
    private static final ThreadLocal<Deque<LoopRootInvocationContext>>
            LOOP_ROOT_INVOCATIONS =
            new ThreadLocal<Deque<LoopRootInvocationContext>>() {
                @Override
                protected Deque<LoopRootInvocationContext> initialValue() {
                    return new ArrayDeque<>();
                }
            };
    static final ThreadLocal<AccessorCallContext>
            CURRENT_ACCESSOR_CALL_CONTEXT = new ThreadLocal<>();
    private static final Pattern BRANCH_OPERATOR = Pattern.compile(
            "(?:^|\\s)(==|!=|<=|>=|<|>)(?:\\s|$)");
    /** Session this JVM opened for its workload, or zero when it opened none. */
    static volatile long workloadSessionId;
    /**
     * Content-addressed expression universe of the current VM workload
     * session.  Native expression ids are session-wide, so decoding them in
     * one store per region needlessly rebuilt the same propagated DAG at every
     * hop and every concurrent occurrence.
     */
    private static volatile VmExpressionTable.Store workloadExpressionStore =
            new VmExpressionTable.Store();
    private ConcolicRegionRuntime() {
    }

    /**
     * Starts an observation-only subtree before an instrumented method calls
     * back into this runtime. Soot emits this boundary in the analyzed method
     * so runtime/Gson frames are entered while symbolic propagation is muted.
     * The VM still keeps structural shadow frames balanced.
     */
    public static void pauseObservation() {
        OBSERVATION_PAUSE_DEPTH.set(OBSERVATION_PAUSE_DEPTH.get() + 1);
        try {
            engine().pausePathCondition();
        } catch (Throwable ignored) {
            // A missing/inactive engine is already handled by the region hook.
        }
    }

    /** Completes the observation-only subtree started by {@link #pauseObservation()}. */
    public static void resumeObservation() {
        int depth = OBSERVATION_PAUSE_DEPTH.get();
        if (depth <= 1) OBSERVATION_PAUSE_DEPTH.remove();
        else OBSERVATION_PAUSE_DEPTH.set(depth - 1);
        try {
            engine().resumePathCondition();
        } catch (Throwable ignored) {
            // Resume is intentionally harmless when no region is active.
        }
    }

    /**
     * Opens the exact static call-site context for a configured-source hook.
     */
    public static long enterConfiguredSourcePhaseCallSite(
            String method, int unitIndex, String declaredCallee) {
        try {
            ActiveRegion active = activeRegion();
            long replayOwnerId = active == null ? 0L : active.token;
            return CausynthTraceRecorder.beginCall(replayOwnerId, safe(method),
                    unitIndex, safe(declaredCallee), null);
        } catch (Throwable ignored) {
            // Evidence bookkeeping must never change workload behavior.  A
            // zero id makes both matching close hooks no-ops.
            return 0L;
        }
    }

    /** Closes the context opened by {@link #enterConfiguredSourcePhaseCallSite}. */
    public static void exitConfiguredSourcePhaseCallSite(
            long invocationId, Object returnValue, String primitiveValue) {
        if (invocationId <= 0L) return;
        try {
            CausynthTraceRecorder.endCall(invocationId, returnValue,
                    safe(primitiveValue));
        } catch (Throwable ignored) {
            // See enterConfiguredSourcePhaseCallSite: trace failure is not an
            // application failure.
        }
    }

    /** Closes a configured-source call-site on the invocation's throw edge. */
    public static void throwConfiguredSourcePhaseCallSite(long invocationId) {
        if (invocationId <= 0L) return;
        try {
            CausynthTraceRecorder.throwCall(invocationId);
        } catch (Throwable ignored) {
            // Keep the original workload exception as the only visible one.
        }
    }

    /**
     * Mutes this layer's own bookkeeping for the duration of one evidence
     * call, and must be paired with {@link #endBookkeeping()} in a finally.
     *
     * <p>It has to be: this layer reflects, parses JSON, builds strings and
     * walks collections holding the very objects the workload symbolized, and
     * an unmuted call records hundreds of conditions of GraphChecker's own
     * control flow into the workload's path condition and mints session
     * expressions for GraphChecker's own strings.</p>
     */
    static void beginBookkeeping() {
        pauseObservation();
    }

    /** Ends the muted subtree {@link #beginBookkeeping()} opened. */
    static void endBookkeeping() {
        resumeObservation();
    }

    /**
     * The innermost activation, or null while observation is muted: a hook
     * reached from GraphChecker's own bookkeeping accounts for nothing.
     */
    private static ActiveRegion observingActiveRegion() {
        return OBSERVATION_PAUSE_DEPTH.get() > 0 ? null : activeRegion();
    }

    /**
     * Accounts for one attempted traversal of an instrumented normal CFG
     * backedge.
     */
    public static void checkLoopBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        ActiveRegion active = observingActiveRegion();
        if (active == null) return;

        ConcolicVmBroker api = engine();
        boolean paused = false;
        LoopBoundCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            String edge = safe(backedgeId);
            int runtimeMax = instrumentedMaxTraversals;
            if (edge.isEmpty() || !active.activation.loopBound
                    .acceptsInstrumentedBound(runtimeMax)) {
                cut = active.loopBoundCut(edge, runtimeMax,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            } else {
                long attempted = active.loopBackedges.recordTraversal(edge);
                if (attempted >= runtimeMax) {
                    cut = active.loopBoundCut(edge, runtimeMax,
                            "MAX_LOOP_BODY_ITERATIONS_REACHED");
                }
            }
        } catch (Throwable failure) {
            cut = active.loopBoundCut(safe(backedgeId),
                    instrumentedMaxTraversals,
                    "BOUND_HOOK_FAILURE:" + rootCause(failure));
        } finally {
            if (resumeLoopAccounting(active, api, paused) && cut == null) {
                cut = active.loopBoundCut(safe(backedgeId),
                        instrumentedMaxTraversals,
                        "BOUND_HOOK_RESUME_FAILURE");
            }
        }
        endAtCut(active, cut);
    }

    /**
     * Charges one loop body to the replay resource cap without consulting the
     * unroll bound.
     */
    public static void checkReplayLoopBody(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = observingActiveRegion();
        if (active == null) return;

        ConcolicVmBroker api = engine();
        boolean paused = false;
        ReplayLoopResourceCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            String loop = safe(loopId);
            if (loop.isEmpty() || instrumentedMaxTraversals
                    != active.activation.loopBound.maxBackedgeTraversals()) {
                // The class was instrumented under a different policy, so its
                // loop identities cannot be trusted to account for anything.
                cut = new ReplayLoopResourceCut(loop, 0, 0L);
                active.replayResourceCut = cut.toJson();
                active.addUnresolvedOnce(
                        ReplayLoopResourceCut.REASON
                                + ":INSTRUMENTATION_POLICY_MISMATCH:" + loop);
            } else {
                cut = active.chargeLoopBody(loop);
            }
        } catch (Throwable failure) {
            active.addUnresolvedOnce("replay loop resource hook failed: "
                    + rootCause(failure));
        } finally {
            resumeLoopAccounting(active, api, paused);
        }
        endAtCut(active, cut);
    }

    /**
     * Records the exact array length supplying one fixed-count loop
     * invocation.
     */
    public static void recordLoopCardinality(
            String loopId, int cardinality) {
        ActiveRegion active = observingActiveRegion();
        if (active == null) return;
        beginBookkeeping();
        try {
            active.recordLoopCardinality(safe(loopId), cardinality);
        } finally {
            endBookkeeping();
        }
    }

    /** Ends the current dynamic occurrence of one fixed-count loop. */
    public static void completeLoopCardinality(String loopId) {
        ActiveRegion active = observingActiveRegion();
        if (active == null) return;
        beginBookkeeping();
        try {
            active.completeLoopCardinality(safe(loopId));
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Restores the path condition a loop-accounting hook paused.  True when
     * the resume was lost, leaving the workload's own observation muted.
     */
    private static boolean resumeLoopAccounting(
            ActiveRegion active, ConcolicVmBroker api, boolean paused) {
        if (!paused) return false;
        try {
            api.resumePathCondition();
            return false;
        } catch (Throwable failure) {
            active.addUnresolvedOnce("loop-bound path-condition resume "
                    + "failed: " + rootCause(failure));
            return true;
        }
    }

    /** Publishes the bounded prefix and detaches symbolic observation. */
    private static void endAtCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        diag("REGION_CUT", cut.toString());
        finish(active.token, "CUT", "", null);
    }

    /**
     * Opens the exact accessor invocation selected by one activation's
     * symbolize action.
     *
     * <p>Soot initializes the token to zero and always invokes the exit hook,
     * so disabled and unselected executions remain harmless.</p>
     */
    public static long enterAccessorCallContext(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object receiver) {
        try {
            ActiveRegion active = activeRegion();
            String caller = safe(callerMethod);
            String site = safe(callSiteId);
            String callee = safe(declaredCallee);
            if (active == null || caller.isEmpty() || callUnitIndex < 0
                    || callee.isEmpty()
                    || !site.equals(SiteId.render(caller, callUnitIndex))) {
                return 0L;
            }
            AccessorCallContext previous =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (previous != null && previous.regionToken != active.token) {
                // A context may never cross a region activation.
                CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                previous = null;
            }
            long contextToken = ACCESSOR_CONTEXT_TOKEN_COUNTER
                    .incrementAndGet();
            String occurrenceKey = safe(caller) + "\n" + safe(site) + "\n"
                    + safe(callee);
            int occurrence = active.accessorCallOccurrences.getOrDefault(
                    occurrenceKey, 0) + 1;
            active.accessorCallOccurrences.put(occurrenceKey, occurrence);
            CURRENT_ACCESSOR_CALL_CONTEXT.set(new AccessorCallContext(
                    contextToken, active.token, Thread.currentThread(),
                    caller, callUnitIndex, site, callee, receiver, occurrence,
                    previous));
            return contextToken;
        } catch (Throwable ignored) {
            // Instrumentation hooks must not perturb the workload.
            return 0L;
        }
    }

    /** Closes a lightweight accessor scope on normal or exceptional return. */
    public static void exitAccessorCallContext(long contextToken) {
        if (contextToken == 0L) return;
        try {
            AccessorCallContext current =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (current == null) return;
            if (current.contextToken == contextToken) {
                if (current.previous == null) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                } else {
                    CURRENT_ACCESSOR_CALL_CONTEXT.set(current.previous);
                }
                return;
            }
            // Out-of-order close means malformed instrumentation or a missed
            // exceptional edge.
            for (AccessorCallContext cursor = current; cursor != null;
                 cursor = cursor.previous) {
                if (cursor.contextToken == contextToken) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                    return;
                }
            }
        } catch (Throwable ignored) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        }
    }


    /**
     * Opens the workload-wide symbolic session that outlives every individual
     * region in this JVM.
     *
     * @return an empty string on success, otherwise a named diagnostic
     */
    public static String openWorkloadSession() {
        if (configuration().tasks.isEmpty()) {
            workloadExpressionStore = new VmExpressionTable.Store();
            return "";
        }
        ConcolicVmBroker api = engine();
        api.requireCurrentCapabilities();
        final long status;
        try {
            status = api.openWorkloadSession();
        } catch (Throwable failure) {
            return "WORKLOAD_SESSION_OPEN_FAILED: " + rootCause(failure);
        }
        if (status <= 0L) {
            return "WORKLOAD_SESSION_OPEN_REFUSED: "
                    + workloadSessionStatusName(status) + " "
                    + api.workloadSessionStatus();
        }
        SymbolicMessageEnvelope.clear();
        workloadExpressionStore = new VmExpressionTable.Store();
        workloadSessionId = status;
        return "";
    }

    /**
     * Closes the session opened by {@link #openWorkloadSession}.
     *
     * @return an empty string on success or when nothing was opened, otherwise
     * a named diagnostic
     */
    public static String closeWorkloadSession() {
        // Closing the workload is the general durability boundary, regardless
        // of which launcher owns it.
        awaitSelectedResultPublications();
        long sessionId = workloadSessionId;
        if (sessionId == 0L) {
            workloadExpressionStore = new VmExpressionTable.Store();
            return "";
        }
        ConcolicVmBroker api = engine();
        final long status;
        try {
            status = api.closeWorkloadSession();
        } catch (Throwable failure) {
            return "WORKLOAD_SESSION_CLOSE_FAILED: " + rootCause(failure);
        }
        if (status != 0L) {
            return "WORKLOAD_SESSION_CLOSE_REFUSED: "
                    + workloadSessionStatusName(status)
                    + " sessionId=" + sessionId + " "
                    + api.workloadSessionStatus();
        }
        SymbolicMessageEnvelope.clear();
        workloadSessionId = 0L;
        workloadExpressionStore = new VmExpressionTable.Store();
        return "";
    }

    /**
     * Waits until every selected activation has durably closed its result
     * record or reported a write failure.
     *
     * <p>Called from outside this class: a launcher that owns no workload
     * session drives the durability barrier directly, the way the workload
     * checkouts call {@link #symbolizeConfiguredSourceField}.  The work
     * itself belongs to {@code ConcolicResultPublisher}; this is the driver
     * entry point that names it.</p>
     */
    public static void awaitSelectedResultPublications() {
        ConcolicResultPublisher.awaitSelectedResultPublications();
    }

    private static String workloadSessionStatusName(long status) {
        if (status == 0L) return "OK";
        if (status == -1L) return "ALREADY_OPEN";
        if (status == -2L) return "NOT_OPEN";
        if (status == -3L) return "MEMBERS_REMAIN";
        if (status == -4L) return "CLOSING";
        return "UNNAMED_STATUS(" + status + ")";
    }

    /**
     * Admits the one planned occurrence this root invocation will execute.
     *
     * @return the started occurrence, or {@code null} when nothing was
     *         admitted or it could not be started
     */
    private static ActiveRegion admitRegion(
            ConcolicTaskPlan config, String rootHookGroupKey,
            String rootMethod, Object receiver, Object[] rootArguments) {
        if (config.tasks.isEmpty() || rootMethod == null) {
            return null;
        }
        RuntimeTask admitted = selectTask(config, rootHookGroupKey,
                rootMethod, receiver, rootArguments);
        if (admitted == null) return null;
        if (boundedLoopOccurrenceCut(admitted)) {
            // The bounded loop's captured occurrence set is full: release the
            // candidate so the next iteration re-selects and re-caps, and run
            // this iteration concretely.
            config.releaseCandidate(admitted);
            return null;
        }
        return startSymbolicRegion(admitted, receiver);
    }

    /**
     * Decides which planned occurrence this root invocation admits, muted.
     *
     * <p>The decision itself is this bridge's own control flow over the
     * workload's own objects: {@code RootContextSelector.matches} compares the
     * root receiver against {@code null} and against a declared class, and a
     * campaign instruments one entry hook per plan row, so every later hook on
     * a thread that already holds a selected symbolic object evaluates that
     * comparison again.</p>
     */
    private static RuntimeTask selectTask(ConcolicTaskPlan config,
                                          String rootHookGroupKey,
                                          String rootMethod,
                                          Object receiver,
                                          Object[] rootArguments) {
        beginBookkeeping();
        try {
            return config.select(rootHookGroupKey, rootMethod, receiver,
                    rootArguments);
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Whether this admission is a bounded cut of a loop-body region whose
     * captured occurrence set is already full.
     *
     * <p>When it is, the one region marker is written once and the caller
     * runs the iteration concretely: no VM region, no symbolization, no
     * capture, no occurrence row -- the fast path a bounded inner loop takes
     * past {@code checkLoopBackedge}.  Hadoop still runs every heartbeat; we
     * only stop capturing after K_L.</p>
     */
    private static boolean boundedLoopOccurrenceCut(RuntimeTask admitted) {
        if (!admitted.cutsBoundedLoopOccurrence()) return false;
        // The bound records turns; the plan addresses one of them by k.  A k
        // past the bound names an activation no replay can reach, which is a
        // gap rather than a turn quietly missed.
        if (admitted.addressesOccurrenceBeyondBound()
                && admitted.claimLoopBoundGapMarker()) {
            JsonObject beyond = new JsonObject();
            beyond.addProperty("plannedOccurrenceId", admitted.occurrenceId);
            beyond.addProperty("regionId", admitted.regionId);
            beyond.addProperty("addressedOccurrence",
                    admitted.address.ordinal());
            beyond.addProperty("boundedAt", admitted.loopOccurrenceBudget);
            writeSkipped(admitted, SKIP_LOOP_OCCURRENCE_BEYOND_BOUND,
                    "this task addresses activation "
                            + admitted.address.ordinal() + " of a loop the "
                            + "instrumentation records "
                            + admitted.loopOccurrenceBudget + " turns of, so "
                            + "the activation it names cannot be reached",
                    beyond);
        }
        if (admitted.claimLoopBoundCutMarker()) {
            int bound = admitted.loopOccurrenceBudget;
            JsonObject evidence = new JsonObject();
            evidence.addProperty("plannedOccurrenceId", admitted.occurrenceId);
            evidence.addProperty("regionId", admitted.regionId);
            evidence.addProperty("boundedAt", bound);
            String reason = "loop-body region occurrence set bounded at K_L="
                    + bound + "; further iterations run concretely without "
                    + "capture";
            writeSkipped(admitted, SKIP_LOOP_OCCURRENCES_BOUNDED, reason,
                    evidence);
        }
        return true;
    }

    /** Starts one planned region occurrence. */
    private static ActiveRegion startSymbolicRegion(
            RuntimeTask admitted, Object receiver) {
        beginLiveSelectedRegion();
        ConcolicVmBroker api = engine();
        boolean engineStarted = false;
        boolean pathConditionPaused = false;
        boolean javaRegionPushed = false;
        ActiveRegion active = null;
        try {
            api.start(admitted.regionId, admitted.taskId);
            engineStarted = true;
            // Region setup performs reflection, collection lookups and JSON-
            // safe bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
            ActiveRegion enclosing = activeRegion();
            active = new ActiveRegion(TOKEN_COUNTER.incrementAndGet(),
                    admitted, receiver, Thread.currentThread());
            // A nested region starts with the symbolic state already carried
            // by its caller.  Its local branches must therefore open
            // immediately even when it mints no new task-local root.
            if (enclosing != null && enclosing.pathRecordingStarted) {
                active.pathRecordingStarted = true;
            }
            active.activationOrdinal = admitted.nextActivationOrdinal();
            LoopRootInvocationContext enclosingInvocation =
                    enclosingLoopRoot(admitted);
            if (enclosingInvocation != null) {
                active.enclosingInvocationEvent = enclosingInvocation.token;
                active.enclosingInvocationThread =
                        enclosingInvocation.threadName;
                active.enclosingInvocationOrdinal =
                        enclosingInvocation.ordinalOf(admitted.taskId);
            }
            ACTIVE.put(active.token, active);
            pushActiveRegion(active);
            javaRegionPushed = true;
            active.vmContextId = api.currentContextId();
            if (active.vmContextId <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no context id");
            }
            active.vmRegionEnterEventId = api.currentRegionEnterEventId();
            if (active.vmRegionEnterEventId <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no region-entry "
                                + "event id");
            }
            // A delivery can establish the causal request immediately before
            // the selected handler entry.
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            SourceRef receiverSource = RuntimeTraceContext.sourceFor(receiver);
            if (receiverSource != null) {
                observeCausalSource(receiverSource.key());
            } else if (context.source != null
                    && RuntimeTraceContext.sameSourceIdentity(
                    admitted.sourceKey, context.source.key())) {
                observeCausalSource(context.source.key());
            }
            prepare(active);
            diag("REGION_START", "token=" + active.token
                    + " task=" + safe(admitted.taskId)
                    + " source=" + safe(admitted.sourceKey)
                    + " region=" + safe(admitted.regionId));
            api.resumePathCondition();
            pathConditionPaused = false;
            return active;
        } catch (Throwable throwable) {
            if (active != null) {
                ACTIVE.remove(active.token);
                if (javaRegionPushed) popActiveRegion(active);
                active.releaseActivationOrdinal();
            }
            if (engineStarted) {
                if (pathConditionPaused) {
                    // Best effort only: cleanupAfterFailure is also valid while recording
                    // is paused, but balancing the API keeps diagnostics clear.
                    try {
                        api.resumePathCondition();
                    } catch (Throwable ignored) {
                        // cleanupAfterFailure below owns the definitive cleanup.
                    }
                }
                api.cleanupAfterFailure();
            }
            writeSkipped(admitted, SKIP_NOT_STARTED,
                    "engine start failed: " + rootCause(throwable), null);
            configuration().releaseCandidate(admitted);
            endLiveSelectedRegion();
            return null;
        }
    }

    /** Performs the declared entry setup for one selected occurrence. */
    private static void prepare(ActiveRegion active) {
        if (active.prepared) return;
        active.prepared = true;
        RuntimeTask task = active.activation;
        symbolizeReceiverFields(active, task, engine());
    }
    /** Instrumentation-facing root entry. */
    public static long enterRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        RootHookGroup group = config.rootHookGroup(
                instrumentationSelector, rootMethod);
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        // A plan may contain several dynamic occurrences rooted at the same
        // Java method.  Instrumentation emits one hook for each plan row, but
        // one concrete method invocation is one logical activation.  The
        // first physical hook dispatches the whole group even when no task is
        // admitted; every remaining hook at that same entry is transparent.
        for (RootInvocationFrame existing : frames) {
            if (existing.claimsSiblingHook(group.key)) {
                frames.push(new RootInvocationFrame(instrumentationSelector,
                        rootMethod, group.key, 0, 0L));
                return 0L;
            }
        }
        RootInvocationFrame frame = new RootInvocationFrame(
                instrumentationSelector, rootMethod, group.key,
                Math.max(0, group.hookCount - 1), 0L);
        frames.push(frame);
        ActiveRegion active = admitRegion(config, group.key, rootMethod,
                receiver, rootArguments);
        long token = active == null ? 0L : active.token;
        frame.token = token;
        return token;
    }

    /**
     * Opens the lightweight enclosing call that addresses LOOP_BODY_ROOT
     * iterations. The outer invocation is counted once; individual body
     * entries only consult this context and never advance that address.
     */
    public static long enterLoopRootInvocationFrame(
            String instrumentationSelector, String rootMethod,
            Object receiver, Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        RootHookGroup group = config.loopRootHookGroup(
                instrumentationSelector, rootMethod);
        Deque<LoopRootInvocationContext> contexts =
                LOOP_ROOT_INVOCATIONS.get();
        for (LoopRootInvocationContext existing : contexts) {
            if (existing.claimsSiblingHook(group.key)) return 0L;
        }
        // The entry event of this enclosing invocation, minted before the
        // plan is asked, because it is what the plan binds a loop task to:
        // the bodies of one occurrence are the bodies of ONE enclosing
        // activation, and a second one is a second k.
        long token = TOKEN_COUNTER.incrementAndGet();
        Map<String, Integer> admittedTasks = config.addressLoopRootInvocation(
                group.key, rootMethod, receiver, rootArguments, token);
        contexts.push(new LoopRootInvocationContext(token, group.key,
                Math.max(0, group.hookCount - 1), admittedTasks));
        return token;
    }

    /** Closes one enclosing LOOP_BODY_ROOT method call. */
    public static void exitLoopRootInvocationFrame(long token) {
        if (token == 0L) return;
        try {
            Deque<LoopRootInvocationContext> contexts =
                    LOOP_ROOT_INVOCATIONS.get();
            LoopRootInvocationContext context = contexts.peek();
            if (context == null || context.token != token) return;
            contexts.pop();
            if (contexts.isEmpty()) LOOP_ROOT_INVOCATIONS.remove();
        } catch (Throwable ignored) {
            // Runtime bookkeeping must not alter a workload terminal.
        }
    }

    /** Exceptional counterpart of {@link #exitLoopRootInvocationFrame}. */
    public static void throwLoopRootInvocationFrame(
            long token, Throwable throwable) {
        exitLoopRootInvocationFrame(token);
    }

    /** Whether the nearest matching outer call owns this loop task. */
    static boolean enclosingLoopRootAdmits(RuntimeTask task) {
        return enclosingLoopRoot(task) != null;
    }

    /**
     * The enclosing invocation on this thread that owns {@code task}, or
     * {@code null}.
     *
     * <p>One loop task's bodies belong to exactly one of these -- the
     * invocation it was admitted for -- and the row it publishes names
     * which, so "two enclosing invocations, one occurrence" is a statement
     * the corpus can contradict rather than an inference from thread
     * names.</p>
     */
    static LoopRootInvocationContext enclosingLoopRoot(RuntimeTask task) {
        if (task == null || !task.loopBodyRoot) return null;
        for (LoopRootInvocationContext context
                : LOOP_ROOT_INVOCATIONS.get()) {
            if (!context.groupKey.equals(task.loopRootHookGroupKey())) {
                continue;
            }
            return context.ordinalByTaskId.containsKey(task.taskId)
                    ? context : null;
        }
        return null;
    }

    /** Null-safe equality for either string naming one root hook. */
    static boolean sameHookIdentity(String left, String right) {
        return left == null ? right == null : left.equals(right);
    }

    /**
     * Called once per Java argument immediately after
     * {@link #enterRegionFrame}.
     */
    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) {
            return;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))
                    || action.index != argumentIndex) {
                continue;
            }
            if (value == null) {
                if (active.hasAppliedExactNullReferenceAssignment(action)) {
                    // The exact model assignment has already replaced this
                    // declared reference argument with null.
                    continue;
                } else if ("ARGUMENT".equals(action.location)
                        && action.declaresArrayInput(
                        Collections.<String>emptyList())) {
                    symbolize(active, action, null, engine());
                } else {
                    active.unresolved.add(action.symbol
                            + ": primitive argument requires a stack-value model (concrete="
                            + safe(primitiveValue) + ")");
                }
                continue;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                if (action.fieldPaths.isEmpty()) {
                    active.unresolved.add(action.symbol
                            + ": selective argument has no field paths");
                    continue;
                }
                for (List<String> path : action.fieldPaths) {
                    symbolizeFieldPath(active, action, value, path, engine());
                }
            } else {
                symbolize(active, action, value, engine());
            }
        }
    }

    /** Symbolizes one scheduler-selected helper-method argument in-region. */
    public static void symbolizeMethodArgument(String method,
                                               int argumentIndex,
                                               Object value,
                                               String primitiveValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        int occurrence = active.materializationOccurrences
                .observedMethodArgument(method, argumentIndex);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesMethodArgument(method, argumentIndex)
                    || !action.acceptsOccurrence(occurrence)
                    || !active.materialized.add(action.symbol)) {
                continue;
            }
            if (value == null && !action.declaresArrayInput(
                    Collections.<String>emptyList())) {
                active.unresolved.add(action.symbol
                        + ": null method argument cannot be symbolized");
                continue;
            }
            symbolize(active, action, value, engine());
        }
    }

    /**
     * Applies a solver model to the real root argument before ordinary Java
     * control flow consumes it.  Soot writes the returned value back to the
     * parameter local (including an unbox for primitive parameters).  No
     * branch outcome is overridden here: the changed input must make the
     * unmodified branch evaluate to the requested outcome during replay.
     */
    public static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return boxedOrReference;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (action.index != argumentIndex
                    || !("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))) {
                continue;
            }
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, null);
            }
            if (boxedOrReference == null) {
                Object modeled = modeledReference(active, action, null,
                        "root reference");
                return unmodeled(modeled) ? null : modeled;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                for (List<String> path : action.fieldPaths) {
                    applyFieldPathModel(active, action, boxedOrReference,
                            path);
                }
            } else {
                Object modeled = modeledReference(active, action,
                        boxedOrReference, "root reference");
                if (!unmodeled(modeled)) {
                    trackMaterializedContainer(active, action, modeled);
                    return modeled;
                }
            }
            trackMaterializedContainer(active, action, boxedOrReference);
        }
        return boxedOrReference;
    }

    /** Applies a solver model at an exact in-region helper parameter. */
    public static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return boxedOrReference;
        int occurrence = active.materializationOccurrences.methodArgument(
                method, argumentIndex);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesMethodArgument(method, argumentIndex)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, null);
            }
            Object modeled = modeledReference(active, action,
                    boxedOrReference, "method argument");
            if (modeled == UnsupportedReplayValue.INSTANCE) {
                return boxedOrReference;
            }
            Object materialized = modeled == MissingValue.INSTANCE
                    ? boxedOrReference : modeled;
            trackMaterializedContainer(active, action, materialized);
            return materialized;
        }
        return boxedOrReference;
    }

    /** Materializes a reference-valued live-in at its defining Jimple local. */
    public static Object materializeReference(String method, int unitIndex,
                                              String local, Object value) {
        ActiveRegion active = activeRegion();
        if (active == null) {
            return value;
        }
        int occurrence = active.nextLocalMaterializationOccurrence(
                method, unitIndex, local);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, unitIndex, local)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            if (!active.materialized.add(action.symbol)) {
                continue;
            }
            Object materialized = value;
            ModelAssignment assignment = active.assignment(action, null);
            if (assignment != null) {
                Object modeled = assignment.referenceValue(value);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    if (isPrimitiveBox(value)) {
                        return materializePrimitiveValue(active, action,
                                value, null);
                    }
                    active.unresolved.add(action.symbol
                            + ": unsupported local reference model "
                            + assignment.valueType + "=" + assignment.value);
                } else {
                    materialized = modeled;
                    active.recordModelAssignment(assignment);
                }
            }
            if (materialized != null
                    || action.declaresArrayInput(
                    Collections.<String>emptyList())) {
                symbolize(active, action, materialized, engine());
            }
            return materialized;
        }
        return value;
    }

    /**
     * Materializes a primitive live-in and returns a fresh boxed value.  Soot
     * immediately unboxes this result back into the original local, allowing
     * the VM's symbolic field expression to flow into the actual branch.
     */
    public static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        ActiveRegion active = activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        int occurrence = active.nextLocalMaterializationOccurrence(
                method, unitIndex, local);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, unitIndex, local)
                    || !action.acceptsOccurrence(occurrence)
                    || !action.repeatedPrimitiveAccessor()
                    && !active.materialized.add(action.symbol)) {
                continue;
            }
            return materializePrimitiveValue(active, action, boxedValue,
                    null);
        }
        return boxedValue;
    }

    /**
     * The frozen actions that model one firing of a named fault marker.
     *
     * <p>The classification lives on {@code sourceKind}: the finalizer stamps
     * it there when it mints the port
     * ({@code RuntimeSelectedRegionFinalizer.explicitFaultPorts}).  Nothing
     * writes it into {@code symbolicDemand}, which carries the scheduler's
     * selection verdict for the same action and is either absent or
     * {@code WORKLOAD_DECLARED_SYMBOLIC_FAULT} for a fault, so reading the
     * demand here matched nothing and pinned every marker to {@code false}.
     * </p>
     *
     * <p>A marker literal is one call site, so two in-scope requests inside
     * one activation are two recorded firings with two roots.  The recorded
     * {@code replayOccurrence} is what tells them apart; without it both rows
     * answer to the name and the firing resolves to nothing.  More than one
     * survivor is still ambiguous and the caller refuses.</p>
     */
    static List<SymbolizeAction> explicitFaultCandidates(
            Collection<SymbolizeAction> actions, String name,
            int occurrence) {
        List<SymbolizeAction> candidates = new ArrayList<>();
        for (SymbolizeAction action : actions == null
                ? Collections.<SymbolizeAction>emptyList() : actions) {
            if (!RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                    .equals(action.sourceKind)
                    || !safe(name).equals(action.symbolicName)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            candidates.add(action);
        }
        return candidates;
    }

    /**
     * The name one unanswered fault-control question answers to.
     *
     * <p>{@link #materializeSymbolicBoolean} must hand the workload a
     * {@code boolean}: the marker stands at a call site the program is about
     * to branch on, so there is no third value to return and no point at
     * which the replay can stop.  What it must not do is let the
     * {@code false} it returns pass for an answer.</p>
     *
     * <p>There are two answers, and a firing is unanswered only when it has
     * neither.  A flip replay answers from its model assignment.  A seed
     * replay has no model by construction -- it reproduces the recording --
     * and answers from the recording's own polarity, which the plan states as
     * the action's {@code primitiveValue} gated on {@code observed}.  Reading
     * "no model" alone as "unanswered" refused every seed summary that
     * touches a declared marker and took the DEPENDENCY worklist with it
     * ({@code NO_OBSERVED_PATH_SEED}); the recorded value is what
     * distinguishes an answer from the default that used to stand here.</p>
     *
     * <p>With neither, the question the search exists to decide has no
     * answer, and pinning the marker to the polarity the search wants to flip
     * would be a fabricated chain element -- so the value stays concrete and
     * the activation is flagged, which refuses the summary at import.</p>
     *
     * <p>A marker this plan does not control at all is a different thing: no
     * question was put to the replay, the recording ran the same hook to the
     * same {@code false}, and there is nothing to refuse.  Those firings are
     * named on the diagnostic stream instead, so a corpus can still be
     * grepped for them.</p>
     */
    static final String FAULT_IDLE_UNANSWERED = "FAULT_IDLE_UNANSWERED";

    /** One fault firing answered from the recording rather than a model. */
    static final String RECORDED_FAULT_ANSWER = "RECORDED_FAULT_ANSWER";

    /**
     * The name one unwitnessed target link answers to.
     *
     * <p>Used on both sides of the link: by the replay, when a target-reach
     * task names no fatal occurrence for its reach to be checked against, and
     * by {@code RuntimeRegionPlanner}, when a declared required outcome was
     * taken by no recorded occurrence of its site.</p>
     */
    static final String TARGET_REACH_NOT_OBSERVED =
            "TARGET_REACH_NOT_OBSERVED";

    /**
     * The polarity the recording gave one fault marker, or null.
     *
     * <p>{@code recordedPrimitiveValue} is already gated on the action's
     * {@code observed} flag, so a value here is one the mint actually saw.
     * Anything that is not a boolean literal states nothing: a marker is a
     * {@code boolean} and a value that cannot be read as one is not the
     * recording's answer to it.</p>
     */
    static Boolean recordedFaultPolarity(SymbolizeAction action) {
        String recorded = action == null ? ""
                : safe(action.recordedPrimitiveValue).trim();
        if ("true".equalsIgnoreCase(recorded)) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(recorded)) return Boolean.FALSE;
        return null;
    }

    /** Whether this activation's plan controls the named fault marker. */
    static boolean declaresExplicitFault(
            Collection<SymbolizeAction> actions, String name) {
        for (SymbolizeAction action : actions == null
                ? Collections.<SymbolizeAction>emptyList() : actions) {
            if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                    .equals(action.sourceKind)
                    && safe(name).equals(action.symbolicName)) {
                return true;
            }
        }
        return false;
    }

    /** Returns the replay model for one explicitly named application fault. */
    public static boolean materializeSymbolicBoolean(String name) {
        ActiveRegion active = activeRegion();
        if (active == null) {
            // Outside every replayed region: no activation is claiming
            // anything about this firing, so there is no ledger to refuse.
            diag(FAULT_IDLE_UNANSWERED, "marker=" + safe(name)
                    + " reason=NO_ACTIVE_REGION");
            return false;
        }
        int occurrence = active.materializationOccurrences.explicitFault(
                name);
        List<SymbolizeAction> candidates = explicitFaultCandidates(
                active.activation.symbolize, name, occurrence);
        if (candidates.size() > 1) {
            active.addUnresolvedOnce("ambiguous explicit fault: " + name
                    + "#" + occurrence);
            return false;
        }
        boolean controlled = declaresExplicitFault(
                active.activation.symbolize, name);
        if (candidates.isEmpty()) {
            active.noteFaultIdle(name, occurrence, controlled,
                    "NO_ACTION_ACCEPTS_THIS_OCCURRENCE");
            return false;
        }
        SymbolizeAction selected = candidates.get(0);
        ModelAssignment assignment = active.assignment(selected, null);
        if (assignment == null) {
            // A seed replay has no model by construction: it reproduces the
            // recording, and the recording's own polarity is the answer.  The
            // plan states it as this action's primitiveValue, gated on
            // observed, so it is a value the mint witnessed and not a default
            // chosen here -- which is the whole difference between answering
            // the marker and pinning it.  Only a firing with neither a model
            // nor a recorded value is unanswered.
            Boolean recorded = recordedFaultPolarity(selected);
            if (recorded == null) {
                active.noteFaultIdle(name, occurrence, controlled,
                        "NO_MODEL_ASSIGNMENT_AND_NO_RECORDED_VALUE");
                return false;
            }
            active.noteRecordedFaultAnswer(name, occurrence, recorded);
            return recorded;
        }
        Object value = coerceModelValue(assignment.valueType,
                assignment.value, Boolean.class);
        if (!(value instanceof Boolean)) {
            active.addUnresolvedOnce("unsupported explicit fault model: "
                    + assignment.valueType + "=" + assignment.value);
            return false;
        }
        active.recordModelAssignment(assignment);
        return (Boolean) value;
    }

    /**
     * Materializes the primitive value consumed by one exact {@code getstatic}
     * site.
     */
    public static Object materializeStaticPrimitiveField(
            String method, int unitIndex, String fieldSignature,
            String fieldName, Object boxedValue) {
        ActiveRegion active = activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        SymbolizeAction selected = null;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesStaticField(method, unitIndex,
                    fieldSignature, fieldName)) {
                continue;
            }
            if (selected != null && selected != action) {
                active.addUnresolvedOnce(SiteId.render(method, unitIndex)
                        + ": AMBIGUOUS_STATIC_FIELD_MATERIALIZATION");
                return boxedValue;
            }
            selected = action;
        }
        if (selected == null
                || !active.materialized.add(selected.symbol)) {
            return boxedValue;
        }
        List<String> logicalPath = selected.exactStaticFieldPath(
                fieldSignature, fieldName);
        if (logicalPath == null) {
            active.addUnresolvedOnce(SiteId.render(method, unitIndex)
                    + ": STATIC_FIELD_LOGICAL_PATH_OR_DECLARATION_MISMATCH");
            return boxedValue;
        }
        return materializePrimitiveValue(active, selected, boxedValue,
                logicalPath);
    }


    public static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return;
        int occurrence = active.materializationOccurrences.field(
                method, unitIndex);
        ConsumerAccessAnchor consumer = consumerAccessAnchor(active, method,
                unitIndex, occurrence, owner);
        GuardedReadAssignment guardedRead =
                active.activation.guardedReadAssignment(consumer,
                        fieldSignature);
        List<SymbolizeAction> claimed = active.activation.symbolize;
        for (SymbolizeAction action : claimed) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName, null)
                    || !action.acceptsDirectFieldOccurrence(occurrence)) {
                continue;
            }
            Object leafOwner = action.leafOwner(owner);
            if (leafOwner == null || leafOwner == MissingValue.INSTANCE) {
                active.addUnresolvedOnce(action.symbol
                        + ": field owner is unavailable for "
                        + action.fieldPath);
                continue;
            }
            if (!active.materialized.add(action.symbol)) continue;
            try {
                ConcolicVmBroker api = engine();
                Field exactField = declaredInstanceField(leafOwner,
                        action.exactLeafFieldSignature());
                if (exactField == null) {
                    active.addUnresolvedOnce(action.symbol
                            + ": exact field declaration is unavailable");
                    continue;
                }
                String leafFieldSignature = exactFieldSignature(exactField);
                Object value = exactField.get(leafOwner);
                boolean assignmentFailed = false;
                for (ModelAssignment assignment
                        : active.fieldAssignments(action)) {
                    if (!assignment.hasContainerTarget()) continue;
                    if (!assignment.validContainerTarget()
                            || !writeContainerTarget(value, assignment)) {
                        active.addUnresolvedOnce(action.symbol
                                + ": solver container model could not be "
                                + "materialized");
                        assignmentFailed = true;
                        break;
                    }
                    active.recordModelAssignment(assignment);
                }
                if (assignmentFailed) continue;
                JsonElement carried;
                try {
                    carried = containerValue(value)
                            ? engineExpression(api.expression(value))
                            : engineExpression(api.fieldExpression(leafOwner,
                            exactField.getDeclaringClass().getName(),
                            exactField.getName(), javaTypeDescriptor(
                            exactField.getType().getTypeName()), value));
                } catch (PropagatedExpressionImportFailure unreadable) {
                    // Not "nothing propagated": the producer's expression is
                    // there and could not be read.  Minting would answer that
                    // with a root nothing constrains.
                    refuseImportedExpression(active, action.symbol,
                            leafFieldSignature, unreadable);
                    continue;
                } catch (Throwable unsymbolized) {
                    carried = null;
                }
                // Ask before replay writes or fresh minting. A boundary that
                // already reached this field is the input authority.
                if (retainPropagatedInput(active, action, value, carried,
                        action.symbol, action.fieldPath,
                        leafFieldSignature)) {
                    continue;
                }
                JsonElement expression;
                if (value != null && value != MissingValue.INSTANCE
                        && containerValue(value)) {
                    requireTrackedContainer(api, value, action.symbol);
                    ensurePathRecordingStarted(active);
                    active.recordSymbolizedInputPort(action.symbol, value);
                    expression = engineExpression(api.expression(value));
                } else {
                    active.addUnresolvedOnce(action.symbol
                            + ": exact input has no propagated VM expression");
                    continue;
                }
                active.recordManualSymbolization(action, action.symbol,
                        action.fieldPath, leafFieldSignature, expression,
                        true, false);
            } catch (Throwable throwable) {
                active.addUnresolvedOnce(action.symbol
                        + ": field materialization "
                        + SiteId.render(method, unitIndex) + " failed: "
                        + rootCause(throwable));
            }
        }
        armGuardedRead(active, owner, guardedRead);
    }

    /** Applies a model to the key used by this exact live Map.get. */
    public static void materializeAssociativeRead(Object container,
                                                  Object key) {
        ActiveRegion active = activeRegion();
        if (active == null || !(container instanceof Map<?, ?>)) return;
        beginBookkeeping();
        try {
            String inputSymbol = safe(
                    active.symbolizedInputPorts.get(container));
            if (inputSymbol.isEmpty()) return;
            int occurrence = active.associativeAccessOccurrences
                    .getOrDefault(inputSymbol, 0) + 1;
            active.associativeAccessOccurrences.put(inputSymbol, occurrence);
            ModelAssignment selected = null;
            for (ModelAssignment candidate
                    : active.activation.modelAssignments) {
                if (!candidate.dynamicAssociativeTarget()
                        || !candidate.inputSymbol.equals(inputSymbol)
                        || candidate.containerAccessOrdinal != occurrence
                        || active.appliedModelAssignments.contains(
                        candidate.key)) {
                    continue;
                }
                if (selected != null) {
                    active.addUnresolvedOnce(inputSymbol + "#access."
                            + occurrence + ": ambiguous model assignments");
                    return;
                }
                selected = candidate;
            }
            if (selected == null) return;
            if (!selected.validContainerTarget()
                    || !writeAssociativeContainerTarget(container, key,
                    selected)) {
                active.addUnresolvedOnce(inputSymbol + "#access."
                        + occurrence
                        + ": solver model could not be materialized");
                return;
            }
            active.recordModelAssignment(selected);
        } finally {
            endBookkeeping();
        }
    }

    /** Installs the selected arm at its exact consumer read. */
    private static void armGuardedRead(ActiveRegion active, Object owner,
                                       GuardedReadAssignment assignment) {
        if (assignment == null || active.armedGuardedReads.containsKey(
                assignment.readIdentity)) {
            return;
        }
        try {
            long token = engine().armSharedPrimitiveFieldRead(owner,
                    assignment.declaringClass, assignment.fieldName,
                    assignment.descriptor, assignment.valueBits);
            if (token > 0L) {
                active.armedGuardedReads.put(assignment.readIdentity, token);
            } else {
                active.addUnresolvedOnce(assignment.readIdentity
                        + ": VM rejected guarded read materialization: "
                        + token);
            }
        } catch (Throwable failure) {
            active.addUnresolvedOnce(assignment.readIdentity
                    + ": guarded read materialization failed: "
                    + rootCause(failure));
        }
    }

    /**
     * The address of one read inside one activation: an exact bytecode site
     * and the occurrence of it this activation reached.
     *
     * <p>It named carriers once, and does not any more -- a location is named
     * by the object the VM filed it under.  What is left is the job it was
     * always doing underneath: saying <em>which read</em> a guarded-read model
     * applies to, which is a fact about the access and not about the
     * location.</p>
     */
    static final class ConsumerAccessAnchor {
        final String siteId;
        final int occurrence;

        ConsumerAccessAnchor(String siteId, int occurrence) {
            this.siteId = safe(siteId);
            this.occurrence = occurrence;
        }
    }

    /** The address of the read this hook stands on, or {@code null}. */
    static ConsumerAccessAnchor consumerAccessAnchor(
            ActiveRegion active, String method, int unitIndex,
            int occurrence, Object owner) {
        AccessorCallContext accessor = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (accessor != null && active != null
                && accessor.regionToken == active.token
                && accessor.thread == Thread.currentThread()
                && accessor.receiver == owner
                && !accessor.callSiteId.isEmpty()
                && accessor.occurrence > 0) {
            return new ConsumerAccessAnchor(accessor.callSiteId,
                    accessor.occurrence);
        }
        if (safe(method).isEmpty() || unitIndex < 0 || occurrence < 1) {
            return null;
        }
        return new ConsumerAccessAnchor(SiteId.of(method, unitIndex),
                occurrence);
    }

    /** Records a stable logical source a live occurrence just entered. */
    static void observeCausalSource(String sourceKey) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        if (sourceKey != null && !sourceKey.isEmpty()) {
            active.observedSourceKeys.add(sourceKey);
        }
    }

    /**
     * The VM name of one fresh mint.
     *
     * <p>The phase label is the stable semantic name of the mint SITE, which
     * the evidence contract keys its rows by.  Entries past the first append
     * their entry number, so every occurrence is its own VM root while a site
     * entered once keeps exactly the name it always had.</p>
     */
    /**
     * One entry of one declared mint site.
     *
     * <p>Wave 3 selects nothing.  The frozen catalog says only WHERE a mint
     * site is; every entry of that site is its own symbolic variable, and the
     * ordinal is the per-(activation, site) entry count starting at 1.</p>
     */
    private static final class SourceSiteEntry {
        private final ConfiguredSourcePhaseContract.Occurrence phase;
        private final String siteId;
        private final int ordinal;
        private SourceSiteEntry(
                ConfiguredSourcePhaseContract.Occurrence phase,
                String siteId, int ordinal) {
            this.phase = phase;
            this.siteId = safe(siteId);
            this.ordinal = ordinal;
        }

        private String phaseId() {
            return phase == null ? "" : phase.phaseId();
        }

        /** Identity of this entry inside one activation. */
        private String key() {
            return siteId + "#" + ordinal;
        }
    }

    /**
     * Mints one symbol for one entry of a declared mint site.
     *
     * <p>Every occurrence of a declared field is its own symbolic variable.
     * The VM is the authority on the value: a field that already carries a
     * propagated expression keeps it - {@code SymInstance::has_sym_exp} makes
     * the mint a no-op - and the published row says {@code reused}.  Manual
     * input is only WHICH FIELDS, never which occurrence of one.</p>
     *
     * <p>Called from outside this repository: the workload checkouts invoke it
     * directly from {@code org.apache.hadoop.ipc.CausynthSymbolicSource}, and
     * it is the only symbolic root of HDFS-17960.</p>
     */
    public static boolean symbolizeConfiguredSourceField(
            String sourceId, Object owner, String fieldSignature) {
        ActiveRegion active = activeRegion();
        // Nothing to mint on is not a gap: the site simply was not carrying a
        // declared owner on this entry.
        if (active == null || owner == null) return false;
        SourceSiteEntry entry = active.observeConfiguredSourceEntry(
                safe(sourceId), safe(fieldSignature));
        if (entry == null) return false;
        beginBookkeeping();
        try {
            Field field = declaredInstanceField(owner, safe(fieldSignature));
            if (field == null || !field.getType().isPrimitive()) {
                active.addUnresolvedOnce(entry.key()
                        + ": configured source is not an exact primitive "
                        + "field");
                return false;
            }
            ConcolicVmBroker api = engine();
            String declaringClass = field.getDeclaringClass().getName();
            String descriptor = javaTypeDescriptor(
                    field.getType().getTypeName());
            // The authority question, asked before anything is written: did
            // this value arrive carrying an expression of its own?  A VM that
            // has no answer for an unsymbolized field is answering "no", so
            // the read-out never decides the mint by throwing.
            JsonElement carried;
            try {
                carried = engineExpression(api.fieldExpression(owner,
                        declaringClass, field.getName(), descriptor,
                        field.get(owner)));
            } catch (PropagatedExpressionImportFailure unreadable) {
                // A declared source whose carried expression could not be
                // read must not be answered by minting a second root over
                // the top of the one already in the field.
                refuseImportedExpression(active, entry.key(),
                        safe(fieldSignature), unreadable);
                return false;
            } catch (Throwable unsymbolized) {
                carried = null;
            }
            // A hook site is a declared primitive root by construction: the
            // entry above refuses anything else.  So it asks the strict
            // question, the same one a declared plan action asks in
            // carriesInputAuthority.  The loose rule would answer "already
            // propagated" for any field a shared-state carrier has wrapped in
            // a ReadFrom -- which every field the hook stands on eventually
            // is -- and the mint would never fire, leaving the declared
            // source concrete.  Only a tree that actually names a VM symbol
            // root inside those wrappers is an expression of its own.
            boolean reused = configuredSourceCarriesAuthority(carried);
            // The application's Map re-key reads the modeled value back
            // through this same path, so the model is written first.
            ModelAssignment assignment = reused ? null
                    : active.configuredSourceAssignment(entry.phaseId(),
                    safe(sourceId), safe(fieldSignature), owner);
            if (assignment != null) {
                if (!writeModeledField(owner, safe(fieldSignature),
                        assignment)) {
                    throw new IllegalStateException(
                            "configured source model could not be written");
                }
            }
            String symbol = "";
            if (!reused) {
                // The phase is the stable semantic source site.  Exact
                // activation identity is recorded separately in the evidence
                // row; changing the VM label per occurrence only duplicates
                // equivalent symbolic roots and complicates composition.
                String sourceOccurrence = active.occurrenceId();
                symbol = "sym__" + safe(sourceId) + "__"
                        + safe(sourceOccurrence) + "__"
                        + entry.ordinal;
                String label = SymbolicSourceEvidence.engineLabelForPhase(
                        entry.phaseId(), safe(sourceId));
                api.symbolizeExactField(owner, exactFieldSignature(field),
                        entry.ordinal <= 1 ? label
                                : label + "__" + entry.ordinal);
            }
            // The mint is a symbolic write, so the VM has started this
            // field's version log by itself; the declaration that used to be
            // filed here bought nothing that the write did not already do.
            ensurePathRecordingStarted(active);
            Object value = field.get(owner);
            JsonElement expression = engineExpression(api.fieldExpression(
                    owner, declaringClass, field.getName(), descriptor,
                    value));
            // Only the occurrence that minted the VM leaf owns source
            // evidence and its model assignment.  A propagated bare or
            // compound expression remains the consumer's exact input and is
            // recorded below as reuse without acquiring a second identity.
            JsonObject evidence = null;
            if (!reused) {
                // Fail closed: a concrete write is not a materialized
                // symbolic input until the VM has accepted the exact field
                // and returned one exact root for it.  The evidence row is
                // built before the mint row so that a read-back the VM did
                // not replace -- the shape this catch names -- leaves no row
                // claiming a symbol it never published.
                try {
                    evidence = SymbolicSourceEvidence.event(entry.phaseId(),
                            safe(sourceId), active.occurrenceId(),
                            safe(fieldSignature), expression,
                            entry.ordinal, reused, symbol,
                            // Only an activation that read the field as the
                            // program left it observed a recorded value.  A
                            // replay that wrote a model assignment into the
                            // field above read the model back, and publishing
                            // that as "recorded" is how a counterfactual
                            // becomes the recording.
                            assignment == null
                                    ? recordedScalar(value) : null);
                } catch (IllegalArgumentException refused) {
                    throw new IllegalStateException(refused.getMessage()
                            + " (VM read-back after symbolizeExactField: "
                            + describeReadBack(expression) + ")", refused);
                }
            }
            active.recordConfiguredSourceMint(entry, safe(sourceId),
                    safe(fieldSignature), symbol, expression, reused);
            if (evidence != null) {
                active.recordSymbolicSource(entry.key(), evidence);
            }
            if (assignment != null) {
                // A concrete write is not a materialized symbolic input until
                // the VM has accepted the exact field and returned its
                // expression.
                active.recordModelAssignment(assignment);
            }
            return true;
        } catch (Throwable failure) {
            active.addUnresolvedOnce(entry.key()
                    + ": exact symbolic source materialization failed: "
                    + rootCause(failure));
            return false;
        } finally {
            endBookkeeping();
        }
    }


    /**
     * The outermost shape of what the VM handed back for a minted field, for
     * the unresolved-input line.  A mint that reads back as anything but one
     * VM symbol means the VM kept an expression the field already carried,
     * and the line should say what that was rather than only that the
     * evidence contract refused it.
     */
    static String describeReadBack(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return expression == null ? "no expression"
                    : expression.toString();
        }
        JsonObject node = expression.getAsJsonObject();
        String type = optionalString(node, "_type");
        String raw = optionalString(node, "_exp");
        return type.isEmpty() ? "untyped expression"
                : raw.isEmpty() ? type : type + " " + raw;
    }

    /**
     * The name one unreadable propagated producer expression answers to.
     *
     * <p>A malformed or unreadable import is not "nothing propagated".  The
     * producer did deliver a value and it does carry an expression; what
     * failed is this replay's ability to read it.  Reading those two answers
     * as one is how a consumer whose producer expression could not be
     * imported acquired a <em>fresh unconstrained root</em> in its place:
     * {@link #carriesInputAuthority} was asked about a {@code null}, said
     * "nothing propagated", and the caller minted.  That manufactures a
     * freedom the recording never had, and a witness is free to exploit
     * it.</p>
     *
     * <p>So the failure travels as its own exception.  Every caller either
     * lets it reach a handler that files a named gap, or catches it here and
     * keeps the consumer's value concrete-and-flagged; none of them mints.
     * The row lands in {@code unresolvedInputs}, which {@code
     * ConcolicSummaryImporter} turns into {@code UNRESOLVED_INPUT} and
     * refuses the whole summary under, so the gap blocks rather than
     * decorates.</p>
     */
    static final String PROPAGATED_EXPRESSION_IMPORT_FAILED =
            "PROPAGATED_EXPRESSION_IMPORT_FAILED";

    /**
     * A propagated producer expression this replay could not import.
     *
     * <p>Its own type, so the three call sites that legitimately read "the VM
     * has no expression for this value" as {@code null} can keep doing that
     * for an unsymbolized read while still refusing an import that failed.
     * </p>
     */
    static final class PropagatedExpressionImportFailure
            extends IllegalStateException {
        private static final long serialVersionUID = 1L;

        PropagatedExpressionImportFailure(String detail, Throwable cause) {
            super(detail, cause);
        }
    }

    /** Package-visible for the import-refusal contract test. */
    static JsonElement engineExpression(String serialized) {
        ActiveRegion active = activeRegion();
        try {
            VmExpressionTable.Store store = active == null
                    ? workloadExpressionStore
                    : active.expressionStore;
            return store.importField(serialized, "expression");
        } catch (RuntimeException malformed) {
            String detail = PROPAGATED_EXPRESSION_IMPORT_FAILED
                    + ": producer=" + describeImportPayload(serialized)
                    + " occurrence=" + (active == null ? "<none>"
                    : safe(active.activation.occurrenceId))
                    + ": " + rootCause(malformed);
            // Recorded here as well as at the consumer, because a call site
            // that lets the failure propagate to its own handler names the
            // consumer but loses which import failed.
            if (active != null) active.addUnresolvedOnce(detail);
            throw new PropagatedExpressionImportFailure(detail, malformed);
        }
    }

    /**
     * Files one unreadable producer expression against the consumer that
     * asked for it, and leaves that consumer's value concrete.
     *
     * <p>The row names the consumer port, the field it read and the
     * activation, beside the producer detail the import carried.  There is no
     * value to state and no freedom to grant, so the only honest answer is a
     * gap that blocks.</p>
     */
    static void refuseImportedExpression(
            ActiveRegion active, String consumerSymbol, String fieldSignature,
            PropagatedExpressionImportFailure unreadable) {
        if (active == null) return;
        active.addUnresolvedOnce(PROPAGATED_EXPRESSION_IMPORT_FAILED
                + ": consumer=" + safe(consumerSymbol)
                + " field=" + safe(fieldSignature)
                + " occurrence=" + safe(active.activation.occurrenceId)
                + ": " + safe(unreadable.getMessage()));
    }

    /** The outermost shape of a VM payload an import refused, for the row. */
    static String describeImportPayload(String serialized) {
        String value = safe(serialized);
        if (value.isEmpty()) return "<empty payload>";
        return value.length() <= 160 ? value
                : value.substring(0, 160) + "...(" + value.length() + " B)";
    }

    /** Resolves a native session DAG while retaining content sharing here. */
    static JsonObject decodeVmEnvelope(JsonObject envelope,
                                               ActiveRegion active) {
        VmExpressionTable.Store store = active == null
                ? workloadExpressionStore
                : active.expressionStore;
        return store.importEnvelope(envelope);
    }

    /** Result of one VM symbolic-expression export or attach. */
    private static final class HandoffResult {
        private final String stage;
        private final int status;
        private final long handle;
        private final JsonObject record;

        private HandoffResult(String stage, int status, long handle,
                              JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.handle = handle;
            this.record = record;
        }

        public boolean ok() {
            return status == RpcExpressionHandoff.OK;
        }

        /** Named reason for a failure; empty for a successful call. */
        public String reason() {
            return RpcExpressionHandoff.reason(status);
        }

        private long handle() {
            return handle;
        }

        /**
         * The VM ledger event of this exact attach.
         *
         * <p>README {@code RPC-1}: the second endpoint of the {@code
         * VALUE_HANDOFF} edge.</p>
         */
        @Override
        public String toString() {
            return "HandoffResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " handle=" + handle + "]";
        }
    }

    private static HandoffResult exportSymbolicLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        HandoffResult result;
        beginBookkeeping();
        try {
            result = exportLeaf(owner, declaringClass, fieldName, descriptor);
        } finally {
            endBookkeeping();
        }
        return result;
    }

    private static HandoffResult exportLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        String missing = missingFieldMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (!missing.isEmpty()) {
            return record(failed(RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.MISSING_METADATA, 0L, missing));
        }
        ConcolicVmBroker api = engine();
        long handle;
        // README RPC-1: the VM reports the export's own ledger event here,
        // so the producer's interaction row can name the exact export it
        // published instead of leaving the Composer to count port
        // observations for it.
        long[] exportEvent = new long[1];
        try {
            handle = api.exportExpression(owner, declaringClass, fieldName,
                    descriptor, exportEvent);
        } catch (Throwable throwable) {
            return record(failed(RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.INVOCATION_FAILED, 0L,
                    rootCause(throwable)));
        }
        if (handle <= 0L) {
            int status = exportStatus(handle);
            HandoffResult result = failed(
                    RpcExpressionHandoff.STAGE_EXPORT, status, 0L,
                    "exportExpression returned " + handle);
            if (status == RpcExpressionHandoff.NOT_SYMBOLIC) return result;
            return record(result);
        }
        JsonObject exported = new JsonObject();
        exported.addProperty("exportEventId", exportEvent[0]);
        HandoffResult result = new HandoffResult(
                RpcExpressionHandoff.STAGE_EXPORT,
                RpcExpressionHandoff.OK, handle, exported);
        record(result);
        return result;
    }

    /**
     * Attaches one receive whose destination this occurrence's plan declares
     * as a communication port.
     */
    private static HandoffResult attachDeclaredCommunicationExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, SymbolicMessageEnvelope.Entry carried,
            CommunicationHandoffSpec declared) {
        beginBookkeeping();
        try {
            HandoffResult result = record(attach(owner, declaringClass,
                    fieldName, descriptor, carried.handle()));
            if (result.ok()) {
                recordVmHandoffEvent(declared, result, owner, declaringClass,
                        fieldName, descriptor, carried.producerTaskId(),
                        carried.producerOccurrenceId());
            }
            return result;
        } finally {
            endBookkeeping();
        }
    }

    /** The one instance field a declared communication port crosses on. */
    public static final class HandoffLeafCarrier {
        public boolean z;
        public byte b;
        public short s;
        public char c;
        public int i;
        public long j;
        public float f;
        public double d;
        public Object o;
    }

    private static final String CARRIER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                    + "$HandoffLeafCarrier";
    // ------------------------------------------------------------------
    // Communication message flow
    // ------------------------------------------------------------------

    /** Stages one VM handle and its producer on the next outbound message. */
    private static boolean stageMessageExpression(String portId,
                                                  long handle) {
        ActiveRegion active = activeRegion();
        // The producer site ran, so the message carries the value.  Which
        // occurrence produced it and which the plan addressed are what the
        // entry says about itself, not conditions on saying it.
        String producerTask = active == null ? UNPLANNED_ENDPOINT
                : active.activation.taskId;
        String producerOccurrence = active == null ? UNPLANNED_ENDPOINT
                : active.occurrenceId();
        // The entry says which consumers the plan bound to this port, which
        // is a property of the port and not of whoever is producing: asking
        // the running task first only narrowed it to the subset that task
        // happened to declare.
        List<String> consumerOccurrences = plannedExportConsumers(portId);
        boolean staged = SymbolicMessageEnvelope.stage(
                portId, handle, producerTask, producerOccurrence,
                consumerOccurrences);
        if (staged && active != null) {
            beginBookkeeping();
            try {
            } finally {
                endBookkeeping();
            }
        }
        return staged;
    }

    /**
     * Stands in for an endpoint no plan named.
     *
     * <p>A leaf may be staged or taken under an identity the plan did not
     * select.  The value is still the value; the entry says plainly that its
     * endpoint was not planned rather than pretending to an occurrence.</p>
     */
    static final String UNPLANNED_ENDPOINT = "UNPLANNED";

    /** Every consumer occurrence any plan bound to this port. */
    private static List<String> plannedExportConsumers(String portId) {
        List<String> consumers = new ArrayList<>();
        for (ConcolicTaskPlan.RuntimeTask task : configuration().tasks) {
            for (String consumer : task.exportConsumerOccurrences(portId)) {
                if (!consumers.contains(consumer)) consumers.add(consumer);
            }
        }
        if (consumers.isEmpty()) consumers.add(UNPLANNED_ENDPOINT);
        return consumers;
    }

    // ------------------------------------------------------------------
    // Declared communication ports
    // ------------------------------------------------------------------

    /**
     * Opens the frame around one message instance being serialized.
     *
     * <p>A declared port is one pair of bytecode sites, and a protocol sends
     * many unrelated values of that shape through it.  The frame is the thing
     * whose single construction builds one instance of the value the port
     * belongs to; leaves staged inside it are addressed within it, so two
     * groups of the same shape in one message stay apart.</p>
     */
    public static void pushOutboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.pushOutboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /** Closes the frame {@link #pushOutboundMessageFrame} opened. */
    public static void popOutboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.popOutboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Opens the frame around one message instance being decoded.
     *
     * <p>The mirror of {@link #pushOutboundMessageFrame}: the receiver counts
     * its frames the way the sender counted theirs, so the k-th frame means
     * the same thing on both sides without either naming the other.</p>
     */
    public static void pushInboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.pushInboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /** Closes the frame {@link #pushInboundMessageFrame} opened. */
    public static void popInboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.popInboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Exports the live expression of one declared communication port.
     *
     * <p>The value arrives on a {@link HandoffLeafCarrier} the
     * <em>instrumented frame</em> allocated and stored into, because a broker
     * leaf is an exact instance field while a cut argument is a local - and
     * because only the application's own frame propagates a value's expression
     * into a field.</p>
     */
    public static void exportCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        CommunicationHandoffSpec site;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, true);
        } finally {
            endBookkeeping();
        }
        if (site == null || carrier == null) return;
        HandoffResult result = exportSymbolicLeaf(carrier, CARRIER_CLASS,
                field, descriptor);
        // A concrete leaf is still a leaf the message carried.
        if (!result.ok()
                && result.status != RpcExpressionHandoff.NOT_SYMBOLIC) {
            return;
        }
        if (!stageMessageExpression(site.portId(),
                result.ok() ? result.handle() : 0L)) {
            recordHandoffGap(RpcExpressionHandoff.portGap(
                    RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.MISSING_METADATA,
                    result.ok() ? result.handle() : 0L, site.portId(),
                    "communication leaf could not enter the message: "
                            + site.portId()));
        }
    }

    /**
     * Attaches the exported expression of one declared communication port.
     *
     * <p>After a successful attach the carrier leaf <em>denotes the sender's
     * expression</em>; the instrumented frame reads it straight back into its
     * own local, so the receiver's later arithmetic, branches and exports
     * build on that term directly.</p>
     */
    public static void attachCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        CommunicationHandoffSpec site;
        SymbolicMessageEnvelope.Entry carried;
        long handle;
        boolean leafCarried;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, false);
            carried = site == null ? null
                    : SymbolicMessageEnvelope.take(site.portId());
            leafCarried = carried != null && carried.present();
            handle = carried == null ? 0L : carried.handle();
        } finally {
            endBookkeeping();
        }
        if (site == null) {
            // A capture ran for a port no task of this campaign declares.
            // Rule 5: the run says so rather than returning in silence --
            // an attach that files nothing and an attach nobody planned
            // read identically from the corpus, and only one of them is a
            // coverage question.
            recordHandoffGap(RpcExpressionHandoff.portGap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, 0L, safe(portId),
                    // The set actually tested is the task slice handed to
                    // THIS replay, which is narrower than the campaign's
                    // plan: on lane17897h the plan declared the port on a
                    // cache-encryption-key occurrence the slice did not
                    // carry, and the old wording sent a reader looking for
                    // a planning bug that was not there.
                    "no task of this replay's slice declares this capture's"
                            + " port: " + safe(portId)));
            return;
        }
        if (carrier == null) {
            recordHandoffGap(RpcExpressionHandoff.portGap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, handle,
                    site.portId(),
                    "required communication port has no carrier: "
                            + site.portId()));
            return;
        }
        if (!leafCarried || handle <= 0L) {
            // The delivery carried no producer expression, and the mint
            // happens anyway.  v_H is the consumer's boundary variable,
            // minted at the consumer's declared capture on the value that
            // ARRIVED; the envelope element only supplies e_p, which is one
            // member of H's family and not a condition of H existing.
            // Absent, the row says so and this delivery contributes no
            // family arm -- which is exactly right for a flip replay whose
            // job is the consumer's path under an assigned v_H, with the
            // producing node running concretely.
            //
            // Two ways for it to be absent, one fact for the consumer.  The
            // message may carry no element for this decode at all; or it may
            // carry one the producer staged with handle 0, which is what
            // exportCommunicationLeaf stages for a leaf the VM answered
            // NOT_SYMBOLIC -- "a concrete leaf is still a leaf the message
            // carried".  Either way there is no e_p and there is an arrived
            // value, so both take this path and the row states
            // elementAbsent.
            //
            // Refusing here left the assignment unapplied: on hdfs-17899
            // bug3 the flip replay of the target published zero handoff
            // rows, the fatal read still found the recorded key, and the
            // obligation ended REPLAY_NOT_ADMITTED with no primary case.
            mintArrivedCommunicationLeaf(site, carrier, field, descriptor);
            return;
        }
        attachDeclaredCommunicationExpression(carrier, CARRIER_CLASS, field,
                descriptor, carried, site);
    }

    /** The declared site of {@code portId} in this occurrence's plan. */
    /**
     * The declared site of {@code portId}, whoever is running.
     *
     * <p>Propagation is a property of the value, not of the activation that
     * happens to be on the stack.  The same conversion runs under several
     * region identities -- the one the plan selected for the port and the
     * ones that merely call the same helper -- and the leaf crossing the
     * wire is the same leaf in all of them.  Asking only the active task
     * meant a value arriving under an unselected identity was dropped, which
     * is how the four conversions that fill a DataNode's key map received no
     * producer expression at all.  Occurrences decide what gets published,
     * never whether a value propagates.</p>
     */
    private static CommunicationHandoffSpec communicationHandoffSite(
            String portId, boolean exporting) {
        if (safe(portId).isEmpty()) return null;
        ActiveRegion active = activeRegion();
        if (active != null) {
            CommunicationHandoffSpec declared =
                    active.activation.communicationHandoff(portId, exporting);
            if (declared != null) return declared;
        }
        for (ConcolicTaskPlan.RuntimeTask task : configuration().tasks) {
            CommunicationHandoffSpec declared =
                    task.communicationHandoff(portId, exporting);
            if (declared != null) return declared;
        }
        return null;
    }

    /**
     * Files one case-local reference into the VM's own handoff ledger and the
     * exact expression now held by the attached destination.
     */
    private static void recordVmHandoffEvent(CommunicationHandoffSpec site,
                                             HandoffResult result,
                                             Object owner,
                                             String declaringClass,
                                             String fieldName,
                                             String descriptor,
                                             String producerTaskId,
                                             String producerOccurrenceId) {
        ActiveRegion active = attachConsumerRegion(site);
        if (active == null || site == null) return;
        noteAttachFiledElsewhere(site, active);
        if (safe(producerTaskId).isEmpty()
                || safe(producerOccurrenceId).isEmpty()) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, result.handle(),
                    "attached leaf carried no exact producer execution"));
            return;
        }
        long exportEvent = result.ok()
                ? optionalLongInteger(result.record, "exportEventId", 0L) : 0L;
        if (exportEvent <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "attached leaf named no VM export event"));
            return;
        }
        // README RPC-1: the reference carries both endpoints of the edge.
        long attachEvent = result.ok()
                ? optionalLongInteger(result.record, "attachEventId", 0L) : 0L;
        if (attachEvent <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "attached leaf named no VM attach event"));
            return;
        }
        JsonElement expression;
        try {
            Field storage = declaredInstanceField(owner, declaringClass,
                    fieldName, descriptor);
            if (storage == null) {
                recordHandoffGap(RpcExpressionHandoff.gap(
                        RpcExpressionHandoff.STAGE_ATTACH,
                        RpcExpressionHandoff.MISSING_METADATA,
                        result.handle(),
                        "attached leaf has no exact destination storage"));
                return;
            }
            Object value = storage.get(owner);
            ConcolicVmBroker api = engine();
            expression = containerValue(value)
                    ? engineExpression(api.expression(value))
                    : engineExpression(api.fieldExpression(owner,
                    declaringClass, fieldName, descriptor, value));
        } catch (Throwable failure) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.INVOCATION_FAILED, result.handle(),
                    "attached destination expression read-out failed: "
                            + rootCause(failure)));
            return;
        }
        if (expression == null || expression.isJsonNull()) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "custom VM returned no propagated destination expression"));
            return;
        }
        mintHandoffVariable(active, site, exportEvent, attachEvent,
                expression, producerTaskId, producerOccurrenceId, owner,
                declaringClass, fieldName, descriptor, false);
    }

    /**
     * Mints v_H at a declared capture whose message carried no element.
     *
     * <p>The consumer's boundary variable is the consumer's, so it is minted
     * from what arrived: the row states {@code elementAbsent}, the delivered
     * value, and no producer -- and an assignment for this H answers the
     * mint exactly as it does when the element is there, because the answer
     * is written on the carrier leaf the receiving frame reads back.</p>
     */
    private static void mintArrivedCommunicationLeaf(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        beginBookkeeping();
        try {
            ActiveRegion active = attachConsumerRegion(site);
            if (active == null) {
                // Nothing is live to carry the mint.  Named, not silent:
                // "the capture ran outside every selected occurrence" is a
                // statement about coverage, and it is the only remaining
                // way this path can publish nothing.
                recordHandoffGap(RpcExpressionHandoff.portGap(
                        RpcExpressionHandoff.STAGE_ATTACH,
                        RpcExpressionHandoff.NO_ACTIVE_REGION, 0L,
                        site.portId(),
                        "capture ran outside every selected occurrence: "
                                + site.portId()));
                return;
            }
            noteAttachFiledElsewhere(site, active);
            mintHandoffVariable(active, site, 0L, 0L, null, "", "", carrier,
                    CARRIER_CLASS, field, descriptor, true);
        } finally {
            endBookkeeping();
        }
    }

    /**
     * The activation this attach belongs to: the innermost live region whose
     * own plan declares this port as an IN site.
     *
     * <p>An attach happens inside whichever regions are live, and the
     * innermost of them is not always the one whose slice owns the attach
     * site: a loop-body region's activation spans one turn, and the same
     * decode site also runs outside the loop.  Filing on the innermost live
     * region regardless published the row under a region that never
     * declared the port -- on hdfs-17899 bug2, REGION.b7266d53, the caller,
     * carried both rows while REGION.16ba41cf, which declares them IN,
     * published none, so one attach was reported twice: unplanned there and
     * unreproduced here.</p>
     *
     * <p>When no live region declares it, the innermost live one still
     * carries the row: the replay is exact about what it did, and R5 then
     * says truthfully that a region ran a handoff nobody planned there.</p>
     */
    private static ActiveRegion attachConsumerRegion(
            CommunicationHandoffSpec site) {
        ActiveRegion innermost = activeRegion();
        if (site == null) return innermost;
        String portId = safe(site.portId());
        for (Long token : CURRENT_TOKENS.get()) {
            ActiveRegion candidate = ownerRegion(token);
            if (candidate == null) continue;
            if (candidate.activation.communicationHandoff(portId, false)
                    != null) {
                return candidate;
            }
        }
        return innermost;
    }

    /**
     * Tells every other live occurrence that declares this port where its
     * attach went.
     *
     * <p>One capture site can lie inside two selected regions -- on
     * hdfs-17899 bug2 the per-call {@code convert(BlockKeyProto)} region
     * and the loop-body region rooted at the enclosing
     * {@code convert(ExportedBlockKeysProto)} both declare
     * {@code resp.block-key-id} at unit 2 of the same method.  The value
     * crosses the wire once, so it is attached once and the row names one
     * consumer; the other declaring occurrence got nothing at all, and its
     * planned attach was read at IMPORT as never reproduced.  It did
     * reproduce -- on the occurrence named here -- and that is what the row
     * now says.</p>
     */
    private static void noteAttachFiledElsewhere(
            CommunicationHandoffSpec site, ActiveRegion named) {
        if (site == null || named == null) return;
        String portId = safe(site.portId());
        if (portId.isEmpty()) return;
        for (Long token : CURRENT_TOKENS.get()) {
            ActiveRegion candidate = ownerRegion(token);
            if (candidate == null || candidate == named) continue;
            if (candidate.activation.communicationHandoff(portId, false)
                    == null) {
                continue;
            }
            candidate.rpcHandoffGaps.add(RpcExpressionHandoff.portGap(
                    RpcExpressionHandoff.LEAF_ATTACHED_ELSEWHERE,
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, 0L, portId,
                    "port declared here was attached on "
                            + named.occurrenceId() + ": " + portId));
        }
    }

    /**
     * Mints the handoff variable v_H on the element this attach landed on.
     *
     * <p>The producer's expression {@code e_p} has just been attached and is
     * in {@code expression}; the element's shadow now becomes a fresh
     * variable instead, so the consumer's formula has a free variable at the
     * boundary rather than the producer's whole expression inlined into it.
     * That is what lets the two sides be explored independently and joined
     * offline at H: {@code e_p} travels on the row as one member of H's
     * family, never as a substitution.</p>
     *
     * <p>One variable per handoff occurrence per replay. A loop attaching the
     * same element on each turn gets one per turn, because k is part of H.
     * The mint is the configured-source mint -- same broker call, same model
     * answering, same "a mint the VM did not accept publishes no row" rule --
     * under a label that says handoff so nothing downstream mistakes it for a
     * configured source.</p>
     */
    private static void mintHandoffVariable(
            ActiveRegion active, CommunicationHandoffSpec site,
            long exportEvent, long attachEvent, JsonElement producerExpression,
            String producerTaskId, String producerOccurrenceId,
            Object owner, String declaringClass, String fieldName,
            String descriptor, boolean elementAbsent) {
        String portId = safe(site.portId());
        Field element = declaredInstanceField(owner, declaringClass,
                fieldName, descriptor);
        List<HandoffLeaf> leaves = handoffLeaves(owner, element);
        if (leaves.isEmpty()) {
            // Never silence: a port whose delivered value exposes no
            // primitive leaf the VM can mint on has no v_H, and a row
            // without one names no occurrence two replays could be joined
            // at, so the loss is named.
            recordHandoffGap(RpcExpressionHandoff.portGap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, 0L, portId,
                    "handoff element exposes no primitive leaf: " + portId));
            return;
        }
        for (HandoffLeaf leaf : leaves) {
            mintHandoffLeaf(active, portId, exportEvent, attachEvent,
                    producerExpression, producerTaskId, producerOccurrenceId,
                    leaf, elementAbsent);
        }
    }

    /**
     * Mints v_H at one primitive leaf of one attach.
     *
     * <p>A port that crosses on a reference or an array is one attach and
     * several variables: {@code exportAllKeys} delivers a {@code BlockKey[]}
     * and what the consumer's formula reads are the leaves --
     * {@code [i].keyId}, {@code [i].expiryDate}.  One row per leaf, the leaf
     * in the element path, so each is its own handoff occurrence and R3
     * joins each to its own family.</p>
     */
    private static void mintHandoffLeaf(
            ActiveRegion active, String portId, long exportEvent,
            long attachEvent, JsonElement producerExpression,
            String producerTaskId, String producerOccurrenceId,
            HandoffLeaf leaf, boolean elementAbsent) {
        String elementPath = leaf.path;
        // H belongs to the occurrence the plan declares this IN site on,
        // not to whichever activation is live when the value arrives.  A
        // CALL_RETURN attach runs in the CALLER's frame -- the callee has
        // returned, so its activation has closed and published -- and the
        // row therefore rides on the caller while the handoff is the
        // callee's.  On hdfs-17899 bug2 that is REGION.16ba41cf's decode:
        // its rows landed on REGION.b7266d53, its caller, so one attach was
        // reported twice, unplanned there and unreproduced here.
        String consumerOccurrenceId = declaredConsumerOccurrence(portId,
                active);
        String phaseId;
        try {
            phaseId = HandoffPhaseContract.phaseId(portId,
                    OccurrenceAddress.parse(consumerOccurrenceId).render(),
                    active.nextHandoffAttach(portId + "\n" + elementPath),
                    elementPath);
        } catch (IllegalArgumentException unaddressed) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, 0L,
                    "handoff names no occurrence: "
                            + unaddressed.getMessage()));
            return;
        }
        Object owner = leaf.owner;
        Field element = leaf.field;
        String declaringClass = element.getDeclaringClass().getName();
        String fieldName = element.getName();
        String descriptor = javaTypeDescriptor(
                element.getType().getTypeName());
        try {
            ConcolicVmBroker api = engine();
            String recordedValue = recordedScalar(element.get(owner));
            // Answering is the configured source's, by construction: a
            // handoff assignment IS a configured-source assignment whose
            // phase id is this one, so the solver emits one row shape and
            // the runtime runs one mechanism.
            // The identity is the leaf's indexed path; what the VM
            // resolves on the owner is the field signature itself.
            String signature = leaf.signature();
            // The phase id IS the identity of H -- it hashes the port, the
            // consumer occurrence, k and the element path -- so the answer
            // is looked up by it alone.  Naming the port and the element
            // path again beside it was a second spelling of the same fact,
            // and the solver emits the phase.
            ModelAssignment assignment = active.configuredSourceAssignment(
                    phaseId, phaseId, "", owner);
            if (assignment != null
                    && !writeModeledField(owner, signature, assignment)) {
                throw new IllegalStateException(
                        "handoff model could not be written");
            }
            api.symbolizeExactField(owner, signature,
                    HandoffPhaseContract.engineLabelForPhase(phaseId,
                            portId));
            ensurePathRecordingStarted(active);
            JsonObject minted = exactSymbolOf(engineExpression(
                    api.fieldExpression(owner, declaringClass, fieldName,
                            descriptor, element.get(owner))));
            if (minted == null) {
                recordHandoffGap(RpcExpressionHandoff.portGap(
                        RpcExpressionHandoff.STAGE_ATTACH,
                        RpcExpressionHandoff.MALFORMED_RESULT, 0L, portId,
                        "handoff mint returned no exact variable at "
                                + portId));
                return;
            }
            if (assignment != null) active.recordModelAssignment(assignment);
            active.vmHandoffEvents.add(VmHandoffEvidence.event(portId,
                    exportEvent, attachEvent, producerExpression,
                    producerTaskId, producerOccurrenceId,
                    consumerOccurrenceId, phaseId,
                    optionalString(minted, "_exp"),
                    recordedValue, optionalString(minted, "_java_type"),
                    assignment == null ? "" : safe(assignment.value),
                    elementAbsent));
        } catch (Throwable failure) {
            recordHandoffGap(RpcExpressionHandoff.portGap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.INVOCATION_FAILED, 0L, portId,
                    "handoff mint failed at " + portId + ": "
                            + rootCause(failure)));
        }
    }

    /**
     * The occurrence this port's IN site is declared on.
     *
     * <p>The plan names it, so it is the same string on both sides and in
     * every replay; the live activation is whatever the value happened to
     * arrive under.  Falls back to the carrying activation when no task
     * declares the port, which is the case R5 names UNPLANNED_HANDOFF.</p>
     */
    private static String declaredConsumerOccurrence(String portId,
                                                     ActiveRegion carrying) {
        // The live activation that declares it, innermost first.  Several
        // occurrences of one region declare the same port -- bug2's
        // REGION.1f6914ec has five -- so "the first task in the plan that
        // declares this port" names one of them for every attach: in lane
        // B2e every handoff row came out with consumerOccurrenceId
        // REGION.1f6914ec…#5 and ONE handoff phase id, which is one
        // variable for what are several handoffs, and left the occurrence
        // that did attach reported as not having reproduced its port.
        for (Long token : CURRENT_TOKENS.get()) {
            ActiveRegion candidate = ownerRegion(token);
            if (candidate != null
                    && candidate.activation.communicationHandoff(portId,
                    false) != null) {
                return candidate.activation.occurrenceId;
            }
        }
        // None live declares it: the attach is where it is, and the row
        // says so rather than borrowing another occurrence's address.  A
        // CALL_RETURN attach whose callee has already closed and published
        // lands here, and R5 then reports it against the carrier.
        return carrying.activation.occurrenceId;
    }

    /** One primitive leaf of one attach, and how the row names it. */
    private static final class HandoffLeaf {
        private final Object owner;
        private final Field field;
        /** How the row names this leaf: indexed, so two elements differ. */
        private final String path;

        private HandoffLeaf(Object owner, Field field, String path) {
            this.owner = owner;
            this.field = field;
            this.path = path;
        }

        /** What the VM resolves on the owner: the bare field signature. */
        private String signature() {
            return exactFieldSignature(field);
        }
    }

    /** How many leaves of one attach are minted before the rest is named. */
    private static final int HANDOFF_LEAF_LIMIT = 64;

    /**
     * The primitive leaves one attach delivered.
     *
     * <p>A primitive destination is one leaf, itself.  A reference or array
     * destination is the leaves reachable through it that the VM can mint
     * on: each element's declared primitive instance fields, index-qualified
     * so two elements are two handoff occurrences.  An array of primitives
     * has no field to address and yields none, which the caller names rather
     * than passes over.</p>
     */
    private static List<HandoffLeaf> handoffLeaves(Object owner,
                                                   Field element) {
        List<HandoffLeaf> leaves = new ArrayList<>();
        if (element == null) return leaves;
        if (element.getType().isPrimitive()) {
            leaves.add(new HandoffLeaf(owner, element,
                    exactFieldSignature(element)));
            return leaves;
        }
        final Object value;
        try {
            value = element.get(owner);
        } catch (Throwable unreadable) {
            return leaves;
        }
        if (value == null) return leaves;
        if (value.getClass().isArray()) {
            int length = java.lang.reflect.Array.getLength(value);
            for (int index = 0; index < length
                    && leaves.size() < HANDOFF_LEAF_LIMIT; index++) {
                Object item = java.lang.reflect.Array.get(value, index);
                if (item == null) continue;
                addPrimitiveLeaves(item, "[" + index + "]", leaves);
            }
            return leaves;
        }
        addPrimitiveLeaves(value, "", leaves);
        return leaves;
    }

    private static void addPrimitiveLeaves(Object owner, String prefix,
                                           List<HandoffLeaf> leaves) {
        // Only the application's own objects.  An array of primitives boxes
        // each element on the way out of reflection, and java.lang.Integer's
        // own private "value" is not a leaf the workload addresses -- it is
        // the box the array element already is, and minting into it would
        // publish a handoff at a field no decode ever reads.
        if (owner.getClass().getName().startsWith("java.")) return;
        for (Field field : owner.getClass().getDeclaredFields()) {
            if (leaves.size() >= HANDOFF_LEAF_LIMIT) return;
            if (java.lang.reflect.Modifier.isStatic(field.getModifiers())
                    || !field.getType().isPrimitive()) {
                continue;
            }
            try {
                field.setAccessible(true);
            } catch (Throwable sealed) {
                continue;
            }
            leaves.add(new HandoffLeaf(owner, field,
                    prefix + exactFieldSignature(field)));
        }
    }

    /** The one exact VM root of a read-back, or null when it is not one. */
    private static JsonObject exactSymbolOf(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject root = expression.getAsJsonObject();
        if (!"SymbolExpression".equals(optionalString(root, "_type"))
                || optionalString(root, "_exp").isEmpty()
                || optionalString(root, "_java_type").isEmpty()) {
            return null;
        }
        return root;
    }

    /**
     * Whether this decision is the declared target event of the addressed
     * occurrence.
     *
     * <p>The site the plan named, at the activation of it the plan
     * addressed, decided.  Nothing else: not whether the predicate there was
     * symbolic, not whether this activation followed a replay prefix, not
     * what the outcome was.  An anchor is the fatal predicate when the
     * branch has one and the concrete outcome when it has not, and which of
     * the two it is lives in the branch row beside the reach, where the
     * composer reads it to decide a propagation cut.</p>
     *
     * <p>It was gated on a solver witness.  On hdfs-17960 the target branch
     * compares two concrete ints -- {@code i != sm.getNumSnapshots()},
     * reached by control dependence because the flip skips a decrement -- so
     * the same activation recorded the decision and was then named by
     * {@code nameUnreachedTargetBranch} as never having decided it.  Those
     * two statements cannot both be true of one activation, and the second
     * one is the one that was wrong.</p>
     *
     * @param decided             whether the decision was recorded at all,
     *                            which is false only where the VM emitted no
     *                            branch event and no row exists to state a
     *                            reach beside
     * @param permutedOccurrence  whether a bounded loop ran the planned
     *                            target occurrence at another one, which the
     *                            replay contract addressed by value
     */
    static boolean statesTargetReach(
            boolean decided, boolean permutedOccurrence,
            String targetBranchSite, int targetBranchOccurrence,
            String branchSite, int occurrence) {
        return decided && !safe(targetBranchSite).isEmpty()
                && safe(targetBranchSite).equals(safe(branchSite))
                && (permutedOccurrence
                || targetBranchOccurrence == occurrence);
    }

    /**
     * Names one element of a closing message that no decode looked up.
     *
     * <p>Called by {@link SymbolicMessageEnvelope} as the receiver drops the
     * message: at that point nothing else will ever ask for the element, so
     * the value it was carrying reaches whatever it feeds as a leaf with no
     * producer.  Refusing here rather than at the reader is what keeps the
     * loss named instead of inferred later from a literal.</p>
     */
    static void reportUnattachedMessageLeaf(String portId, int ordinal,
                                            String producerOccurrenceId) {
        recordHandoffGap(RpcExpressionHandoff.portGap(
                RpcExpressionHandoff.LEAVES_UNATTACHED,
                RpcExpressionHandoff.STAGE_ATTACH,
                RpcExpressionHandoff.MISSING_METADATA, 0L, safe(portId),
                "message element nothing decoded: " + safe(portId)
                        + " element " + ordinal + " from "
                        + safe(producerOccurrenceId)));
    }

    /**
     * A gap raised with no region running, held for the next one.
     *
     * <p>A message ends in the transport, below every selected region, so the
     * finding that nothing decoded one of its elements has no activation to
     * belong to at the moment it is made.  Dropping it there would make the
     * refusal invisible in the corpus and the whole vocabulary decorative;
     * holding it until a region publishes puts it in front of the reader that
     * has to act on it.</p>
     */
    private static final List<JsonObject> UNOWNED_HANDOFF_GAPS =
            Collections.synchronizedList(new ArrayList<JsonObject>());

    /** Files one handoff gap with the active region, or holds it. */
    /**
     * Says why a selected occurrence's outbound envelope came out empty.
     *
     * <p>The recorder swallows the refusal and returns an empty header,
     * which is right -- most sends in a workload are outside any request --
     * but inside a selected region it is the whole story: on hdfs-17899
     * bug2 the fault marker is guarded by {@code causynth.active()}, so an
     * empty Outbound means {@code Debug.makeSymbolicBoolean} is never
     * called and the region publishes NO_SELECTED_INPUT_MATERIALIZED with
     * nothing saying why.  Only a live region records it, so a workload's
     * ordinary unscoped traffic stays quiet.</p>
     */
    static void noteOutboundEnvelopeRefused(String transport,
                                            String correlationId,
                                            String half, String detail) {
        if (activeRegion() == null) return;
        recordHandoffGap(RpcExpressionHandoff.gap(
                RpcExpressionHandoff.OUTBOUND_SCOPE_REFUSED,
                RpcExpressionHandoff.STAGE_EXPORT,
                RpcExpressionHandoff.MISSING_METADATA, 0L,
                "outbound envelope refused for " + safe(transport) + " "
                        + safe(half) + " " + safe(correlationId) + ": "
                        + safe(detail)));
    }

    private static void recordHandoffGap(JsonObject gap) {
        ActiveRegion active = activeRegion();
        if (active != null) {
            drainUnownedHandoffGaps(active);
            active.rpcHandoffGaps.add(gap);
        } else {
            UNOWNED_HANDOFF_GAPS.add(gap);
        }
        diag(RpcExpressionHandoff.GAP_KIND, String.valueOf(gap));
    }

    /** Moves the gaps raised below every region into this one. */
    private static void drainUnownedHandoffGaps(ActiveRegion active) {
        if (UNOWNED_HANDOFF_GAPS.isEmpty()) return;
        synchronized (UNOWNED_HANDOFF_GAPS) {
            active.rpcHandoffGaps.addAll(UNOWNED_HANDOFF_GAPS);
            UNOWNED_HANDOFF_GAPS.clear();
        }
    }

    private static HandoffResult attach(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long handle) {
        String missing = missingFieldMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (handle <= 0L) {
            missing = firstNonBlank(missing,
                    "attach needs a positive handle");
        }
        if (!missing.isEmpty()) {
            return failed(RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, handle, missing);
        }
        ConcolicVmBroker api = engine();
        long exportEventId;
        // README RPC-1: both endpoints of the VALUE_HANDOFF edge leave the VM
        // together.
        long[] attachEvent = new long[1];
        try {
            exportEventId = api.attachExpression(owner, declaringClass,
                    fieldName, descriptor, handle, attachEvent);
        } catch (Throwable throwable) {
            return failed(RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.INVOCATION_FAILED, handle,
                    rootCause(throwable));
        }
        if (exportEventId <= 0L) {
            int status = exportStatus(exportEventId);
            return failed(RpcExpressionHandoff.STAGE_ATTACH, status, handle,
                    "attachExpression returned " + exportEventId);
        }
        if (attachEvent[0] <= 0L) {
            // A VM that accepted the attach but named no attach event has told
            // us half an edge.
            return failed(RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, handle,
                    "attachExpression named no attach event for export "
                            + exportEventId);
        }
        JsonObject success = new JsonObject();
        success.addProperty("exportEventId", exportEventId);
        success.addProperty("attachEventId", attachEvent[0]);
        return new HandoffResult(RpcExpressionHandoff.STAGE_ATTACH,
                RpcExpressionHandoff.OK, handle, success);
    }

    private static String missingFieldMetadata(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        if (owner == null) return "handoff leaf has no owner instance";
        if (firstNonBlank(declaringClass).isEmpty()
                || firstNonBlank(fieldName).isEmpty()
                || firstNonBlank(descriptor).isEmpty()) {
            return "handoff leaf has no exact declaring class, field name "
                    + "and type descriptor";
        }
        return "";
    }

    /** Maps a non-positive {@code exportExpression} answer onto a status. */
    private static int exportStatus(long handle) {
        if (handle == 0L || handle < Integer.MIN_VALUE) {
            return RpcExpressionHandoff.MALFORMED_RESULT;
        }
        return (int) handle;
    }

    private static HandoffResult failed(String stage, int status, long handle,
                                        String detail) {
        return new HandoffResult(stage, status, handle,
                RpcExpressionHandoff.gap(stage, status, handle, detail));
    }

    /**
     * Files failed calls with the active region and reports every outcome to
     * the diagnostic trace.
     */
    private static HandoffResult record(HandoffResult result) {
        ActiveRegion active = activeRegion();
        if (active != null) drainUnownedHandoffGaps(active);
        if (active != null && !result.ok()) {
            active.rpcHandoffGaps.add(result.record);
        }
        if (!result.ok()) {
            diag(RpcExpressionHandoff.GAP_KIND, result.toString());
        }
        return result;
    }



    /**
     * Invocation-exact normal cleanup used by injected roots.  This method is
     * intentionally no-throw: instrumentation bookkeeping must never turn a
     * normal program return into an exception (or let the synthetic catch-all
     * pop an enclosing frame a second time).
     */
    public static void exitRegionFrame(String instrumentationSelector,
                                       String rootMethod) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    instrumentationSelector, rootMethod);
            if (frame != null && frame.token != 0L) {
                finish(frame.token, "NORMAL", "", null);
            }
        } catch (Throwable ignored) {
            // Runtime observation is fail-closed and cannot alter the return.
        }
    }

    /**
     * Invocation-exact exceptional cleanup used by the synthetic catch-all.
     * The original throwable is rethrown by injected bytecode; consequently
     * every runtime failure is swallowed here so it cannot replace it.
     */
    public static void throwRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Throwable throwable) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    instrumentationSelector, rootMethod);
            if (frame != null && frame.token != 0L) {
                if (throwable instanceof LoopBoundCut) {
                    finish(frame.token, "CUT", "", throwable);
                } else {
                    finish(frame.token, "THROW",
                            throwable == null ? ""
                                    : throwable.getClass().getName(),
                            throwable);
                }
            }
        } catch (Throwable ignored) {
            // Preserve the program's original throwable identity.
        }
    }

    private static RootInvocationFrame popRootInvocationFrame(
            String instrumentationSelector, String rootMethod) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = frames.peek();
        if (frame == null) {
            ROOT_INVOCATION_FRAMES.remove();
            return null;
        }
        boolean matches = sameHookIdentity(frame.instrumentationSelector,
                instrumentationSelector)
                && sameHookIdentity(frame.rootMethod, rootMethod);
        if (!matches) {
            // Never guess ownership.  In particular, do not expose or close
            // an outer selected frame when instrumentation is malformed.
            return null;
        }
        frames.pop();
        if (frames.isEmpty()) {
            ROOT_INVOCATION_FRAMES.remove();
        }
        return frame;
    }

    /**
     * The sibling-hook accounting both root stacks share: one physical entry
     * emits one hook per plan row, and only the first is an activation.
     */
    private static class SiblingHookGroupEntry {
        final String groupKey;
        private int remainingSiblingHooks;

        SiblingHookGroupEntry(String groupKey, int remainingSiblingHooks) {
            this.groupKey = safe(groupKey);
            this.remainingSiblingHooks = remainingSiblingHooks;
        }

        /** Absorbs one further hook emitted at this same physical entry. */
        final boolean claimsSiblingHook(String actualGroupKey) {
            if (remainingSiblingHooks <= 0
                    || !groupKey.equals(safe(actualGroupKey))) {
                return false;
            }
            remainingSiblingHooks--;
            return true;
        }
    }

    private static final class RootInvocationFrame
            extends SiblingHookGroupEntry {
        private final String instrumentationSelector;
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String instrumentationSelector,
                                    String rootMethod, String rootHookGroupKey,
                                    int remainingSiblingHooks,
                                    long token) {
            super(rootHookGroupKey, remainingSiblingHooks);
            this.instrumentationSelector = instrumentationSelector;
            this.rootMethod = rootMethod;
            this.token = token;
        }
    }

    /** Static hook group that instrumentation placed at one Java entry. */
    static final class RootHookGroup {
        final String key;
        final int hookCount;

        RootHookGroup(String key, int hookCount) {
            this.key = safe(key);
            this.hookCount = Math.max(1, hookCount);
        }
    }

    /** One real enclosing method invocation for bounded body activations. */
    static final class LoopRootInvocationContext
            extends SiblingHookGroupEntry {
        /** This invocation's entry event: what a loop task is bound to. */
        final long token;
        /** The thread that ran it, as the recording names threads. */
        final String threadName = Thread.currentThread().getName();
        /** Which k this entry was counted at, per task it was offered to. */
        private final Map<String, Integer> ordinalByTaskId;

        private LoopRootInvocationContext(
                long token, String groupKey, int remainingSiblingHooks,
                Map<String, Integer> ordinalByTaskId) {
            super(groupKey, remainingSiblingHooks);
            this.token = token;
            this.ordinalByTaskId = Collections.unmodifiableMap(
                    new LinkedHashMap<>(ordinalByTaskId));
        }

        /** The observed activation ordinal this entry took for a task. */
        int ordinalOf(String taskId) {
            Integer ordinal = ordinalByTaskId.get(taskId);
            return ordinal == null ? 0 : ordinal;
        }
    }

    /**
     * Reserves a VM-attested branch event immediately before the original
     * conditional executes.
     */
    public static long prepareBranch(String method, int unitIndex,
                                     String expression) {
        ActiveRegion active = activeRegion();
        if (active == null || !active.pathRecordingStarted) return 0L;
        try {
            PreparedBranch prepared = active.prepareBranch(method, unitIndex,
                    expression);
            return prepared == null ? 0L : prepared.handle;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch event preparation failed: "
                    + rootCause(throwable));
            return 0L;
        }
    }

    /**
     * Exact-event overload carrying the id returned by the native marker that
     * the instrumented class executes immediately before its original if.
     */
    public static boolean resolveBranch(long preparedHandle, long vmEventId,
                                        String method, int unitIndex,
                                        String expression,
                                        boolean observedOutcome) {
        observeDecision(BranchDecision.binary(observedOutcome), preparedHandle,
                vmEventId, method, unitIndex, expression);
        return observedOutcome;
    }

    /** Exact multiway counterpart of {@link #resolveBranch}. */
    public static int resolveSwitchBranch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        SwitchExpectation expected;
        try {
            expected = SwitchExpectation.parse(branchKind, encodedCaseKeys,
                    observedSuccessorIndex);
        } catch (IllegalArgumentException malformed) {
            ActiveRegion active = activeRegion();
            if (active != null) {
                active.addUnresolvedOnce(SiteId.render(method, unitIndex)
                        + ": invalid static switch contract: "
                        + rootCause(malformed));
            }
            return observedSuccessorIndex;
        }
        observeDecision(BranchDecision.multiway(expected), preparedHandle,
                vmEventId, method, unitIndex, expression);
        return observedSuccessorIndex;
    }

    /**
     * Observes one decision of either kind at one instrumented site.
     *
     * <p>The workload's own value is the hook's to return: nothing observed
     * here may change it, so this reports nothing back.</p>
     */
    private static void observeDecision(
            BranchDecision decision, long preparedHandle, long vmEventId,
            String method, int unitIndex, String expression) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        String branchSite = SiteId.render(method, unitIndex);
        boolean declared = active.activation.declaresBranch(branchSite);
        boolean replayBoundary = active.activation
                .observesReplayBoundary(branchSite);
        if (!declared && !replayBoundary) {
            active.takePreparedBranch(preparedHandle);
            return;
        }
        if (!declared) {
            PreparedBranch prepared = active.takePreparedBranch(
                    preparedHandle);
            int occurrence;
            if (!active.pathRecordingStarted) {
                occurrence = active.nextBranchOccurrence(branchSite);
            } else if (prepared != null && prepared.matches(method,
                    unitIndex, expression)) {
                occurrence = prepared.occurrence;
            } else {
                active.addUnresolvedOnce("missing or mismatched "
                        + decision.boundaryNoun() + " " + preparedHandle
                        + " for " + branchSite);
                return;
            }
            ExactConcreteBranchObservation observation =
                    active.recordReplayBoundary(method, unitIndex,
                            occurrence, decision);
            if (observation != null) {
                active.observeReplayDecision(branchSite, occurrence,
                        decision);
            }
            if (active.replayPrefixContradicted()) {
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                        null);
            }
            return;
        }
        if (!active.pathRecordingStarted) {
            ExactConcreteBranchObservation observation =
                    active.recordConcreteDecision(method, unitIndex,
                            decision);
            if (observation != null) {
                active.observeReplayDecision(observation.siteId(),
                        observation.occurrence(), decision);
                if (active.replayPrefixContradicted()) {
                    finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                            null);
                }
            }
            return;
        }
        PreparedBranch prepared = active.takePreparedBranch(preparedHandle);
        if (prepared == null || !prepared.matches(method, unitIndex,
                expression)) {
            active.addUnresolvedOnce("missing or mismatched "
                    + decision.preparedNoun() + " " + preparedHandle
                    + " for " + branchSite);
            // No unverified VM event may be rebound heuristically on a JDK
            // that advertised the exact API.
            return;
        }
        ConcolicVmBroker api = engine();
        boolean paused = false;
        boolean replayContradicted = false;
        try {
            api.pausePathCondition();
            paused = true;
            RecordedBranch recorded = decision.recordPaused(active, api,
                    method, unitIndex, expression, prepared.occurrence,
                    vmEventId);
            // Advances the replay contract and records a prefix mismatch;
            // whether this decision consumed the contract's source event
            // says nothing about whether the target site ran.
            active.observeReplayDecision(branchSite, prepared.occurrence,
                    decision, recorded.symbolicSupportDigest);
            replayContradicted = active.replayPrefixContradicted();
            // A bounded loop may have run the planned target occurrence at
            // another one.  targetReach is the planner's semantic source
            // address; the branch mapping beside it retains the actual
            // occurrence and symbolic support which matched that source.
            boolean permuted = decision.addressesPermutedTargetOccurrence()
                    && active.activation.replayContract != null;
            if (statesTargetReach(recorded.decided, permuted,
                    active.activation.targetBranchSite,
                    active.activation.targetBranchOccurrence,
                    branchSite, prepared.occurrence)) {
                // Reaching the target is the site having executed, and
                // nothing else -- including whether the predicate there was
                // symbolic.  It was gated on a solver witness, so a target
                // branch that compares two concrete values published no
                // reach at all: on hdfs-17960 the fatal branch is
                // "i != sm.getNumSnapshots()" over two concrete ints, which
                // the root reaches by control dependence (the flip skips a
                // decrement), and the same activation then recorded the
                // decision AND was named as never having decided it.  The
                // anchor evidence is the fatal predicate when there is one
                // and the concrete outcome when there is not; which of the
                // two it is belongs in the branch row beside it, where the
                // composer reads it to decide a propagation cut.
                //
                // The replay contract decides whether this
                // activation followed the prefix it was asked to follow --
                // a different question, and one whose answer is "no" at the
                // target on every flip replay whose source branch is
                // somewhere else, because the contract names no event here
                // to consume.  Gating on it published the target event only
                // from the recording, so every flip's disjunct was lost
                // before composition ever saw it.  The composition wants
                // them all: a flip that leaves the predicate false is the
                // disjunct that contributes nothing, and a flip that
                // diverges is still evidence that the branch was tried.
                //
                // Reaching the target is also a fact of this case, never a
                // reason to stop recording it: the RPC, state and throw
                // effects the occurrence still owes all happen after this
                // branch.
                active.recordTargetReach(
                        permuted ? active.activation.targetBranchSite
                                : branchSite,
                        permuted ? active.activation.targetBranchOccurrence
                                : prepared.occurrence,
                        decision.outcome(), vmEventId);
            }
        } catch (Throwable throwable) {
            active.addUnresolvedOnce(decision.observationNoun()
                    + " exact-event observation failed: "
                    + rootCause(throwable));
        } finally {
            if (paused) resumePathCondition(active, api);
            if (replayContradicted) {
                // Release the engine here rather than at this activation's own
                // return: the branch that just executed already decided that
                // nothing publishable can follow.
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    private static RecordedBranch recordBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        if (vmEventId <= 0L) {
            // The VM emitted no symbolic branch event.
            return RecordedBranch.NONE;
        }
        String siteId = SiteId.render(method, unitIndex);
        int baseline = active.lastPathConditionSize;
        // One read of the event stream, used by both questions asked of it.
        JsonElement events = parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        // An exact conditionless event contributes no branch guard, and a
        // non-contiguous one names no exact range: both leave the window
        // empty and the raw size at the baseline.
        boolean exactRange = !noVmCondition
                && contiguousConditionIndices(eventConditionIndices);
        PathConditionWindow.Read read = PathConditionWindow.forEvent(
                active.expressionStore, api, eventConditionIndices,
                (start, end) -> diag("PC_READ_BEGIN", siteId + " occ="
                        + occurrence + " range=[" + start + "," + end + ")"));
        PathConditionWindow conditions = read.conditions;
        int rawPathConditionSize = exactRange ? conditions.size() : baseline;
        int attestationBaseline = noVmCondition ? 0 : baseline;
        if (exactRange) {
            diag("PC_READ_END", siteId + " occ=" + occurrence
                    + " chars=" + read.chars + " source=" + read.source);
            diag("PC_PARSED", siteId + " occ=" + occurrence
                    + " conditions=" + rawPathConditionSize
                    + " mode=" + conditions.mode());
        }
        VmBranchEventAttestation vmAttestation = attestVmBranchEvent(api,
                active, siteId, expression, observedOutcome, vmEventId,
                occurrence, conditions, attestationBaseline, null, events);
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence,
                vmEventId);
        // Exact VM ownership is one condition for an IfStmt.
        int mappingBaseline = conditionIndex >= 0
                ? conditionIndex : baseline;
        int mappingLimit = conditionIndex >= 0
                ? conditionIndex + 1 : rawPathConditionSize;
        mapping.addProperty("rawPathConditionSize", mappingLimit);
        mapping.addProperty("rawPathConditionBaseline", mappingBaseline);
        String symbolicSupportDigest = "";
        if (conditionIndex >= 0) {
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition = semanticBranchCondition(
                    expression, observedOutcome, condition);
            String rawOperator = binaryOperator(condition);
            String semanticOperator = binaryOperator(semanticCondition);
            if (vmAttestation.valid) {
                symbolicSupportDigest =
                        BranchPredicateAlgebra.symbolicSupportDigest(
                                semanticCondition);
                JsonObject metadata = new JsonObject();
                metadata.addProperty("predicateNormalization",
                        safe(rawOperator).equals(safe(semanticOperator))
                                ? BranchWitness.IDENTITY_NORMALIZATION
                                : BranchWitness.CMP_NORMALIZATION);
                BranchWitness witness = BranchWitness.vmPcImmutable(siteId,
                        safe(method), unitIndex, occurrence,
                        observedOutcome, semanticCondition, conditionIndex,
                        metadata);
                mapping.add("witness", witness.toImmutableJsonView());
            }
        } else if (vmAttestation.valid
                && vmAttestation.conditionIndices.isEmpty()) {
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attested(siteId,
                            safe(method), unitIndex, occurrence,
                            observedOutcome).toJson());
        }
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
        // A row was published for this decision: the site executed and the
        // outcome beside it is this execution's own.  Whether it carried a
        // path condition is the difference between a symbolic witness and a
        // concreteObservation in that row, and the composer reads it there.
        return new RecordedBranch(true, symbolicSupportDigest);
    }

    /**
     * Result of one exact capture: whether this decision was recorded at
     * all, and the symbolic support a binary branch matched its replay
     * prefix on.  A multiway successor is its own authority and carries no
     * support.
     *
     * <p>{@code decided} is false only where the VM emitted no branch event
     * to capture, and there is no row beside which a target reach could be
     * stated.  It used to mean "attested well enough to address a target
     * reach", which read the presence of a path condition as permission to
     * publish the anchor -- so an activation that decided the target site
     * concretely published a branch row and no reach.</p>
     */
    private static final class RecordedBranch {
        private static final RecordedBranch NONE =
                new RecordedBranch(false, "");
        private final boolean decided;
        private final String symbolicSupportDigest;

        private RecordedBranch(boolean decided,
                               String symbolicSupportDigest) {
            this.decided = decided;
            this.symbolicSupportDigest = safe(symbolicSupportDigest);
        }
    }


    private static boolean recordSwitchBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        String siteId = SiteId.render(method, unitIndex);
        int baseline = active.lastPathConditionSize;
        JsonElement events = parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        // The switch hook does not trace the range it is about to read.
        PathConditionWindow.Read read = PathConditionWindow.forEvent(
                active.expressionStore, api, eventConditionIndices, null);
        diag("PC_READ_END", siteId + " occ=" + occurrence
                + " chars=" + read.chars + " source=" + read.source);
        PathConditionWindow conditions = read.conditions;
        VmBranchEventAttestation attestation = attestVmBranchEvent(api,
                active, siteId, expression, expected.caseArm(), vmEventId,
                occurrence, conditions, noVmCondition ? 0 : baseline,
                expected, events);
        List<Integer> conditionIndices = attestation.valid
                ? attestation.conditionIndices
                : Collections.<Integer>emptyList();
        int mappingBaseline = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(0);
        int mappingLimit = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(
                conditionIndices.size() - 1) + 1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence,
                vmEventId);
        mapping.addProperty("rawPathConditionSize", mappingLimit);
        mapping.addProperty("rawPathConditionBaseline", mappingBaseline);
        if (!attestation.valid) {
            active.addUnresolvedOnce(siteId
                    + ": exact switch event attestation failed: "
                    + attestation.error);
        } else {
            // The source-level successor is the replay authority.  Its VM
            // predicates below constrain this path but are never Boolean flip
            // sources of their own.
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attestedSwitch(siteId,
                            safe(method), unitIndex, occurrence,
                            expected.branchKind, expected.caseKeys,
                            expected.observedSuccessorIndex).toJson());
        }
        active.branchMappings.add(mapping);
        if (attestation.valid) {
            int decisionOrdinal = 1;
            for (Integer conditionIndex : conditionIndices) {
                JsonObject predicate = branchMapping(method, unitIndex,
                        occurrence, vmEventId);
                predicate.addProperty("rawPathConditionSize", mappingLimit);
                predicate.addProperty("rawPathConditionBaseline",
                        mappingBaseline);
                predicate.add("witness",
                        BranchWitness.pcPredicateImmutable(siteId,
                                safe(method), unitIndex, occurrence,
                                decisionOrdinal++,
                                conditions.get(conditionIndex),
                                conditionIndex).toImmutableJsonView());
                active.branchMappings.add(predicate);
            }
        }
        active.lastPathConditionSize = Math.max(
                active.lastPathConditionSize, mappingLimit);
        return attestation.valid;
    }

    /**
     * One published decision row.
     *
     * <p>{@code vmEventId} is the VM's own event sequence number for the
     * decision -- the id the native marker returned immediately before the
     * workload's branch.  It is the only monotone per-replay clock the
     * publication carries: {@code unitIndex} and the path-condition indices
     * are positions inside a method and inside one condition window, and
     * {@code startedAtMillis} is telemetry.  A composer needs this to say
     * which decisions were taken before an anchor and in what order two
     * activations' decisions interleave.</p>
     *
     * <p>Nothing here reads the id's scale.  It was a per-ThreadContext
     * counter -- 1, 2, 3 per thread, restarting for every context -- and the
     * VM now draws it from the session-global event counter, the same one
     * behind {@code fieldVersionId}, {@code readEventId} and
     * {@code regionEnterEventId}.  The values stop being small and dense and
     * start interleaving with the write log's, which is the point: "the
     * latest write whose event precedes this decision" becomes a valid
     * comparison, within one {@code sessionId}.  This publication is
     * unchanged either way, and the only other runtime use of the id is the
     * exact-event lookup in {@code PathConditionWindow}, which matches on
     * equality and requires the id to be unique among the events read -- true
     * on both scales.</p>
     *
     * <p>It is published only when the VM assigned one.  A decision recorded
     * with the symbolic gate closed has no VM event, and stating a zero there
     * would order it ahead of everything the VM did record.</p>
     */
    private static JsonObject branchMapping(
            String method, int unitIndex, int occurrence, long vmEventId) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", SiteId.render(method, unitIndex));
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        if (vmEventId > 0L) mapping.addProperty("vmEventId", vmEventId);
        return mapping;
    }

    /**
     * @param readEvents the caller's own read of the exact event stream, or
     *                   {@code null} to read it here.  A caller that has
     *                   already asked the stream a question about this event
     *                   passes what it read: a second read costs a full
     *                   serialization and decode of every event the thread has
     *                   recorded, and would let the two answers be taken from
     *                   two different observations of it.
     */
    private static VmBranchEventAttestation attestVmBranchEvent(
            ConcolicVmBroker api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, PathConditionWindow conditions, int baseline,
            SwitchExpectation switchExpectation, JsonElement readEvents) {
        if (eventId <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "marker returned a non-positive event id");
        }
        final JsonElement parsed;
        if (readEvents != null) {
            parsed = readEvents;
        } else {
            try {
                parsed = parseJson(api.branchEvents());
            } catch (Throwable throwable) {
                return VmBranchEventAttestation.invalid(
                        "event stream is not readable: "
                                + rootCause(throwable));
            }
        }
        if (!parsed.isJsonObject()) {
            return VmBranchEventAttestation.invalid(
                    "event stream is not a JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        if (optionalInteger(envelope, "schemaVersion", -1) != 1
                || !"CONCOLIC_THREAD_BRANCH_EVENTS".equals(
                optionalString(envelope, "kind"))
                || !optionalBool(envelope, "active", false)) {
            return VmBranchEventAttestation.invalid(
                    "unexpected or inactive event stream");
        }
        long envelopeContext = optionalLongInteger(envelope, "contextId", 0L);
        long envelopeOwner = optionalLongInteger(envelope,
                "ownerJavaThreadId", 0L);
        if (envelopeContext <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "missing positive VM thread context id");
        }
        if (envelopeOwner != active.thread.getId()) {
            return VmBranchEventAttestation.invalid(
                    "event stream belongs to Java thread " + envelopeOwner
                            + " instead of " + active.thread.getId());
        }
        if (!safe(active.activation.regionId).equals(
                optionalString(envelope, "regionId"))
                || !safe(active.activation.taskId).equals(
                optionalString(envelope, "taskId"))) {
            return VmBranchEventAttestation.invalid(
                    "event stream region/task does not match owner");
        }

        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(envelope, "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (optionalLongInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) {
            return VmBranchEventAttestation.invalid(
                    "event id " + eventId + " matched " + matches
                            + " records");
        }
        String authority = optionalString(selected, "authority");
        if (!"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(authority)) {
            return VmBranchEventAttestation.invalid(
                    "unsupported event authority " + authority);
        }
        if (!safe(siteId).equals(optionalString(selected, "siteId"))
                || optionalInteger(selected, "occurrence", -1) != occurrence) {
            return VmBranchEventAttestation.invalid(
                    "event site/occurrence does not match prepared branch");
        }
        if (optionalBool(selected, "outcome", !observedOutcome)
                != observedOutcome) {
            return VmBranchEventAttestation.invalid(
                    "event outcome differs from observed branch");
        }
        JsonArray indices = array(selected, "conditionIndices");
        if (optionalInteger(selected, "conditionCount", -1) != indices.size()) {
            return VmBranchEventAttestation.invalid(
                    "event condition count differs from its index vector");
        }
        if (switchExpectation != null) {
            return attestVmSwitchConditions(selected,
                    switchExpectation, indices, conditions);
        }
        if (indices.size() > 1) {
            return VmBranchEventAttestation.invalid(
                    "instrumented IfStmt emitted multiple condition indices");
        }
        int conditionIndex = -1;
        if (indices.size() == 1) {
            try {
                conditionIndex = indices.get(0).getAsInt();
            } catch (RuntimeException exception) {
                return VmBranchEventAttestation.invalid(
                        "condition index is not an integer");
            }
            if (conditionIndex < baseline
                    || conditionIndex >= conditions.size()) {
                return VmBranchEventAttestation.invalid(
                        "condition index " + conditionIndex
                                + " is outside new path-condition suffix ["
                                + baseline + "," + conditions.size() + ")");
            }
            if (!branchConditionMatches(expression, observedOutcome,
                    conditions.get(conditionIndex))) {
                return VmBranchEventAttestation.invalid(
                        "selected VM condition does not match the original "
                                + "branch predicate");
            }
        }
        return VmBranchEventAttestation.valid(
                conditionIndex < 0
                        ? Collections.<Integer>emptyList()
                        : Collections.singletonList(conditionIndex));
    }

    private static VmBranchEventAttestation attestVmSwitchConditions(
            JsonObject event, SwitchExpectation expected,
            JsonArray rawIndices, PathConditionWindow conditions) {
        int expectedOpcode = "TABLE_SWITCH".equals(expected.branchKind)
                ? 170 : 171;
        if (optionalInteger(event, "opcode", -1) != expectedOpcode) {
            return VmBranchEventAttestation.invalid(
                    "event opcode does not match static "
                            + expected.branchKind);
        }
        if (optionalString(event, "codePosition").isEmpty()) {
            return VmBranchEventAttestation.invalid(
                    "switch event has no bytecode position");
        }

        int completeSymbolicCount = expected.caseArm()
                ? 1 : expected.caseKeys.size();
        // The VM still emits an exact event when the selector is concrete.
        if (rawIndices.size() == 0) {
            return VmBranchEventAttestation.valid(
                    Collections.<Integer>emptyList());
        }
        if (rawIndices.size() != completeSymbolicCount) {
            return VmBranchEventAttestation.invalid(
                    "switch arm owns " + rawIndices.size()
                            + " conditions; exact arm requires "
                            + completeSymbolicCount);
        }
        List<Integer> indices = new ArrayList<>();
        String selector = "";
        String expectedPosition = optionalString(event, "codePosition");
        int previousIndex = -1;
        for (int offset = 0; offset < rawIndices.size(); offset++) {
            final int conditionIndex;
            try {
                conditionIndex = rawIndices.get(offset).getAsInt();
            } catch (RuntimeException malformed) {
                return VmBranchEventAttestation.invalid(
                        "switch condition index is not an integer");
            }
            if (conditionIndex < 0
                    || offset > 0 && conditionIndex != previousIndex + 1) {
                return VmBranchEventAttestation.invalid(
                        "switch condition indices are not one exact ordered "
                                + "VM event range");
            }
            final JsonElement condition;
            try {
                condition = conditions.get(conditionIndex);
            } catch (IndexOutOfBoundsException unavailable) {
                return VmBranchEventAttestation.invalid(
                        "switch condition index " + conditionIndex
                                + " is outside the exact VM event range");
            }
            int key = expected.caseArm()
                    ? expected.caseKeys.get(
                    expected.observedSuccessorIndex)
                    : expected.caseKeys.get(offset);
            String operator = expected.caseArm() ? "==" : "!=";
            String matchedSelector = switchSelectorIfMatches(condition,
                    operator, key);
            if (matchedSelector.isEmpty()) {
                return VmBranchEventAttestation.invalid(
                        "switch condition " + offset
                                + " is not selector " + operator + " "
                                + key);
            }
            if (selector.isEmpty()) {
                selector = matchedSelector;
            } else if (!selector.equals(matchedSelector)) {
                return VmBranchEventAttestation.invalid(
                        "switch conditions do not share one selector");
            }
            String conditionPosition = condition.isJsonObject()
                    ? optionalString(condition.getAsJsonObject(), "_code_position")
                    : "";
            if (!conditionPosition.isEmpty()
                    && !expectedPosition.equals(conditionPosition)) {
                return VmBranchEventAttestation.invalid(
                        "switch condition bytecode position differs from "
                                + "its exact event");
            }
            indices.add(conditionIndex);
            previousIndex = conditionIndex;
        }
        return VmBranchEventAttestation.valid(indices);
    }

    private static String switchSelectorIfMatches(
            JsonElement condition, String expectedOperator, int expectedKey) {
        if (condition == null || !condition.isJsonObject()) return "";
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))
                || !expectedOperator.equals(optionalString(object, "_op"))) {
            return "";
        }
        JsonElement left = object.get("_left");
        JsonElement right = object.get("_right");
        if (left == null || !left.isJsonObject()
                || right == null || !right.isJsonObject()
                || "ConstExpr".equals(optionalString(left.getAsJsonObject(),
                "_type"))) {
            return "";
        }
        JsonObject constant = right.getAsJsonObject();
        if (!"ConstExpr".equals(optionalString(constant, "_type"))) return "";
        Matcher encoded = Pattern.compile("^Y_I_(-?(?:0|[1-9][0-9]*))$")
                .matcher(optionalString(constant, "_exp"));
        if (!encoded.matches()) return "";
        final int key;
        try {
            key = Integer.parseInt(encoded.group(1));
        } catch (NumberFormatException malformed) {
            return "";
        }
        return key == expectedKey ? left.toString() : "";
    }

    /** Marks one selected occurrence unusable before its VM close. */
    private static void abandonOccurrence(
            ActiveRegion active, String skipKind, String reason) {
        active.releaseActivationOrdinal();
        active.abandoned = true;
        active.terminalGap = true;
        endLiveSelectedRegion();
        writeSkipped(active.activation, skipKind, reason, null);
    }

    /** Ends whichever selected occurrence owns {@code token}. */
    private static void finish(long token, String exitKind,
                               String exceptionType, Throwable throwable) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return;
        finishOccurrence(active, exitKind, exceptionType, throwable);
    }

    private static void finishOccurrence(ActiveRegion active, String exitKind,
                                         String exceptionType,
                                         Throwable throwable) {
        if (!active.finished.compareAndSet(false, true)) return;
        beginSelectedResultPublication();
        boolean publicationDeferred = false;
        // Judgement and publication are bookkeeping, not workload control
        // flow, so they remain muted until this occurrence's VM context is
        // closed.
        beginBookkeeping();
        try {
            try {
                // Exact call-site traps normally close every accessor scope
                // first.
                AccessorCallContext scope =
                        CURRENT_ACCESSOR_CALL_CONTEXT.get();
                if (scope != null && scope.regionToken == active.token) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                }
                diag("REGION_FINISH", "token=" + active.token
                        + " task=" + safe(active.activation.taskId)
                        + " source=" + active.attributedSourceKeys()
                        + " exit=" + safe(exitKind));
                active.exitKind = safe(exitKind);
                active.exceptionType = safe(exceptionType);
                active.exitThrowable = throwable;
                judgeFinishedOccurrence(active);
            } finally {
                publicationDeferred = closeOccurrence(active);
            }
        } finally {
            endBookkeeping();
            if (!publicationDeferred) endSelectedResultPublication();
        }
    }

    /**
     * Applies the admission gates a finished occurrence must pass before its
     * relation may be built.
     */
    private static void judgeFinishedOccurrence(ActiveRegion active) {
        // First, because it is the only gate that asks whether this activation
        // is the addressed occurrence at all.
        String unaddressed =
                active.activation.rootContextSelector.unconfirmed(
                        active.attributedSourceKeys());
        if (!unaddressed.isEmpty()) {
            // A candidate that is not the addressed occurrence is the
            // candidate loop working, not a finding, so it is released without
            // a durable row.
            active.activation.noteUnaddressedCandidate(unaddressed);
            active.releaseActivationOrdinal();
            active.abandoned = true;
            endLiveSelectedRegion();
            return;
        }
        // The source/address gate has now answered this planned occurrence.
        // A later prefix or materialization rejection owns the sole durable
        // diagnostic; do not also report the same activation as an unmatched
        // occurrence when the workload terminates.
        configuration().markOccurrenceClaimed(active.activation);
        // A target address that several activations of one region on one
        // source answer is separated by the only thing that distinguishes
        // them: whether this activation reached the declared target event.
        // One that did not has not answered the address, so it releases it by
        // name and the next candidate is tried - which is what README OCC-1
        // means by treating each target occurrence as a candidate.
        // An activation that did not take the declared target event is not a
        // rejected candidate: it is an occurrence of this address that did
        // something else, and it publishes with targetReached:false so the
        // importer never selects it as THE target case.

        if (active.replayPrefixContradicted()) {
            abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                    "activation contradicts the recorded replay prefix: "
                            + active.replayProgress.failure());
            return;
        }
        // Replay progress is frozen at this terminal.
        if (active.activation.replayContract != null) {
            if (!active.replayProgress.complete()) {
                abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                        "no compatible activation matched replay prefix: "
                                + active.replayProgress.failure());
                return;
            }
        }
        List<String> unapplied = new ArrayList<>();
        for (ModelAssignment assignment
                : active.activation.modelAssignments) {
            if (active.appliedModelAssignments.contains(assignment.key)) {
                continue;
            }
            // A model for a configured source names a mint SITE, and the
            // site is reached by whichever activation runs it.  An
            // activation that did not reach it minted nothing to write the
            // model into and owes nothing: on lane VM12 six companions
            // addressed at REGION.08ab84c9 carried the serialNo model whose
            // mint site is in updateKeys() -- REGION.aaa1cfd7, another
            // member of the same linked group -- and were refused at their
            // terminal for not applying a model that was never theirs to
            // apply.  A model this activation DID mint for and did not
            // write is still a refusal, which is the case this gate is for.
            if (assignment.configuredSourceAssignment()
                    && !active.owesConfiguredSourceModel(
                    assignment.configuredSourcePhaseId)) {
                continue;
            }
            unapplied.add(assignment.key);
        }
        if (!unapplied.isEmpty()) {
            // Every linked member owns its explicit source assignments.  A
            // companion has no branch replay contract, but allowing it to
            // publish before applying these rows would silently leave an
            // upstream root concrete.
            abandonOccurrence(active, SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                    "terminal reached with unapplied model assignment keys "
                            + unapplied);
            return;
        }
        List<String> unappliedReads = new ArrayList<>();
        for (GuardedReadAssignment assignment
                : active.activation.guardedReadAssignments) {
            if (active.materializedGuardedReads.contains(
                    assignment.readIdentity)) {
                continue;
            }
            Long token = active.armedGuardedReads.get(
                    assignment.readIdentity);
            if (token == null) {
                unappliedReads.add(assignment.readIdentity + ":NOT_ARMED");
                continue;
            }
            try {
                long status = engine().confirmSharedPrimitiveFieldRead(token);
                if (status > 0L) {
                    active.materializedGuardedReads.add(
                            assignment.readIdentity);
                } else {
                    unappliedReads.add(assignment.readIdentity
                            + ":NOT_CONSUMED(" + status + ")");
                }
            } catch (Throwable failure) {
                unappliedReads.add(assignment.readIdentity
                        + ":CONFIRM_FAILED(" + rootCause(failure) + ")");
            }
        }
        if (!unappliedReads.isEmpty()) {
            abandonOccurrence(active, SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                    "terminal reached with unapplied guarded read "
                            + "assignments " + unappliedReads);
            return;
        }
        if (active.activation.replayContract != null) {
            return;
        }
    }

    /**
     * Reads one occurrence and closes its VM region on the owner thread, then
     * transfers JSON decoding and durable publication to the daemon pool.
     *
     * @return true only when the publication executor owns the in-flight
     *         publication counter
     */
    private static boolean closeOccurrence(ActiveRegion active) {
        if (!active.beginClose()) return false;
        boolean hasEnclosingRegion = hasEnclosingActiveRegion(active);
        ActiveRegion enclosingRegion = hasEnclosingRegion
                ? enclosingActiveRegion(active) : null;
        ConcolicVmBroker api = engine();
        boolean engineFinished = false;
        boolean pathConditionPaused = false;
        String rawEngineSummary = null;
        RawSharedStateReadOut rawSharedState = null;
        JsonObject result = null;
        try {
            // Everything below is observational bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
            try {
                if (!active.abandoned) {
                    result = new JsonObject();
                    // One ordinal names every row assembled for this close.
                    active.evidenceSnapshot =
                            EVIDENCE_SNAPSHOTS.incrementAndGet();
                    RecordedEvidenceIdentity identity =
                            evidenceIdentity(active);
                    try {
                        buildCompletedResult(result, active, identity);
                    } catch (Throwable throwable) {
                        result.addProperty("engineSummaryError",
                                rootCause(throwable));
                    }
                    try {
                        rawSharedState = captureRecordedSharedStateRaw(active,
                                api, identity);
                    } catch (Throwable throwable) {
                        active.sharedStateGaps.add(SharedStateEvidence.gap(
                                SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.INVOCATION_FAILED, "",
                                rootCause(throwable)));
                    }
                }
            } finally {
            }
            String summary = api.finish();
            engineFinished = true;
            // Symbolic state created or attached in a nested region remains
            // on the VM values returned to its caller.  The native thread PC
            // gate remains admitted as well, so open the caller's Java branch
            // gate before its next selected conditional executes.
            if (enclosingRegion != null && active.pathRecordingStarted) {
                enclosingRegion.pathRecordingStarted = true;
            }
            // Finishing an inner native region pops only that region.  Its
            // caller continues in the same thread context, so undo the pause
            // that protected this read-out before returning to application
            // code.  An outermost finish detached the context and needs no
            // balancing call.
            if (hasEnclosingRegion) {
                api.resumePathCondition();
                pathConditionPaused = false;
            }
            if (jsonObjectEnvelope(summary)) {
                // The VM already serialized this large object.
                rawEngineSummary = summary;
            } else if (result != null) {
                result.addProperty("engineSummaryError",
                        "VM summary is not a JSON object");
            }
        } catch (Throwable throwable) {
            if (result != null) {
                result.addProperty("engineSummaryError", rootCause(throwable));
            }
        } finally {
            if (pathConditionPaused && hasEnclosingRegion) {
                try {
                    api.resumePathCondition();
                    pathConditionPaused = false;
                } catch (Throwable ignored) {
                    // A failed native close below is still popped explicitly.
                }
            }
            if (!engineFinished) {
                // A failing native finish used to be able to throw after it
                // had already popped this region.  Never let recovery pop an
                // enclosing activation: cleanup belongs only to the exact VM
                // occurrence Java is closing.
                try {
                    if (api.currentRegionEnterEventId()
                            == active.vmRegionEnterEventId) {
                        api.cleanupAfterFailure();
                    }
                } catch (Throwable ignored) {
                    // Without an exact owner identity, destructive recovery
                    // would be less safe than letting this run terminate.
                }
            }
            ACTIVE.remove(active.token, active);
            popActiveRegion(active);
            if (!active.abandoned) endLiveSelectedRegion();
        }
        if (result == null) {
            configuration().releaseCandidate(active.activation);
            if (active.terminalGap && !active.activation.loopBodyRoot) {
                active.activation.reserveCompletedEvidence(false);
                haltWhenCampaignSettled(active.activation.taskId, 2);
            }
            return false;
        }
        if (!result.has("event")) {
            addResultIdentity(result, active, active.exitKind,
                    active.exceptionType);
        }
        return submitCompletedResultPublication(active, result,
                rawEngineSummary, rawSharedState);
    }


    private static void symbolizeReceiverFields(ActiveRegion active,
                                               RuntimeTask task,
                                               ConcolicVmBroker api) {
        for (SymbolizeAction action : task.symbolize) {
            // Nested/shared heap fields are materialized on their real owner
            // at the field-access hook.
            if (!"RECEIVER_FIELD".equals(action.location)) {
                continue;
            }
            if (!action.fieldPath.isEmpty()) {
                symbolizeFieldPath(active, action, active.receiver,
                        action.fieldPath, api);
                continue;
            }
            DeclaredField declared = FieldPathSpec.declaredField(
                    firstNonBlank(action.accessFieldSignature, action.cell));
            if (declared == null) {
                active.unresolved.add(action.symbol
                        + ": exact receiver field is unavailable");
                continue;
            }
            symbolizeField(active, action, active.receiver,
                    declared.name(), Collections.singletonList(
                            declared.name()), api);
        }
    }

    private static void symbolizeField(ActiveRegion active,
                                       SymbolizeAction action,
                                       Object owner, String symbolicPath,
                                       List<String> exactFieldPath,
                                       ConcolicVmBroker api) {
        String symbol = action.symbol + "." + safe(symbolicPath);
        try {
            String leafFieldSignature = action.exactLeafFieldSignature(
                    exactFieldPath);
            Object value = readExactField(owner, leafFieldSignature);
            DeclaredField field = FieldPathSpec.declaredField(
                    leafFieldSignature);
            if (field == null) {
                active.unresolved.add(symbol
                        + ": exact field declaration is unavailable");
                return;
            }
            JsonElement carried = containerValue(value)
                    ? engineExpression(api.expression(value))
                    : engineExpression(api.fieldExpression(owner,
                    field.owner(), field.name(),
                    javaTypeDescriptor(field.type()), value));
            if (retainPropagatedInput(active, action, value, carried, symbol,
                    exactFieldPath, leafFieldSignature)) {
                return;
            }
            JsonElement expression;
            if (value != null && value != MissingValue.INSTANCE
                    && containerValue(value)) {
                if (!trackContainerOrObserveConcrete(active, api, value,
                        action)) {
                    return;
                }
                ensurePathRecordingStarted(active);
                active.recordSymbolizedInputPort(action.symbol, value);
                expression = engineExpression(api.expression(value));
            } else {
                api.symbolizeExactField(owner, leafFieldSignature,
                        manualMintLabel(symbol, active.activation.occurrenceId,
                                primitiveDescriptor(field.type())));
                ensurePathRecordingStarted(active);
                expression = engineExpression(api.fieldExpression(owner,
                        field.owner(), field.name(),
                        javaTypeDescriptor(field.type()), value));
            }
            active.recordManualSymbolization(action, symbol, exactFieldPath,
                    leafFieldSignature, expression, true, false);
        } catch (Throwable throwable) {
            active.unresolved.add(symbol + ": shallow field symbolize failed: "
                    + rootCause(throwable));
        }
    }

    private static void symbolizeFieldPath(ActiveRegion active,
                                           SymbolizeAction action,
                                           Object root,
                                           List<String> path,
                                           ConcolicVmBroker api) {
        String label = FieldPathSpec.join(path);
        if (path == null || path.isEmpty() || label.isEmpty()) {
            active.unresolved.add(action.symbol
                    + ": selective argument contains an empty field path");
            return;
        }
        Object leafOwner = resolveFieldPathLeafOwner(root, path);
        if (leafOwner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + label
                    + ": projected field owner is missing");
            return;
        }
        if (leafOwner == null) {
            active.unresolved.add(action.symbol + "." + label
                    + ": projected field owner is null");
            return;
        }
        symbolizeField(active, action, leafOwner, label, path, api);
    }

    private static void applyFieldPathModel(ActiveRegion active,
                                            SymbolizeAction action,
                                            Object root,
                                            List<String> path) {
        if (path == null || path.isEmpty()
                || active.assignment(action, path) == null) {
            return;
        }
        Object owner = resolveFieldPathLeafOwner(root, path);
        if (owner == null || owner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + FieldPathSpec.join(path)
                    + ": solver-model field owner is unavailable");
            return;
        }
        applyFieldModel(active, action, owner, path);
    }

    private static void applyFieldModel(ActiveRegion active,
                                        SymbolizeAction action,
                                        Object owner, List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null) return;
        if (!writeModeledField(owner, action.exactLeafFieldSignature(path),
                assignment)) {
            active.unresolved.add(action.symbol + "." + FieldPathSpec.join(path)
                    + ": solver model could not be written to real field");
            return;
        }
        active.recordModelAssignment(assignment);
    }

    /**
     * Applies the solve's reference model for one action.  Returns the
     * replacement (possibly null), {@code MissingValue} when the solve named
     * no assignment, or {@code UnsupportedReplayValue} when it cannot be
     * replayed as a reference - which is also filed as unresolved.
     */
    private static Object modeledReference(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            String label) {
        ModelAssignment assignment = active.assignment(action, null);
        if (assignment == null) return MissingValue.INSTANCE;
        Object modeled = assignment.referenceValue(concrete);
        if (modeled == UnsupportedReplayValue.INSTANCE) {
            active.unresolved.add(action.symbol + ": unsupported " + label
                    + " model " + assignment.valueType + "="
                    + assignment.value);
            return UnsupportedReplayValue.INSTANCE;
        }
        active.recordModelAssignment(assignment);
        return modeled;
    }

    /** True for both {@link #modeledReference} outcomes that model nothing. */
    private static boolean unmodeled(Object modeled) {
        return modeled == MissingValue.INSTANCE
                || modeled == UnsupportedReplayValue.INSTANCE;
    }

    /** Symbolizes a materialized container the first time an action claims it. */
    private static void trackMaterializedContainer(
            ActiveRegion active, SymbolizeAction action, Object value) {
        if (containerValue(value) && active.materialized.add(action.symbol)) {
            symbolize(active, action, value, engine());
        }
    }

    /**
     * The literal one declared root must return on this replay.
     *
     * <p>For every root but a clock this is the solver's value verbatim: an
     * identity, a key id or a length has no run-relative reading, and the
     * model means exactly the number it states.</p>
     *
     * <p>A wall clock is the exception, and it is why a clock-only
     * experiment could not be won.  The model for a clock is an absolute
     * millisecond stamp the solver derived from the constants the
     * <em>seed</em> recording carried -- an expiry, a deadline, a lease.  A
     * flip replay is a fresh JVM: it mints its own copies of those constants
     * minutes later, so replaying the stamp literally puts the clock behind
     * its own run, the flipped comparison keeps its recorded outcome, and
     * the replay is refused with {@code REPLAY_PREFIX_UNMATCHED} -- "still
     * waiting for the flipped source decision".  No flipped case is ever
     * recorded, so the composer's exactly-one partition over observed cases
     * keeps asserting the recorded polarity of that branch and no window,
     * however wide, can admit the other one.</p>
     *
     * <p>What the solver actually chose is the <em>offset</em> from the
     * value this read returned, which is what {@link ClockRootPhysics}
     * bounds with a window and orders with monotonicity, and what a
     * cross-node skew mechanism means in the first place.  Carrying that
     * offset onto this run's own read reproduces the decision the model
     * asked for against this run's own constants and keeps the replayed
     * clock monotone with the rest of the JVM.  When the live read equals
     * the recorded one the two readings coincide, so nothing changes for a
     * replay that reproduces its recording.</p>
     *
     * <p>Soundness is unaffected: no injected value is ever asserted.  The
     * replay records a new real case with its own recorded constants and its
     * own path conditions, which the composer lowers as it lowers any other
     * observed case.  Injection only steers the search, exactly as a fault
     * marker's model does.</p>
     */
    static String replayModelLiteral(SymbolizeAction action,
                                     ModelAssignment assignment,
                                     Object concrete) {
        String modeled = assignment == null ? "" : safe(assignment.value).trim();
        if (action == null || modeled.isEmpty()
                || !action.declaresWallClockRead()) {
            return modeled;
        }
        return clockSkewLiteral(action.recordedPrimitiveValue, modeled,
                concrete);
    }

    /**
     * This run's clock, moved by the offset the model asked of the recorded
     * one.  Anything that is not an exact integral triple replays the model
     * value unchanged.
     */
    static String clockSkewLiteral(String recordedValue, String modelValue,
                                   Object liveValue) {
        String modeled = safe(modelValue).trim();
        Long recorded = integralLiteral(safe(recordedValue).trim());
        Long model = integralLiteral(modeled);
        Long live = integralValue(liveValue);
        if (recorded == null || model == null || live == null) {
            return modeled;
        }
        try {
            return Long.toString(Math.addExact(live,
                    Math.subtractExact(model, recorded)));
        } catch (ArithmeticException outsideTheDomain) {
            // A skew a long cannot hold is not a clock any run could read.
            return modeled;
        }
    }

    private static Long integralLiteral(String value) {
        if (value == null || value.isEmpty()) return null;
        try {
            return Long.valueOf(value);
        } catch (NumberFormatException notIntegral) {
            return null;
        }
    }

    private static Long integralValue(Object value) {
        if (value instanceof Long || value instanceof Integer
                || value instanceof Short || value instanceof Byte) {
            return ((Number) value).longValue();
        }
        return null;
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            List<String> path) {
        ConcolicVmBroker api = engine();
        List<String> exactPath = path == null
                ? Collections.<String>emptyList() : path;
        String fieldSignature = path == null ? ""
                : action.exactLeafFieldSignature(path);
        JsonElement carried;
        try {
            carried = primitiveBoxExpression(api, concrete);
        } catch (PropagatedExpressionImportFailure unreadable) {
            // Keep the value the replay actually holds, flagged, rather than
            // replacing an unreadable propagated box with a free root.
            refuseImportedExpression(active, action.symbol, fieldSignature,
                    unreadable);
            return concrete;
        } catch (Throwable unsymbolized) {
            carried = null;
        }
        if (retainPropagatedInput(active, action, concrete, carried,
                action.symbol, exactPath, fieldSignature)) {
            return concrete;
        }
        ModelAssignment assignment = active.assignment(action, path);
        ModelAssignment applied = null;
        Object modeled = concrete;
        if (assignment != null) {
            String literal = replayModelLiteral(action, assignment, concrete);
            modeled = coerceModelValue(assignment.valueType, literal,
                    concrete == null ? null : concrete.getClass());
            if (modeled == UnsupportedReplayValue.INSTANCE) {
                active.unresolved.add(action.symbol
                        + ": unsupported primitive model "
                        + assignment.valueType + "=" + literal);
                modeled = concrete;
            } else {
                applied = assignment;
            }
        }
        Object fresh = freshPrimitiveBox(modeled);
        try {
            api.symbolizeField(fresh, "value", manualMintLabel(action.symbol,
                    active.activation.occurrenceId, true));
            ensurePathRecordingStarted(active);
            JsonElement expression = primitiveBoxExpression(api, fresh);
            active.recordManualSymbolization(action, action.symbol,
                    exactPath, fieldSignature, expression, true, false,
                    // Only an activation that read the value as the program
                    // left it observed a recorded value.
                    applied == null ? recordedScalar(concrete) : "");
            if (applied != null) {
                active.recordModelAssignment(applied);
            }
            return fresh;
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol
                    + ": primitive materialization failed: "
                    + rootCause(throwable));
            return concrete;
        }
    }

    /** Exact expression stored in a Java primitive wrapper's value field. */
    private static JsonElement primitiveBoxExpression(
            ConcolicVmBroker api, Object boxed) throws Exception {
        if (boxed == null) return null;
        String descriptor = JavaPrimitiveBoxing.primitiveDescriptor(
                boxed.getClass().getName());
        if (descriptor.isEmpty()) return null;
        return engineExpression(api.fieldExpression(boxed,
                boxed.getClass().getName(), "value", descriptor, boxed));
    }

    static boolean writeModeledField(
            Object owner, String fieldSignature,
            ModelAssignment assignment) {
        Field field = declaredInstanceField(owner, fieldSignature);
        if (field == null) return false;
        try {
            Object value = coerceModelValue(assignment.valueType,
                    assignment.value, field.getType());
            if (value == UnsupportedReplayValue.INSTANCE) return false;
            field.set(owner, value);
            return true;
        } catch (Throwable ignored) {
            return false;
        }
    }

    static boolean writeIndexedContainerElement(
            Object container, int index, String valueType, String value) {
        if (container == null || container == MissingValue.INSTANCE
                || index < 0) {
            return false;
        }
        try {
            if (container.getClass().isArray()) {
                if (index >= Array.getLength(container)) return false;
                Object modeled = coerceModelValue(valueType, value,
                        container.getClass().getComponentType());
                if (modeled == UnsupportedReplayValue.INSTANCE
                        || modeled == null
                        && container.getClass().getComponentType()
                        .isPrimitive()) {
                    return false;
                }
                Array.set(container, index, modeled);
                return true;
            }
            if (container instanceof List) {
                List<Object> values = (List<Object>) container;
                if (index >= values.size()) return false;
                Object current = values.get(index);
                Object modeled = modeledContainerValue(current, valueType,
                        value);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    return false;
                }
                values.set(index, modeled);
                return true;
            }
        } catch (Throwable ignored) {
            return false;
        }
        return false;
    }

    static boolean writeContainerTarget(
            Object container, ModelAssignment assignment) {
        if ("INDEXED".equals(assignment.containerShape)) {
            return writeIndexedContainerElement(container,
                    assignment.containerIndex,
                    assignment.valueType, assignment.value);
        }
        if (!"ASSOCIATIVE".equals(assignment.containerShape)) return false;
        if (assignment.iterationTarget()) {
            return writeOrderedIterationTarget(container, assignment);
        }
        if (assignment.dynamicAssociativeTarget()) return false;
        if (!(container instanceof Map<?, ?>)) return false;
        Object key = containerKey(assignment.containerKeyJavaType,
                assignment.containerKeyValue);
        if (key == UnsupportedReplayValue.INSTANCE) return false;
        return writeAssociativeContainerTarget(container, key, assignment);
    }

    @SuppressWarnings("unchecked")
    static boolean writeAssociativeContainerTarget(
            Object container, Object key, ModelAssignment assignment) {
        if (!(container instanceof Map<?, ?>)
                || !"ASSOCIATIVE".equals(assignment.containerShape)) {
            return false;
        }
        Map<Object, Object> map = (Map<Object, Object>) container;
        if ("UNCHANGED".equals(assignment.valueType)) {
            // A non-null reference model constrains only nullness. The live
            // object is already the only replayable identity.
            return map.containsKey(key) && map.get(key) != null;
        }
        if (!map.containsKey(key)) {
            // Map.get on an absent key already yields null.  Replaying that
            // observation must not turn it into a present-null entry.
            return "NULL".equals(assignment.valueType);
        }
        Object current = map.get(key);
        Object modeled = modeledContainerValue(current, assignment);
        if (modeled == UnsupportedReplayValue.INSTANCE) return false;
        map.put(key, modeled);
        return true;
    }

    @SuppressWarnings("unchecked")
    private static boolean writeOrderedIterationTarget(
            Object container, ModelAssignment assignment) {
        int index = assignment.containerIndex;
        if (index < 0) return false;
        try {
            if (container instanceof LinkedHashSet<?>
                    && "KEY".equals(assignment.containerProjection)) {
                List<Object> values = new ArrayList<>(
                        (Set<Object>) container);
                if (index >= values.size()) return false;
                Object current = values.get(index);
                Object modeled = modeledContainerValue(current, assignment);
                if (modeled == UnsupportedReplayValue.INSTANCE) return false;
                if (collidesWithLiveElement(current, modeled,
                        ((Set<?>) container).contains(modeled))) {
                    return false;
                }
                values.set(index, modeled);
                LinkedHashSet<Object> target =
                        (LinkedHashSet<Object>) container;
                target.clear();
                target.addAll(values);
                return target.size() == values.size();
            }
            if (container instanceof Map<?, ?>
                    && "VALUE".equals(assignment.containerProjection)) {
                Map<Object, Object> target = (Map<Object, Object>) container;
                List<Map.Entry<Object, Object>> entries = new ArrayList<>(
                        target.entrySet());
                if (index >= entries.size()) return false;
                Map.Entry<Object, Object> selected = entries.get(index);
                Object modeled = modeledContainerValue(
                        selected.getValue(), assignment);
                if (modeled == UnsupportedReplayValue.INSTANCE) return false;
                // Replacing the value of an existing entry is not a
                // structural modification and therefore preserves the live
                // map's current iteration frontier, including HashMap's.
                target.put(selected.getKey(), modeled);
                return true;
            }
            if (!(container instanceof LinkedHashMap<?, ?>)) return false;
            LinkedHashMap<Object, Object> target =
                    (LinkedHashMap<Object, Object>) container;
            List<Map.Entry<Object, Object>> entries = new ArrayList<>(
                    target.entrySet());
            if (index >= entries.size()) return false;
            Map.Entry<Object, Object> selected = entries.get(index);
            if (!"KEY".equals(assignment.containerProjection)) return false;
            Object current = selected.getKey();
            Object modeled = modeledContainerValue(current, assignment);
            if (modeled == UnsupportedReplayValue.INSTANCE) return false;
            if (collidesWithLiveElement(current, modeled,
                    target.containsKey(modeled))) {
                return false;
            }
            target.clear();
            for (int cursor = 0; cursor < entries.size(); cursor++) {
                Map.Entry<Object, Object> entry = entries.get(cursor);
                target.put(cursor == index ? modeled : entry.getKey(),
                        entry.getValue());
            }
            return target.size() == entries.size();
        } catch (Throwable ignored) {
            return false;
        }
    }

    private static Object modeledContainerValue(
            Object current, ModelAssignment assignment) {
        return modeledContainerValue(current, assignment.valueType,
                assignment.value);
    }

    /**
     * The replacement a model names for a live container element.  A model
     * may null an element out or re-coerce a present one; an absent element
     * has no Java type to coerce against.
     */
    private static Object modeledContainerValue(
            Object current, String valueType, String value) {
        if ("NULL".equals(valueType)) return null;
        return current == null ? UnsupportedReplayValue.INSTANCE
                : coerceModelValue(valueType, value, current.getClass());
    }

    /** True when this write would merge two distinct live entries into one. */
    private static boolean collidesWithLiveElement(
            Object current, Object modeled, boolean alreadyPresent) {
        return alreadyPresent && !(current == null ? modeled == null
                : current.equals(modeled));
    }

    private static Object containerKey(String javaType, String value) {
        String descriptor = javaTypeDescriptor(javaType);
        if ("Z".equals(descriptor)) {
            return coerceModelValue("BOOL", value, Boolean.class);
        }
        if (descriptor.length() == 1
                && "BCSIJ".contains(descriptor)) {
            Class<?> target = "B".equals(descriptor) ? Byte.class
                    : "C".equals(descriptor) ? Character.class
                    : "S".equals(descriptor) ? Short.class
                    : "J".equals(descriptor) ? Long.class : Integer.class;
            return coerceModelValue("INT", value, target);
        }
        if ("Ljava/lang/String;".equals(descriptor)) {
            return unquoteSmtString(value);
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    static Object coerceModelValue(String valueType, String value,
                                   Class<?> requestedType) {
        String type = safe(valueType).toUpperCase();
        String raw = safe(value).trim();
        try {
            // Reference null must be decided before type-specific String
            // decoding.
            if ((requestedType == null || !requestedType.isPrimitive())
                    && ("NULL".equals(type)
                    || "null".equalsIgnoreCase(raw))) {
                return null;
            }
            if (requestedType == boolean.class
                    || requestedType == Boolean.class
                    || "BOOL".equals(type)) {
                return "true".equalsIgnoreCase(raw) || "1".equals(raw);
            }
            if (requestedType == byte.class || requestedType == Byte.class) {
                return Byte.valueOf(raw);
            }
            if (requestedType == short.class || requestedType == Short.class) {
                return Short.valueOf(raw);
            }
            if (requestedType == char.class
                    || requestedType == Character.class) {
                return raw.length() == 1 ? raw.charAt(0)
                        : (char) Integer.parseInt(raw);
            }
            if (requestedType == int.class || requestedType == Integer.class) {
                return Integer.valueOf(raw);
            }
            if (requestedType == long.class || requestedType == Long.class
                    || "INT".equals(type) && requestedType == null) {
                return Long.valueOf(raw);
            }
            if (requestedType == float.class || requestedType == Float.class) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Float.valueOf(decimal);
            }
            if (requestedType == double.class || requestedType == Double.class
                    || "REAL".equals(type) && requestedType == null) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Double.valueOf(decimal);
            }
            if (requestedType == String.class || "STRING".equals(type)) {
                return SmtModelValueCodec.decodeString(raw);
            }
        } catch (RuntimeException ignored) {
            return UnsupportedReplayValue.INSTANCE;
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    private static String unquoteSmtString(String value) {
        return SmtModelValueCodec.decodeString(value);
    }

    private static boolean isPrimitiveBox(Object value) {
        return value instanceof Boolean || value instanceof Byte
                || value instanceof Short || value instanceof Character
                || value instanceof Integer || value instanceof Long
                || value instanceof Float || value instanceof Double;
    }

    static Object resolveFieldPathLeafOwner(Object root, List<String> path) {
        if (root == null || path == null || path.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Object current = root;
        for (int index = 0; index + 1 < path.size(); index++) {
            String field = safe(path.get(index)).trim();
            if (field.isEmpty()) {
                return MissingValue.INSTANCE;
            }
            current = readPathSegment(current, field);
            if (current == null || current == MissingValue.INSTANCE) {
                return current;
            }
        }
        String leaf = safe(path.get(path.size() - 1)).trim();
        return leaf.isEmpty() ? MissingValue.INSTANCE : current;
    }

    private static Object readPathSegment(Object receiver, String segment) {
        if (receiver == null || segment == null || segment.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Integer index = pathIndex(segment);
        if (index != null && receiver.getClass().isArray()) {
            return index >= 0 && index < Array.getLength(receiver)
                    ? Array.get(receiver, index) : MissingValue.INSTANCE;
        }
        if (index != null && receiver instanceof List) {
            List<?> values = (List<?>) receiver;
            return index >= 0 && index < values.size()
                    ? values.get(index) : MissingValue.INSTANCE;
        }
        return readField(receiver, segment);
    }

    private static Integer pathIndex(String segment) {
        String value = safe(segment).trim();
        if (value.startsWith("[") && value.endsWith("]")) {
            value = value.substring(1, value.length() - 1).trim();
        }
        if (!value.matches("[0-9]+")) return null;
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static void symbolize(ActiveRegion active, SymbolizeAction action,
                                  Object value, ConcolicVmBroker api) {
        try {
            boolean liveArray = value != null && value.getClass().isArray();
            boolean declaredArray = action.declaresArrayInput(
                    Collections.<String>emptyList());
            if (declaredArray && !liveArray) return;
            JsonElement carried = value == null ? null
                    : engineExpression(api.expression(value));
            if (retainPropagatedInput(active, action, value, carried,
                    action.symbol, Collections.<String>emptyList(), "")) {
                return;
            }
            if (containerValue(value)) {
                if (!trackContainerOrObserveConcrete(active, api, value,
                        action)) {
                    return;
                }
            } else {
                api.symbolize(value, manualMintLabel(action.symbol,
                        active.activation.occurrenceId,
                        isPrimitiveBox(value)));
            }
            ensurePathRecordingStarted(active);
            if (value != null && !liveArray) {
                active.recordSymbolizedInputPort(action.symbol, value);
            }
            JsonElement expression = value == null ? null
                    : engineExpression(api.expression(value));
            active.recordManualSymbolization(action, action.symbol,
                    Collections.<String>emptyList(), "", expression,
                    true, false);
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol + ": symbolize failed: "
                    + rootCause(throwable));
        }
    }

    /** Keeps a VM-propagated value as this consumer's input authority. */
    private static boolean retainPropagatedInput(
            ActiveRegion active, SymbolizeAction action, Object value,
            JsonElement expression, String requestedSymbol,
            List<String> fieldPath, String fieldSignature) {
        if (!carriesInputAuthority(action, expression)) {
            return observeWithoutMinting(active, action, value);
        }
        ensurePathRecordingStarted(active);
        if (value != null && !value.getClass().isArray()) {
            active.recordSymbolizedInputPort(action.symbol, value);
        }
        active.recordManualSymbolization(action, requestedSymbol, fieldPath,
                fieldSignature, expression, false, true);
        return true;
    }

    /**
     * The one thing a tracked carrier does when nothing propagated into it.
     *
     * <p>Every caller of {@link #retainPropagatedInput} treats {@code false}
     * as permission to mint.  Two kinds of action must not take it.</p>
     *
     * <p>The first is an action the plan tracked but did not make
     * mint-eligible: the experiment declared where the search starts, and
     * this read is not it.</p>
     *
     * <p>The second is a declared communication cut port, whatever the plan
     * says about mint eligibility -- including a plan with no selection file
     * at all, where every action is eligible by default.  The value at such
     * a port is produced on the other side of the wire, and the instrumented
     * frame installs the producer's expression with
     * {@link #attachCommunicationLeaf} <em>after</em> this hook runs: the
     * handoff pass and the materialization pass both insert after the cut
     * statement, so the later pass lands closer to it and nothing symbolic
     * has reached the local yet when the hook asks.  Minting there creates a
     * free variable the attach immediately overwrites -- the program uses
     * the producer's value while the formula keeps an existential root
     * nothing constrains, which is how HDFS-17899 bug3 acquired four of them
     * on {@code PBHelper.convert(BlockKeyProto)} and lost its reach
     * condition to {@code true}.  A flow whose value never arrives is
     * already named three times over, by {@link #attachCommunicationLeaf}'s
     * own handoff gap, by {@code SymbolicPropagationClosure
     * .RPC_ATTACH_SENDER_EXPRESSION_MISSING} and by {@code the composition
     * .WIRE_FLOW_VALUE_UNBOUND}; a mint hid all three behind a root that
     * answered to nothing.</p>
     *
     * <p>Either way: open path recording and publish the port at its
     * recorded value -- the same two steps a selected shared read already
     * takes -- so the VM still resolves the writer and creates the read
     * boundary, and return {@code true} to say the caller has nothing left
     * to do.</p>
     *
     * <p>A container is the exception and falls through: tracking one
     * publishes the versions of a shared state, which is what a carrier
     * exists to do, and mints no scalar the solver can move.</p>
     */
    private static boolean observeWithoutMinting(
            ActiveRegion active, SymbolizeAction action, Object value) {
        if (action == null || containerValue(value)) return false;
        boolean cutPort = declaredCommunicationCutPort(action);
        if (action.mintEligible && !cutPort) return false;
        if (cutPort) {
            diag(DECLARED_CUT_PORT_MINT_REFUSED, "port="
                    + safe(action.symbol) + " occurrence="
                    + (active == null ? ""
                    : safe(active.activation.occurrenceId)));
        }
        ensurePathRecordingStarted(active);
        if (value != null && value != MissingValue.INSTANCE
                && !value.getClass().isArray()) {
            active.recordSymbolizedInputPort(action.symbol, value);
        }
        return true;
    }

    /**
     * Whether a live value is a container whose whole state one carrier can
     * select, rather than a reference slot.
     *
     * <p>An array is excluded: its elements already have their own element
     * locations, and selecting the array whole would name the same storage
     * twice.  A set is excluded because no carrier this build declares
     * versions one whole.</p>
     */
    private static boolean wholeStateContainerValue(Object value) {
        return value != null && !value.getClass().isArray()
                && (value instanceof Map<?, ?>
                || value instanceof List<?>
                || value instanceof Deque<?>
                || value instanceof java.util.Queue<?>);
    }

    private static boolean containerValue(Object value) {
        return value != null && (value.getClass().isArray()
                || value instanceof Map<?, ?>
                || value instanceof Set<?>
                || value instanceof Collection<?>);
    }

    /**
     * Gives each manually minted primitive root the stable address of its
     * planned occurrence. A propagated expression never reaches a mint call,
     * and reference/container labels retain their existing wire identity.
     */
    static String manualMintLabel(String requestedSymbol,
                                  String plannedOccurrenceId,
                                  boolean primitiveRoot) {
        String requested = safe(requestedSymbol);
        if (!primitiveRoot) return requested;
        String occurrence = safe(plannedOccurrenceId);
        if (requested.isEmpty() || occurrence.isEmpty()) {
            throw new IllegalArgumentException(
                    "manual primitive mint requires symbol and occurrence");
        }
        return requested + ".occ."
                + CanonicalJson.sha256(occurrence);
    }

    /**
     * Whether the value that arrived is already this input's authority.
     *
     * <p>For an automatic input the answer is any propagated expression: a
     * consumer boundary around a constant still records which producer case
     * delivered it.  A <em>declared</em> primitive source is the one case
     * where that is the wrong answer.  The experiment named the field to say
     * "the search starts here"; by the time the read fires, a shared-state
     * carrier has wrapped it in a {@code ReadFrom} whose every candidate is a
     * constant, so the loose rule reports "already propagated" and no root is
     * ever minted -- the field is declared symbolic and stays concrete.  Ask
     * the strict question there instead: is anything symbolic actually inside?
     * Non-primitives keep the loose rule, because a container or reference
     * has no root to mint in the first place.</p>
     */
    /** Package-visible for the declared-mint contract test. */
    static boolean carriesInputAuthority(
            SymbolizeAction action, JsonElement expression) {
        return action != null && action.declaredSymbolicRoot
                && primitiveDescriptor(action.javaType)
                ? VmExpressionIr.carriesSymbolicValue(expression)
                : VmExpressionIr.carriesPropagatedValue(expression);
    }

    /**
     * The same question for the {@code CausynthSymbolicSource} hook path.
     *
     * <p>{@link #symbolizeConfiguredSourceField} accepts only a declared
     * primitive field, so it is exactly the case
     * {@link #carriesInputAuthority} narrows: the strict rule, with no
     * action row to consult.  Keeping it a named seam is what the
     * declared-mint contract test asserts against, because the hook itself
     * cannot run without a live VM and an active region.</p>
     */
    /** Package-visible for the declared-mint contract test. */
    static boolean configuredSourceCarriesAuthority(JsonElement carried) {
        return VmExpressionIr.carriesSymbolicValue(carried);
    }

    /**
     * Whether this action names a port {@code communication-mappings.jsonl}
     * declared, on either side of the wire.
     *
     * <p>The finalizer stamps the classification on {@code sourceKind} when
     * it mints the port, and that is what both stages read:
     * {@code ConcolicScheduler.SymbolicInputSelection.declaredCutPort} asks
     * the same question of the same field at plan time.</p>
     */
    static boolean declaredCommunicationCutPort(SymbolizeAction action) {
        return action != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(action.sourceKind);
    }

    /** Diagnostic name of one refused mint at a declared cut port. */
    static final String DECLARED_CUT_PORT_MINT_REFUSED =
            "DECLARED_CUT_PORT_MINT_REFUSED";

    private static boolean primitiveDescriptor(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        return descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor);
    }

    private static void requireTrackedContainer(
            ConcolicVmBroker api, Object value, String symbol) throws Exception {
        if (!api.trackContainer(value, symbol)) {
            throw new UnsupportedOperationException(
                    "custom VM has no symbolic model for container "
                            + value.getClass().getName());
        }
    }

    /**
     * A bounded container port describes the concrete receiver/cardinality
     * that scopes separately symbolized leaves.
     */
    private static boolean trackContainerOrObserveConcrete(
            ActiveRegion active, ConcolicVmBroker api, Object value,
            SymbolizeAction action) throws Exception {
        if (api.trackContainer(value, action.symbol)) return true;
        if (!"BOUNDED_CONTAINER_STATE".equals(action.symbolicDemand)) {
            requireTrackedContainer(api, value, action.symbol);
        }
        active.recordSymbolizedInputPort(action.symbol, value);
        return false;
    }

    private static Object readField(Object receiver, String name) {
        if (receiver == null || name == null || name.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Class<?> type = receiver.getClass();
        while (type != null) {
            try {
                Field field = type.getDeclaredField(name);
                if (Modifier.isStatic(field.getModifiers())) {
                    return MissingValue.INSTANCE;
                }
                if (!field.isAccessible()) {
                    field.setAccessible(true);
                }
                return field.get(receiver);
            } catch (NoSuchFieldException ignored) {
                type = type.getSuperclass();
            } catch (Throwable throwable) {
                return MissingValue.INSTANCE;
            }
        }
        return MissingValue.INSTANCE;
    }

    static Object readExactField(
            Object receiver, String fieldSignature) {
        Field field = declaredInstanceField(receiver, fieldSignature);
        if (field == null) return MissingValue.INSTANCE;
        try {
            return field.get(receiver);
        } catch (Throwable ignored) {
            return MissingValue.INSTANCE;
        }
    }

    private static Field declaredInstanceField(
            Object owner, String fieldSignature) {
        DeclaredField declared = FieldPathSpec.declaredField(fieldSignature);
        return declared == null ? null
                : declaredInstanceField(owner, declared.owner(),
                declared.name(), javaTypeDescriptor(declared.type()), true);
    }

    /** Exact live field named by a VM handoff export. */
    private static Field declaredInstanceField(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        return declaredInstanceField(owner, declaringClass, fieldName,
                descriptor, false);
    }

    /**
     * The one non-static {@code declaringClass#fieldName} of {@code owner}
     * whose type descriptor matches, made accessible.  {@code inherited} also
     * accepts a field the declaring class inherits - which the field-signature
     * form resolves and an exact VM export must not.
     */
    private static Field declaredInstanceField(
            Object owner, String declaringClass, String fieldName,
            String descriptor, boolean inherited) {
        if (owner == null || safe(declaringClass).isEmpty()
                || safe(fieldName).isEmpty() || safe(descriptor).isEmpty()) {
            return null;
        }
        Class<?> type = owner.getClass();
        while (type != null && !declaringClass.equals(type.getName())) {
            type = type.getSuperclass();
        }
        while (type != null) {
            try {
                Field field = type.getDeclaredField(fieldName);
                if (Modifier.isStatic(field.getModifiers())
                        || !descriptor.equals(javaTypeDescriptor(
                        field.getType().getTypeName()))) {
                    return null;
                }
                if (!field.isAccessible()) field.setAccessible(true);
                return field;
            } catch (NoSuchFieldException absent) {
                if (!inherited) return null;
                type = type.getSuperclass();
            } catch (Throwable inaccessible) {
                return null;
            }
        }
        return null;
    }

    private static String exactFieldSignature(Field field) {
        return "<" + field.getDeclaringClass().getName() + ": "
                + field.getType().getTypeName() + " " + field.getName()
                + ">";
    }

    static ActiveRegion activeRegion() {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long token = tokens.peek();
        return token == null ? null : ownerRegion(token);
    }

    private static void pushActiveRegion(ActiveRegion active) {
        CURRENT_TOKENS.get().push(active.token);
    }

    /** The stack, having proved {@code active} is its innermost entry. */
    private static Deque<Long> innermostActiveRegionStack(
            ActiveRegion active, String violation) {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long current = tokens.peek();
        if (current == null || current.longValue() != active.token) {
            throw new IllegalStateException(violation);
        }
        return tokens;
    }

    /** True only when {@code active} is the innermost region with a caller. */
    private static boolean hasEnclosingActiveRegion(ActiveRegion active) {
        return innermostActiveRegionStack(active,
                "selected regions must close in strict LIFO order").size() > 1;
    }

    /** The exact selected caller of the current innermost activation. */
    private static ActiveRegion enclosingActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = innermostActiveRegionStack(active,
                "selected regions must inspect callers in strict LIFO order");
        java.util.Iterator<Long> iterator = tokens.iterator();
        iterator.next();
        Long enclosingToken = iterator.hasNext() ? iterator.next() : null;
        return enclosingToken == null ? null : ownerRegion(enclosingToken);
    }

    /** Pops the exact innermost activation; an ownership mismatch is fatal. */
    private static void popActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = innermostActiveRegionStack(active,
                "selected region stack does not own token " + active.token);
        tokens.pop();
        if (tokens.isEmpty()) CURRENT_TOKENS.remove();
    }

    /** Returns null only when no lightweight accessor scope is active. */
    private static Boolean lightweightAccessorContextMatches(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object fieldOwner) {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (context == null) return null;
        ActiveRegion active = activeRegion();
        if (active == null || context.regionToken != active.token
                || context.thread != Thread.currentThread()) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
            return Boolean.FALSE;
        }
        return context.matches(callerMethod, callUnitIndex, callSiteId,
                declaredCallee, fieldOwner);
    }

    private static int lightweightAccessorContextOccurrence() {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        ActiveRegion active = activeRegion();
        if (context == null || active == null
                || context.regionToken != active.token
                || context.thread != Thread.currentThread()) {
            return -1;
        }
        return context.occurrence;
    }

    private static ActiveRegion ownerRegion(long token) {
        ActiveRegion active = ACTIVE.get(token);
        return active != null && active.thread == Thread.currentThread()
                ? active : null;
    }

    @SuppressWarnings("deprecation")
    private static Object freshPrimitiveBox(Object value) {
        if (value instanceof Integer) {
            return new Integer(((Integer) value).intValue());
        }
        if (value instanceof Boolean) {
            return new Boolean(((Boolean) value).booleanValue());
        }
        if (value instanceof Long) {
            return new Long(((Long) value).longValue());
        }
        if (value instanceof Byte) {
            return new Byte(((Byte) value).byteValue());
        }
        if (value instanceof Short) {
            return new Short(((Short) value).shortValue());
        }
        if (value instanceof Character) {
            return new Character(((Character) value).charValue());
        }
        if (value instanceof Float) {
            return new Float(((Float) value).floatValue());
        }
        if (value instanceof Double) {
            return new Double(((Double) value).doubleValue());
        }
        if (value instanceof String) {
            return new String((String) value);
        }
        return value;
    }

    private static boolean instanceOfName(Class<?> type, String expected) {
        if (type == null || expected == null || expected.isEmpty()) {
            return expected == null || expected.isEmpty();
        }
        if (expected.equals(type.getName())) {
            return true;
        }
        for (Class<?> iface : type.getInterfaces()) {
            if (instanceOfName(iface, expected)) {
                return true;
            }
        }
        return instanceOfName(type.getSuperclass(), expected);
    }

    static boolean branchConditionMatches(String expression, boolean outcome,
                                          JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return false;
        }
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))) {
            Boolean requiredValue = booleanValueRequiredByZeroBranch(
                    expression, outcome);
            Boolean representedValue = representedBooleanValue(object);
            return requiredValue != null && representedValue != null
                    && requiredValue.equals(representedValue);
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return false;
        }
        String declared = matcher.group(1);
        String expected = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        String observed = optionalString(object, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))) {
            return false;
        }
        if (safe(expression).matches(".*\\bnull\\b.*")) {
            return symbolicNull(object.get("_left"))
                    || symbolicNull(object.get("_right"));
        }
        return true;
    }

    /** Resolves the Java boolean value selected by a Jimple zero test. */
    private static Boolean booleanValueRequiredByZeroBranch(
            String expression, boolean outcome) {
        String rendered = safe(expression).trim();
        Matcher matcher = BRANCH_OPERATOR.matcher(rendered);
        if (!matcher.find()) return null;
        String declared = matcher.group(1);
        if (!("==".equals(declared) || "!=".equals(declared))) {
            return null;
        }
        String left = rendered.substring(0, matcher.start()).trim();
        String right = rendered.substring(matcher.end()).trim();
        boolean leftZero = "0".equals(left);
        boolean rightZero = "0".equals(right);
        if (leftZero == rightZero) return null;
        String effective = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        return "!=".equals(effective);
    }

    /**
     * Returns the underlying Java boolean represented by an asserted engine
     * condition, or {@code null} when the IR node is value-producing or its
     * semantics are not part of the exact codec.
     */
    private static Boolean representedBooleanValue(JsonObject condition) {
        if (!"OpStrExpression".equals(optionalString(condition, "_type"))) {
            return null;
        }
        String operation = optionalString(condition, "_name");
        int expectedArity;
        if ("isEmpty".equals(operation)) {
            expectedArity = 1;
        } else if ("contains".equals(operation)
                || "equals".equals(operation)
                || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            expectedArity = 2;
        } else {
            return null;
        }
        if (array(condition, "_param_list").size() != expectedArity) {
            return null;
        }
        return !optionalBool(condition, "_is_not", false);
    }

    /**
     * Soot may describe one selected Jimple edge as {@code >=}/{@code <=}
     * while the asserted VM relation for that concrete edge is the stronger
     * {@code >}, {@code <}, or {@code ==}.  Admit only that forward
     * implication, then canonicalize the retained condition to the actual
     * Jimple predicate below.  Numeric {@code *cmp*} bytecodes now propagate
     * their symbolic trichotomy result to the consuming branch; this is not a
     * fallback to the removed concrete compare-witness mechanism.
     */
    private static boolean observedOperatorImpliesBranch(
            String expected, String observed, boolean nullComparison) {
        if (expected.equals(observed)) {
            return true;
        }
        if (nullComparison) {
            return false;
        }
        return ">=".equals(expected)
                && (">".equals(observed) || "==".equals(observed))
                || "<=".equals(expected)
                && ("<".equals(observed) || "==".equals(observed));
    }

    /** Returns the branch-level predicate while retaining the VM operands. */
    private static JsonElement semanticBranchCondition(
            String expression, boolean outcome, JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return condition;
        }
        JsonObject original = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(original, "_type"))) {
            return condition;
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return condition;
        }
        String expected = outcome ? matcher.group(1)
                : BranchPredicateAlgebra.complementOperator(
                matcher.group(1));
        String observed = optionalString(original, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))
                || expected.equals(observed)) {
            return condition;
        }
        JsonObject normalized = shallowCopy(original);
        normalized.addProperty("_op", expected);
        return normalized;
    }

    private static String binaryOperator(JsonElement condition) {
        return condition != null && condition.isJsonObject()
                ? optionalString(condition.getAsJsonObject(), "_op") : "";
    }

    private static boolean symbolicNull(JsonElement element) {
        if (element == null || !element.isJsonObject()) {
            return false;
        }
        JsonObject object = element.getAsJsonObject();
        return "SymbolExpression".equals(optionalString(object, "_type"))
                && VmExpressionIr.SYMBOLIC_NULL.equals(
                optionalString(object, "_exp"));
    }

    private static void resumePathCondition(ActiveRegion active,
                                            ConcolicVmBroker api) {
        try {
            api.resumePathCondition();
        } catch (Throwable throwable) {
            active.unresolved.add("path-condition recording resume failed: "
                    + rootCause(throwable));
        }
    }

    /**
     * Opens the Java-side branch-observation gate when the first selected
     * input becomes symbolic.
     */
    private static void ensurePathRecordingStarted(ActiveRegion active) {
        if (active.pathRecordingStarted) return;
        active.pathRecordingStarted = true;
    }


    private static boolean diagnosticsEnabled() {
        Boolean cached = diagnostics;
        if (cached != null) return cached;
        boolean enabled;
        try {
            enabled = Boolean.parseBoolean(
                    safe(System.getProperty(DIAGNOSTICS_PROPERTY)));
        } catch (Throwable ignored) {
            enabled = false;
        }
        diagnostics = enabled;
        return enabled;
    }

    /**
     * Writes one diagnostic line with path-condition recording paused, so the
     * trace can never manufacture a condition of the program under test.
     */
    static void diag(String event, String detail) {
        if (!diagnosticsEnabled()) return;
        ConcolicVmBroker api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
        } catch (Throwable ignored) {
            // A missing engine still leaves the line worth printing.
        }
        try {
            diagLine(event, detail);
        } finally {
            if (paused) {
                try {
                    api.resumePathCondition();
                } catch (Throwable ignored) {
                    // Resume failure is already reported by the real hooks.
                }
            }
        }
    }

    /** Diagnostic for daemon publication, where no VM context may be called. */
    static void diagAfterVmClose(String event, String detail) {
        if (diagnosticsEnabled()) diagLine(event, detail);
    }

    /** The line itself, which never fails the replay or the publication. */
    private static void diagLine(String event, String detail) {
        try {
            System.err.println("CAUSYNTH-DIAG|"
                    + System.currentTimeMillis() + "|t"
                    + Thread.currentThread().getId() + "|heapMB"
                    + (Runtime.getRuntime().totalMemory()
                    - Runtime.getRuntime().freeMemory()) / 1048576L + "|"
                    + safe(event) + "|" + safe(detail));
        } catch (Throwable ignored) {
        }
    }


    static JsonElement parseJson(String value) {
        if (value == null || value.trim().isEmpty()) {
            return new JsonObject();
        }
        try {
            return new JsonParser().parse(value);
        } catch (RuntimeException ignored) {
            return GSON.toJsonTree(value);
        }
    }

    static String rootCause(Throwable throwable) {
        Throwable current = throwable;
        while (current instanceof InvocationTargetException
                && ((InvocationTargetException) current).getTargetException() != null) {
            current = ((InvocationTargetException) current).getTargetException();
        }
        return current == null ? "unknown" : current.toString();
    }



    /**
     * How a configured source's recorded value is spelled in the ledger.
     *
     * <p>The same spelling the recorded-root ledger already uses for a
     * manual root's {@code primitiveValue}, so one reader can compare a
     * witness against either: {@code "true"}/{@code "false"} for a Boolean,
     * the decimal digits for an integral, the literal text for a String. A
     * reference the runtime cannot spell as a scalar states nothing rather
     * than a {@code toString()} nobody can compare against.</p>
     */
    static String recordedScalar(Object value) {
        if (value instanceof Boolean || value instanceof Character
                || value instanceof Byte || value instanceof Short
                || value instanceof Integer || value instanceof Long
                || value instanceof Float || value instanceof Double
                || value instanceof String) {
            return String.valueOf(value);
        }
        return "";
    }

    enum MissingValue { INSTANCE }

    private enum UnsupportedReplayValue { INSTANCE }

    static final class AccessorCallContext {
        private final long contextToken;
        final long regionToken;
        final Thread thread;
        private final String callerMethod;
        private final int callUnitIndex;
        final String callSiteId;
        private final String declaredCallee;
        final Object receiver;
        final int occurrence;
        private final AccessorCallContext previous;

        private AccessorCallContext(
                long contextToken, long regionToken, Thread thread,
                String callerMethod, int callUnitIndex, String callSiteId,
                String declaredCallee, Object receiver,
                int occurrence,
                AccessorCallContext previous) {
            this.contextToken = contextToken;
            this.regionToken = regionToken;
            this.thread = thread;
            this.callerMethod = callerMethod;
            this.callUnitIndex = callUnitIndex;
            this.callSiteId = callSiteId;
            this.declaredCallee = declaredCallee;
            this.receiver = receiver;
            this.occurrence = occurrence;
            this.previous = previous;
        }

        private boolean matches(
                String actualCallerMethod, int actualCallUnitIndex,
                String actualCallSiteId, String actualDeclaredCallee,
                Object actualFieldOwner) {
            return callerMethod.equals(safe(actualCallerMethod))
                    && callUnitIndex == actualCallUnitIndex
                    && callSiteId.equals(safe(actualCallSiteId))
                    && declaredCallee.equals(safe(actualDeclaredCallee))
                    && receiver == actualFieldOwner;
        }
    }

    private static final class SwitchExpectation {
        private final String branchKind;
        private final List<Integer> caseKeys;
        private final int observedSuccessorIndex;

        private SwitchExpectation(String branchKind, List<Integer> caseKeys,
                                  int observedSuccessorIndex) {
            this.branchKind = branchKind;
            this.caseKeys = Collections.unmodifiableList(
                    new ArrayList<>(caseKeys));
            this.observedSuccessorIndex = observedSuccessorIndex;
        }

        private static SwitchExpectation parse(
                String branchKind, String encodedCaseKeys,
                int observedSuccessorIndex) {
            String kind = safe(branchKind);
            if (!("TABLE_SWITCH".equals(kind)
                    || "LOOKUP_SWITCH".equals(kind))) {
                throw new IllegalArgumentException(
                        "unsupported branch kind " + kind);
            }
            List<Integer> keys = new ArrayList<>();
            String encoded = safe(encodedCaseKeys);
            if (!encoded.isEmpty()) {
                for (String token : encoded.split(",", -1)) {
                    if (!token.matches("-?(?:0|[1-9][0-9]*)")) {
                        throw new IllegalArgumentException(
                                "malformed switch key " + token);
                    }
                    try {
                        keys.add(Integer.parseInt(token));
                    } catch (NumberFormatException malformed) {
                        throw new IllegalArgumentException(
                                "switch key outside int domain " + token,
                                malformed);
                    }
                }
            }
            if (keys.isEmpty() || observedSuccessorIndex < 0
                    || observedSuccessorIndex > keys.size()) {
                throw new IllegalArgumentException(
                        "successor " + observedSuccessorIndex
                                + " outside switch domain [0,"
                                + keys.size() + "]");
            }
            if ("TABLE_SWITCH".equals(kind)) {
                for (int index = 1; index < keys.size(); index++) {
                    if ((long) keys.get(index - 1) + 1L
                            != (long) keys.get(index)) {
                        throw new IllegalArgumentException(
                                "tableswitch keys are not dense/ordered");
                    }
                }
            } else {
                Set<Integer> distinct = new LinkedHashSet<>(keys);
                if (distinct.size() != keys.size()) {
                    throw new IllegalArgumentException(
                            "lookupswitch keys are not unique");
                }
            }
            return new SwitchExpectation(kind, keys,
                    observedSuccessorIndex);
        }

        private boolean caseArm() {
            return observedSuccessorIndex < caseKeys.size();
        }
    }

    /**
     * One decision an instrumented site made: the outcome a binary branch
     * took, or the successor a multiway switch selected out of its static
     * case-key domain.
     *
     * <p>The stages of one observation -- record the decision behind a closed
     * symbolic gate, record it at a replay-invocation boundary, capture it
     * against the open VM path-condition window, observe it against the
     * recorded replay prefix, and address the target reach it may complete --
     * ask the same questions of both kinds, and are written once against
     * this.  A switch carries its {@link SwitchExpectation}; a binary branch
     * carries none, exactly as {@link ExactConcreteBranchObservation}
     * distinguishes the two observations it publishes.</p>
     */
    private static final class BranchDecision {
        private final boolean outcome;
        private final SwitchExpectation expected;

        private BranchDecision(boolean outcome, SwitchExpectation expected) {
            this.outcome = outcome;
            this.expected = expected;
        }

        static BranchDecision binary(boolean outcome) {
            return new BranchDecision(outcome, null);
        }

        static BranchDecision multiway(SwitchExpectation expected) {
            return new BranchDecision(expected.caseArm(), expected);
        }

        /** The source-level outcome this decision took. */
        boolean outcome() { return outcome; }

        /** This decision's exact observation at one occurrence of a site. */
        ExactConcreteBranchObservation observationAt(
                String siteId, String method, int unitIndex, int occurrence) {
            return expected == null
                    ? ExactConcreteBranchObservation.attested(siteId, method,
                    unitIndex, occurrence, outcome)
                    : ExactConcreteBranchObservation.attestedSwitch(siteId,
                    method, unitIndex, occurrence, expected.branchKind,
                    expected.caseKeys, expected.observedSuccessorIndex);
        }

        /**
         * Tells the replay ledger this decision ran, and whether it is the
         * decision the recorded prefix was waiting for.  A successor is the
         * replay authority itself, so there is no second, symbolic reading of
         * a switch for the prefix to disagree with.
         */
        boolean observeReplayProgress(
                BranchReplayContract.ReplayProgress progress, String siteId,
                int occurrence, String symbolicSupportDigest) {
            if (expected == null) {
                return progress.observeBinary(siteId, occurrence, outcome,
                        symbolicSupportDigest);
            }
            progress.observeSwitch(siteId, occurrence, expected.branchKind,
                    expected.caseKeys, expected.observedSuccessorIndex);
            return true;
        }

        /** How {@code REPLAY_OBSERVE} names the decision it just observed. */
        String replayTrace(boolean matched) {
            return expected == null
                    ? " outcome=" + outcome + " matched=" + matched
                    : " successor=" + expected.observedSuccessorIndex;
        }

        /** This decision's exact capture while the VM window is open. */
        RecordedBranch recordPaused(
                ActiveRegion active, ConcolicVmBroker api, String method,
                int unitIndex, String expression, int occurrence,
                long vmEventId) throws Exception {
            return expected == null
                    ? recordBranchPaused(active, api, method, unitIndex,
                    expression, occurrence, outcome, vmEventId)
                    : new RecordedBranch(recordSwitchBranchPaused(active, api,
                    method, unitIndex, expression, occurrence, expected,
                    vmEventId), "");
        }

        /** What an absent replay-boundary handle is refused as. */
        String boundaryNoun() {
            return expected == null ? "replay loop boundary"
                    : "replay loop switch boundary";
        }

        /** What an absent prepared event is refused as. */
        String preparedNoun() {
            return expected == null ? "prepared branch" : "prepared switch";
        }

        /** What a failed exact-event observation is reported as. */
        String observationNoun() {
            return expected == null ? "branch/PC" : "switch/PC";
        }

        /**
         * Whether a bounded-loop permutation may address the planned target
         * occurrence from a different one.  A binary branch is the decision
         * the solver flips, so it may; a multiway successor is retained as a
         * path assumption, so it addresses only the planned occurrence.
         */
        boolean addressesPermutedTargetOccurrence() {
            return expected == null;
        }

    }

    private static final class VmBranchEventAttestation {
        private final List<Integer> conditionIndices;
        private final boolean valid;
        private final String error;

        private VmBranchEventAttestation(List<Integer> conditionIndices,
                                         boolean valid,
                                         String error) {
            this.conditionIndices = Collections.unmodifiableList(
                    new ArrayList<>(conditionIndices));
            this.valid = valid;
            this.error = safe(error);
        }

        private static VmBranchEventAttestation valid(
                List<Integer> conditionIndices) {
            return new VmBranchEventAttestation(conditionIndices, true, "");
        }

        private static VmBranchEventAttestation invalid(String error) {
            return new VmBranchEventAttestation(
                    Collections.<Integer>emptyList(), false, error);
        }
    }

    private static final class PreparedBranch {
        private final long handle;
        private final String method;
        private final int unitIndex;
        private final String expression;
        private final int occurrence;

        private PreparedBranch(long handle, String method, int unitIndex,
                               String expression, int occurrence) {
            this.handle = handle;
            this.method = safe(method);
            this.unitIndex = unitIndex;
            this.expression = safe(expression);
            this.occurrence = occurrence;
        }

        private boolean matches(String actualMethod, int actualUnitIndex,
                                String actualExpression) {
            return method.equals(safe(actualMethod))
                    && unitIndex == actualUnitIndex
                    && expression.equals(safe(actualExpression));
        }
    }

    /**
     * Activation-local ordinals for repeated executions of one hook.  A new
     * region activation owns a new counter, so no runtime event id or
     * process-global invocation ordinal becomes replay identity.
     */
    static final class OccurrenceCounter {
        private final Map<String, Integer> occurrences =
                new LinkedHashMap<>();

        int local(String method, int unitIndex, String local) {
            return observe("LOCAL\u0000"
                    + SiteId.render(method, unitIndex)
                    + "::" + safe(local));
        }

        int methodArgument(String method, int argumentIndex) {
            return observe("ARGUMENT\u0000" + safe(method) + "#arg"
                    + argumentIndex);
        }

        int observedMethodArgument(String method, int argumentIndex) {
            return observed("ARGUMENT\u0000" + safe(method) + "#arg"
                    + argumentIndex);
        }

        /**
         * One read site's occurrences.
         *
         * <p>{@code SiteId.render} and not {@code SiteId.of}: the
         * instrumentation deliberately passes a {@code -1} unit index for an
         * accessor implementation that has no unit of its own, and a strict
         * parse of that sentinel throws inside the workload.</p>
         */
        int field(String method, int unitIndex) {
            return observe("FIELD\u0000"
                    + SiteId.render(method, unitIndex));
        }

        /**
         * A workload-declared fault marker counts per activation and per
         * declared symbol.  The recorder counts the same firings per
         * activation and per call site
         * ({@code RuntimeRefinedGraphBuilder.collectAccessorBindings}); one
         * marker literal names one call site, so the two ordinals agree and
         * {@code replayOccurrence} selects the exact recorded firing.
         */
        int explicitFault(String symbolicName) {
            return observe("EXPLICIT_FAULT\u0000" + safe(symbolicName));
        }


        private int observe(String key) {
            int occurrence = observed(key) + 1;
            occurrences.put(key, occurrence);
            return occurrence;
        }

        private int observed(String key) {
            return occurrences.getOrDefault(key, 0);
        }
    }

    static final class ActiveRegion {
        /**
         * When this activation started, and how long it ran.
         *
         * <p>A campaign's only per-unit timings used to be the stage totals
         * and the final solver's own attempt rows, so a replay that took
         * three minutes and a replay that took three seconds were
         * indistinguishable after the fact.  These two are published on the
         * activation's result row; they are telemetry the importer does not
         * read, so no summary identity, local case id or replay match
         * depends on them.</p>
         */
        final long startedAtMillis = System.currentTimeMillis();
        /** The thread this activation ran on, as the recording names it. */
        final String threadName = Thread.currentThread().getName();
        /**
         * The request in force when this activation was entered, or "".
         *
         * <p>Never an admission condition -- an occurrence is (node, epoch,
         * region, k) and the request is a circumstance -- but the circumstance
         * has to be on the row: a task anchored to one request answered by an
         * activation that ran under none is a divergence IMPORT must name,
         * and nothing published it.</p>
         */
        final String entryRequestKey =
                RuntimeTraceContext.current().requestKey;
        private final long startedAtNanos = System.nanoTime();

        long elapsedMillis() {
            return Math.max(0L,
                    (System.nanoTime() - startedAtNanos) / 1_000_000L);
        }

        final long token;
        /** The one task whose region-local path this activation records. */
        final RuntimeTask activation;
        /**
         * This activation's ordinal within its address, taken at admission so
         * every symbol, mint row and handoff lineage it publishes can name
         * the occurrence it belongs to rather than the planned address.
         */
        int activationOrdinal;
        /**
         * The enclosing invocation these loop bodies were charged to: its
         * entry event, the thread that ran it, and the k it was counted at.
         *
         * <p>Zero and "" on a region that is not a loop body.  An
         * occurrence is (node, epoch, region, k-th activation), and its loop
         * bodies are its own; bodies of a different enclosing invocation --
         * another thread, another entry event -- belong to a different k by
         * definition, so the row says which one it was.</p>
         */
        long enclosingInvocationEvent;
        String enclosingInvocationThread = "";
        int enclosingInvocationOrdinal;
        /** VM context whose writes belong to this materialized activation. */
        long vmContextId;
        /** Exact event-ledger entry of this native region frame. */
        long vmRegionEnterEventId;
        final Object receiver;
        private final Thread thread;
        /** Entry lacked local producer-source evidence; OUT must confirm it. */
        /** Exact outgoing message leaves this provisional activation reached. */
        final AtomicBoolean finished = new AtomicBoolean();
        private boolean prepared;
        /**
         * The declared target branch event this occurrence decided, or {@code
         * null} while it has not decided one.
         */
        JsonObject targetReach;
        /** Terminal outcome, frozen when the occurrence stops running. */
        boolean abandoned;
        /** A selected non-loop occurrence ended in a durable named gap. */
        private boolean terminalGap;
        private boolean closed;
        /** Loop bodies this activation has charged. */
        volatile long chargedLoopBodies;
        /**
         * The stable causal context this candidate observed while it was live:
         * the logical sources it ran on and the external request scopes it ran
         * inside.
         */
        private final Set<String> observedSourceKeys = new LinkedHashSet<>();
        /** element key -> attaches of it so far in this activation. */
        private final Map<String, Integer> handoffAttachOrdinals =
                new LinkedHashMap<>();
        /**
         * Every stable source this occurrence can be attributed to by the
         * application's own registration.
         *
         * <p>Two kinds of evidence, both produced by the replay itself.</p>
         */
        private Set<String> attributedSourceKeys() {
            Set<String> keys = new LinkedHashSet<>(observedSourceKeys);
            SourceRef registered = RuntimeTraceContext.sourceFor(receiver);
            if (registered != null) keys.add(registered.key());
            return keys;
        }

        private synchronized boolean beginClose() {
            if (closed) return false;
            closed = true;
            return true;
        }

        String exitKind = "";
        String exceptionType = "";
        Throwable exitThrowable;
        /** Exact configured-source and planned-action observations. */
        final List<JsonObject> symbolizedRows = new ArrayList<>();
        /** Exact configured source roots materialized by this activation. */
        final Map<String, JsonObject> symbolicSources =
                new LinkedHashMap<>();
        /**
         * Mint sites, and the fields they mint, this activation reached.
         *
         * <p>A configured source mints one symbol per element of the walk it
         * runs, and those occurrences are recorded here rather than in
         * the ordinary input-action ledger: the mint hook is a call-site
         * phase, not an instrumented field access. A capture anchored on one of those
         * per-element ports is answered by the site having run.</p>
         */
        private final Set<String> reachedConfiguredSourceSites =
                new LinkedHashSet<>();
        /** Phase entries used by this activation; committed on publication. */
        final Map<String, Integer> configuredSourcePhaseOrdinals =
                new LinkedHashMap<>();
        /** Ordered, structured replay ledger emitted with the raw result. */
        final List<JsonObject> configuredSourcePhaseObservations =
                new ArrayList<>();
        /** Structured fail-closed phase replay gaps. */
        final List<JsonObject> configuredSourcePhaseGaps =
                new ArrayList<>();
        private final Set<String> configuredSourcePhaseGapIdentities =
                new LinkedHashSet<>();
        /** Exact semantic anchors this activation will commit if published. */
        final Set<String> unresolved = new LinkedHashSet<>();
        final List<JsonObject> branchMappings = new ArrayList<>();
        /**
         * Case-local references into the VM's own handoff ledger: the
         * declared port an attach landed on and the export event the
         * {@code VALUE_HANDOFF} edge relates it to.
         */
        final List<JsonObject> vmHandoffEvents = new ArrayList<>();
        /**
         * VM export event most recently published at each declared port.
         *
         * <p>README {@code RPC-1}: written down from the VM's own export
         * answer so the producer's interaction row can name it.</p>
         */
        final List<JsonObject> rpcHandoffGaps = new ArrayList<>();

        /** The write log this activation read out, and its gaps. */
        final Map<String, JsonObject> sharedStateRecords =
                new LinkedHashMap<>();
        final List<JsonObject> sharedStateGaps = new ArrayList<>();
        /** Read-out batch every record of this activation is stamped with. */
        private long evidenceSnapshot;
        private final Set<String> materialized = new LinkedHashSet<>();
        private final Map<String, Long> armedGuardedReads =
                new LinkedHashMap<>();
        private final Set<String> materializedGuardedReads =
                new LinkedHashSet<>();
        private final Set<String> appliedModelAssignments =
                new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        private final OccurrenceCounter
                materializationOccurrences =
                new OccurrenceCounter();
        private final Map<String, Integer> accessorCallOccurrences =
                new LinkedHashMap<>();
        final LoopBackedgeBudget loopBackedges;
        /** Current fixed-count invocation by runtime natural-loop id. */
        private final Map<String, DynamicLoopCardinality>
                activeLoopCardinalities = new LinkedHashMap<>();
        /** Next occurrence ordinal by runtime natural-loop id. */
        private final Map<String, Integer> loopCardinalityOccurrences =
                new LinkedHashMap<>();
        /** Exact N for every dynamic fixed-count invocation in this path. */
        final List<JsonObject> loopCardinalities = new ArrayList<>();
        /** Ambiguous/malformed cardinality observations remain coverage. */
        final List<JsonObject> loopCardinalityGaps =
                new ArrayList<>();
        private final Map<Long, PreparedBranch> preparedBranches =
                new LinkedHashMap<>();
        private final IdentityHashMap<Object, String>
                symbolizedInputPorts = new IdentityHashMap<>();
        private final Map<String, Integer> associativeAccessOccurrences =
                new LinkedHashMap<>();
        private final BranchReplayContract.ReplayProgress replayProgress;
        /** One shared expression DAG for all read-outs in this VM session. */
        final VmExpressionTable.Store expressionStore;
        private long preparedBranchSequence;
        private int lastPathConditionSize;
        JsonObject loopBoundCut;
        JsonObject replayResourceCut;
        boolean pathRecordingStarted;

        ActiveRegion(long token, RuntimeTask activation,
                             Object receiver, Thread thread) {
            this.token = token;
            this.activation = activation;
            this.receiver = receiver;
            this.thread = thread;
            this.expressionStore = workloadExpressionStore;
            this.loopBackedges = new LoopBackedgeBudget(
                    activation.loopBound);
            this.replayProgress = new BranchReplayContract.ReplayProgress(
                    activation.replayContract);
        }


        /** Gives back this activation's ordinal; it published nothing. */
        void releaseActivationOrdinal() {
            if (activationOrdinal <= 0) return;
            activation.releaseActivationOrdinal(activationOrdinal);
            activationOrdinal = 0;
        }

        /** This activation's own occurrence identity: address plus ordinal. */
        String occurrenceId() {
            return activationOrdinal <= 0 ? safe(activation.occurrenceId)
                    : OccurrenceId.parse(safe(activation.occurrenceId))
                            .withActivation(activationOrdinal).render();
        }

        /**
         * Charges one body of this loop to the replay resource cap, returning
         * the cut that ends the activation once the cap is spent.
         */
        private synchronized ReplayLoopResourceCut chargeLoopBody(
                String loopId) {
            int maxBodies = activation.maxLoopBodies(loopId);
            chargedLoopBodies++;
            // A fixed-count loop may be invoked repeatedly inside one region
            // activation.  Its resource ceiling applies to each dynamic
            // invocation; accumulating all invocations under the static loop
            // id cuts ordinary code after (for example) two 16-element array
            // walks.  recordLoopCardinality opens the exact invocation before
            // the first body hook and completeLoopCardinality closes it.
            DynamicLoopCardinality invocation =
                    activeLoopCardinalities.get(loopId);
            String budgetKey = invocation == null ? loopId
                    : LoopBackedgeBudget.scoped(
                    loopId, invocation.occurrence);
            long entered = loopBackedges.recordBody(budgetKey);
            if (entered <= maxBodies) return null;
            ReplayLoopResourceCut cut = new ReplayLoopResourceCut(
                    loopId, maxBodies, entered);
            if (replayResourceCut == null) {
                replayResourceCut = cut.toJson();
            }
            return cut;
        }

        private synchronized void recordLoopCardinality(
                String loopId, int cardinality) {
            if (loopId.isEmpty() || cardinality < 0) {
                loopCardinalityGap(
                        LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS,
                        loopId, 0,
                        "fixed-count array observation has no valid loop id "
                                + "or non-negative cardinality");
                return;
            }
            DynamicLoopCardinality current =
                    activeLoopCardinalities.get(loopId);
            if (current == null) {
                int occurrence = loopCardinalityOccurrences
                        .getOrDefault(loopId, 0) + 1;
                loopCardinalityOccurrences.put(loopId, occurrence);
                current = new DynamicLoopCardinality(
                        occurrence, cardinality);
                activeLoopCardinalities.put(loopId, current);
                JsonObject row = new JsonObject();
                row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, loopId);
                row.addProperty(LoopBoundPolicy.DYNAMIC_OCCURRENCE,
                        occurrence);
                row.addProperty(LoopBoundPolicy.LOOP_CARDINALITY,
                        cardinality);
                row.addProperty("cardinalityAuthority",
                        LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY);
                loopCardinalities.add(row);
                return;
            }
            if (current.cardinality != cardinality) {
                loopCardinalityGap(
                        LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS,
                        loopId, current.occurrence,
                        "one dynamic fixed-count occurrence observed N="
                                + current.cardinality + " and N="
                                + cardinality);
            }
        }

        private synchronized void completeLoopCardinality(String loopId) {
            if (!loopId.isEmpty()) activeLoopCardinalities.remove(loopId);
        }

        private void loopCardinalityGap(String reason, String loopId,
                                        int occurrence, String detail) {
            JsonObject row = new JsonObject();
            row.addProperty("reason", reason);
            row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, loopId);
            if (occurrence > 0) {
                row.addProperty(LoopBoundPolicy.DYNAMIC_OCCURRENCE,
                        occurrence);
            }
            row.addProperty("detail", detail);
            loopCardinalityGaps.add(row);
        }

        /** Records the terminal of this activation's bounded local path. */
        LoopBoundCut loopBoundCut(
                String backedgeId, int maxTraversals, String reason) {
            LoopBoundCut cut = new LoopBoundCut(backedgeId, maxTraversals,
                    reason);
            if (loopBoundCut == null) {
                loopBoundCut = cut.toJson();
                addUnresolvedOnce("LOOP_BOUND_PATH_CUT:"
                        + cut.backedgeId + ':' + cut.reason);
            }
            return cut;
        }

        /** k for the next attach of one element in this activation. */
        private int nextHandoffAttach(String elementKey) {
            Integer previous = handoffAttachOrdinals.get(elementKey);
            int ordinal = previous == null ? 1 : previous + 1;
            handoffAttachOrdinals.put(elementKey, ordinal);
            return ordinal;
        }

        private int nextBranchOccurrence(String siteId) {
            Integer previous = branchOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            branchOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        /** Records a decision while the symbolic gate is closed. */
        private ExactConcreteBranchObservation recordConcreteDecision(
                String method, int unitIndex, BranchDecision decision) {
            try {
                // observeDecision is the only caller and it has already
                // returned for every undeclared site, so the site here is
                // always one the plan named.
                String site = SiteId.render(method, unitIndex);
                ExactConcreteBranchObservation observation =
                        decision.observationAt(site, safe(method), unitIndex,
                                nextBranchOccurrence(site));
                recordDecisionRow(method, unitIndex,
                        observation.occurrence(), observation);
                if (activation.targetBranchSite.equals(site)
                        && activation.targetBranchOccurrence
                        == observation.occurrence()) {
                    recordTargetReach(site, observation.occurrence(),
                            decision.outcome(), 0L);
                }
                return observation;
            } catch (Throwable ignored) {
                // Observation must never alter the workload's own outcome.
                return null;
            }
        }

        /** Persists an exact replay-invocation boundary without adding a PC. */
        private ExactConcreteBranchObservation recordReplayBoundary(
                String method, int unitIndex, int occurrence,
                BranchDecision decision) {
            try {
                ExactConcreteBranchObservation observation =
                        decision.observationAt(SiteId.render(method, unitIndex),
                                safe(method), unitIndex, occurrence);
                recordDecisionRow(method, unitIndex, occurrence, observation);
                return observation;
            } catch (Throwable ignored) {
                return null;
            }
        }

        /** The branch row one decision that added no path condition is. */
        private void recordDecisionRow(
                String method, int unitIndex, int occurrence,
                ExactConcreteBranchObservation observation) {
            JsonObject mapping = branchMapping(method, unitIndex, occurrence,
                    0L);
            mapping.addProperty("rawPathConditionSize", 0);
            mapping.addProperty("rawPathConditionBaseline", 0);
            mapping.add("concreteObservation", observation.toJson());
            branchMappings.add(mapping);
        }

        private boolean observeReplayDecision(
                String siteId, int occurrence, BranchDecision decision) {
            return observeReplayDecision(siteId, occurrence, decision, "");
        }

        private boolean observeReplayDecision(
                String siteId, int occurrence, BranchDecision decision,
                String symbolicSupportDigest) {
            boolean matched = decision.observeReplayProgress(replayProgress,
                    siteId, occurrence, symbolicSupportDigest);
            diag("REPLAY_OBSERVE", siteId + " occ=" + occurrence
                    + decision.replayTrace(matched)
                    + " complete=" + replayProgress.complete()
                    + " failed=" + replayProgress.failed());
            if (replayProgress.failed()) {
                addUnresolvedOnce("REPLAY_PREFIX_MISMATCH:"
                        + replayProgress.failure());
            }
            return matched;
        }

        /**
         * Whether this activation has already walked a branch the recorded
         * replay prefix forbids.
         */
        private boolean replayPrefixContradicted() {
            return activation.replayContract != null
                    && replayProgress.failed();
        }

        private int nextLocalMaterializationOccurrence(
                String method, int unitIndex, String local) {
            return materializationOccurrences.local(method, unitIndex,
                    local);
        }

        private PreparedBranch prepareBranch(
                String method, int unitIndex, String expression)
                throws Exception {
            String site = SiteId.render(method, unitIndex);
            int occurrence = nextBranchOccurrence(site);
            long sequence = ++preparedBranchSequence;
            if (sequence > Integer.MAX_VALUE) {
                addUnresolvedOnce(site + "#" + occurrence
                        + ": prepared branch sequence overflow");
                return null;
            }
            long handle = (sequence << 32)
                    | (occurrence & 0xffffffffL);
            PreparedBranch prepared = new PreparedBranch(handle, method,
                    unitIndex, expression, occurrence);
            preparedBranches.put(handle, prepared);
            return prepared;
        }

        private PreparedBranch takePreparedBranch(long handle) {
            return handle <= 0L ? null : preparedBranches.remove(handle);
        }

        /**
         * Names a declared target branch event this occurrence never decided,
         * and the target task that declared no such event at all.
         *
         * <p>The second case used to return here in silence, which is what
         * let {@code targetReachedByActivation} read any throw as the reach:
         * no declaration to check it against, and no row saying the check was
         * impossible.  A target-reach task with no named fatal occurrence has
         * no target link to state, and that is a gap like any other.</p>
         */
        void nameUnreachedTargetBranch() {
            if (!activation.declaresTargetBranch()) {
                if (activation.capturesTargetReach) {
                    addUnresolvedOnce(TARGET_REACH_NOT_OBSERVED
                            + ": this target-reach task names no target read "
                            + "or throw occurrence, so no site this replay "
                            + "decided can be shown to be the one it claims "
                            + "to reach (exit " + safe(exitKind) + " "
                            + safe(exceptionType) + ")");
                }
                return;
            }
            if (targetReach != null) return;
            addUnresolvedOnce("TARGET_BRANCH_NOT_REACHED: "
                    + activation.targetBranchLabel()
                    + " was not decided before this occurrence ended at "
                    + safe(exitKind));
        }

        /**
         * Records the declared target branch event this occurrence decided.
         */
        private void recordTargetReach(String siteId, int occurrence,
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
            diag("TARGET_REACHED", "token=" + token + " site=" + safe(siteId)
                    + "#" + occurrence);
        }

        void addUnresolvedOnce(String detail) {
            String value = safe(detail);
            if (!value.isEmpty()) unresolved.add(value);
        }

        /**
         * Records one firing of a fault marker this replay could not answer.
         *
         * <p>{@code controlled} decides whether it blocks: a marker the plan
         * declares is a question the search asked and the model did not
         * answer, and the polarity it would otherwise default to is the very
         * one the search exists to flip.  A marker the plan never declared
         * put no question to this replay.</p>
         */
        /**
         * Records that one firing was answered from the recording, not from
         * a model.
         *
         * <p>It is not a gap -- the question has an answer -- but a witness
         * that moves nothing has to be distinguishable from one that moved a
         * marker the solver chose, so which firings the seed answered is
         * stated rather than left to be inferred from an absent
         * assignment.</p>
         */
        void noteRecordedFaultAnswer(String name, int occurrence,
                                     boolean recorded) {
            diag(RECORDED_FAULT_ANSWER, "marker=" + safe(name) + "#"
                    + occurrence + " recorded=" + recorded
                    + " occurrence=" + safe(activation.occurrenceId));
        }

        void noteFaultIdle(String name, int occurrence, boolean controlled,
                           String reason) {
            String subject = "marker=" + safe(name) + "#" + occurrence
                    + " reason=" + safe(reason);
            diag(FAULT_IDLE_UNANSWERED, subject + " controlled=" + controlled
                    + " occurrence=" + safe(activation.occurrenceId));
            if (controlled) {
                addUnresolvedOnce(FAULT_IDLE_UNANSWERED + ": " + subject
                        + "; this plan controls the marker, so an unanswered "
                        + "firing may not read back as its idle polarity");
            }
        }

        /**
         * Counts one entry of one declared mint site.
         *
         * <p>The catalog is a list of mint SITES, not a selection: any entry
         * of a known site mints, and the ordinal is the entry count.  A hook
         * that fires at a site the catalog does not name is still a gap -
         * that is a plan/instrumentation disagreement, not a free
         * occurrence.</p>
         */
        private synchronized SourceSiteEntry observeConfiguredSourceEntry(
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
                addSourcePhaseGap("ACTIVE_CALL_SITE_MISSING",
                        declaration.isEmpty() ? null : declaration.get(0),
                        "PUBLISH hook for " + safe(sourceId)
                                + " has no active call-site context");
                return null;
            }
            if (declaration.isEmpty()) {
                addSourcePhaseGap("EXTRA", null,
                        "PUBLISH " + site + " is outside the replay-call "
                                + "catalog");
                return null;
            }
            String ordinalKey = "PUBLISH\n" + safe(sourceId) + "\n" + site;
            int localOrdinal = configuredSourcePhaseOrdinals.merge(
                    ordinalKey, 1, Integer::sum);
            int ordinal = activation.configuredSourcePhaseOrdinal(
                    ordinalKey, localOrdinal);
            boolean cataloged = ordinal <= declaration.size();
            ConfiguredSourcePhaseContract.Occurrence matched = cataloged
                    ? declaration.get(ordinal - 1)
                    : declaration.get(declaration.size() - 1);
            if (!cataloged) {
                addSourcePhaseGap("EXTRA", matched,
                        "PUBLISH " + site + " occurrence " + ordinal
                                + " exceeds the frozen phase catalog size "
                                + declaration.size());
                return null;
            }
            if (!matched.fieldSignature().equals(
                    safe(runtimeFieldSignature))
                    || !matched.runtimeDeclaredCallee().equals(
                    context.declaredCallee())) {
                addSourcePhaseGap("DECLARATION_MISMATCH", matched,
                        "runtime field/callee differs from the catalog site");
                return null;
            }
            reachedConfiguredSourceSites.add(matched.siteId());
            if (!site.isEmpty()) reachedConfiguredSourceSites.add(site);
            recordConfiguredSourcePhaseObservation(matched, context);
            return new SourceSiteEntry(matched, site, ordinal);
        }

        /**
         * Records that one named catalog entry was reached.  The row carries
         * runtime facts only: everything else about the entry is read off the
         * catalog row {@code matchedPhaseId} names.
         */
        private void recordConfiguredSourcePhaseObservation(
                ConfiguredSourcePhaseContract.Occurrence matched,
                CausynthTraceRecorder.ActiveCallSiteContext context) {
            JsonObject observation = new JsonObject();
            observation.addProperty("schemaVersion", 1);
            observation.addProperty("kind",
                    "CONFIGURED_SOURCE_PHASE_OBSERVATION");
            observation.addProperty("authority",
                    "EXACT_ACTIVE_CALL_SITE_REPLAY_V1");
            observation.addProperty("observationIndex",
                    configuredSourcePhaseObservations.size() + 1);
            observation.addProperty("matchedPhaseId", matched.phaseId());
            observation.addProperty("ownerCallId", context.ownerCallId());
            observation.addProperty("invocationId", context.invocationId());
            configuredSourcePhaseObservations.add(observation);
        }

        /**
         * Whether a model for this phase is this activation's to apply.
         *
         * <p>Only an activation that minted the root FRESH owes it: the
         * model is written into the value the mint is about to symbolize,
         * so an activation that found the root already symbolic -- the
         * second activation of a site the first one minted, which is what
         * "one variable per phase" means -- has nothing to write it into.
         * On hdfs-17899 bug3 that is the two companions addressed at
         * REGION.08ab84c9#2, refused at their terminal for not applying a
         * model to a root activation #1 had already minted.</p>
         *
         * <p>Reaching the site is not enough and never was: a hook that
         * returns before minting (no declared owner, not an exact
         * primitive) leaves nothing to write into either, and says so with
         * its own unresolved note.</p>
         */
        private synchronized boolean owesConfiguredSourceModel(
                String phaseId) {
            String wanted = safe(phaseId);
            if (wanted.isEmpty()) return false;
            for (JsonObject row : symbolizedRows) {
                if (wanted.equals(optionalString(row, "sourcePhaseId"))) {
                    return !optionalBool(row, "reused", false);
                }
            }
            return false;
        }

        /** Publishes one mint row for one entry of a declared site. */
        private synchronized void recordConfiguredSourceMint(
                SourceSiteEntry entry, String sourceId,
                String fieldSignature, String symbol,
                JsonElement expression, boolean reused) {
            JsonObject row = new JsonObject();
            row.addProperty("sourceId", safe(sourceId));
            row.addProperty("sourcePhaseId", entry.phaseId());
            row.addProperty("occurrenceId", occurrenceId());
            row.addProperty("siteId", entry.siteId);
            row.addProperty("ordinal", entry.ordinal);
            row.addProperty("fieldSignature", safe(fieldSignature));
            row.addProperty("symbol", safe(symbol));
            row.add("expression", expression == null
                    ? JsonNull.INSTANCE : expression);
            row.addProperty("reused", reused);
            symbolizedRows.add(row);
        }

        /**
         * Records what one exact frozen {@code SYMBOLIC} action observed after
         * its runtime hook either minted a value or retained a propagated one.
         * The requested VM label is descriptive only; downstream authority is
         * derived from the exact expression, never from this label.
         */
        private synchronized void recordManualSymbolization(
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
         * what the field held ({@code SymbolicSourceEvidence.recordedValue})
         * and a manual one stated nothing, so a root the composer met
         * through a manual input had no recorded value to lower -- on lane
         * VM12 that is DelegationKey.expiryDate, minted as
         * {@code M_J_field_REGION.aaa1cfd7...}, and
         * RECORDED_ROOT_VALUE_UNSTATED was the anchor's last refusal.  The
         * suppression rule is the configured source's too: a replay that
         * wrote a model into the value read the model back, and publishing
         * that as "recorded" is how a counterfactual becomes the
         * recording.</p>
         */
        private synchronized void recordManualSymbolization(
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
            row.addProperty("kind", MANUAL_INPUT_OBSERVATION_KIND);
            row.addProperty("authority",
                    MANUAL_INPUT_OBSERVATION_AUTHORITY);
            row.addProperty("portId", action.symbol);
            row.addProperty("actionDigest", action.actionDigest);
            row.addProperty("plannedOccurrenceId",
                    activation.occurrenceId);
            row.addProperty("occurrenceId", occurrenceId());
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
                // What THIS execution read at the mint.  For every root but
                // a clock it is also what the recording read, and the two
                // members carry the same value; for a clock they differ by
                // definition, and a reader that needs this replay's own
                // instant -- the per-path window is centred on it -- must
                // not have to take the seed's.
                row.addProperty("observedValue", recordedValue);
                row.addProperty("recordedValue", recordedValue);
            }
            // A cell minted through the clock hook is a wall-clock read by
            // construction: the declaration names the callee, so the mint
            // row states it and no reader downstream has to guess a clock
            // from a site name.  The value it states is the one the
            // RECORDING read, not this replay's: a clock is what every
            // replay reads differently, and pinning the root to one
            // replay's instant is what left eleven of bug3's twelve paths
            // unsatisfiable at every valuation.  The recorded reading is
            // the centre of the window the case's declared skew allows.
            if (action.declaresWallClockRead()) {
                row.addProperty("declaredCallee", action.declaredCallee);
                row.addProperty("siteId", action.siteId);
                row.addProperty("eventSeq", action.eventSeq);
                row.addProperty("recordedValue",
                        action.recordedPrimitiveValue);
            }
            symbolizedRows.add(row);
        }

        private synchronized void addSourcePhaseGap(
                String gapKind,
                ConfiguredSourcePhaseContract.Occurrence phase,
                String detail) {
            String phaseId = phase == null ? "" : phase.phaseId();
            String identity = safe(gapKind) + "\n" + phaseId + "\n"
                    + safe(detail);
            if (!configuredSourcePhaseGapIdentities.add(identity)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("schemaVersion", 1);
            gap.addProperty("kind", "CONFIGURED_SOURCE_PHASE_GAP");
            gap.addProperty("authority",
                    "FAIL_CLOSED_EXACT_PHASE_REPLAY_V1");
            gap.addProperty("gapKind", safe(gapKind));
            gap.addProperty("phaseId", phaseId);
            gap.addProperty("phaseKind",
                    phase == null ? "" : phase.phase().name());
            gap.addProperty("siteId",
                    phase == null ? "" : phase.siteId());
            gap.addProperty("baselineOrdinal",
                    phase == null ? 0 : phase.baselineOrdinal());
            gap.addProperty("sourceId",
                    phase == null ? "" : phase.sourceId());
            gap.addProperty("detail", safe(detail));
            configuredSourcePhaseGaps.add(gap);
            addUnresolvedOnce("CONFIGURED_SOURCE_PHASE_" + safe(gapKind)
                    + ": " + (phaseId.isEmpty() ? safe(detail)
                    : phaseId + ": " + safe(detail)));
        }

        private synchronized void recordSymbolicSource(
                String sourcePhaseId, JsonObject evidence) {
            JsonObject prior = symbolicSources.putIfAbsent(sourcePhaseId,
                    shallowCopy(evidence));
            if (prior != null && !prior.equals(evidence)) {
                addUnresolvedOnce(sourcePhaseId
                        + ": configured source phase produced conflicting "
                        + "expressions");
            }
        }

        /**
         * The read-out batch this activation's evidence belongs to, allocated
         * on first use so a capture outside the exit batch still gets its own
         * comparable ordinal rather than borrowing a later one.
         */
        long evidenceSnapshot() {
            if (evidenceSnapshot == 0L) {
                evidenceSnapshot = EVIDENCE_SNAPSHOTS.incrementAndGet();
            }
            return evidenceSnapshot;
        }

        private void recordSymbolizedInputPort(String symbol, Object value) {
            if (value == null) return;
            String previous = symbolizedInputPorts.get(value);
            symbolizedInputPorts.put(value, previous == null
                    || previous.equals(symbol) ? symbol : "");
        }

        /**
         * The one unspent assignment matching {@code matcher}.  Two survivors
         * address nothing, so the ambiguity is filed and neither applies.
         */
        private ModelAssignment uniqueAssignment(
                Predicate<ModelAssignment> matcher, boolean reusable,
                String subject, String ambiguity) {
            ModelAssignment selected = null;
            for (ModelAssignment candidate : activation.modelAssignments) {
                if (!matcher.test(candidate) || !reusable
                        && appliedModelAssignments.contains(candidate.key)) {
                    continue;
                }
                if (selected != null) {
                    addUnresolvedOnce(subject + ambiguity);
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        private ModelAssignment assignment(SymbolizeAction action,
                                           List<String> path) {
            return uniqueAssignment(
                    candidate -> candidate.matches(action, path),
                    action.repeatedPrimitiveAccessor(), action.symbol,
                    ": ambiguous model assignments");
        }

        /** One solver value for one exact configured source hook. */
        private ModelAssignment configuredSourceAssignment(
                String sourcePhaseId, String sourceId,
                String fieldSignature, Object mintOwner) {
            ModelAssignment selected = uniqueAssignment(
                    candidate -> candidate.matchesConfiguredSource(
                            sourcePhaseId, sourceId, fieldSignature),
                    false, sourcePhaseId,
                    ": ambiguous configured source models");
            if (selected == null) return null;
            // A configured-source model names one mint SITE, and the site is
            // reached once per node lifecycle.  The site is not the address:
            // the address is (node, epoch, region, k-th activation), and the
            // epoch is the half nothing here was checking.  On hdfs-17960 the
            // flip replay threw inside the workload before it restarted the
            // NameNode, so the only activation it offered was epoch 0 -- and
            // root=false was written there, at the mint the recording made
            // before the restart, instead of at the epoch-1 mint the plan
            // addresses.  The recorded execution was rewritten at a point the
            // solver said nothing about.
            String unattributed = mintIsNotThePlannedNode(mintOwner);
            if (!unattributed.isEmpty()) {
                addSourcePhaseGap(mintAttribution(mintOwner).isEmpty()
                        ? "MINT_UNATTRIBUTED" : "EPOCH_UNMATCHED", null,
                        unattributed);
                return null;
            }
            return selected;
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

        private boolean hasAppliedExactNullReferenceAssignment(
                SymbolizeAction action) {
            if (action == null || !action.declaresReferenceInput()) {
                return false;
            }
            int matches = 0;
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.matches(action, null)
                        && assignment.inputSymbol.equals(action.symbol)
                        && assignment.modelIsNull
                        && ("NULL".equalsIgnoreCase(assignment.valueType)
                        || "null".equalsIgnoreCase(assignment.value))
                        && appliedModelAssignments.contains(assignment.key)) {
                    matches++;
                }
            }
            return matches == 1;
        }

        private List<ModelAssignment> fieldAssignments(
                SymbolizeAction action) {
            List<ModelAssignment> result = new ArrayList<>();
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.targetsFieldAccess(action)
                        && !assignment.dynamicAssociativeTarget()
                        && !appliedModelAssignments.contains(assignment.key)) {
                    result.add(assignment);
                }
            }
            return result;
        }

        private void recordModelAssignment(ModelAssignment assignment) {
            appliedModelAssignments.add(assignment.key);
        }

    }

    /** Active identity of one dynamic fixed-count loop invocation. */
    private static final class DynamicLoopCardinality {
        private final int occurrence;
        private final int cardinality;

        private DynamicLoopCardinality(int occurrence, int cardinality) {
            this.occurrence = occurrence;
            this.cardinality = cardinality;
        }
    }

    /** Per-activation, per-CFG-edge completed traversal accounting. */
    static final class LoopBackedgeBudget {
        private static final String SCOPE_SEPARATOR = "\u0000definition:";
        private final int maxTraversals;
        private final Map<String, Integer> traversals =
                new LinkedHashMap<>();
        private final Map<String, Integer> bodies = new LinkedHashMap<>();

        LoopBackedgeBudget(LoopBoundPolicy policy) {
            if (policy == null) {
                throw new IllegalArgumentException(
                        "loop bound policy is required");
            }
            maxTraversals = policy.maxBackedgeTraversals();
        }

        long recordTraversal(String backedgeId) {
            Integer previous = traversals.get(backedgeId);
            int completed = previous == null ? 0 : previous;
            long attempted = (long) completed + 1L;
            // Body one executes before this edge. Attempt K would enter body
            // K+1, so only the first K-1 backedge transfers may complete.
            if (attempted < maxTraversals) {
                traversals.put(backedgeId, (int) attempted);
            }
            return attempted;
        }

        static String scoped(String loopId, long invocation) {
            return safe(loopId) + SCOPE_SEPARATOR + invocation;
        }

        /**
         * Counts one body of this loop against the replay resource cap and
         * returns the body number just entered.
         */
        long recordBody(String loopId) {
            long entered = (long) bodies.getOrDefault(loopId, 0) + 1L;
            bodies.put(loopId, (int) Math.min(entered, Integer.MAX_VALUE));
            return entered;
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            for (Map.Entry<String, Integer> entry : traversals.entrySet()) {
                String scoped = safe(entry.getKey());
                int separator = scoped.indexOf(SCOPE_SEPARATOR);
                String loopId = separator < 0 ? scoped
                        : scoped.substring(0, separator);
                int previous = optionalInteger(encoded, loopId, 0);
                if (entry.getValue() > previous) {
                    encoded.addProperty(loopId, entry.getValue());
                }
            }
            return encoded;
        }

        JsonObject bodiesToJson() {
            JsonObject encoded = new JsonObject();
            for (Map.Entry<String, Integer> entry : bodies.entrySet()) {
                String scoped = safe(entry.getKey());
                int separator = scoped.indexOf(SCOPE_SEPARATOR);
                String loopId = separator < 0 ? scoped
                        : scoped.substring(0, separator);
                long total = (long) optionalInteger(encoded, loopId, 0)
                        + entry.getValue();
                encoded.addProperty(loopId,
                        (int) Math.min(total, Integer.MAX_VALUE));
            }
            return encoded;
        }
    }

    /**
     * Non-workload control signal aborting a replay that has spent its loop
     * resource cap.
     */
    public static final class ReplayLoopResourceCut extends Error {
        private static final long serialVersionUID = 1L;
        static final String REASON = "REPLAY_LOOP_RESOURCE_CAP";
        private final String loopId;
        private final int maxBodies;
        private final long attemptedBody;

        ReplayLoopResourceCut(String loopId, int maxBodies,
                              long attemptedBody) {
            super(REASON + " at " + safe(loopId) + ": body "
                    + attemptedBody + " exceeds " + maxBodies);
            this.loopId = safe(loopId);
            this.maxBodies = maxBodies;
            this.attemptedBody = attemptedBody;
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("kind", REASON);
            encoded.addProperty("loopId", loopId);
            encoded.addProperty("maxLoopBodies", maxBodies);
            encoded.addProperty("attemptedBody", attemptedBody);
            encoded.addProperty("reason", REASON);
            return encoded;
        }

    }

    /** Non-workload control signal used solely to abort a bounded path. */
    public static final class LoopBoundCut extends Error {
        private static final long serialVersionUID = 1L;
        private final String backedgeId;
        private final int maxTraversals;
        private final String reason;

        LoopBoundCut(String backedgeId, int maxTraversals, String reason) {
            super("concolic path cut at " + safe(backedgeId)
                    + " after " + maxTraversals
                    + " loop body iterations");
            this.backedgeId = safe(backedgeId);
            this.maxTraversals = maxTraversals;
            this.reason = safe(reason);
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("kind", "LOOP_BOUND");
            encoded.addProperty("backedgeId", backedgeId);
            encoded.addProperty("maxBackedgeTraversals", maxTraversals);
            encoded.addProperty("reason", reason);
            return encoded;
        }
    }

    static final class SymbolizeAction {
        final String symbol;
        /** Canonical identity of the exact frozen task action row. */
        final String actionDigest;
        final String cell;
        final String location;
        final int index;
        final int replayOccurrence;
        final List<List<String>> fieldPaths;
        final String bindingMode;
        final String method;
        final String local;
        final String accessField;
        final String accessOwnerClass;
        final String accessFieldSignature;
        final Set<String> accessSites = new LinkedHashSet<>();
        final String accessorCallerMethod;
        final int accessorCallUnitIndex;
        final String accessorDeclaredCallee;
        final String accessorImplementationMethod;
        final String symbolicDemand;
        /** How the finalizer classified the port that minted this action. */
        final String sourceKind;
        /** The external call whose return this action symbolizes, or "". */
        final String declaredCallee;
        /** The static site the plan observed this read at, or "". */
        final String siteId;
        /** The recorded event this read was observed at, or -1. */
        final long eventSeq;
        /** What this read returned in the recording, or "" when unobserved. */
        final String recordedPrimitiveValue;
        /** The selection file named this input by hand: mint, do not reuse. */
        final boolean declaredSymbolicRoot;
        /**
         * Whether this input may become a fresh root at all.
         *
         * <p>The scheduler tracks every carrier -- so the VM keeps
         * publishing its {@code ReadFrom} candidates and container versions
         * -- while reserving the mint for the three declaring authorities.
         * A tracked carrier that no propagated expression reached is simply
         * read at its recorded value; falling through to a mint would put a
         * free root exactly where the experiment said there is none.
         * Absent from a plan row it defaults to {@code true}, which is the
         * unnarrowed behaviour of a campaign with no selection file.</p>
         */
        final boolean mintEligible;
        final String rootKind;
        final List<String> fieldPath;
        final String javaType;
        final String symbolicName;
        final Set<Integer> definitionUnitIndices =
                new LinkedHashSet<>();
        final Map<String, String> leafFieldSignaturesByPath =
                new LinkedHashMap<>();

        SymbolizeAction(JsonObject json) {
            this.symbol = optionalString(json, "symbol");
            this.actionDigest = CanonicalJson.sha256(json);
            this.cell = optionalString(json, "cell");
            this.location = optionalString(json, "location");
            this.index = optionalInteger(json, "index", -1);
            this.replayOccurrence = optionalInteger(json,
                    "replayOccurrence", -1);
            this.bindingMode = optionalString(json, "bindingMode");
            this.javaType = optionalString(json, "javaType");
            JsonObject definition = json;
            this.method = optionalString(definition, "method");
            this.local = optionalString(definition, "local");
            int unitIndex = optionalInteger(definition, "unitIndex", -1);
            if (unitIndex >= 0) definitionUnitIndices.add(unitIndex);
            for (JsonElement element : array(json, "definitionSites")) {
                if (element.isJsonObject()) {
                    int definitionIndex = optionalInteger(element.getAsJsonObject(),
                            "unitIndex", -1);
                    if (definitionIndex >= 0) {
                        definitionUnitIndices.add(definitionIndex);
                    }
                }
            }
            this.fieldPath = new ArrayList<>(
                    FieldPathSpec.stringArray(json, "fieldPath"));
            this.accessField = this.fieldPath.isEmpty() ? ""
                    : this.fieldPath.get(0);
            this.accessFieldSignature = optionalString(json,
                    "accessFieldSignature");
            DeclaredField accessDeclaration = FieldPathSpec.declaredField(
                    this.accessFieldSignature);
            this.accessOwnerClass = accessDeclaration == null ? ""
                    : accessDeclaration.owner();
            this.accessSites.addAll(
                    FieldPathSpec.stringArray(json, "accessSites"));
            this.accessorCallerMethod = optionalString(json,
                    "accessorCallerMethod");
            this.accessorCallUnitIndex = optionalInteger(json,
                    "accessorCallUnitIndex", -1);
            this.accessorDeclaredCallee = optionalString(json,
                    "accessorDeclaredCallee");
            this.accessorImplementationMethod = optionalString(json,
                    "accessorImplementationMethod");
            this.symbolicDemand = optionalString(json, "symbolicDemand");
            this.sourceKind = optionalString(json, "sourceKind");
            this.declaredCallee = optionalString(json, "declaredCallee");
            this.siteId = optionalString(json, "siteId");
            this.eventSeq = optionalLongInteger(json, "eventSeq", -1L);
            this.recordedPrimitiveValue = optionalBool(json, "observed", false)
                    ? optionalString(json, "primitiveValue") : "";
            this.declaredSymbolicRoot = optionalBool(json,
                    InputActionCatalog.DECLARED_SYMBOLIC_ROOT, false);
            this.mintEligible = optionalBool(json, "mintEligible", true);
            this.rootKind = optionalString(json, "rootKind");
            String explicitLeafSignature = firstNonBlank(
                    optionalString(json, "leafFieldSignature"),
                    this.accessFieldSignature);
            this.fieldPaths = new ArrayList<>(
                    FieldPathSpec.paths(json, "fieldPaths"));
            if (this.fieldPaths.isEmpty() && !this.fieldPath.isEmpty()) {
                this.fieldPaths.add(new ArrayList<>(this.fieldPath));
            }
            // A port materialized through several hops carries one declared
            // field per hop.
            List<String> pathDeclarations = FieldPathSpec.stringArray(json,
                    "fieldPathDeclarations");
            if (pathDeclarations.size() == this.fieldPath.size()) {
                for (int hop = 0; hop < pathDeclarations.size(); hop++) {
                    String signature = pathDeclarations.get(hop);
                    DeclaredField declared = FieldPathSpec.declaredField(
                            signature);
                    if (declared == null || !declared.name().equals(
                            this.fieldPath.get(hop))) {
                        continue;
                    }
                    leafFieldSignaturesByPath.putIfAbsent(FieldPathSpec.join(
                            this.fieldPath.subList(0, hop + 1)), signature);
                }
            }
            if (!this.fieldPath.isEmpty()
                    && FieldPathSpec.declaredField(
                    explicitLeafSignature) != null) {
                leafFieldSignaturesByPath.put(FieldPathSpec.join(
                        this.fieldPath), explicitLeafSignature);
            }
            this.symbolicName = optionalString(json, "symbolicName");
        }

        boolean declaresArrayInput(List<String> actualPath) {
            String pathSignature = leafFieldSignaturesByPath.get(
                    FieldPathSpec.join(actualPath));
            DeclaredField declared = FieldPathSpec.declaredField(
                    pathSignature);
            if (declared != null
                    && javaTypeDescriptor(declared.type()).startsWith("[")) {
                return true;
            }
            for (String signature : new String[]{accessFieldSignature,
                    cell}) {
                declared = FieldPathSpec.declaredField(signature);
                if (declared != null
                        && javaTypeDescriptor(declared.type()).startsWith("[")
                        && (actualPath == null || actualPath.isEmpty()
                        || declared.name().equals(actualPath.get(
                        actualPath.size() - 1)))) {
                    return true;
                }
            }
            return javaTypeDescriptor(javaType).startsWith("[");
        }

        boolean declaresReferenceInput() {
            String descriptor = javaTypeDescriptor(javaType);
            return descriptor.startsWith("L") || descriptor.startsWith("[");
        }

        boolean matchesLocal(String actualMethod,
                                     int actualUnitIndex,
                                     String actualLocal) {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && (definitionUnitIndices.isEmpty()
                    || definitionUnitIndices.contains(actualUnitIndex))
                    && local.equals(safe(actualLocal));
        }

        boolean matchesMethodArgument(String actualMethod,
                                              int actualIndex) {
            return "METHOD_ARGUMENT".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && index == actualIndex;
        }

        boolean acceptsOccurrence(int actualOccurrence) {
            return replayOccurrence < 1
                    || replayOccurrence == actualOccurrence;
        }

        boolean acceptsDirectFieldOccurrence(int actualOccurrence) {
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorImplementationMethod.isEmpty();
            return accessorConstrained || acceptsOccurrence(actualOccurrence);
        }

        boolean repeatedPrimitiveAccessor() {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && "CALL_RETURN".equals(location)
                    && JavaPrimitiveBoxing.unboxReturn(cell);
        }

        /**
         * Whether this root is a wall-clock read whose recorded answer is
         * known.
         *
         * <p>{@link ClockRootPhysics} already names the callees whose return
         * is a millisecond clock; it is the same list that anchors each
         * read's window and order in the composed formula, so a root it
         * classifies as a clock here is exactly a root the composer lets
         * move within a skew of what it read.</p>
         */
        boolean declaresWallClockRead() {
            return ClockRootPhysics.clockCallee(declaredCallee)
                    && !recordedPrimitiveValue.isEmpty();
        }

        boolean matchesStaticField(String actualMethod,
                                           int actualUnitIndex,
                                           String signature,
                                           String actualField) {
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "HEAP_OBJECT_FIELD".equals(location))) {
                return false;
            }
            String exactSignature = safe(signature);
            DeclaredField declaration = FieldPathSpec.declaredField(
                    exactSignature);
            if (declaration == null
                    || !declaration.name().equals(safe(actualField))
                    || !accessField.equals(safe(actualField))) {
                return false;
            }
            if (!accessOwnerClass.isEmpty()
                    && !accessOwnerClass.equals(declaration.owner())) {
                return false;
            }
            if (!accessFieldSignature.isEmpty()
                    && !accessFieldSignature.equals(exactSignature)) {
                return false;
            }
            if (accessSites.isEmpty()) {
                return false;
            }
            return accessSites.contains(SiteId.render(actualMethod,
                    actualUnitIndex))
                    && (cell.contains(exactSignature)
                    || accessFieldSignature.equals(exactSignature));
        }

        /**
         * Reconstructs the activation's logical path for an exact getstatic
         * materialization.
         */
        List<String> exactStaticFieldPath(
                String signature, String actualField) {
            String exactSignature = safe(signature);
            DeclaredField declaration = FieldPathSpec.declaredField(
                    exactSignature);
            if (declaration == null
                    || !declaration.name().equals(safe(actualField))
                    || fieldPath.size() != 1
                    || !fieldPath.get(0).equals(actualField)
                    || !accessField.equals(actualField)
                    || !accessFieldSignature.isEmpty()
                    && !accessFieldSignature.equals(exactSignature)
                    || !accessOwnerClass.isEmpty()
                    && !accessOwnerClass.equals(declaration.owner())
                    || !javaType.isEmpty()
                    && !javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(declaration.type()))) {
                return null;
            }
            return Collections.singletonList(actualField);
        }

        boolean matchesField(String actualMethod,
                                     int actualUnitIndex, Object owner,
                                     String signature, String actualField,
                                     Boolean accessorContextOverride) {
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "HEAP_OBJECT_FIELD".equals(location))) {
                return false;
            }
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorImplementationMethod.isEmpty();
            String accessorSiteId = accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex < 0 ? ""
                    : SiteId.render(accessorCallerMethod,
                            accessorCallUnitIndex);
            boolean accessSiteConstrained = !accessSites.isEmpty();
            // Accessor actions name their caller's invoke site in accessSites,
            // while this hook runs at the implementation's field read.
            if (accessSiteConstrained) {
                String constrainedSite = accessorConstrained
                        ? accessorSiteId
                        : SiteId.render(actualMethod, actualUnitIndex);
                if (constrainedSite.isEmpty()
                        || !accessSites.contains(constrainedSite)) {
                    return false;
                }
            }
            Boolean lightweightContext = accessorContextOverride != null
                    ? null : lightweightAccessorContextMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee, owner);
            boolean accessorContextMatches = accessorContextOverride != null
                    ? accessorContextOverride
                    : lightweightContext != null
                    ? lightweightContext
                    : CausynthTraceRecorder.currentCallParentSiteMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee);
            int actualAccessorOccurrence =
                    lightweightAccessorContextOccurrence();
            if (accessorConstrained
                    && (!accessorImplementationMethod.equals(
                    safe(actualMethod))
                    || !accessorContextMatches)) {
                return false;
            }
            if (accessorConstrained
                    && !acceptsOccurrence(
                    actualAccessorOccurrence)) {
                return false;
            }
            if (!accessField.equals(safe(actualField))) {
                return false;
            }
            if (!accessOwnerClass.isEmpty()
                    && !instanceOfName(owner.getClass(), accessOwnerClass)) {
                return false;
            }
            if (accessSiteConstrained
                    && (accessOwnerClass.isEmpty()
                    || accessFieldSignature.isEmpty()
                    || !accessFieldSignature.equals(safe(signature)))) {
                return false;
            }
            // A path rooted at a method return/local may not carry a
            // statically known access owner.
            return !accessOwnerClass.isEmpty()
                    || !safe(signature).isEmpty()
                    && cell.contains(safe(signature));
        }

        Object leafOwner(Object accessOwner) {
            return resolveFieldPathLeafOwner(accessOwner, fieldPath);
        }

        /**
         * Returns the exact declaration of the scalar/array leaf that will
         * actually be symbolized.
         */
        String exactLeafFieldSignature() {
            return exactLeafFieldSignature(fieldPath);
        }

        String exactLeafFieldSignature(List<String> actualPath) {
            String actualLeaf = actualPath == null || actualPath.isEmpty()
                    ? "" : actualPath.get(actualPath.size() - 1);
            String explicit = leafFieldSignaturesByPath.get(
                    FieldPathSpec.join(actualPath));
            DeclaredField declaration = FieldPathSpec.declaredField(
                    explicit);
            if (declaration != null
                    && declaration.name().equals(actualLeaf)) {
                return explicit;
            }
            if (actualPath == null || actualPath.size() != 1) {
                return "";
            }
            String selected = "";
            for (String candidate : new String[]{accessFieldSignature,
                    cell}) {
                declaration = FieldPathSpec.declaredField(candidate);
                if (declaration == null
                        || !declaration.name().equals(actualLeaf)) {
                    continue;
                }
                if (!selected.isEmpty() && !selected.equals(candidate)) {
                    return "";
                }
                selected = candidate;
            }
            return selected;
        }
    }

    /** One scalar assignment returned by a path-flip solve. */
    static final class ModelAssignment {
        final String key;
        final String engineSymbol;
        final String inputSymbol;
        final String valueType;
        final String value;
        final String configuredSourcePhaseId;
        final String configuredSourceId;
        final String configuredSourceFieldSignature;
        final boolean modelIsNull;
        final boolean containerTargetPresent;
        final String containerShape;
        final String containerSelectorKind;
        final String containerProjection;
        final int containerIndex;
        final int containerAccessOrdinal;
        final String containerKeyJavaType;
        final String containerKeyValue;
        final List<String> path = new ArrayList<>();

        ModelAssignment(JsonObject json) {
            this.engineSymbol = firstNonBlank(optionalString(json, "engineSymbol"));
            this.inputSymbol = optionalString(json, "inputSymbol");
            this.valueType = optionalString(json, "valueType");
            this.value = optionalString(json, "value");
            this.configuredSourcePhaseId = optionalString(json,
                    "configuredSourcePhaseId");
            this.configuredSourceId = optionalString(json,
                    "configuredSourceId");
            this.configuredSourceFieldSignature = optionalString(json,
                    "configuredSourceFieldSignature");
            this.modelIsNull = optionalBool(json, "modelIsNull", false);
            JsonElement encodedContainerTarget = json.get("containerTarget");
            this.containerTargetPresent = encodedContainerTarget != null;
            JsonObject containerTarget = object(json, "containerTarget");
            this.containerShape = optionalString(containerTarget, "shape");
            this.containerSelectorKind = optionalString(containerTarget,
                    "selectorKind");
            this.containerProjection = optionalString(containerTarget,
                    "projection");
            this.containerIndex = optionalInteger(containerTarget, "index", -1);
            this.containerAccessOrdinal = optionalInteger(containerTarget,
                    "accessOrdinal", -1);
            this.containerKeyJavaType = optionalString(containerTarget,
                    "keyJavaType");
            this.containerKeyValue = optionalString(containerTarget, "keyValue");
            for (JsonElement element : array(json,
                    "materializationPath")) {
                if (element.isJsonPrimitive()) {
                    path.add(element.getAsString());
                }
            }
            this.key = firstNonBlank(optionalString(json, "modelAssignmentKey"),
                    engineSymbol);
        }

        boolean configuredSourceAssignment() {
            return !configuredSourcePhaseId.isEmpty()
                    || !configuredSourceId.isEmpty()
                    || !configuredSourceFieldSignature.isEmpty();
        }

        boolean matchesConfiguredSource(String sourcePhaseId,
                                                 String sourceId,
                                                 String fieldSignature) {
            return configuredSourcePhaseId.equals(safe(sourcePhaseId))
                    && configuredSourceId.equals(safe(sourceId))
                    && configuredSourceFieldSignature.equals(
                            safe(fieldSignature))
                    && inputSymbol.equals("SOURCE_PHASE:"
                    + safe(sourcePhaseId));
        }

        boolean hasContainerTarget() {
            return containerTargetPresent;
        }

        boolean iterationTarget() {
            return "ASSOCIATIVE".equals(containerShape)
                    && "ITERATION_INDEX".equals(containerSelectorKind);
        }

        boolean dynamicAssociativeTarget() {
            return "ASSOCIATIVE".equals(containerShape)
                    && "ACCESS_ORDINAL".equals(containerSelectorKind)
                    && containerAccessOrdinal >= 1;
        }

        boolean validContainerTarget() {
            if ("INDEXED".equals(containerShape)) {
                return containerIndex >= 0;
            }
            if (iterationTarget()) {
                return containerIndex >= 0
                        && ("KEY".equals(containerProjection)
                        || "VALUE".equals(containerProjection));
            }
            if (dynamicAssociativeTarget()) {
                return true;
            }
            if (!"ASSOCIATIVE".equals(containerShape)
                    || containerKeyJavaType.isEmpty()
                    || containerKeyValue.isEmpty()) {
                return false;
            }
            return true;
        }

        boolean matches(SymbolizeAction action,
                                List<String> actualPath) {
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) {
                return actualPath == null || actualPath.isEmpty()
                        || action.fieldPath.equals(actualPath);
            }
            return actualPath != null && path.equals(actualPath);
        }

        boolean targetsFieldAccess(SymbolizeAction action) {
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) return true;
            if (action.fieldPath.isEmpty()
                    || path.size() < action.fieldPath.size()) return false;
            for (int index = 0; index < action.fieldPath.size(); index++) {
                if (!path.get(index).equals(action.fieldPath.get(index))) {
                    return false;
                }
            }
            return true;
        }

        Object referenceValue(Object concrete) {
            if ("STRING".equalsIgnoreCase(valueType)) {
                return unquoteSmtString(value);
            }
            if ("NULL".equalsIgnoreCase(valueType)
                    || "null".equalsIgnoreCase(value)) return null;
            if ("UNCHANGED".equalsIgnoreCase(valueType)) return concrete;
            return UnsupportedReplayValue.INSTANCE;
        }

    }

    /** One solver-selected scalar arm for one exact shared-field read. */
    static final class GuardedReadAssignment {
        static final String KIND = "PRIMITIVE_FIELD_READ";
        static final String AUTHORITY =
                "SOLVER_SELECTED_GUARDED_READ_ARM_V1";

        final String readIdentity;
        final String candidateIdentity;
        final String readerTaskId;
        final String readerOccurrenceId;
        final String consumerSiteId;
        final int consumerSiteOccurrence;
        final String declaringClass;
        final String fieldName;
        final String descriptor;
        final long valueBits;

        GuardedReadAssignment(JsonObject json, String taskOccurrenceId) {
            if (optionalInteger(json, "schemaVersion", 0) != 1
                    || !KIND.equals(optionalString(json, "kind"))
                    || !AUTHORITY.equals(optionalString(json, "authority"))) {
                throw new IllegalArgumentException(
                        "unsupported guarded read assignment schema");
            }
            this.readIdentity = optionalString(json, "readIdentity");
            this.candidateIdentity = optionalString(json, "candidateIdentity");
            this.readerTaskId = optionalString(json, "readerTaskId");
            this.readerOccurrenceId = OccurrenceId.parse(
                    optionalString(json, "readerOccurrenceId")).planned();
            this.consumerSiteId = optionalString(json, "consumerSiteId");
            this.consumerSiteOccurrence = optionalInteger(json,
                    "consumerSiteOccurrence", 0);
            this.declaringClass = optionalString(json, "declaringClass");
            this.fieldName = optionalString(json, "fieldName");
            this.descriptor = javaTypeDescriptor(optionalString(json, "descriptor"));
            String valueType = optionalString(json, "valueType");
            String value = optionalString(json, "value");
            String plannedTaskOccurrence = OccurrenceId.parse(
                    taskOccurrenceId).planned();
            if (readIdentity.isEmpty() || candidateIdentity.isEmpty()
                    || readerTaskId.isEmpty() || readerOccurrenceId.isEmpty()
                    || !readerOccurrenceId.equals(plannedTaskOccurrence)
                    || consumerSiteId.isEmpty() || consumerSiteOccurrence < 1
                    || declaringClass.isEmpty() || fieldName.isEmpty()) {
                throw new IllegalArgumentException(
                        "incomplete guarded read assignment " + readIdentity);
            }
            this.valueBits = primitiveValueBits(descriptor, valueType, value);
        }

        static long primitiveValueBits(String descriptor,
                                               String valueType,
                                               String value) {
            if ("Z".equals(descriptor)) {
                if (!"BOOL".equals(valueType)
                        || !("true".equals(value) || "false".equals(value))) {
                    throw new IllegalArgumentException(
                            "boolean guarded read has malformed value " + value);
                }
                return "true".equals(value) ? 1L : 0L;
            }
            if (!("B".equals(descriptor) || "C".equals(descriptor)
                    || "S".equals(descriptor) || "I".equals(descriptor)
                    || "J".equals(descriptor))
                    || !"INT".equals(valueType)) {
                throw new IllegalArgumentException(
                        "unsupported guarded read descriptor/type "
                                + descriptor + "/" + valueType);
            }
            final BigInteger parsed;
            try {
                parsed = new BigInteger(value);
            } catch (NumberFormatException malformed) {
                throw new IllegalArgumentException(
                        "guarded read has malformed integer value " + value,
                        malformed);
            }
            BigInteger[] range = integralRange(descriptor);
            if (parsed.compareTo(range[0]) < 0
                    || parsed.compareTo(range[1]) > 0) {
                throw new IllegalArgumentException(
                        "guarded read value is outside " + descriptor
                                + " range: " + value);
            }
            return parsed.longValue();
        }

        boolean matches(ConsumerAccessAnchor consumer,
                                DeclaredField field) {
            return consumer != null && field != null
                    && consumerSiteId.equals(consumer.siteId)
                    && consumerSiteOccurrence == consumer.occurrence
                    && declaringClass.equals(field.owner())
                    && fieldName.equals(field.name())
                    && descriptor.equals(javaTypeDescriptor(field.type()));
        }
    }




}
