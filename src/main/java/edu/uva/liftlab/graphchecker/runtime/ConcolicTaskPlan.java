package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ConsumerAccessAnchor;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.GuardedReadAssignment;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ModelAssignment;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.RootHookGroup;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.SymbolizeAction;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.DEFAULT_EXECUTOR_THREAD_NAME;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.DEFAULT_OBJECT_IDENTITY_THREAD_NAME;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ROOT_ARGUMENT_PREDICATE_KIND;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.SKIP_ANCHOR_SOURCE_NEVER_EXISTED;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.SKIP_OCCURRENCE_ANCHOR_UNMATCHED;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.enclosingLoopRootAdmits;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.outgoingProducerMayDeferMissingContext;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.registerRunTotalsHook;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.sameHookIdentity;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.SKIP_ROOT_NEVER_EXECUTED;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.writeSkipped;

/** The bounded campaign this JVM executes. */
final class ConcolicTaskPlan {
    private static final Object LOCK = new Object();
    private static volatile ConcolicTaskPlan plan;

    /** The plan this JVM executes, loaded on first use. */
    static ConcolicTaskPlan configuration() {
        ConcolicTaskPlan current = plan;
        if (current != null) {
            return current;
        }
        synchronized (LOCK) {
            if (plan == null) {
                plan = ConcolicTaskPlan.load();
            }
            return plan;
        }
    }

    final Path resultFile;
    final List<RuntimeTask> tasks;
    /**
     * Tasks whose occurrence is running as a candidate right now, and
     * tasks whose candidate confirmed its anchor and published.
     *
     * <p>Together they turn admission into what README {@code OCC-1} asks
     * for: every compatible root invocation is a candidate for the
     * address, one at a time, until one of them is the addressed
     * occurrence.</p>
     */
    final boolean[] candidateLive;
    final boolean[] occurrenceClaimed;
    /** Next observed physical entry in each planner-authored scope. */
    final Map<String, Integer> invocationOrdinals =
            new LinkedHashMap<>();
    /** Halt-status contribution of each task that has settled. */
    final Map<String, Integer> settled = new LinkedHashMap<>();
    boolean unansweredAddressesPublished;

    ConcolicTaskPlan(Path resultFile, List<RuntimeTask> tasks) {
        this.resultFile = resultFile;
        this.tasks = Collections.unmodifiableList(tasks);
        this.candidateLive = new boolean[tasks.size()];
        this.occurrenceClaimed = new boolean[tasks.size()];
        indexDeferredOutgoingSourceAnchors(tasks);
    }

    /**
     * Admits an OUT site as source evidence only when the frozen runtime
     * edges give that exact root/request/port scope one producer source.
     */
    static void indexDeferredOutgoingSourceAnchors(
            List<RuntimeTask> tasks) {
        Map<String, Set<String>> sourcesByScope = new LinkedHashMap<>();
        for (RuntimeTask task : tasks) {
            // Include even malformed/unbound declarations in the
            // uniqueness denominator; they must make admission less
            // permissive, never disappear from the proof.
            for (String portId : task.declaredOutgoingPorts()) {
                sourcesByScope.computeIfAbsent(
                        task.outgoingSourceScope(portId),
                        ignored -> new LinkedHashSet<>()).add(
                        task.sourceKey);
            }
        }
        for (RuntimeTask task : tasks) {
            Set<String> candidates =
                    task.exactOutgoingSourceCandidatePorts;
            if (candidates.isEmpty()
                    || !candidates.equals(task.declaredOutgoingPorts())
                    || !candidates.equals(
                    task.exportConsumerOccurrenceByPort.keySet())) {
                continue;
            }
            boolean unique = true;
            for (String portId : candidates) {
                Set<String> sources = sourcesByScope.get(
                        task.outgoingSourceScope(portId));
                if (sources == null || sources.size() != 1
                        || !sources.contains(task.sourceKey)) {
                    unique = false;
                    break;
                }
            }
            if (unique) {
                task.deferredOutgoingSourcePorts.addAll(candidates);
            }
        }
    }

    /**
     * Releases the address of a candidate that ended without being the
     * occurrence, so the next compatible invocation may try for it.
     */
    synchronized void releaseCandidate(RuntimeTask task) {
        int index = tasks.indexOf(task);
        if (index >= 0) candidateLive[index] = false;
    }

    /**
     * States every selected address this run could not answer with exactly
     * one occurrence, once each, now that the run is over and both "never
     * registered in this run" and "several activations fit" are decidable
     * rather than snapshots the same run can contradict.
     *
     * <p>An address nothing answered is a coverage statement about the
     * replay; an address several activations answered is README {@code
     * OCC-1}'s ambiguity, a statement about the address itself.</p>
     */
    synchronized void publishUnansweredAddresses() {
        if (unansweredAddressesPublished) return;
        unansweredAddressesPublished = true;
        for (int index = 0; index < tasks.size(); index++) {
            RuntimeTask task = tasks.get(index);
            // An address that published at least one occurrence has been
            // answered for end-of-run diagnostics. Goal completion owns
            // the separate decision to admit another activation.
            if (occurrenceClaimed[index]) continue;
            if (task.unaddressedCandidates == 0) {
                // Nothing compatible ran at all -- not one activation the
                // address could have been compared against.  That is a
                // different statement from "several ran and none matched",
                // and it used to be no statement: the task published neither
                // an activation nor a skip, and the importer met silence.
                writeSkipped(task, SKIP_ROOT_NEVER_EXECUTED,
                        "the planned root did not execute in this replay: no"
                                + " compatible activation was offered for "
                                + task.occurrenceId, null);
                continue;
            }
            writeSkipped(task, task.rootContextSelector
                            .anchorSourceNeverExisted()
                            ? SKIP_ANCHOR_SOURCE_NEVER_EXISTED
                            : SKIP_OCCURRENCE_ANCHOR_UNMATCHED,
                    task.unansweredAddress(), null);
        }
    }

    /** Marks durable evidence without clearing a newer live candidate. */
    synchronized void markOccurrenceClaimed(RuntimeTask task) {
        int index = tasks.indexOf(task);
        if (index >= 0) occurrenceClaimed[index] = true;
    }

    /** The campaign task with this id, or {@code null}. */
    RuntimeTask taskById(String taskId) {
        if (taskId == null || taskId.isEmpty()) return null;
        for (RuntimeTask task : tasks) {
            if (taskId.equals(task.taskId)) return task;
        }
        return null;
    }

    /**
     * Resolves an occurrence-specific instrumentation hook to the stable
     * region entry shared by every sibling hook at that Java method.
     */
    synchronized RootHookGroup rootHookGroup(
            String instrumentationSelector, String rootMethod) {
        RuntimeTask selected = null;
        for (RuntimeTask task : tasks) {
            if (!task.instrumentationSelector.equals(
                    safe(instrumentationSelector))
                    || !sameHookIdentity(task.rootMethod, rootMethod)) {
                continue;
            }
            if (selected != null && !selected.rootHookGroupKey().equals(
                    task.rootHookGroupKey())) {
                throw new IllegalStateException(
                        "instrumentation selector addresses multiple "
                                + "root hook groups: "
                                + safe(instrumentationSelector));
            }
            selected = task;
        }
        if (selected == null) {
            return new RootHookGroup("UNPLANNED\n"
                    + safe(instrumentationSelector) + "\n"
                    + safe(rootMethod), 1);
        }
        String key = selected.rootHookGroupKey();
        int hooks = 0;
        for (RuntimeTask task : tasks) {
            if (key.equals(task.rootHookGroupKey())) hooks++;
        }
        return new RootHookGroup(key, hooks);
    }

    /** Resolves one lightweight outer hook shared by loop-body tasks. */
    synchronized RootHookGroup loopRootHookGroup(
            String instrumentationSelector, String rootMethod) {
        RuntimeTask selected = null;
        for (RuntimeTask task : tasks) {
            if (!task.loopBodyRoot
                    || !task.instrumentationSelector.equals(
                    safe(instrumentationSelector))
                    || !sameHookIdentity(task.rootMethod, rootMethod)) {
                continue;
            }
            selected = task;
            break;
        }
        if (selected == null) {
            return new RootHookGroup("UNPLANNED_LOOP_ROOT\n"
                    + safe(rootMethod), 1);
        }
        String key = selected.loopRootHookGroupKey();
        int hooks = 0;
        for (RuntimeTask task : tasks) {
            if (task.loopBodyRoot
                    && key.equals(task.loopRootHookGroupKey())) hooks++;
        }
        return new RootHookGroup(key, hooks);
    }

    /**
     * Counts one real enclosing method entry and freezes which loop task
     * owns all body iterations executed by that invocation.
     */
    synchronized Set<String> addressLoopRootInvocation(
            String loopRootHookGroupKey, String rootMethod,
            Object receiver, Object[] rootArguments) {
        String threadName = Thread.currentThread().getName();
        SourceRef registeredReceiverSource =
                RuntimeTraceContext.sourceFor(receiver);
        // Where this activation ran, by the one function the recorder
        // stamped it with and the planner counted it by.
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        Map<String, Integer> actualOrdinalByScope =
                new LinkedHashMap<>();
        for (RuntimeTask task : tasks) {
            if (!task.loopBodyRoot
                    || !task.loopRootHookGroupKey().equals(
                    safe(loopRootHookGroupKey))
                    || !compatibleRoot(task.rootMethod, rootMethod,
                    task.rootContextSelector,
                    task.enclosingRootArgumentSelector,
                    receiver, rootArguments, threadName)) {
                continue;
            }
            // Outside the recording window there is nothing to count.  A
            // workload starts its cluster, names its sources, then does the
            // thing being recorded; whatever the process did before the
            // first registration the recording never saw, so the plan
            // counted none of it.  Counting it here numbers a different
            // population than the plan numbered -- on hdfs-17960 the
            // process's first saveNamespace, 38 seconds before the workload
            // begins, took ordinal 1 and pushed the checkpoint activation
            // the plan means to 2.
            if (!RuntimeTraceContext.recordingWindowOpen()) continue;
            // Counted before anything else may refuse it: the planner
            // counted every observed activation of this region, so a
            // candidate the replay declines for another reason still
            // occupies the ordinal the recording gave it.  Filtering first
            // would renumber the activations after it.
            String scope = task.invocationCounterKey(countedLifecycle(
                    task, activationSource));
            countInvocation(scope, actualOrdinalByScope);
            // An activation this run attributed nowhere is counted in the
            // unregistered population, where the planner counts it.  In the
            // planned one it takes no k at all until it is confirmed: it
            // only reads what the next confirmed k would be, and the close
            // takes it if the frame arm names the planned node.  Taking it
            // at entry and giving it back needed the k to still be the last
            // one handed out, and on hdfs-17899 bug2 it was not -- the real
            // heartbeat convert had already been numbered against it and
            // came out "activation 2, not 1".
            if (unattributed(activationSource)) {
                String planned = task.invocationCounterKey();
                if (!actualOrdinalByScope.containsKey(planned)) {
                    actualOrdinalByScope.put(planned,
                            invocationOrdinals.getOrDefault(planned, 0) + 1);
                }
            }
            String sourceMismatch = sourceAdmissionMismatch(task,
                    registeredReceiverSource, context);
            if (!sourceMismatch.isEmpty()) {
                task.noteUnaddressedCandidate(sourceMismatch);
                continue;
            }
            // The request a root entered is recorded, never a refusal: an
            // occurrence is (node, epoch, region, k-th activation), and the
            // exchange that happened to be open around it is not part of
            // that identity.  Vetoing on it refused a flip replay whose
            // activation is the seed's -- same node, same region, same
            // ordinal -- because the workload reached it under a different
            // request the second time.
            String enteredUnder = requestMismatch(task,
                    registeredReceiverSource, context);
            if (!enteredUnder.isEmpty()) {
                task.noteRequestContext(enteredUnder);
            }
            if (mayDeferMissingContextToOutgoingAnchor(task,
                    registeredReceiverSource, context)) {
                continue;
            }
        }
        Set<String> admitted = new LinkedHashSet<>();
        // An activation the recording never saw is not a candidate here
        // either.  The counting pass above skipped it, so looking its
        // ordinal up would answer null and the run would report "invocation
        // null instead of 1" -- a comparison against an ordinal nobody
        // assigned, rather than the plain fact that this activation is
        // outside the window.
        if (!RuntimeTraceContext.recordingWindowOpen()) {
            return admitted;
        }
        for (RuntimeTask task : tasks) {
            if (!task.loopBodyRoot
                    || !task.loopRootHookGroupKey().equals(
                    safe(loopRootHookGroupKey))
                    || !compatibleRoot(task.rootMethod, rootMethod,
                    task.rootContextSelector,
                    task.enclosingRootArgumentSelector,
                    receiver, rootArguments, threadName)
                    || !sourceAdmissionMismatch(task,
                    registeredReceiverSource,
                    context).isEmpty()) {
                continue;
            }
            OccurrenceAddress observed = task.observedAddress(
                    countedLifecycle(task, activationSource),
                    actualOrdinalByScope);
            boolean exactOutgoingAddress =
                    mayDeferMissingContextToOutgoingAnchor(task,
                            registeredReceiverSource, context);
            if (admitsProvisionally(task, activationSource, observed,
                    exactOutgoingAddress, actualOrdinalByScope)) {
                admitted.add(task.taskId);
                continue;
            }
            if (!task.acceptsRootInvocation(observed,
                    exactOutgoingAddress)) {
                task.noteUnaddressedCandidate("matching enclosing root: "
                        + task.address.difference(observed)
                        + attribution(activationSource));
                continue;
            }
            admitted.add(task.taskId);
        }
        return admitted;
    }

    /** Claims at most one open task for this root invocation. */
    synchronized RuntimeTask select(String rootHookGroupKey,
                                            String rootMethod,
                                            Object receiver,
                                            Object[] rootArguments) {
        String threadName = Thread.currentThread().getName();
        // A short-lived Runnable need not be registered as an alias
        // itself: an exact inherited async/request/RPC context can still
        // attribute its entry.
        SourceRef registeredReceiverSource =
                RuntimeTraceContext.sourceFor(receiver);
        // Where this activation ran, by the one function the recorder
        // stamped it with and the planner counted it by.
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        Map<String, Integer> actualOrdinalByScope =
                new LinkedHashMap<>();

        // Count this physical entry once in every matching stable scope.
        // This pass deliberately ignores task completion and candidate
        // ownership: later planned ordinals must still see entries that
        // an earlier task already consumed.
        for (RuntimeTask task : tasks) {
            if (task.loopBodyRoot
                    || !task.rootHookGroupKey().equals(
                    safe(rootHookGroupKey))
                    || !compatibleRoot(task.rootMethod, rootMethod,
                    task.rootContextSelector, task.rootArgumentSelector,
                    receiver, rootArguments, threadName)) {
                continue;
            }
            // Outside the recording window there is nothing to count.  A
            // workload starts its cluster, names its sources, then does the
            // thing being recorded; whatever the process did before the
            // first registration the recording never saw, so the plan
            // counted none of it.  Counting it here numbers a different
            // population than the plan numbered -- on hdfs-17960 the
            // process's first saveNamespace, 38 seconds before the workload
            // begins, took ordinal 1 and pushed the checkpoint activation
            // the plan means to 2.
            if (!RuntimeTraceContext.recordingWindowOpen()) continue;
            // Counted before anything else may refuse it: the planner
            // counted every observed activation of this region, so a
            // candidate the replay declines for another reason still
            // occupies the ordinal the recording gave it.  Filtering first
            // would renumber the activations after it.
            String scope = task.invocationCounterKey(countedLifecycle(
                    task, activationSource));
            countInvocation(scope, actualOrdinalByScope);
            // An activation this run attributed nowhere is counted in the
            // unregistered population, where the planner counts it.  In the
            // planned one it takes no k at all until it is confirmed: it
            // only reads what the next confirmed k would be, and the close
            // takes it if the frame arm names the planned node.  Taking it
            // at entry and giving it back needed the k to still be the last
            // one handed out, and on hdfs-17899 bug2 it was not -- the real
            // heartbeat convert had already been numbered against it and
            // came out "activation 2, not 1".
            if (unattributed(activationSource)) {
                String planned = task.invocationCounterKey();
                if (!actualOrdinalByScope.containsKey(planned)) {
                    actualOrdinalByScope.put(planned,
                            invocationOrdinals.getOrDefault(planned, 0) + 1);
                }
            }
            String sourceMismatch = sourceAdmissionMismatch(task,
                    registeredReceiverSource, context);
            if (!sourceMismatch.isEmpty()) {
                task.noteUnaddressedCandidate(sourceMismatch);
                continue;
            }
            // The request a root entered is recorded, never a refusal: an
            // occurrence is (node, epoch, region, k-th activation), and the
            // exchange that happened to be open around it is not part of
            // that identity.  Vetoing on it refused a flip replay whose
            // activation is the seed's -- same node, same region, same
            // ordinal -- because the workload reached it under a different
            // request the second time.
            String enteredUnder = requestMismatch(task,
                    registeredReceiverSource, context);
            if (!enteredUnder.isEmpty()) {
                task.noteRequestContext(enteredUnder);
            }
            if (mayDeferMissingContextToOutgoingAnchor(task,
                    registeredReceiverSource, context)) {
                continue;
            }
        }

        // Same rule as the counting pass: outside the recording window
        // there is no candidate to select.
        if (!RuntimeTraceContext.recordingWindowOpen()) return null;
        for (int index = 0; index < tasks.size(); index++) {
            RuntimeTask task = tasks.get(index);
            if (!task.rootHookGroupKey().equals(
                    safe(rootHookGroupKey))) continue;
            if (task.blocksAdmissionAfterCompletedGoal()) continue;
            if (task.loopBodyRoot) {
                if (!enclosingLoopRootAdmits(task)
                        || candidateLive[index]) {
                    continue;
                }
                candidateLive[index] = true;
                return task;
            }
            if (!compatibleRoot(task.rootMethod, rootMethod,
                    task.rootContextSelector, task.rootArgumentSelector,
                    receiver, rootArguments, threadName)) {
                continue;
            }
            if (!sourceAdmissionMismatch(task, registeredReceiverSource,
                    context).isEmpty()) continue;
            OccurrenceAddress observed = task.observedAddress(
                    countedLifecycle(task, activationSource),
                    actualOrdinalByScope);
            boolean exactOutgoingAddress =
                    mayDeferMissingContextToOutgoingAnchor(task,
                            registeredReceiverSource, context);
            boolean provisional = admitsProvisionally(task, activationSource,
                    observed, exactOutgoingAddress, actualOrdinalByScope);
            if (!provisional && !task.acceptsRootInvocation(observed,
                    exactOutgoingAddress)) {
                // Said out loud, as the loop-body path already says it.  A
                // non-loop root that ran and was refused on its address was
                // refused in silence, and the end of the run then reported
                // the task as ROOT_NEVER_EXECUTED -- "no compatible
                // activation was offered" -- which is a statement about the
                // region never running.  On hdfs-17899 bug2 that is
                // REGION.763d087e on target-dn: activations of
                // Client$Connection.sendRpcRequest were offered and refused
                // on the ordinal, and the row said the root never executed.
                task.noteUnaddressedCandidate("matching root: "
                        + task.address.difference(observed)
                        + attribution(activationSource));
                continue;
            }
            if (candidateLive[index]) continue;
            candidateLive[index] = true;
            return task;
        }
        return null;
    }

    /**
     * How the request this root entered differs from the planned one, or "".
     *
     * <p>Information, not admission.  The request was the stitcher's way of
     * addressing an occurrence, because it merged replays and needed the RPC
     * exchange to tell two runs of one region apart.  An occurrence is
     * (node, epoch, region, k-th activation); which exchange happened to be
     * open around it says where it was reached from, not which occurrence it
     * is.</p>
     */
    static String requestMismatch(
            RuntimeTask task, SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        return task.rootContextSelector.reachedUnder
                .requestDifference(context);
    }

    /** Entry admission may defer only missing producer context to OUT. */
    static String sourceAdmissionMismatch(
            RuntimeTask task, SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        String mismatch = sourceMismatch(task, registeredReceiverSource,
                context);
        return mismatch.isEmpty()
                || mayDeferMissingContextToOutgoingAnchor(
                task, registeredReceiverSource, context) ? "" : mismatch;
    }

    static boolean mayDeferMissingContextToOutgoingAnchor(
            RuntimeTask task, SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        RootContextSelector selector = task.rootContextSelector;
        return outgoingProducerMayDeferMissingContext(
                !task.deferredOutgoingSourcePorts.isEmpty(),
                registeredReceiverSource, context.source, task.sourceKey,
                selector.reachedUnder.requestKey,
                selector.reachedUnder.requestApi,
                context.requestKey, context.requestApi);
    }

    /**
     * Why this run's evidence says the activation is another lifecycle of
     * the planned node, or {@code ""}.
     *
     * <p>An occurrence is (node, epoch, region, k-th activation).  Nothing
     * compared the <em>epoch</em>: source evidence was matched with {@code
     * sameSourceIdentity}, which strips {@code #epoch<n>} deliberately, so an
     * activation of {@code nn0#epoch0} answered an address on
     * {@code nn0#epoch1}.  On hdfs-17960 the flip replay threw inside the
     * workload before it restarted the NameNode, so every activation it
     * offered was epoch 0 -- and the flip's model, {@code root=false}, was
     * written at the mint the recording made <em>before</em> the restart
     * instead of at the epoch-1 mint the plan addresses.  The recorded
     * execution was rewritten at a point the solver said nothing about.</p>
     *
     * <p>One fact refuses: evidence attributing this activation to the same
     * node at a <em>different</em> epoch.  A workload declares its epochs
     * literally ({@code registerSource(..., 0)} at start,
     * {@code restartSource(..., 1)} across a restart), so the label means the
     * same lifecycle in every run of it and an activation that ran under
     * another one is another occurrence.  An activation nothing attributed
     * anywhere is still the occurrence, as everywhere else here: absence of
     * evidence is not evidence of another epoch.</p>
     *
     * <p>"This run never registered the planned epoch" was a second refusal
     * here, and it was wrong in a way only a whole run shows.  It is a fact
     * about a <em>moment</em> -- the epoch has not been registered YET -- and
     * it was being read as a verdict about the run.  On hdfs-17960 the two
     * activations of the {@code deleteSnapshot} region that precede the
     * NameNode restart were refused by it, permanently, and the run then
     * registered {@code nn0#epoch1} thirty lines of workload later and
     * published epoch-1 occurrences for five other regions.  Both statements
     * were in one seed replay's output: five regions answered at epoch 1, and
     * eight tasks told that the run "never registered" it.  The activations
     * that arm refused are refused anyway, by the arm that remains and for
     * the reason that is actually true of them -- they ran at epoch 0 -- and
     * the ones that come after the restart are now free to answer.</p>
     */
    static String lifecycleMismatch(String plannedSourceKey,
                                    Collection<String> attributed) {
        String planned = safe(plannedSourceKey);
        if (!RuntimeTraceContext.declaresEpoch(planned)) return "";
        if (attributed == null || attributed.contains(planned)) return "";
        for (String observed : attributed) {
            if (observed != null && !observed.equals(planned)
                    && RuntimeTraceContext.sameSourceIdentity(planned,
                    observed)) {
                return "matching root ran at " + observed + ", not at "
                        + planned;
            }
        }
        return "";
    }

    /**
     * The node and epoch this activation is counted in.
     *
     * <p>The one the run attributed to it -- {@link
     * RuntimeTraceContext#activationSource}, the same function that stamped
     * the recording's {@code METHOD_ENTER} and that the planner counted the
     * recorded population by -- and the planned one only when the run
     * attributed it nowhere.  Falling back to the plan then keeps an
     * unattributed activation counting exactly where it counted before:
     * absence of evidence moves nothing, and a replay that reconstructs a
     * receiver without repeating its alias registration still answers.</p>
     *
     * <p>The fallback used to be wider: it also swallowed every activation
     * the run attributed to <em>another node</em>, because an ambient
     * context that did not already name the planned node was read as
     * provenance.  One JVM running nn0, source-dn and target-dn then counted
     * all three nodes' activations of one region in each planned node's
     * bucket.  On hdfs-17899 bug3 that is REGION.16ba41cf's planned first
     * activation on target-dn answered by "invocation 2 instead of 1", and
     * REGION.763d087e's one target-dn activation published as source-dn's
     * because it was ordinal 1 in source-dn's bucket too.</p>
     *
     * <p>Read at the moment the activation starts, from the same registry
     * {@link #lifecycleMismatch} and the configured-source mint read, so the
     * three cannot disagree about which lifecycle an activation belongs
     * to.</p>
     */
    static String countedLifecycle(RuntimeTask task,
                                   SourceRef activationSource) {
        String planned = safe(task.sourceKey);
        if (!RuntimeTraceContext.declaresEpoch(planned)) return planned;
        // Never the planned node.  RuntimeTraceContext.activationSource is
        // the planner's own rule and its last arm is the unregistered
        // source, so an activation nothing attributed counts in the
        // population the planner counted it in.  It used to fall back to the
        // plan's own key, and that is what let hdfs-17899 bug2's
        // pre-registration heartbeats -- the DataNode's own loop runs before
        // the workload registers dn.getDatanodeId(), so those activations
        // carry no node at all -- take target-dn's k=1 ahead of the
        // heartbeat the plan addresses.
        return activationSource == null
                ? RuntimeTraceContext.UNREGISTERED_SOURCE.key()
                : activationSource.key();
    }

    /**
     * What this run attributed the refused activation to, for the note.
     *
     * <p>An ordinal refusal says "occurrence is activation 2, not 1" and
     * that reads the same whether the activation ran on the planned node and
     * was genuinely its second, or ran on no node this run could name and
     * was counted in the planned bucket by the fallback.  Those are two
     * different findings with two different owners -- on hdfs-17899 bug2 the
     * DataNode's heartbeat runs on its own BPServiceActor thread, whose
     * stamp the workload opens with {@code beginRequestIfRegistered}, so
     * whether a given heartbeat carries the node at all depends on when the
     * workload registered it -- and the row could not tell them apart.</p>
     */
    static String attribution(SourceRef activationSource) {
        if (activationSource == null
                || RuntimeTraceContext.UNREGISTERED_SOURCE.key()
                .equals(activationSource.key())) {
            return " (this run attributed the activation to no node, so it"
                    + " counts in the unregistered source)";
        }
        return " (attributed to " + activationSource.key() + ")";
    }

    /**
     * Whether an activation this run has attributed nowhere may answer the
     * planned address for now, to be decided at close.
     *
     * <p>The planner attributes an activation by its own stamp, else the
     * unique stamp among its own FRAMES, else the unregistered source -- and
     * the frame arm is knowable only once the activation has run its frames.
     * At a root entry the replay has none of them yet, so an activation
     * whose frames will name the planned node is indistinguishable from one
     * that belongs to nobody.  Refusing both at entry withheld the first
     * kind: on hdfs-17899 bug2 that is twenty-five activations of
     * REGION.1f6914ec refused with "ran on workload/unregistered, not sps".
     * So it is admitted against the planned address, provisionally, and
     * {@code rootContextSelector.unconfirmed} -- which IS the frame arm,
     * over the frames the activation actually ran -- decides at close.  A
     * refusal there gives the ordinal back.</p>
     */
    private synchronized boolean admitsProvisionally(
            RuntimeTask task, SourceRef activationSource,
            OccurrenceAddress observed, boolean exactOutgoingAddress,
            Map<String, Integer> actualOrdinalByScope) {
        if (!unattributed(activationSource)
                || task.acceptsRootInvocation(observed,
                exactOutgoingAddress)) {
            return false;
        }
        String scope = task.invocationCounterKey();
        OccurrenceAddress planned = task.observedAddress(task.sourceKey,
                actualOrdinalByScope);
        if (!task.acceptsRootInvocation(planned, exactOutgoingAddress)) {
            return false;
        }
        task.markProvisionalOrdinal(scope, planned.ordinal());
        return true;
    }

    private synchronized void countInvocation(
            String scope, Map<String, Integer> actualOrdinalByScope) {
        if (actualOrdinalByScope.containsKey(scope)) return;
        int ordinal = invocationOrdinals.getOrDefault(scope, 0) + 1;
        invocationOrdinals.put(scope, ordinal);
        actualOrdinalByScope.put(scope, ordinal);
    }

    /** Whether this run attributed the activation to no node at all. */
    static boolean unattributed(SourceRef activationSource) {
        return activationSource == null
                || RuntimeTraceContext.UNREGISTERED_SOURCE.key()
                .equals(activationSource.key());
    }

    /**
     * Gives back an ordinal a provisional admission took.
     *
     * <p>Nothing to give back: a provisional admission never took the k,
     * it only read what the next confirmed one would be.</p>
     */
    synchronized void releaseProvisionalOrdinal(RuntimeTask task) {
        if (task != null) task.clearProvisionalOrdinal();
    }

    /**
     * Takes the k a provisional admission was reading, now that the frame
     * arm has confirmed it.
     *
     * <p>Numbering by confirmed order: a provisional activation holds no k
     * while it runs, so an activation the close refuses never displaces the
     * one that follows it.  Only here does the bucket advance.</p>
     */
    synchronized void confirmProvisionalOrdinal(RuntimeTask task) {
        if (task == null || task.provisionalOrdinal <= 0) return;
        invocationOrdinals.put(task.provisionalScope,
                invocationOrdinals.getOrDefault(task.provisionalScope, 0)
                        + 1);
        task.clearProvisionalOrdinal();
    }

    /** The source keys this run attributed to one live root entry. */
    static Set<String> attributedSourceKeys(
            SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        Set<String> keys = new LinkedHashSet<>();
        if (registeredReceiverSource != null) {
            keys.add(registeredReceiverSource.key());
        }
        if (context != null && context.source != null) {
            keys.add(context.source.key());
        }
        return keys;
    }

    /** Empty only when entry-time runtime evidence names this source. */
    static String sourceMismatch(
            RuntimeTask task, SourceRef registeredReceiverSource,
            RuntimeTraceContext.View context) {
        SourceRef inherited = context.source;
        // The epoch is part of the address, so it is compared before any of
        // the four evidence shapes below, all of which ignore it.
        String lifecycle = lifecycleMismatch(task.sourceKey,
                attributedSourceKeys(registeredReceiverSource, context));
        if (!lifecycle.isEmpty()) return lifecycle;
        boolean receiverMatches = registeredReceiverSource != null
                && RuntimeTraceContext.sameSourceIdentity(task.sourceKey,
                registeredReceiverSource.key());
        boolean inheritedMatches = inherited != null
                && RuntimeTraceContext.sameSourceIdentity(task.sourceKey,
                inherited.key());
        if (OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(
                task.sourceKey)) {
            return registeredReceiverSource == null && inherited == null
                    ? "" : "matching root carried a registered source "
                    + (registeredReceiverSource == null
                    ? inherited.key() : registeredReceiverSource.key())
                    + " instead of the unregistered source";
        }
        // One rule for every anchor kind.  How the planned source was
        // established -- registered on the receiver, or inherited from the
        // thread -- says how the recording found it, not which source it is,
        // so it decided nothing here and the three arms it selected between
        // were three spellings of one question: does this run's evidence name
        // ANOTHER source?
        //
        // The receiver's own registration, when there is one, is that
        // evidence and is authoritative: a root entered on an object the
        // application registered elsewhere is elsewhere's, whatever the
        // thread was carrying.  With no registration, an inherited context
        // that names another source still contradicts.  Nothing attributed at
        // all does not: a replay reconstructs a receiver without repeating
        // its alias registration and reaches a region by a path carrying no
        // inherited context, and refusing it there withheld the occurrence
        // over a fact nobody established -- on 17960 that was every target
        // activation of the seed.  Node, epoch, region and ordinal have
        // already agreed by the time this is asked.
        if (registeredReceiverSource != null) {
            return receiverMatches ? ""
                    : "matching root receiver belonged to "
                    + registeredReceiverSource.key() + " instead of "
                    + task.sourceKey;
        }
        // An inherited context is not where the activation ran.  It is the
        // node the thread was carrying -- on an RPC service that is the
        // CALLER, and on a workload whose values cross nodes it is the node
        // of the mint the value came from, which is value provenance.  An
        // activation with no registration of its own has no evidence of
        // where it ran, and absence of evidence is not evidence of another
        // node, exactly as it is not for an absent inherited source.
        //
        // It refused, and on hdfs-17899 bug3 -- one JVM with nn0, source-dn
        // and target-dn all registered -- that is five tasks refused with
        // "matching root inherited hdfs-17899/nn0#epoch0 instead of
        // hdfs-17899/source-dn#epoch0" and five
        // PUBLICATION_TASK_ANSWERED_BY_NO_RUN behind them.  The difference
        // is still worth saying, so it is recorded rather than dropped.
        if (inherited != null && !inheritedMatches) {
            task.noteRequestContext("matching root inherited "
                    + inherited.key() + " instead of " + task.sourceKey);
        }
        return "";
    }

    /**
     * Records one task's terminal outcome and returns the campaign's halt
     * status once every task has settled, or {@code -1} while any task can
     * still produce evidence.
     */
    synchronized int settle(String taskId, int status) {
        if (tasks.isEmpty()) return -1;
        Integer previous = settled.get(safe(taskId));
        if (previous == null) settled.put(safe(taskId), status);
        if (settled.size() < tasks.size()) return -1;
        int worst = 0;
        for (Integer contribution : settled.values()) {
            worst = Math.max(worst, contribution);
        }
        return worst;
    }

    static ConcolicTaskPlan load() {
        String planValue = safe(System.getProperty(
                "causynth.concolic.task.plan")).trim();
        String selectedTasks = safe(System.getProperty(
                "causynth.concolic.task.id")).trim();
        if (planValue.isEmpty()) {
            return new ConcolicTaskPlan(null,
                    Collections.<RuntimeTask>emptyList());
        }
        String resultValue = safe(System.getProperty(
                "causynth.concolic.results")).trim();
        if (selectedTasks.isEmpty() || resultValue.isEmpty()) {
            throw new IllegalStateException("Concolic runtime requires "
                    + "task id and result path with a task plan");
        }
        Path result = Paths.get(resultValue);
        Path plan = Paths.get(planValue);
        if (!Files.isRegularFile(plan)) {
            throw new IllegalStateException(
                    "Concolic task plan not found: " + plan);
        }
        Set<String> selected = campaignTaskIds(selectedTasks);
        List<RuntimeTask> tasks = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(plan,
                StandardCharsets.UTF_8)) {
            Set<String> taskIds = new LinkedHashSet<>();
            int maxTasks = ExecutionTask.maxCampaignTasks();
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement parsed = new JsonParser().parse(line);
                if (!parsed.isJsonObject()) {
                    throw new IllegalStateException("malformed plan: "
                            + "every task plan row must be an object");
                }
                if (tasks.size() == maxTasks) {
                    throw new IllegalStateException("malformed plan: "
                            + "campaign exceeds its bound of " + maxTasks
                            + " tasks");
                }
                ExecutionTask encoded = ExecutionTask.decode(
                        parsed.getAsJsonObject());
                RuntimeTask task = new RuntimeTask(encoded);
                if (!taskIds.add(task.taskId)) {
                    throw new IllegalStateException("malformed plan: "
                            + "duplicate execution task " + task.taskId);
                }
                tasks.add(task);
            }
        } catch (IOException | RuntimeException exception) {
            throw new IllegalStateException("Causynth rejected "
                    + "task plan " + plan + ": "
                    + exception.getMessage(), exception);
        }
        for (String taskId : selected) {
            boolean present = false;
            for (RuntimeTask task : tasks) {
                present |= task.taskId.equals(taskId);
            }
            if (!present) {
                throw new IllegalStateException("Selected execution task "
                        + taskId + " is absent in " + plan);
            }
        }
        return new ConcolicTaskPlan(result, tasks);
    }

    /** The selected campaign, in plan order. */
    static Set<String> campaignTaskIds(String property) {
        Set<String> ids = new LinkedHashSet<>();
        for (String value : property.split(",")) {
            String taskId = safe(value).trim();
            if (taskId.isEmpty()) continue;
            if (!ids.add(taskId)) {
                throw new IllegalStateException("malformed plan: "
                        + "duplicate selected execution task " + taskId);
            }
        }
        if (ids.isEmpty()) {
            throw new IllegalStateException("malformed plan: "
                    + "no execution task is selected");
        }
        return ids;
    }

    static boolean compatibleRoot(
            String selectedMethod, String actualMethod,
            RootContextSelector context, RootArgumentSelector arguments,
            Object receiver, Object[] rootArguments, String threadName) {
        if (!safe(selectedMethod).equals(safe(actualMethod))) return false;
        if (!context.matches(receiver, threadName)) {
            return false;
        }
        return !arguments.present || arguments.matches(rootArguments);
    }

    /**
     * The replay address of one planned occurrence.
     *
     * <p>Two halves, decided at two different moments because that is when
     * each becomes knowable.</p>
     */
    /**
     * What an activation was reached under -- never what it is.
     *
     * <p>The RPC exchange, the request api, the thread it ran on, the
     * receiver's runtime class, and whether the recording established the
     * source by the receiver's own registration or by the thread's inherited
     * context.  None of it is identity: an occurrence is (node, epoch,
     * region, k-th activation), and these say where it was reached from and
     * how the recording found it.</p>
     *
     * <p>They were identity fields of the selector, and each grew its own
     * rule for when it might veto.  Two of the expensive 17960 failures were
     * exactly that: the request veto refused every flip replay whose workload
     * reached the planned activation by another path, and the
     * inherited-source anchor made an absence read as a contradiction.  They
     * are kept here because where an occurrence was reached from is worth
     * saying -- it is written into the gap when an address goes unanswered --
     * and matching never consults them.</p>
     *
     * <p>The one exception is {@link #candidate}, and it is not a matching
     * rule: a receiver-scoped root hook stands on an object of a named class,
     * so this decides which invocations are offered as candidates at all,
     * the way an instrumentation scope does.  It cannot distinguish two
     * activations of one address.</p>
     */
    static final class ReachedUnder {
        private final boolean receiverScoped;
        private final String receiverRuntimeClass;
        private final String threadName;
        private final String requestKey;
        private final String requestApi;
        /**
         * How the recording established the planned source: the receiver's
         * own registration, or the thread's inherited context.  Recorded
         * because it says how the occurrence was found; it selected between
         * three admission arms that asked one question, and the arms are
         * gone.
         */
        private final boolean registeredSourceAnchor;
        private final boolean inheritedContextAnchor;

        private ReachedUnder(boolean receiverScoped,
                             String receiverRuntimeClass, String threadName,
                             String requestKey, String requestApi,
                             boolean registeredSourceAnchor,
                             boolean inheritedContextAnchor) {
            this.receiverScoped = receiverScoped;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = stableReplayThreadContext(threadName);
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
            this.registeredSourceAnchor = registeredSourceAnchor;
            this.inheritedContextAnchor = inheritedContextAnchor;
        }

        /** Whether this invocation is offered as a candidate at all. */
        private boolean candidate(Object receiver, String actualThreadName) {
            if (!receiverScoped) return true;
            return receiver != null
                    && receiverRuntimeClass.equals(
                    receiver.getClass().getName())
                    && (threadName.isEmpty()
                    || threadName.equals(stableReplayThreadContext(
                    actualThreadName)));
        }

        /** How the exchange this root entered differs, or {@code ""}. */
        private String requestDifference(RuntimeTraceContext.View context) {
            if (!requestKey.equals(safe(context.requestKey))) {
                return "matching root entered request "
                        + safe(context.requestKey) + " instead of "
                        + requestKey;
            }
            if (!requestApi.equals(safe(context.requestApi))) {
                return "matching root entered request API "
                        + safe(context.requestApi) + " instead of "
                        + requestApi;
            }
            return "";
        }

        /** The circumstances on one line, for a named gap. */
        private String describe() {
            StringBuilder description = new StringBuilder();
            if (!requestKey.isEmpty()) {
                description.append("/requestKey=").append(requestKey);
            }
            if (!requestApi.isEmpty()) {
                description.append("/requestApi=").append(requestApi);
            }
            return description.toString();
        }

        private static String stableReplayThreadContext(String value) {
            return RootContextSelector.stableReplayThreadContext(value);
        }
    }

    static final class RootContextSelector {
        private final String sourceKey;
        /**
         * One-based invocation ordinal in this selector's stable runtime
         * scope.  This is planner evidence and is deliberately independent
         * of the trace occurrence id, which names evidence rather than a
         * replay counter.
         */
        private final int invocationOrdinal;
        /** Everything this address is not: see {@link ReachedUnder}. */
        private final ReachedUnder reachedUnder;

        private RootContextSelector(boolean receiverScoped,
                                    String receiverRuntimeClass,
                                    String threadName, String sourceKey,
                                    String requestKey, String requestApi,
                                    int invocationOrdinal,
                                    boolean registeredSourceAnchor,
                                    boolean inheritedContextAnchor) {
            this.sourceKey = safe(sourceKey);
            this.invocationOrdinal = invocationOrdinal;
            this.reachedUnder = new ReachedUnder(receiverScoped,
                    receiverRuntimeClass, threadName, requestKey, requestApi,
                    registeredSourceAnchor, inheritedContextAnchor);
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = optionalString(selector, "kind");
            boolean global = "GLOBAL_INVOCATION".equals(kind);
            String receiverClass = optionalString(selector, "receiverClass");
            String thread = selector.has("thread")
                    ? optionalString(selector, "thread") : "";
            JsonObject anchor = object(selector, "causalAnchor");
            String sourceKey = optionalString(anchor, "sourceKey");
            String requestKey = optionalString(anchor, "requestKey");
            String requestApi = optionalString(anchor, "requestApi");
            int invocationOrdinal = optionalInteger(selector,
                    "invocationOrdinal", -1);
            String anchorKind = optionalString(anchor, "kind");
            boolean registeredSource = RuntimeRegionPlanner
                    .ANCHOR_REGISTERED_SOURCE.equals(anchorKind);
            boolean unregisteredSource = RuntimeRegionPlanner
                    .ANCHOR_UNREGISTERED_SOURCE.equals(anchorKind);
            boolean inheritedContext = RuntimeRegionPlanner
                    .ANCHOR_INHERITED_CONTEXT.equals(anchorKind);
            boolean sentinelSource = RuntimeRegionPlanner.UNREGISTERED_SOURCE
                    .key().equals(sourceKey);
            if (!global && (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || !"RECEIVER_CONTEXT".equals(kind)
                    || selector.has("thread") && (thread.isEmpty()
                    || !thread.equals(thread.trim())))
                    || sourceKey.isEmpty()
                    || !sourceKey.equals(sourceKey.trim())
                    || invocationOrdinal < 1) {
                throw new IllegalArgumentException(
                        "rootSelector requires an exact receiver context and "
                                + "a causal anchor naming its source and a "
                                + "positive invocationOrdinal");
            }
            if (!registeredSource && !unregisteredSource && !inheritedContext
                    || unregisteredSource != sentinelSource) {
                throw new IllegalArgumentException(
                        "rootSelector causalAnchor.kind must be exactly "
                                + RuntimeRegionPlanner
                                .ANCHOR_REGISTERED_SOURCE + " or "
                                + RuntimeRegionPlanner
                                .ANCHOR_INHERITED_CONTEXT + " for a named "
                                + "source or " + RuntimeRegionPlanner
                                .ANCHOR_UNREGISTERED_SOURCE + " for "
                                + RuntimeRegionPlanner.UNREGISTERED_SOURCE
                                .key());
            }
            return new RootContextSelector(!global, receiverClass, thread,
                    sourceKey, requestKey, requestApi, invocationOrdinal,
                    registeredSource,
                    inheritedContext);
        }

        /** Whether this root invocation is a candidate for the occurrence. */
        private boolean matches(Object receiver, String actualThreadName) {
            return reachedUnder.candidate(receiver, actualThreadName);
        }

        /**
         * Why the candidate that just ran is not the addressed occurrence, or
         * {@code ""} when it is.
         */
        String unconfirmed(Set<String> attributedSourceKeys) {
            if (attributedSourceKeys.isEmpty()) {
                // Nothing attributed this activation to any node.  That is
                // the absence of evidence, not evidence of another node --
                // the same distinction the admission test draws for an
                // absent inherited source, and it has to be drawn here too
                // or the refusal simply moves from entry to close.  A replay
                // reconstructs a receiver without its alias registration and
                // reaches a region by a path that carries no inherited
                // context; on 17960 that is every target activation of the
                // seed, and refusing them left the run with no TARGET_REACH
                // at all.  Node, epoch, region and ordinal still decided
                // that this candidate was compatible; what is missing is a
                // second opinion nobody offered.
                return "";
            }
            boolean sameSource = false;
            for (String attributed : attributedSourceKeys) {
                if (RuntimeTraceContext.sameSourceIdentity(
                        sourceKey, attributed)) {
                    sameSource = true;
                    break;
                }
            }
            if (!sameSource) {
                return "occurrence ran on " + attributedSourceKeys
                        + ", but its anchor names " + sourceKey;
            }
            return "";
        }

        /** This address on one line, for a named gap. */
        private String describe() {
            return sourceKey + reachedUnder.describe() + "/invocation="
                    + invocationOrdinal;
        }

        /**
         * Whether the anchored source was never registered in this run, which
         * makes the address unsatisfiable here rather than merely unmatched.
         */
        private boolean anchorSourceNeverExisted() {
            return !OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(sourceKey)
                    && !RuntimeTraceContext.sourceIdentityRegistered(sourceKey);
        }

        static String stableReplayThreadContext(String value) {
            String thread = safe(value);
            Matcher executor = DEFAULT_EXECUTOR_THREAD_NAME.matcher(thread);
            if (executor.matches()) {
                return "pool-*-thread-" + executor.group(1);
            }
            Matcher objectIdentity =
                    DEFAULT_OBJECT_IDENTITY_THREAD_NAME.matcher(thread);
            return objectIdentity.matches()
                    ? objectIdentity.group(1) + "@*" : thread;
        }

    }

    private static final class RootArgumentSelector {
        private final boolean present;
        private final List<RootArgumentTypePredicate> predicates;

        private RootArgumentSelector(boolean present,
                                     List<RootArgumentTypePredicate> predicates) {
            this.present = present;
            this.predicates = predicates;
        }

        private static RootArgumentSelector from(JsonObject rootSelector) {
            if (!rootSelector.has("arguments")) {
                return new RootArgumentSelector(false,
                        Collections.emptyList());
            }
            JsonElement raw = rootSelector.get("arguments");
            if (raw == null || !raw.isJsonObject()) {
                return invalid("rootSelector.arguments must be an object");
            }
            JsonObject json = raw.getAsJsonObject();
            JsonElement rawPredicates = json.get("predicates");
            if (rawPredicates == null || !rawPredicates.isJsonArray()
                    || rawPredicates.getAsJsonArray().size() == 0) {
                return invalid("predicates must be a non-empty array");
            }
            List<RootArgumentTypePredicate> predicates = new ArrayList<>();
            Set<Integer> indices = new LinkedHashSet<>();
            for (JsonElement rawPredicate
                    : rawPredicates.getAsJsonArray()) {
                if (rawPredicate == null || !rawPredicate.isJsonObject()) {
                    return invalid("each predicate must be an object");
                }
                JsonObject predicate = rawPredicate.getAsJsonObject();
                if (!ROOT_ARGUMENT_PREDICATE_KIND.equals(
                        optionalString(predicate, "kind"))) {
                    return invalid("predicate kind must be exact runtime type");
                }
                int index = optionalInteger(predicate, "argumentIndex", -1);
                String runtimeType = optionalString(predicate, "runtimeType");
                if (index < 0 || runtimeType.isEmpty()
                        || !runtimeType.equals(runtimeType.trim())
                        || !indices.add(index)) {
                    return invalid("predicate index/type is malformed or duplicate");
                }
                predicates.add(new RootArgumentTypePredicate(index,
                        runtimeType));
            }
            predicates.sort((left, right) -> Integer.compare(
                    left.argumentIndex, right.argumentIndex));
            return new RootArgumentSelector(true,
                    Collections.unmodifiableList(predicates));
        }

        private static RootArgumentSelector invalid(String error) {
            throw new IllegalArgumentException(error);
        }

        /** No argument predicate: every activation of the root is admitted. */
        private boolean matches(Object[] rootArguments) {
            if (!present || rootArguments == null) return false;
            for (RootArgumentTypePredicate predicate : predicates) {
                if (predicate.argumentIndex >= rootArguments.length) {
                    return false;
                }
                Object value = rootArguments[predicate.argumentIndex];
                if (value == null || !predicate.runtimeType.equals(
                        value.getClass().getName())) {
                    return false;
                }
            }
            return true;
        }

    }

    private static final class RootArgumentTypePredicate {
        private final int argumentIndex;
        private final String runtimeType;

        private RootArgumentTypePredicate(int argumentIndex,
                                          String runtimeType) {
            this.argumentIndex = argumentIndex;
            this.runtimeType = runtimeType;
        }
    }

    static final class RuntimeTask {
        final String taskId;
        final String instrumentationSelector;
        final String regionId;
        /** The activation this task is. */
        final String sourceKey;
        final String occurrenceId;
        /**
         * The one address this task plans: node, epoch, region, k-th
         * activation.  Every comparison that decides whether a live
         * activation is this occurrence goes through it.
         */
        final OccurrenceAddress address;
        final String rootMethod;
        final RootContextSelector rootContextSelector;
        /** Argument predicates evaluated at the enclosing method entry. */
        final RootArgumentSelector enclosingRootArgumentSelector;
        final RootArgumentSelector rootArgumentSelector;
        /** Actions that execute directly at ordinary instrumentation hooks. */
        final List<SymbolizeAction> symbolize;
        final Map<String, String> branchPolicies;
        final Set<String> replayLoopExitSites;
        final LoopBoundPolicy loopBound;
        final List<ModelAssignment> modelAssignments;
        final List<GuardedReadAssignment> guardedReadAssignments;
        final boolean capturesTargetReach;
        /** Whether this non-loop address has already completed its goal. */
        volatile boolean completedGoalReserved;
        /**
         * Result rows this address has published in this replay.
         *
         * <p>Every admitted activation that reaches a terminal is its own
         * occurrence. This counts them so each row can name which one it is;
         * non-loop admission stops after its goal has completed.</p>
         */
        int publishedActivations;
        /**
         * Whether this region is rooted on a bounded loop body.  Its published
         * occurrence set is unrolled at most {@code loopBound
         * .maxBackedgeTraversals()} (K_L) times, exactly as an inner bounded
         * loop is: the iterations past K_L run concretely and capture nothing.
         */
        final boolean loopBodyRoot;
        final String rootLoopMethod;
        final int rootLoopHeaderUnitIndex;
        /**
         * The occurrence budget of a loop-body region: its ROOT loop's own
         * K_L, not the region's global max.  The root loop is what generates
         * one occurrence per iteration; the region's inner loops (the {@code
         * allKeys} walks) are unrolled WITHIN one occurrence and their larger
         * bounds must not inflate the occurrence count.  Using the region max
         * here published up to the inner-loop bound of occurrences, each
         * re-snapshotting the growing {@code allKeys} map, which under a
         * 600-min token lifetime (no physical expiry) explodes the symbolic
         * session.
         */
        final int loopOccurrenceBudget;
        /** Whether the one bounded-cut marker for this region was written. */
        boolean loopBoundCutRecorded;
        /** Turns of the root loop examined for this bounded address. */
        int admittedTurns;
        private boolean loopBoundGapClaimed;
        /** Kept occurrences that carried the selected causal anchor. */
        /** Exact phase/exchange identities committed by published turns. */
        final Set<String> observedSemanticAnchorIds =
                new LinkedHashSet<>();
        /** Turns run and given back for carrying no selected anchor. */
        /** Stable identity shared by every task in one linked replay. */
        final String replayGroupId;
        final String linkedReplayRole;
        final String topologyEpoch;
        final BranchReplayContract.RuntimeSchedule replayContract;
        /** The declared target branch event of a target-reach task. */
        final String targetBranchSite;
        final int targetBranchOccurrence;
        /** Solver-selected outcome that reaches the annotated failure. */
        final boolean targetBranchRequiredOutcome;
        /**
         * Declared communication ports this occurrence hands to the VM, by
         * port id.
         */
        final Map<String, CommunicationHandoffSpec>
                communicationHandoffs = new LinkedHashMap<>();
        /** Exact baseline hook executions, in recorded event order. */
        final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        /** Reserved source-hook ordinal across one LOOP_BODY_ROOT address. */
        final Map<String, Integer> configuredSourcePhaseOrdinals =
                new LinkedHashMap<>();
        /** Strict phase lookup; phase ids never alias source ids. */
        final Map<String, ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhasesById = new LinkedHashMap<>();
        /** Every protocol input this occurrence attaches from the VM. */
        final Set<String> attachPortIds = new LinkedHashSet<>();
        /**
         * Planned consumer occurrences of each protocol value this task
         * sends, in the order the plan's edges name them.  A producer rooted
         * at a loop body exports one value per iteration onto one message, so
         * one port legitimately addresses one consumer occurrence per value.
         */
        final Map<String, List<String>> exportConsumerOccurrenceByPort =
                new LinkedHashMap<>();
        /** OUT ports allowed to establish an otherwise absent producer source. */
        final Set<String> deferredOutgoingSourcePorts =
                new LinkedHashSet<>();
        /** OUT ports backed by one exact traced exchange in this task row. */
        final Set<String> exactOutgoingSourceCandidatePorts =
                new LinkedHashSet<>();
        /** Frozen runtime bindings used to resolve exact Map producers. */
        final JsonArray edgeBindings;
        /** Declared field -> unique frozen receiver locator for this task. */
        final Map<String, Long> plannedReceiverObjectIdByField =
                new LinkedHashMap<>();
        /**
         * Declared field and access anchor -> frozen receiver locator.  This
         * is what names a per-instance field whose declaring class has
         * several live receivers inside one activation.
         */
        final Map<String, Long> plannedReceiverObjectIdByFieldAccess =
                new LinkedHashMap<>();
        /**
         * Activations that ran as candidates for this address and were not the
         * addressed occurrence, and every distinct reason they were not.
         */
        int unaddressedCandidates;
        final Set<String> unaddressedReasons = new LinkedHashSet<>();
        /** The bucket and k a provisional admission took, or "" / 0. */
        String provisionalScope = "";
        int provisionalOrdinal;

        synchronized void markProvisionalOrdinal(String scope, int ordinal) {
            provisionalScope = safe(scope);
            provisionalOrdinal = ordinal;
        }

        synchronized void clearProvisionalOrdinal() {
            provisionalScope = "";
            provisionalOrdinal = 0;
        }

        RuntimeTask(ExecutionTask task) {
            if (!task.executable()) {
                throw new IllegalArgumentException(
                        "runtime task must be executable");
            }
            JsonObject rootSelector = task.rootSelector();
            this.taskId = task.taskId();
            this.instrumentationSelector = task.instrumentationSelector();
            this.regionId = task.regionId();
            this.sourceKey = task.sourceKey();
            this.occurrenceId = task.occurrenceId();
            this.address = OccurrenceAddress.parse(this.occurrenceId);
            this.rootMethod = task.rootMethod();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            this.enclosingRootArgumentSelector =
                    RootArgumentSelector.from(rootSelector);
            if (!this.sourceKey.equals(rootContextSelector.sourceKey)) {
                throw new IllegalArgumentException(
                        "rootSelector causal anchor names "
                                + rootContextSelector.sourceKey
                                + " instead of task source " + this.sourceKey);
            }
            // A region rooted at a loop body binds no arguments at its
            // frame: the method's parameters were bound once, at the entry
            // above the loop.  Its activation therefore carries an empty
            // argument array, and a type predicate over arguments that do not
            // exist there would refuse every iteration without saying so.
            this.rootArgumentSelector =
                    LoopBoundPolicy.LOOP_BODY_ROOT.equals(task.rootAuthority())
                            ? new RootArgumentSelector(false,
                            Collections.<RootArgumentTypePredicate>emptyList())
                            : RootArgumentSelector.from(rootSelector);
            this.symbolize = new ArrayList<>();
            this.branchPolicies = new LinkedHashMap<>();
            this.replayLoopExitSites = task.loopExitSites();
            this.loopBound = task.loopBound();
            this.loopBodyRoot = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                    task.rootAuthority());
            // A bounded loop publishes the activations some task addresses,
            // so a loop-body task must say WHICH activation it is: k, in its
            // occurrence id, like every other task.  Without it the replay
            // would have to default to the first turn or to any turn, and
            // neither is something the recording said.  Refused here, at the
            // plan, because a plan that cannot be executed should not reach
            // a replay.
            if (this.loopBodyRoot && !this.address.isNamed()) {
                throw new IllegalArgumentException(
                        "ROOT_LOOP_OCCURRENCE_UNADDRESSED: loop-body task "
                                + this.taskId + " plans occurrence "
                                + this.occurrenceId + ", which names no "
                                + "k-th activation");
            }
            this.rootLoopMethod = task.rootLoopMethod();
            this.rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            // The root loop's declared K_L (its loopSiteId is the key its
            // bound is under); an undeclared site inherits the default.
            this.loopOccurrenceBudget = this.loopBound
                    .maxBackedgeTraversals(task.rootLoopSiteId());
            this.modelAssignments = new ArrayList<>();
            this.guardedReadAssignments = new ArrayList<>();
            this.capturesTargetReach =
                    task.goalKind().capturesTargetReach();
            // The plan names the propagation ledger every task of this
            // invocation shares: ConcolicScheduler stamps the seed replay,
            // PathReplayTaskFactory stamps each flip bundle. A row that
            // names none is a plan no scheduler wrote, and the importer
            // refuses its results by name (CONCOLIC_RESULT_REPLAY_GROUP_MISSING).
            this.replayGroupId = optionalString(task.json(),
                    "linkedReplayGroupId");
            this.linkedReplayRole = optionalString(task.json(),
                    "linkedReplayRole");
            this.topologyEpoch = optionalString(task.json(), "topologyEpoch");
            this.edgeBindings = task.edgeBindings();
            indexPlannedReceiverObjectIds(task.inputActions().all());
            // The plan row decoded this catalog once; phase ids are already
            // one strict ordered ledger by then, so this is an index, not a
            // second admission.
            this.configuredSourcePhases = task.configuredSourcePhases();
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                // One id, many executions: the first is the one the
                // recording saw first, and the rest differ only in where.
                configuredSourcePhasesById.putIfAbsent(phase.phaseId(),
                        phase);
            }
            this.replayContract = task.replaySchedule();
            JsonObject targetBranch = object(task.json(), "targetBranch");
            this.targetBranchSite = optionalString(targetBranch, "siteId");
            this.targetBranchOccurrence = optionalInteger(targetBranch,
                    "occurrence", -1);
            this.targetBranchRequiredOutcome = targetRequiredOutcome(
                    task.branches(), targetBranchSite,
                    targetBranchOccurrence);
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
            }
            for (JsonElement element : task.branches()) {
                JsonObject branch = element.getAsJsonObject();
                String siteId = optionalString(branch, "siteId");
                branchPolicies.put(siteId, optionalString(branch, "policy"));
            }
            JsonElement encodedAssignments = task.json().get(
                    "modelAssignments");
            if (encodedAssignments != null
                    && !encodedAssignments.isJsonArray()) {
                throw new IllegalArgumentException(
                        "modelAssignments must be an array in " + taskId);
            }
            for (JsonElement element : task.modelAssignments()) {
                modelAssignments.add(new ModelAssignment(
                        element.getAsJsonObject()));
            }
            Set<String> assignmentKeys = new LinkedHashSet<>();
            for (ModelAssignment assignment : modelAssignments) {
                if (assignment.key.isEmpty()
                        || !assignmentKeys.add(assignment.key)) {
                    throw new IllegalArgumentException(
                            "model assignment keys must be nonempty and "
                                    + "unique in " + taskId);
                }
            }
            Set<String> guardedReadIdentities = new LinkedHashSet<>();
            Set<String> guardedReadAnchors = new LinkedHashSet<>();
            for (JsonElement element : task.guardedReadAssignments()) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "guardedReadAssignments must contain objects in "
                                    + taskId);
                }
                GuardedReadAssignment assignment =
                        new GuardedReadAssignment(element.getAsJsonObject(),
                                occurrenceId);
                String anchor = assignment.consumerSiteId + "\n"
                        + assignment.consumerSiteOccurrence + "\n"
                        + assignment.declaringClass + "\n"
                        + assignment.fieldName + "\n"
                        + assignment.descriptor;
                if (!guardedReadIdentities.add(assignment.readIdentity)
                        || !guardedReadAnchors.add(anchor)) {
                    throw new IllegalArgumentException(
                            "guarded read assignments must have unique "
                                    + "identities and exact anchors in "
                                    + taskId);
                }
                guardedReadAssignments.add(assignment);
            }
            for (CommunicationHandoffSpec site
                    : task.communicationHandoffs()) {
                if (!site.outgoing()) {
                    attachPortIds.add(site.portId());
                }
                // A region that holds both sides of a cut declares the same
                // port twice, once per role, and each role has its own site.
                if (communicationHandoffs.put(handoffKey(site.portId(),
                        site.outgoing()), site) != null) {
                    throw new IllegalArgumentException(
                            "communication port declares two handoff sites "
                            + "in " + taskId + ": " + site.portId());
                }
            }
            // A configured-source model names one mint SITE of the frozen
            // catalog.  There is no selected-source row to agree with any
            // more: the site is the identity.
            for (ModelAssignment assignment : modelAssignments) {
                if (!assignment.configuredSourceAssignment()) continue;
                ConfiguredSourcePhaseContract.Occurrence publish =
                        configuredSourcePhasesById.get(
                                assignment.configuredSourcePhaseId);
                if (publish == null
                        || publish.phase()
                        != ConfiguredSourcePhaseContract.Phase.PUBLISH
                        || !assignment.configuredSourceId.equals(
                        publish.sourceId())
                        || !assignment.configuredSourceFieldSignature.equals(
                        publish.fieldSignature())
                        || !assignment.matchesConfiguredSource(
                        publish.phaseId(), publish.sourceId(),
                        publish.fieldSignature())
                        || assignment.hasContainerTarget()) {
                    throw new IllegalArgumentException(
                            "model assignment names an undeclared or "
                                    + "unsupported configured source in "
                                    + taskId + ": " + assignment.key);
                }
            }
            indexExportConsumerOccurrences(task, edgeBindings);
        }

        /** Solver value for the one exact getfield this hook precedes. */
        GuardedReadAssignment guardedReadAssignment(
                ConsumerAccessAnchor consumer, String fieldSignature) {
            DeclaredField field = FieldPathSpec.declaredField(fieldSignature);
            GuardedReadAssignment selected = null;
            for (GuardedReadAssignment candidate : guardedReadAssignments) {
                if (!candidate.matches(consumer, field)) continue;
                if (selected != null) {
                    throw new IllegalStateException(
                            "two guarded read assignments match "
                                    + consumer.siteId + " occurrence "
                                    + consumer.occurrence);
                }
                selected = candidate;
            }
            return selected;
        }

        /**
         * Whether a declared field type is a container whose whole state the
         * VM versions, rather than a reference slot.
         */
        static boolean isWholeStateContainerType(DeclaredField field) {
            if (field == null) return false;
            // The map rule is the one this build always had, reflectively
            // widened past the three names the planner lists.
            return isMapType(field.type())
                    || SharedFieldFlow.wholeStateCarrierField(field.owner(),
                    field.name(), field.type());
        }

        /** Whether a declared field type is a Map the VM versions whole. */
        static boolean isMapType(String javaType) {
            try {
                return Map.class.isAssignableFrom(Class.forName(
                        safe(javaType).trim()));
            } catch (Throwable notLoadable) {
                // Judge by name when the type is not on this loader: the
                // declaration is the authority, not the loaded class.
                String value = safe(javaType);
                return value.endsWith("Map") || value.contains("Map<");
            }
        }

        /**
         * The cells this task's declared SYMBOLIC inputs stand on.
         *
         * <p>For the one row that has to say what did not materialize.</p>
         */
        List<String> declaredInputCells() {
            List<String> cells = new ArrayList<>();
            for (SymbolizeAction action : symbolize) {
                cells.add(safe(action.cell).isEmpty()
                        ? safe(action.symbol) : safe(action.cell));
            }
            return cells;
        }

        /** The declared handoff site of one communication port role. */
        CommunicationHandoffSpec communicationHandoff(
                String portId, boolean exporting) {
            return communicationHandoffs.get(handoffKey(portId, exporting));
        }


        /**
         * Indexes the consumers named by this occurrence's outgoing protocol
         * edges.  The plan's own decode has already refused a port whose
         * consumers span two execution sources; what is read here is which
         * planned consumer occurrences one delivery may be attached by.
         */
        void indexExportConsumerOccurrences(ExecutionTask task,
                                            JsonArray bindings) {
            for (CommunicationHandoffSpec site
                    : communicationHandoffs.values()) {
                if (!site.outgoing()) continue;
                String portId = site.portId();
                List<String> consumers = task.exportConsumerOccurrences(
                        portId);
                if (consumers.isEmpty()) continue;
                // The edges are re-walked only to decide exactness: an OUT
                // site may establish an absent producer source when every
                // edge that carries it is this root's own traced exchange.
                boolean exactSourceCandidate = true;
                for (JsonElement element : bindings) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!"RUNTIME_PROTOCOL_FLOW".equals(
                            optionalString(binding, "kind"))
                            || !portId.equals(
                            optionalString(binding, "fromOutputPort"))
                            || !occurrenceId.equals(OccurrenceId.parse(
                            optionalString(binding, "fromOccurrenceId"))
                            .planned())) {
                        continue;
                    }
                    if (!"TRACED_RPC_EXCHANGE_CORRELATION_V1".equals(
                            optionalString(binding, "correlationAuthority"))
                            || !rootContextSelector.reachedUnder.requestKey.equals(
                            optionalString(binding, "requestKey"))
                            || !rootContextSelector.reachedUnder.requestApi.equals(
                            optionalString(binding, "requestApi"))) {
                        exactSourceCandidate = false;
                    }
                }
                exportConsumerOccurrenceByPort.put(portId, consumers);
                if (exactSourceCandidate) {
                    exactOutgoingSourceCandidatePorts.add(portId);
                }
            }
        }

        /** The planned consumer occurrences one exported port may address. */
        List<String> exportConsumerOccurrences(String portId) {
            List<String> consumers = exportConsumerOccurrenceByPort.get(
                    safe(portId));
            return consumers == null ? Collections.<String>emptyList()
                    : consumers;
        }

        String outgoingSourceScope(String portId) {
            return rootMethod + '\n' + rootContextSelector.reachedUnder.requestKey + '\n'
                    + rootContextSelector.reachedUnder.requestApi + '\n' + safe(portId);
        }

        Set<String> declaredOutgoingPorts() {
            Set<String> ports = new LinkedHashSet<>();
            for (CommunicationHandoffSpec handoff
                    : communicationHandoffs.values()) {
                if (handoff.outgoing()) ports.add(handoff.portId());
            }
            return ports;
        }

        /**
         * Indexes the frozen receiver locator of every planned field access.
         *
         * <p>A per-instance field (one object per key, several receivers of
         * the same declared field inside one activation) has no unique
         * locator for the field alone.  The plan does distinguish those
         * receivers: every action names the exact static access site and the
         * activation-local occurrence of that site which read it.  That pair
         * is the same replay-stable access anchor the runtime builds at each
         * read ({@link ConsumerAccessAnchor}) and the composer already uses
         * to name a read independently of any object id, so it is what binds
         * one live receiver to one planned locator.  The by-field index
         * stays as the answer for a field with a single receiver, including
         * every carrier selected without ever being read.</p>
         */
        void indexPlannedReceiverObjectIds(JsonArray inputActions) {
            Map<String, Set<Long>> candidates = new LinkedHashMap<>();
            Map<String, Set<Long>> accessCandidates = new LinkedHashMap<>();
            for (JsonElement element : inputActions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                long receiver = optionalLongInteger(action,
                        "fieldReceiverObjectId", 0L);
                DeclaredField field = FieldPathSpec.declaredField(
                        firstNonBlank(optionalString(action, "leafFieldSignature"),
                                optionalString(action, "accessFieldSignature")));
                if (field == null || receiver <= 0L) continue;
                String fieldKey = field.owner() + "#" + field.name();
                candidates.computeIfAbsent(fieldKey,
                        ignored -> new LinkedHashSet<>()).add(receiver);
                for (String site : plannedAccessSites(action)) {
                    for (int occurrence : plannedAccessOccurrences(action)) {
                        accessCandidates.computeIfAbsent(
                                fieldAccessKey(fieldKey, site, occurrence),
                                ignored -> new LinkedHashSet<>()).add(receiver);
                    }
                }
            }
            indexUniqueReceivers(candidates,
                    plannedReceiverObjectIdByField);
            indexUniqueReceivers(accessCandidates,
                    plannedReceiverObjectIdByFieldAccess);
        }

        /** Keeps only the locators one key names without contradiction. */
        private static void indexUniqueReceivers(
                Map<String, Set<Long>> candidates, Map<String, Long> index) {
            for (Map.Entry<String, Set<Long>> entry : candidates.entrySet()) {
                if (entry.getValue().size() == 1) {
                    index.put(entry.getKey(),
                            entry.getValue().iterator().next());
                }
            }
        }

        /** Every static access site one planned action was observed at. */
        private static Set<String> plannedAccessSites(JsonObject action) {
            Set<String> sites = new LinkedHashSet<>();
            for (String member : new String[]{"staticAccessSiteId", "siteId"}) {
                String site = optionalString(action, member);
                if (!site.isEmpty()) sites.add(site);
            }
            for (JsonElement element : array(action, "accessSites")) {
                if (!element.isJsonPrimitive()) continue;
                String site = safe(element.getAsString());
                if (!site.isEmpty()) sites.add(site);
            }
            return sites;
        }

        /**
         * Every activation-local occurrence the plan states for one access.
         *
         * <p>An accessor-mediated read counts calls of the accessor's call
         * site and a direct read counts executions of the getfield site.  The
         * plan names both under its own member, so every stated count is
         * indexed and {@link #indexUniqueReceivers} drops a key two actions
         * disagree on rather than guessing which counter was meant.</p>
         */
        private static Set<Integer> plannedAccessOccurrences(
                JsonObject action) {
            Set<Integer> occurrences = new LinkedHashSet<>();
            for (String member : new String[]{"accessorOccurrence",
                    "activationLocalStaticSiteOccurrence",
                    "replayOccurrence"}) {
                int occurrence = optionalInteger(action, member, 0);
                if (occurrence > 0) occurrences.add(occurrence);
            }
            return occurrences;
        }

        private static String fieldAccessKey(String fieldKey, String site,
                                             int occurrence) {
            return fieldKey + "\n" + site + "\n" + occurrence;
        }

        static String handoffKey(String portId, boolean exporting) {
            return (exporting ? "EXPORT\n" : "ATTACH\n") + safe(portId);
        }

        /**
         * Records that one candidate ran and was not this address, keeping
         * the last reason for the run's single statement about it.
         */
        private final Set<String> requestContexts = new LinkedHashSet<>();

        synchronized void noteUnaddressedCandidate(String reason) {
            unaddressedCandidates++;
            unaddressedReasons.add(candidateNote(reason));
            registerRunTotalsHook();
        }

        /**
         * One refused candidate, as a sentence a reader can act on.
         *
         * <p>Two facts every refusal owes and none of them carried: the
         * thread the candidate ran on -- this method runs on it -- and a
         * difference that is actually stated.  A row whose difference was
         * empty read as "matching root:  (attributed to X)", which is the
         * shape 11741's balancer#3 and 17897's dn0#1 were reported in: the
         * address matched and something else refused it, and the row said
         * neither half out loud.</p>
         */
        private static String candidateNote(String reason) {
            String stated = safe(reason).trim();
            if (stated.isEmpty()) {
                stated = "matching root was refused with no stated"
                        + " difference";
            }
            return stated + " [thread="
                    + Thread.currentThread().getName() + "]";
        }

        /**
         * Records which request a matching root entered, when it is not the
         * planned one.  Kept so the run can say where an admitted occurrence
         * was reached from; it never withholds the address.
         */
        synchronized void noteRequestContext(String enteredUnder) {
            requestContexts.add(safe(enteredUnder));
        }

        /** The run's one statement about an address nothing answered. */
        synchronized String unansweredAddress() {
            boolean neverExisted = rootContextSelector
                    .anchorSourceNeverExisted();
            return unaddressedCandidates + " compatible activation(s) did "
                    + "not answer the addressed occurrence; "
                    + unaddressedReasons + (neverExisted
                    ? "; " + rootContextSelector.describe()
                    + " was never registered in this run" : "");
        }

        /** Body entries this loop may run before the replay is cut. */
        int maxLoopBodies(String loopId) {
            return LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES;
        }

        String policy(String siteId) {
            String policy = branchPolicies.get(siteId);
            return "EXPLORE".equals(policy)
                    || "PATH_ASSUMPTION".equals(policy) ? policy : "EXPLORE";
        }

        /** Whether the frozen plan declares a policy for this branch site. */
        boolean declaresBranch(String siteId) {
            return branchPolicies.containsKey(safe(siteId));
        }

        /** Boundary-only loop controls advance replay invocation identity. */
        boolean observesReplayBoundary(String siteId) {
            return replayLoopExitSites.contains(safe(siteId));
        }

        /** The next activation ordinal of this address. */
        synchronized int nextActivationOrdinal() {
            return ++publishedActivations;
        }

        /**
         * The planner numbers a source site inside one activation root.  An
         * ordinary region activation is that root and therefore restarts at
         * one.  LOOP_BODY_ROOT is different: several body activations are
         * slices of one enclosing root-loop activation, so only that address
         * carries a reserved ordinal across its retained turns.
         */
        synchronized int configuredSourcePhaseOrdinal(
                String key, int localOrdinal) {
            return (loopBodyRoot
                    ? configuredSourcePhaseOrdinals.getOrDefault(
                    safe(key), 0) : 0) + localOrdinal;
        }

        /** Reserves the phase prefix used by one retained loop-body turn. */
        synchronized void reserveConfiguredSourcePhaseOrdinals(
                Map<String, Integer> used) {
            if (!loopBodyRoot) return;
            for (Map.Entry<String, Integer> entry : used.entrySet()) {
                configuredSourcePhaseOrdinals.merge(entry.getKey(),
                        entry.getValue(), Integer::sum);
            }
        }

        /**
         * Settles the small occurrence ledger before asynchronous decoding.
         * A later body turn is allowed to rely on this reservation; any
         * publication failure is consequently terminal and never rolled back.
         */
        synchronized void reserveCompletedOccurrence(
                Map<String, Integer> sourceOrdinals) {
            reserveConfiguredSourcePhaseOrdinals(sourceOrdinals);
        }


        /** Exact source phases that may address a semantic loop turn. */
        Set<String> configuredSourceAnchorPhases() {
            Set<String> phases = new LinkedHashSet<>();
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                phases.add(phase.phaseId());
            }
            return phases;
        }

        /**
         * Whether this loop-body region has already published its bounded
         * occurrence set (K_L rows), so a further iteration is a bounded cut.
         *
         * <p>README: a bounded loop is unrolled K_L times, and OCC-1 must not
         * defeat that -- one occurrence per iteration would publish one row
         * per heartbeat (~128 for the DN {@code offerService} loop) and make
         * every iteration pay for full symbolic capture.  {@code
         * publishedActivations} is the net kept-ordinal count, so an iteration
         * whose occurrence was abandoned frees its slot and does not spend the
         * budget: the cap is on published occurrences, not admissions.</p>
         *
         * <p>While an anchored slot is still open the cut waits: the address
         * has not yet seen the exchange it was selected for, and cutting on
         * the raw ordinal would end the window before that exchange happens.
         * The raw number of polling turns is deliberately not bounded by
         * K_L: K_L bounds the <em>published symbolic cases</em>, not how many
         * concrete workload turns may be inspected before the selected RPC
         * exchange occurs.  Workload termination bounds that inspection.  If
         * the exchange never occurs, shutdown publishes a named coverage gap
         * instead of silently substituting an unrelated prefix turn.</p>
         */
        /**
         * Whether this task names an activation the bound cannot record.
         *
         * <p>A bounded loop publishes the activations some task addresses,
         * and K_L is what the instrumentation records.  A k past it is an
         * activation no replay reaches, and saying so is the difference
         * between a stated gap and a silently missing occurrence.</p>
         */
        synchronized boolean addressesOccurrenceBeyondBound() {
            return loopBodyRoot && address.isNamed()
                    && loopOccurrenceBudget > 0
                    && address.ordinal() > loopOccurrenceBudget;
        }

        /** One bound gap per task, however many turns follow it. */
        synchronized boolean claimLoopBoundGapMarker() {
            if (loopBoundGapClaimed) return false;
            loopBoundGapClaimed = true;
            return true;
        }

        synchronized boolean cutsBoundedLoopOccurrence() {
            if (!loopBodyRoot) return false;
            // A bounded-loop region publishes the activations whose k a task
            // on it addresses, and every task names k.  The addressed k is
            // therefore the whole rule: the turn that is the k-th publishes,
            // and the rest of the loop runs unrecorded.
            //
            // No slots are reserved for anything.  They used to be, for
            // turns carrying a "semantic anchor" -- which was a second
            // admission condition deciding which activation mattered outside
            // the address, and is gone with it.
            if (publishedActivations >= loopOccurrenceBudget) return true;
            admittedTurns++;
            return false;
        }

        /** Claims the one bounded-cut marker write for this region. */
        synchronized boolean claimLoopBoundCutMarker() {
            if (loopBoundCutRecorded) return false;
            loopBoundCutRecorded = true;
            return true;
        }

        /**
         * Gives back an ordinal whose activation published nothing, so the
         * ordinals of one address stay dense and gapless.  Only one
         * activation of an address runs at a time, so the ordinal being
         * returned is always the last one taken.
         */
        synchronized void releaseActivationOrdinal(int ordinal) {
            if (ordinal > 0 && ordinal == publishedActivations) {
                publishedActivations--;
            }
        }

        boolean declaresTargetBranch() {
            return !targetBranchSite.isEmpty();
        }

        /** Every injected hook that belongs to one physical Java entry. */
        String rootHookGroupKey() {
            // Source is resolved from runtime evidence by the dispatcher. If
            // it were part of this static hook group, the first hook for one
            // source could not dispatch a sibling task for another source at
            // the same region root.
            return (loopBodyRoot ? "LOOP\n" : "METHOD\n")
                    + regionId + "\n" + rootMethod
                    + (loopBodyRoot ? "\n" + rootLoopMethod + "\n"
                    + rootLoopHeaderUnitIndex : "");
        }

        /** All lightweight enclosing hooks physically share this method. */
        String loopRootHookGroupKey() {
            return loopBodyRoot ? rootMethod : "";
        }

        /**
         * The bucket this region's activations are counted in.
         *
         * <p>An occurrence is the k-th activation of this region on this
         * node and epoch.  Counting and matching have to use the same scope
         * or the ordinal means one thing when the plan writes it and
         * another when the replay checks it -- the planner counts every
         * observed activation of the region ({@code
         * RuntimeRegionPlanner.replayInvocationScope}), so the replay counts
         * every compatible activation of it too.</p>
         *
         * <p>The request is in neither scope.  It used to be in both, which
         * was consistent; then matching stopped comparing it while counting
         * still partitioned by it, and "ordinal 1 of the bucket this
         * candidate happens to be in" satisfied "ordinal 1 of the bucket the
         * plan meant".  On hdfs-17960 that matched the checkpoint region's
         * planned occurrence to the process's first saveNamespace, which
         * serialized no snapshots and decided none of the branches the goal
         * needs.  Which exchange an activation was reached under is
         * information about it, and information does not partition a
         * count.</p>
         */
        String invocationCounterKey() {
            return invocationCounterKey(sourceKey);
        }

        /**
         * The bucket an activation attributed to {@code lifecycle} counts in.
         *
         * <p>The k in "k-th activation" is counted within one node <em>and
         * one epoch</em>, because that is what the address says.  Keying the
         * bucket on the planned epoch made it a per-node counter instead:
         * one JVM that restarts a node runs both lifecycles, so on
         * hdfs-17960 the two {@code deleteSnapshot} activations before the
         * NameNode restart took ordinals 1 and 2 and the two after it --
         * the ones the plan addresses as epoch 1's first and second -- took
         * 3 and 4 and matched nothing.  The planner already counts per
         * observed source ({@code RuntimeRegionPlanner.replayInvocationScope}
         * is handed each activation's own {@code rootSource}), so this is
         * the replay counting the population the plan counted.</p>
         */
        String invocationCounterKey(String lifecycle) {
            return OccurrenceAddress.of(safe(lifecycle).isEmpty()
                    ? sourceKey : lifecycle, regionId, 1)
                    .counterScope(rootMethod);
        }

        /**
         * The address this activation ran at: the lifecycle the run
         * attributed to it and the k it took in that lifecycle's bucket.
         *
         * <p>Unnamed when the bucket handed out no ordinal, which is an
         * activation outside the recording window; an unnamed address
         * matches nothing rather than half-matching on the node.</p>
         */
        OccurrenceAddress observedAddress(
                String lifecycle, Map<String, Integer> ordinalByScope) {
            Integer ordinal = ordinalByScope.get(
                    invocationCounterKey(lifecycle));
            return OccurrenceAddress.of(safe(lifecycle).isEmpty()
                            ? sourceKey : lifecycle, regionId,
                    ordinal == null ? 0 : ordinal.intValue());
        }

        /**
         * Selects a communication consumer by the message that invoked it.
         * Tasks with no planner-authored IN edge retain ordinal addressing.
         */
        boolean acceptsRootInvocation(OccurrenceAddress observed,
                                              boolean exactOutgoingAddress) {
            // The whole address the occurrence id states -- node, epoch,
            // region and k -- against the whole address this activation ran
            // at, read from the occurrence id every other stage reads it
            // from.  Comparing the k alone let a task planned for one node
            // answer another node's first activation of the same region.
            //
            // And nothing else.  An occurrence is that address; the message
            // an activation was reached by is provenance the handoff row
            // states, not a second identity that may veto the first.  The
            // arm that stood here replaced the address entirely whenever
            // the plan named an IN producer, so an activation that agreed
            // on node, epoch, region and k was refused for arriving on an
            // envelope the replay had not reproduced -- 11741's
            // balancer#3 and #7 and 17897's dn0#1, each reported with an
            // empty reason because the address it was refused on matched.
            return exactOutgoingAddress || address.matches(observed);
        }

        /**
         * Reserves completed evidence before reopening task admission.
         *
         * <p>Loop-body roots remain governed exclusively by K_L. Every
         * non-loop address denotes one dynamic occurrence and is complete
         * after its first full terminal result; targetReached:false is that
         * occurrence's seed case.</p>
         */
        void reserveCompletedEvidence(boolean targetReached) {
            if (!loopBodyRoot) {
                completedGoalReserved = true;
            }
        }

        boolean blocksAdmissionAfterCompletedGoal() {
            return completedGoalReserved;
        }

        /**
         * Whether this occurrence directly witnessed the selected failure
         * outcome, rather than merely deviating from its recorded seed path.
         */
        boolean reachedRequiredTargetOutcome(JsonObject reach) {
            return declaresTargetBranch()
                    && reach != null
                    && targetBranchSite.equals(optionalString(reach, "siteId"))
                    && targetBranchOccurrence == optionalInteger(reach,
                    "occurrence", -1)
                    && reach.has("outcome")
                    && reach.get("outcome").isJsonPrimitive()
                    && reach.getAsJsonPrimitive("outcome").isBoolean()
                    && reach.get("outcome").getAsBoolean()
                    == targetBranchRequiredOutcome;
        }

        /** The declared target branch event, for a named coverage gap. */
        String targetBranchLabel() {
            return targetBranchSite + "#" + targetBranchOccurrence;
        }

        static boolean targetRequiredOutcome(
                JsonArray branches, String targetSite,
                int targetOccurrence) {
            if (safe(targetSite).isEmpty()) return false;
            Boolean required = null;
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!targetSite.equals(optionalString(branch, "siteId"))
                        || targetOccurrence != optionalInteger(branch,
                        "selectedOccurrence", -1)) {
                    continue;
                }
                JsonElement encoded = branch.get("requiredOutcome");
                if (encoded == null || !encoded.isJsonPrimitive()
                        || !encoded.getAsJsonPrimitive().isBoolean()) {
                    throw new IllegalArgumentException(
                            "target branch requires a boolean outcome: "
                                    + targetSite + '#' + targetOccurrence);
                }
                boolean candidate = encoded.getAsBoolean();
                if (required != null && required != candidate) {
                    throw new IllegalArgumentException(
                            "ambiguous target required outcome: "
                                    + targetSite + '#' + targetOccurrence);
                }
                required = candidate;
            }
            if (required == null) {
                throw new IllegalArgumentException(
                        "target branch is absent from the branch catalog: "
                                + targetSite + '#' + targetOccurrence);
            }
            return required;
        }

    }
}
