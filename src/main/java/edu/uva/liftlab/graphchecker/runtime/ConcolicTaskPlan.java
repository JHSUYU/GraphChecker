package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.plan.ConcolicScheduler;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.RootHookGroup;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ROOT_ARGUMENT_PREDICATE_KIND;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.enclosingLoopRootAdmits;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.registerRunTotalsHook;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.sameHookIdentity;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.taskUnanswered;

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
    /**
     * Each task's slot in {@link #candidateLive} and
     * {@link #occurrenceClaimed}, by the task object itself.
     *
     * <p>A task is its own identity here -- it declares no {@code equals} --
     * and the two arrays are addressed by position, so the position is looked
     * up rather than searched for.  {@code tasks.indexOf} walked the whole
     * plan under this monitor on every admitted occurrence and every released
     * candidate.</p>
     */
    private final Map<RuntimeTask, Integer> slots =
            new IdentityHashMap<RuntimeTask, Integer>();
    /**
     * The hook group of each {@code (instrumentationSelector, rootMethod)}
     * this run has entered.
     *
     * <p>{@link #rootHookGroup} is a function of the pair and of
     * {@link #tasks}, which is unmodifiable, so its answer is a property of
     * the pair: computed on the first entry at that hook and read from here
     * afterwards.  It scanned the plan twice at EVERY woven root entry --
     * {@code ConcolicRegionRuntime.enterRegionFrame} asks before it knows
     * whether the hook is even a sibling of one already open -- which is
     * where hdfs-11741's replay threads were found blocked.</p>
     */
    private final Map<String, RootHookGroup> rootHookGroups =
            new LinkedHashMap<String, RootHookGroup>();
    private final Map<String, RootHookGroup> loopRootHookGroups =
            new LinkedHashMap<String, RootHookGroup>();
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
        for (int index = 0; index < this.tasks.size(); index++) {
            this.slots.put(this.tasks.get(index), index);
        }
    }


    /**
     * Releases the address of a candidate that ended without being the
     * occurrence, so the next compatible invocation may try for it.
     */
    synchronized void releaseCandidate(RuntimeTask task) {
        Integer index = slots.get(task);
        if (index != null) candidateLive[index] = false;
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
    void publishUnansweredAddresses() {
        List<RuntimeTask> unanswered = new ArrayList<RuntimeTask>();
        synchronized (this) {
            if (unansweredAddressesPublished) return;
            unansweredAddressesPublished = true;
            for (int index = 0; index < tasks.size(); index++) {
                // An address that published at least one occurrence has been
                // answered for end-of-run diagnostics. Goal completion owns
                // the separate decision to admit another activation.
                if (occurrenceClaimed[index]) continue;
                unanswered.add(tasks.get(index));
            }
        }
        // Rendering a refusal reads the endpoints this run filed and digests
        // the addresses it names, and it happens here -- once per address
        // nothing answered, with this monitor released.  It used to happen
        // once per candidate COMPARISON, inside #select, and hdfs-11741's
        // seed replay then spent 980 seconds with every woven thread blocked
        // behind the one holding this monitor to hash.
        for (RuntimeTask task : unanswered) {
            if (task.unaddressedCandidates == 0) {
                // Nothing compatible ran at all -- not one activation the
                // address could have been compared against.  That is a
                // different statement from "several ran and none matched",
                // and it used to be no statement: the task published neither
                // an activation nor a skip, and the importer met silence.
                taskUnanswered(task, "ROOT_NEVER_EXECUTED: the planned root"
                        + " did not execute in this replay: no compatible"
                        + " activation was offered for "
                        + task.occurrenceId);
                continue;
            }
            taskUnanswered(task, (task.rootContextSelector
                            .anchorSourceNeverExisted()
                            ? "ANCHOR_EPOCH_NOT_REACHED: "
                            : "OCCURRENCE_ANCHOR_UNMATCHED: ")
                    + task.unansweredAddress());
        }
    }

    /**
     * One candidate that ran and was not the addressed occurrence: the facts
     * of the refusal, not a sentence about it.
     *
     * <p>A refusal is stated once, at {@code TASK_UNANSWERED}, and admission
     * only files what the sentence is made of -- the prefix, the address the
     * activation ran at, the node this run attributed it to and the thread it
     * ran on.  All four are already in hand at the comparison; rendering them
     * is what is not, because it digests two addresses and searches the
     * endpoints this run filed for the two anchors behind them.</p>
     *
     * <p>Distinct refusals stay distinct: the four facts ARE the identity the
     * rendered sentence had, so the set the run reports is the same set.</p>
     */
    static final class RefusedCandidate {
        private final String said;
        /** The address the activation ran at, or null when {@code said} is
         * the whole reason. */
        private final OccurrenceAddress observed;
        /** Which node this run attributed the candidate to, as the sentence
         * states it, or {@code ""} where the refusal states no node.  Short
         * enough to render where it is read; the address is not. */
        private final String attribution;
        private final String thread;

        private RefusedCandidate(String said, OccurrenceAddress observed,
                                 String attribution) {
            this.said = safe(said);
            this.observed = observed;
            this.attribution = safe(attribution);
            this.thread = Thread.currentThread().getName();
        }

        /** A candidate refused on its address, stated against {@code said}. */
        static RefusedCandidate onAddress(String said,
                                          OccurrenceAddress observed,
                                          SourceRef activationSource) {
            return new RefusedCandidate(said, observed,
                    attribution(activationSource == null ? ""
                            : activationSource.key()));
        }

        /** A candidate refused on something that is not its address. */
        static RefusedCandidate stated(String said,
                                       SourceRef activationSource) {
            return new RefusedCandidate(said, null,
                    attribution(activationSource == null ? ""
                            : activationSource.key()));
        }

        /** The same, where the refusal itself names where it ran. */
        static RefusedCandidate stated(String said) {
            return new RefusedCandidate(said, null, "");
        }

        /**
         * One refused candidate, as a sentence a reader can act on.
         *
         * <p>Two facts every refusal owes and neither of which it carried:
         * the thread the candidate ran on -- filed when it ran -- and a
         * difference that is actually stated.  A row whose difference was
         * empty read as "matching root:  (attributed to X)", which is the
         * shape 11741's balancer#3 and 17897's dn0#1 were reported in: the
         * address matched and something else refused it, and the row said
         * neither half out loud.  Both halves are always stated now --
         * {@link #difference} names "the two addresses do not differ" rather
         * than nothing, and every caller states a {@code said} -- so the
         * arm that substituted a sentence for an empty one is gone.</p>
         */
        String render(RuntimeTask task) {
            String stated = (observed == null ? said
                    : said + ": " + task.addressDifference(observed))
                    + attribution;
            return stated.trim() + " [thread=" + thread + "]";
        }

        @Override
        public boolean equals(Object value) {
            if (this == value) return true;
            if (!(value instanceof RefusedCandidate)) return false;
            RefusedCandidate other = (RefusedCandidate) value;
            return said.equals(other.said)
                    && thread.equals(other.thread)
                    && attribution.equals(other.attribution)
                    && (observed == null ? other.observed == null
                    : observed.equals(other.observed));
        }

        @Override
        public int hashCode() {
            return Objects.hash(said, thread, attribution, observed);
        }
    }

    /** Marks durable evidence without clearing a newer live candidate. */
    synchronized void markOccurrenceClaimed(RuntimeTask task) {
        Integer index = slots.get(task);
        if (index != null) occurrenceClaimed[index] = true;
    }

    /**
     * Resolves an occurrence-specific instrumentation hook to the stable
     * region entry shared by every sibling hook at that Java method.
     *
     * <p>An index lookup: the answer belongs to the {@code
     * (instrumentationSelector, rootMethod)} pair, so it is computed on the
     * first entry at that hook and read afterwards ({@link
     * #rootHookGroups}).</p>
     */
    synchronized RootHookGroup rootHookGroup(
            String instrumentationSelector, String rootMethod) {
        String hook = safe(instrumentationSelector) + "\n" + safe(rootMethod);
        RootHookGroup known = rootHookGroups.get(hook);
        if (known != null) return known;
        RootHookGroup resolved = resolveRootHookGroup(instrumentationSelector,
                rootMethod);
        rootHookGroups.put(hook, resolved);
        return resolved;
    }

    private RootHookGroup resolveRootHookGroup(
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
        String hook = safe(instrumentationSelector) + "\n" + safe(rootMethod);
        RootHookGroup known = loopRootHookGroups.get(hook);
        if (known != null) return known;
        RootHookGroup resolved = resolveLoopRootHookGroup(
                instrumentationSelector, rootMethod);
        loopRootHookGroups.put(hook, resolved);
        return resolved;
    }

    private RootHookGroup resolveLoopRootHookGroup(
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
    synchronized Map<String, Integer> addressLoopRootInvocation(
            String loopRootHookGroupKey, String rootMethod,
            Object receiver, Object[] rootArguments,
            long enclosingInvocationEvent) {
        SourceRef registeredReceiverSource =
                RuntimeTraceContext.sourceFor(receiver);
        // Where this activation ran, by the one function the recorder
        // stamped it with and the planner counted it by.
        SourceRef activationSource =
                RuntimeTraceContext.activationSource(receiver);
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        Map<String, Integer> admitted = new LinkedHashMap<>();
        // An activation the recording never saw is not a candidate here
        // either.  The counting pass above skipped it, so looking its
        // ordinal up would answer null and the run would report "invocation
        // null instead of 1" -- a comparison against an ordinal nobody
        // assigned, rather than the plain fact that this activation is
        // outside the window.
        if (!RuntimeTraceContext.recordingWindowOpen()) {
            return admitted;
        }
        ObservedAddresses observedAddresses = new ObservedAddresses();
        for (RuntimeTask task : tasks) {
            if (!task.loopBodyRoot
                    || !task.loopRootHookGroupKey().equals(
                    safe(loopRootHookGroupKey))
                    || !compatibleRoot(task.rootMethod, rootMethod,
                    task.rootContextSelector,
                    task.enclosingRootArgumentSelector,
                    receiver, rootArguments)
                    || !sourceMismatch(task,
                    registeredReceiverSource,
                    context).isEmpty()) {
                continue;
            }
            OccurrenceAddress observed = observedAddresses.of(task,
                    activationSource);
            // The whole address, and nothing standing in for it.  A
            // non-loop root publishes one occurrence and its unique OUT
            // anchor confirms the node before that publication, so entry may
            // defer a missing registration to it; an enclosing loop root
            // decides which occurrence a whole SEQUENCE of bodies belongs
            // to, and there the deferral was not deferring the node, it was
            // replacing k.  Any invocation under the planned request was
            // admitted to any address, which is how one occurrence came to
            // own two enclosing invocations.
            if (!task.acceptsRootInvocation(observed)) {
                task.noteUnaddressedCandidate(RefusedCandidate.onAddress(
                        "matching enclosing root", observed,
                        activationSource));
                continue;
            }
            // One occurrence, one enclosing activation.  The bodies of
            // occurrence k are the bodies of the invocation admitted for k;
            // a later invocation of the same region on the same node is the
            // next k and belongs to the task addressed there, never to this
            // one.  Nothing said so, and on hdfs-11741 lane11741f
            // REGION.2392e4b7...#5 published eight loop bodies -- #a1..#a6
            // from an enclosing call on IPC Server handler 8 and #a7,#a8
            // from another on handler 2 -- while the tasks addressed #1 and
            // #4, the two other balancer-driven invocations, were never
            // answered.  Same defect class as the provisional-admission
            // bucket: bookkeeping that lets one occurrence absorb another
            // activation.
            if (!task.claimsEnclosingInvocation(enclosingInvocationEvent)) {
                task.noteUnaddressedCandidate(RefusedCandidate.stated(
                        "a second enclosing invocation of this region: "
                                + "occurrence " + task.occurrenceId
                                + " already runs the bodies of entry event "
                                + task.enclosingInvocationEvent()
                                + ", so this entry is another activation",
                        activationSource));
                continue;
            }
            // Which of this invocation's admissions this task is, not an
            // ordinal of its address: identity v3 has none, and what the
            // enclosing loop root needs to know is that this task's bodies
            // are charged here and in what order they were admitted.
            admitted.put(task.taskId, admitted.size() + 1);
        }
        return admitted;
    }

    /** Claims at most one open task for this root invocation. */
    synchronized RuntimeTask select(String rootHookGroupKey,
                                            String rootMethod,
                                            Object receiver,
                                            Object[] rootArguments) {
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

        // Same rule as the counting pass: outside the recording window
        // there is no candidate to select.
        if (!RuntimeTraceContext.recordingWindowOpen()) return null;
        ObservedAddresses observedAddresses = new ObservedAddresses();
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
                    receiver, rootArguments)) {
                continue;
            }
            if (!sourceMismatch(task, registeredReceiverSource,
                    context).isEmpty()) continue;
            OccurrenceAddress observed = observedAddresses.of(task,
                    activationSource);
            if (!task.acceptsRootInvocation(observed)) {
                // Said out loud, as the loop-body path already says it.  A
                // non-loop root that ran and was refused on its address was
                // refused in silence, and the end of the run then reported
                // the task as ROOT_NEVER_EXECUTED -- "no compatible
                // activation was offered" -- which is a statement about the
                // region never running.  On hdfs-17899 bug2 that is
                // REGION.763d087e on target-dn: activations of
                // Client$Connection.sendRpcRequest were offered and refused
                // on the ordinal, and the row said the root never executed.
                task.noteUnaddressedCandidate(RefusedCandidate.onAddress(
                        "matching root", observed, activationSource));
                continue;
            }
            if (candidateLive[index]) continue;
            candidateLive[index] = true;
            return task;
        }
        return null;
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
     * The address one root entry ran at, computed once for that entry.
     *
     * <p>{@link RuntimeTask#observedAddress} is {@code Identity.occurrence}:
     * it reads the frames standing on this thread, folds them into an
     * execution index (one digest per frame) and digests the address.  Its
     * answer depends on the entry -- the thread's frames and the causal
     * context it stands in -- and on the (lifecycle, region) the task names,
     * and admission asked it once per CANDIDATE.  The key is exactly what the
     * answer depends on, so this is a memo and not a narrowing: {@link
     * #select} has already matched the root hook group, which names the
     * region, and {@link #countedLifecycle} answers the same lifecycle for
     * every task whose planned node declares an epoch.</p>
     */
    static final class ObservedAddresses {
        private final Map<String, OccurrenceAddress> byTarget =
                new LinkedHashMap<String, OccurrenceAddress>();

        OccurrenceAddress of(RuntimeTask task, SourceRef activationSource) {
            String lifecycle = countedLifecycle(task, activationSource);
            String target = lifecycle + "\n" + task.regionId;
            if (byTarget.containsKey(target)) return byTarget.get(target);
            OccurrenceAddress observed = task.observedAddress(lifecycle);
            byTarget.put(target, observed);
            return observed;
        }
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
    static String attribution(String activationSourceKey) {
        String key = safe(activationSourceKey);
        if (key.isEmpty()
                || RuntimeTraceContext.UNREGISTERED_SOURCE.key().equals(key)) {
            return " (this run attributed the activation to no node, so it"
                    + " counts in the unregistered source)";
        }
        return " (attributed to " + key + ")";
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
        if (OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
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
            Object receiver, Object[] rootArguments) {
        if (!safe(selectedMethod).equals(safe(actualMethod))) return false;
        if (!context.matches(receiver)) {
            return false;
        }
        return !arguments.present || arguments.matches(rootArguments);
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
        /**
         * The class a receiver-scoped root hook stands on, or {@code ""}.
         *
         * <p>The one thing about "what this activation was reached under"
         * that selection reads, and it is a DECLARED fact of the plan's
         * selector rather than a circumstance of the run.  It is not a
         * matching rule either: it decides which invocations are offered as
         * candidates at all, the way an instrumentation scope does, and it
         * cannot distinguish two activations of one address.</p>
         *
         * <p>The RPC exchange, the request api, how the recording
         * established the source, and the thread the activation ran on used
         * to travel beside it and each grew its own rule for when it might
         * veto.  They are gone: an occurrence IS its address
         * (IDENTITY-V3 SS1), and a thread name in particular is a timing
         * fact no replay can be held to.</p>
         */
        private final String receiverRuntimeClass;

        private RootContextSelector(String receiverRuntimeClass,
                                    String sourceKey,
                                    int invocationOrdinal) {
            this.sourceKey = safe(sourceKey);
            this.invocationOrdinal = invocationOrdinal;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = optionalString(selector, "kind");
            boolean global = "GLOBAL_INVOCATION".equals(kind);
            String receiverClass = optionalString(selector, "receiverClass");
            JsonObject anchor = object(selector, "causalAnchor");
            String sourceKey = optionalString(anchor, "sourceKey");
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
                    || !"RECEIVER_CONTEXT".equals(kind))
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
            return new RootContextSelector(global ? "" : receiverClass,
                    sourceKey, invocationOrdinal);
        }

        /** Whether this root invocation is a candidate for the occurrence. */
        private boolean matches(Object receiver) {
            return receiverRuntimeClass.isEmpty()
                    || receiver != null && receiverRuntimeClass.equals(
                            receiver.getClass().getName());
        }

        /**
         * Why the candidate that just ran is not the addressed occurrence, or
         * {@code ""} when it is.
         */
        String unconfirmed(Set<String> attributedSourceKeys) {
            if (attributedSourceKeys.isEmpty()) {
                // Nothing attributed this activation to any node, so it is
                // the UNREGISTERED source's -- the third arm of the one
                // attribution function, which the planner runs too.  That
                // is an occurrence, and it is addressed there; it is never
                // the planned node's next k.
                //
                // Answering "" for every anchor was the planned-node
                // fallback, deleted at entry and living on here: on
                // lane11741d it let activations on IPC handler threads --
                // threads the recording never attributes to dn0 -- take
                // dn0's k, so the five genuine activations on main were
                // numbered 1, 3, 5, 7 and the addressed activation 4 was
                // consumed by an activation that was nobody's.
                return OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
                        sourceKey) ? ""
                        : "occurrence ran on "
                        + OccurrenceBinding.UNREGISTERED_SOURCE_KEY
                        + " (nothing attributed it to any node), but its"
                        + " anchor names " + sourceKey;
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
            return sourceKey + "/invocation=" + invocationOrdinal;
        }

        /**
         * Whether the anchored source was never registered in this run, which
         * makes the address unsatisfiable here rather than merely unmatched.
         */
        private boolean anchorSourceNeverExisted() {
            return !OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(sourceKey)
                    && !RuntimeTraceContext.sourceIdentityRegistered(sourceKey);
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
        final LoopBoundPolicy loopBound;
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
        /**
         * The one enclosing invocation whose loop bodies this occurrence is.
         *
         * <p>Its entry event, or {@code 0} before the first admission.  An
         * occurrence is (node, epoch, region, k-th activation), and the
         * activation is the enclosing call: its bodies are {@code #k#aN}.  A
         * second enclosing invocation -- another thread, another entry event
         * -- is the next k and belongs to the task addressed there.</p>
         */
        private long enclosingInvocationEvent;
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
        final String topologyEpoch;
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
        /** Strict phase lookup; phase ids never alias source ids. */
        final Map<String, ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhasesById = new LinkedHashMap<>();
        /** Every protocol input this occurrence attaches from the VM. */
        final Set<String> attachPortIds = new LinkedHashSet<>();
        /**
         * Activations that ran as candidates for this address and were not the
         * addressed occurrence, and every distinct reason they were not.
         */
        int unaddressedCandidates;
        final Set<RefusedCandidate> unaddressedReasons = new LinkedHashSet<>();

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
            this.address = parseAddress(this.occurrenceId);
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
            if (this.loopBodyRoot && this.address == null) {
                throw new IllegalArgumentException(
                        "ROOT_LOOP_OCCURRENCE_UNADDRESSED: loop-body task "
                                + this.taskId + " plans occurrence "
                                + this.occurrenceId + ", which names no "
                                + "occurrence");
            }
            this.rootLoopMethod = task.rootLoopMethod();
            this.rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            // The root loop's declared K_L (its loopSiteId is the key its
            // bound is under); an undeclared site inherits the default.
            this.loopOccurrenceBudget = this.loopBound
                    .maxBackedgeTraversals(task.rootLoopSiteId());
            this.capturesTargetReach =
                    task.goalKind().capturesTargetReach();
            // The plan names the propagation ledger every task of this
            // invocation shares: ConcolicScheduler stamps the seed replay,
            // PathReplayTaskFactory stamps each flip replay. A row that
            // names none is a plan no scheduler wrote, and the importer
            // refuses its results by name (CONCOLIC_RESULT_REPLAY_GROUP_MISSING).
            this.replayGroupId = optionalString(task.json(),
                    "replayGroupId");
            this.topologyEpoch = optionalString(task.json(), "topologyEpoch");
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
            JsonObject targetBranch = object(task.json(), "targetBranch");
            this.targetBranchSite = optionalString(targetBranch, "siteId");
            this.targetBranchOccurrence = optionalInteger(targetBranch,
                    "occurrence", -1);
            this.targetBranchRequiredOutcome = targetRequiredOutcome(
                    targetBranch, targetBranchSite);
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
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


        static String handoffKey(String portId, boolean exporting) {
            return (exporting ? "EXPORT\n" : "ATTACH\n") + safe(portId);
        }

        private final Set<String> requestContexts = new LinkedHashSet<>();

        /**
         * Records that one candidate ran and was not this address, as the
         * facts of the refusal rather than a sentence about them.
         */
        synchronized void noteUnaddressedCandidate(
                RefusedCandidate refusal) {
            unaddressedCandidates++;
            unaddressedReasons.add(refusal);
            registerRunTotalsHook();
        }

        /**
         * Records which request a matching root entered, when it is not the
         * planned one.  Kept so the run can say where an admitted occurrence
         * was reached from; it never withholds the address.
         */
        synchronized void noteRequestContext(String enteredUnder) {
            requestContexts.add(safe(enteredUnder));
        }

        /**
         * The run's one statement about an address nothing answered.
         *
         * <p>Where every refusal this address met is rendered, once: the
         * facts were filed as each candidate ran ({@link RefusedCandidate}).
         * Called with the plan's monitor released, because rendering digests
         * addresses and reads the endpoints the run filed.</p>
         */
        synchronized String unansweredAddress() {
            boolean neverExisted = rootContextSelector
                    .anchorSourceNeverExisted();
            List<String> said = new ArrayList<String>(
                    unaddressedReasons.size());
            for (RefusedCandidate refusal : unaddressedReasons) {
                said.add(refusal.render(this));
            }
            return unaddressedCandidates + " compatible activation(s) did "
                    + "not answer the addressed occurrence; " + said
                    + (neverExisted
                    ? "; " + rootContextSelector.describe()
                    + " was never registered in this run" : "");
        }

        /** Body entries this loop may run before the replay is cut. */
        int maxLoopBodies(String loopId) {
            return LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES;
        }

        /**
         * Counts one activation of this address against its published set.
         *
         * <p>Not an identity: the occurrence an activation is IS its
         * execution index (IDENTITY-V3).  This is the count a bounded
         * loop-body region's occurrence budget is spent against, and
         * nothing else reads it.</p>
         */
        synchronized void claimActivation() {
            publishedActivations++;
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

        /**
         * Binds this occurrence to one enclosing invocation, and answers
         * whether {@code entryEvent} is it.
         *
         * <p>The first enclosing invocation admitted for this address owns
         * it for the whole replay.  There is no releasing: an occurrence
         * that ended is still the k-th activation, and a later invocation of
         * the same region is the (k+1)-th, which some other task addresses
         * -- or which nothing does, and then the row says so by name.</p>
         */
        synchronized boolean claimsEnclosingInvocation(long entryEvent) {
            if (entryEvent <= 0L) return false;
            if (enclosingInvocationEvent == 0L) {
                enclosingInvocationEvent = entryEvent;
                return true;
            }
            return enclosingInvocationEvent == entryEvent;
        }

        /** The enclosing invocation this occurrence's bodies come from. */
        synchronized long enclosingInvocationEvent() {
            return enclosingInvocationEvent;
        }

        /** Claims the one bounded-cut marker write for this region. */
        synchronized boolean claimLoopBoundCutMarker() {
            if (loopBoundCutRecorded) return false;
            loopBoundCutRecorded = true;
            return true;
        }

        /** Gives back the count of an activation that published nothing. */
        synchronized void releaseActivation() {
            if (publishedActivations > 0) publishedActivations--;
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
         * The address this activation ran at: the lifecycle the run
         * attributed to it and the k it took in that lifecycle's bucket.
         *
         * <p>Unnamed when the bucket handed out no ordinal, which is an
         * activation outside the recording window; an unnamed address
         * matches nothing rather than half-matching on the node.</p>
         */
        OccurrenceAddress observedAddress(String lifecycle) {
            // Identity.occurrence, and nothing of this class's own: the
            // address a replay computes here is the same function, over the
            // same frame stack and scope, that the recorder ran on the stock
            // JDK and wrote onto the activation the plan was built from.
            // `open` is false -- admission asks the question before the
            // session publisher opens the region, and opening it twice would
            // move the base every endpoint inside is indexed from.
            //
            // I1, the fold rule: this root's entry hook has already run, and
            // when it FOLDED -- a declared region entered synchronously
            // inside another region's occurrence opens none of its own
            // (Identity#fold) -- the activation starting here is an
            // activation of the occurrence it folded into.  That is the
            // occurrence the plan names, because the recording folded at the
            // same entry in the same function, so admission compares the two
            // passes' answers and not a fresh address minted under this
            // task's own region id, which no folded activation ever carries.
            OccurrenceAddress folded = edu.uva.liftlab.graphchecker.runtime
                    .Identity.foldedOccurrence();
            if (folded != null) return folded;
            return edu.uva.liftlab.graphchecker.runtime.Identity.occurrence(
                    safe(lifecycle).isEmpty() ? sourceKey : lifecycle,
                    regionId, false);
        }

        /**
         * Whether this activation is the addressed occurrence.
         *
         * <p>The whole address the occurrence id states -- node, epoch,
         * region, request family and k -- against the whole address this
         * activation ran at, read from the occurrence id every other stage
         * reads it from.  Comparing the k alone let a task planned for one
         * node answer another node's first activation of the same region.</p>
         *
         * <p>And nothing else.  Two arms stood here in turn and both
         * replaced the address rather than refining it: the message an
         * activation arrived on, which refused activations that agreed on
         * every component (11741's balancer#3 and #7, 17897's dn0#1); and a
         * unique planner-authored OUT anchor, which admitted any invocation
         * under the planned request to any k of that region.  An occurrence
         * is its address.</p>
         */
        /** The planned address, or null when the id names no occurrence. */
        private static OccurrenceAddress parseAddress(String occurrenceId) {
            String value = safe(occurrenceId);
            if (value.isEmpty()) return null;
            try {
                return OccurrenceAddress.parse(value);
            } catch (RuntimeException notAnAddress) {
                return null;
            }
        }

        boolean acceptsRootInvocation(OccurrenceAddress observed) {
            return address != null && observed != null
                    && address.id().equals(observed.id());
        }

        /**
         * Why {@code observed} is not this task's occurrence.
         *
         * <p>The one component that differs, then both addresses rendered.
         * A v3 address is a node, a region, a causal context and an
         * execution index; the refusal states which of the four parted and
         * where ({@link #difference}), and still carries the two whole
         * addresses behind it.</p>
         *
         * <p>And, when the two differ in their causal anchor, the
         * COMPONENTS behind each anchor digest: which occurrence sent the
         * message, at which transport site, the k-th event of that
         * occurrence there, and the attempt -- the four inputs the one mint
         * was given, read back from the producer it filed ({@link
         * Interactions#components}).  Two digests that differ say only
         * that; on hdfs-17960 they agreed on everything but one number and
         * the row did not say so.  An anchor this run never minted is
         * stated as that, which is itself the finding.</p>
         */
        String addressDifference(OccurrenceAddress observed) {
            if (address == null) return "the task plans no occurrence";
            if (observed == null) {
                return "the activation ran where this run cannot name it";
            }
            return difference(address, observed)
                    + "planned " + address.render() + anchorComponents(address)
                    + ", ran at " + observed.render()
                    + anchorComponents(observed);
        }

        /**
         * Which component of the address differs, said before the addresses.
         *
         * <p>A v3 address is a node, a region, a causal context and an
         * execution index, and printing two of them leaves the reader to
         * diff two multi-kilobyte strings: the 13 refusals of hdfs-17960
         * verification #3 differed in ONE number -- frame 5 of 8, the
         * {@code applyEditLogOp} call site, planned iteration 3 and ran 0 --
         * inside ~2500 characters that were otherwise character-identical,
         * and finding that out took a script. The components are compared
         * outermost-first (node, region, context, index) and each differing
         * one is named; an index names the frame's position, its call site,
         * and the two iterations. Nothing is summarized away: the two whole
         * addresses still follow.</p>
         */
        private static String difference(OccurrenceAddress planned,
                OccurrenceAddress observed) {
            List<String> differ = new ArrayList<String>();
            if (!planned.node().equals(observed.node())) {
                differ.add("the node (planned " + planned.node().render()
                        + ", ran " + observed.node().render() + ")");
            }
            if (!planned.regionId().equals(observed.regionId())) {
                differ.add("the region (planned " + planned.regionId()
                        + ", ran " + observed.regionId() + ")");
            }
            if (!planned.context().equals(observed.context())) {
                differ.add(contextDifference(planned.context(),
                        observed.context()));
            }
            String index = indexDifference(planned.index(), observed.index());
            if (!index.isEmpty()) differ.add(index);
            if (differ.isEmpty()) {
                // Equal addresses reach here only when admission refused on
                // something that is not the address; say that, do not invent
                // a difference.
                return "the two addresses do not differ; ";
            }
            StringBuilder said = new StringBuilder("differs in ");
            for (int at = 0; at < differ.size(); at++) {
                if (at > 0) said.append(at + 1 == differ.size()
                        ? " and " : ", ");
                said.append(differ.get(at));
            }
            return said.append("; ").toString();
        }

        /** The frame the two indexes part at, or {@code ""} when equal. */
        private static String indexDifference(ExecutionIndex planned,
                ExecutionIndex observed) {
            List<Frame> plannedFrames = planned.frames();
            List<Frame> observedFrames = observed.frames();
            if (plannedFrames.size() != observedFrames.size()) {
                return "its execution index depth (planned "
                        + plannedFrames.size() + " frames, ran "
                        + observedFrames.size() + ")";
            }
            int first = -1;
            int differing = 0;
            for (int at = 0; at < plannedFrames.size(); at++) {
                if (plannedFrames.get(at).equals(observedFrames.get(at))) {
                    continue;
                }
                differing++;
                if (first < 0) first = at;
            }
            if (first < 0) return "";
            Frame plan = plannedFrames.get(first);
            Frame ran = observedFrames.get(first);
            String where = "frame " + first + " of " + plannedFrames.size();
            String said = plan.callSite().equals(ran.callSite())
                    ? where + ", " + plan.callSite() + ", at iteration "
                    + ran.iteration() + " and not the planned "
                    + plan.iteration()
                    : where + "'s call site (planned " + plan.callSite()
                    + ", ran " + ran.callSite() + ")";
            return differing == 1 ? said
                    : said + " (and " + (differing - 1) + " further frame"
                    + (differing == 2 ? "" : "s") + " below it)";
        }

        /**
         * Which part of the causal context differs.
         *
         * <p>Two anchors are two digests, so the difference is stated over
         * the four inputs the mint was given, read back from the producer
         * this run filed ({@link Interactions#endpoint}).</p>
         */
        private static String contextDifference(CausalContext planned,
                CausalContext observed) {
            if (!(planned instanceof CausalContext.Anchor)
                    || !(observed instanceof CausalContext.Anchor)) {
                return "its causal context (planned " + planned.render()
                        + ", ran " + observed.render() + ")";
            }
            CausalContext.Anchor plan = (CausalContext.Anchor) planned;
            CausalContext.Anchor ran = (CausalContext.Anchor) observed;
            if (!plan.rpcSite().equals(ran.rpcSite())) {
                return "its anchor's transport site (planned "
                        + plan.rpcSite() + ", ran " + ran.rpcSite() + ")";
            }
            Endpoint plannedEnd = InteractionRefusals.endpoint(
                    plan.producerEndpointId());
            Endpoint ranEnd = InteractionRefusals.endpoint(ran.producerEndpointId());
            if (plannedEnd == null || ranEnd == null) {
                return "its causal anchor (planned "
                        + plan.producerEndpointId()
                        + (plannedEnd == null ? ", which no message of this "
                        + "run minted" : "") + "; ran "
                        + ran.producerEndpointId()
                        + (ranEnd == null ? ", which no message of this run "
                        + "minted" : "") + ")";
            }
            if (!plannedEnd.occurrence().equals(ranEnd.occurrence())) {
                return "its anchor's producer occurrence (planned "
                        + plannedEnd.occurrence().render() + ", ran "
                        + ranEnd.occurrence().render() + ")";
            }
            if (!plannedEnd.site().equals(ranEnd.site())) {
                return "its anchor's producer site (planned "
                        + plannedEnd.site() + ", ran " + ranEnd.site() + ")";
            }
            if (!plannedEnd.siteIndex().equals(ranEnd.siteIndex())) {
                return "its anchor's producer site index (planned "
                        + plannedEnd.siteIndex().render() + ", ran "
                        + ranEnd.siteIndex().render() + ")";
            }
            if (plannedEnd.attempt() != ranEnd.attempt()) {
                return "its anchor's producer attempt (planned "
                        + plannedEnd.attempt() + ", ran "
                        + ranEnd.attempt() + ")";
            }
            return "its causal anchor's digest over components that agree "
                    + "(planned " + plan.producerEndpointId() + ", ran "
                    + ran.producerEndpointId() + ")";
        }

        /** The producer endpoint one address's anchor is a digest of. */
        private static String anchorComponents(OccurrenceAddress address) {
            if (!(address.context() instanceof CausalContext.Anchor)) {
                return "";
            }
            String producer = ((CausalContext.Anchor) address.context())
                    .producerEndpointId();
            String components = InteractionRefusals.components(producer);
            return " [anchor " + producer + " = "
                    + (components.isEmpty()
                    ? "no message of this run minted it" : components) + "]";
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

        /**
         * The arm of the declared target branch that reaches the annotated
         * throw, as the task states it.
         *
         * <p>One authority, {@code causynth.SiteControlDependence}, computes
         * it in ANALYZE, publishes it on the static scope map's TARGET_SITE
         * row and the scheduler carries it onto {@code targetBranch}.  It
         * used to be searched for again here, across the task's whole branch
         * catalog, by matching the site and its selected occurrence.</p>
         */
        static boolean targetRequiredOutcome(JsonObject targetBranch,
                                             String targetSite) {
            if (safe(targetSite).isEmpty()) return false;
            JsonElement encoded = targetBranch == null ? null
                    : targetBranch.get("requiredOutcome");
            if (encoded == null || !encoded.isJsonPrimitive()
                    || !encoded.getAsJsonPrimitive().isBoolean()) {
                throw new IllegalArgumentException(
                        "target branch states no fatal arm: " + targetSite);
            }
            return encoded.getAsBoolean();
        }

    }
}
