package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * States what a shared container held before the replayed region selected it.
 *
 * <p>Selecting a whole-state carrier roots the container's state, and that
 * root is opaque: the VM did not watch the members that were already there,
 * so the INITIAL version alone leaves a solver free to answer "absent" for
 * every key. The VM can publish the contents instead - a {@code
 * SNAPSHOT_BASE} with one {@code PUT} per map entry or one {@code APPEND} per
 * list element - but it never iterates a Java collection itself. The walk is
 * this class's job, and it runs immediately before the selection and so
 * before the region's first write to the container.</p>
 *
 * <p>Fidelity is the whole point: a snapshot that states members the
 * container did not hold is a false premise about the recorded execution, and
 * a formula that carries one is unsatisfiable for a reason the program never
 * had. Everything here therefore refuses rather than guesses - an
 * unrecognized class, a container past the entry bound, a walk that raced a
 * concurrent write - and says so as an {@code INITIAL_SNAPSHOT_SKIPPED} row,
 * leaving the honest opaque root in place.</p>
 */
final class InitialContainerSnapshot {

    /** Telemetry event naming one container this run declined to state. */
    static final String SKIPPED_EVENT = "INITIAL_SNAPSHOT_SKIPPED";

    /**
     * Telemetry event naming one container whose base was recovered from the
     * mutation history the recorder had already watched.
     *
     * <p>Its own row, not a {@link #STATED_EVENT} one, because the two are
     * different facts about the run: a stated container was untouched when it
     * was offered, a rebased one had already been changed inside a recording
     * region and the engine had to undo that change to say what it started
     * with. Both publish a base; only the second says the campaign is
     * selecting carriers after the workload has begun mutating them.</p>
     */
    static final String REBASED_EVENT = "INITIAL_SNAPSHOT_REBASED";

    /**
     * Telemetry event naming one container this run did state.
     *
     * <p>A declined container has always said so; an accepted one said
     * nothing, and the two silences are indistinguishable in a corpus. So
     * "this campaign published no snapshot at all" and "this campaign
     * snapshotted everything it was offered" read the same, and separating
     * them meant scanning every result row of every replay for an absent
     * field. This row is the other half of the vocabulary: what was stated,
     * for which container, how many members, and under what bound.</p>
     */
    static final String STATED_EVENT = "INITIAL_SNAPSHOT_STATED";

    /** The VM's own bound, read from the same property the VM parses. */
    static final String BOUND_PROPERTY =
            "causynth.concolic.initial.snapshot.max";
    static final int DEFAULT_MAX_ENTRIES = 64;

    /** Snapshot kinds of {@code System.snapshotContainerExpression}. */
    static final int KIND_INDEXED = 0;
    static final int KIND_ASSOCIATIVE = 1;

    // What the VM did with one offer.  These mirror
    // ConcolicMngr::InitialSnapshotAnswer and cross the JNI boundary as the
    // int the native method answers.
    //
    // The call used to answer a bool, and three of these answered the same
    // `true`: INSTALLED, KEPT_EXISTING_HISTORY and REFUSED_OVER_BOUND.  This
    // side mapped all three to "installed", so a carrier whose INITIAL
    // version carried no base at all was recorded as carrying a complete one
    // - and a free INITIAL arm is a whole container the solver has to search
    // over, which is what turned one Boolean root into twelve 180 s timeouts
    // on the recorded HDFS-17960 corpus.

    /** Nothing was stated and nothing is claimed. */
    static final int NOT_SELECTABLE = 0;
    /** The chain was installed; the state now states the content. */
    static final int INSTALLED = 1;
    /** A recorded mutation history was kept; its base is unrecoverable. */
    static final int KEPT_EXISTING_HISTORY = 2;
    /** The content held more members than the VM's entry bound admits. */
    static final int REFUSED_OVER_BOUND = 3;
    /** The recorded history was rebuilt on a recovered, stated base. */
    static final int REBASED_UNDER_HISTORY = 4;
    /** An earlier offer already stated this container's content. */
    static final int ALREADY_STATED = 5;

    // The declined reasons.  One vocabulary, because a reader of the
    // telemetry has to be able to tell "held nothing" from each separate way
    // of not having said what it held.
    static final String NOT_A_WHOLE_STATE_CARRIER =
            "not a whole-state carrier";
    static final String CLASS_NOT_ALLOWLISTED = "class not allowlisted";
    static final String OVER_BOUND = "over bound";
    static final String CONTENT_RACED = "content changed while it was read";
    static final String VM_DECLINED = "the VM declined the snapshot";
    // The VM's own answers, one reason each.  A single "the VM said no" hides
    // exactly the distinction this call was changed to make.
    static final String VM_KEPT_HISTORY =
            "the recorded mutation history has no recoverable base";
    static final String VM_OVER_BOUND =
            "the VM refused the content over its own entry bound";
    static final String VM_NOT_SELECTABLE =
            "the VM does not carry this container's state";

    /**
     * Concrete classes whose contents this runtime knows how to enumerate
     * exactly, in the order the container itself iterates them.
     *
     * <p>A map is a set of entries in the SMT lowering, so its own iteration
     * order is faithful whatever it is; a list's iteration order is its index
     * order, which the indexed algebra depends on.</p>
     */
    private static final Set<String> ASSOCIATIVE_CLASSES = names(
            "java.util.HashMap", "java.util.LinkedHashMap",
            "java.util.TreeMap", "java.util.concurrent.ConcurrentHashMap",
            "java.util.Hashtable");
    private static final Set<String> INDEXED_CLASSES = names(
            "java.util.ArrayList", "java.util.LinkedList",
            "java.util.concurrent.CopyOnWriteArrayList",
            "java.util.ArrayDeque");

    /**
     * The subset whose mutations the VM's container algebra keeps versioned
     * ({@code SymMap}/{@code SymList} targets, which is also what
     * {@code ContainerSupport::whole_state_selectable} admits).
     *
     * <p>Snapshotting anything outside it would install a constant nothing
     * ever updates: faithful at selection and false at the first unwatched
     * put. That is exactly the unfaithful snapshot that makes a whole formula
     * unsatisfiable, so those classes are declined by name.</p>
     */
    private static final Set<String> VM_VERSIONED_CLASSES = names(
            "java.util.HashMap", "java.util.LinkedHashMap",
            "java.util.ArrayList", "java.util.ArrayDeque");

    /** Delegating views: the backing container decides both questions. */
    private static final String SYNCHRONIZED_WRAPPER =
            "java.util.Collections$Synchronized";
    private static final String UNMODIFIABLE_WRAPPER =
            "java.util.Collections$Unmodifiable";

    /**
     * Containers this JVM has already offered a snapshot for.
     *
     * <p>The chain may only be installed while the recorded INITIAL version
     * does not exist yet. A second selection of the same container - another
     * activation, another thread - would install a chain the already-recorded
     * INITIAL version does not describe, so each container is offered exactly
     * once. Identity, never equality: a map's {@code equals} is its contents,
     * which is the one thing this class must not consult.</p>
     */
    private static final Set<Object> OFFERED = Collections.synchronizedSet(
            Collections.newSetFromMap(new IdentityHashMap<Object, Boolean>()));

    /**
     * Containers already reported as carried by a pointer rather than whole.
     *
     * <p>Kept apart from {@link #OFFERED} on purpose: the same container can
     * be selected both ways, and a pointer selection must not consume the one
     * chance the whole-state selection has to state the content.</p>
     */
    private static final Set<Object> POINTER_ONLY = Collections.synchronizedSet(
            Collections.newSetFromMap(new IdentityHashMap<Object, Boolean>()));

    private InitialContainerSnapshot() {
    }

    /**
     * The VM call, isolated so a test can observe exactly what was sent.
     *
     * <p>Answers one of the constants above, never a bool: which of the VM's
     * outcomes happened decides whether the INITIAL version has a base.</p>
     */
    interface Installer {
        int install(Object container, Object[] keys, Object[] values,
                    int kind) throws Exception;
    }

    /** What one attempt did, and why it did not do more. */
    static final class Outcome {
        /** The VM's answer, or {@link #NOT_SELECTABLE} if it was not asked. */
        final int answer;
        /**
         * Whether the container's INITIAL version now states its content.
         *
         * <p>Three of the VM's answers state it - an installed chain, a
         * history rebuilt on a recovered base, and a container an earlier
         * offer already stated - and every other answer leaves the content
         * unknown. Nothing here treats "the call returned" as "the content is
         * stated": that conflation is the defect this vocabulary exists to
         * remove.</p>
         */
        final boolean stated;
        /** Empty when nothing needed saying; a declined reason otherwise. */
        final String reason;
        final String detail;
        /** Members stated, or the count that was refused; -1 when unknown. */
        final int entries;

        private Outcome(int answer, boolean stated, String reason,
                        String detail, int entries) {
            this.answer = answer;
            this.stated = stated;
            this.reason = reason;
            this.detail = detail;
            this.entries = entries;
        }

        /** Whether this outcome is worth a telemetry row. */
        boolean declined() {
            return !stated && !reason.isEmpty();
        }

        /** The event a stated outcome is filed under. */
        String statedEvent() {
            return answer == REBASED_UNDER_HISTORY
                    ? REBASED_EVENT : STATED_EVENT;
        }
    }

    private static final Outcome SILENT =
            new Outcome(NOT_SELECTABLE, false, "", "", -1);

    private static Outcome declined(String reason, String detail,
                                    int entries) {
        return declined(NOT_SELECTABLE, reason, detail, entries);
    }

    private static Outcome declined(int answer, String reason, String detail,
                                    int entries) {
        return new Outcome(answer, false, reason, detail, entries);
    }

    /**
     * The outcome of one VM answer, with the content the walk handed over.
     *
     * <p>Each answer gets its own reason, so a corpus can be grepped for
     * which of them happened instead of being scanned for an absent field on
     * every version row.</p>
     */
    private static Outcome answered(int answer, String contentClass,
                                    int size) {
        switch (answer) {
            case INSTALLED:
            case ALREADY_STATED:
            case REBASED_UNDER_HISTORY:
                return new Outcome(answer, true, "", contentClass, size);
            case KEPT_EXISTING_HISTORY:
                return declined(answer, VM_KEPT_HISTORY, contentClass, -1);
            case REFUSED_OVER_BOUND:
                return declined(answer, VM_OVER_BOUND, contentClass, size);
            case NOT_SELECTABLE:
                return declined(answer, VM_NOT_SELECTABLE, contentClass,
                        size);
            default:
                // An answer this runtime does not know is not an answer it
                // may read as "stated": a newer VM may have added an outcome
                // that carries no base.
                return declined(answer, VM_DECLINED,
                        contentClass + " answered " + answer, size);
        }
    }

    /** The VM answer as a name, for a telemetry row a person reads. */
    static String answerName(int answer) {
        switch (answer) {
            case NOT_SELECTABLE: return "NOT_SELECTABLE";
            case INSTALLED: return "INSTALLED";
            case KEPT_EXISTING_HISTORY: return "KEPT_EXISTING_HISTORY";
            case REFUSED_OVER_BOUND: return "REFUSED_OVER_BOUND";
            case REBASED_UNDER_HISTORY: return "REBASED_UNDER_HISTORY";
            case ALREADY_STATED: return "ALREADY_STATED";
            default: return "UNKNOWN_" + answer;
        }
    }

    /**
     * Offers the VM the exact content of one container that is about to
     * become a whole-state carrier.
     *
     * @param installer   the VM entry point, absent on a stock JDK
     * @param container   the object the carrier selection will name
     * @param monitor     the lock the workload guards the content with, or
     *                    null to use the container itself
     * @param wholeState  whether this carrier carries the container's state
     *                    rather than the field that points at it
     */
    static Outcome install(Installer installer, Object container,
                           Object monitor, boolean wholeState) {
        if (container == null
                || !(container instanceof Map || container instanceof
                Collection)) {
            // Nothing with members: a scalar carrier has no initial content
            // to state, and saying so once per field read would be noise.
            return SILENT;
        }
        if (!wholeState) {
            // Said once per container: the same pointer carrier is selected
            // at every access, and the answer never changes.
            return POINTER_ONLY.add(container)
                    ? declined(NOT_A_WHOLE_STATE_CARRIER,
                    container.getClass().getName(), -1)
                    : SILENT;
        }
        if (!OFFERED.add(container)) return SILENT;
        if (installer == null) {
            return declined(VM_DECLINED,
                    "this VM has no snapshotContainerExpression", -1);
        }
        Object content = delegate(container);
        String contentClass = content.getClass().getName();
        boolean associative = content instanceof Map;
        if (!(associative ? ASSOCIATIVE_CLASSES : INDEXED_CLASSES)
                .contains(contentClass)
                || !VM_VERSIONED_CLASSES.contains(contentClass)) {
            return declined(CLASS_NOT_ALLOWLISTED, contentClass, -1);
        }
        // The lock the workload itself holds over this content, taken for
        // exactly the length of the walk.  BlockTokenSecretManager reaches
        // allKeys only from synchronized methods, so the monitor is the
        // declaring receiver and this thread usually already owns it.
        Object lock = monitor == null ? container : monitor;
        int bound = maxEntries();
        try {
            synchronized (lock) {
                int size = associative ? ((Map<?, ?>) content).size()
                        : ((Collection<?>) content).size();
                if (size > bound) {
                    return declined(OVER_BOUND,
                            size + " entries over the bound of " + bound,
                            size);
                }
                List<Object> keys = associative
                        ? new ArrayList<Object>(size) : null;
                List<Object> values = new ArrayList<Object>(size);
                if (associative) {
                    for (Map.Entry<?, ?> entry
                            : ((Map<?, ?>) content).entrySet()) {
                        keys.add(entry.getKey());
                        values.add(entry.getValue());
                    }
                } else {
                    for (Object element : (Collection<?>) content) {
                        values.add(element);
                    }
                }
                // A walk that saw a different number of members than the
                // container claimed states a content that never existed.
                if (values.size() != size) {
                    return declined(CONTENT_RACED,
                            "size " + size + " but " + values.size()
                                    + " members", values.size());
                }
                int answer = installer.install(container,
                        associative ? keys.toArray() : null,
                        values.toArray(),
                        associative ? KIND_ASSOCIATIVE : KIND_INDEXED);
                return answered(answer, contentClass, size);
            }
        } catch (Throwable failed) {
            // A ConcurrentModificationException, a wrapper whose delegate
            // moved, a VM that refused the call: none of them can be told
            // apart from a racing writer, and all of them mean the same
            // thing - this run cannot state what was in there.
            return declined(CONTENT_RACED,
                    ConcolicRegionRuntime.rootCause(failed), -1);
        }
    }

    /**
     * The bound the VM applies, read from the same property so the two never
     * disagree about which containers are stated.
     */
    static int maxEntries() {
        try {
            String configured = System.getProperty(BOUND_PROPERTY);
            if (configured == null || configured.trim().isEmpty()) {
                return DEFAULT_MAX_ENTRIES;
            }
            long value = Long.parseLong(configured.trim());
            return value < 0L || value > 1000000L
                    ? DEFAULT_MAX_ENTRIES : (int) value;
        } catch (RuntimeException unparseable) {
            return DEFAULT_MAX_ENTRIES;
        }
    }

    /**
     * The container whose class decides the walk, following {@code
     * Collections.synchronizedX} / {@code unmodifiableX} to what they wrap.
     *
     * <p>Iterating the wrapper iterates the backing container, and it is the
     * backing container's mutations the VM versions, so both questions are
     * the delegate's. The snapshot itself is still attached to the object the
     * carrier names.</p>
     */
    private static Object delegate(Object container) {
        Object cursor = container;
        for (int depth = 0; depth < 8; depth++) {
            String name = cursor.getClass().getName();
            if (!name.startsWith(SYNCHRONIZED_WRAPPER)
                    && !name.startsWith(UNMODIFIABLE_WRAPPER)) {
                return cursor;
            }
            Object backing = wrapped(cursor);
            if (backing == null) return cursor;
            cursor = backing;
        }
        return cursor;
    }

    /** The {@code m} or {@code c} the JDK's wrappers delegate to. */
    private static Object wrapped(Object wrapper) {
        for (Class<?> owner = wrapper.getClass(); owner != null;
             owner = owner.getSuperclass()) {
            for (String name : new String[]{"m", "c"}) {
                try {
                    Field backing = owner.getDeclaredField(name);
                    backing.setAccessible(true);
                    Object value = backing.get(wrapper);
                    if (value != null && value != wrapper) return value;
                } catch (Throwable unavailable) {
                    // Try the next name, then the superclass.
                }
            }
        }
        return null;
    }

    /** One telemetry row for a container this run declined to state. */
    static JsonObject skipRow(Outcome outcome, String locationDescription) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", SKIPPED_EVENT);
        row.addProperty("schemaVersion", 1);
        row.addProperty("reason", outcome.reason);
        row.addProperty("answer", answerName(outcome.answer));
        row.addProperty("detail", ConcolicRegionRuntime.safe(outcome.detail));
        row.addProperty("carrier",
                ConcolicRegionRuntime.safe(locationDescription));
        row.addProperty("entries", outcome.entries);
        row.addProperty("maxEntries", maxEntries());
        return row;
    }

    /**
     * The row for a container this run did state.
     *
     * <p>{@code entries} is what the walk handed the VM, and {@code answer}
     * names which of the VM's outcomes stated it - an installed chain, a
     * history rebuilt on a recovered base, or a container an earlier offer
     * had already stated. The row is filed under {@link #REBASED_EVENT} for
     * the middle one and {@link #STATED_EVENT} otherwise.</p>
     *
     * <p>This row says the content was stated. It does not replace the
     * version's own answer - {@code
     * SharedStateEvidence.declaresInitialSnapshot} - which remains
     * authoritative, because it is read off the value the solver will
     * actually see.</p>
     */
    static JsonObject statedRow(Outcome outcome, String locationDescription) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", outcome.statedEvent());
        row.addProperty("schemaVersion", 1);
        row.addProperty("answer", answerName(outcome.answer));
        row.addProperty("detail", ConcolicRegionRuntime.safe(outcome.detail));
        row.addProperty("carrier",
                ConcolicRegionRuntime.safe(locationDescription));
        row.addProperty("entries", outcome.entries);
        row.addProperty("maxEntries", maxEntries());
        return row;
    }

    /** Test seam: forget which containers have already been offered. */
    static void forgetOfferedContainers() {
        OFFERED.clear();
        POINTER_ONLY.clear();
    }

    private static Set<String> names(String... values) {
        Set<String> set = new LinkedHashSet<>();
        Collections.addAll(set, values);
        return Collections.unmodifiableSet(set);
    }
}
